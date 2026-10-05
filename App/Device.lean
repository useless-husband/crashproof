import Crashproof

/-!
# Running a `Prog` on a disk-image file

This is the unverified bridge between the proofs and a real file. It interprets the very
`Prog` values the theorems are about, with a simulated volatile write cache in front of the
file:

* `write` puts the block in the cache (reads see it);
* `sync` writes every cached block to the file in a shuffled order, then calls
  `fsync`/`F_FULLFSYNC` (unless `--no-fsync`);
* with `--crash-at N` the process cuts the power just before the N-th write or sync
  (counting from 0): each cached block independently keeps its old value or reaches the
  file with one of the values written since the last sync; with `--torn` a block may also
  be torn at a 512-byte sector boundary. Then the process exits with status 99.

That is the disk model of `Crashproof.Disk`, executed. `--keep a,b,..` replaces the random
choice by a fixed one (the listed blocks reach the file with their newest value, the rest
are lost), for directed reproducers.
-/

namespace App

@[extern "crashproof_dev_open"] opaque devOpen (path : @& String) (create : Bool) : IO UInt32
@[extern "crashproof_dev_close"] opaque devClose (fd : UInt32) : IO Unit
@[extern "crashproof_dev_size"] opaque devSize (fd : UInt32) : IO UInt64
@[extern "crashproof_dev_pread"] opaque devPread (fd : UInt32) (off : UInt64) (len : USize) :
  IO ByteArray
@[extern "crashproof_dev_pwrite"] opaque devPwrite (fd : UInt32) (off : UInt64)
  (data : @& ByteArray) : IO Unit
@[extern "crashproof_dev_fsync"] opaque devFsync (fd : UInt32) : IO Unit
@[extern "crashproof_dev_usleep"] opaque devUsleep (us : UInt32) : IO Unit

def blockSize : Nat := Crashproof.Block.blockSize

structure Config where
  crashAt : Option Nat := none
  seed : UInt64 := 1
  torn : Bool := false
  fsync : Bool := true
  delayUs : Nat := 0
  keep : Option (List Nat) := none

structure State where
  /-- Versions written since the last sync, oldest first, per block. -/
  pending : Array (Nat × Array ByteArray) := #[]
  ops : Nat := 0
  rng : UInt64 := 0x9E3779B97F4A7C15

structure Dev where
  fd : UInt32
  nBlocks : Nat
  cfg : Config
  st : IO.Ref State

/-- xorshift64* -/
def Dev.rand (dev : Dev) (n : Nat) : IO Nat := do
  let s ← dev.st.get
  let mut x := s.rng
  x := x ^^^ (x >>> 12)
  x := x ^^^ (x <<< 25)
  x := x ^^^ (x >>> 27)
  dev.st.set { s with rng := x }
  let r := (x * 0x2545F4914F6CDD1D) >>> 11
  return if n = 0 then 0 else r.toNat % n

def Dev.openImage (path : String) (cfg : Config) : IO Dev := do
  let fd ← devOpen path false
  let size ← devSize fd
  let st ← IO.mkRef ({ rng := cfg.seed * 0x9E3779B97F4A7C15 + 1 } : State)
  return { fd, nBlocks := size.toNat / blockSize, cfg, st }

def Dev.durable (dev : Dev) (a : Nat) : IO ByteArray :=
  devPread dev.fd (a * blockSize).toUInt64 blockSize.toUSize

def Dev.put (dev : Dev) (a : Nat) (v : ByteArray) : IO Unit :=
  devPwrite dev.fd (a * blockSize).toUInt64 v

def Dev.read (dev : Dev) (a : Nat) : IO ByteArray := do
  if a ≥ dev.nBlocks then throw <| IO.userError s!"read of block {a} beyond the image"
  let s ← dev.st.get
  match s.pending.find? (·.1 == a) with
  | some (_, vs) => return vs.back!
  | none => dev.durable a

def Dev.close (dev : Dev) : IO Unit := devClose dev.fd

/-- Power cut: every block with pending writes picks what reaches the platter. -/
def Dev.crash (dev : Dev) : IO Unit := do
  let s ← dev.st.get
  for (a, vs) in s.pending do
    match dev.cfg.keep with
    | some keep => if keep.contains a then dev.put a vs.back!
    | none =>
      let old ← dev.durable a
      let cands := #[old] ++ vs
      let i ← dev.rand cands.size
      let tear ← if dev.cfg.torn then (· == 0) <$> dev.rand 3 else pure false
      if tear then
        let j ← dev.rand cands.size
        let k := 1 + (← dev.rand 7)
        let x := cands[i]!
        let y := cands[j]!
        let cut := k * Crashproof.Block.sectorSize
        dev.put a (x.extract 0 cut ++ y.extract cut blockSize)
      else if i ≠ 0 then
        dev.put a cands[i]!
  IO.eprintln s!"crash: power cut before block operation {s.ops}"
  IO.Process.exit 99

/-- Called before every write and sync. -/
def Dev.step (dev : Dev) : IO Unit := do
  let s ← dev.st.get
  if dev.cfg.crashAt == some s.ops then dev.crash
  dev.st.set { s with ops := s.ops + 1 }
  if dev.cfg.delayUs > 0 then devUsleep dev.cfg.delayUs.toUInt32

def Dev.write (dev : Dev) (a : Nat) (v : ByteArray) : IO Unit := do
  if a ≥ dev.nBlocks then throw <| IO.userError s!"write of block {a} beyond the image"
  if v.size ≠ blockSize then throw <| IO.userError s!"block of {v.size} bytes"
  dev.step
  dev.st.modify fun s =>
    match s.pending.findIdx? (·.1 == a) with
    | some i => { s with pending := s.pending.modify i fun (b, vs) => (b, vs.push v) }
    | none => { s with pending := s.pending.push (a, #[v]) }

def Dev.sync (dev : Dev) : IO Unit := do
  dev.step
  let s ← dev.st.get
  -- the drive empties its cache in an order of its choosing
  let mut order := s.pending
  for i in [0:order.size] do
    let j := i + (← dev.rand (order.size - i))
    order := order.swapIfInBounds i j
  for (a, vs) in order do
    dev.put a vs.back!
  if dev.cfg.fsync then devFsync dev.fd
  dev.st.modify fun s => { s with pending := #[] }

def Dev.ops (dev : Dev) : IO Nat := return (← dev.st.get).ops

/-- Execute a program of the verified library on the device. -/
def Dev.run {α : Type} (dev : Dev) : Crashproof.Prog ByteArray α → IO α
  | .ret a => pure a
  | .read a k => do
    let v ← dev.read a
    dev.run (k v)
  | .write a v p => do
    dev.write a v
    dev.run p
  | .sync p => do
    dev.sync
    dev.run p

end App
