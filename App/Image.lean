import App.Device

/-!
# Disk images

```
block 0                 log header
blocks 1 .. L           log slots
blocks L+1 .. L+N       data blocks 0 .. N-1 (the logical disk)
block L+N+1             image descriptor ("CPSB", L, N), written once by `format`
```

The descriptor sits after the data area, where the protocol never writes: logical
addresses are checked against N before they reach the log.

Test blocks are *tagged*: block contents for tag `t` carry `t` and the sector number at the
start of each 512-byte sector, so a dump can tell which write a block (or a torn half of
it) came from.
-/

namespace App

open Crashproof

def u32At (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat + (b.get! (i + 1)).toNat * 256 + (b.get! (i + 2)).toNat * 65536 +
    (b.get! (i + 3)).toNat * 16777216

def putU32 (b : ByteArray) (i n : Nat) : ByteArray :=
  (((b.set! i (UInt8.ofNat n)).set! (i + 1) (UInt8.ofNat (n >>> 8))).set! (i + 2)
    (UInt8.ofNat (n >>> 16))).set! (i + 3) (UInt8.ofNat (n >>> 24))

def zeroBlock : ByteArray := ⟨Array.replicate blockSize 0⟩

def sbMagic : Nat := 0x42535043  -- "CPSB"

structure Geometry where
  logLen : Nat
  nData : Nat

def Geometry.layout (g : Geometry) : Layout := ⟨g.logLen⟩
def Geometry.sbBlock (g : Geometry) : Nat := g.logLen + g.nData + 1
def Geometry.nBlocks (g : Geometry) : Nat := g.logLen + g.nData + 2

def tagByte (t i : Nat) : UInt8 :=
  let s := i / 512
  let j := i % 512
  if j < 4 then UInt8.ofNat (t >>> (8 * j))
  else if j < 8 then UInt8.ofNat (s >>> (8 * (j - 4)))
  else UInt8.ofNat ((t * 31 + i * 7) % 251)

/-- The contents a test write with tag `t` stores (tag 0 is the zero block). -/
def tagBlock (t : Nat) : ByteArray :=
  if t = 0 then zeroBlock else ⟨Array.ofFn (n := blockSize) fun i => tagByte t i.val⟩

/-- What a dump prints for a block: its tag, or `?` and the sector tags if the block is not
exactly one test write (a torn or foreign block). -/
def describe (b : ByteArray) : String :=
  let t := u32At b 0
  if b == tagBlock t then toString t
  else
    let secs := (List.range Block.sectors).map fun s => toString (u32At b (s * 512))
    "?" ++ ",".intercalate secs

def readGeometry (dev : Dev) : IO Geometry := do
  if dev.nBlocks < 3 then throw <| IO.userError "not a crashproof image (too small)"
  let sb ← dev.durable (dev.nBlocks - 1)
  if u32At sb 0 ≠ sbMagic then throw <| IO.userError "not a crashproof image (no descriptor)"
  let g : Geometry := ⟨u32At sb 4, u32At sb 8⟩
  if g.nBlocks ≠ dev.nBlocks then throw <| IO.userError "image size does not match its descriptor"
  return g

def format (path : String) (g : Geometry) : IO Unit := do
  if g.logLen = 0 ∨ g.logLen > Block.capacity then
    throw <| IO.userError s!"log length must be 1..{Block.capacity}"
  if g.nData = 0 ∨ g.nData ≥ 2 ^ 32 then throw <| IO.userError "bad number of data blocks"
  let fd ← devOpen path true
  devPwrite fd 0 (Block.encode [])
  for a in [1:g.nBlocks - 1] do
    devPwrite fd (a * blockSize).toUInt64 zeroBlock
  let sb := putU32 (putU32 (putU32 zeroBlock 0 sbMagic) 4 g.logLen) 8 g.nData
  devPwrite fd (g.sbBlock * blockSize).toUInt64 sb
  devFsync fd
  devClose fd

/-- FNV-1a, for reporting whole-image checksums. -/
def fnv (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  return h

end App
