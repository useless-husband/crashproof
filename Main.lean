import App.Image
import App.Buggy

/-!
Command-line front end. Every disk operation goes through `App.Dev.run` on the verified
programs `Crashproof.recover`, `Crashproof.commit` and `Crashproof.get`; transactions are
built with the verified `Crashproof.Txn.put?`.
-/

open App Crashproof

def usage : String :=
  "usage:
  crashproof format IMAGE [--log L] [--data N]   create an image (default L=8, N=32)
  crashproof recover IMAGE [device flags]        mount: run log recovery
  crashproof run IMAGE WORKLOAD [device flags]   mount, then run a workload file
  crashproof dump IMAGE                          print the header and every data block
  crashproof demo                                format, crash mid-commit, recover, dump

workload lines:  begin | put ADDR TAG | get ADDR TAG | commit   ('#' starts a comment)
device flags:
  --crash-at N     cut the power just before the N-th block write or sync (from 0)
  --seed S         seed for what the crash keeps, tears and the flush order (default 1)
  --torn           let a crash tear blocks at sector boundaries
  --keep A,B,...   instead of random: only these blocks' newest pending writes survive
  --no-fsync       skip fsync at sync (the simulated cache still orders writes)
  --delay-us D     sleep D microseconds per block operation (for kill tests)
  --buggy MODE     run a deliberately broken protocol (mutation testing); MODE is one of
                   no-log-sync hdr-first no-install-sync no-clear no-clear-sync
                   rec-no-clear rec-no-sync
exit status: 0 ok, 99 simulated power cut, 3 a read returned the wrong block, 1 error"

def parseFlags : List String → Config → Except String Config
  | [], c => .ok c
  | "--crash-at" :: n :: r, c => do parseFlags r { c with crashAt := some (← num n) }
  | "--seed" :: n :: r, c => do parseFlags r { c with seed := (← num n).toUInt64 }
  | "--torn" :: r, c => parseFlags r { c with torn := true }
  | "--no-fsync" :: r, c => parseFlags r { c with fsync := false }
  | "--delay-us" :: n :: r, c => do parseFlags r { c with delayUs := ← num n }
  | "--keep" :: l :: r, c => do
    let xs ← (l.splitOn ",").filter (· ≠ "") |>.mapM num
    parseFlags r { c with keep := some xs }
  | x :: _, _ => .error s!"unknown flag {x}"
where
  num (s : String) : Except String Nat :=
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"not a number: {s}"

def takeBuggy : List String → Except String (Option Buggy.Mode × List String)
  | "--buggy" :: m :: r => do
    let some mode := Buggy.Mode.ofString? m | .error s!"unknown --buggy mode {m}"
    .ok (some mode, r)
  | x :: r => do let (b, r') ← takeBuggy r; .ok (b, x :: r')
  | [] => .ok (none, [])

def orFail {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError e

def mount (path : String) (cfg : Config) (bug : Option Buggy.Mode) : IO (Dev × Geometry) := do
  let dev ← Dev.openImage path cfg
  let g ← readGeometry dev
  match bug with
  | some m => dev.run (Buggy.recover m g.layout)
  | none => dev.run (recover g.layout)
  return (dev, g)

def runWorkload (dev : Dev) (g : Geometry) (bug : Option Buggy.Mode) (lines : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let mut txn : Option (Txn ByteArray) := none
  let mut acks := 0
  for raw in lines do
    let line := (raw.splitOn "#").head!.trimAscii.toString
    if line.isEmpty then continue
    match line.splitOn " " |>.filter (· ≠ "") with
    | ["begin"] =>
      if txn.isSome then throw <| IO.userError "begin inside a transaction"
      txn := some []
    | ["put", a, t] =>
      let some t0 := txn | throw <| IO.userError "put outside a transaction"
      let (a, t) ← orFail do pure (← parseFlags.num a, ← parseFlags.num t)
      if a ≥ g.nData then throw <| IO.userError s!"address {a} out of range"
      match Txn.put? g.layout t0 a (tagBlock t) with
      | some t' => txn := some t'
      | none => throw <| IO.userError "transaction does not fit in the log"
    | ["get", a, t] =>
      let (a, t) ← orFail do pure (← parseFlags.num a, ← parseFlags.num t)
      if a ≥ g.nData then throw <| IO.userError s!"address {a} out of range"
      let v ← dev.run (get g.layout (txn.getD []) a)
      if v != tagBlock t then
        out.putStrLn s!"read-mismatch {a}: expected {t}, got {describe v}"
        out.flush
        return 3
    | ["commit"] =>
      let some t0 := txn | throw <| IO.userError "commit outside a transaction"
      match bug with
      | some m => dev.run (Buggy.commit m g.layout t0)
      | none => dev.run (commit g.layout t0)
      txn := none
      acks := acks + 1
      out.putStrLn s!"ack {acks}"
      out.flush
    | _ => throw <| IO.userError s!"bad workload line: {raw}"
  out.putStrLn s!"ops {← dev.ops}"
  return 0

def dump (path : String) : IO Unit := do
  let dev ← Dev.openImage path {}
  let g ← readGeometry dev
  let h ← dev.durable 0
  match Block.decode h with
  | some [] => IO.println "header empty"
  | some l => IO.println s!"header commits {l.length} blocks {l}"
  | none => IO.println "header garbage"
  for a in [0:g.nData] do
    IO.println s!"{a} {describe (← dev.durable (g.layout.home a))}"
  dev.close

def demo : IO Unit := do
  let dir ← IO.FS.createTempDir
  let img := (dir / "demo.img").toString
  format img ⟨4, 4⟩
  IO.println "formatted a 4-block disk with a 4-slot log; committing tags 1,2 to blocks 0,1"
  let (dev, g) ← mount img {} none
  dev.run (commit g.layout [(0, tagBlock 1), (1, tagBlock 2)])
  dev.close
  dump img
  IO.println "\nnow committing tags 3,4 to blocks 0,1 (a child process loses power at block operation 9,\nafter the commit point, while installing)"
  let wl := (dir / "wl.txt").toString
  IO.FS.writeFile wl "begin\nput 0 3\nput 1 4\ncommit\n"
  let self ← IO.appPath
  let r ← IO.Process.output { cmd := self.toString, args := #["run", img, wl, "--crash-at", "9",
    "--seed", "1", "--no-fsync"] }
  IO.print r.stderr
  IO.println "\nafter the crash, before recovery (block 1 is new, block 0 is still old):"
  dump img
  let (dev, _) ← mount img {} none
  dev.close
  IO.println "\nafter recovery (the header commits the transaction, so the log is replayed):"
  dump img
  IO.FS.removeDirAll dir

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["format", img] => format img ⟨8, 32⟩; return 0
    | "format" :: img :: rest =>
      let (l, n) ← orFail (geo rest 8 32)
      format img ⟨l, n⟩
      return 0
    | "recover" :: img :: flags =>
      let (bug, flags) ← orFail (takeBuggy flags)
      let (dev, _) ← mount img (← orFail (parseFlags flags {})) bug
      IO.println s!"recovered ops {← dev.ops}"
      dev.close
      return 0
    | "run" :: img :: wl :: flags =>
      let (bug, flags) ← orFail (takeBuggy flags)
      let cfg ← orFail (parseFlags flags {})
      let lines := (← IO.FS.readFile wl).splitOn "\n"
      let (dev, g) ← mount img cfg bug
      let rc ← runWorkload dev g bug lines
      dev.close
      return rc
    | ["dump", img] => dump img; return 0
    | ["demo"] => demo; return 0
    | _ => IO.eprintln usage; return 1
  catch e =>
    IO.eprintln s!"crashproof: {e}"
    return 1
where
  geo : List String → Nat → Nat → Except String (Nat × Nat)
    | [], l, n => .ok (l, n)
    | "--log" :: x :: r, _, n => do geo r (← parseFlags.num x) n
    | "--data" :: x :: r, l, _ => do geo r l (← parseFlags.num x)
    | x :: _, _, _ => .error s!"unknown flag {x}"
