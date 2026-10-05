import Crashproof

/-!
# Deliberately broken protocols, for mutation testing

Each of these is the commit or recovery protocol with one barrier or write removed or
reordered -- the kind of one-line mistake the proofs are meant to rule out. They are NOT
proved (no theorem mentions them), and the executable runs them only under `--buggy MODE`.
`harness/mutants.py` runs each through the crash harness and checks that it is caught.

The matching *proof* mutations (editing the real `Crashproof.commitOps` / `recoverOps`) make
`lake build` fail; `harness/mutants.py` applies those too.
-/

namespace App.Buggy

open Crashproof

/-- No sync between writing the log slots and writing the commit-point header: the header can
reach the disk before the data it certifies. (Without a checksum, recovery then trusts a
header whose log blocks are stale.) -/
def commitNoLogSync (L : Layout) (t : Txn ByteArray) : List (Op ByteArray) :=
  logWrites t 0 ++
  [.write 0 (Block.encode (t.map Prod.fst))] ++
  [.sync] ++
  installOps L t ++
  [.sync] ++
  [.write 0 (Block.encode [])] ++
  [.sync]

/-- Header first, then the log slots: the commit point precedes the data entirely. -/
def commitHdrFirst (L : Layout) (t : Txn ByteArray) : List (Op ByteArray) :=
  [.write 0 (Block.encode (t.map Prod.fst))] ++
  logWrites t 0 ++
  [.sync] ++
  installOps L t ++
  [.sync] ++
  [.write 0 (Block.encode [])] ++
  [.sync]

/-- No sync after installing at the home blocks before clearing the header: the header can be
cleared while the installed data is still only in the cache, so a crash loses it. -/
def commitNoInstallSync (L : Layout) (t : Txn ByteArray) : List (Op ByteArray) :=
  logWrites t 0 ++
  [.sync] ++
  [.write 0 (Block.encode (t.map Prod.fst))] ++
  [.sync] ++
  installOps L t ++
  [.write 0 (Block.encode [])] ++
  [.sync]

/-- Never retire the header (drop step 4). Recovery clears it at the next mount, but the next
transaction overwrites the log slots while the stale header still commits them. -/
def commitNoClear (L : Layout) (t : Txn ByteArray) : List (Op ByteArray) :=
  logWrites t 0 ++ [.sync] ++ [.write 0 (Block.encode (t.map Prod.fst))] ++ [.sync] ++
  installOps L t ++ [.sync]

/-- Retire the header but do not sync afterwards -- wren-os's choice. Without wren-os's
checksum, the next transaction's log writes can reach the disk while the stale header is still
there, and recovery replays the old address list with the new data. -/
def commitNoClearSync (L : Layout) (t : Txn ByteArray) : List (Op ByteArray) :=
  logWrites t 0 ++ [.sync] ++ [.write 0 (Block.encode (t.map Prod.fst))] ++ [.sync] ++
  installOps L t ++ [.sync] ++ [.write 0 (Block.encode [])]

/-- Recovery that never clears the header: it stays committing, so the next mount replays for
ever and the "header empty" invariant never holds. -/
def recoverNoClear (L : Layout) (es : List (Nat × ByteArray)) : List (Op ByteArray) :=
  installOps L es ++ [.sync]

/-- Recovery that clears the header without first syncing the replayed blocks: a crash can
clear the header while the home blocks are still stale. -/
def recoverNoSync (L : Layout) (es : List (Nat × ByteArray)) : List (Op ByteArray) :=
  installOps L es ++ [.write 0 (Block.encode [])] ++ [.sync]

inductive Mode where
  | noLogSync | hdrFirst | noInstallSync | noClear | noClearSync | recNoClear | recNoSync
deriving Repr, DecidableEq

def Mode.ofString? : String → Option Mode
  | "no-log-sync" => some .noLogSync
  | "hdr-first" => some .hdrFirst
  | "no-install-sync" => some .noInstallSync
  | "no-clear" => some .noClear
  | "no-clear-sync" => some .noClearSync
  | "rec-no-clear" => some .recNoClear
  | "rec-no-sync" => some .recNoSync
  | _ => none

def allModes : List String :=
  ["no-log-sync", "hdr-first", "no-install-sync", "no-clear", "no-clear-sync", "rec-no-clear",
    "rec-no-sync"]

/-- The buggy commit for a mode (commit-phase bugs; recovery bugs reuse the real commit). -/
def commit (m : Mode) (L : Layout) (t : Txn ByteArray) : Prog ByteArray Unit :=
  match t with
  | [] => .ret ()
  | _ => Op.run <| match m with
    | .noLogSync => commitNoLogSync L t
    | .hdrFirst => commitHdrFirst L t
    | .noInstallSync => commitNoInstallSync L t
    | .noClear => commitNoClear L t
    | .noClearSync => commitNoClearSync L t
    | _ => commitOps L t          -- recovery-phase bugs: commit normally

/-- The buggy recovery for a mode. -/
def recover (m : Mode) (L : Layout) : Prog ByteArray Unit :=
  .read 0 fun h => (readLog (committed L h) 0).bind fun es => Op.run <| match m with
    | .recNoClear => recoverNoClear L es
    | .recNoSync => recoverNoSync L es
    | _ => recoverOps L es

end App.Buggy
