import Crashproof.Prog

/-!
# The write-ahead log

On-disk layout (`Layout`), with `L` log slots:

```
block 0            header: the home addresses of the committed transaction, or empty
blocks 1 .. L      log slots: copies of the transaction's new block values
blocks L+1 ..      the logical disk: logical block a lives at L + 1 + a
```

A transaction is built in memory (`Txn`): `put` records a new value for a logical block
(a later `put` to the same block replaces the earlier one, so each block is logged once),
`get` returns the transaction's value if there is one and otherwise reads the disk.

`commit` (each line is one step of `commitOps`; the comments name the protocol steps):

1. write the new values to log slots 1..n, then sync;
2. write the header listing the n home addresses, then sync — this single-block write is
   the commit point;
3. install: write every new value to its home block, then sync;
4. retire: write an empty header, then sync.

`recover` (run at every mount): read the header; if it lists n ≤ L addresses, copy log slot
i to the i-th home address for every i, sync; then write an empty header and sync. Replaying
is idempotent, so a crash during recovery is handled by running recovery again.

This is xv6's log with explicit barriers, and the same sequence as wren-os's
`kernel/log.c`, except that wren-os protects the header with a CRC instead of syncing after
step 4 (see `docs/report.md`).
-/

namespace Crashproof

variable {V : Type}

/-- Point update of a function. -/
def upd (m : Nat → V) (a : Nat) (v : V) : Nat → V := fun b => if b = a then v else m b

/-- Apply a list of (address, value) writes in order; a later write to the same address
wins. -/
def applyWrites (ws : List (Nat × V)) (m : Nat → V) : Nat → V :=
  ws.foldl (fun m p => upd m p.1 p.2) m

/-- Where the log lives. -/
structure Layout where
  /-- Number of log slots. A transaction may change at most this many blocks. -/
  logLen : Nat

namespace Layout

/-- Physical address of logical block `a`. -/
def home (L : Layout) (a : Nat) : Nat := L.logLen + 1 + a

/-- The logical disk stored in a physical state. -/
def data (L : Layout) (x : Nat → V) : Nat → V := fun a => x (L.home a)

end Layout

/-- The (address, value) pairs that log slots `1 + i ..` hold for header list `l`. -/
def logEntries (x : Nat → V) : List Nat → Nat → List (Nat × V)
  | [], _ => []
  | a :: l, i => (a, x (1 + i)) :: logEntries x l (i + 1)

section WithCodec
variable [Codec V]

/-- The addresses a header block commits. Anything that is not a well-formed header of at
most `L.logLen` entries commits nothing. -/
def committed (L : Layout) (h : V) : List Nat :=
  match Codec.decode h with
  | some l => if l.length ≤ L.logLen then l else []
  | none => []

/-- **The meaning of a crashed disk**: the logical disk recovery will produce from platter
contents `x`. Everything the theorems say about crashes is phrased through this function. -/
def recovered (L : Layout) (x : Nat → V) : Nat → V :=
  applyWrites (logEntries x (committed L (x 0)) 0) (L.data x)

/-- The log is idle and the logical disk is `m`: an empty header that is durable, and every
data block durable with the value `m` gives it. (Log slots may hold anything.) -/
structure Idle (L : Layout) (m : Nat → V) (d : Disk V) : Prop where
  hdr_durable : d.Durable 0
  hdr_empty : Codec.decode (d 0).cur = some []
  data_durable : ∀ a, d.Durable (L.home a)
  data_cur : ∀ a, (d (L.home a)).cur = m a

/-! ## In-memory transactions -/

/-- An open transaction: the blocks it changed, newest first, each address once. -/
abbrev Txn (V : Type) := List (Nat × V)

/-- The value a transaction gives an address, if it changed it. -/
def Txn.find? : Txn V → Nat → Option V
  | [], _ => none
  | (b, v) :: t, a => if b = a then some v else Txn.find? t a

/-- Record a write in the transaction. -/
def Txn.put (t : Txn V) (a : Nat) (v : V) : Txn V := (a, v) :: t.filter (fun p => p.1 ≠ a)

/-- A transaction the log can commit: it fits in the log and in one header. -/
structure TxnOK (L : Layout) (t : Txn V) : Prop where
  fits_log : t.length ≤ L.logLen
  fits_header : t.length ≤ Codec.capacity (V := V)
  addrs : ∀ p ∈ t, p.1 < Codec.addrBound (V := V)

/-- `put` that refuses writes the log could not commit. -/
def Txn.put? (L : Layout) (t : Txn V) (a : Nat) (v : V) : Option (Txn V) :=
  let t' := t.put a v
  if t'.length ≤ L.logLen ∧ t'.length ≤ Codec.capacity (V := V) ∧ a < Codec.addrBound (V := V)
  then some t' else none

/-! ## The protocol -/

/-- Step 1: copy the transaction's values into log slots `1 + i ..`. -/
def logWrites : Txn V → Nat → List (Op V)
  | [], _ => []
  | (_, v) :: t, i => .write (1 + i) v :: logWrites t (i + 1)

/-- Step 3 (and recovery's replay): write each value to its home block. -/
def installOps (L : Layout) (ws : List (Nat × V)) : List (Op V) :=
  ws.map fun p => .write (L.home p.1) p.2

/-- The whole commit as a straight-line list of block operations. -/
def commitOps (L : Layout) (t : Txn V) : List (Op V) :=
  logWrites t 0 ++
  [.sync] ++                                   -- log slots durable before the commit point
  [.write 0 (Codec.encode (t.map Prod.fst))] ++  -- commit point
  [.sync] ++
  installOps L t ++                            -- install at home
  [.sync] ++
  [.write 0 (Codec.encode [])] ++              -- retire the header
  [.sync]

/-- Read a transaction's value, or the disk's. -/
def get (L : Layout) (t : Txn V) (a : Nat) : Prog V V :=
  match t.find? a with
  | some v => .ret v
  | none => .read (L.home a) .ret

def commit (L : Layout) (t : Txn V) : Prog V Unit :=
  match t with
  | [] => .ret ()
  | _ => Op.run (commitOps L t)

/-- Read log slots `1 + i ..` for the addresses in `l`. -/
def readLog : List Nat → Nat → Prog V (List (Nat × V))
  | [], _ => .ret []
  | a :: l, i => .read (1 + i) fun v => (readLog l (i + 1)).bind fun es => .ret ((a, v) :: es)

/-- Recovery's writes once the log has been read. -/
def recoverOps (L : Layout) (es : List (Nat × V)) : List (Op V) :=
  installOps L es ++
  [.sync] ++                                   -- replayed blocks durable before retiring
  [.write 0 (Codec.encode [])] ++
  [.sync]

def recover (L : Layout) : Prog V Unit :=
  .read 0 fun h => (readLog (committed L h) 0).bind fun es => Op.run (recoverOps L es)

/-- Every way a recovery can end: it completes, or it crashes and recovery starts over from
whatever the platter holds. -/
inductive RecoversTo (L : Layout) : (Nat → V) → Disk V → Prop where
  | done {x d} : Exec (recover L) (Disk.ofState x) (.done d ()) → RecoversTo L x d
  | crash {x x' d' d} : Exec (recover L) (Disk.ofState x) (.crashed d') → CrashesTo d' x' →
      RecoversTo L x' d → RecoversTo L x d

end WithCodec

end Crashproof
