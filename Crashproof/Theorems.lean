import Crashproof.LogProofs

/-!
# The main theorems

Every statement is about *all* executions: a crash may strike before any block operation,
the drive may lose, reorder or tear any write since the last sync, and recovery itself may
crash any number of times. `scripts/axioms.lean` prints the axioms each theorem uses.
-/

namespace Crashproof.Theorems

open Crashproof

variable {V : Type} [Codec V]

/-- **Recovery is idempotent.** However many times recovery crashes and restarts, once it
completes the log is idle and the logical disk is the one the first crash determined. -/
theorem recovery_idempotent {L : Layout} {x : Nat → V} {d : Disk V} (h : RecoversTo L x d) :
    Idle L (recovered L x) d := by
  induction h with
  | done he => exact (recover_spec L _).done rfl he
  | crash he hx' _ ih =>
    have := (recover_spec L _).crashed rfl he _ hx'
    rw [← this]
    exact ih

/-- **Atomicity.** A crash at any point of `commit` (logging, the commit point, install, or
retiring the header), followed by recovery that may itself crash any number of times, ends
with the logical disk either as it was before the transaction or as the transaction left it. -/
theorem atomicity {L : Layout} {t : Txn V} (htx : TxnOK L t) {m : Nat → V} {d dc df : Disk V}
    {x : Nat → V} (hidle : Idle L m d) (he : Exec (commit L t) d (.crashed dc))
    (hx : CrashesTo dc x) (hr : RecoversTo L x df) :
    Idle L m df ∨ Idle L (applyWrites t m) df := by
  have hi := recovery_idempotent hr
  rcases (commit_spec htx m).crashed hidle he x hx with h | h
  · rw [h] at hi; exact Or.inl hi
  · rw [h] at hi; exact Or.inr hi

/-- **Durability.** Once `commit` returns, the logical disk is the transaction's result, and
any crash from then on (before the next operation) recovers to exactly that result. -/
theorem durability {L : Layout} {t : Txn V} (htx : TxnOK L t) {m : Nat → V} {d d' : Disk V}
    (hidle : Idle L m d) (he : Exec (commit L t) d (.done d' ())) :
    Idle L (applyWrites t m) d' ∧
      ∀ x df, CrashesTo d' x → RecoversTo L x df → Idle L (applyWrites t m) df := by
  have hpost := (commit_spec htx m).done hidle he
  refine ⟨hpost, fun x df hx hr => ?_⟩
  have := recovery_idempotent hr
  rwa [hpost.crash hx] at this

/-- A crash while no commit is running (for example while a transaction is still being
built in memory) loses only the uncommitted transaction. -/
theorem crash_while_idle {L : Layout} {m : Nat → V} {d df : Disk V} {x : Nat → V}
    (hidle : Idle L m d) (hx : CrashesTo d x) (hr : RecoversTo L x df) : Idle L m df := by
  have := recovery_idempotent hr
  rwa [hidle.crash hx] at this

/-- **Reads inside a transaction** return the transaction's own writes, and the disk's
committed contents for every other block; they change nothing on disk. -/
theorem get_correct {L : Layout} {t : Txn V} (hnd : (t.map Prod.fst).Nodup) {m : Nat → V}
    {d0 : Disk V} (hidle : Idle L m d0) (a : Nat) :
    Spec (fun d => d = d0) (get L t a) (fun v d => d = d0 ∧ v = applyWrites t m a)
      (fun d => d = d0) := by
  rw [find?_meaning hnd a m]
  unfold get
  cases hf : t.find? a with
  | some v => exact spec_ret (fun d h => ⟨h, rfl⟩) (fun _ h => h)
  | none =>
    apply spec_read (fun _ h => h)
    intro v
    apply spec_ret
    · intro d ⟨hd, hv⟩
      subst hd
      refine ⟨rfl, ?_⟩
      rw [← hv, hidle.data_cur a]
      rfl
    · intro d h; exact h.1

/-- **Writes inside a transaction**: `put` changes exactly one block of the transaction's
logical disk, and keeps each block logged at most once (so a read sees the newest write). -/
theorem put_correct (t : Txn V) (a : Nat) (v : V) (m : Nat → V) :
    applyWrites (t.put a v) m = upd (applyWrites t m) a v :=
  put_meaning t a v m

theorem put_keeps_nodup {t : Txn V} (h : (t.map Prod.fst).Nodup) (a : Nat) (v : V) :
    ((t.put a v).map Prod.fst).Nodup :=
  put_nodup h a v

/-- `put?` only builds transactions the log can commit. -/
theorem put?_ok {L : Layout} {t t' : Txn V} {a : Nat} {v : V} (ht : TxnOK L t)
    (h : Txn.put? L t a v = some t') : TxnOK L t' := by
  dsimp only [Txn.put?] at h
  split at h
  · rename_i hc
    cases h
    refine ⟨hc.1, hc.2.1, ?_⟩
    intro p hp
    simp only [Txn.put, List.mem_cons, List.mem_filter] at hp
    rcases hp with rfl | ⟨hp, _⟩
    · exact hc.2.2
    · exact ht.addrs p hp
  · cases h

/-- Run several transactions one after the other. -/
def commitAll (L : Layout) : List (Txn V) → Prog V Unit
  | [] => .ret ()
  | t :: ts => (commit L t).bind fun _ => commitAll L ts

/-- The logical disks a run of transactions passes through. -/
def states (m : Nat → V) : List (Txn V) → List (Nat → V)
  | [] => [m]
  | t :: ts => m :: states (applyWrites t m) ts

def finalState (m : Nat → V) (ts : List (Txn V)) : Nat → V :=
  ts.foldl (fun m t => applyWrites t m) m

/-- **Sequences of transactions** (proved only from `commit_spec` with the sequencing rule
of the logic): a crash anywhere recovers to the state after some prefix of the
transactions — never to a state in which a transaction is half applied. -/
theorem commitAll_spec (L : Layout) (ts : List (Txn V)) (hok : ∀ t ∈ ts, TxnOK L t)
    (m : Nat → V) :
    Spec (Idle L m) (commitAll L ts) (fun _ => Idle L (finalState m ts))
      (fun d => ∀ x, CrashesTo d x → recovered L x ∈ states m ts) := by
  induction ts generalizing m with
  | nil =>
    exact spec_ret (fun d h => h) (fun d h x hx => by simp [states, h.crash hx])
  | cons t ts ih =>
    apply spec_bind (spec_conseq (commit_spec (hok t (List.mem_cons_self ..)) m)
      (fun _ h => h) (fun _ _ h => h) ?_)
    · intro _
      exact spec_conseq (ih (fun t' h' => hok t' (List.mem_cons_of_mem _ h')) _)
        (fun _ h => h) (fun _ _ h => h)
        (fun d h x hx => List.mem_cons_of_mem _ (h x hx))
    · intro d h x hx
      rcases h x hx with h1 | h1
      · rw [h1]; exact List.mem_cons_self ..
      · rw [h1]
        apply List.mem_cons_of_mem
        cases ts <;> simp [states]

end Crashproof.Theorems
