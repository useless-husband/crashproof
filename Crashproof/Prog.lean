import Crashproof.Disk

/-!
# Programs that may crash, and crash-aware specifications

`Prog V α` is a program that reads, writes and syncs blocks of type `V` and returns an `α`.
It is a free monad: the same value is *executed* on a real file by `Crashproof.Device` and
*reasoned about* through `Exec`, a relation that allows a crash before any step.

`Spec pre p post crash` is a Crash Hoare Logic triple (FSCQ's `{pre} p {post} {crash}`):
started on a disk satisfying `pre`, every execution of `p` either finishes in a state
satisfying `post`, or is cut short by a crash in a state satisfying `crash`. The crash
condition talks about the disk *at the moment of the crash* (with its pending writes); what
the platter may hold afterwards is `CrashesTo`.
-/

namespace Crashproof

inductive Prog (V : Type) (α : Type) : Type where
  | ret : α → Prog V α
  | read : Nat → (V → Prog V α) → Prog V α
  | write : Nat → V → Prog V α → Prog V α
  | sync : Prog V α → Prog V α

namespace Prog
variable {V α β : Type}

def bind : Prog V α → (α → Prog V β) → Prog V β
  | .ret a, k => k a
  | .read a f, k => .read a (fun v => (f v).bind k)
  | .write a v p, k => .write a v (p.bind k)
  | .sync p, k => .sync (p.bind k)

instance : Monad (Prog V) where
  pure := .ret
  bind := Prog.bind

end Prog

inductive Result (V α : Type) : Type where
  | done : Disk V → α → Result V α
  | crashed : Disk V → Result V α

/-- One run of a program. `crash` may fire before any step, including the first and after
the last; otherwise the program runs to completion. Reads see the current (cached) value. -/
inductive Exec {V : Type} : {α : Type} → Prog V α → Disk V → Result V α → Prop where
  | ret {α} {a : α} {d} : Exec (.ret a) d (.done d a)
  | read {α} {a : Nat} {k : V → Prog V α} {d r} :
      Exec (k (d a).cur) d r → Exec (.read a k) d r
  | write {α} {a : Nat} {v : V} {p : Prog V α} {d r} :
      Exec p (d.write a v) r → Exec (.write a v p) d r
  | sync {α} {p : Prog V α} {d r} : Exec p d.sync r → Exec (.sync p) d r
  | crash {α} {p : Prog V α} {d} : Exec p d (.crashed d)

section Exec
variable {V α β : Type}

theorem exec_bind {p : Prog V α} {k : α → Prog V β} {d : Disk V} {r : Result V β}
    (h : Exec (p.bind k) d r) :
    (∃ d', Exec p d (.crashed d') ∧ r = .crashed d') ∨
    (∃ d1 a, Exec p d (.done d1 a) ∧ Exec (k a) d1 r) := by
  induction p generalizing d with
  | ret a => exact Or.inr ⟨d, a, .ret, h⟩
  | read a f ih =>
    cases h with
    | read h =>
      rcases ih _ h with ⟨d', h1, rfl⟩ | ⟨d1, b, h1, h2⟩
      · exact Or.inl ⟨d', .read h1, rfl⟩
      · exact Or.inr ⟨d1, b, .read h1, h2⟩
    | crash => exact Or.inl ⟨d, .crash, rfl⟩
  | write a v p ih =>
    cases h with
    | write h =>
      rcases ih h with ⟨d', h1, rfl⟩ | ⟨d1, b, h1, h2⟩
      · exact Or.inl ⟨d', .write h1, rfl⟩
      · exact Or.inr ⟨d1, b, .write h1, h2⟩
    | crash => exact Or.inl ⟨d, .crash, rfl⟩
  | sync p ih =>
    cases h with
    | sync h =>
      rcases ih h with ⟨d', h1, rfl⟩ | ⟨d1, b, h1, h2⟩
      · exact Or.inl ⟨d', .sync h1, rfl⟩
      · exact Or.inr ⟨d1, b, .sync h1, h2⟩
    | crash => exact Or.inl ⟨d, .crash, rfl⟩

end Exec

/-- Crash Hoare Logic triple. -/
def Spec {V α : Type} (pre : Disk V → Prop) (p : Prog V α) (post : α → Disk V → Prop)
    (crash : Disk V → Prop) : Prop :=
  ∀ d r, pre d → Exec p d r →
    match r with
    | .done d' a => post a d'
    | .crashed d' => crash d'

section Rules
variable {V α β : Type}

theorem Spec.done {pre : Disk V → Prop} {p : Prog V α} {post crash} (h : Spec pre p post crash)
    {d d' a} (hp : pre d) (he : Exec p d (.done d' a)) : post a d' := h d _ hp he

theorem Spec.crashed {pre : Disk V → Prop} {p : Prog V α} {post crash}
    (h : Spec pre p post crash) {d d'} (hp : pre d) (he : Exec p d (.crashed d')) : crash d' :=
  h d _ hp he

/-- A crash may happen before the first step, so a crash condition must follow from the
precondition. -/
theorem Spec.pre_crash {pre : Disk V → Prop} {p : Prog V α} {post crash}
    (h : Spec pre p post crash) {d} (hp : pre d) : crash d := h.crashed hp .crash

theorem spec_conseq {pre pre' : Disk V → Prop} {p : Prog V α} {post post' : α → Disk V → Prop}
    {crash crash' : Disk V → Prop} (h : Spec pre p post crash) (hpre : ∀ d, pre' d → pre d)
    (hpost : ∀ a d, post a d → post' a d) (hcrash : ∀ d, crash d → crash' d) :
    Spec pre' p post' crash' := by
  intro d r hp he
  have := h d r (hpre d hp) he
  cases r with
  | done d' a => exact hpost a d' this
  | crashed d' => exact hcrash d' this

/-- Sequencing: the crash condition of the whole is that of either part. -/
theorem spec_bind {pre : Disk V → Prop} {p : Prog V α} {k : α → Prog V β}
    {mid : α → Disk V → Prop} {post : β → Disk V → Prop} {crash : Disk V → Prop}
    (hp : Spec pre p mid crash) (hk : ∀ a, Spec (mid a) (k a) post crash) :
    Spec pre (p.bind k) post crash := by
  intro d r hpre he
  rcases exec_bind he with ⟨d', h1, rfl⟩ | ⟨d1, a, h1, h2⟩
  · exact hp.crashed hpre h1
  · exact hk a d1 r (hp.done hpre h1) h2

theorem spec_ret {pre : Disk V → Prop} {a : α} {post : α → Disk V → Prop}
    {crash : Disk V → Prop} (hpost : ∀ d, pre d → post a d) (hcrash : ∀ d, pre d → crash d) :
    Spec pre (.ret a) post crash := by
  intro d r hp he
  cases he with
  | ret => exact hpost d hp
  | crash => exact hcrash d hp

/-- Reads do not change the disk. -/
theorem spec_read {pre : Disk V → Prop} {a : Nat} {k : V → Prog V α}
    {post : α → Disk V → Prop} {crash : Disk V → Prop}
    (hcrash : ∀ d, pre d → crash d)
    (hk : ∀ v, Spec (fun d => pre d ∧ (d a).cur = v) (k v) post crash) :
    Spec pre (.read a k) post crash := by
  intro d r hp he
  cases he with
  | read h => exact hk _ d r ⟨hp, rfl⟩ h
  | crash => exact hcrash d hp

end Rules

/-! ## Straight-line block operations

The commit protocol and the second half of recovery never branch on what they read, so
they are lists of writes and syncs. A crash during such a list leaves the disk after some
prefix of it. -/

inductive Op (V : Type) : Type where
  | write : Nat → V → Op V
  | sync : Op V

namespace Op
variable {V : Type}

def apply : Op V → Disk V → Disk V
  | .write a v, d => d.write a v
  | .sync, d => d.sync

def run : List (Op V) → Prog V Unit
  | [] => .ret ()
  | .write a v :: ops => .write a v (run ops)
  | .sync :: ops => .sync (run ops)

/-- The disk after a list of operations. -/
def applyAll (ops : List (Op V)) (d : Disk V) : Disk V := ops.foldl (fun d o => o.apply d) d

@[simp] theorem applyAll_nil (d : Disk V) : applyAll [] d = d := rfl
@[simp] theorem applyAll_cons (o : Op V) (ops : List (Op V)) (d : Disk V) :
    applyAll (o :: ops) d = applyAll ops (o.apply d) := rfl
theorem applyAll_append (ops ops' : List (Op V)) (d : Disk V) :
    applyAll (ops ++ ops') d = applyAll ops' (applyAll ops d) := by
  simp [applyAll, List.foldl_append]

theorem exec_run {ops : List (Op V)} {d : Disk V} {r : Result V Unit} (h : Exec (run ops) d r) :
    r = .done (applyAll ops d) () ∨ ∃ k, r = .crashed (applyAll (ops.take k) d) := by
  induction ops generalizing d with
  | nil =>
    cases h with
    | ret => exact Or.inl rfl
    | crash => exact Or.inr ⟨0, rfl⟩
  | cons o ops ih =>
    cases o with
    | write a v =>
      cases h with
      | write h =>
        rcases ih h with rfl | ⟨k, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k + 1, rfl⟩
      | crash => exact Or.inr ⟨0, rfl⟩
    | sync =>
      cases h with
      | sync h =>
        rcases ih h with rfl | ⟨k, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k + 1, rfl⟩
      | crash => exact Or.inr ⟨0, rfl⟩

/-- Crash states of `A ++ B`: a crash state of `A`, or one of `B` started where `A` ended. -/
theorem take_append_cases (A B : List (Op V)) (k : Nat) (d : Disk V) :
    (∃ j, applyAll ((A ++ B).take k) d = applyAll (A.take j) d) ∨
    (∃ j, applyAll ((A ++ B).take k) d = applyAll (B.take j) (applyAll A d)) := by
  rw [List.take_append]
  by_cases hk : k ≤ A.length
  · left
    refine ⟨k, ?_⟩
    have : k - A.length = 0 := by omega
    simp [this]
  · right
    refine ⟨k - A.length, ?_⟩
    rw [List.take_of_length_le (by omega), applyAll_append]

/-- Spec of a straight-line list: the post state is exact, crash states are prefixes. -/
theorem spec_run (ops : List (Op V)) (d0 : Disk V) :
    Spec (fun d => d = d0) (run ops) (fun _ d => d = applyAll ops d0)
      (fun d => ∃ k, d = applyAll (ops.take k) d0) := by
  intro d r hd he
  subst hd
  rcases exec_run he with rfl | ⟨k, rfl⟩
  · rfl
  · exact ⟨k, rfl⟩

/-- Addresses an operation writes. -/
def writes : Op V → List Nat
  | .write a _ => [a]
  | .sync => []

/-- Blocks that no operation writes keep their current value. -/
theorem applyAll_cur_other (ops : List (Op V)) (d : Disk V) (b : Nat)
    (h : ∀ o ∈ ops, b ∉ o.writes) : (applyAll ops d b).cur = (d b).cur := by
  induction ops generalizing d with
  | nil => rfl
  | cons o ops ih =>
    simp only [applyAll_cons]
    rw [ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
    have hb := h o (List.mem_cons_self ..)
    cases o with
    | write a v =>
      simp [writes] at hb
      simp [apply, Disk.write_other _ _ hb]
    | sync => rfl

/-- A block that no operation writes and that was durable stays durable and unchanged. -/
theorem applyAll_other_durable (ops : List (Op V)) (d : Disk V) (b : Nat)
    (h : ∀ o ∈ ops, b ∉ o.writes) (hd : d.Durable b) : applyAll ops d b = d b := by
  induction ops generalizing d with
  | nil => rfl
  | cons o ops ih =>
    have hb := h o (List.mem_cons_self ..)
    have hrest : ∀ o' ∈ ops, b ∉ o'.writes := fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    simp only [applyAll_cons]
    cases o with
    | write a v =>
      simp [writes] at hb
      have this : (Op.write a v).apply d b = d b := Disk.write_other _ _ hb
      rw [ih _ hrest (by simp only [Disk.Durable, this]; exact hd), this]
    | sync =>
      have this : (Op.sync : Op V).apply d b = d b := by
        show (⟨(d b).cur, []⟩ : ValSet V) = d b
        simp only [Disk.Durable] at hd; cases h' : d b; simp_all
      rw [ih _ hrest (by simp only [Disk.Durable, this]; exact hd), this]

theorem mem_take_writes {ops : List (Op V)} {k : Nat} {o : Op V} (h : o ∈ ops.take k) :
    o ∈ ops := List.mem_of_mem_take h

end Op

end Crashproof
