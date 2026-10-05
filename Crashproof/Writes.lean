import Crashproof.Log

/-! Facts about `applyWrites` and in-memory transactions. -/

namespace Crashproof

variable {V : Type}

@[simp] theorem upd_same (m : Nat → V) (a : Nat) (v : V) : upd m a v a = v := by simp [upd]

theorem upd_other (m : Nat → V) {a b : Nat} (v : V) (h : b ≠ a) : upd m a v b = m b := by
  simp [upd, h]

@[simp] theorem applyWrites_nil (m : Nat → V) : applyWrites [] m = m := rfl

@[simp] theorem applyWrites_cons (a : Nat) (v : V) (ws : List (Nat × V)) (m : Nat → V) :
    applyWrites ((a, v) :: ws) m = applyWrites ws (upd m a v) := rfl

/-- Addresses the writes do not mention keep their value. -/
theorem applyWrites_not_mem {ws : List (Nat × V)} {b : Nat} (h : b ∉ ws.map Prod.fst)
    (m : Nat → V) : applyWrites ws m b = m b := by
  induction ws generalizing m with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨a, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyWrites_cons, ih h.2, upd_other _ _ h.1]

/-- Writes overwrite everything they mention: what the starting maps held at those
addresses does not matter. -/
theorem applyWrites_congr {ws : List (Nat × V)} {m₁ m₂ : Nat → V}
    (h : ∀ b, b ∉ ws.map Prod.fst → m₁ b = m₂ b) : applyWrites ws m₁ = applyWrites ws m₂ := by
  induction ws generalizing m₁ m₂ with
  | nil => funext b; exact h b (by simp)
  | cons p ws ih =>
    obtain ⟨a, v⟩ := p
    simp only [applyWrites_cons]
    apply ih
    intro b hb
    by_cases hba : b = a
    · subst hba; simp
    · rw [upd_other _ _ hba, upd_other _ _ hba]
      apply h
      simp [hba, hb]

/-- **Replay is idempotent.** -/
theorem applyWrites_idem (ws : List (Nat × V)) (m : Nat → V) :
    applyWrites ws (applyWrites ws m) = applyWrites ws m :=
  applyWrites_congr (fun _ hb => applyWrites_not_mem hb m)

theorem applyWrites_away {ws : List (Nat × V)} {m₁ m₂ : Nat → V} {a b : Nat}
    (hm : ∀ c, c ≠ a → m₁ c = m₂ c) (hb : b ≠ a) : applyWrites ws m₁ b = applyWrites ws m₂ b := by
  induction ws generalizing m₁ m₂ with
  | nil => exact hm b hb
  | cons p ws ih =>
    obtain ⟨c, v⟩ := p
    simp only [applyWrites_cons]
    apply ih
    intro e he
    by_cases hec : e = c
    · subst hec; simp
    · rw [upd_other _ _ hec, upd_other _ _ hec]; exact hm e he

theorem applyWrites_filter (ws : List (Nat × V)) {a b : Nat} (hb : b ≠ a) (m : Nat → V) :
    applyWrites (ws.filter fun p => p.1 ≠ a) m b = applyWrites ws m b := by
  induction ws generalizing m with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨c, v⟩ := p
    by_cases hc : c = a
    · subst hc
      have : (((c, v) :: ws).filter fun p => p.1 ≠ c) = ws.filter fun p => p.1 ≠ c := by
        simp
      rw [this, ih, applyWrites_cons]
      exact applyWrites_away (fun e he => (upd_other _ _ he).symm) hb
    · have : (((c, v) :: ws).filter fun p => p.1 ≠ a) = (c, v) :: ws.filter fun p => p.1 ≠ a := by
        simp [hc]
      rw [this, applyWrites_cons, applyWrites_cons, ih]

theorem not_mem_filter_keys (t : Txn V) (a : Nat) :
    a ∉ (t.filter fun p => p.1 ≠ a).map Prod.fst := by
  simp

/-- **Meaning of `put`**: the transaction's logical disk gets the new value at `a`. -/
theorem put_meaning (t : Txn V) (a : Nat) (v : V) (m : Nat → V) :
    applyWrites (t.put a v) m = upd (applyWrites t m) a v := by
  funext b
  simp only [Txn.put, applyWrites_cons]
  by_cases hb : b = a
  · subst hb
    rw [applyWrites_not_mem (not_mem_filter_keys t b), upd_same, upd_same]
  · rw [applyWrites_filter _ hb, upd_other _ _ hb]
    exact applyWrites_away (fun c hc => upd_other _ _ hc) hb

theorem put_nodup {t : Txn V} (h : (t.map Prod.fst).Nodup) (a : Nat) (v : V) :
    ((t.put a v).map Prod.fst).Nodup := by
  simp only [Txn.put, List.map_cons, List.nodup_cons]
  refine ⟨not_mem_filter_keys t a, ?_⟩
  exact h.sublist ((List.filter_sublist).map _)

/-- With each address at most once, the first match is the value the writes leave. -/
theorem find?_meaning {t : Txn V} (h : (t.map Prod.fst).Nodup) (a : Nat) (m : Nat → V) :
    applyWrites t m a = (t.find? a).getD (m a) := by
  induction t generalizing m with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨b, w⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [applyWrites_cons, Txn.find?]
    by_cases hb : b = a
    · subst hb
      rw [applyWrites_not_mem h.1]
      simp
    · rw [ih h.2]
      simp [hb, upd_other _ _ (Ne.symm hb)]

end Crashproof
