import Crashproof.Writes

/-!
# Why the log is crash-safe

The proof has three layers.

1. *Address bookkeeping*: which blocks each phase writes (`logWrites_writes`,
   `installOps_writes`), and what the log slots and home blocks hold afterwards
   (`logEntries_logWrites`, `installOps_cur`).
2. *Three crash lemmas*, one per kind of intermediate state. They carry the weight:
   * `Idle.crash` — header durable and empty: recovery yields the data blocks as they are;
   * `crash_committed` — header durable and committing `t`, log slots durable: recovery
     yields `applyWrites t m` *whatever* the home blocks of `t` hold (they may be half
     installed or torn);
   * `crash_header_pending` — the header is being written: it decodes as the old or the
     new header (`Codec.decode_mix`), so recovery yields one of two states.
3. *Walking the operation list* (`AllPrefixes`): a crash leaves the disk after some prefix of
   `commitOps`; each prefix falls in one of the three kinds.
-/

namespace Crashproof

variable {V : Type}

/-! ## Crash conditions along a list of operations -/

/-- `G` holds after every prefix of `ops` run from `d`: wherever a crash strikes, `G`. -/
def AllPrefixes (G : Disk V → Prop) (ops : List (Op V)) (d : Disk V) : Prop :=
  ∀ k, G (Op.applyAll (ops.take k) d)

theorem AllPrefixes.append {G : Disk V → Prop} {A B : List (Op V)} {d : Disk V}
    (h1 : AllPrefixes G A d) (h2 : AllPrefixes G B (Op.applyAll A d)) :
    AllPrefixes G (A ++ B) d := by
  intro k
  rcases Op.take_append_cases A B k d with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj]; exact h1 j
  · rw [hj]; exact h2 j

theorem AllPrefixes.single {G : Disk V → Prop} {o : Op V} {d : Disk V} (h0 : G d)
    (h1 : G (o.apply d)) : AllPrefixes G [o] d := by
  intro k
  cases k with
  | zero => exact h0
  | succ k => simpa [Op.applyAll] using h1

theorem AllPrefixes.full {G : Disk V → Prop} {ops : List (Op V)} {d : Disk V}
    (h : AllPrefixes G ops d) : G (Op.applyAll ops d) := by
  have := h ops.length
  rwa [List.take_length] at this

theorem spec_run_prefixes {G : Disk V → Prop} {ops : List (Op V)} {d0 : Disk V}
    (h : AllPrefixes G ops d0) :
    Spec (fun d => d = d0) (Op.run ops) (fun _ d => d = Op.applyAll ops d0) G := by
  intro d r hd he
  subst hd
  rcases Op.exec_run he with rfl | ⟨k, rfl⟩
  · rfl
  · exact h k

/-! ## Address bookkeeping -/

theorem logWrites_writes {t : Txn V} {i b : Nat} {o : Op V} (ho : o ∈ logWrites t i)
    (hb : b ∈ o.writes) : i + 1 ≤ b ∧ b ≤ i + t.length := by
  induction t generalizing i with
  | nil => simp [logWrites] at ho
  | cons p t ih =>
    obtain ⟨a, v⟩ := p
    simp only [logWrites, List.mem_cons] at ho
    rcases ho with rfl | ho
    · simp [Op.writes] at hb; simp; omega
    · have := ih ho; simp; omega

theorem installOps_writes {L : Layout} {ws : List (Nat × V)} {b : Nat} {o : Op V}
    (ho : o ∈ installOps L ws) (hb : b ∈ o.writes) : ∃ a ∈ ws.map Prod.fst, b = L.home a := by
  simp only [installOps, List.mem_map] at ho
  obtain ⟨⟨a, v⟩, hmem, rfl⟩ := ho
  simp [Op.writes] at hb
  exact ⟨a, List.mem_map_of_mem hmem, hb⟩

theorem home_inj {L : Layout} {a b : Nat} (h : L.home a = L.home b) : a = b := by
  simp [Layout.home] at h; exact h

theorem home_gt (L : Layout) (a : Nat) : L.logLen < L.home a := by
  simp [Layout.home]; omega

theorem logEntries_keys (x : Nat → V) (l : List Nat) (i : Nat) :
    (logEntries x l i).map Prod.fst = l := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => simp [logEntries, ih]

theorem logEntries_congr {x y : Nat → V} {l : List Nat} {i : Nat}
    (h : ∀ b, i + 1 ≤ b → b ≤ i + l.length → x b = y b) : logEntries x l i = logEntries y l i := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    simp only [logEntries]
    rw [h (1 + i) (by omega) (by simp; omega), ih]
    intro b h1 h2
    exact h b (by omega) (by simp at h2 ⊢; omega)

/-- After step 1 the log slots hold the transaction. -/
theorem logEntries_logWrites (t : Txn V) (i : Nat) (d : Disk V) :
    logEntries (Op.applyAll (logWrites t i) d).curState (t.map Prod.fst) i = t := by
  induction t generalizing i d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, v⟩ := p
    simp only [logWrites, Op.applyAll_cons, List.map_cons, logEntries]
    have hcur : (Op.applyAll (logWrites t (i + 1)) ((Op.write (1 + i) v).apply d) (1 + i)).cur = v := by
      rw [Op.applyAll_cur_other]
      · simp [Op.apply]
      · intro o ho hb
        have := logWrites_writes ho hb
        omega
    simp only [Disk.curState] at ih ⊢
    rw [hcur, ih]

/-- After step 3 the home blocks hold the transaction's logical disk. -/
theorem installOps_cur (L : Layout) (ws : List (Nat × V)) (d : Disk V) (b : Nat) :
    (Op.applyAll (installOps L ws) d (L.home b)).cur =
      applyWrites ws (fun a => (d (L.home a)).cur) b := by
  induction ws generalizing d with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨a, v⟩ := p
    simp only [installOps, List.map_cons, Op.applyAll_cons] at ih ⊢
    rw [ih, applyWrites_cons]
    congr 1
    funext c
    by_cases hc : c = a
    · subst hc; simp [Op.apply]
    · have : L.home c ≠ L.home a := fun h => hc (home_inj h)
      simp [Op.apply, Disk.write_other _ _ this, upd_other _ _ hc]

/-! ## Decoding headers -/

section Codec
variable [Codec V]

theorem committed_eq {L : Layout} {h : V} {l : List Nat} (hd : Codec.decode h = some l)
    (hl : l.length ≤ L.logLen) : committed L h = l := by
  simp [committed, hd, hl]

theorem committed_congr {L : Layout} {h h' : V} (hd : Codec.decode h = Codec.decode h') :
    committed L h = committed L h' := by
  simp [committed, hd]

theorem decode_keys {L : Layout} {t : Txn V} (htx : TxnOK L t) :
    Codec.decode (Codec.encode (V := V) (t.map Prod.fst)) = some (t.map Prod.fst) := by
  apply Codec.decode_encode
  · simpa using htx.fits_header
  · intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact htx.addrs p hp

theorem decode_empty : Codec.decode (Codec.encode (V := V) []) = some [] :=
  Codec.decode_encode [] (by simp) (by simp)

/-- A header block being overwritten with `h` decodes like `h` or like the durable value. -/
theorem survives_write_hdr {d : Disk V} (hd : d.Durable 0) {h v : V}
    (hv : Survives (d.write 0 h 0) v) :
    Codec.decode v = Codec.decode h ∨ Codec.decode v = Codec.decode (d 0).cur := by
  obtain ⟨u, hu, he⟩ := survives_decode hv
  simp only [Disk.Durable] at hd
  simp [ValSet.vals, hd] at hu
  rcases hu with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

/-! ## The three crash lemmas -/

/-- An idle log crashes to its logical disk. -/
theorem Idle.crash {L : Layout} {m : Nat → V} {d : Disk V} {x : Nat → V} (h : Idle L m d)
    (hx : CrashesTo d x) : recovered L x = m := by
  have h0 : x 0 = (d 0).cur := crashesTo_durable hx h.hdr_durable
  have hc : committed L (x 0) = [] := by rw [h0]; exact committed_eq h.hdr_empty (by simp)
  funext a
  simp only [recovered, hc, logEntries, applyWrites_nil, Layout.data]
  rw [crashesTo_durable hx (h.data_durable a), h.data_cur a]

/-- Header durable and committing `t`, log slots durable and holding `t`, and the home
blocks of addresses outside `t` durable with `m`: recovery yields `applyWrites t m`. -/
theorem crash_committed {L : Layout} {t : Txn V} (htx : TxnOK L t) {d : Disk V} {m : Nat → V}
    {x : Nat → V} (hhdr : d.Durable 0)
    (hdec : Codec.decode (d 0).cur = some (t.map Prod.fst))
    (hlog : ∀ b, 1 ≤ b → b ≤ t.length → d.Durable b)
    (hent : logEntries d.curState (t.map Prod.fst) 0 = t)
    (hdata : ∀ a, a ∉ t.map Prod.fst → d.Durable (L.home a) ∧ (d (L.home a)).cur = m a)
    (hx : CrashesTo d x) : recovered L x = applyWrites t m := by
  have h0 : x 0 = (d 0).cur := crashesTo_durable hx hhdr
  have hc : committed L (x 0) = t.map Prod.fst := by
    rw [h0]; exact committed_eq hdec (by simpa using htx.fits_log)
  have hlx : logEntries x (t.map Prod.fst) 0 = t := by
    refine (logEntries_congr ?_).trans hent
    intro b h1 h2
    simp at h2
    exact crashesTo_durable hx (hlog b (by omega) (by omega))
  simp only [recovered, hc, hlx]
  apply applyWrites_congr
  intro a ha
  simp only [Layout.data]
  rw [crashesTo_durable hx (hdata a ha).1, (hdata a ha).2]

/-- The header is pending between "empty" and "committing `t`", everything else is
durable: recovery yields the old or the new logical disk. -/
theorem crash_header_pending {L : Layout} {t : Txn V} (htx : TxnOK L t) {d : Disk V}
    {m : Nat → V} {x : Nat → V}
    (hhdr : ∀ v, Survives (d 0) v →
      Codec.decode v = some [] ∨ Codec.decode v = some (t.map Prod.fst))
    (hlog : ∀ b, 1 ≤ b → b ≤ t.length → d.Durable b)
    (hent : logEntries d.curState (t.map Prod.fst) 0 = t)
    (hdata : ∀ a, d.Durable (L.home a) ∧ (d (L.home a)).cur = m a)
    (hx : CrashesTo d x) : recovered L x = m ∨ recovered L x = applyWrites t m := by
  have hlx : logEntries x (t.map Prod.fst) 0 = t := by
    refine (logEntries_congr ?_).trans hent
    intro b h1 h2
    simp at h2
    exact crashesTo_durable hx (hlog b (by omega) (by omega))
  have hdx : L.data x = m := by
    funext a
    simp only [Layout.data]
    rw [crashesTo_durable hx (hdata a).1, (hdata a).2]
  rcases hhdr (x 0) (hx 0) with he | hk
  · left
    simp only [recovered, committed_eq he (by simp), logEntries, applyWrites_nil, hdx]
  · right
    simp only [recovered, committed_eq hk (by simpa using htx.fits_log), hlx, hdx]

/-! ## Idle states -/

theorem Idle.sync {L : Layout} {m : Nat → V} {d : Disk V} (h : Idle L m d) : Idle L m d.sync where
  hdr_durable := rfl
  hdr_empty := h.hdr_empty
  data_durable _ := rfl
  data_cur a := h.data_cur a

/-- Operations confined to the log slots keep an idle log idle. -/
theorem Idle.untouched {L : Layout} {m : Nat → V} {d : Disk V} {ops : List (Op V)}
    (h : Idle L m d) (hops : ∀ o ∈ ops, ∀ b ∈ o.writes, 1 ≤ b ∧ b ≤ L.logLen) :
    Idle L m (Op.applyAll ops d) := by
  have h0 : Op.applyAll ops d 0 = d 0 :=
    Op.applyAll_other_durable ops d 0 (fun o ho hb => by have := hops o ho 0 hb; omega)
      h.hdr_durable
  have hh : ∀ a, Op.applyAll ops d (L.home a) = d (L.home a) := fun a =>
    Op.applyAll_other_durable ops d _
      (fun o ho hb => by have := hops o ho _ hb; have := home_gt L a; omega) (h.data_durable a)
  exact {
    hdr_durable := by simp only [Disk.Durable, h0]; exact h.hdr_durable
    hdr_empty := by rw [h0]; exact h.hdr_empty
    data_durable := fun a => by simp only [Disk.Durable, hh]; exact h.data_durable a
    data_cur := fun a => by rw [hh]; exact h.data_cur a }

/-! ## Commit -/

/-- The crash condition of `commit`: whatever the platter holds, recovery yields the old or
the new logical disk. -/
def CommitCrash (L : Layout) (m m' : Nat → V) (d : Disk V) : Prop :=
  ∀ x, CrashesTo d x → recovered L x = m ∨ recovered L x = m'

theorem commit_prefixes {L : Layout} {t : Txn V} (htx : TxnOK L t) {m : Nat → V} {d : Disk V}
    (hidle : Idle L m d) :
    AllPrefixes (CommitCrash L m (applyWrites t m)) (commitOps L t) d ∧
      Idle L (applyWrites t m) (Op.applyAll (commitOps L t) d) := by
  -- names for the states between the phases
  let keys := t.map Prod.fst
  let H : V := Codec.encode keys
  let E : V := Codec.encode []
  let m' := applyWrites t m
  let d1 := Op.applyAll (logWrites t 0) d
  have hklen : keys.length = t.length := by simp [keys]
  let d2 := d1.sync
  let d3 := d2.write 0 H
  let d4 := d3.sync
  let d5 := Op.applyAll (installOps L t) d4
  let d6 := d5.sync
  let d7 := d6.write 0 E
  let d8 := d7.sync
  have hlogw : ∀ o ∈ logWrites t 0, ∀ b ∈ o.writes, 1 ≤ b ∧ b ≤ L.logLen := by
    intro o ho b hb
    have := logWrites_writes ho hb
    have := htx.fits_log
    omega
  -- phase 1: the log slots fill up while the header stays empty
  have i1 : Idle L m d1 := hidle.untouched hlogw
  have i2 : Idle L m d2 := i1.sync
  have ent2 : logEntries d2.curState keys 0 = t := logEntries_logWrites t 0 d
  have log2 : ∀ b, 1 ≤ b → b ≤ t.length → d2.Durable b := fun _ _ _ => rfl
  -- phase 2: the commit point
  have ent3 : logEntries d3.curState keys 0 = t := by
    refine (logEntries_congr ?_).trans ent2; intro b hb _
    simp [d3, Disk.curState, Disk.write_other _ _ (show b ≠ 0 by omega)]
  have log3 : ∀ b, 1 ≤ b → b ≤ t.length → d3.Durable b := fun b hb _ => by
    simp only [Disk.Durable, d3, Disk.write_other _ _ (show b ≠ 0 by omega)]; rfl
  have data3 : ∀ a, d3.Durable (L.home a) ∧ (d3 (L.home a)).cur = m a := fun a => by
    have hne : L.home a ≠ 0 := by simp [Layout.home]
    simp only [Disk.Durable, d3, Disk.write_other _ _ hne]
    exact ⟨i2.data_durable a, i2.data_cur a⟩
  have hdr3 : ∀ v, Survives (d3 0) v →
      Codec.decode v = some [] ∨ Codec.decode v = some keys := by
    intro v hv
    rcases survives_write_hdr i2.hdr_durable hv with h | h
    · exact Or.inr (h.trans (decode_keys htx))
    · exact Or.inl (h.trans i2.hdr_empty)
  have hdr4 : Codec.decode (d4 0).cur = some keys := by
    simp only [d4, d3, Disk.sync_apply, Disk.write_same]; exact decode_keys htx
  have ent4 : logEntries d4.curState keys 0 = t := ent3
  -- phase 3: install
  have inst : ∀ j, let dj := Op.applyAll ((installOps L t).take j) d4
      dj.Durable 0 ∧ dj 0 = d4 0 ∧ (∀ b, 1 ≤ b → b ≤ t.length → dj.Durable b ∧ dj b = d4 b) ∧
      (∀ a, a ∉ keys → dj.Durable (L.home a) ∧ dj (L.home a) = d4 (L.home a)) := by
    intro j
    have hw : ∀ o ∈ (installOps L t).take j, ∀ b ∈ o.writes, ∃ a ∈ keys, b = L.home a :=
      fun o ho b hb => installOps_writes (List.mem_of_mem_take ho) hb
    have h0 : Op.applyAll ((installOps L t).take j) d4 0 = d4 0 :=
      Op.applyAll_other_durable _ d4 0 (fun o ho hb => by
        obtain ⟨a, _, h⟩ := hw o ho 0 hb; have := home_gt L a; omega) rfl
    refine ⟨?_, h0, ?_, ?_⟩
    · simp only [Disk.Durable, h0]; rfl
    · intro b h1 h2
      have hne : ∀ o ∈ (installOps L t).take j, b ∉ o.writes := fun o ho hb => by
        obtain ⟨a, _, h⟩ := hw o ho b hb
        have := home_gt L a; have := htx.fits_log; omega
      have := Op.applyAll_other_durable _ d4 b hne rfl
      exact ⟨by simp only [Disk.Durable, this]; rfl, this⟩
    · intro a ha
      have hne : ∀ o ∈ (installOps L t).take j, L.home a ∉ o.writes := fun o ho hb => by
        obtain ⟨c, hc, h⟩ := hw o ho _ hb
        rw [home_inj h] at ha; exact ha hc
      have := Op.applyAll_other_durable _ d4 _ hne rfl
      exact ⟨by simp only [Disk.Durable, this]; rfl, this⟩
  have crashInst : ∀ j, CommitCrash L m m' (Op.applyAll ((installOps L t).take j) d4) := by
    intro j x hx
    obtain ⟨hd0, he0, hlog, hdata⟩ := inst j
    right
    refine crash_committed htx hd0 (by rw [he0]; exact hdr4) (fun b h1 h2 => (hlog b h1 h2).1)
      ?_ (fun a ha => ⟨(hdata a ha).1, by rw [(hdata a ha).2]; exact (data3 a).2⟩) hx
    refine (logEntries_congr ?_).trans ent4; intro b h1 h2
    simp at h2
    simp only [Disk.curState, ((hlog b (by omega) (by omega)).2)]
  have d5eq : d5 = Op.applyAll ((installOps L t).take (installOps L t).length) d4 := by
    rw [List.take_length]
  have cur5 : ∀ a, (d5 (L.home a)).cur = m' a := by
    intro a
    simp only [d5, installOps_cur]
    congr 1
    funext c
    exact (data3 c).2
  obtain ⟨d5h0, d5e0, d5log, _⟩ := inst (installOps L t).length
  rw [← d5eq] at d5h0 d5e0 d5log
  have ent6 : logEntries d6.curState keys 0 = t := by
    refine (logEntries_congr ?_).trans ent4; intro b h1 h2
    simp at h2
    simp only [d6, Disk.curState, Disk.sync_apply, (d5log b (by omega) (by omega)).2]
  -- phase 4: retire the header
  have hdr7 : ∀ v, Survives (d7 0) v →
      Codec.decode v = some [] ∨ Codec.decode v = some keys := by
    intro v hv
    rcases survives_write_hdr (d := d6) rfl hv with h | h
    · exact Or.inl (h.trans decode_empty)
    · refine Or.inr (h.trans ?_)
      simp only [d6, Disk.sync_apply, d5e0]; exact hdr4
  have data7 : ∀ a, d7.Durable (L.home a) ∧ (d7 (L.home a)).cur = m' a := fun a => by
    have hne : L.home a ≠ 0 := by simp [Layout.home]
    simp only [Disk.Durable, d7, Disk.write_other _ _ hne]
    exact ⟨rfl, cur5 a⟩
  have ent7 : logEntries d7.curState keys 0 = t := by
    refine (logEntries_congr ?_).trans ent6; intro b hb _
    simp [d7, Disk.curState, Disk.write_other _ _ (show b ≠ 0 by omega)]
  have log7 : ∀ b, 1 ≤ b → b ≤ t.length → d7.Durable b := fun b hb _ => by
    simp only [Disk.Durable, d7, Disk.write_other _ _ (show b ≠ 0 by omega)]; rfl
  have i8 : Idle L m' d8 := {
    hdr_durable := rfl
    hdr_empty := by simp only [d8, d7, Disk.sync_apply, Disk.write_same]; exact decode_empty
    data_durable := fun _ => rfl
    data_cur := fun a => (data7 a).2 }
  -- the crash condition at each state
  have c_idle : ∀ {e}, Idle L m e → CommitCrash L m m' e := fun h x hx => Or.inl (h.crash hx)
  have c3 : CommitCrash L m m' d3 := fun x hx =>
    crash_header_pending htx hdr3 log3 ent3 data3 hx
  have c4 : CommitCrash L m m' d4 := by simpa using crashInst 0
  have c5 : CommitCrash L m m' d5 := by rw [d5eq]; exact crashInst _
  have c6 : CommitCrash L m m' d6 := by
    intro x hx
    right
    refine crash_committed (d := d6) htx rfl (by simp only [d6, Disk.sync_apply, d5e0]; exact hdr4)
      (fun _ _ _ => rfl) ent6 (fun a _ => ⟨rfl, ?_⟩) hx
    simp only [d6, Disk.sync_apply]
    rw [cur5]
    exact (applyWrites_not_mem ‹_› m)
  have c7 : CommitCrash L m m' d7 := by
    intro x hx
    right
    rcases crash_header_pending htx hdr7 log7 ent7 data7 hx with h | h
    · exact h
    · rw [h]; exact applyWrites_idem t m
  have c8 : CommitCrash L m m' d8 := fun x hx => Or.inr (i8.crash hx)
  refine ⟨?_, ?_⟩
  · simp only [commitOps, List.append_assoc]
    refine AllPrefixes.append (fun k => c_idle (hidle.untouched fun o ho => hlogw o
      (List.mem_of_mem_take ho))) ?_
    refine AllPrefixes.append (AllPrefixes.single (c_idle i1) (c_idle i2)) ?_
    refine AllPrefixes.append (AllPrefixes.single (c_idle i2) c3) ?_
    refine AllPrefixes.append (AllPrefixes.single c3 c4) ?_
    refine AllPrefixes.append crashInst ?_
    refine AllPrefixes.append (AllPrefixes.single c5 c6) ?_
    refine AllPrefixes.append (AllPrefixes.single c6 c7) ?_
    exact AllPrefixes.single c7 c8
  · simp only [commitOps, Op.applyAll_append]
    exact i8

/-- **Commit, as a Crash Hoare Logic triple.** From an idle log with logical disk `m`,
`commit` ends idle with `applyWrites t m`; if it crashes, every platter state the crash can
leave recovers to `m` or to `applyWrites t m`. -/
theorem commit_spec {L : Layout} {t : Txn V} (htx : TxnOK L t) (m : Nat → V) :
    Spec (Idle L m) (commit L t) (fun _ => Idle L (applyWrites t m))
      (CommitCrash L m (applyWrites t m)) := by
  intro d r hidle he
  cases t with
  | nil =>
    cases he with
    | ret => exact hidle
    | crash => exact fun x hx => Or.inl (hidle.crash hx)
  | cons p t' =>
    obtain ⟨hpre, hpost⟩ := commit_prefixes htx hidle
    have := spec_run_prefixes hpre d r rfl he
    cases r with
    | done d' a => simp only at this; subst this; exact hpost
    | crashed d' => exact this

/-! ## Recovery -/

theorem readLog_spec (D : Disk V) (l : List Nat) (i : Nat) :
    Spec (fun d => d = D) (readLog l i) (fun es d => d = D ∧ es = logEntries D.curState l i)
      (fun d => d = D) := by
  induction l generalizing i with
  | nil => exact spec_ret (fun d h => ⟨h, rfl⟩) (fun _ h => h)
  | cons a l ih =>
    apply spec_read (fun _ h => h)
    intro v d r ⟨hd, hv⟩ he
    subst hd; subst hv
    exact spec_bind (ih (i + 1)) (fun es => spec_ret (fun d' h' => ⟨h'.1, by rw [h'.2]; rfl⟩)
      (fun d' h' => h'.1)) d r rfl he

/-- The crash condition of recovery: a crash changes nothing that matters. -/
def RecoverCrash (L : Layout) (x : Nat → V) (d : Disk V) : Prop :=
  ∀ x', CrashesTo d x' → recovered L x' = recovered L x

theorem recover_prefixes (L : Layout) (x : Nat → V) :
    let es := logEntries x (committed L (x 0)) 0
    AllPrefixes (RecoverCrash L x) (recoverOps L es) (Disk.ofState x) ∧
      Idle L (recovered L x) (Op.applyAll (recoverOps L es) (Disk.ofState x)) := by
  intro es
  let l := committed L (x 0)
  let r := recovered L x
  let D := Disk.ofState x
  let E : V := Codec.encode []
  have hl : l.length ≤ L.logLen := by
    simp only [l, committed]
    split
    · split <;> simp_all
    · simp
  have hkeys : es.map Prod.fst = l := logEntries_keys x l 0
  have hw : ∀ j, ∀ o ∈ (installOps L es).take j, ∀ b ∈ o.writes, ∃ a ∈ l, b = L.home a := by
    intro j o ho b hb
    rw [← hkeys]; exact installOps_writes (List.mem_of_mem_take ho) hb
  -- during the replay: header and log untouched, homes outside `l` untouched
  have crashInst : ∀ j, RecoverCrash L x (Op.applyAll ((installOps L es).take j) D) := by
    intro j x' hx'
    let dj := Op.applyAll ((installOps L es).take j) D
    have keep : ∀ b, (∀ a ∈ l, b ≠ L.home a) → x' b = x b := by
      intro b hb
      have := Op.applyAll_other_durable ((installOps L es).take j) D b
        (fun o ho hbo => by obtain ⟨a, ha, h⟩ := hw j o ho b hbo; exact hb a ha h) rfl
      have h2 : dj.Durable b := by simp only [Disk.Durable, dj, this]; rfl
      rw [crashesTo_durable hx' h2]; simp only [dj, this]; rfl
    have h0 : x' 0 = x 0 := keep 0 (fun a _ h => by simp [Layout.home] at h; omega)
    have hl' : committed L (x' 0) = l := by rw [h0]
    have hes : logEntries x' l 0 = es := by
      apply logEntries_congr
      intro b h1 h2
      apply keep b
      intro a _ h
      have := home_gt L a
      simp at h2
      omega
    simp only [RecoverCrash, recovered, hl', hes]
    show applyWrites es (L.data x') = applyWrites es (L.data x)
    apply applyWrites_congr
    intro a ha
    rw [hkeys] at ha
    exact keep _ (fun c hc h => ha (by rw [home_inj h]; exact hc))
  let d5 := Op.applyAll (installOps L es) D
  have d5eq : d5 = Op.applyAll ((installOps L es).take (installOps L es).length) D := by
    rw [List.take_length]
  have d5other : ∀ b, (∀ a ∈ l, b ≠ L.home a) → d5 b = D b := fun b hb =>
    Op.applyAll_other_durable _ D b (fun o ho hbo => by
      obtain ⟨a, ha, h⟩ := hw (installOps L es).length o
        (by rw [List.take_length]; exact ho) b hbo
      exact hb a ha h) rfl
  have cur5 : ∀ a, (d5 (L.home a)).cur = r a := by
    intro a; simp only [d5, installOps_cur]; rfl
  let d6 := d5.sync
  let d7 := d6.write 0 E
  let d8 := d7.sync
  have hlog7 : ∀ b, 1 ≤ b → b ≤ L.logLen → d7 b = ⟨x b, []⟩ := by
    intro b h1 h2
    simp only [d7, Disk.write_other _ _ (show b ≠ 0 by omega), d6, Disk.sync_apply]
    rw [d5other b (fun a _ h => by have := home_gt L a; omega)]
    rfl
  have c7 : RecoverCrash L x d7 := by
    intro x' hx'
    have hlx : logEntries x' l 0 = es := by
      apply logEntries_congr
      intro b h1 h2
      simp at h2
      have := hlog7 b (by omega) (by omega)
      have := crashesTo_durable (a := b) hx' (by simp [Disk.Durable, this])
      rw [this, hlog7 b (by omega) (by omega)]
    have hdx : L.data x' = r := by
      funext a
      have hne : L.home a ≠ 0 := by simp [Layout.home]
      have h7 : d7 (L.home a) = ⟨(d5 (L.home a)).cur, []⟩ := by
        simp only [d7, Disk.write_other _ _ hne, d6, Disk.sync_apply]
      simp only [Layout.data]
      rw [crashesTo_durable hx' (by simp [Disk.Durable, h7]), h7, cur5]
    have hd0 : d6 0 = ⟨x 0, []⟩ := by
      simp only [d6, Disk.sync_apply, d5other 0 (fun a _ h => by simp [Layout.home] at h; omega)]
      rfl
    rcases survives_write_hdr (d := d6) (by simp [Disk.Durable, hd0]) (hx' 0) with h | h
    · -- the empty header reached the platter
      have : committed L (x' 0) = [] := committed_eq (h.trans decode_empty) (by simp)
      simp only [recovered, this, logEntries, applyWrites_nil, hdx]
      rfl
    · -- the old header is still there: replaying it again changes nothing
      rw [hd0] at h
      have : committed L (x' 0) = l := committed_congr h
      simp only [recovered, this, hlx, hdx]
      exact applyWrites_idem es (L.data x)
  have i8 : Idle L r d8 := {
    hdr_durable := rfl
    hdr_empty := by simp only [d8, d7, Disk.sync_apply, Disk.write_same]; exact decode_empty
    data_durable := fun _ => rfl
    data_cur := fun a => by
      have hne : L.home a ≠ 0 := by simp [Layout.home]
      simp only [d8, d7, Disk.sync_apply, Disk.write_other _ _ hne, d6]
      exact cur5 a }
  have c8 : RecoverCrash L x d8 := fun x' hx' => i8.crash hx'
  have c5 : RecoverCrash L x d5 := by rw [d5eq]; exact crashInst _
  have c6 : RecoverCrash L x d6 := by
    intro x' hx'
    have h7 := c7 x'
    -- a crash at d6 can leave only what a crash at d7 could have left with the old header
    apply h7
    intro b
    by_cases hb : b = 0
    · subst hb
      refine Or.inl ?_
      have := survives_durable (s := d6 0) rfl (hx' 0)
      simp [d7, ValSet.vals, this]
    · simp only [d7, Disk.write_other _ _ hb]; exact hx' b
  refine ⟨?_, ?_⟩
  · simp only [recoverOps, List.append_assoc]
    refine AllPrefixes.append crashInst ?_
    refine AllPrefixes.append (AllPrefixes.single c5 c6) ?_
    refine AllPrefixes.append (AllPrefixes.single c6 c7) ?_
    exact AllPrefixes.single c7 c8
  · simp only [recoverOps, Op.applyAll_append]
    exact i8

/-- **Recovery, as a Crash Hoare Logic triple.** Started on any platter state `x`, recovery
ends idle with logical disk `recovered L x`; if it crashes, every platter state the crash
can leave has the same `recovered` value, so running recovery again is safe. -/
theorem recover_spec (L : Layout) (x : Nat → V) :
    Spec (fun d => d = Disk.ofState x) (recover L) (fun _ => Idle L (recovered L x))
      (RecoverCrash L x) := by
  obtain ⟨hpre, hpost⟩ := recover_prefixes L x
  apply spec_read
  · intro d hd x' hx'
    subst hd
    rw [crashesTo_ofState hx']
  · intro v d r ⟨hd, hv⟩ he
    subst hd
    simp only [Disk.ofState_apply] at hv
    subst hv
    refine spec_bind (spec_conseq (readLog_spec (Disk.ofState x) _ 0) (fun d hd => hd)
      (fun _ _ h => h) (fun d hd x' hx' => by subst hd; rw [crashesTo_ofState hx']))
      ?_ (Disk.ofState x) r rfl he
    intro es d r ⟨hd, hes⟩ he
    subst hd; subst hes
    have := spec_run_prefixes hpre _ r rfl he
    cases r with
    | done d' a => simp only at this; subst this; exact hpost
    | crashed d' => exact this

end Codec

end Crashproof
