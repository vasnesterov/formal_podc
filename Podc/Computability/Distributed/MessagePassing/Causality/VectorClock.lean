import Podc.Computability.Distributed.MessagePassing.Causality.MergeAlg

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/Causality/VectorClock.lean

/-!
# Vector clocks (Fidge, Mattern)

The standard vector clock algorithm as a merge-and-update algorithm (`vcAlg`): each process
keeps a vector of naturals indexed by processes, merges (pointwise max) the vector piggybacked on
each received message and increments its own entry at each event.

* `vc_self`: `vc e (proc e) = index(e)`.
* `vc_witness`: every nonzero entry `vc f p` is the index of an event of `p` in the causal past
  of `f`.
* `idx_le_vc_iff`: for `e` at `p`, `index(e) ≤ vc f p ↔ (e = f ∨ e → f)` — the fundamental
  property used to read causality off vector clocks.
* `vc_captures`: vector clocks are distinct and `e → f ↔ vc e < vc f`;
  `vectorClock_isOnline`: they form an online timestamping algorithm on every graph.
-/

namespace Cslib.Causality

variable {P : Type*} [DecidableEq P]

/-- The standard vector clock algorithm. -/
def vcAlg (P : Type*) [DecidableEq P] : MergeAlg P (P → ℕ) where
  init := 0
  upd _ a x := x + Pi.single a.proc 1

namespace Exec

/-- The vector clock of event `i`. -/
def vc (ex : Exec P) (i : ℕ) : P → ℕ := (vcAlg P).ts ex i

variable {ex : Exec P}

lemma vc_eq {j : ℕ} {a : Act P} (hj : ex[j]? = some a) :
    ex.vc j = (vcAlg P).merged ex j + Pi.single a.proc 1 :=
  (vcAlg P).ts_eq ex hj

lemma vc_of_length_le {j : ℕ} (hj : ex.length ≤ j) : ex.vc j = 0 :=
  (vcAlg P).ts_of_length_le ex hj

lemma vcAlg_lt (j : ℕ) (a : Act P) (x : P → ℕ) : x < (vcAlg P).upd j a x := by
  simp only [vcAlg]
  refine Pi.lt_def.2 ⟨fun i => by simp, a.proc, by simp⟩

lemma vc_mono (hwf : ex.WF) {i j : ℕ} (h : ex.HBeq i j) : ex.vc i ≤ ex.vc j :=
  MergeAlg.hbeq_le hwf (fun j a x => (vcAlg_lt j a x).le) h

lemma vc_lt_of_hb (hwf : ex.WF) {i j : ℕ} (h : ex.HB i j) : ex.vc i < ex.vc j :=
  MergeAlg.hb_lt hwf vcAlg_lt h

/-- Each entry of the merged vector is `0` or comes from an immediate predecessor. -/
lemma merged_cases (hwf : ex.WF) (j : ℕ) (p : P) :
    (vcAlg P).merged ex j p = 0 ∨ ∃ k, ex.Step k j ∧ (vcAlg P).merged ex j p = ex.vc k p := by
  have hin : (vcAlg P).inVal ex j p = 0 ∨ ∃ k, ex.Step k j ∧ (vcAlg P).inVal ex j p = ex.vc k p := by
    unfold MergeAlg.inVal
    cases h : ex.prev j with
    | none => left; rfl
    | some k => exact Or.inr ⟨k, .po h, rfl⟩
  unfold MergeAlg.merged
  match hjm : ex[j]? with
  | some (.recv q m) =>
    simp only [Pi.sup_apply, hwf.recv_lt hjm, ite_true]
    change max _ (ex.vc m p) = 0 ∨ ∃ k, ex.Step k j ∧ max _ (ex.vc m p) = ex.vc k p
    rcases le_total ((vcAlg P).inVal ex j p) (ex.vc m p) with h | h
    · rw [max_eq_right h]
      exact Or.inr ⟨m, .msg hjm, rfl⟩
    · rw [max_eq_left h]
      exact hin
  | some (.send _ _) => exact hin
  | some (.comp _) => exact hin
  | none => exact hin

lemma inVal_le_merged_apply (j : ℕ) (p : P) :
    (vcAlg P).inVal ex j p ≤ (vcAlg P).merged ex j p :=
  (MergeAlg.inVal_le_merged (A := vcAlg P) ex j) p

/-- The two basic vector clock invariants, by strong induction. -/
lemma vc_main (hwf : ex.WF) (j : ℕ) :
    (∀ p, ex.procAt j = some p → ex.vc j p = ex.idx j) ∧
      ∀ p, ex.vc j p ≠ 0 → ∃ y, ex.HBeq y j ∧ ex.procAt y = some p ∧ ex.idx y = ex.vc j p := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjl : j < ex.length
    swap
    · refine ⟨fun p hp => absurd (lt_length_of_procAt hp) hjl, fun p hp => ?_⟩
      simp [vc_of_length_le (not_lt.1 hjl)] at hp
    set a := ex[j] with ha
    have hj : ex[j]? = some a := List.getElem?_eq_getElem hjl
    have hpj : ex.procAt j = some a.proc := procAt_of_get hj
    -- the merged entry at the own process
    have hown : (vcAlg P).merged ex j a.proc = (ex.prev j).elim 0 ex.idx := by
      apply le_antisymm
      · rcases merged_cases hwf j a.proc with h | ⟨k, hk, h⟩
        · rw [h]; exact Nat.zero_le _
        · rw [h]
          by_cases h0 : ex.vc k a.proc = 0
          · rw [h0]; exact Nat.zero_le _
          obtain ⟨y, hy, hyp, hyi⟩ := (ih k (hk.lt hwf)).2 a.proc h0
          have hyj : y < j := (hy.le hwf).trans_lt (hk.lt hwf)
          obtain ⟨i', hi', hle⟩ := exists_prev_of_lt hyj hyp hpj
          rw [hi', ← hyi]
          obtain ⟨h1, -, h3, -⟩ := prev_spec hi'
          exact (idx_le_idx_iff hyp (h3.trans hpj)).2 hle
      · cases h : ex.prev j with
        | none => exact Nat.zero_le _
        | some i' =>
          refine le_trans ?_ (inVal_le_merged_apply j a.proc)
          obtain ⟨h1, -, h3, -⟩ := prev_spec h
          simp only [MergeAlg.inVal, h, Option.elim]
          exact ((ih i' h1).1 a.proc (h3.trans hpj)).ge
    have hself : ex.vc j a.proc = ex.idx j := by
      rw [vc_eq hj, Pi.add_apply, hown, Pi.single_eq_same]
      cases h : ex.prev j with
      | none => simp [idx_of_prev_none hpj h]
      | some i' => simp [idx_prev h]
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [hpj] at hp
      cases hp
      exact hself
    · by_cases hpa : p = a.proc
      · subst hpa
        exact ⟨j, HBeq.refl _, hpj, hself.symm⟩
      · have hvm : ex.vc j p = (vcAlg P).merged ex j p := by
          rw [vc_eq hj, Pi.add_apply, Pi.single_eq_of_ne hpa, add_zero]
        rw [hvm] at hp ⊢
        rcases merged_cases hwf j p with h | ⟨k, hk, h⟩
        · exact absurd h hp
        · rw [h] at hp ⊢
          obtain ⟨y, hy, hyp, hyi⟩ := (ih k (hk.lt hwf)).2 p hp
          exact ⟨y, Or.inr (hy.trans_hb (.of_step hk)), hyp, hyi⟩

lemma vc_self (hwf : ex.WF) {j : ℕ} {p : P} (hp : ex.procAt j = some p) : ex.vc j p = ex.idx j :=
  (vc_main hwf j).1 p hp

lemma vc_witness (hwf : ex.WF) {j : ℕ} {p : P} (hp : ex.vc j p ≠ 0) :
    ∃ y, ex.HBeq y j ∧ ex.procAt y = some p ∧ ex.idx y = ex.vc j p :=
  (vc_main hwf j).2 p hp

/-- The fundamental property of vector clocks: for an event `e` of `p`,
`index(e) ≤ vc(f)[p] ↔ e = f ∨ e → f`. -/
theorem idx_le_vc_iff (hwf : ex.WF) {e f : ℕ} {p : P} (he : ex.procAt e = some p) :
    ex.idx e ≤ ex.vc f p ↔ ex.HBeq e f := by
  constructor
  · intro h
    have h0 : ex.vc f p ≠ 0 := by have := pos_of_idx he; omega
    obtain ⟨y, hy, hyp, hyi⟩ := vc_witness hwf h0
    rw [← hyi, idx_le_idx_iff he hyp] at h
    exact (hbeq_of_le h he hyp).trans hy
  · intro h
    rw [← vc_self hwf he]
    exact vc_mono hwf h p

/-- Vector clocks capture causality: they are distinct and `e → f ↔ vc e < vc f`. -/
theorem vc_captures (hwf : ex.WF) : CapturesCausality ex ex.vc := by
  intro i j hi hj
  obtain ⟨pi, hpi⟩ : ∃ p, ex.procAt i = some p := ⟨_, procAt_of_get (List.getElem?_eq_getElem hi)⟩
  obtain ⟨pj, hpj⟩ : ∃ p, ex.procAt j = some p := ⟨_, procAt_of_get (List.getElem?_eq_getElem hj)⟩
  have hle : ∀ {i j p}, ex.procAt i = some p → ex.vc i ≤ ex.vc j → ex.HBeq i j := by
    intro i j p hp h
    exact (idx_le_vc_iff hwf hp).1 ((vc_self hwf hp).symm.le.trans (h p))
  refine ⟨⟨vc_lt_of_hb hwf, fun h => ?_⟩, fun hne h => ?_⟩
  · rcases hle hpi h.le with rfl | h'
    · exact absurd h (lt_irrefl _)
    · exact h'
  · rcases hle hpi h.le with rfl | h1
    · exact hne rfl
    · exact HB.irrefl hwf _ (h1.trans_hbeq (hle hpj h.ge))

end Exec

/-- The standard vector clock algorithm is an online timestamping algorithm on every
communication graph (vectors of length `n` suffice). -/
theorem vectorClock_isOnline (G : SimpleGraph P) :
    IsOnlineTimestamping G (fun l : Exec P => l.vc (l.length - 1)) := by
  intro ex hwf _ i j hi hj
  have h := Exec.vc_captures hwf i j hi hj
  have e1 := (vcAlg P).ts_eq_onlineTs ex hi
  have e2 := (vcAlg P).ts_eq_onlineTs ex hj
  change ex.vc i = onlineTs (fun l : Exec P => l.vc (l.length - 1)) ex i at e1
  change ex.vc j = onlineTs (fun l : Exec P => l.vc (l.length - 1)) ex j at e2
  rwa [← e1, ← e2]

end Cslib.Causality
