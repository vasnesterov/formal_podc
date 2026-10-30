import Papers.PODC2026.FewToManyFaultsBA.SyncBA.StageB

/-!
# Decisions of `SyncBA`

A party decides its commit value as soon as it has a commit in stage A (`decides_of_commit`); a
party without commit at the end of stage A decides its value (`decides_of_noFb`) or, if it holds a
fallback certificate, what it decides in stage B (`decides_iff_stageB`).
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] (π : Params n) {Mf : Type} (Afb : Protocol (Fin n) Bool Mf Bool)

/-- `SyncBA` as a plain sequential composition (same messages). -/
noncomputable abbrev seqP := (stageA π).seq (R0 n) toB (stageB Afb)

variable {π Afb}
variable {sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)}

lemma hist_syncBA : hist (G n) (syncBA π Afb) sc = hist (G n) (seqP π Afb) sc :=
  hist_eq_of_send_eq _ _ _ rfl

/-- The stage-A scenario of a run of `SyncBA`. -/
abbrev scA (sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)) : Scenario (Fin n) Bool (Msg n) :=
  sc.seqFst (R0 n)

lemma stateOf_hist (r : ℕ) (p : Fin n) :
    stateOf π p (sc.input p) (histL ((hist (G n) (syncBA π Afb) sc r p).take (R0 n))) =
      S π (scA sc) (min r (R0 n)) p := by
  rw [hist_syncBA]
  have htake : (hist (G n) (seqP π Afb) sc r p).take (R0 n) =
      hist (G n) (seqP π Afb) sc (min r (R0 n)) p := by
    rcases le_total r (R0 n) with h | h
    · rw [min_eq_left h]; exact List.take_of_length_le (by simp [h])
    · rw [min_eq_right h]; exact take_hist _ _ _ h p
  rw [htake, histL_hist_seq (G n) (stageA π) (R0 n) toB (stageB Afb) sc _ (min_le_right _ _)]
  rfl

/-- The decision status of `SyncBA`. -/
lemma status_syncBA (r : ℕ) (p : Fin n) :
    status (G n) (syncBA π Afb) sc r p =
      match (S π (scA sc) (min r (R0 n)) p).commit with
      | some c => some c.1
      | none =>
        if r < R0 n then none
        else if (S π (scA sc) (min r (R0 n)) p).fb.isSome then
          Afb.decide p (finalValue π (S π (scA sc) (min r (R0 n)) p) (sc.input p))
            (histR ((hist (G n) (syncBA π Afb) sc r p).drop (R0 n)))
        else some (finalValue π (S π (scA sc) (min r (R0 n)) p) (sc.input p)) := by
  have hs := stateOf_hist (π := π) (Afb := Afb) (sc := sc) r p
  have hl : (hist (G n) (syncBA π Afb) sc r p).length = r := length_hist _ _ _ _ _
  unfold status
  generalize hist (G n) (syncBA π Afb) sc r p = h at hs hl ⊢
  simp only [syncBA, hs, hl]
  rfl

lemma S_commit_none_of_le {r r' : ℕ} {p : Fin n} (h : r ≤ r')
    (hc : (S π (scA sc) r' p).commit = none) : (S π (scA sc) r p).commit = none := by
  rcases hcr : (S π (scA sc) r p).commit with _ | c
  · rfl
  · rw [S_commit_mono h hcr] at hc; cases hc

/-- A party with a commit decides its value; it has decided by the time it holds the commit. -/
theorem decides_of_commit {r₀ : ℕ} (hr₀ : r₀ ≤ R0 n) {p : Fin n} {c : Proof n}
    (hc : (S π (scA sc) r₀ p).commit = some c) :
    Decides (G n) (syncBA π Afb) sc p c.1 ∧ status (G n) (syncBA π Afb) sc r₀ p = some c.1 := by
  classical
  have hex : ∃ r, (S π (scA sc) r p).commit.isSome := ⟨r₀, by simp [hc]⟩
  set r₁ := Nat.find hex
  have hr₁ : r₁ ≤ r₀ := Nat.find_min' hex (by simp [hc])
  obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  have hcc : c₁ = c := by
    have := S_commit_mono hr₁ hc₁; rw [hc] at this; cases this; rfl
  subst hcc
  have hst : status (G n) (syncBA π Afb) sc r₀ p = some c₁.1 := by
    rw [status_syncBA, min_eq_left hr₀, hc]
  refine ⟨⟨r₁, ?_, fun r hr => ?_⟩, hst⟩
  · rw [status_syncBA, min_eq_left (hr₁.trans hr₀), hc₁]
  · have hnone : (S π (scA sc) r p).commit = none := by
      have := Nat.find_min hex hr; simpa using this
    rw [status_syncBA, min_eq_left (by omega), hnone]
    simp [show r < R0 n by omega]

/-- A party without commit and without fallback certificate decides its value at round `R₀`. -/
theorem decides_of_noFb {p : Fin n} (hc : (S π (scA sc) (R0 n) p).commit = none)
    (hfb : (S π (scA sc) (R0 n) p).fb = none) :
    Decides (G n) (syncBA π Afb) sc p (finalValue π (S π (scA sc) (R0 n) p) (sc.input p)) ∧
      status (G n) (syncBA π Afb) sc (R0 n) p =
        some (finalValue π (S π (scA sc) (R0 n) p) (sc.input p)) := by
  have hst : status (G n) (syncBA π Afb) sc (R0 n) p =
      some (finalValue π (S π (scA sc) (R0 n) p) (sc.input p)) := by
    rw [status_syncBA, min_self, hc]; simp [hfb]
  refine ⟨⟨R0 n, hst, fun r hr => ?_⟩, hst⟩
  rw [status_syncBA, min_eq_left hr.le, S_commit_none_of_le hr.le hc]
  simp [hr]

/-- The input of stage B. -/
lemma seqInputs_val (p : Fin n) :
    seqInputs (G n) (stageA π) (R0 n) toB sc p =
      if (S π (scA sc) (R0 n) p).fb.isSome then
        some (finalValue π (S π (scA sc) (R0 n) p) (sc.input p)) else none := by
  rw [seqInputs_eq_firstUpTo]
  have hR : status (G n) (stageA π) (scA sc) (R0 n) p =
      some ⟨(S π (scA sc) (R0 n) p).fb.isSome, finalValue π (S π (scA sc) (R0 n) p) (sc.input p)⟩ := by
    simp [status, stageA, length_hist, S]
  rw [firstUpTo_of_firstSome hR (fun r' hr' => by
    simp [status, stageA, length_hist, Nat.ne_of_lt hr']) le_rfl]
  simp only [toB]

/-- The stage-B scenario of a run of `SyncBA`. -/
noncomputable abbrev scB (sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)) :
    Scenario (Fin n) (Option Bool) Mf :=
  sc.seqSnd (R0 n) (seqInputs (G n) (stageA π) (R0 n) toB sc)

lemma status_syncBA_R0 {p : Fin n} (hc : (S π (scA sc) (R0 n) p).commit = none)
    (hfb : (S π (scA sc) (R0 n) p).fb.isSome) (j : ℕ) :
    status (G n) (syncBA π Afb) sc (R0 n + j) p =
      status (G n) (stageB Afb) (scB (π := π) sc) j p := by
  rw [status_syncBA, min_eq_right (by omega), hc]
  simp only [show ¬ R0 n + j < R0 n by omega, ite_false, hfb, ite_true]
  rw [hist_syncBA, histR_hist_seq (G n) (stageA π) (R0 n) toB (stageB Afb) sc j p]
  simp only [status, Scenario.seqSnd_input, seqInputs_val, hfb, ite_true, stageB]

/-- A party without commit but with a fallback certificate decides what it decides in stage B. -/
theorem decides_iff_stageB {p : Fin n} (hc : (S π (scA sc) (R0 n) p).commit = none)
    (hfb : (S π (scA sc) (R0 n) p).fb.isSome) (o : Bool) :
    Decides (G n) (syncBA π Afb) sc p o ↔ Decides (G n) (stageB Afb) (scB (π := π) sc) p o := by
  show FirstSome _ o ↔ FirstSome _ o
  rw [firstSome_shift (R0 n) (fun r hr => by
    rw [status_syncBA, min_eq_left hr.le, S_commit_none_of_le hr.le hc]; simp [hr])]
  simp only [status_syncBA_R0 hc hfb]

end Podc.FewToManyFaultsBA.Sync
