import Papers.PODC2024.AllBAExpensive.LowerBound
import Podc.PartialSync.Map

/-!
# All Byzantine Agreement Problems Are Expensive — §4.2: weak consensus is the weakest problem

* `weakReduction A c₀ c₁ v₀`: **Algorithm 1** (propose `c₀[i]` / `c₁[i]` to `A` for proposal
  `0` / `1`; decide `0` iff `A` decides `v₀`): input pre-processing and decision post-processing
  (`Algorithm.comapInput`, `Algorithm.mapDecide` of `Podc.PartialSync.Map`), so it has the states
  and messages of `A` (`Run.st_comapInput`, `Run.msgsUpTo_comapInput`).
* `exists_reduction_data`: Table 2 and **Lemma 17** (`v₀' ≠ v₁'`), via Lemma 7.
* `weakReduction_solves`: **Lemma 18** — Algorithm 1 solves weak consensus.
* `weakConsensus_solvableAuthSync_of`, `weakConsensus_solvableSync_of`: **Lemma 6** (zero-message
  reduction from weak consensus to any solvable non-trivial problem).

As in the paper, the reduction relies on the fully correct execution being determined by the
proposals, which holds in the lock-step model (`δ = 0`); for `δ > 0` (bounded but variable delays)
different fault-free executions with the same proposals may decide differently. This only
affects Algorithm 1 as a stand-alone algorithm: the lower bound (`message_lower_bound_auth`) is
proved for every `δ`.
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-- **Algorithm 1**: reduction from (binary) weak consensus to `A`. -/
abbrev weakReduction [DecidableEq VO] (A : Algorithm P M S VI VO) (c₀ c₁ : P → VI) (v₀ : VO) :
    Algorithm P M S Bool Bool :=
  (A.comapInput fun p b => if b then c₁ p else c₀ p).mapDecide fun v => decide (v ≠ v₀)

variable [DecidableEq VO] {c₀ c₁ : P → VI} {v₀ : VO}

omit [Fintype P] in
theorem decides_weakReduction {R : Run P M Bool} {p : P} {b : Bool} :
    R.Decides (weakReduction A c₀ c₁ v₀) p b ↔
      ∃ v, (R.mapInput fun p b => if b then c₁ p else c₀ p).Decides A p v ∧
        decide (v ≠ v₀) = b := by
  simp only [Run.decides_mapDecide, Run.decides_comapInput]

omit [Fintype P] in
/-- **Lemma 18** of [AllBAExpensive]: if `A` solves `val`-agreement in the lock-step synchronous
model (`δ = 0`), the fault-free execution with proposals `c₀` only decides `v₀`, and the one with
proposals `c₁` never decides `v₀`, then Algorithm 1 solves (binary) weak consensus. -/
theorem weakReduction_solves (hA : SolvesConsensusAuthSync Au t 0 A val)
    (h₀ : ∀ p v, (ffRun M c₀).Decides A p v → v = v₀)
    (h₁ : ∀ p v, (ffRun M c₁).Decides A p v → v ≠ v₀) :
    SolvesConsensusAuthSync Au t 0 (weakReduction A c₀ c₁ v₀) (weakValidity P Bool) where
  termination R hR hRa h0 p hp := by
    obtain ⟨v, hv⟩ := hA.termination _ ((R.valid_mapInput).2 hR)
      ((R.authValid_comapInput Au).1 ((R.authValid_mapDecide Au).1 hRa)) h0 p hp
    exact ⟨_, decides_weakReduction.mpr ⟨v, hv, rfl⟩⟩
  agreement R hR hRa h0 p hp q hq b b' hb hb' := by
    obtain ⟨v, hv, rfl⟩ := decides_weakReduction.mp hb
    obtain ⟨v', hv', rfl⟩ := decides_weakReduction.mp hb'
    rw [hA.agreement _ ((R.valid_mapInput).2 hR)
      ((R.authValid_comapInput Au).1 ((R.authValid_mapDecide Au).1 hRa)) h0 p hp q hq v v' hv hv']
  validity R hR hRa h0 p hp b hb := by
    intro b' hall
    obtain ⟨v, hv, rfl⟩ := decides_weakReduction.mp hb
    -- the run is fault-free and lock-step
    have hf : R.faulty = ∅ := by
      ext q; simp only [Finset.notMem_empty, iff_false]; intro hq
      have := hall q; simp [Run.inputConf, hq] at this
    have hinp : ∀ q, R.inp q = b' := by
      intro q; have := hall q; simpa [Run.inputConf, hf] using this
    have hdl : ∀ q τ r, R.dl q τ r = τ := by
      intro q τ r
      have h1 := hR.dl_ge q τ r (by simp [hf]) (by simp [hf])
      have h2 := hR.dl_le q τ r (by simp [hf]) (by simp [hf])
      rw [h0] at h2; simp at h2; omega
    have hst : ∀ τ q, (R.mapInput fun p b => if b then c₁ p else c₀ p).st A τ q =
        (ffRun M (if b' then c₁ else c₀)).st A τ q := by
      intro τ q
      have hx : (R.mapInput fun p b => if b then c₁ p else c₀ p).inp =
          (ffRun M (if b' then c₁ else c₀)).inp := by
        funext r
        simp only [Run.mapInput_inp, Run.quiet_inp, hinp r]
        split_ifs <;> rfl
      rw [Run.st_eq_ff (A := A) (R := R.mapInput fun p b => if b then c₁ p else c₀ p) hf hdl,
        Run.st_eq_ff (R := ffRun M (if b' then c₁ else c₀)) rfl (fun _ _ _ => rfl), hx]
    have hv' : (ffRun M (if b' then c₁ else c₀)).Decides A p v := by
      obtain ⟨τ, h⟩ := hv; exact ⟨τ, by rwa [← hst]⟩
    cases b'
    · simpa using h₀ p v hv'
    · simpa using h₁ p v hv'

omit [DecidableEq VO] in
/-- **Table 2 / Lemma 17** of [AllBAExpensive]: for a non-trivial problem solved by `A` in
synchrony, there are full proposal vectors `c₀`, `c₁` and a value `v₀` such that the fault-free
execution from `c₀` only decides `v₀` and the one from `c₁` never decides `v₀` (`v₁' ≠ v₀'`). -/
theorem exists_reduction_data [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuthSync Au t δ A val) (hnt : ¬ val.Trivial t)
    (htn : t < Fintype.card P) :
    ∃ (c₀ c₁ : P → VI) (v₀ : VO), (∀ p v, (ffRun M c₀).Decides A p v → v = v₀) ∧
      (∀ p v, (ffRun M c₁).Decides A p v → v ≠ v₀) := by
  classical
  obtain ⟨p⟩ : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  set d : VI := Classical.arbitrary VI
  have hff : ∀ x : P → VI, (ffRun M x).AuthValid Au A := fun _ => Run.quiet_authValid
  obtain ⟨v₀, hv₀⟩ := hA.termination (ffRun M fun _ => d) (ffRun_valid M _) (hff _) rfl p
    (by simp [ffRun])
  obtain ⟨c, hc, hvc⟩ : ∃ c, IsInputConfig t c ∧ v₀ ∉ val c := by
    by_contra h; push Not at h; exact hnt ⟨v₀, h⟩
  refine ⟨fun _ => d, fun q => (c q).getD d, v₀, fun q v hv => ?_, fun q v hv hvv => ?_⟩
  · exact hA.agreement _ (ffRun_valid M _) (hff _) rfl q (by simp [ffRun]) p (by simp [ffRun])
      v v₀ hv hv₀
  · apply hvc
    rw [← hvv]
    refine containment_auth hU hA htn (ffRun_valid M _) (hff _) rfl (by simp [ffRun]) hv hc
      fun r hr => ?_
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hr
    simp [Run.inputConf, ffRun, hw]

omit [DecidableEq VO] in
/-- **Lemma 6** of [AllBAExpensive] (authenticated): weak consensus reduces at zero message cost
to any solvable non-trivial agreement problem (lock-step synchrony). -/
theorem weakConsensus_solvableAuthSync_of [Nonempty VI] (h : val.SolvableAuthSync t 0)
    (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P) :
    (weakValidity P Bool).SolvableAuthSync t 0 := by
  classical
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  obtain ⟨c₀, c₁, v₀, h₀, h₁⟩ := exists_reduction_data hU hA hnt htn
  exact ⟨M, S, K, Au, weakReduction A c₀ c₁ v₀, (hU.comapInput _).mapDecide _,
    weakReduction_solves hA h₀ h₁⟩

omit [DecidableEq VO] in
/-- **Lemma 6** of [AllBAExpensive] (unauthenticated). -/
theorem weakConsensus_solvableSync_of [Nonempty VI] (h : val.SolvableSync t 0)
    (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P) :
    (weakValidity P Bool).SolvableSync t 0 := by
  classical
  obtain ⟨M, S, A, hA⟩ := h
  obtain ⟨c₀, c₁, v₀, h₀, h₁⟩ := exists_reduction_data A.unforging_none hA hnt htn
  exact ⟨M, S, weakReduction A c₀ c₁ v₀, weakReduction_solves hA h₀ h₁⟩

end AllBAExpensive
