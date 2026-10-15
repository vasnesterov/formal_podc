import Papers.PODC2024.AllBAExpensive.LowerBound

/-!
# All Byzantine Agreement Problems Are Expensive — §4.2: weak consensus is the weakest problem

* `weakReduction A c₀ c₁ v₀`: **Algorithm 1** (propose `c₀[i]` / `c₁[i]` to `A` for proposal
  `0` / `1`; decide `0` iff `A` decides `v₀`). Same states and messages as `A`
  (`st_weakReduction`, `msgsUpTo_weakReduction`).
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
def weakReduction [DecidableEq VO] (A : Algorithm P M S VI VO) (c₀ c₁ : P → VI) (v₀ : VO) :
    Algorithm P M S Bool Bool where
  init p b := A.init p (if b then c₁ p else c₀ p)
  step := A.step
  send := A.send
  decide p s := (A.decide p s).map fun v => decide (v ≠ v₀)

/-- The run of `A` corresponding to a run of `weakReduction A c₀ c₁ v₀`. -/
def mapInp (R : Run P M Bool) (c₀ c₁ : P → VI) : Run P M VI :=
  { R with inp := fun p => if R.inp p then c₁ p else c₀ p }

variable [DecidableEq VO] {c₀ c₁ : P → VI} {v₀ : VO}

omit [Fintype P] [DecidableEq P] [DecidableEq VO] in
theorem valid_mapInp {R : Run P M Bool} (hR : R.Valid t δ) : (mapInp R c₀ c₁).Valid t δ :=
  ⟨hR.1, hR.2, hR.3⟩

omit [Fintype P] in
theorem st_weakReduction (R : Run P M Bool) :
    ∀ τ p, R.st (weakReduction A c₀ c₁ v₀) τ p = (mapInp R c₀ c₁).st A τ p := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p
    rcases τ with _ | τ
    · rfl
    · rw [Run.st_succ, Run.st_succ, ih τ (by omega)]
      show A.step p _ _ = A.step p _ _
      congr 1
      funext q
      rw [Run.inbox_eq_flatMap, Run.inbox_eq_flatMap]
      refine List.flatMap_congr fun σ hσ => ?_
      have hσ' : σ < τ + 1 := by simpa using hσ
      simp only [Run.dlv]
      congr 1
      by_cases hq : q ∈ R.faulty
      · rw [Run.out_of_faulty _ _ hq, Run.out_of_faulty _ _ (by exact hq)]; rfl
      · rw [Run.out_of_correct _ _ hq, Run.out_of_correct _ _ (by exact hq), ih σ hσ']; rfl

omit [Fintype P] in
theorem out_weakReduction (R : Run P M Bool) :
    R.out (weakReduction A c₀ c₁ v₀) = (mapInp R c₀ c₁).out A := by
  funext q τ p
  by_cases hq : q ∈ R.faulty
  · rw [Run.out_of_faulty _ _ hq, Run.out_of_faulty _ _ (by exact hq)]; rfl
  · rw [Run.out_of_correct _ _ hq, Run.out_of_correct _ _ (by exact hq), st_weakReduction]; rfl

omit [Fintype P] in
theorem inbox_weakReduction (R : Run P M Bool) :
    R.inbox (weakReduction A c₀ c₁ v₀) = (mapInp R c₀ c₁).inbox A := by
  funext p τ q
  rw [Run.inbox_eq_flatMap, Run.inbox_eq_flatMap]
  simp only [Run.dlv, out_weakReduction]
  rfl

omit [Fintype P] in
theorem decides_weakReduction {R : Run P M Bool} {p : P} {b : Bool} :
    R.Decides (weakReduction A c₀ c₁ v₀) p b ↔
      ∃ v, (mapInp R c₀ c₁).Decides A p v ∧ b = decide (v ≠ v₀) := by
  simp only [Run.Decides, st_weakReduction]
  simp only [weakReduction, Option.map_eq_some_iff]
  constructor
  · rintro ⟨τ, v, h, rfl⟩; exact ⟨v, ⟨τ, h⟩, rfl⟩
  · rintro ⟨v, ⟨τ, h⟩, rfl⟩; exact ⟨τ, v, h, rfl⟩

omit [Fintype P] in
theorem authValid_weakReduction (R : Run P M Bool) :
    R.AuthValid Au (weakReduction A c₀ c₁ v₀) ↔ (mapInp R c₀ c₁).AuthValid Au A := by
  simp only [Run.AuthValid, Run.honestTokens, out_weakReduction]
  rfl

omit [Fintype P] in
theorem unforging_weakReduction (hU : A.Unforging Au) :
    (weakReduction A c₀ c₁ v₀).Unforging Au := by
  intro R p τ q m hm x hx
  rw [st_weakReduction] at hm
  have := hU (mapInp R c₀ c₁) p τ q m hm x hx
  simpa only [Run.recvTokens, inbox_weakReduction] using this

/-- Algorithm 1 sends exactly the messages of `A`. -/
theorem msgsUpTo_weakReduction (R : Run P M Bool) (N : ℕ) :
    R.msgsUpTo (weakReduction A c₀ c₁ v₀) N = (mapInp R c₀ c₁).msgsUpTo A N := by
  simp only [Run.msgsUpTo, Run.msgsAt, out_weakReduction]
  rfl

/-- **Lemma 18** of [AllBAExpensive]: if `A` solves `val`-agreement in the lock-step synchronous
model (`δ = 0`), the fault-free execution with proposals `c₀` only decides `v₀`, and the one with
proposals `c₁` never decides `v₀`, then Algorithm 1 solves (binary) weak consensus. -/
theorem weakReduction_solves (hA : SolvesConsensusAuthSync Au t 0 A val)
    (h₀ : ∀ p v, (ffRun M c₀).Decides A p v → v = v₀)
    (h₁ : ∀ p v, (ffRun M c₁).Decides A p v → v ≠ v₀) :
    SolvesConsensusAuthSync Au t 0 (weakReduction A c₀ c₁ v₀) (weakValidity P Bool) where
  termination R hR hRa h0 p hp := by
    obtain ⟨v, hv⟩ := hA.termination (mapInp R c₀ c₁) (valid_mapInp hR) ((authValid_weakReduction R).mp hRa)
      h0 p hp
    exact ⟨_, decides_weakReduction.mpr ⟨v, hv, rfl⟩⟩
  agreement R hR hRa h0 p hp q hq b b' hb hb' := by
    obtain ⟨v, hv, rfl⟩ := decides_weakReduction.mp hb
    obtain ⟨v', hv', rfl⟩ := decides_weakReduction.mp hb'
    rw [hA.agreement (mapInp R c₀ c₁) (valid_mapInp hR) ((authValid_weakReduction R).mp hRa) h0 p hp q hq v v'
      hv hv']
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
    have hst : ∀ τ q, (mapInp R c₀ c₁).st A τ q = (ffRun M (if b' then c₁ else c₀)).st A τ q := by
      intro τ q
      rw [st_eq_ffExec (R := mapInp R c₀ c₁) hf hdl,
        st_eq_ffExec (R := ffRun M (if b' then c₁ else c₀)) rfl (fun _ _ _ => rfl)]
      congr 2
      funext r
      simp only [mapInp, ffRun, hinp r]
      split_ifs <;> rfl
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
  have hff : ∀ x : P → VI, (ffRun M x).AuthValid Au A :=
    fun x => Run.authValid_of_canonical (fun _ h => by simp [ffRun] at h)
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
  exact ⟨M, S, K, Au, weakReduction A c₀ c₁ v₀, unforging_weakReduction hU,
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
