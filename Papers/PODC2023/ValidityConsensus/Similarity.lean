import Papers.PODC2023.ValidityConsensus.Triviality

/-!
# On the Validity of Consensus — §4.2: the similarity condition is necessary (Theorem 3)

`SimilarityCondition t val` (`C_S`): there is a function `Λ` that maps every input configuration
`c` with exactly `n - t` processes to a value admissible for every input configuration similar
to `c`.

The paper requires `Λ` to be *Turing-computable*. Here `SimilarityCondition` asks for an
arbitrary function; the computable refinement is in `SimilarityComputable.lean`.
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-- `I_{n-t}`: input configurations with exactly `n - t` process-proposal pairs. -/
def IsInputConfigExact (t : ℕ) (c : Config P VI) : Prop :=
  c.procs.card = Fintype.card P - t

/-- `Λ c` is admissible for every input configuration similar to `c`. -/
def CommonAdmissible (t : ℕ) (val : ValidityProperty P VI VO) (c : Config P VI) (v : VO) :
    Prop :=
  ∀ c', IsInputConfig t c' → Similar c' c → v ∈ val c'

/-- **Definition 2 (similarity condition `C_S`)**, without the computability requirement. -/
def SimilarityCondition (t : ℕ) (val : ValidityProperty P VI VO) : Prop :=
  ∃ Λ : Config P VI → VO, ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)

/-- The core of Theorem 3 (authenticated model): in the canonical synchronous execution for `c ∈ I_{n-t}` a correct
process decides a value admissible for all configurations similar to `c`. -/
theorem exists_commonAdmissible_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val)
    (htn : t < Fintype.card P) {c : Config P VI} (hc : IsInputConfigExact t c) :
    ∃ v, CommonAdmissible t val c v ∧ ∃ p, c p ≠ none ∧
      (canonRun (M := M) c (Classical.arbitrary VI)).Decides A p v := by
  have hc' : IsInputConfig t c := by unfold IsInputConfig; rw [hc]
  let R := canonRun (M := M) c (Classical.arbitrary VI)
  have hR : R.Valid t δ := canonRun.valid c _ hc' δ
  obtain ⟨p, hp⟩ : c.procs.Nonempty := card_pos.mp (by unfold IsInputConfigExact at hc; omega)
  have hpF : p ∉ R.faulty := by simpa [R, canonRun, Option.isSome_iff_ne_none] using hp
  obtain ⟨v, hv⟩ := hA.termination R hR (canonRun_authValid _ _) p hpF
  refine ⟨v, fun c' hc'' hsim => ?_, p, Config.mem_procs_iff_ne_none.mp hp, hv⟩
  refine canonical_similarity_auth hU hA hR (canonRun.canonical c _) hpF hv hc'' ?_
  rwa [canonRun.inputConf]

/-- The core of Theorem 3: in the canonical synchronous execution for `c ∈ I_{n-t}` a correct
process decides a value admissible for all configurations similar to `c`. -/
theorem exists_commonAdmissible [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (htn : t < Fintype.card P) {c : Config P VI} (hc : IsInputConfigExact t c) :
    ∃ v, CommonAdmissible t val c v ∧ ∃ p, c p ≠ none ∧
      (canonRun (M := M) c (Classical.arbitrary VI)).Decides A p v :=
  exists_commonAdmissible_auth A.unforging_none (hA.auth _) htn hc

/-- **Theorem 3** (authenticated model). Any validity property solvable with signatures satisfies the similarity condition
(for any `n`, `t` with `t < n`). -/
theorem similarityCondition_of_solvesConsensus_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val)
    (htn : t < Fintype.card P) : SimilarityCondition t val := by
  classical
  -- `VO` is inhabited: some process decides in the failure-free synchronous execution
  have : Nonempty VO := by
    let c : Config P VI := fun _ => some (Classical.arbitrary VI)
    have hc : IsInputConfig t c := by
      unfold IsInputConfig; simp [Config.procs, c]
    let R := canonRun (M := M) c (Classical.arbitrary VI)
    have hR : R.Valid t δ := canonRun.valid c _ hc δ
    obtain ⟨p⟩ : Nonempty P := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨v, -⟩ := hA.termination R hR (canonRun_authValid _ _) p (by simp [R, canonRun, c, Config.procs])
    exact ⟨v⟩
  refine ⟨fun c => if h : ∃ v, CommonAdmissible t val c v then h.choose
    else Classical.arbitrary VO, fun c hc => ?_⟩
  obtain ⟨v, hv, -⟩ := exists_commonAdmissible_auth hU hA htn hc (M := M)
  have h : ∃ v, CommonAdmissible t val c v := ⟨v, hv⟩
  simp only [h, dite_true]
  exact h.choose_spec

/-- **Theorem 3.** Any solvable validity property satisfies the similarity condition
(for any `n`, `t` with `t < n`). -/
theorem similarityCondition_of_solvesConsensus [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (htn : t < Fintype.card P) : SimilarityCondition t val :=
  similarityCondition_of_solvesConsensus_auth A.unforging_none (hA.auth _) htn

/-- **Theorem 3** (authenticated, solvability form). -/
theorem similarityCondition_of_solvableAuth [Nonempty VI] (h : val.SolvableAuth t δ)
    (htn : t < Fintype.card P) : SimilarityCondition t val := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := h
  exact similarityCondition_of_solvesConsensus_auth hU hA htn

/-- **Theorem 3** (solvability form). -/
theorem similarityCondition_of_solvable [Nonempty VI] (h : val.Solvable t δ)
    (htn : t < Fintype.card P) : SimilarityCondition t val := by
  obtain ⟨M, S, A, hA⟩ := h
  exact similarityCondition_of_solvesConsensus hA htn

end ValidityConsensus
