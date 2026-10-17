import Papers.PODC2023.ValidityConsensus.Similarity
import Cslib.Computability.Distributed.Byzantine.PartialSync.Computable

/-!
# On the Validity of Consensus — Theorems 2 and 3 with Turing-computable `Λ`

The paper's similarity condition `C_S` (Definition 2) requires the function `Λ` to be
*Turing-computable*. We use Mathlib's notion `Computable` (partial recursive and total, via
`Primcodable` encodings). Processes are `Fin n`; then `Config (Fin n) VI = Fin n → Option VI` is
`Primcodable` (`Primcodable.finArrow`) as soon as `VI` is.

* `Algorithm.IsComputable A` (shared library `Cslib.Computability.Distributed.Byzantine.PartialSync.Computable`): the algorithm is a
  computable state machine (`init`, `step`, `send`, `decide` are computable).
* `similarityCondition_computable_auth` / `similarityCondition_computable` (**Theorem 3**, in the
  authenticated / unauthenticated model): `Λ c` is the first decision of a process of
  `π(c)` in the canonical run of `c`, found by unbounded search
  (`Algorithm.IsComputable.exists_computable_canonDecision`), which terminates by Termination.
* `alwaysAdmissible_computable` (**Theorem 2**): immediate from Theorem 1.
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {M S VI VO : Type*} [Primcodable M] [Primcodable S] [Primcodable VI]
  [Primcodable VO] {t δ : ℕ} {A : Algorithm (Fin n) M S VI VO}
  {val : ValidityProperty (Fin n) VI VO}

/-- **Theorem 3 of [Civit et al., PODC 2023]** (with the computability requirement), in the
authenticated model `Au` (with an unforging algorithm): if a computable algorithm solves
consensus with validity property `val` (and `t < n`), then `val` satisfies the similarity
condition `C_S` with a *Turing-computable* `Λ`.

`Λ c` is the first decision (in the order of `Nat.rfindOpt` over pairs ⟪time, process⟫) of a
process of `π(c)` in the canonical synchronous execution of `c`; to make `Λ` total, a
configuration `c` that is not an input configuration is first replaced by the failure-free
configuration with all proposals equal to a fixed value. -/
theorem similarityCondition_computable_auth {K : Type*} {Au : Auth (Fin n) M K} [Nonempty VI]
    (hU : A.Unforging Au) (hA : SolvesConsensusAuth Au t δ A val)
    (hc : A.IsComputable) (htn : t < n) :
    ∃ Λ : Config (Fin n) VI → VO, Computable Λ ∧
      ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c) := by
  set d := Classical.arbitrary VI
  obtain ⟨Λ, hΛc, hΛ⟩ := hc.exists_computable_canonDecision (M := M) d htn
    fun c hc' p hp => hA.termination _ (canonRun.valid c d hc' δ) (canonRun_authValid c d) p
      (by simpa [canonRun, Option.isSome_iff_ne_none] using hp)
  refine ⟨Λ, hΛc, fun c hc' c' hc'' hsim => ?_⟩
  have hcI : IsInputConfig t c := by unfold IsInputConfig; rw [hc']
  obtain ⟨p, hp, hdec⟩ := hΛ c hcI
  refine canonical_similarity_auth hU hA (canonRun.valid c d hcI δ) (canonRun.canonical c d) ?_
    hdec hc'' (by rwa [canonRun.inputConf])
  simp [canonRun, Option.isSome_iff_ne_none, hp]

/-- **Theorem 3 of [Civit et al., PODC 2023]** (with the computability requirement), in the
unauthenticated model: the special case `Au = Auth.none` of
`similarityCondition_computable_auth`. -/
theorem similarityCondition_computable [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (hc : A.IsComputable) (htn : t < n) :
    ∃ Λ : Config (Fin n) VI → VO, Computable Λ ∧
      ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c) :=
  similarityCondition_computable_auth A.unforging_none (hA.auth _) hc htn

omit [Primcodable M] [Primcodable S] [Primcodable VI] in
/-- **Theorem 2 of [Civit et al., PODC 2023]** (with the computability requirement): if
`n ≤ 3t`, every solvable validity property is trivial, and the always-admissible value is
produced by a Turing-computable (constant) function.

Once the elements of `V_O` are encodable (`Primcodable VO`), every constant function is
computable, so this has no content beyond Theorem 1 (`trivial_of_solvable`). -/
theorem alwaysAdmissible_computable [Nonempty VI] (h : val.Solvable t δ) (ht : 0 < t)
    (htn : t < n) (hn : n ≤ 3 * t) :
    ∃ f : Unit → VO, Computable f ∧ ∀ c, IsInputConfig t c → f () ∈ val c := by
  obtain ⟨v, hv⟩ := trivial_of_solvable h ht (by simpa using htn) (by simpa using hn)
  exact ⟨fun _ => v, Computable.const v, hv⟩

end ValidityConsensus
