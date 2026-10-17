import Mathlib
import Papers.PODC2023.RuntimeVerification.Enforce
import Papers.PODC2023.RuntimeVerification.Witness
import Papers.PODC2023.RuntimeVerification.Objects
import Papers.PODC2023.RuntimeVerification.Infinite
import Papers.PODC2023.RuntimeVerification.Lemma74

/-!
# Main results of Castañeda–Rodríguez, PODC 2023 (arXiv 2301.02638v3)

Impossibility (`Impossibility.lean`, `Objects.lean`):
* `Impossibility.thm_5_1`, `Objects.thm_5_1_queue`, … — Theorem 5.1;
* `Impossibility.thm_A_1`, `Objects.thm_A_1_queue`, … — Theorem A.1;
* `Impossibility.trivialVerifier_predictive` — Definition 6.1 is trivial if the verifier may depend
  on its input implementation.

GenLin (`Similarity.lean`): `lemma_7_1` (linearizability ∈ GenLin).

The construction (this file and `Exec`, `Sketch`, `Verifier`, `Theorems`, `Enforce`, `Witness`):
* `lemma_7_2` — `A` correct ⇒ `A*` correct (for `O ∈ GenLin`);
* `thm_8_1` — Theorem 8.1 for finite executions: predictive soundness (every reported witness
  is a history of `A*` violating `O`), soundness for correct executions of `A`, completeness and
  stability;
* `thm_8_2` — Theorem 8.2 (self-enforced implementations);
* `lemma_7_4_false` — Lemma 7.4 is false as stated (pending operations invisible to all views).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

/-- **Lemma 7.2 (⇒).** If every history of `A` belongs to `O ∈ GenLin`, so does every history of
`A*` (views disregarded). -/
theorem lemma_7_2 {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) {𝒜 : Set (Hist (Fin n) Op Y)}
    (h𝒜O : 𝒜 ⊆ O) {T : Type} [LinearOrder T] {F : Exec n Op Y T} (hF : IsAStarExec 𝒜 F) :
    (F.hSy 6).toList ∈ O :=
  GenLin.mem_of_simTH hO (Exec.proj_WF hF.1 _ (by norm_num) (by norm_num))
    (Exec.proj_WF hF.1 _ (by norm_num) (by norm_num)) (Exec.simTH_S_A hF.1 (by norm_num) _)
    (h𝒜O hF.2)

/-- **Theorem 8.1** (finite executions). Let `O ∈ GenLin`, let `A` be an abstract implementation
(a prefix-closed set `𝒜` of histories) and let `E` be a finite execution of the verifier `V_O`
(Figure 10) running `A*` (Figure 7) on top of `A`.
1. *Predictive soundness*: whenever a process reports `(ERROR, X(τ))`, the witness `X(τ)` is a
   history of `A*` and violates `O`.
2. *Soundness for correct executions of `A`*: if the history of `A` is in `O`, nobody reports.
3. *Completeness*: if the history of `A*` up to time `t₀` is not in `O`, every test (line 10)
   that reads `M` after all operations whose `N.Snapshot` precedes `t₀` have written their tuple
   reports `ERROR`.
4. *Stability*: once a test reports `ERROR`, every later test reports `ERROR`. -/
theorem thm_8_1 {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) {𝒜 : Set (Hist (Fin n) Op Y)}
    (h𝒜 : ∀ h ∈ 𝒜, ∀ h', h' <+: h → h' ∈ 𝒜) {E : Exec n Op Y ℕ} (hw : E.WF)
    (hA : (E.hA 8).toList ∈ 𝒜) :
    (∀ p k, E.Reports O p k →
      IsAStarHist 𝒜 (XTH (E.tau p k)).toList ∧
        (XTH (E.tau p k)).toList.map (TH.evMap Prod.fst) ∉ O) ∧
    ((E.hA 8).toList ∈ O → ∀ p k, ¬ E.Reports O p k) ∧
    (∀ t₀ p k, 8 * k + 7 < E.len p →
      (∀ q j, 8 * j + 4 < E.len q → E.T q (8 * j + 4) < t₀ →
        8 * j + 6 < E.len q ∧ E.T q (8 * j + 6) < E.T p (8 * k + 7)) →
      ((E.hSy 8).cut t₀).toList ∉ O → E.Reports O p k) ∧
    (∀ p k q j, E.Reports O p k → 8 * j + 7 < E.len q → E.T p (8 * k + 7) ≤ E.T q (8 * j + 7) →
      E.Reports O q j) := by
  refine ⟨fun p k hr => ⟨sketch_isAStarHist h𝒜 hw hA _, ?_⟩, fun hAO p k hr => ?_,
    fun t₀ p k hk H hnot => ⟨hk, fun hX => hnot (Exec.cut_mem_of_sketch hO hw H hX)⟩,
    fun p k q j hr hj hle => ⟨hj, fun hX => hr.2 (Exec.sketch_mono hO hw hle hX)⟩⟩
  · rw [← TH.toList_mapRes]; exact hr.2
  · apply hr.2
    have hT : (E.hTy 8).toList ∈ O :=
      GenLin.mem_of_simTH hO (Exec.hTy_WF hw) (Exec.hA_WF hw)
        (Exec.simTH_T_A hw (by norm_num) _) hAO
    exact Exec.sketch_mem_of_tight hO hw hT _

/-- **Theorem 8.2** (self-enforced implementations), for finite executions of `V_{O,A}`
(Figure 11), `O ∈ GenLin` non-empty:
1. if `A` is correct with respect to `O` (all its histories are in `O`), no operation of
   `V_{O,A}` returns `ERROR` and the history of `V_{O,A}` is in `O`;
2. the history of `V_{O,A}` up to any time before the first `ERROR` response is in `O`;
3. after an `ERROR` response, every later response is `ERROR`;
4. every `ERROR` comes with a witness: a history of `A*` violating `O`. -/
theorem thm_8_2 {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) (hO₀ : [] ∈ O)
    {𝒜 : Set (Hist (Fin n) Op Y)} (h𝒜 : ∀ h ∈ 𝒜, ∀ h', h' <+: h → h' ∈ 𝒜)
    {E : Exec n Op Y ℕ} (hw : E.WF) (hA : (E.hA 8).toList ∈ 𝒜) :
    (𝒜 ⊆ O → (∀ p k, ¬ E.Reports O p k) ∧ E.hVy.toList ∈ O) ∧
    (∀ t, (∀ p k, 8 * k + 7 < E.len p → E.T p (8 * k + 7) < t → ¬ E.Reports O p k) →
      (E.cut t).hVy.toList ∈ O) ∧
    (∀ p k q j, E.Reports O p k → 8 * j + 7 < E.len q → E.T p (8 * k + 7) ≤ E.T q (8 * j + 7) →
      E.Reports O q j) ∧
    (∀ p k, E.Reports O p k →
      IsAStarHist 𝒜 (XTH (E.tau p k)).toList ∧
        (XTH (E.tau p k)).toList.map (TH.evMap Prod.fst) ∉ O) := by
  obtain ⟨h1, h2, -, h4⟩ := thm_8_1 hO h𝒜 hw hA
  refine ⟨fun hAO => ?_, fun t hno => Exec.hVy_cut_mem hO hO₀ hw hno, h4, h1⟩
  have hno := h2 (hAO hA)
  exact ⟨hno, Exec.hVy_mem_of_noReport hO hO₀ hw hno⟩

/-- **Theorem 8.1** (infinite executions, Definition 6.1). Let `E` be an infinite execution of
`V_O` running `A*` over `A` (every finite prefix of the history of `A` is in the prefix-closed
`𝒜`).
1. *Predictive soundness*: every `ERROR` comes with a witness `X(τ)` that is a history of `A*`
   violating `O`.
2. *Soundness for correct executions of `A`*: if every finite prefix of the history of `A` is in
   `O`, nobody reports `ERROR`.
3. *Completeness and stability*: if no process stops between its `N.Snapshot` and its `M.Write`,
   tests happen at arbitrarily late times, and some finite prefix of the history of `A*` is not in
   `O`, then there is a time after which every test reports `ERROR` (and there are such tests). -/
theorem thm_8_1_inf {O : Set (Hist (Fin n) Op Y)} (hO : GenLin O) {𝒜 : Set (Hist (Fin n) Op Y)}
    (h𝒜 : ∀ h ∈ 𝒜, ∀ h', h' <+: h → h' ∈ 𝒜) {E : InfExec n Op Y} (hw : E.WF)
    (hA : ∀ t, ((E.pre t).hA 8).toList ∈ 𝒜) :
    (∀ p k, E.Reports O p k →
      IsAStarHist 𝒜 (XTH ((E.pre (E.T p (8 * k + 7) + 1)).tau p k)).toList ∧
        (XTH ((E.pre (E.T p (8 * k + 7) + 1)).tau p k)).toList.map (TH.evMap Prod.fst) ∉ O) ∧
    ((∀ t, ((E.pre t).hA 8).toList ∈ O) → ∀ p k, ¬ E.Reports O p k) ∧
    ((∀ p k, ((8 * k + 4 : ℕ) : ℕ∞) < E.len p → ((8 * k + 6 : ℕ) : ℕ∞) < E.len p) →
      (∀ t, ∃ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p ∧ t ≤ E.T p (8 * k + 7)) →
      (∃ t₀, ((E.pre t₀).hSy 8).toList ∉ O) →
      ∃ t₁, (∃ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p ∧ t₁ ≤ E.T p (8 * k + 7)) ∧
        ∀ p k, ((8 * k + 7 : ℕ) : ℕ∞) < E.len p → t₁ ≤ E.T p (8 * k + 7) → E.Reports O p k) :=
  ⟨fun p k hr => (thm_8_1 hO h𝒜 (InfExec.pre_WF hw _) (hA _)).1 p k hr,
    fun hAO p k => InfExec.no_report_of_correct hO hw hAO p k,
    fun hfair hprog ⟨_, hbad⟩ => InfExec.thm_8_1_infinite hO hw hfair hprog hbad⟩

end Podc2023.RuntimeVerification
