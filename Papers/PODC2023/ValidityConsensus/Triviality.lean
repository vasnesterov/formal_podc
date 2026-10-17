import Podc.PartialSync.Triviality

/-!
# On the Validity of Consensus — §3.4 and §4.1

The proofs are in the shared library `Podc.PartialSync.Triviality`; this file states the paper's
results under their paper names.

* Lemma 1 (canonical similarity): `ValidityConsensus.canonical_similarity(_auth)`
  (`SolvesConsensusAuth.mem_of_similar`).
* Lemma 2 (merging compatible canonical executions): `ValidityConsensus.eq_of_compatible(_auth)`
  (`SolvesConsensusAuth.eq_of_compatible`).
* Lemmas 3–4, Theorem 1 (if `n ≤ 3t`, every solvable validity property is trivial):
  `ValidityConsensus.trivial_of_solvesConsensus(_auth)`, `ValidityConsensus.trivial_of_solvable`,
  `ValidityConsensus.trivial_of_solvableAuth` (with signatures) (`SolvesConsensusAuth.trivial`).
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-! All results are proved in the authenticated model (`Au`, with an unforging algorithm);
the unauthenticated statements are the special case `Au = Auth.none`. -/

/-- **Lemma 1 (canonical similarity).** In a canonical execution corresponding to `c`, a correct
process can only decide a value admissible for every input configuration similar to `c`. -/
theorem canonical_similarity_auth (hU : A.Unforging Au) (hA : SolvesConsensusAuth Au t δ A val)
    {R : Run P M VI} (hR : R.Valid t δ) (hcan : R.Canonical) {p : P} (hp : p ∉ R.faulty) {v : VO}
    (hv : R.Decides A p v) {c' : Config P VI} (hc' : IsInputConfig t c')
    (hsim : Similar c' R.inputConf) : v ∈ val c' :=
  hA.mem_of_similar hU hR hcan hp hv hc' hsim

/-- **Lemma 2 (merging).** Two canonical executions with compatible input configurations
decide the same value. -/
theorem eq_of_compatible_auth (hU : A.Unforging Au) (hA : SolvesConsensusAuth Au t δ A val)
    {R₁ R₂ : Run P M VI}
    (h₁ : R₁.Valid t δ) (h₂ : R₂.Valid t δ) (hc₁ : R₁.Canonical) (hc₂ : R₂.Canonical)
    (hcomp : Compatible t R₁.inputConf R₂.inputConf) {p₁ p₂ : P} {v₁ v₂ : VO}
    (hp₁ : p₁ ∉ R₁.faulty) (hd₁ : R₁.Decides A p₁ v₁)
    (hp₂ : p₂ ∉ R₂.faulty) (hd₂ : R₂.Decides A p₂ v₂) : v₁ = v₂ :=
  hA.eq_of_compatible hU h₁ h₂ hc₁ hc₂ hcomp hp₁ hd₁ hp₂ hd₂

/-- **Lemmas 3 and 4 / Theorem 1.** If `n ≤ 3t`, any validity property with which an algorithm
solves consensus is trivial. -/
theorem trivial_of_solvesConsensus_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val) (ht : 0 < t) (htn : t < Fintype.card P)
    (hn : Fintype.card P ≤ 3 * t) : val.Trivial t :=
  hA.trivial hU ht htn hn

/-- **Lemma 1 (canonical similarity)**, unauthenticated model. -/
theorem canonical_similarity (hA : SolvesConsensus t δ A val) {R : Run P M VI}
    (hR : R.Valid t δ) (hcan : R.Canonical) {p : P} (hp : p ∉ R.faulty) {v : VO}
    (hv : R.Decides A p v) {c' : Config P VI} (hc' : IsInputConfig t c')
    (hsim : Similar c' R.inputConf) : v ∈ val c' :=
  canonical_similarity_auth A.unforging_none (hA.auth _) hR hcan hp hv hc' hsim

/-- **Lemma 2 (merging)**, unauthenticated model. -/
theorem eq_of_compatible (hA : SolvesConsensus t δ A val) {R₁ R₂ : Run P M VI}
    (h₁ : R₁.Valid t δ) (h₂ : R₂.Valid t δ) (hc₁ : R₁.Canonical) (hc₂ : R₂.Canonical)
    (hcomp : Compatible t R₁.inputConf R₂.inputConf) {p₁ p₂ : P} {v₁ v₂ : VO}
    (hp₁ : p₁ ∉ R₁.faulty) (hd₁ : R₁.Decides A p₁ v₁)
    (hp₂ : p₂ ∉ R₂.faulty) (hd₂ : R₂.Decides A p₂ v₂) : v₁ = v₂ :=
  eq_of_compatible_auth A.unforging_none (hA.auth _) h₁ h₂ hc₁ hc₂ hcomp hp₁ hd₁ hp₂ hd₂

/-- **Theorem 1**, for a given algorithm, unauthenticated model. -/
theorem trivial_of_solvesConsensus [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (ht : 0 < t) (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) : val.Trivial t :=
  trivial_of_solvesConsensus_auth A.unforging_none (hA.auth _) ht htn hn

/-- **Theorem 1**, authenticated model: if `n ≤ 3t`, every validity property solvable with
(ideal) signatures is trivial. -/
theorem trivial_of_solvableAuth [Nonempty VI] (h : val.SolvableAuth t δ) (ht : 0 < t)
    (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) : val.Trivial t :=
  h.trivial ht htn hn

/-- **Theorem 1.** If `n ≤ 3t`, every solvable validity property is trivial. -/
theorem trivial_of_solvable [Nonempty VI] (h : val.Solvable t δ) (ht : 0 < t)
    (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) : val.Trivial t :=
  h.trivial ht htn hn

end ValidityConsensus
