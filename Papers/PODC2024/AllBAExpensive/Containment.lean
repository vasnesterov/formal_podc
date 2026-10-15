import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# All Byzantine Agreement Problems Are Expensive — Lemma 7 (containment)

In synchrony, a value decided in an execution corresponding to `c` is admissible for every input
configuration `c'` contained in `c` (`c ⊒ c'`): the same execution, with the processes of
`π(c) \ π(c')` turned Byzantine (and replaying their behaviour), corresponds to `c'`.

* `AllBAExpensive.containment_auth`, `AllBAExpensive.containment`: Lemma 7.
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {A : Algorithm P M S VI VO} {val : ValidityProperty P VI VO} {Au : Auth P M K}

/-- The input configuration of `R.enlarge A c'.procsᶜ` is `c'` if `R.inputConf ⊒ c'`. -/
theorem inputConf_enlarge {R : Run P M VI} {c' : Config P VI} (hc : Contains R.inputConf c') :
    (R.enlarge A c'.procsᶜ).inputConf = c' := by
  funext p
  rw [Run.enlarge_inputConf]
  by_cases hp : c' p = none
  · simp [hp]
  · have := hc p hp
    simp only [mem_compl, Config.mem_procs_iff_ne_none]
    rw [← this]
    have hpf : p ∉ R.faulty := by
      intro h; apply hp; rw [← this]; simp [Run.inputConf, h]
    simp [Run.inputConf, hpf]

theorem faulty_subset_of_contains {R : Run P M VI} {c' : Config P VI}
    (hc : Contains R.inputConf c') : R.faulty ⊆ c'.procsᶜ := by
  intro p hp
  rw [mem_compl, Config.mem_procs_iff_ne_none, not_not]
  by_contra h
  have := hc p h
  simp [Run.inputConf, hp] at this
  exact h this.symm

/-- **Lemma 7 (containment).** Let `A` solve `val`-agreement in synchrony (authenticated model).
If a correct process decides `v` in a synchronous execution `R`, then `v ∈ val c'` for every input
configuration `c'` contained in `input_conf(R)`. -/
theorem containment_auth (hU : A.Unforging Au) (hA : SolvesConsensusAuthSync Au t δ A val)
    (htn : t < Fintype.card P) {R : Run P M VI} (hR : R.Valid t δ) (hRa : R.AuthValid Au A)
    (h0 : R.gst = 0) {p : P} (hp : p ∉ R.faulty) {v : VO} (hv : R.Decides A p v)
    {c' : Config P VI} (hc' : IsInputConfig t c') (hcont : Contains R.inputConf c') :
    v ∈ val c' := by
  have hF := faulty_subset_of_contains hcont
  obtain ⟨p', hp'⟩ : c'.procs.Nonempty := by
    rw [← card_pos]; unfold IsInputConfig at hc'; omega
  have hp'F : p' ∉ c'.procsᶜ := by rw [mem_compl, not_not]; exact hp'
  have hp'R : p' ∉ R.faulty := fun h => hp'F (hF h)
  obtain ⟨w, hw⟩ := hA.termination R hR hRa h0 p' hp'R
  obtain rfl : w = v := hA.agreement R hR hRa h0 p' hp'R p hp w v hw hv
  have hR' : (R.enlarge A c'.procsᶜ).Valid t δ :=
    Run.enlarge_valid hR hF (by
      rw [card_compl]; unfold IsInputConfig at hc'; have := c'.procs.card_le_univ; omega)
  have := hA.validity _ hR' (Run.enlarge_authValid hU hRa hF) (by simpa using h0) p' hp'F w
    ((Run.enlarge_decides hF hp'F).mpr hw)
  rwa [inputConf_enlarge hcont] at this

/-- **Lemma 7 (containment)**, unauthenticated model. -/
theorem containment (hA : SolvesConsensusSync t δ A val)
    (htn : t < Fintype.card P) {R : Run P M VI} (hR : R.Valid t δ)
    (h0 : R.gst = 0) {p : P} (hp : p ∉ R.faulty) {v : VO} (hv : R.Decides A p v)
    {c' : Config P VI} (hc' : IsInputConfig t c') (hcont : Contains R.inputConf c') :
    v ∈ val c' :=
  containment_auth A.unforging_none hA htn hR (R.authValid_none A) h0 hp hv hc' hcont

end AllBAExpensive
