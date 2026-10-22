import Papers.PODC2017.PPVerification.Prop17
import Papers.PODC2017.PPVerification.Prop18
import Papers.PODC2017.PPVerification.Lemma21
import Papers.PODC2017.PPVerification.Lemma22

/-!
# `P_thr ∈ WS³`, and `P_thr` computes the threshold predicate

* `pthr_ws3`: Propositions 17 and 18 together: `P_thr ∈ WS³`.
* `pthr_computes`: consequently (soundness of WS³, and the explicit output in the proof of
  Proposition 17) every fair execution of `P_thr` from `I(X)` stabilizes to `∑ᵢ aᵢ X(xᵢ) < c`.
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol Cslib.TransitionSystem Filter

variable (c : ℤ) {Λ : Type*} [Fintype Λ] (a : Λ → ℤ)

/-- **`P_thr ∈ WS³`** (Propositions 17 and 18). -/
theorem pthr_ws3 : WS3 (Pthr c a) := ⟨proposition_18 c a, proposition_17_Pthr c a⟩

/-- **`P_thr` computes `∑ᵢ aᵢ xᵢ < c`**: every fair execution from `I(X)` stabilizes to the
truth value of `∑ᵢ a(i) · X(i) < c`. -/
theorem pthr_computes (X : Multiset Λ) (hX : 2 ≤ Multiset.card X) (E : Run (Pthr c a).Step)
    (hE0 : E.st 0 = (Pthr c a).init X) (hE : E.EdgeFair) :
    (Pthr c a).StabilizesTo E (decide ((X.map a).sum < c)) := by
  obtain ⟨n, hn⟩ := (ws3_subset_ws2 (pthr_ws3 c a)).2 E hE
  have hterm : Terminal (Pthr c a).T (E.st n) :=
    terminal_iff_isSilent.2 (hE.globallyFair.isSilent_of_silent hn)
  have hreach : MReach (Pthr c a).T ((Pthr c a).init X) (E.st n) := hE0 ▸ E.reach n
  have hcons := consensus_of_potReach c a _ (le_vmax c a).1 hX hreach.potReach hterm
  rw [val_init] at hcons
  exact eventually_atTop.2 ⟨n, fun t ht => (hn t ht) ▸ hcons⟩

end Podc.PPVerification.Threshold
