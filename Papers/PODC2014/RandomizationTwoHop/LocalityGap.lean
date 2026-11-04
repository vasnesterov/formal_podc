import Papers.PODC2014.RandomizationTwoHop.Theorem2

/-!
# The locality claim in the proof of Lemma 9 needs one more level of view with port numbers

The proof of Lemma 9 uses that the first `k` rounds of an execution at `v` are determined by the
view `L_k(v)` and the random bits. With port numbers this is off by more than the paper allows:
already one round is not determined by `L_2(v)` (tree depth 1), because the port number at the
neighbour's end of an edge depends on the colours of the neighbour's *other* neighbours.

`locality_gap`: two 2-hop coloured paths `1 – 2 – 3` and `1 – 2 – 0` (labels: degree and colour),
the endpoint `0` has the same view `L_2` in both, yet after one round of a deterministic
algorithm (every node sends its port number) it is in different states, with the colour-sorted
port numbering used by `A*` in its simulations. (Any port numbering that is a local function of
the colours has this problem.)
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

/-- A path on three nodes with labels `(degree, colour)`. -/
def path3 (c : Fin 3 → ℕ) : LGraph (ℕ × ℕ) where
  V := Fin 3
  G := pathGraph 3
  conn := pathGraph_connected 2
  lab i := (if i = 1 then 2 else 1, c i)

/-- The endpoint `0` of the path. -/
def p0 (c : Fin 3 → ℕ) : (path3 c).V := (0 : Fin 3)

/-- Every node sends its port number; the state after round 1 is the number received on port 0. -/
def sendPort : RAlg ℕ ℕ := ⟨Option ℕ, ℕ, fun _ _ => none, fun _ i => i, fun _ _ m => m 0, id⟩

def colG : Fin 3 → ℕ := ![1, 2, 3]
def colH : Fin 3 → ℕ := ![1, 2, 0]

theorem path3_twoHop (c : Fin 3 → ℕ) (hc : Function.Injective c) :
    IsTwoHopColoring (path3 c).G (Prod.snd ∘ (path3 c).lab) :=
  fun _ _ hne _ h => hne (hc h)

theorem pathGraph3_nbr0 : (pathGraph 3).neighborSet 0 = {1} := by
  ext w; fin_cases w <;> simp [pathGraph_adj]

theorem rankC_path3 (c : Fin 3 → ℕ) (v : Fin 3) (a : ℕ) :
    rankC (pathGraph 3) c v a = ((Finset.univ.filter fun w : Fin 3 =>
      (v.val + 1 = w.val ∨ w.val + 1 = v.val) ∧ c w < a)).card := by
  unfold rankC
  rw [← Set.ncard_coe_finset]; congr 1; ext w; simp [pathGraph_adj]

theorem cdeg_path3_0 : cdeg (pathGraph 3) 0 = 1 := by
  unfold cdeg; rw [pathGraph3_nbr0]; simp

/-- The state of node `0` after one round. -/
theorem sendPort_round1 (c : Fin 3 → ℕ) (hc : Function.Injective c) (β : Fin 3 → ℕ → Bool) :
    runX sendPort (path3 c) β 1 (p0 c) = some (rankC (pathGraph 3) c 1 (c 0)) := by
  have hN : NbhdInj (path3 c).G (Prod.snd ∘ (path3 c).lab) :=
    nbhdInj_of_twoHop (path3_twoHop c hc)
  have hadj : (pathGraph 3).Adj 0 1 := by simp [pathGraph_adj]
  have hr : rankC (pathGraph 3) c 0 (c 1) = 0 := by
    rw [rankC_path3]; simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ ⟨hw, _⟩; fin_cases w <;> simp_all
  have hpick : pick (pathGraph 3) c 0 0 = 1 := by
    have := pick_rankC (G := pathGraph 3) (c := c) hN hadj; rwa [hr] at this
  simp only [runX, runC, RAlg.decided, RAlg.state, RAlg.inbox, sendPort]
  rw [colorPN_deg hN, colorPN_rport hN]
  change (none : Option ℕ).or (if 0 < cdeg (pathGraph 3) 0 then
    some (rankC (pathGraph 3) c (pick (pathGraph 3) c 0 0) (c 0)) else none) = _
  rw [cdeg_path3_0, hpick]; rfl

/-- **The locality claim used in Lemma 9 fails with port numbers.** -/
theorem locality_gap :
    IsTwoHopColoring (path3 colG).G (Prod.snd ∘ (path3 colG).lab) ∧
    IsTwoHopColoring (path3 colH).G (Prod.snd ∘ (path3 colH).lab) ∧
    ViewEq (path3 colG) (p0 colG) (path3 colH) (p0 colH) 2 ∧ sendPort.IsDeterministic ∧
    ∀ β : Fin 3 → ℕ → Bool,
      runX sendPort (path3 colG) β 1 (p0 colG) ≠ runX sendPort (path3 colH) β 1 (p0 colH) := by
  have hG : Function.Injective colG := by decide
  have hH : Function.Injective colH := by decide
  refine ⟨path3_twoHop _ hG, path3_twoHop _ hH, ?_, fun _ _ _ _ => rfl, fun β => ?_⟩
  · refine ⟨rfl, Equiv.refl _, fun w => ?_⟩
    obtain ⟨w, hw⟩ := w
    change w ∈ (pathGraph 3).neighborSet 0 at hw
    rw [pathGraph3_nbr0] at hw
    subst hw; rfl
  · rw [sendPort_round1 _ hG, sendPort_round1 _ hH, rankC_path3, rankC_path3]
    decide

end Podc.RandomizationTwoHop
