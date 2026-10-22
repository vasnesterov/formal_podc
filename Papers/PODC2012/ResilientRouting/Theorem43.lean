import Papers.PODC2012.ResilientRouting.Fig3
import Papers.PODC2012.ResilientRouting.Lemma41

/-!
# Theorem 4.3: no perfectly resilient forwarding pattern for the network of Figure 3

The proof follows the paper's strategy, with the two gaps repaired.

* **Node 1 routes cyclically** (the instance of Lemma 4.2 that is needed). Let `σ` be the
  forwarding function of node `1` when its four links are up. For `w ∈ {2,3,4,5}` consider the
  scenario in which only the four links of `1` and a path `w – m – d` survive. Every other
  neighbour of `1` is a dead end, so a packet from a node `x ≠ w` bounces between `1` and the
  dead ends along the `σ`-orbit of `x` until it reaches `w`; hence no proper non-empty subset
  of `{2,3,4,5}` avoiding `w` is closed under `σ` (`closed_false`). Therefore `σ` is a 4-cycle
  `5 ↦ a ↦ b ↦ c ↦ 5` (`exists_cycle`; a finite check).
* **The failure scenario of Figure 3** (for the cycle `(5 a b c)`; the figure is the case
  `a, b, c = 2, 3, 4`): the surviving links are `1–2, 1–3, 1–4, 1–5`, `a – X – c` and
  `b – Y – d`, where `X` is the node of the pair `{a, c}` and `Y` the node of `{b, 5}`. The paper
  applies Lemma 4.1 to node `a` here, but every path from `a` to `d` passes through `1`, so
  Lemma 4.1 does not apply. Instead, three more scenarios with the same local views (`pass_through`)
  show that `a` forwards packets from `1` to `X`, `X` forwards packets from `a` to `c`, and `c`
  forwards packets from `X` to `1`. Then a packet of node `5` (whose only live link is to `1`)
  travels `5 → 1 → a → X → c → 1 → 5 → 1 → …` and never reaches `d` (`final_false`).

Only condition (1) of resilience is used, so even the weaker requirement "every node connected to
`d` has a forwarding path to `d`" cannot be met.
-/

namespace Podc.ResilientRouting.Fig3

open SimpleGraph

/-- The neighbours of node `1`. -/
def N1 : List (Fin 12) := [2, 3, 4, 5]

/-- An escape node for `w ∈ {2,3,4,5}`: adjacent to `w` and to `d`. -/
def M (w : Fin 12) : Fin 12 := if w = 2 then 6 else if w = 3 then 7 else if w = 4 then 8 else 9

/-- Surviving links: the links of `1` and the path `w – M w – d`. -/
def Lw (w : Fin 12) : List (Fin 12 × Fin 12) := [(1, 2), (1, 3), (1, 4), (1, 5), (w, M w), (M w, 0)]

set_option maxRecDepth 100000 in
theorem facts_Lw : ∀ w ∈ N1,
    (∀ u, G.Adj 1 u → memB (Lw w) 1 u = true) ∧
    (∀ x ∈ N1, x ≠ w → ∀ y, Live G (scen (Lw w)) x y → y = 1) ∧
    (∀ x ∈ N1, Live G (scen (Lw w)) x 1 ∧ x ≠ 0) ∧
    Live G (scen (Lw w)) 1 w ∧ Live G (scen (Lw w)) w (M w) ∧ Live G (scen (Lw w)) (M w) 0 := by
  decide

theorem adj_one_iff : ∀ y, G.Adj 1 y ↔ y ∈ N1 := by decide

section

variable {f : Pattern G} (hf : PerfectlyResilient G d f)
include hf

/-- No proper non-empty subset `C` of the neighbours of `1` that avoids some neighbour `w` is
closed under the forwarding function of node `1` (with all links of `1` up). -/
theorem closed_false {w : Fin 12} (hw : w ∈ N1) {C : List (Fin 12)} (hC : ∀ x ∈ C, x ∈ N1)
    (hwC : w ∉ C) {x₀ : Fin 12} (hx₀ : x₀ ∈ C) (hcl : ∀ x ∈ C, f.next 1 A1 x ∈ C) : False := by
  obtain ⟨hA, hdead, hspoke, h1w, hwM, hM0⟩ := facts_Lw w hw
  have hv1 : view G (scen (Lw w)) 1 = A1 := view_eq_A1 hA
  have hne : ∀ x ∈ C, x ≠ w := fun x hx h => hwC (h ▸ hx)
  refine not_good_of_trap (f := f) {δ | (δ.1 ∈ C ∧ δ.2 = 1) ∨ (δ.1 = 1 ∧ δ.2 ∈ C)} ?_
    (hspoke x₀ (hC x₀ hx₀)).2
    (((reachable_of_live (hspoke x₀ (hC x₀ hx₀)).1).trans (reachable_of_live h1w)).trans
      ((reachable_of_live hwM).trans (reachable_of_live hM0)))
    (fun y hy => Or.inl ⟨hx₀, hdead x₀ (hC x₀ hx₀) (hne x₀ hx₀) y hy⟩)
    (hf _ (scen_subset _))
  rintro ⟨x, y⟩ hδ _
  rcases hδ with ⟨hx, rfl⟩ | ⟨rfl, hy⟩
  · refine ⟨show (1 : Fin 12) ≠ 0 by decide, fun _ => Or.inr ⟨rfl, ?_⟩⟩
    simp only [nxt, hv1]
    exact hcl x hx
  · refine ⟨(hspoke y (hC y hy)).2, fun hl => Or.inl ⟨hy, ?_⟩⟩
    exact hdead y (hC y hy) (hne y hy) _ hl

end

/-! ### `σ` is a 4-cycle -/

/-- The table of a function on `{2,3,4,5}`. -/
def tab (s₂ s₃ s₄ s₅ x : Fin 12) : Fin 12 :=
  if x = 2 then s₂ else if x = 3 then s₃ else if x = 4 then s₄ else s₅

/-- The proper non-empty subsets of `{2,3,4,5}`, each with a node of `{2,3,4,5}` outside it. -/
def pieces : List (List (Fin 12) × Fin 12) :=
  [([2], 3), ([3], 2), ([4], 2), ([5], 2), ([2, 3], 4), ([2, 4], 3), ([2, 5], 3), ([3, 4], 2),
   ([3, 5], 2), ([4, 5], 2), ([2, 3, 4], 5), ([2, 3, 5], 4), ([2, 4, 5], 3), ([3, 4, 5], 2)]

/-- The 4-cycles `5 ↦ a ↦ b ↦ c ↦ 5`, as triples `(a, b, c)`. -/
def cycles : List (Fin 12 × Fin 12 × Fin 12) :=
  [(2, 3, 4), (2, 4, 3), (3, 2, 4), (3, 4, 2), (4, 2, 3), (4, 3, 2)]

theorem pieces_ok : ∀ p ∈ pieces, p.2 ∈ N1 ∧ (∀ x ∈ p.1, x ∈ N1) ∧ p.2 ∉ p.1 ∧ p.1 ≠ [] := by
  decide

set_option maxRecDepth 100000 in
theorem cycle_of_tab : ∀ s₂ ∈ N1, ∀ s₃ ∈ N1, ∀ s₄ ∈ N1, ∀ s₅ ∈ N1,
    (∀ p ∈ pieces, ∃ x ∈ p.1, tab s₂ s₃ s₄ s₅ x ∉ p.1) →
    ∃ t ∈ cycles, tab s₂ s₃ s₄ s₅ 5 = t.1 ∧ tab s₂ s₃ s₄ s₅ t.1 = t.2.1 ∧
      tab s₂ s₃ s₄ s₅ t.2.1 = t.2.2 ∧ tab s₂ s₃ s₄ s₅ t.2.2 = 5 := by
  decide

set_option maxRecDepth 100000 in
theorem cycles_mem : ∀ t ∈ cycles, t.1 ∈ N1 ∧ t.2.1 ∈ N1 ∧ t.2.2 ∈ N1 := by decide

/-- The forwarding function of node `1` (all four links up) is a 4-cycle on `{2,3,4,5}`
(Lemma 4.2 for node `1` of Figure 3). -/
theorem exists_cycle {f : Pattern G} (hf : PerfectlyResilient G d f) :
    ∃ t ∈ cycles, f.next 1 A1 5 = t.1 ∧ f.next 1 A1 t.1 = t.2.1 ∧ f.next 1 A1 t.2.1 = t.2.2 ∧
      f.next 1 A1 t.2.2 = 5 := by
  set σ := f.next 1 A1
  have hσ : ∀ x ∈ N1, σ x ∈ N1 := fun x hx =>
    (adj_one_iff _).1 (f.adj_next 1 A1 x ((adj_one_iff x).2 hx))
  have htab : ∀ x ∈ N1, tab (σ 2) (σ 3) (σ 4) (σ 5) x = σ x := by
    intro x hx
    simp only [N1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [tab]
  have hp : ∀ p ∈ pieces, ∃ x ∈ p.1, tab (σ 2) (σ 3) (σ 4) (σ 5) x ∉ p.1 := by
    intro p hp
    obtain ⟨hw, hC, hwC, hne⟩ := pieces_ok p hp
    by_contra hcon
    push Not at hcon
    obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil _ hne
    refine closed_false hf hw hC hwC hx₀ fun x hx => ?_
    have := hcon x hx
    rwa [htab x (hC x hx)] at this
  obtain ⟨t, ht, h1, h2, h3, h4⟩ := cycle_of_tab _ (hσ 2 (by decide)) _ (hσ 3 (by decide)) _
    (hσ 4 (by decide)) _ (hσ 5 (by decide)) hp
  obtain ⟨ha, hb, hc⟩ := cycles_mem t ht
  refine ⟨t, ht, ?_, ?_, ?_, ?_⟩
  · rwa [htab 5 (by decide)] at h1
  · rwa [htab _ ha] at h2
  · rwa [htab _ hb] at h3
  · rwa [htab _ hc] at h4

/-! ### The scenario of Figure 3 and three auxiliary scenarios -/

section Scenarios

variable (t : Fin 12 × Fin 12 × Fin 12)

/-- The scenario of Figure 3 for the cycle `(5 a b c)`. -/
def Lmain : List (Fin 12 × Fin 12) :=
  [(1, 2), (1, 3), (1, 4), (1, 5), (t.1, mid t.1 t.2.2), (mid t.1 t.2.2, t.2.2),
   (t.2.1, mid t.2.1 5), (mid t.2.1 5, 0)]

/-- `1 – a – X – d`: `a` must pass packets from `1` on to `X`. -/
def Li : List (Fin 12 × Fin 12) := [(1, t.1), (t.1, mid t.1 t.2.2), (mid t.1 t.2.2, 0)]

/-- `a – X – c – Z – d`: `X` must pass packets from `a` on to `c`. -/
def Lii : List (Fin 12 × Fin 12) :=
  [(t.1, mid t.1 t.2.2), (mid t.1 t.2.2, t.2.2), (t.2.2, mid t.2.2 5), (mid t.2.2 5, 0)]

/-- `X – c – 1 – b – Y – d`: `c` must pass packets from `X` on to `1`. -/
def Liii : List (Fin 12 × Fin 12) :=
  [(mid t.1 t.2.2, t.2.2), (t.2.2, 1), (1, t.2.1), (t.2.1, mid t.2.1 5), (mid t.2.1 5, 0)]

end Scenarios

set_option maxRecDepth 100000 in
theorem facts_i : ∀ t ∈ cycles,
    t.1 ≠ 0 ∧ Live G (scen (Li t)) 1 t.1 ∧ Live G (scen (Li t)) t.1 (mid t.1 t.2.2) ∧
    Live G (scen (Li t)) (mid t.1 t.2.2) 0 ∧ (∀ y, Live G (scen (Li t)) 1 y → y = t.1) ∧
    (∀ y, Live G (scen (Li t)) t.1 y → y = 1 ∨ y = mid t.1 t.2.2) ∧
    ∀ u, memB (Li t) t.1 u = memB (Lmain t) t.1 u := by
  decide

set_option maxRecDepth 100000 in
theorem facts_ii : ∀ t ∈ cycles,
    t.1 ≠ 0 ∧ mid t.1 t.2.2 ≠ 0 ∧ Live G (scen (Lii t)) t.1 (mid t.1 t.2.2) ∧
    Live G (scen (Lii t)) (mid t.1 t.2.2) t.2.2 ∧ Live G (scen (Lii t)) t.2.2 (mid t.2.2 5) ∧
    Live G (scen (Lii t)) (mid t.2.2 5) 0 ∧ (∀ y, Live G (scen (Lii t)) t.1 y → y = mid t.1 t.2.2) ∧
    (∀ y, Live G (scen (Lii t)) (mid t.1 t.2.2) y → y = t.1 ∨ y = t.2.2) ∧
    ∀ u, memB (Lii t) (mid t.1 t.2.2) u = memB (Lmain t) (mid t.1 t.2.2) u := by
  decide

set_option maxRecDepth 100000 in
theorem facts_iii : ∀ t ∈ cycles,
    mid t.1 t.2.2 ≠ 0 ∧ t.2.2 ≠ 0 ∧ Live G (scen (Liii t)) (mid t.1 t.2.2) t.2.2 ∧
    Live G (scen (Liii t)) t.2.2 1 ∧ Live G (scen (Liii t)) 1 t.2.1 ∧
    Live G (scen (Liii t)) t.2.1 (mid t.2.1 5) ∧ Live G (scen (Liii t)) (mid t.2.1 5) 0 ∧
    (∀ y, Live G (scen (Liii t)) (mid t.1 t.2.2) y → y = t.2.2) ∧
    (∀ y, Live G (scen (Liii t)) t.2.2 y → y = mid t.1 t.2.2 ∨ y = 1) ∧
    ∀ u, memB (Liii t) t.2.2 u = memB (Lmain t) t.2.2 u := by
  decide

set_option maxRecDepth 100000 in
theorem facts_main : ∀ t ∈ cycles,
    (∀ u, G.Adj 1 u → memB (Lmain t) 1 u = true) ∧
    Live G (scen (Lmain t)) 5 1 ∧ Live G (scen (Lmain t)) 1 t.2.1 ∧
    Live G (scen (Lmain t)) t.2.1 (mid t.2.1 5) ∧ Live G (scen (Lmain t)) (mid t.2.1 5) 0 ∧
    (∀ y, Live G (scen (Lmain t)) 5 y → y = 1) ∧
    t.1 ≠ 0 ∧ mid t.1 t.2.2 ≠ 0 ∧ t.2.2 ≠ 0 := by
  decide

/-- The final step: with `σ = (5 a b c)`, node `5` has no forwarding path to `d` in the scenario
of Figure 3. -/
theorem final_false {f : Pattern G} (hf : PerfectlyResilient G d f) {t : Fin 12 × Fin 12 × Fin 12}
    (ht : t ∈ cycles) (h5 : f.next 1 A1 5 = t.1) (hc : f.next 1 A1 t.2.2 = 5) : False := by
  obtain ⟨hA, l51, l1b, lbY, lY0, h5only, ha0, hX0, hc0⟩ := facts_main t ht
  -- (i): `a` passes packets from `1` to `X`
  obtain ⟨-, i1, i2, i3, i4, i5, i6⟩ := facts_i t ht
  have pi := pass_through (hf _ (scen_subset (Li t))) (by decide) ha0
    ((reachable_of_live i1).trans ((reachable_of_live i2).trans (reachable_of_live i3))) i4 i5
  rw [view_congr i6] at pi
  -- (ii): `X` passes packets from `a` to `c`
  obtain ⟨-, -, j1, j2, j3, j4, j5, j6, j7⟩ := facts_ii t ht
  have pii := pass_through (hf _ (scen_subset (Lii t))) ha0 hX0
    ((reachable_of_live j1).trans ((reachable_of_live j2).trans
      ((reachable_of_live j3).trans (reachable_of_live j4)))) j5 j6
  rw [view_congr j7] at pii
  -- (iii): `c` passes packets from `X` to `1`
  obtain ⟨-, -, k1, k2, k3, k4, k5, k6, k7, k8⟩ := facts_iii t ht
  have piii := pass_through (hf _ (scen_subset (Liii t))) hX0 hc0
    ((reachable_of_live k1).trans ((reachable_of_live k2).trans ((reachable_of_live k3).trans
      ((reachable_of_live k4).trans (reachable_of_live k5))))) k6 k7
  rw [view_congr k8] at piii
  -- the trap in the scenario of Figure 3
  have hv1 : view G (scen (Lmain t)) 1 = A1 := view_eq_A1 hA
  refine not_good_of_trap (f := f)
    {(5, 1), (1, t.1), (t.1, mid t.1 t.2.2), (mid t.1 t.2.2, t.2.2), (t.2.2, 1), (1, 5)} ?_
    (by decide) ((reachable_of_live l51).trans ((reachable_of_live l1b).trans
      ((reachable_of_live lbY).trans (reachable_of_live lY0))))
    (fun y hy => by simp [h5only y hy]) (hf _ (scen_subset _))
  intro δ hδ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
  rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨show (1 : Fin 12) ≠ 0 by decide, fun _ => by simp [nxt, hv1, h5]⟩
  · exact ⟨ha0, fun _ => by simp [nxt, pi]⟩
  · exact ⟨hX0, fun _ => by simp [nxt, pii]⟩
  · exact ⟨hc0, fun _ => by simp [nxt, piii]⟩
  · exact ⟨show (1 : Fin 12) ≠ 0 by decide, fun _ => by simp [nxt, hv1, hc]⟩
  · refine ⟨show (5 : Fin 12) ≠ 0 by decide, fun hl => ?_⟩
    have h := h5only _ hl
    simp only [nxt] at h
    simp [nxt, h]

/-- **Theorem 4.3.** There is a network (Figure 3) for which no perfectly resilient forwarding
pattern exists. -/
theorem theorem_4_3 : ¬ ∃ f : Pattern G, PerfectlyResilient G d f := by
  rintro ⟨f, hf⟩
  obtain ⟨t, ht, h5, -, -, hc⟩ := exists_cycle hf
  exact final_false hf ht h5 hc

end Podc.ResilientRouting.Fig3

namespace Podc.ResilientRouting

/-- **Theorem 4.3** (existential form). There exists a connected network for which no perfectly
resilient forwarding pattern exists. -/
theorem theorem_4_3 : ∃ (G : SimpleGraph (Fin 12)) (d : Fin 12), G.Connected ∧
    ¬ ∃ f : Pattern G, PerfectlyResilient G d f :=
  ⟨Fig3.G, Fig3.d, Fig3.connected, Fig3.theorem_4_3⟩

end Podc.ResilientRouting
