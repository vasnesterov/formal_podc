import Papers.PODC2019.AutomaticSpeedup.Theorem1

/-!
# Theorem 1, (2) ⇒ (1), is false without edge symmetry breaking

The paper's proof of (2) ⇒ (1) lets both endpoints `u, v` of an edge `e` pick a pair `(o, o')`
from their two `Π_1`-outputs with `{o, o'} ∈ g_{1/2}`, `v` taking `o` and `u` taking `o'`, "by
looking only at `N^t(e)`". This needs the two endpoints to agree on who is who. If `N^t(e)` looks
the same from both sides, both endpoints make the same choice.

Counterexample. `Π` = *edge orientation*: labels `{true, false}`, an edge is good iff its two
half-edges carry different labels, every node configuration is good. Then the constant output
`{{true}, {false}}` solves `Π_1` in `0` rounds (hence in `t - 1` rounds) on every graph, but in any
graph where some edge has the same port number at both ends and both endpoints have the same view
(for instance a single edge `K_2`, or any `d`-regular graph whose port numbering is a proper edge
colouring, with no inputs), no algorithm solves `Π` at all.

`theorem_1_backward_false`: for every `t ≥ 1`, the class consisting of `K_2` alone (`n = 2`,
`Δ = 1`, simple, connected, acyclic, so of girth `∞ ≥ 2t + 2`) is `t`-independent, `Π_1` is
solvable in `t - 1` rounds and `Π` is not solvable in `t` rounds.
-/

namespace AutomaticSpeedup

open Cslib.PortNumbering Problem

/-- Edge orientation: the two half-edges of every edge carry different labels. -/
def orientation : Problem Bool where
  f _ := Set.univ
  g _ := {{true, false}}
  h Δ := {m | Multiset.card m ≤ Δ}

theorem orientation_wf : orientation.WF where
  f_finite _ := Set.toFinite _
  g_card _ m hm := by rw [Set.mem_singleton_iff.1 hm]; rfl
  g_sub _ _ _ _ _ := trivial
  h_card _ _ hm := hm
  h_sub _ _ _ _ _ := trivial

/-- The constant `Π_1`-label `{{true}, {false}}`. -/
def bothOrientations : Set (Set Bool) := {{true}, {false}}

theorem edgeAll_true_false (Δ : ℕ) : orientation.EdgeAll Δ {true} {false} :=
  ⟨Set.subset_univ _, Set.subset_univ _, by
    rintro y rfl z rfl; exact Set.mem_singleton _⟩

/-- `Π_1` for edge orientation is solvable in any number of rounds (in particular `0`) on every
class of graphs of maximum degree `≤ Δ`: output `{{true}, {false}}` everywhere. -/
theorem speedup_orientation_solvable {I : Type} {n : ℕ} (𝒢 : Set (LGraph I n)) (Δ t : ℕ)
    (hΔ : ∀ G ∈ 𝒢, ∀ v, G.deg v ≤ Δ) : SolvableIn 𝒢 orientation.speedup Δ t := by
  rw [solvableIn_iff_view]
  refine ⟨fun _ _ => bothOrientations, fun G hG => ⟨fun _ _ _ => ?_, fun _ _ _ => ?_, fun v => ?_⟩⟩
  · intro Y _; exact Set.subset_univ _
  · rw [speedup, nodeStep_g_iff]
    refine ⟨fun Y _ => Set.subset_univ _, fun Y _ => Set.subset_univ _, {true}, by simp
      [bothOrientations], {false}, by simp [bothOrientations], ?_⟩
    rw [edgeStep_g_iff]; exact edgeAll_true_false Δ
  · rw [speedup, nodeStep, Set.mem_ofPred_eq, nodeAll_map_range]
    refine ⟨hΔ G hG v, fun _ _ Y _ => Set.subset_univ _, fun y hy => ?_⟩
    refine nodeEx_map_range_of (hΔ G hG v) (fun _ _ => Set.subset_univ _)
      (fun i => if y i = {true} then true else false) (fun i hi => ?_) ?_
    · have := hy i hi
      simp only [bothOrientations, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h <;> simp [h]
    · show Multiset.card _ ≤ Δ
      simpa using hΔ G hG v

/-- If some edge of a graph in the class has the same port number at both ends and both endpoints
have the same radius-`t` view, edge orientation is not solvable in `t` rounds. -/
theorem orientation_not_solvable {I : Type} {n : ℕ} {𝒢 : Set (LGraph I n)} {Δ t : ℕ}
    {G : LGraph I n} (hG : G ∈ 𝒢) {v : Fin n} {i : ℕ} (hi : i < G.deg v)
    (hport : G.rport v i = i) (hview : G.view t (G.nbr v i) = G.view t v) :
    ¬ SolvableIn 𝒢 orientation Δ t := by
  rw [solvableIn_iff_view]
  rintro ⟨F, hF⟩
  have := (hF G hG).2.1 v i hi
  simp only [hport, hview] at this
  have h2 := Set.mem_singleton_iff.1 this
  cases hb : F (G.view t v) i <;> rw [hb] at h2 <;> simp at h2

/-! ### Symmetric graphs -/

/-- A graph is *symmetric* if all nodes have degree `d`, both ends of every edge have the same
port number (the port numbering is a proper edge colouring), and all input labels are equal. -/
structure LGraph.IsSymmetric {I : Type} {n : ℕ} (G : LGraph I n) (d : ℕ) (c : I) : Prop where
  deg_eq : ∀ v, G.deg v = d
  rport_eq : ∀ v, ∀ i < d, G.rport v i = i
  inp_eq : ∀ v i, G.inp v i = c

/-- In a symmetric graph all nodes have the same view, at every radius. -/
theorem LGraph.IsSymmetric.view_eq {I : Type} {n : ℕ} {G : LGraph I n} {d : ℕ} {c : I}
    (hG : G.IsSymmetric d c) (t : ℕ) (u v : Fin n) : G.view t u = G.view t v := by
  have hin : ∀ u v, G.inputs u = G.inputs v := by
    intro u v; simp [LGraph.inputs, hG.deg_eq, hG.inp_eq]
  induction t generalizing u v with
  | zero => exact hin u v
  | succ t ih =>
    show (G.inputs u, _) = (G.inputs v, _)
    rw [hin u v, hG.deg_eq, hG.deg_eq]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [hG.rport_eq u i hi, hG.rport_eq v i hi, ih]

/-- A class consisting of a single symmetric graph is `t`-independent for every `t`. -/
theorem isIndependent_singleton_symmetric {I : Type} {n : ℕ} {G : LGraph I n} {d : ℕ} {c : I}
    (hG : G.IsSymmetric d c) (t : ℕ) : IsIndependent ({G} : Set (LGraph I n)) t := by
  cases t with
  | zero => trivial
  | succ s =>
    refine ⟨?_, ?_⟩
    · intro G' hG' v i hi H₁ hH₁ w₁ k₁ hk₁ he₁ H₂ hH₂ w₂ k₂ hk₂ he₂
      obtain rfl : G' = G := hG'
      obtain rfl : H₁ = G' := hH₁
      obtain rfl : H₂ = H₁ := hH₂
      exact ⟨_, rfl, v, i, hi, rfl, hG.view_eq _ _ _, hG.view_eq _ _ _⟩
    · intro G' hG' v Hs ws hws
      obtain rfl : G' = G := hG'
      refine ⟨_, rfl, v, rfl, fun i hi => ?_⟩
      obtain ⟨hH, -⟩ := hws i hi
      rw [Set.mem_singleton_iff] at hH
      rw [hH]
      have hd : i < d := hG.deg_eq v ▸ hi
      simp only [LGraph.eview, hG.rport_eq _ i hd, hG.view_eq s v (ws i),
        hG.view_eq s (G'.nbr v i) (G'.nbr (ws i) i)]

/-- **Counterexample to Theorem 1, (2) ⇒ (1), for every class consisting of a symmetric graph
with at least one edge.** -/
theorem theorem_1_backward_false_of_symmetric {I : Type} {n : ℕ} {G : LGraph I n} {d : ℕ} {c : I}
    (hG : G.IsSymmetric d c) (hd : 1 ≤ d) (t : ℕ) (hn : 0 < n) :
    IsIndependent ({G} : Set (LGraph I n)) t ∧
      SolvableIn ({G} : Set (LGraph I n)) orientation.speedup d (t - 1) ∧
      ¬ SolvableIn ({G} : Set (LGraph I n)) orientation d t := by
  refine ⟨isIndependent_singleton_symmetric hG t, speedup_orientation_solvable _ _ _ ?_, ?_⟩
  · intro G' hG' v; rw [Set.mem_singleton_iff.1 hG', hG.deg_eq]
  · have h0 : 0 < G.deg ⟨0, hn⟩ := by rw [hG.deg_eq]; omega
    exact orientation_not_solvable rfl h0 (hG.rport_eq _ 0 hd) (hG.view_eq _ _ _)

/-! ### The single edge `K_2` -/

/-- The single edge on `Fin 2`, port `0` at both ends. -/
def k2PN : PNGraph (Fin 2) where
  deg _ := 1
  p v _ := (Fin.rev v, 0)
  p_lt _ _ _ := Nat.one_pos
  p_p v i hi := by
    have : i = 0 := by omega
    subst this; simp

/-- `K_2` without inputs. -/
def k2 : LGraph Unit 2 := ⟨k2PN, fun _ _ => ()⟩

theorem k2_isSymmetric : k2.IsSymmetric 1 () :=
  ⟨fun _ => rfl, fun _ i hi => by simp only [Nat.lt_one_iff] at hi; subst hi; rfl, fun _ _ => rfl⟩

theorem k2_isSimple : k2.G.IsSimple := by
  refine ⟨fun v i _ => ?_, fun v i j hi hj _ => ?_⟩
  · show Fin.rev v ≠ v
    fin_cases v <;> decide
  · change i < 1 at hi; change j < 1 at hj; omega

theorem k2_adj (u v : Fin 2) : k2.G.toSimpleGraph.Adj u v ↔ u ≠ v := by
  rw [PNGraph.toSimpleGraph_adj]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, 0, Nat.one_pos, ?_⟩
    show Fin.rev u = v
    fin_cases u <;> fin_cases v <;> simp_all

theorem k2_connected : k2.G.toSimpleGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨0⟩⟩
  by_cases h : u = v
  · subst h; rfl
  · exact ((k2_adj u v).2 h).reachable

theorem k2_isAcyclic : k2.G.toSimpleGraph.IsAcyclic := by
  intro v c hc
  have h3 := hc.three_le_length
  have hnd := hc.support_nodup
  have hlen := hnd.length_le_card
  simp only [List.length_tail, SimpleGraph.Walk.length_support, Fintype.card_fin] at hlen
  omega

/-- **Theorem 1, (2) ⇒ (1), is false as stated.** For every `t ≥ 1` there is a class `𝒢` of
`n`-node graphs of maximum degree `Δ` (here `𝒢 = {K_2}`, `n = 2`, `Δ = 1`: simple, connected,
`1`-regular, girth `∞ ≥ 2t + 2`), which is `t`-independent, and a problem `Π` satisfying the
paper's definition (`WF`), such that `Π_1` is solvable in `t - 1` rounds, but `Π` is not solvable
in `t` rounds. -/
theorem theorem_1_backward_false (t : ℕ) :
    ∃ (𝒢 : Set (LGraph Unit 2)) (P : Problem Bool),
      (∀ G ∈ 𝒢, G.G.IsSimple ∧ G.G.toSimpleGraph.Connected ∧
        ((2 * t + 2 : ℕ) : ℕ∞) ≤ G.G.toSimpleGraph.egirth ∧ ∀ v, G.deg v = 1) ∧
      IsIndependent 𝒢 t ∧ P.WF ∧
      SolvableIn 𝒢 P.speedup 1 (t - 1) ∧ ¬ SolvableIn 𝒢 P 1 t := by
  obtain ⟨h1, h2, h3⟩ := theorem_1_backward_false_of_symmetric k2_isSymmetric le_rfl t two_pos
  refine ⟨{k2}, orientation, fun G hG => ?_, h1, orientation_wf, h2, h3⟩
  rw [Set.mem_singleton_iff.1 hG]
  exact ⟨k2_isSimple, k2_connected, by rw [k2_isAcyclic.egirth_eq_top]; exact le_top,
    fun _ => rfl⟩

end AutomaticSpeedup
