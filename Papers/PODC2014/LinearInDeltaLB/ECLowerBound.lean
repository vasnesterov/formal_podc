import Papers.PODC2014.LinearInDeltaLB.ECConfig

/-!
# Step 1 of [GHS14]: the maximal FM problem needs time `k - 1` on loopy EC-graphs

Section 4 of [M. Göös, J. Hirvonen, J. Suomela, *Linear-in-Δ lower bounds in the LOCAL model*,
PODC 2014]. We build, for `i = 0, …, k - 2`, pairs of good configurations (finite trees with loops,
every node with at least `k - 1 - i` loops) whose roots have equal radius-`i` views, carry a loop of
a common colour `c`, and receive different weights on it (invariant `Inv`, properties (P1)–(P3)).

* Base case (Section 4.2): `exists_inv_zero`. The paper takes `c₀` to be the colour of the removed
  loop `e`; but `e` is absent from `H₀`, so we take a colour `c₀ ≠ e` on which the outputs differ
  (it exists because both nodes are saturated and `y(e) ≠ 0`).
* Inductive step (Section 4.3), unfold and mix: `Inv.step`. The propagation principle (Fact 3) is
  `propagation`; the propagation walk is replaced by choosing a node with an "incoming
  disagreement" that is farthest from the root. View agreement (equation (3)) is proved by a mutual
  induction on the radius over the two halves of the mixed graph.
* Main results: `ECAlg.exists_pair` and `ECAlg.le_runTime`.
-/

namespace Podc.LinearInDeltaLB

open Cslib.ColourSystem FreeCox Pointwise Cfg

variable {k : ℕ}

/-- Fact 3 of [GHS14] (propagation principle): if two weightings give the same total load on a
node and disagree on one incident edge, they disagree on another incident edge. -/
theorem propagation {F : Finset (Fin k)} {y y' : Fin k → ℝ} (h : ∑ d ∈ F, y d = ∑ d ∈ F, y' d)
    {p : Fin k} (hp : p ∈ F) (hne : y p ≠ y' p) : ∃ d ∈ F, d ≠ p ∧ y d ≠ y' d := by
  classical
  by_contra hcon
  push Not at hcon
  rw [← Finset.add_sum_erase F y hp, ← Finset.add_sum_erase F y' hp,
    Finset.sum_congr rfl fun d hd =>
      hcon d (Finset.mem_of_mem_erase hd) (Finset.ne_of_mem_erase hd)] at h
  exact hne (add_right_cancel h)

/-- The invariant of Section 4.1 of [GHS14] at level `i`, for the pair `(G_i, H_i) = (C, D)` rooted
at `g_i = h_i = 1`: (P1) equal radius-`i` views and a common colour-`c` loop at the roots with
different weights, (P2)–(P3) via `Cfg.Good`. -/
structure Inv (A : ECAlg k) (i : ℕ) (C D : Cfg k) (c : Fin k) : Prop where
  goodC : C.Good i
  goodD : D.Good i
  notC : gen c ∉ C.T
  notD : gen c ∉ D.T
  loopC : c ∈ C.L 1
  loopD : c ∈ D.L 1
  ball_eq : ball (C.view 1) i = ball (D.view 1) i
  ne : A (C.view 1) c ≠ A (D.view 1) c

variable {A : ECAlg k} {i : ℕ} {C D : Cfg k} {c : Fin k}

theorem Inv.symm (h : Inv A i C D c) : Inv A i D C c :=
  ⟨h.goodD, h.goodC, h.notD, h.notC, h.loopD, h.loopC, h.ball_eq.symm, h.ne.symm⟩

theorem loop_of_step {X : Cfg k} {s : FreeCox k} {d : Fin k} (h : X.graph.step s d = some s) :
    s * gen d ∉ X.T ∧ d ∈ X.L s := by
  rcases (graph_step_eq_some h).2 with ⟨-, h1⟩ | ⟨h1, h2, -⟩
  · exact absurd (by simpa using congrArg (s⁻¹ * ·) h1) (gen_ne_one d).symm
  · exact ⟨h1, h2⟩

/-! ### Base case -/

/-- A single node with loops of the colours in `L`. -/
def single (L : Set (Fin k)) : Cfg k := ⟨{1}, fun _ => L⟩

theorem good_single (L : Set (Fin k)) (e : Fin k) (hL : ∀ d, d ≠ e → d ∈ L) :
    (single L).Good 0 := by
  classical
  refine ⟨⟨rfl, fun x hx d hd => ?_⟩, Set.finite_singleton _, fun x hx => ?_⟩
  · simp only [single, Set.mem_singleton_iff] at hx; subst hx; simp at hd
  · simp only [single, Set.mem_singleton_iff] at hx
    subst hx
    refine (Finset.card_le_card (t := {e}) fun d hd => ?_).trans (by simp)
    rw [mem_bad] at hd
    simp only [single, Set.mem_singleton_iff, one_mul, gen_ne_one, false_or] at hd
    simpa using fun h => hd (hL d h)

theorem single_step_isSome (L : Set (Fin k)) (d : Fin k) :
    ((single L).graph.step 1 d).isSome ↔ d ∈ L := by
  simp [graph, single, tGraph_step_isSome, gen_ne_one]

/-- Section 4.2 of [GHS14] (base case `i = 0`). -/
theorem exists_inv_zero (hk : 2 ≤ k) (hA : A.SolvesLoopy) : ∃ C D c, Inv A 0 C D c := by
  classical
  set C := single (k := k) Set.univ
  have hC : C.Good 0 := good_single _ ⟨0, by omega⟩ (by simp)
  set y := A (C.view 1)
  have hy : ∑ d, y d = 1 := by
    have := hC.load_eq_one hA (by omega) rfl
    unfold load at this
    simpa [C, single_step_isSome] using this
  obtain ⟨e, he⟩ : ∃ e, y e ≠ 0 := by
    by_contra h; push Not at h; simp [h] at hy
  set D := single (k := k) {e}ᶜ
  have hD : D.Good 0 := good_single _ e (by simp)
  set y' := A (D.view 1)
  have hy' : ∑ d ∈ Finset.univ.erase e, y' d = 1 := by
    have := hD.load_eq_one hA (by omega) rfl
    unfold load at this
    rw [← this]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d; simp [D, single_step_isSome]
  obtain ⟨c, hc, hne⟩ : ∃ c, c ≠ e ∧ y c ≠ y' c := by
    by_contra h
    push Not at h
    have : ∑ d ∈ Finset.univ.erase e, y d = 1 := by
      rw [← hy']; exact Finset.sum_congr rfl fun d hd => h d (Finset.ne_of_mem_erase hd)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), this] at hy
    exact he (by linarith)
  refine ⟨C, D, c, hC, hD, ?_, ?_, trivial, by simpa [D, single] using hc,
    ball_view_zero _ _ _ _, hne⟩ <;> simp [C, D, single, gen_ne_one]

/-! ### Inductive step -/

/-- Section 4.3 of [GHS14] (unfold and mix), in the case where the weight of the new edge
`{g, h}` differs from the weight of `e`: the new pair is `(GG, GH)`. -/
theorem Inv.step_core (hA : A.SolvesLoopy) (h : Inv A i C D c) (hik : i + 2 < k)
    (hne : A ((C.mix D c).view 1) c ≠ A (C.view 1) c) : ∃ C' D' c', Inv A (i + 1) C' D' c' := by
  classical
  have hCcs := h.goodC.1
  have hDcs := h.goodD.1
  have hGG : (C.mix C c).Good (i + 1) := h.goodC.mix h.goodC h.notC h.notC
  have hGH : (C.mix D c).Good (i + 1) := h.goodC.mix h.goodD h.notC h.notD
  have hik' : i + 1 + 1 < k := by omega
  -- view agreement, equation (3): mutual induction on the radius
  have hQ : ∀ r ≤ i + 1,
      (∀ x ∈ C.T, ball ((C.mix C c).view x) r = ball ((C.mix D c).view x) r) ∧
      (∀ z ∈ D.T, ball ((D.mix D c).view (gen c * z)) r =
        ball ((C.mix D c).view (gen c * z)) r) := by
    intro r
    induction r with
    | zero => exact fun _ => ⟨fun _ _ => ball_view_zero _ _ _ _, fun _ _ => ball_view_zero _ _ _ _⟩
    | succ r ih =>
      intro hr
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have key1 : ball ((C.mix C c).view (gen c)) r = ball ((C.mix D c).view (gen c)) r := by
        calc ball ((C.mix C c).view (gen c)) r = ball (C.view 1) r := by
              rw [view_mix_self_gen hCcs h.notC h.loopC]
          _ = ball (D.view 1) r := ball_mono (by omega) h.ball_eq
          _ = ball ((D.mix D c).view (gen c)) r := by
              rw [view_mix_self_gen hDcs h.notD h.loopD]
          _ = ball ((C.mix D c).view (gen c)) r := by simpa using ih2 1 hDcs.one_mem
      have key2 : ball ((D.mix D c).view 1) r = ball ((C.mix D c).view 1) r := by
        calc ball ((D.mix D c).view 1) r = ball (D.view 1) r := by
              rw [view_mix_self_of_mem hDcs h.notD h.loopD hDcs.one_mem]
          _ = ball (C.view 1) r := (ball_mono (by omega) h.ball_eq).symm
          _ = ball ((C.mix C c).view 1) r := by
              rw [view_mix_self_of_mem hCcs h.notC h.loopC hCcs.one_mem]
          _ = ball ((C.mix D c).view 1) r := ih1 1 hCcs.one_mem
      constructor
      · intro x hx
        refine ball_view_succ_of_step_eq _ _ x r
          (fun d => mix_step_left_eq hCcs hCcs hDcs h.notC h.notC h.notD hx d) ?_
        intro d b hb
        by_cases hxd : x = 1 ∧ d = c
        · obtain ⟨rfl, rfl⟩ := hxd
          rw [mix_step_bridge hx hx] at hb
          cases hb
          exact key1
        · rw [mix_step_left hCcs hCcs h.notC h.notC hx hxd] at hb
          exact ih1 b (graph_step_mem hb)
      · intro z hz
        refine ball_view_succ_of_step_eq _ _ _ r
          (fun d => mix_step_right_eq hDcs hCcs hDcs h.notD h.notC h.notD hz d) ?_
        intro d b hb
        by_cases hzd : z = 1 ∧ d = c
        · obtain ⟨rfl, rfl⟩ := hzd
          rw [mul_one, mix_step_bridge_right hz hz] at hb
          cases hb
          exact key2
        · rw [mix_step_right hDcs hDcs h.notD h.notD hz hzd] at hb
          obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
          exact ih2 b' (graph_step_mem hb')
  -- propagation (Fact 3): find a node `g*` of `C` with a disagreeing loop
  obtain ⟨s, hs, d, hlGG, hlGH, hdiff⟩ : ∃ s ∈ C.T, ∃ d, (C.mix C c).graph.step s d = some s ∧
      (C.mix D c).graph.step s d = some s ∧
      A ((C.mix C c).view s) d ≠ A ((C.mix D c).view s) d := by
    set y := fun a => A ((C.mix C c).view a)
    set y' := fun a => A ((C.mix D c).view a)
    have hsteq : ∀ x ∈ C.T, ∀ d, (C.mix C c).graph.step x d = (C.mix D c).graph.step x d :=
      fun x hx d => mix_step_left_eq hCcs hCcs hDcs h.notC h.notC h.notD hx d
    have hsum : ∀ x ∈ C.T,
        ∑ d ∈ Finset.univ.filter (fun d => ((C.mix C c).graph.step x d).isSome), y x d =
        ∑ d ∈ Finset.univ.filter (fun d => ((C.mix C c).graph.step x d).isSome), y' x d := by
      intro x hx
      have h1 := hGG.load_eq_one hA hik' (mem_mix_T.2 (Or.inl hx))
      have h2 := hGH.load_eq_one hA hik' (mem_mix_T.2 (Or.inl hx))
      unfold load at h1 h2
      rw [h1, ← h2]
      simp_rw [hsteq x hx]
      rfl
    let P : FreeCox k → Prop := fun s => ∃ p, ((C.mix C c).graph.step s p).isSome ∧
      y s p ≠ y' s p ∧ ((s = 1 ∧ p = c) ∨ (s ≠ 1 ∧ len (s * gen p) < len s))
    set S := h.goodC.2.1.toFinset.filter P
    have h1S : (1 : FreeCox k) ∈ S := by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨hCcs.one_mem, c, by rw [mix_step_bridge hCcs.one_mem hCcs.one_mem]; rfl, ?_,
        Or.inl ⟨rfl, rfl⟩⟩
      simp only [y, y', view_mix_self_of_mem hCcs h.notC h.loopC hCcs.one_mem]
      exact fun e => hne e.symm
    obtain ⟨s, hsS, hmax⟩ := S.exists_max_image len ⟨1, h1S⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hsS
    obtain ⟨hs, p, hpsome, hpne, hpcase⟩ := hsS
    obtain ⟨d, hdF, hdp, hdne⟩ := propagation (hsum s hs) (p := p)
      (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hpsome⟩) hpne
    rw [Finset.mem_filter] at hdF
    have hnot : ¬ (s = 1 ∧ d = c) := by
      rintro ⟨rfl, rfl⟩
      rcases hpcase with ⟨-, rfl⟩ | ⟨h1, -⟩
      · exact hdp rfl
      · exact h1 rfl
    by_cases hsd : s * gen d ∈ C.T
    · exfalso
      have hCs : C.graph.step s d = some (s * gen d) := tGraph_step_of_mem hs hsd
      have hGGs : (C.mix C c).graph.step s d = some (s * gen d) := by
        rw [mix_step_left hCcs hCcs h.notC h.notC hs hnot, hCs]
      have hGHs : (C.mix D c).graph.step s d = some (s * gen d) := by
        rw [mix_step_left hCcs hDcs h.notC h.notD hs hnot, hCs]
      have e1 := hGG.output_symm hA hik' hGGs
      have e2 := hGH.output_symm hA hik' hGHs
      have hlen : len s < len (s * gen d) := by
        by_contra hl
        have hl' : len (s * gen d) < len s := by have := len_mul_gen_ne s d; omega
        rcases hpcase with ⟨rfl, -⟩ | ⟨-, hp⟩
        · simp at hl'
        · exact hdp (eq_of_len_mul_gen_lt hl' hp)
      have hmem : s * gen d ∈ S := by
        rw [Finset.mem_filter, Set.Finite.mem_toFinset]
        refine ⟨hsd, d, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
        · rw [(C.mix C c).graph.symm _ _ _ hGGs]; rfl
        · simp only [y, y'] at hdne ⊢
          rwa [← e1, ← e2]
        · rintro h1; rw [h1, len_one] at hlen; omega
        · rwa [mul_gen_mul_gen]
      have := hmax _ hmem
      omega
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hdF.2
      rw [mix_step_left hCcs hCcs h.notC h.notC hs hnot] at hb
      have hCs : C.graph.step s d = some s := by
        rcases (graph_step_eq_some hb).2 with ⟨h1, -⟩ | ⟨-, -, rfl⟩
        · exact absurd h1 hsd
        · exact hb
      refine ⟨s, hs, d, ?_, ?_, hdne⟩
      · rw [mix_step_left hCcs hCcs h.notC h.notC hs hnot, hCs]
      · rw [mix_step_left hCcs hDcs h.notC h.notD hs hnot, hCs]
  -- re-root at `g*`
  have hsGG : s ∈ (C.mix C c).T := mem_mix_T.2 (Or.inl hs)
  have hsGH : s ∈ (C.mix D c).T := mem_mix_T.2 (Or.inl hs)
  obtain ⟨n1, l1⟩ := loop_of_step hlGG
  obtain ⟨n2, l2⟩ := loop_of_step hlGH
  refine ⟨(C.mix C c).shift s, (C.mix D c).shift s, d, hGG.shift hsGG, hGH.shift hsGH,
    by simpa using n1, by simpa using n2, by simpa [shift] using l1, by simpa [shift] using l2,
    ?_, ?_⟩
  · rw [view_shift_one, view_shift_one]; exact (hQ (i + 1) le_rfl).1 s hs
  · rw [view_shift_one, view_shift_one]; exact hdiff

/-- Section 4.3 of [GHS14]: the inductive step (both cases of the analysis). -/
theorem Inv.step (hA : A.SolvesLoopy) (h : Inv A i C D c) (hik : i + 2 < k) :
    ∃ C' D' c', Inv A (i + 1) C' D' c' := by
  by_cases hne : A ((C.mix D c).view 1) c = A (C.view 1) c
  · refine h.symm.step_core hA hik ?_
    have hGH : (C.mix D c).Good (i + 1) := h.goodC.mix h.goodD h.notC h.notD
    rw [mix_swap D C c, view_shift_one,
      ← hGH.output_symm hA (by omega) (mix_step_bridge h.goodC.1.one_mem h.goodD.1.one_mem), hne]
    exact h.ne
  · exact h.step_core hA hik hne

theorem exists_inv (hk : 2 ≤ k) (hA : A.SolvesLoopy) :
    ∀ i, i + 2 ≤ k → ∃ C D c, Inv A i C D c := by
  intro i
  induction i with
  | zero => exact fun _ => exists_inv_zero hk hA
  | succ i ih =>
    intro hi
    obtain ⟨C, D, c, h⟩ := ih (by omega)
    exact h.step hA (by omega)

/-! ### Main results -/

/-- Section 4 (Step 1) of [GHS14], property (P1) for `i = k - 2`: for every EC-algorithm `A` that
finds a maximal fractional matching on all finite loopy EC-graphs, there are two finite loopy
EC-graphs with nodes `g`, `h` whose radius-`(k - 2)` views coincide, which carry a loop of a common
colour `c`, and to which `A` assigns different weights on that loop. -/
theorem ECAlg.exists_pair (hk : 2 ≤ k) {A : ECAlg k} (hA : A.SolvesLoopy) :
    ∃ (α β : Type) (_ : Finite α) (_ : Finite β) (G : ColouredGraph k α) (H : ColouredGraph k β)
      (g : α) (h : β), IsLoopy G ∧ IsLoopy H ∧ ball (G.view g) (k - 2) = ball (H.view h) (k - 2) ∧
      ∃ c, G.step g c = some g ∧ H.step h c = some h ∧ A (G.view g) c ≠ A (H.view h) c := by
  obtain ⟨C, D, c, h⟩ := exists_inv hk hA (k - 2) (by omega)
  have h1C := h.goodC.1.one_mem
  have h1D := h.goodD.1.one_mem
  refine ⟨C.T, D.T, h.goodC.finite, h.goodD.finite, C.toGraph, D.toGraph, ⟨1, h1C⟩, ⟨1, h1D⟩,
    h.goodC.isLoopy (by omega), h.goodD.isLoopy (by omega), ?_, c, ?_, ?_, ?_⟩
  · rw [view_toGraph, view_toGraph]; exact h.ball_eq
  · exact toGraph_step (tGraph_step_of_loop h1C (by simpa using h.notC) h.loopC) h1C h1C
  · exact toGraph_step (tGraph_step_of_loop h1D (by simpa using h.notD) h.loopD) h1D h1D
  · rw [view_toGraph, view_toGraph]; exact h.ne

/-- Step 1 of [GHS14] (Section 4): an EC-algorithm that finds a maximal fractional matching on all
finite loopy EC-graphs with `k` colours has run-time at least `k - 1`. -/
theorem ECAlg.le_runTime (hk : 2 ≤ k) {A : ECAlg k} (hA : A.SolvesLoopy) {t : ℕ}
    (ht : A.HasRunTime t) : k - 1 ≤ t := by
  by_contra hlt
  obtain ⟨C, D, c, h⟩ := exists_inv hk hA (k - 2) (by omega)
  exact h.ne (congrFun (ht _ _ (ball_mono (by omega) h.ball_eq)) c)

end Podc.LinearInDeltaLB
