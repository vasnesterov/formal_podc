import Papers.PODC2021.RestorableTiebreaking.Existence
import Podc.Combinatorics.IsolationLemma

/-!
# Corollary 22: tiebreaking weights with `O(f log n)` bits via the isolation lemma

Bodwin–Parter, PODC 2021, Section 3.2. The weights are `r(u, v) = sgn(u, v) · ρ({u,v})` with
`ρ(e) = i(e) / (2 n W)` and `i(e)` uniform in `{-W, …, W}` (so `r(u, v) = (i/W) · 1/(2n)` as in the
paper).

* `corollary22` — counting form: the number of `i ∈ {-W, …, W}^{Sym2 V}` for which `rOf ρ_i` is
  **not** an `f`-ATW function, times `2W + 1`, is at most
  `n² · N_f · |E| · (2W + 1)^{|Sym2 V|}`, where `N_f` is the number of edge sets of size `≤ f`.
  So the failure probability is at most `n² N_f |E| / (2W + 1)`.
* `paper_count_false` — the paper's union bound counts "`≤ n^{f+2}` possible choices of
  `s, t, F`"; already for `K₄` and `f = 1` there are `16 · 7 = 112 > 4³` choices with ordered pairs
  `(s, t)` (`84 > 64` excluding `s = t`). In general `N_f ≈ |E|^f` is up to `≈ n^{2f}`, so with the
  paper's choice `W = n^{f+4+c}` the union bound only gives `≈ n^{f-c}`; `W = n^{2f+4+c}` gives the
  claimed `n^{-c}` (still `O(f log n)` bits). This final arithmetic is not stated in Lean.
-/

open Finset SimpleGraph SimpleGraph.Walk Podc.Isolation

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- Two shortest walks of `G \ A` from the same vertex traverse a common edge the same way. -/
lemma cnt_eq_of_mem_edges {A : Set (Sym2 V)} {s t t' : V} {p : G.Walk s t} {q : G.Walk s t'}
    (hp : p.IsShortestIn A) (hq : q.IsShortestIn A) {e : Sym2 V} (hep : e ∈ p.edges)
    (heq : e ∈ q.edges) : cnt p e = cnt q e := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hep
  obtain ⟨d', hd', hdd'⟩ := List.mem_map.mp heq
  have := hp.dart_eq_of_edge_eq hq hd hd' hdd'.symm
  subst this
  rw [cnt_of_mem hp.isPath hd, cnt_of_mem hq.isPath hd']

lemma abs_cnt_of_mem {s t : V} {p : G.Walk s t} (hp : p.IsPath) {e : Sym2 V}
    (he : e ∈ p.edges) : |cnt p e| = 1 := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  rw [cnt_of_mem hp hd]; unfold sgn; split_ifs <;> simp

/-- Only faults that are edges of `G` matter. -/
lemma hasMinWalks_congr {r : V → V → ℝ} {A B : Set (Sym2 V)}
    (h : ∀ e ∈ G.edgeSet, e ∈ A ↔ e ∈ B) (hA : HasMinWalks G r A) : HasMinWalks G r B := by
  have hav : ∀ {s t : V} (p : G.Walk s t), p.Avoids A ↔ p.Avoids B := fun p =>
    ⟨fun hp e he hB => hp e he ((h e (p.edges_subset_edgeSet he)).mpr hB),
      fun hp e he hA => hp e he ((h e (p.edges_subset_edgeSet he)).mp hA)⟩
  have hdel : G.deleteEdges A = G.deleteEdges B := by
    ext u v
    simp only [deleteEdges_adj]
    exact ⟨fun ⟨huv, hn⟩ => ⟨huv, fun hb => hn ((h _ huv).mpr hb)⟩,
      fun ⟨huv, hn⟩ => ⟨huv, fun ha => hn ((h _ huv).mp ha)⟩⟩
  intro s t hst
  rw [← hdel] at hst
  obtain ⟨p, ⟨hpA, hpmin⟩, hpS⟩ := hA s t hst
  exact ⟨p, ⟨(hav p).mp hpA, fun q hq hne => hpmin q ((hav q).mpr hq) hne⟩,
    ⟨(hav p).mp hpS.1, by rw [← hdel]; exact hpS.2⟩⟩

/-- The common orientation sign of the edge `e` on shortest `s ⇝ t` walks of `G \ A`. -/
noncomputable def tau (G : SimpleGraph V) (A : Set (Sym2 V)) (s t : V) (e : Sym2 V) : ℤ :=
  open Classical in
  if h : ∃ q : G.Walk s t, q.IsShortestIn A ∧ e ∈ q.edges then cnt h.choose e else 1

lemma cnt_eq_tau {A : Set (Sym2 V)} {s t : V} {p : G.Walk s t} (hp : p.IsShortestIn A)
    {e : Sym2 V} (he : e ∈ p.edges) : cnt p e = tau G A s t e := by
  have h : ∃ q : G.Walk s t, q.IsShortestIn A ∧ e ∈ q.edges := ⟨p, hp, he⟩
  simp only [tau, h, ↓reduceDIte]
  exact cnt_eq_of_mem_edges hp h.choose_spec.1 he h.choose_spec.2

lemma tau_mul_self (A : Set (Sym2 V)) (s t : V) (e : Sym2 V) :
    tau G A s t e * tau G A s t e = 1 := by
  unfold tau
  split_ifs with h
  · have := abs_cnt_of_mem h.choose_spec.1.isPath h.choose_spec.2
    rcases abs_eq (zero_le_one) |>.mp this with h' | h' <;> rw [h'] <;> norm_num
  · simp

/-- The integer-valued weights: `ρ_i(e) = i(e) / (2 n W)`. -/
noncomputable def rhoInt (W : ℕ) (i : Sym2 V → ℤ) (e : Sym2 V) : ℝ :=
  (i e : ℝ) / (2 * Fintype.card V * W)

/-- The shortest `s ⇝ t` walks of `G \ A` (a finite set: they are paths). -/
noncomputable def shortestSet (G : SimpleGraph V) (A : Set (Sym2 V)) (s t : V) :
    Finset (G.Walk s t) :=
  open Classical in
  ((Set.toFinite {p : G.Walk s t | p.length < Fintype.card V}).subset
    (show {p : G.Walk s t | p.IsShortestIn A} ⊆ _ from
      fun p (hp : p.IsShortestIn A) => hp.isPath.length_lt)).toFinset

lemma mem_shortestSet {A : Set (Sym2 V)} {s t : V} {p : G.Walk s t} :
    p ∈ shortestSet G A s t ↔ p.IsShortestIn A := by
  rw [shortestSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The family of edge sets of shortest `s ⇝ t` walks of `G \ A`. -/
noncomputable def fam (G : SimpleGraph V) (A : Set (Sym2 V)) (s t : V) : Finset (Finset (Sym2 V)) :=
  (shortestSet G A s t).image fun p => p.edges.toFinset

lemma dwt_eq_wt {W : ℕ} {i : Sym2 V → ℤ} {A : Set (Sym2 V)} {s t : V} {p : G.Walk s t}
    (hp : p.IsShortestIn A) :
    p.dwt (wstar (rOf (rhoInt W i))) = p.length +
      (wt (fun e => tau G A s t e * i e) p.edges.toFinset : ℝ) / (2 * Fintype.card V * W) := by
  rw [dwt_rOf_eq]
  congr 1
  rw [wt, ← sum_subset (subset_univ p.edges.toFinset)]
  · push_cast
    rw [sum_div]
    refine sum_congr rfl fun e he => ?_
    rw [List.mem_toFinset] at he
    rw [cnt_eq_tau hp he, rhoInt, mul_div_assoc]
  · intro e _ he
    rw [List.mem_toFinset] at he
    simp [cnt_of_not_mem he]

/-- One pair: a unique minimum of the isolation family yields the unique lightest walk. -/
lemma isMinWalk_of_uniqueMin {W : ℕ} (hW : 0 < W) {i : Sym2 V → ℤ}
    (hi : ∀ e, i e ∈ Icc (-(W : ℤ)) W) {A : Set (Sym2 V)} {s t : V}
    (hu : UniqueMin (fam G A s t) fun e => tau G A s t e * i e) :
    ∃ p : G.Walk s t, IsMinWalk G (rOf (rhoInt W i)) A p ∧ p.IsShortestIn A := by
  obtain ⟨S0, hS0, hmin⟩ := hu
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hS0
  rw [mem_shortestSet] at hp
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hc : (0 : ℝ) < 2 * Fintype.card V * W := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  refine ⟨p, isMinWalk_of_unique (ε := 1 / (2 * Fintype.card V)) (by positivity) ?_ ?_ hp
    fun q hq hne => ?_, hp⟩
  · rw [mul_one_div, div_lt_one (by positivity)]; linarith
  · intro u v _
    refine abs_rOf_le _ (fun e => ?_) u v
    rw [rhoInt, abs_div, abs_of_pos hc, div_le_div_iff₀ hc (by positivity)]
    have h1 : |(i e : ℝ)| ≤ W := by
      have := hi e; rw [mem_Icc] at this
      rw [abs_le]; exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    nlinarith
  · have hqS : q.edges.toFinset ∈ fam G A s t := mem_image.mpr ⟨q, mem_shortestSet.mpr hq, rfl⟩
    have hneS : q.edges.toFinset ≠ p.edges.toFinset := by
      intro heq
      apply hne
      refine (hq.eq_of_edges_subset hp fun e he => ?_)
      rw [← List.mem_toFinset, ← heq, List.mem_toFinset]; exact he
    have hlt := hmin _ hqS hneS
    rw [dwt_eq_wt hp, dwt_eq_wt hq]
    have hlen : (p.length : ℝ) = q.length := by
      have := hp.2.trans hq.2.symm; exact_mod_cast this
    rw [hlen, add_lt_add_iff_left, div_lt_div_iff_of_pos_right hc]
    exact_mod_cast hlt

/-- The fault sets of size `≤ f` consisting of edges of `G`. -/
def faultSets (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter fun F => #F ≤ f

open Classical in
/-- **Corollary 22 of [Bodwin–Parter]** (counting form of the isolation-lemma construction). Draw
`i(e)` uniformly from `{-W, …, W}` for every `e` and set `r(u,v) = sgn(u,v) · i({u,v}) / (2nW)`.
The number of bad draws (for which `r` is not an `f`-ATW function), times `2W + 1`, is at most
`n² · N_f · |E| · (2W+1)^{|Sym2 V|}`; i.e. the failure probability is at most
`n² N_f |E| / (2W + 1)` with `N_f = #faultSets G f`. -/
theorem corollary22 [DecidableRel G.Adj] (W : ℕ) (hW : 0 < W) (f : ℕ) :
    #((Fintype.piFinset fun _ : Sym2 V => Icc (-(W : ℤ)) W).filter
        fun i => ¬ IsATW G f (rOf (rhoInt W i))) * (2 * W + 1) ≤
      Fintype.card V ^ 2 * #(faultSets G f) * #G.edgeFinset *
        (2 * W + 1) ^ Fintype.card (Sym2 V) := by
  set P := Fintype.piFinset fun _ : Sym2 V => Icc (-(W : ℤ)) W
  set T : Finset (V × V × Finset (Sym2 V)) :=
    (univ ×ˢ univ ×ˢ faultSets G f).filter fun x => (fam G x.2.2 x.1 x.2.1).Nonempty
  let Bad : V × V × Finset (Sym2 V) → Finset (Sym2 V → ℤ) := fun x =>
    P.filter fun i => ¬ UniqueMin (fam G x.2.2 x.1 x.2.1) fun e => tau G x.2.2 x.1 x.2.1 e * i e
  -- every bad draw is bad for some triple
  have hsub : P.filter (fun i => ¬ IsATW G f (rOf (rhoInt W i))) ⊆ T.biUnion Bad := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨hiP, hbad⟩ := hi
    have hiI : ∀ e, i e ∈ Icc (-(W : ℤ)) W := fun e => Fintype.mem_piFinset.mp hiP e
    by_contra hnot
    apply hbad
    refine ⟨fun u v h => rOf_antisymm _ h, fun F hF => ?_⟩
    set F' := F.filter fun e => e ∈ G.edgeFinset
    refine hasMinWalks_congr (A := (F' : Set (Sym2 V))) (fun e he => ?_) ?_
    · simp only [F', coe_filter, Set.mem_ofPred_eq, mem_edgeFinset]
      exact ⟨fun h => h.1, fun h => ⟨h, he⟩⟩
    intro s t hst
    obtain ⟨p₀, hp₀⟩ := exists_isShortestIn hst
    have hxT : (s, t, F') ∈ T := by
      refine mem_filter.mpr ⟨?_, ?_⟩
      · simp only [mem_product, mem_univ, true_and, faultSets, mem_filter, mem_powerset]
        exact ⟨fun e he => (mem_filter.mp he).2, (card_filter_le _ _).trans hF⟩
      · exact ⟨_, mem_image.mpr ⟨p₀, mem_shortestSet.mpr hp₀, rfl⟩⟩
    have : i ∉ Bad (s, t, F') := fun h => hnot (mem_biUnion.mpr ⟨_, hxT, h⟩)
    simp only [Bad, mem_filter, not_and, not_not] at this
    exact isMinWalk_of_uniqueMin hW hiI (this hiP)
  -- each triple: flip signs and apply the isolation lemma
  have hBad : ∀ x ∈ T, #(Bad x) * (2 * W + 1) ≤ #G.edgeFinset * (2 * W + 1) ^
      Fintype.card (Sym2 V) := by
    intro x hx
    have hne := (mem_filter.mp hx).2
    set τ := tau G x.2.2 x.1 x.2.1
    have hcard : #(Bad x) =
        #(P.filter fun w => ¬ UniqueMin (fam G x.2.2 x.1 x.2.1) w) := by
      have hflip : ∀ i ∈ P, (fun e => τ e * i e) ∈ P := by
        intro i hi
        rw [Fintype.mem_piFinset] at hi ⊢
        intro e
        have h1 := tau_mul_self (G := G) x.2.2 x.1 x.2.1 e
        have h2 := hi e
        rw [mem_Icc] at h2 ⊢
        rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> simp only [τ, h] <;> omega
      refine card_nbij' (fun i e => τ e * i e) (fun i e => τ e * i e) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Bad, coe_filter, Set.mem_ofPred_eq] at hi ⊢
        exact ⟨hflip i hi.1, hi.2⟩
      · intro i hi
        simp only [Bad, coe_filter, Set.mem_ofPred_eq] at hi ⊢
        refine ⟨hflip i hi.1, ?_⟩
        convert hi.2 using 2
        funext e; rw [← mul_assoc, tau_mul_self, one_mul]
      · intro i _; funext e; simp only; rw [← mul_assoc, tau_mul_self, one_mul]
      · intro i _; funext e; simp only; rw [← mul_assoc, tau_mul_self, one_mul]
    rw [hcard]
    refine (card_not_uniqueMin_le_Icc _ hne W).trans ?_
    gcongr
    intro e he
    obtain ⟨S, hS, heS⟩ := mem_biUnion.mp he
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hS
    rw [id, List.mem_toFinset] at heS
    exact mem_edgeFinset.mpr (p.edges_subset_edgeSet heS)
  calc #(P.filter fun i => ¬ IsATW G f (rOf (rhoInt W i))) * (2 * W + 1)
      ≤ #(T.biUnion Bad) * (2 * W + 1) := by gcongr
    _ ≤ (∑ x ∈ T, #(Bad x)) * (2 * W + 1) := by gcongr; exact card_biUnion_le
    _ = ∑ x ∈ T, #(Bad x) * (2 * W + 1) := sum_mul _ _ _
    _ ≤ ∑ _x ∈ T, #G.edgeFinset * (2 * W + 1) ^ Fintype.card (Sym2 V) := sum_le_sum hBad
    _ = #T * (#G.edgeFinset * (2 * W + 1) ^ Fintype.card (Sym2 V)) := by rw [sum_const, smul_eq_mul]
    _ ≤ #(univ ×ˢ univ ×ˢ faultSets G f) *
          (#G.edgeFinset * (2 * W + 1) ^ Fintype.card (Sym2 V)) := by
        gcongr; exact filter_subset _ _
    _ = Fintype.card V ^ 2 * #(faultSets G f) * #G.edgeFinset *
          (2 * W + 1) ^ Fintype.card (Sym2 V) := by
        rw [card_product, card_product, card_univ]; ring

/-- The paper's union bound "over the `≤ n^{f+2}` possible choices of `s, t, F`" is wrong: for
`K₄` and `f = 1` there are `4 · 4 · 7 = 112 > 4³` such choices with ordered pairs `(s, t)`. -/
theorem paper_count_false :
    #((univ : Finset (Fin 4)) ×ˢ (univ : Finset (Fin 4)) ×ˢ
      faultSets (⊤ : SimpleGraph (Fin 4)) 1) = 112 ∧ 4 ^ (1 + 2) < 112 := by
  constructor
  · rw [card_product, card_product]
    simp only [card_univ, Fintype.card_fin]
    rfl
  · norm_num

end RestorableTiebreaking
