import Podc.Probability.Finite.LocalLemma
import Mathlib

/-!
# One trial of the first step of `Cluster_j` (proof of Lemma 4.3)

We fix a node `v ∈ V_j` and describe its neighbourhood in the multigraph `G_j` by a finite type `ι`
of neighbours with *volumes* `vol u = |E_j(v, u)| ≥ 1` (the number of parallel edges). A set `R` of
not-yet-queried neighbours determines `X_v = Edges vol R`, the edges from `v` to `R`. A trial draws
`s` edges of `X_v` uniformly and independently with replacement; `queried f` is the set of
neighbours hit.

The proof of Lemma 4.3 partitions the neighbours into `L = 2h` volume classes with ratio `b = n^ε`,
takes the class `K` of maximum volume, cuts it into `q = ⌊|K|/β⌋` groups of `β = ⌈|K|/α⌉` nodes, and
shows that each group is hit with probability `≥ 1 − (1 − θ)^s`, `θ = 1/(L α b)`. Here:

* `uprob_miss`, `uprob_miss_le`: a set `W ⊆ R` of volume `≥ θ · vol R` is missed by all `s` samples
  with probability `(1 − vol W / vol R)^s ≤ (1 − θ)^s`.
* `cls`: the volume class `⌊log_b vol u⌋`, so that `b^x ≤ vol u < b^{x+1}` on class `x`. **The paper
  writes the class as `vol u ∈ (b^x, b^{x+1}]`, which excludes volume `1` (all neighbours in the simple
  graph `G_0`!); we use `[b^x, b^{x+1})`.**
* `exists_heavy_class`: some class `x < L` carries `≥ vol R / L` of the volume.
* `group`: the groups; `volOf_group_ge`: each has volume `≥ vol R/(L α b)`;
  `card_inter_ge_of_hit`: if all groups are hit then `|Q ∩ K| ≥ q`; `subset_or_le_card_of_hit`: then
  `K ⊆ Q` (when `|K| ≤ α`) or `|Q ∩ K| ≥ α/3` (when `α ≥ 6`).
-/

namespace Podc.LocalMessageReduction

open Finset Cslib.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (vol : ι → ℕ)

/-- The volume `|E_j(v, W)| = ∑_{u ∈ W} vol u` of a set of neighbours. -/
def volOf (W : Finset ι) : ℕ := ∑ u ∈ W, vol u

/-- `X_v`: the (parallel) edges from `v` to the neighbours in `R`; the edge `⟨u, i⟩` is the `i`-th
edge of `E_j(v, u)`. -/
abbrev Edges (R : Finset ι) := {e : Σ u : ι, Fin (vol u) // e.1 ∈ R}

/-- The neighbours queried by a sequence of sampled edges. -/
def queried {R : Finset ι} {s : ℕ} (f : Fin s → Edges vol R) : Finset ι :=
  univ.image fun i => (f i).1.1

variable {vol}

omit [Fintype ι] in
lemma queried_subset {R : Finset ι} {s : ℕ} (f : Fin s → Edges vol R) : queried vol f ⊆ R := by
  intro u hu
  simp only [queried, mem_image, mem_univ, true_and] at hu
  obtain ⟨i, rfl⟩ := hu
  exact (f i).2

omit [Fintype ι] in
lemma card_queried_le {R : Finset ι} {s : ℕ} (f : Fin s → Edges vol R) :
    #(queried vol f) ≤ s :=
  card_image_le.trans (by simp)

omit [Fintype ι] in
lemma volOf_sdiff {R W : Finset ι} (h : W ⊆ R) : volOf vol (R \ W) = volOf vol R - volOf vol W := by
  unfold volOf
  rw [← sum_sdiff h]
  omega

/-- The number of edges of `X_v` leading to a subset `A ⊆ R` is `vol A`. -/
lemma card_filter_mem_edges (R A : Finset ι) (hA : A ⊆ R) :
    #(univ.filter fun e : Edges vol R => e.1.1 ∈ A) = volOf vol A := by
  rw [volOf, ← card_map (Function.Embedding.subtype _)]
  have : (univ.filter fun e : Edges vol R => e.1.1 ∈ A).map (Function.Embedding.subtype _) =
      A.sigma fun u => (univ : Finset (Fin (vol u))) := by
    ext ⟨u, i⟩
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, mem_sigma,
      and_true]
    constructor
    · rintro ⟨⟨e, he⟩, h, rfl⟩; exact h
    · intro h; exact ⟨⟨⟨u, i⟩, hA h⟩, h, rfl⟩
  rw [this, card_sigma]
  simp

lemma card_edges (R : Finset ι) : Fintype.card (Edges vol R) = volOf vol R := by
  rw [← card_univ, ← card_filter_mem_edges R R subset_rfl]
  congr 1
  exact (filter_true_of_mem fun e _ => e.2).symm

/-- **One group is missed** by all `s` samples with probability `(vol (R \ W) / vol R)^s`. -/
lemma uprob_miss (R W : Finset ι) (s : ℕ) :
    uprob (fun f : Fin s → Edges vol R => ∀ i, (f i).1.1 ∉ W) =
      ((volOf vol (R \ W) : ℝ) / volOf vol R) ^ s := by
  have h := uprob_pi (α := fun _ : Fin s => Edges vol R) (fun _ e => e.1.1 ∉ W)
  rw [h, prod_const, card_univ, Fintype.card_fin]
  congr 1
  rw [uprob_eq_card_filter, ← card_edges R]
  congr 2
  rw [← card_filter_mem_edges R (R \ W) sdiff_subset]
  congr 1
  ext e; simp [e.2]

/-- A set `W ⊆ R` with `vol W ≥ θ · vol R` is missed by all `s` samples with probability at most
`(1 − θ)^s`. -/
lemma uprob_miss_le {R W : Finset ι} (hWR : W ⊆ R) {θ : ℝ} (hθ1 : θ ≤ 1)
    (hW : θ * volOf vol R ≤ volOf vol W) (s : ℕ) :
    uprob (fun f : Fin s → Edges vol R => ∀ i, (f i).1.1 ∉ W) ≤ (1 - θ) ^ s := by
  rw [uprob_miss]
  rcases (volOf vol R).eq_zero_or_pos with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    rcases s.eq_zero_or_pos with rfl | hs
    · simp
    · rw [zero_pow hs.ne']; exact pow_nonneg (by linarith) _
  · apply pow_le_pow_left₀ (by positivity)
    have hle : volOf vol W ≤ volOf vol R := sum_le_sum_of_subset hWR
    rw [div_le_iff₀ (by exact_mod_cast hpos), volOf_sdiff hWR, Nat.cast_sub hle]
    linarith

/-- **Union bound over groups.** -/
lemma uprob_exists_miss_le {R : Finset ι} {q : ℕ} (W : ℕ → Finset ι) (hWR : ∀ l < q, W l ⊆ R)
    {θ : ℝ} (hθ1 : θ ≤ 1) (hW : ∀ l < q, θ * volOf vol R ≤ volOf vol (W l)) (s : ℕ) :
    uprob (fun f : Fin s → Edges vol R => ∃ l < q, ∀ i, (f i).1.1 ∉ W l) ≤ q * (1 - θ) ^ s := by
  have h := uprob_exists_le (Ω := Fin s → Edges vol R) (range q)
    (fun l f => ∀ i, (f i).1.1 ∉ W l)
  simp only [mem_range] at h
  refine h.trans ?_
  calc ∑ l ∈ range q, uprob (fun f : Fin s → Edges vol R => ∀ i, (f i).1.1 ∉ W l)
      ≤ ∑ _l ∈ range q, (1 - θ) ^ s :=
        sum_le_sum fun l hl => uprob_miss_le (hWR l (mem_range.mp hl)) hθ1
          (hW l (mem_range.mp hl)) s
    _ = q * (1 - θ) ^ s := by simp

/-! ### Volume classes -/

variable (vol) in
/-- The volume class of a neighbour: `⌊log_b vol u⌋`, so that `b^x ≤ vol u < b^{x+1}`. -/
noncomputable def cls (b : ℝ) (u : ι) : ℕ := ⌊Real.logb b (vol u)⌋₊

omit [Fintype ι] [DecidableEq ι] in
lemma cls_spec {b : ℝ} (hb : 1 < b) {u : ι} (hu : 1 ≤ vol u) :
    b ^ cls vol b u ≤ (vol u : ℝ) ∧ (vol u : ℝ) < b ^ (cls vol b u + 1) := by
  have hy : (1 : ℝ) ≤ vol u := by exact_mod_cast hu
  have hl : 0 ≤ Real.logb b (vol u) := Real.logb_nonneg hb hy
  have hrw : (b : ℝ) ^ Real.logb b (vol u) = vol u :=
    Real.rpow_logb (by linarith) hb.ne' (by linarith)
  constructor
  · calc b ^ cls vol b u = b ^ (cls vol b u : ℝ) := (Real.rpow_natCast b _).symm
      _ ≤ b ^ Real.logb b (vol u) := Real.rpow_le_rpow_of_exponent_le hb.le (Nat.floor_le hl)
      _ = vol u := hrw
  · calc (vol u : ℝ) = b ^ Real.logb b (vol u) := hrw.symm
      _ < b ^ ((cls vol b u + 1 : ℕ) : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt hb
          push_cast
          exact Nat.lt_floor_add_one _
      _ = b ^ (cls vol b u + 1) := Real.rpow_natCast b _

omit [Fintype ι] [DecidableEq ι] in
/-- Two neighbours of the same class have volumes within a factor `b`. -/
lemma vol_lt_of_cls_eq {b : ℝ} (hb : 1 < b) {u w : ι} (hu : 1 ≤ vol u) (hw : 1 ≤ vol w)
    (h : cls vol b u = cls vol b w) : (vol u : ℝ) < b * vol w := by
  have h1 := (cls_spec hb hu).2
  have h2 := (cls_spec hb hw).1
  rw [h, pow_succ] at h1
  nlinarith

omit [Fintype ι] [DecidableEq ι] in
lemma cls_lt {b : ℝ} (hb : 1 < b) {u : ι} (hu : 1 ≤ vol u) {L : ℕ} (hL : (vol u : ℝ) < b ^ L) :
    cls vol b u < L := by
  by_contra h
  push Not at h
  have := (cls_spec hb hu).1
  have : b ^ L ≤ b ^ cls vol b u := pow_le_pow_right₀ hb.le h
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- **The maximum-volume class.** If all volumes lie in `[1, b^L)`, some class `x < L` carries at
least a `1/L` fraction of the volume of `R`. -/
lemma exists_heavy_class {b : ℝ} (hb : 1 < b) {L : ℕ} (hL : 0 < L) (R : Finset ι)
    (hvol : ∀ u ∈ R, 1 ≤ vol u ∧ (vol u : ℝ) < b ^ L) :
    ∃ x < L, volOf vol R ≤ L * volOf vol (R.filter fun u => cls vol b u = x) := by
  have hmaps : ∀ u ∈ R, cls vol b u ∈ range L := fun u hu =>
    mem_range.mpr (cls_lt hb (hvol u hu).1 (hvol u hu).2)
  have hsum := sum_fiberwise_of_maps_to hmaps vol
  have : ∑ _x ∈ range L, volOf vol R ≤
      ∑ x ∈ range L, L * volOf vol (R.filter fun u => cls vol b u = x) := by
    rw [← mul_sum, sum_const, card_range, smul_eq_mul]
    unfold volOf
    rw [hsum]
  obtain ⟨x, hx, h⟩ := exists_le_of_sum_le ⟨0, mem_range.mpr hL⟩ this
  exact ⟨x, mem_range.mp hx, h⟩

/-! ### Groups inside a class -/

/-- The `l`-th group of `β` consecutive elements of `K` (in the order of `K.equivFin`). -/
noncomputable def group (K : Finset ι) (β l : ℕ) : Finset ι :=
  (univ.filter fun i : Fin #K => i.1 / β = l).image fun i => (K.equivFin.symm i).1

omit [Fintype ι] in
lemma group_subset (K : Finset ι) (β l : ℕ) : group K β l ⊆ K := by
  intro u hu
  simp only [group, mem_image, mem_filter, mem_univ, true_and] at hu
  obtain ⟨i, -, rfl⟩ := hu
  exact (K.equivFin.symm i).2

omit [Fintype ι] in
lemma card_group {K : Finset ι} {β l : ℕ} (hβ : 0 < β) (hl : (l + 1) * β ≤ #K) :
    #(group K β l) = β := by
  rw [group, card_image_of_injective _ (fun i j h => K.equivFin.symm.injective
    (Subtype.ext h))]
  rw [← card_map Fin.valEmbedding]
  have : (univ.filter fun i : Fin #K => i.1 / β = l).map Fin.valEmbedding = Ico (l * β) (l * β + β) := by
    ext i
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [Nat.div_eq_iff hβ] at hj
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨i, by nlinarith⟩, ?_, rfl⟩
      show i / β = l
      rw [Nat.div_eq_iff hβ]
      omega
  rw [this, Nat.card_Ico]
  omega

omit [Fintype ι] in
lemma group_disjoint (K : Finset ι) (β : ℕ) {l l' : ℕ} (h : l ≠ l') :
    Disjoint (group K β l) (group K β l') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  simp only [group, mem_image, mem_filter, mem_univ, true_and] at hu hu'
  obtain ⟨i, hi, rfl⟩ := hu
  obtain ⟨j, hj, hij⟩ := hu'
  have : j = i := K.equivFin.symm.injective (Subtype.ext hij)
  subst this
  exact h (hi.symm.trans hj)

omit [Fintype ι] in
/-- If every group `l < q` meets `Q`, then `|Q ∩ K| ≥ q`. -/
lemma card_inter_ge_of_hit {K Q : Finset ι} {β q : ℕ} (hit : ∀ l < q, (Q ∩ group K β l).Nonempty) :
    q ≤ #(Q ∩ K) := by
  have hdisj : (↑(range q) : Set ℕ).PairwiseDisjoint fun l => Q ∩ group K β l := by
    intro l _ l' _ hll'
    exact Disjoint.mono inter_subset_right inter_subset_right (group_disjoint K β hll')
  calc q = ∑ _l ∈ range q, 1 := by simp
    _ ≤ ∑ l ∈ range q, #(Q ∩ group K β l) :=
        sum_le_sum fun l hl => (hit l (mem_range.mp hl)).card_pos
    _ = #((range q).biUnion fun l => Q ∩ group K β l) := (card_biUnion hdisj).symm
    _ ≤ #(Q ∩ K) := by
        apply card_le_card
        intro u hu
        simp only [mem_biUnion, mem_inter] at hu
        obtain ⟨l, -, huQ, huG⟩ := hu
        exact mem_inter.mpr ⟨huQ, group_subset K β l huG⟩

/-- The group size `β = ⌈|K|/α⌉`. -/
noncomputable def beta (K : Finset ι) (α : ℝ) : ℕ := ⌈(#K : ℝ) / α⌉₊

/-- The number of groups `q = ⌊|K|/β⌋`. -/
noncomputable def numGroups (K : Finset ι) (α : ℝ) : ℕ := #K / beta K α

omit [Fintype ι] [DecidableEq ι] in
lemma beta_pos {K : Finset ι} (hK : K.Nonempty) {α : ℝ} (hα : 0 < α) : 0 < beta K α := by
  unfold beta
  apply Nat.ceil_pos.mpr
  have : (0 : ℝ) < #K := by exact_mod_cast hK.card_pos
  positivity

omit [Fintype ι] [DecidableEq ι] in
lemma card_le_beta_mul {K : Finset ι} {α : ℝ} (hα : 0 < α) : (#K : ℝ) ≤ beta K α * α := by
  have := Nat.le_ceil ((#K : ℝ) / α)
  rw [div_le_iff₀ hα] at this
  exact this

omit [Fintype ι] in
/-- Outcome of a good trial, deterministic part of Lemma 4.3: if every group of `K` is hit, then
either all of `K` is queried (when `|K| ≤ α`, the groups are singletons) or at least `α/3` nodes of
`K` are queried (when `|K| > α`; needs `α ≥ 6`). -/
lemma subset_or_le_card_of_hit {K Q : Finset ι} (hK : K.Nonempty) {α : ℝ} (hα : 6 ≤ α)
    (hit : ∀ l < numGroups K α, (Q ∩ group K (beta K α) l).Nonempty) :
    K ⊆ Q ∨ α / 3 ≤ #(Q ∩ K) := by
  have hα0 : 0 < α := by linarith
  have hq := card_inter_ge_of_hit hit
  have hβ := beta_pos hK hα0
  by_cases hsmall : (#K : ℝ) ≤ α
  · left
    have hβ1 : beta K α = 1 := by
      have : beta K α ≤ 1 := by
        unfold beta
        rw [Nat.ceil_le, div_le_iff₀ hα0]
        push_cast
        linarith
      omega
    have hqK : numGroups K α = #K := by simp [numGroups, hβ1]
    rw [hqK] at hq
    have heq : Q ∩ K = K := eq_of_subset_of_card_le inter_subset_right hq
    intro u hu
    have : u ∈ Q ∩ K := by rw [heq]; exact hu
    exact (mem_inter.mp this).1
  · right
    push Not at hsmall
    refine le_trans ?_ (by exact_mod_cast hq : (numGroups K α : ℝ) ≤ #(Q ∩ K))
    -- `|K| < (q + 1) β` and `β < |K|/α + 1`
    have h1 : #K < (numGroups K α + 1) * beta K α := by
      have := Nat.lt_div_mul_add (a := #K) hβ
      unfold numGroups
      nlinarith
    have h1' : (#K : ℝ) < (numGroups K α + 1) * beta K α := by exact_mod_cast h1
    have h2 : (beta K α : ℝ) < #K / α + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2' : (beta K α : ℝ) * α < #K + α := by
      have := mul_lt_mul_of_pos_right h2 hα0
      rwa [add_mul, div_mul_cancel₀ _ hα0.ne', one_mul] at this
    have hβ0 : (0 : ℝ) < beta K α := by exact_mod_cast hβ
    -- `α β / 2 < |K| < (q + 1) β`
    have h3 : α * beta K α < 2 * ((numGroups K α + 1) * beta K α) := by nlinarith
    have h4 : α < 2 * (numGroups K α + 1) := by
      have := lt_of_mul_lt_mul_right (by nlinarith : α * beta K α < 2 * (numGroups K α + 1) * beta K α)
        hβ0.le
      linarith
    linarith

omit [Fintype ι] [DecidableEq ι] in
/-- **Group volume.** Inside a class `K` (volumes within a factor `b`) carrying `≥ vol R / L`, every
set `W ⊆ K` of `β = ⌈|K|/α⌉` nodes has volume `≥ vol R / (L α b)`. -/
lemma volOf_group_ge {b : ℝ} (hb : 1 < b) {L : ℕ} (hL : 0 < L) {R K W : Finset ι} (hKR : K ⊆ R)
    (hcls : ∀ u ∈ K, ∀ w ∈ K, (vol u : ℝ) < b * vol w)
    (hheavy : volOf vol R ≤ L * volOf vol K) (hWK : W ⊆ K) {α : ℝ} (hα : 0 < α)
    (hW : #W = beta K α) :
    (volOf vol R : ℝ) / (L * α * b) ≤ volOf vol W := by
  rcases K.eq_empty_or_nonempty with hK | hK
  · subst hK
    have hR : volOf vol R = 0 := by simpa [volOf] using hheavy
    rw [hR]; simp
  have hKpos : (0 : ℝ) < #K := by exact_mod_cast hK.card_pos
  have hb0 : (0 : ℝ) < b := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  -- every `w ∈ K` has `vol K < |K| b vol w`
  have hmin : ∀ w ∈ K, (volOf vol K : ℝ) ≤ #K * b * vol w := by
    intro w hw
    unfold volOf
    push_cast
    calc ∑ u ∈ K, (vol u : ℝ) ≤ ∑ _u ∈ K, b * vol w := sum_le_sum fun u hu => (hcls u hu w hw).le
      _ = #K * b * vol w := by simp; ring
  -- `β vol K ≤ |K| b vol W`
  have hWv : (beta K α : ℝ) * volOf vol K ≤ #K * b * volOf vol W := by
    rw [← hW]
    calc (#W : ℝ) * volOf vol K = ∑ _w ∈ W, (volOf vol K : ℝ) := by simp
      _ ≤ ∑ w ∈ W, (#K : ℝ) * b * vol w := sum_le_sum fun w hw => hmin w (hWK hw)
      _ = #K * b * volOf vol W := by rw [← mul_sum]; simp [volOf]
  have hβ0 : (0 : ℝ) < beta K α := by exact_mod_cast beta_pos hK hα
  have hKβ := card_le_beta_mul (K := K) hα
  have hWnn : (0 : ℝ) ≤ volOf vol W := by positivity
  -- `vol K ≤ α b vol W`
  have hK' : (volOf vol K : ℝ) ≤ α * b * volOf vol W := by
    have : (beta K α : ℝ) * volOf vol K ≤ beta K α * (α * b * volOf vol W) := by
      calc (beta K α : ℝ) * volOf vol K ≤ #K * b * volOf vol W := hWv
        _ ≤ (beta K α * α) * b * volOf vol W := by gcongr
        _ = beta K α * (α * b * volOf vol W) := by ring
    exact le_of_mul_le_mul_left this hβ0
  have hR' : (volOf vol R : ℝ) ≤ L * volOf vol K := by exact_mod_cast hheavy
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end Podc.LocalMessageReduction
