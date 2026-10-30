import Papers.PODC2023.BilateralNetworkCreation.Trees
import Papers.PODC2023.BilateralNetworkCreation.Cut

/-!
# Trees whose subtree sizes depend only on the layer

For the lower-bound construction (Proposition 3.8) we use the following abstract setting: a tree
rooted at `r` such that `|T_x| = f(ℓ(x))` for a function `f` with

* `f` antitone, `2 f(ℓ + k) ≤ f(ℓ)` (sizes halve every `k` layers), `2 f(1) ≤ n`.

The `k`-stretched complete binary tree has this property (`Stretched.lean`). We show:

* `bswe_of_layerSized`: such a tree is in BSwE for `α ≥ 7kn`;
* `bae_of_layerSized`: it is in BAE for `α ≥ 2kn`;
* hence in BGE for `α ≥ 7kn` (`bge_of_layerSized`).

The proofs are our own (they do not follow Lemmas D.2–D.7 of the paper); they are based on the
potential `Φ_S(y) = ∑_{x ∈ S} dist(y, x)` computed along the root path of `y` (`phi_eq`).
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {r : V}

/-- The ancestor of `y` in layer `t` (for `t ≤ ℓ(y)`). -/
noncomputable def anc (G : SimpleGraph V) (r y : V) (t : ℕ) : V :=
  open Classical in
  if h : ∃ w, G.dist r w = t ∧ y ∈ sub G r w then h.choose else r

section Anc

variable (hT : G.IsTree)
include hT

lemma anc_spec {y : V} {t : ℕ} (ht : t ≤ G.dist r y) :
    G.dist r (anc G r y t) = t ∧ y ∈ sub G r (anc G r y t) := by
  have hex : ∃ w, G.dist r w = t ∧ y ∈ sub G r w := by
    obtain ⟨w, -, h1, h2⟩ := exists_anc hT.connected (u := r) (x := y)
      (by rw [sub_root]; exact mem_univ _) t (by simp) ht
    exact ⟨w, h1, h2⟩
  unfold anc
  rw [dif_pos hex]
  exact hex.choose_spec

lemma anc_eq {y w : V} {t : ℕ} (hw : G.dist r w = t) (hy : y ∈ sub G r w) : anc G r y t = w := by
  have ht : t ≤ G.dist r y := hw ▸ layer_le_of_mem_sub hy
  obtain ⟨h1, h2⟩ := anc_spec hT ht
  exact anc_unique hT h2 hy (h1.trans hw.symm)

lemma anc_self (y : V) : anc G r y (G.dist r y) = y := anc_eq hT rfl self_mem_sub

lemma anc_of_mem {y z : V} {t : ℕ} (hz : y ∈ sub G r z) (ht : t ≤ G.dist r z) :
    anc G r y t = anc G r z t := by
  obtain ⟨h1, h2⟩ := anc_spec hT ht
  exact anc_eq hT h1 (sub_trans hT.connected h2 hz)

lemma anc_adj {y : V} (hy : y ≠ r) :
    G.Adj y (anc G r y (G.dist r y - 1)) ∧
      G.dist r (anc G r y (G.dist r y - 1)) + 1 = G.dist r y := by
  have hl : 1 ≤ G.dist r y := Nat.one_le_iff_ne_zero.2 fun h =>
    hy ((hT.connected.preconnected r y).dist_eq_zero_iff.1 h).symm
  obtain ⟨h1, h2⟩ := anc_spec (r := r) hT (y := y) (t := G.dist r y - 1) (by omega)
  have := mem_sub.1 h2
  refine ⟨?_, by omega⟩
  rw [← dist_eq_one_iff_adj, SimpleGraph.dist_comm]; omega

/-- The potential `Φ_S(y) = ∑_{x∈S} dist(y,x)` along the root path of `y`: each step from a
parent to a child `c` changes it by `|S| - 2 |S ∩ T_c|`. -/
theorem phi_eq (S : Finset V) (y : V) :
    ((∑ x ∈ S, G.dist y x : ℕ) : ℤ) = ((∑ x ∈ S, G.dist r x : ℕ) : ℤ) +
      ∑ t ∈ range (G.dist r y),
        ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r y (t + 1)))).card : ℤ)) := by
  induction h : G.dist r y using Nat.strong_induction_on generalizing y with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : y = r := ((hT.connected.preconnected r y).dist_eq_zero_iff.1 h).symm
      subst this; simp
    · have hy : y ≠ r := by rintro rfl; simp at h; omega
      obtain ⟨hadj, hp⟩ := anc_adj hT hy
      set p := anc G r y (G.dist r y - 1)
      have hpm : G.dist r p = m - 1 := by omega
      have ihp := ih (m - 1) (by omega) p hpm
      have hmove := sum_move (r := r) hT hadj hp S
      have h2 := Finset.card_filter_add_card_filter_not (s := S) (· ∈ sub G r y)
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Finset.sum_range_succ]
      have hanc : ∀ t ∈ range k, anc G r y (t + 1) = anc G r p (t + 1) := by
        intro t ht
        rw [mem_range] at ht
        have hyp : y ∈ sub G r p := mem_sub_of_adj hadj hp
        exact anc_of_mem hT hyp (by omega)
      have hsum : ∑ t ∈ range k,
          ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r y (t + 1)))).card : ℤ)) =
          ∑ t ∈ range k,
          ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r p (t + 1)))).card : ℤ)) :=
        Finset.sum_congr rfl fun t ht => by rw [hanc t ht]
      rw [hsum]
      simp only [Nat.add_sub_cancel] at ihp hpm
      rw [show k + 1 = G.dist r y from h.symm, anc_self hT y]
      rw [← add_assoc, ← ihp]
      push_cast at hmove h2 ⊢
      linarith

end Anc

/-! ### Layer-sized trees -/

/-- Subtree sizes depend only on the layer and halve every `k` layers. -/
structure LayerSized (G : SimpleGraph V) (r : V) (k : ℕ) (f : ℕ → ℕ) : Prop where
  card_sub : ∀ x, (sub G r x).card = f (G.dist r x)
  anti : Antitone f
  decay : ∀ ℓ, 2 * f (ℓ + k) ≤ f ℓ
  half : 2 * f 1 ≤ Fintype.card V

namespace LayerSized

variable {k : ℕ} {f : ℕ → ℕ}

/-- Geometric bound: `∑_{s < N} f(ℓ + s) ≤ 2k f(ℓ)`. -/
lemma sum_le (hL : LayerSized G r k f) (hk : 1 ≤ k) (ℓ N : ℕ) :
    ∑ s ∈ range N, f (ℓ + s) ≤ 2 * k * f ℓ := by
  induction N using Nat.strong_induction_on generalizing ℓ with
  | _ N ih =>
    by_cases hN : N ≤ k
    · calc ∑ s ∈ range N, f (ℓ + s) ≤ ∑ _s ∈ range N, f ℓ :=
            Finset.sum_le_sum fun s _ => hL.anti (by omega)
        _ = N * f ℓ := by simp
        _ ≤ 2 * k * f ℓ := Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨N', rfl⟩ : ∃ N', N = k + N' := ⟨N - k, by omega⟩
      rw [Finset.sum_range_add]
      have h1 : ∑ s ∈ range k, f (ℓ + s) ≤ k * f ℓ := by
        calc ∑ s ∈ range k, f (ℓ + s) ≤ ∑ _s ∈ range k, f ℓ :=
              Finset.sum_le_sum fun s _ => hL.anti (by omega)
          _ = k * f ℓ := by simp
      have h2 := ih N' (by omega) (ℓ + k)
      have h3 := hL.decay ℓ
      simp only [← add_assoc] at h2 ⊢
      calc _ ≤ k * f ℓ + 2 * k * f (ℓ + k) := add_le_add h1 h2
        _ ≤ 2 * k * f ℓ := by nlinarith

/-- `2 ℓ f(ℓ + 1) ≤ k n`. -/
lemma two_mul_le (hL : LayerSized G r k f) (hk : 1 ≤ k) (ℓ : ℕ) :
    2 * ℓ * f (ℓ + 1) ≤ k * Fintype.card V := by
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    have h1 := hL.half
    by_cases hℓ : ℓ ≤ k
    · calc 2 * ℓ * f (ℓ + 1) ≤ 2 * k * f 1 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hℓ) (hL.anti (by omega))
        _ ≤ k * Fintype.card V := by nlinarith
    · obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + k := ⟨ℓ - k, by omega⟩
      have h2 := ih m (by omega)
      have h3 := hL.decay (m + 1)
      have h4 : f (m + 1) ≤ f 1 := hL.anti (by omega)
      rw [show m + k + 1 = m + 1 + k by ring]
      nlinarith

lemma f_zero (hL : LayerSized G r k f) : f 0 = Fintype.card V := by
  have := hL.card_sub r
  rw [sub_root, card_univ, SimpleGraph.dist_self] at this
  exact this.symm

lemma two_mul_f_le (hL : LayerSized G r k f) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 2 * f ℓ ≤ Fintype.card V :=
  le_trans (Nat.mul_le_mul_left _ (hL.anti hℓ)) hL.half

end LayerSized

/-! ### Bilateral Swap Equilibrium -/

section Swap

variable {k : ℕ} {f : ℕ → ℕ} {α : ℝ} {M : ℕ}

/-- Swapping a child edge `uv` (`v` a child of `u`) down into `T_v`: if `w` is far from `v`, then
`v` is at least as central in `T_v` as `w`. -/
lemma caseA_contra (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k) {v w : V}
    (hw : w ∈ sub G r v) (hW : 7 * k * Fintype.card V < Fintype.card V * G.dist w v)
    (hU : ∑ x ∈ sub G r v, G.dist w x < ∑ x ∈ sub G r v, G.dist v x) : False := by
  set n := Fintype.card V
  set S := sub G r v with hSdef
  have hlw := mem_sub.1 hw
  set L := G.dist v w with hLdef
  rw [SimpleGraph.dist_comm] at hW
  have hL7 : 7 * k < L := by
    by_contra h; push Not at h
    have := Nat.mul_le_mul_left n h
    nlinarith
  have hS : S.card = f (G.dist r v) := hL.card_sub v
  have pw := phi_eq (r := r) hT S w
  have pv := phi_eq (r := r) hT S v
  rw [hlw, Finset.sum_range_add] at pw
  have hcommon : ∑ t ∈ range (G.dist r v),
      ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r w (t + 1)))).card : ℤ)) =
      ∑ t ∈ range (G.dist r v),
      ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r v (t + 1)))).card : ℤ)) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [mem_range] at ht
    rw [anc_of_mem hT hw (by omega)]
  have htail : ∀ s ∈ range L,
      ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r w (G.dist r v + s + 1)))).card : ℤ))
        = (f (G.dist r v) : ℤ) - 2 * (f (G.dist r v + 1 + s) : ℤ) := by
    intro s hs
    rw [mem_range] at hs
    obtain ⟨h1, h2⟩ := anc_spec (r := r) hT (y := w) (t := G.dist r v + s + 1) (by omega)
    set c := anc G r w (G.dist r v + s + 1)
    have hcv : c ∈ S := mem_sub_of_mem_sub_of_le hT hw h2 (by omega)
    have hfil : S.filter (· ∈ sub G r c) = sub G r c := by
      ext x; simp only [mem_filter, and_iff_right_iff_imp]
      exact fun hx => sub_trans hT.connected hcv hx
    rw [hfil, hL.card_sub c, h1, hS]
    ring_nf
  rw [Finset.sum_congr rfl htail, hcommon, ← add_assoc, ← pv] at pw
  have hsum := hL.sum_le hk (G.dist r v + 1) L
  have hanti : f (G.dist r v + 1) ≤ f (G.dist r v) := hL.anti (by omega)
  have : ((∑ x ∈ S, G.dist w x : ℕ) : ℤ) < ((∑ x ∈ S, G.dist v x : ℕ) : ℤ) := by
    exact_mod_cast hU
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, ← Finset.mul_sum] at pw
  have hsum' : (∑ s ∈ range L, (f (G.dist r v + 1 + s) : ℤ)) ≤ 2 * k * f (G.dist r v + 1) := by
    exact_mod_cast hsum
  rw [nsmul_eq_mul] at pw
  have : (4 * k : ℤ) * f (G.dist r v) ≤ L * f (G.dist r v) := by
    have : (4 * k : ℤ) ≤ L := by exact_mod_cast (show 4 * k ≤ L by omega)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h5 : (f (G.dist r v + 1) : ℤ) ≤ f (G.dist r v) := by exact_mod_cast hanti
  have h6 : (k : ℤ) * f (G.dist r v + 1) ≤ k * f (G.dist r v) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  linarith

/-- Swapping the parent edge `uv` (`v` the parent of `u`) to a far `w`: `v` is at least as
central in `V ∖ T_u` as `w`. -/
lemma caseB_contra (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k) {u v w : V}
    (huv : G.Adj u v) (hp : G.dist r v + 1 = G.dist r u) (hw : w ∉ sub G r u)
    (hW : 7 * k * Fintype.card V < f (G.dist r u) * G.dist w v)
    (hU : ∑ x ∈ (sub G r u)ᶜ, G.dist w x < ∑ x ∈ (sub G r u)ᶜ, G.dist v x) : False := by
  have hG := hT.connected
  set n := Fintype.card V
  set S := (sub G r u)ᶜ with hSdef
  set fu := f (G.dist r u)
  have hSc : (S.card : ℤ) = n - fu := by
    rw [card_compl, hL.card_sub u, Nat.cast_sub]
    exact (hL.card_sub u) ▸ card_le_univ _
  have hfu2 : 2 * fu ≤ n := hL.two_mul_f_le (by omega)
  have hlv : 2 * G.dist r v * fu ≤ k * n := by
    have := hL.two_mul_le hk (G.dist r v); rwa [hp] at this
  have htri : G.dist w v ≤ G.dist r w + G.dist r v := by
    have := hG.dist_triangle (u := w) (v := r) (w := v)
    rwa [SimpleGraph.dist_comm (u := w) (v := r)] at this
  have hW' : 7 * k * n < fu * (G.dist r w + G.dist r v) :=
    lt_of_lt_of_le hW (Nat.mul_le_mul_left _ htri)
  -- `w` is deeper than `v`
  have hdeep : G.dist r v < G.dist r w := by
    by_contra h; push Not at h
    have : fu * (G.dist r w + G.dist r v) ≤ 2 * G.dist r v * fu := by nlinarith
    have : k * n ≤ 7 * k * n := by nlinarith
    omega
  obtain ⟨N, hN⟩ : ∃ N, G.dist r w = G.dist r v + N := ⟨G.dist r w - G.dist r v, by omega⟩
  have hNfu : 6 * k * n < fu * N := by rw [hN] at hW'; nlinarith
  -- the two potentials
  have pw := phi_eq (r := r) hT S w
  have pv := phi_eq (r := r) hT S v
  have hvterm : ∀ t ∈ range (G.dist r v),
      ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r v (t + 1)))).card : ℤ)) =
        (n : ℤ) + fu - 2 * f (t + 1) := by
    intro t ht
    rw [mem_range] at ht
    obtain ⟨h1, h2⟩ := anc_spec (r := r) hT (y := v) (t := t + 1) (by omega)
    set c := anc G r v (t + 1)
    have huc : sub G r u ⊆ sub G r c :=
      sub_subset hG (sub_trans hG h2 (mem_sub_of_adj huv hp))
    have hfil : S.filter (· ∈ sub G r c) = sub G r c \ sub G r u := by
      ext x; simp [S, and_comm]
    rw [hfil, card_sdiff_of_subset huc, hL.card_sub c, hL.card_sub u, h1, hSc]
    have := hL.card_sub u ▸ card_le_card huc
    rw [hL.card_sub c, h1] at this
    push_cast [this]; ring
  have hwterm : ∀ t ∈ range (G.dist r w),
      (n : ℤ) - fu - 2 * f (t + 1) ≤
      ((S.card : ℤ) - 2 * ((S.filter (· ∈ sub G r (anc G r w (t + 1)))).card : ℤ)) := by
    intro t ht
    rw [mem_range] at ht
    obtain ⟨h1, -⟩ := anc_spec (r := r) hT (y := w) (t := t + 1) (by omega)
    have : (S.filter (· ∈ sub G r (anc G r w (t + 1)))).card ≤ f (t + 1) := by
      calc (S.filter (· ∈ sub G r (anc G r w (t + 1)))).card
          ≤ (sub G r (anc G r w (t + 1))).card := card_le_card fun x hx => (mem_filter.1 hx).2
        _ = f (t + 1) := by rw [hL.card_sub, h1]
    rw [hSc]
    have : ((S.filter (· ∈ sub G r (anc G r w (t + 1)))).card : ℤ) ≤ f (t + 1) := by
      exact_mod_cast this
    linarith
  rw [Finset.sum_congr rfl hvterm] at pv
  have hwsum := Finset.sum_le_sum hwterm
  rw [hN, Finset.sum_range_add] at hwsum
  rw [hN] at pw
  -- assemble
  have hsum := hL.sum_le hk (G.dist r v + 1) N
  have hsum' : (∑ s ∈ range N, (f (G.dist r v + 1 + s) : ℤ)) ≤ 2 * k * fu := by
    have h2 : f (G.dist r v + 1) = fu := by simp only [fu, hp]
    rw [h2] at hsum; exact_mod_cast hsum
  have e1 : ∑ t ∈ range (G.dist r v), ((n : ℤ) - fu - 2 * f (t + 1)) -
      ∑ t ∈ range (G.dist r v), ((n : ℤ) + fu - 2 * f (t + 1)) = -2 * fu * G.dist r v := by
    rw [← Finset.sum_sub_distrib]; simp; ring
  have e2 : ∑ s ∈ range N, ((n : ℤ) - fu - 2 * f (G.dist r v + s + 1)) =
      N * (n - fu) - 2 * ∑ s ∈ range N, (f (G.dist r v + 1 + s) : ℤ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    congr 2
    exact Finset.sum_congr rfl fun s _ => by ring_nf
  have hU' : ((∑ x ∈ S, G.dist w x : ℕ) : ℤ) < ((∑ x ∈ S, G.dist v x : ℕ) : ℤ) := by
    exact_mod_cast hU
  have hlv' : (2 * G.dist r v * fu : ℤ) ≤ k * n := by exact_mod_cast hlv
  have hNfu' : (6 * k * n : ℤ) < fu * N := by exact_mod_cast hNfu
  have hfu2' : (2 * fu : ℤ) ≤ n := by exact_mod_cast hfu2
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hN0 : (0 : ℤ) ≤ N := by positivity
  have hfu0 : (0 : ℤ) ≤ fu := by positivity
  rw [e2] at hwsum
  have hA : (N : ℤ) * fu ≤ N * (n - fu) := mul_le_mul_of_nonneg_left (by linarith) hN0
  have hB : (4 * k * fu : ℤ) ≤ 2 * k * n := by nlinarith
  have key : ((∑ x ∈ S, G.dist w x : ℕ) : ℤ) - ((∑ x ∈ S, G.dist v x : ℕ) : ℤ) ≥
      -2 * fu * G.dist r v + N * (n - fu) -
        2 * ∑ s ∈ range N, (f (G.dist r v + 1 + s) : ℤ) := by
    linarith
  nlinarith

/-- The common part of the swap analysis: if `u` swaps `uv` for `uw` and both improve, then `w`
lies on `v`'s side of `uv`, `v` is strictly less central there than `w`, and
`α < |A| · dist(w, v)` where `A` is `u`'s side. -/
lemma swap_core (hT : G.IsTree) (hα : 0 ≤ α) (hMn : Fintype.card V ≤ M)
    (hMc : ∀ x, cost α M G x < M) {A : Finset V} {u v w : V} (huA : u ∈ A) (hvA : v ∉ A)
    (hcut : ∀ x y, G.Adj x y → x ∈ A → y ∉ A → x = u ∧ y = v) (huv : G.Adj u v) (huw : u ≠ w)
    (hnuw : ¬ G.Adj u w) (himp : cost α M (swap G u v w) u < cost α M G u)
    (hw : cost α M (swap G u v w) w < cost α M G w)
    (hdu : ∀ x ∉ A, G.dist u x = 1 + G.dist v x)
    (hdw : w ∉ A → ∀ x ∈ A, G.dist w x = G.dist w v + 1 + G.dist u x) :
    w ∉ A ∧ ∑ x ∈ Aᶜ, G.dist w x < ∑ x ∈ Aᶜ, G.dist v x ∧ α < A.card * G.dist w v := by
  have hG := hT.connected
  have hdef : ∀ y, distCost M (swap G u v w) y =
      ∑ x, d M (G.deleteEdges {s(u, v)} ⊔ edge u w) y x := fun y => rfl
  have hwA : w ∉ A := by
    intro hwA
    have hnr := not_reachable_cut hcut huA hwA huA hvA
    have h1 : M ≤ distCost M (swap G u v w) u := by
      rw [hdef]
      calc M = d M (G.deleteEdges {s(u, v)} ⊔ edge u w) u v := (d_of_not_reachable hnr).symm
        _ ≤ _ := Finset.single_le_sum (f := fun y => d M (G.deleteEdges {s(u, v)} ⊔ edge u w) u y)
              (fun _ _ => Nat.zero_le _) (mem_univ v)
    have h2 := hMc u
    unfold cost at himp
    have : (M : ℝ) ≤ distCost M (swap G u v w) u := by exact_mod_cast h1
    have : 0 ≤ α * deg (swap G u v w) u := by positivity
    unfold cost at h2
    linarith
  refine ⟨hwA, ?_, ?_⟩
  · have hsum := Finset.sum_le_sum fun y (_ : y ∈ univ) =>
      d_swap_ge (M := M) (G := G) hMn hcut huA hwA y
    rw [sum_ite_mem, ← hdef] at hsum
    have heq : distCost M G u = ∑ x ∈ A, G.dist u x + ∑ x ∈ Aᶜ, (1 + G.dist v x) := by
      rw [distCost_eq_sum_dist hG, ← Finset.sum_add_sum_compl A]
      congr 1
      exact Finset.sum_congr rfl fun x hx => hdu x (mem_compl.1 hx)
    have hlt : distCost M (swap G u v w) u < distCost M G u := by
      unfold cost at himp
      rw [deg_swap_self huv huw hnuw] at himp
      exact_mod_cast (by linarith : (distCost M (swap G u v w) u : ℝ) < distCost M G u)
    rw [Finset.sum_add_distrib] at hsum heq
    omega
  · have hcut' : ∀ x y, G.Adj x y → x ∈ Aᶜ → y ∉ Aᶜ → x = v ∧ y = u := by
      intro x y h hx hy
      rw [mem_compl] at hx; rw [mem_compl, not_not] at hy
      obtain ⟨h1, h2⟩ := hcut y x h.symm hy hx
      exact ⟨h2, h1⟩
    have hgraph : G.deleteEdges {s(v, u)} ⊔ edge w u = swap G u v w := by
      rw [Sym2.eq_swap, edge_comm]; rfl
    have hsum := Finset.sum_le_sum fun y (_ : y ∈ univ) =>
      d_swap_ge (M := M) (G := G) hMn hcut' (mem_compl.2 hwA) (by simpa using huA) y
    rw [sum_ite_mem, compl_compl, hgraph] at hsum
    have hd' : ∑ x, d M (swap G u v w) w x = distCost M (swap G u v w) w := rfl
    rw [hd'] at hsum
    have heq : distCost M G w = ∑ x ∈ Aᶜ, G.dist w x +
        ∑ x ∈ A, (G.dist w v + (1 + G.dist u x)) := by
      rw [distCost_eq_sum_dist hG, ← Finset.sum_add_sum_compl A, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun x hx => by rw [hdw hwA x hx]; ring
    unfold cost at hw
    rw [deg_swap_other huv huw hnuw] at hw
    push_cast at hw
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at heq
    have h1 : (distCost M (swap G u v w) w : ℝ) ≥ ((∑ x ∈ Aᶜ, G.dist w x : ℕ) : ℝ) +
        ((∑ x ∈ A, (1 + G.dist u x) : ℕ) : ℝ) := by exact_mod_cast hsum
    have h2 : (distCost M G w : ℝ) = ∑ x ∈ Aᶜ, G.dist w x + A.card * G.dist w v +
        ∑ x ∈ A, (1 + G.dist u x) := by rw [heq]; push_cast; ring
    linarith

/-- Proposition 3.8, BSwE part (abstract form): a layer-sized tree is in BSwE for `α ≥ 7kn`. -/
theorem bswe_of_layerSized (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k)
    (hα : 7 * k * Fintype.card V ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) : BSwE α M G := by
  have hG := hT.connected
  intro u v w huv huw hnuw himp
  by_contra hw
  push Not at hw
  set n := Fintype.card V
  have hn2 : 2 ≤ n := by
    have : ({u, v} : Finset V).card = 2 := card_pair huv.ne
    rw [← this]; exact card_le_univ _
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hα1 : 1 ≤ α := by
    have : (1 : ℝ) ≤ 7 * k * n := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    linarith
  have hα0 : 0 ≤ α := by linarith
  have hMn := card_le_M hα1 hM
  have hMc : ∀ x, cost α M G x < M := by
    intro x
    have hdeg : deg G x ≤ n := by
      unfold deg; exact (Set.ncard_le_ncard (Set.subset_univ _)).trans (by simp [n])
    have hdc : distCost M G x ≤ n * n := by
      rw [distCost_eq_sum_dist hG]
      calc ∑ y, G.dist x y ≤ ∑ _y : V, n :=
            Finset.sum_le_sum fun y _ => (dist_lt_card (hG x y)).le
        _ = n * n := by simp [n]
    have h1 : (deg G x : ℝ) ≤ n := by exact_mod_cast hdeg
    have h2 : (distCost M G x : ℝ) ≤ n * n := by exact_mod_cast hdc
    unfold cost
    have h3 : α * n + n * n ≤ α * (n : ℝ) ^ 3 := by
      have e1 : (n : ℝ) * n ≤ α * n * n := by nlinarith
      have e2 : α * n ≤ α * n * n := by nlinarith
      have e3 : α * n * n * 2 ≤ α * n * n * n :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
      nlinarith
    nlinarith
  rcases hT.dist_eq_dist_add_one_of_adj r huv with h | h
  · -- `v` is the parent of `u`
    have hp : G.dist r v + 1 = G.dist r u := h.symm
    obtain ⟨hwA, hU, hW⟩ := swap_core hT hα0 hMn hMc self_mem_sub (parent_not_mem_sub hp)
      (fun x y hxy hx hy => eq_of_adj_cross hT huv hp hxy hx hy) huv huw hnuw himp hw
      (fun x hx => by have := dist_child_of_not_mem hT huv hp hx; omega)
      (fun hwA x hx => by
        have := dist_cross hT huv hp hx hwA
        rw [SimpleGraph.dist_comm (u := x), SimpleGraph.dist_comm (u := x),
          SimpleGraph.dist_comm (u := v)] at this
        omega)
    refine caseB_contra hT hL hk huv hp hwA ?_ hU
    rw [hL.card_sub u] at hW
    have : ((7 * k * n : ℕ) : ℝ) < ((f (G.dist r u) * G.dist w v : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · -- `u` is the parent of `v`
    have hp : G.dist r u + 1 = G.dist r v := h.symm
    have hvu : G.Adj v u := huv.symm
    obtain ⟨hwA, hU, hW⟩ := swap_core (A := (sub G r v)ᶜ) hT hα0 hMn hMc
      (mem_compl.2 (parent_not_mem_sub hp)) (by simp [self_mem_sub])
      (fun x y hxy hx hy => by
        rw [mem_compl] at hx; rw [mem_compl, not_not] at hy
        obtain ⟨h1, h2⟩ := eq_of_adj_cross hT hvu hp hxy.symm hy hx
        exact ⟨h2, h1⟩) huv huw hnuw himp hw
      (fun x hx => by
        rw [mem_compl, not_not] at hx
        have := dist_parent_of_mem hT hvu hp hx; omega)
      (fun hwA x hx => by
        rw [mem_compl, not_not] at hwA; rw [mem_compl] at hx
        exact dist_cross hT hvu hp hwA hx)
    rw [compl_compl] at hU
    rw [mem_compl, not_not] at hwA
    refine caseA_contra hT hL hk hwA ?_ hU
    have hc : ((sub G r v)ᶜ.card : ℝ) ≤ n := by exact_mod_cast card_le_univ _
    have : ((7 * k * n : ℕ) : ℝ) < ((n * G.dist w v : ℕ) : ℝ) := by
      push_cast
      have : ((sub G r v)ᶜ.card : ℝ) * G.dist w v ≤ n * G.dist w v :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      linarith
    exact_mod_cast this

end Swap

/-! ### Bilateral Add Equilibrium -/

section Add

variable {k : ℕ} {f : ℕ → ℕ} {α : ℝ} {M : ℕ}

lemma sum_range_two_mul_half (g : ℕ → ℕ) (J : ℕ) :
    ∑ e ∈ range (2 * J), g (e / 2) = 2 * ∑ j ∈ range J, g j := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show 2 * (J + 1) = 2 * J + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : (2 * J + 1) / 2 = J := by omega
    have h2 : 2 * J / 2 = J := by omega
    rw [h1, h2]; ring

lemma sum_Ico_half_le (g : ℕ → ℕ) (D : ℕ) :
    ∑ s ∈ Ico 2 (D + 1), g ((D - s) / 2) ≤ 2 * ∑ j ∈ range (D / 2), g j := by
  rw [Finset.sum_Ico_reflect (fun e => g (e / 2)) 2 (le_refl _)]
  rw [Nat.sub_self, Nat.Ico_zero_eq_range, show D + 1 - 2 = D - 1 by omega,
    ← sum_range_two_mul_half]
  exact Finset.sum_le_sum_of_subset (range_subset_range.2 (by omega))

/-- In a layer-sized tree, the shallower endpoint `a` of a new edge `ab` gains at most `2kn` in
distance cost, so it does not improve for `α ≥ 2kn`. -/
lemma add_gain (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k) {a b : V} (hab : a ≠ b)
    (hnadj : ¬ G.Adj a b) (hl : G.dist r a ≤ G.dist r b) (hα : 2 * k * Fintype.card V ≤ α)
    (hMn : Fintype.card V ≤ M) : cost α M G a ≤ cost α M (G ⊔ edge a b) a := by
  have hG := hT.connected
  set n := Fintype.card V
  set D := G.dist a b
  have hDl : D ≤ G.dist r a + G.dist r b := by
    have := hG.dist_triangle (u := a) (v := r) (w := b)
    rwa [SimpleGraph.dist_comm (u := a) (v := r)] at this
  -- the sets `A_s`
  have hAs : ∀ s ∈ Ico 2 (D + 1),
      (univ.filter fun x => s + G.dist b x ≤ G.dist a x).card ≤ f (G.dist r b - (D - s) / 2) := by
    intro s hs
    rw [mem_Ico] at hs
    set j := (D - s) / 2
    have hj : j < G.dist r b := by omega
    obtain ⟨h1, h2⟩ := anc_spec (r := r) hT (y := b) (t := G.dist r b - j) (by omega)
    set y := anc G r b (G.dist r b - j)
    have hby := mem_sub.1 h2
    have hay : a ∉ sub G r y := by
      intro hay
      have := mem_sub.1 hay
      have t := hG.dist_triangle (u := a) (v := y) (w := b)
      rw [SimpleGraph.dist_comm (u := a) (v := y)] at t
      omega
    have hyr : y ≠ r := by rintro hyr; rw [hyr, sub_root] at hay; exact hay (mem_univ _)
    obtain ⟨hadj, hp⟩ := anc_adj hT hyr
    set p := anc G r y (G.dist r y - 1)
    calc (univ.filter fun x => s + G.dist b x ≤ G.dist a x).card ≤ (sub G r y).card := by
          refine card_le_card fun x hx => ?_
          rw [mem_filter] at hx
          by_contra hxy
          have c1 := dist_cross hT hadj hp h2 hxy
          have c2 := dist_cross hT hadj hp h2 hay
          have t := hG.dist_triangle (u := a) (v := p) (w := x)
          rw [SimpleGraph.dist_comm (u := b) (v := a)] at c2
          rw [SimpleGraph.dist_comm (u := a) (v := p)] at t
          rw [SimpleGraph.dist_comm (u := b) (v := y)] at c1 c2
          omega
      _ = f (G.dist r b - j) := by rw [hL.card_sub, h1]
  -- layer cake
  have hpt : ∀ x, G.dist a x - (1 + G.dist b x) ≤
      ((Ico 2 (D + 1)).filter fun s => s + G.dist b x ≤ G.dist a x).card := by
    intro x
    have t := hG.dist_triangle (u := a) (v := b) (w := x)
    have : Ico 2 (G.dist a x - G.dist b x + 1) ⊆
        (Ico 2 (D + 1)).filter fun s => s + G.dist b x ≤ G.dist a x := by
      intro s hs; rw [mem_Ico] at hs; rw [mem_filter, mem_Ico]; omega
    have := card_le_card this
    rw [Nat.card_Ico] at this
    omega
  have hcake : ∑ x, (G.dist a x - (1 + G.dist b x)) ≤ 2 * k * n := by
    calc ∑ x, (G.dist a x - (1 + G.dist b x))
        ≤ ∑ x, ((Ico 2 (D + 1)).filter fun s => s + G.dist b x ≤ G.dist a x).card :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = ∑ s ∈ Ico 2 (D + 1), (univ.filter fun x => s + G.dist b x ≤ G.dist a x).card := by
          simp only [card_eq_sum_ones, sum_filter]
          exact Finset.sum_comm
      _ ≤ ∑ s ∈ Ico 2 (D + 1), f (G.dist r b - (D - s) / 2) := Finset.sum_le_sum hAs
      _ ≤ 2 * ∑ j ∈ range (D / 2), f (G.dist r b - j) :=
          sum_Ico_half_le (fun j => f (G.dist r b - j)) D
      _ ≤ 2 * ∑ j ∈ range (G.dist r b), f (G.dist r b - j) := by
          gcongr; omega
      _ = 2 * ∑ t ∈ range (G.dist r b), f (1 + t) := by
          congr 1
          rw [← Finset.sum_range_reflect]
          exact Finset.sum_congr rfl fun t ht => by rw [mem_range] at ht; congr 1; omega
      _ ≤ 2 * (2 * k * f 1) := by gcongr; exact hL.sum_le hk 1 _
      _ ≤ 2 * k * n := by have := hL.half; nlinarith
  -- costs
  have hge : ∀ x, min (G.dist a x) (1 + G.dist b x) ≤ d M (G ⊔ edge a b) a x :=
    fun x => d_add_ge hMn a b x
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) => hge x
  have hmin : ∀ x, min (G.dist a x) (1 + G.dist b x) + (G.dist a x - (1 + G.dist b x)) =
      G.dist a x := fun x => by omega
  have htot : distCost M G a ≤ distCost M (G ⊔ edge a b) a + 2 * k * n := by
    rw [distCost_eq_sum_dist hG]
    have e : ∑ x, min (G.dist a x) (1 + G.dist b x) + ∑ x, (G.dist a x - (1 + G.dist b x)) =
        ∑ x, G.dist a x := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => hmin x
    unfold distCost
    omega
  have hdeg : deg (G ⊔ edge a b) a = deg G a + 1 := by
    have : (G ⊔ edge a b).neighborSet a = insert b (G.neighborSet a) := by
      ext x
      simp only [mem_neighborSet, sup_adj, edge_adj, Set.mem_insert_iff]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inr h
        · rcases h with ⟨-, rfl⟩ | ⟨rfl, -⟩
          · exact Or.inl rfl
          · exact absurd rfl hab
      · rintro (rfl | h)
        · exact Or.inr ⟨Or.inl ⟨trivial, rfl⟩, hab⟩
        · exact Or.inl h
    unfold deg
    rw [this, Set.ncard_insert_of_notMem (by simpa [mem_neighborSet] using hnadj) (Set.toFinite _)]
  unfold cost
  rw [hdeg]
  push_cast
  have h1 : (distCost M G a : ℝ) ≤ distCost M (G ⊔ edge a b) a + 2 * k * n := by
    exact_mod_cast htot
  linarith

/-- Proposition 3.8, BAE part (abstract form): a layer-sized tree is in BAE for `α ≥ 2kn`. -/
theorem bae_of_layerSized (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k)
    (hα : 2 * k * Fintype.card V ≤ α) (hMn : Fintype.card V ≤ M) : BAE α M G := by
  intro u v huv hnadj himp
  rcases le_total (G.dist r u) (G.dist r v) with hl | hl
  · exact absurd (add_gain hT hL hk huv hnadj hl hα hMn) (not_le.2 himp)
  · rw [edge_comm]
    exact add_gain hT hL hk huv.symm (fun h => hnadj h.symm) hl hα hMn

/-- Proposition 3.8 (abstract form): a layer-sized tree is in BGE for `α ≥ 7kn`. -/
theorem bge_of_layerSized (hT : G.IsTree) (hL : LayerSized G r k f) (hk : 1 ≤ k)
    (hα : 7 * k * Fintype.card V ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) : BGE α M G := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 hT.connected.nonempty
  have hn1' : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hα1 : 1 ≤ α := by nlinarith
  have hMn := card_le_M hα1 hM
  refine ⟨⟨fun u v huv => ?_, bae_of_layerSized hT hL hk (by nlinarith) hMn⟩,
    bswe_of_layerSized hT hL hk hα hM⟩
  have hn2 : 2 ≤ Fintype.card V := by
    have : ({u, v} : Finset V).card = 2 := card_pair huv.ne
    rw [← this]; exact card_le_univ _
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn2
  have hM' : α + 1 ≤ M := by
    have h8 : (2 : ℝ) ^ 3 ≤ (Fintype.card V : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn' 3
    nlinarith [mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ α)]
  exact tree_RE hT (by linarith) hMn hM' u v huv

end Add

end Podc.BilateralNetworkCreation
