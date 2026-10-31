import Papers.PODC2015.DeterministicLoadBalancing.Model

/-!
# Lower bound for stateless algorithms (Theorem 4.2)

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, *Improved Analysis of Deterministic
Load-Balancing Schemes*, PODC 2015 (arXiv:1404.4344v4), Theorem 4.2 and its proof in
Appendix C.2.

An *anonymous stateless deterministic* algorithm with `d` ports (`StatelessAlg d`) is given by two
functions of the current load `x` of a node only: the number `keep x` of tokens kept (the paper's
`p◦`, tokens sent over self-loops / kept as remainder) and the numbers `send x i` of tokens sent
over port `i : Fin d` (the paper's `p₁, …, p_d`). The assignment of ports to the edges of a node
(`port v : Fin d ≃ G.neighborFinset v`) is chosen by the adversary, as in the paper's proof.

**Theorem 4.2.** For every even `n` and every `d < n` there is a `d`-regular graph on `n` nodes, a
port numbering and an initial load vector such that the discrepancy stays `≥ d/3` forever.

Proof (paper, with fixes): `G` is the circulant graph on `Fin n` with jumps `±1, …, ±⌊d/2⌋` and,
for odd `d`, `n/2` (`lbGraph`). The nodes `C = {0, …, h}`, `h = ⌊d/2⌋`, form a clique. All nodes of
`C` get load `h`, all others `0`. With `p = send h`, at most `h` ports carry a positive value; the
port numbering of a clique node `v` maps the `k`-th such port to the clique node `(v + k) mod (h+1)`.
Then every clique node receives exactly `∑ p = h - keep h` and every other node nothing, so the load
vector is a fixed point with discrepancy `h ≥ d/3` (for `d ≥ 2`). For `d = 1` a single token on a
single node gives discrepancy `≥ 1` forever since `n ∤ 1`.
-/

open Finset

namespace Podc.DeterministicLoadBalancing

/-- An anonymous, stateless, deterministic load-balancing algorithm for nodes with `d` ports: a node
with load `x` keeps `keep x` tokens (the paper's `p◦`) and sends `send x i` tokens over its port `i`
(the paper's `p_i`). Tokens are conserved. -/
structure StatelessAlg (d : ℕ) where
  /-- `p◦`: tokens kept (self-loops / remainder) by a node with load `x`. -/
  keep : ℕ → ℕ
  /-- `p_i`: tokens sent over port `i` by a node with load `x`. -/
  send : ℕ → Fin d → ℕ
  /-- Conservation of tokens. -/
  conserve : ∀ x, keep x + ∑ i, send x i = x

namespace StatelessAlg

variable {d : ℕ} (A : StatelessAlg d)

lemma send_le (x : ℕ) (i : Fin d) : A.send x i ≤ x := by
  have := A.conserve x
  have : A.send x i ≤ ∑ j, A.send x j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  omega

lemma send_zero (i : Fin d) : A.send 0 i = 0 := Nat.le_zero.1 (A.send_le 0 i)

lemma keep_zero : A.keep 0 = 0 := by have := A.conserve 0; omega

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Tokens sent by node `v` with load `x` to node `w`, given the port numbering `port`. -/
def out (G : SimpleGraph V) [DecidableRel G.Adj] (port : ∀ v, Fin d ≃ G.neighborFinset v)
    (v : V) (x : ℕ) (w : V) : ℕ :=
  if h : w ∈ G.neighborFinset v then A.send x ((port v).symm ⟨w, h⟩) else 0

lemma sum_out (G : SimpleGraph V) [DecidableRel G.Adj] (port : ∀ v, Fin d ≃ G.neighborFinset v)
    (v : V) (x : ℕ) : ∑ w ∈ G.neighborFinset v, A.out G port v x w = ∑ i, A.send x i := by
  unfold out
  rw [← Finset.sum_attach, ← Finset.univ_eq_attach]
  simp only [Finset.coe_mem, dite_true, Subtype.coe_eta]
  exact Equiv.sum_comp (port v).symm (A.send x)

/-- The balancer on `G` obtained by running `A` with the port numbering `port`. -/
def toBalancer (G : SimpleGraph V) [DecidableRel G.Adj] (port : ∀ v, Fin d ≃ G.neighborFinset v) :
    Balancer G :=
  Balancer.stateless G (A.out G port) (fun _ x => A.keep x)
    (fun v x => by rw [A.sum_out G port v x]; exact A.conserve x)

lemma load_succ_toBalancer (G : SimpleGraph V) [DecidableRel G.Adj]
    (port : ∀ v, Fin d ≃ G.neighborFinset v) (x₀ : V → ℕ) (t : ℕ) (v : V) :
    (A.toBalancer G port).load x₀ (t + 1) v =
      A.keep ((A.toBalancer G port).load x₀ t v) +
        ∑ w ∈ G.neighborFinset v, A.out G port w ((A.toBalancer G port).load x₀ t w) v := by
  rw [Balancer.load_succ]; rfl

end StatelessAlg

/-! ### The lower-bound graph -/

/-- The circulant graph on `Fin n` with jumps `±1, …, ±⌊d/2⌋` and, for odd `d`, `n/2`
(written with the linear distance `|i - j|`: `i ∼ j` iff the circular distance is `≤ ⌊d/2⌋`,
or `d` is odd and `|i - j| = n/2`). -/
def lbGraph (n d : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val ≠ j.val ∧ ((i.val - j.val) + (j.val - i.val) ≤ d / 2 ∨
    n - d / 2 ≤ (i.val - j.val) + (j.val - i.val) ∨
    (d % 2 = 1 ∧ 2 * ((i.val - j.val) + (j.val - i.val)) = n))
  symm := ⟨fun i j h => by omega⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance (n d : ℕ) : DecidableRel (lbGraph n d).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The offsets `k` (with `0 ≤ k < n`) such that `v ∼ v + k` in `lbGraph n d`. -/
def lbOffset (n d k : ℕ) : Prop := k ≠ 0 ∧ (k ≤ d / 2 ∨ n - d / 2 ≤ k ∨ (d % 2 = 1 ∧ 2 * k = n))

instance (n d : ℕ) : DecidablePred (lbOffset n d) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma lbGraph_adj_iff {n d : ℕ} [NeZero n] (v w : Fin n) :
    (lbGraph n d).Adj v w ↔ lbOffset n d (w - v).val := by
  have hv := v.isLt
  have hw := w.isLt
  rcases le_or_gt v w with h | h
  · rw [Fin.coe_sub_iff_le.mpr h]
    have : v.val ≤ w.val := h
    simp only [lbGraph, lbOffset]; omega
  · rw [Fin.coe_sub_iff_lt.mpr h]
    have : w.val < v.val := h
    simp only [lbGraph, lbOffset]; omega

lemma card_filter_fin_val {n : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    #(univ.filter fun k : Fin n => P k.val) = #((range n).filter P) := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext k
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.isLt, ha⟩
  · rintro ⟨hk, hP⟩; exact ⟨⟨k, hk⟩, hP, rfl⟩

lemma card_lbOffset {n d : ℕ} (hn : Even n) (hdn : d < n) :
    #((range n).filter (lbOffset n d)) = d := by
  obtain ⟨r, rfl⟩ := hn
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd
  · have : (range (r + r)).filter (lbOffset (r + r) d) = Icc 1 (d / 2) ∪ Ico (r + r - d / 2) (r + r) := by
      ext k; simp only [mem_filter, mem_range, lbOffset, mem_union, mem_Icc, mem_Ico]; omega
    rw [this, card_union_of_disjoint, Nat.card_Icc, Nat.card_Ico]
    · omega
    · rw [Finset.disjoint_left]; intro k; simp only [mem_Icc, mem_Ico]; omega
  · have : (range (r + r)).filter (lbOffset (r + r) d) =
        (Icc 1 (d / 2) ∪ Ico (r + r - d / 2) (r + r)) ∪ {r} := by
      ext k; simp only [mem_filter, mem_range, lbOffset, mem_union, mem_Icc, mem_Ico,
        mem_singleton]; omega
    rw [this, card_union_of_disjoint, card_union_of_disjoint, Nat.card_Icc, Nat.card_Ico,
      card_singleton]
    · omega
    · rw [Finset.disjoint_left]; intro k; simp only [mem_Icc, mem_Ico]; omega
    · rw [Finset.disjoint_left]; intro k
      simp only [mem_union, mem_Icc, mem_Ico, mem_singleton]; omega

/-- `lbGraph n d` is `d`-regular for even `n > d`. -/
lemma lbGraph_isRegular {n d : ℕ} (hn : Even n) (hdn : d < n) :
    (lbGraph n d).IsRegularOfDegree d := by
  have : NeZero n := ⟨by omega⟩
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (lbGraph n d).neighborFinset v =
      (univ.filter fun k : Fin n => lbOffset n d k.val).map (Equiv.addRight v).toEmbedding := by
    ext w
    simp [lbGraph_adj_iff, sub_eq_add_neg]
  rw [this, card_map, card_filter_fin_val, card_lbOffset hn hdn]

/-! ### The adversarial port numbering and the fixed point -/

section LowerBound

variable {d : ℕ}

/-- The ports over which the send vector `p` carries a positive number of tokens. -/
def posPorts (p : Fin d → ℕ) : Finset (Fin d) := univ.filter fun j => p j ≠ 0

/-- An injective labelling of the positive ports of `p` by `1, …, #(posPorts p)` (`0` elsewhere). -/
noncomputable def portLabel (p : Fin d → ℕ) (j : Fin d) : ℕ :=
  if hj : j ∈ posPorts p then ((posPorts p).equivFin ⟨j, hj⟩).val + 1 else 0

lemma card_posPorts_le (p : Fin d → ℕ) : #(posPorts p) ≤ ∑ j, p j :=
  calc #(posPorts p) = ∑ j ∈ posPorts p, 1 := card_eq_sum_ones _
    _ ≤ ∑ j ∈ posPorts p, p j :=
        sum_le_sum fun j hj => Nat.one_le_iff_ne_zero.2 (by simpa [posPorts] using hj)
    _ ≤ ∑ j, p j := sum_le_sum_of_subset (subset_univ _)

lemma mem_posPorts {p : Fin d → ℕ} {j : Fin d} : j ∈ posPorts p ↔ p j ≠ 0 := by
  simp [posPorts]

lemma portLabel_eq {p : Fin d → ℕ} {j : Fin d} (hj : j ∈ posPorts p) :
    portLabel p j = ((posPorts p).equivFin ⟨j, hj⟩).val + 1 := by
  unfold portLabel; split_ifs; rfl

lemma one_le_portLabel {p : Fin d → ℕ} {j : Fin d} (hj : p j ≠ 0) : 1 ≤ portLabel p j := by
  rw [portLabel_eq (mem_posPorts.2 hj)]; omega

lemma portLabel_le {p : Fin d → ℕ} {j : Fin d} (hj : p j ≠ 0) : portLabel p j ≤ ∑ i, p i := by
  rw [portLabel_eq (mem_posPorts.2 hj)]
  have := ((posPorts p).equivFin ⟨j, mem_posPorts.2 hj⟩).isLt
  have := card_posPorts_le p
  omega

lemma portLabel_inj {p : Fin d → ℕ} {j j' : Fin d} (hj : p j ≠ 0) (hj' : p j' ≠ 0)
    (h : portLabel p j = portLabel p j') : j = j' := by
  rw [portLabel_eq (mem_posPorts.2 hj), portLabel_eq (mem_posPorts.2 hj')] at h
  have := (posPorts p).equivFin.injective (a₁ := ⟨j, mem_posPorts.2 hj⟩)
    (a₂ := ⟨j', mem_posPorts.2 hj'⟩) (Fin.ext (by omega))
  simpa using this

lemma mod_eq_ite {x m : ℕ} (hx : x < 2 * m) : x % m = if x < m then x else x - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma clique_arith {h a b g : ℕ} (ha : a ≤ h) (hb : b ≤ h) (hg1 : 1 ≤ g) (hgh : g ≤ h) :
    (a + g) % (h + 1) = b ↔ a = (b + (h + 1) - g) % (h + 1) := by
  rw [mod_eq_ite (by omega), mod_eq_ite (by omega)]
  split_ifs <;> omega

lemma mod_succ_le (x h : ℕ) : x % (h + 1) ≤ h := Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos h))

/-- Nodes `0, …, ⌊d/2⌋` form a clique of `lbGraph n d`. -/
lemma lbGraph_adj_of_le {n : ℕ} {a b : Fin n} (hab : a.val ≠ b.val) (ha : a.val ≤ d / 2)
    (hb : b.val ≤ d / 2) : (lbGraph n d).Adj a b := by
  simp only [lbGraph]; omega

/-- The initial load of the lower bound: `⌊d/2⌋` on each node of the clique `{0, …, ⌊d/2⌋}`,
`0` elsewhere. -/
def cliqueLoad (n d : ℕ) (v : Fin n) : ℕ := if v.val ≤ d / 2 then d / 2 else 0

/-- The adversary's port numbering: at a clique node `v`, a port `j` over which `A` sends a
positive amount at load `⌊d/2⌋` leads to the clique node `(v + portLabel j) mod (⌊d/2⌋ + 1)`. -/
def IsCliquePort {n : ℕ} (A : StatelessAlg d) (port : ∀ v, Fin d ≃ (lbGraph n d).neighborFinset v) :
    Prop :=
  ∀ v : Fin n, v.val ≤ d / 2 → ∀ j, A.send (d / 2) j ≠ 0 →
    ((port v j : Fin n) : ℕ) = (v.val + portLabel (A.send (d / 2)) j) % (d / 2 + 1)

lemma exists_cliquePort {n : ℕ} (hn : Even n) (hdn : d < n) (A : StatelessAlg d) :
    ∃ port : ∀ v, Fin d ≃ (lbGraph n d).neighborFinset v, IsCliquePort A port := by
  have hsum : ∑ j, A.send (d / 2) j ≤ d / 2 := by have := A.conserve (d / 2); omega
  have hm : d / 2 + 1 ≤ n := by omega
  let f : Fin n → Fin d → Fin n := fun v j =>
    ⟨(v.val + portLabel (A.send (d / 2)) j) % (d / 2 + 1),
      lt_of_lt_of_le (Nat.mod_lt _ (Nat.succ_pos _)) hm⟩
  have key : ∀ v : Fin n, ∃ e : Fin d ≃ (lbGraph n d).neighborFinset v, v.val ≤ d / 2 →
      ∀ j, A.send (d / 2) j ≠ 0 →
        ((e j : Fin n) : ℕ) = (v.val + portLabel (A.send (d / 2)) j) % (d / 2 + 1) := by
    intro v
    have hcard : Fintype.card (Fin d) = #((lbGraph n d).neighborFinset v) := by
      rw [Fintype.card_fin, SimpleGraph.card_neighborFinset_eq_degree,
        lbGraph_isRegular hn hdn v]
    by_cases hv : v.val ≤ d / 2
    · have hf1 : (posPorts (A.send (d / 2))).image (f v) ⊆ (lbGraph n d).neighborFinset v := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := mem_image.1 hw
        rw [mem_posPorts] at hj
        have h1 := one_le_portLabel hj
        have h2 := portLabel_le hj
        rw [SimpleGraph.mem_neighborFinset]
        refine lbGraph_adj_of_le ?_ hv (mod_succ_le _ _)
        simp only [f]
        rw [mod_eq_ite (by omega)]
        split_ifs <;> omega
      have hf2 : Set.InjOn (f v) (posPorts (A.send (d / 2))) := by
        intro j hj j' hj' hjj
        simp only [mem_coe, mem_posPorts] at hj hj'
        have h1 := one_le_portLabel hj
        have h2 := portLabel_le hj
        have h1' := one_le_portLabel hj'
        have h2' := portLabel_le hj'
        simp only [f, Fin.ext_iff] at hjj
        apply portLabel_inj hj hj'
        rw [mod_eq_ite (by omega), mod_eq_ite (by omega)] at hjj
        split_ifs at hjj <;> omega
      obtain ⟨e, he⟩ := Finset.exists_equiv_extend_of_card_eq hcard hf1 hf2
      exact ⟨e, fun _ j hj => by rw [he j (mem_posPorts.2 hj)]⟩
    · exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_coe]; exact hcard), fun h => absurd h hv⟩
  choose port hport using key
  exact ⟨port, hport⟩

/-- The clique load vector is a fixed point of `A` under the adversarial port numbering. -/
lemma cliqueLoad_step {n : ℕ} (hdn : d < n) (A : StatelessAlg d)
    (port : ∀ v, Fin d ≃ (lbGraph n d).neighborFinset v) (hp : IsCliquePort A port) (v : Fin n) :
    A.keep (cliqueLoad n d v) + ∑ w ∈ (lbGraph n d).neighborFinset v,
      A.out (lbGraph n d) port w (cliqueLoad n d w) v = cliqueLoad n d v := by
  have hsum := A.conserve (d / 2)
  have hout0 : ∀ w : Fin n, ¬ w.val ≤ d / 2 → ∀ u,
      A.out (lbGraph n d) port w (cliqueLoad n d w) u = 0 := by
    intro w hw u
    simp only [cliqueLoad, hw, ite_false, StatelessAlg.out]
    split_ifs <;> simp [A.send_zero]
  have hout : ∀ w : Fin n, w.val ≤ d / 2 → ∀ u (hu : u ∈ (lbGraph n d).neighborFinset w),
      A.out (lbGraph n d) port w (cliqueLoad n d w) u = A.send (d / 2) ((port w).symm ⟨u, hu⟩) := by
    intro w hw u hu
    simp only [cliqueLoad, hw, ite_true, StatelessAlg.out, hu, dite_true]
  have hsymm : ∀ u w : Fin n, u ∈ (lbGraph n d).neighborFinset w →
      w ∈ (lbGraph n d).neighborFinset u := by
    intro u w h; rw [SimpleGraph.mem_neighborFinset] at h ⊢; exact h.symm
  by_cases hv : v.val ≤ d / 2
  · have hcv : cliqueLoad n d v = d / 2 := by simp [cliqueLoad, hv]
    rw [hcv]
    suffices hs : ∑ w ∈ (lbGraph n d).neighborFinset v,
        A.out (lbGraph n d) port w (cliqueLoad n d w) v = ∑ j, A.send (d / 2) j by
      rw [hs]; exact hsum
    have hsum' : ∑ j, A.send (d / 2) j ≤ d / 2 := by omega
    -- the clique node whose port `j` leads to `v`
    let src : Fin d → Fin n := fun j =>
      ⟨(v.val + (d / 2 + 1) - portLabel (A.send (d / 2)) j) % (d / 2 + 1),
        lt_of_lt_of_le (Nat.mod_lt _ (Nat.succ_pos _)) (by omega)⟩
    have hsrc_le : ∀ j, (src j).val ≤ d / 2 := fun j => mod_succ_le _ _
    have hsrc : ∀ j, A.send (d / 2) j ≠ 0 →
        ((src j).val + portLabel (A.send (d / 2)) j) % (d / 2 + 1) = v.val := fun j hj =>
      (clique_arith (hsrc_le j) hv (one_le_portLabel hj) ((portLabel_le hj).trans hsum')).2 rfl
    have hsrc_mem : ∀ j, A.send (d / 2) j ≠ 0 → src j ∈ (lbGraph n d).neighborFinset v := by
      intro j hj
      have := hsrc j hj
      have h1 := one_le_portLabel hj
      have h2 := (portLabel_le hj).trans hsum'
      have h3 := hsrc_le j
      rw [SimpleGraph.mem_neighborFinset]
      refine lbGraph_adj_of_le ?_ hv h3
      rw [mod_eq_ite (by omega)] at this
      split_ifs at this <;> omega
    symm
    refine Finset.sum_bij_ne_zero (fun j _ _ => src j) (fun j _ hj => hsrc_mem j hj) ?_ ?_ ?_
    · intro j _ hj j' _ hj' hjj
      have h1 := one_le_portLabel hj
      have h2 := (portLabel_le hj).trans hsum'
      have h1' := one_le_portLabel hj'
      have h2' := (portLabel_le hj').trans hsum'
      simp only [src, Fin.ext_iff] at hjj
      apply portLabel_inj hj hj'
      rw [mod_eq_ite (by omega), mod_eq_ite (by omega)] at hjj
      split_ifs at hjj <;> omega
    · intro w hw hne
      have hwc : w.val ≤ d / 2 := by
        by_contra hwc; exact hne (hout0 w hwc v)
      rw [hout w hwc v (hsymm _ _ hw)] at hne
      set i := (port w).symm ⟨v, hsymm _ _ hw⟩ with hi
      refine ⟨i, mem_univ _, hne, ?_⟩
      have hpi := hp w hwc i hne
      rw [hi, Equiv.apply_symm_apply] at hpi
      have h1 := one_le_portLabel hne
      have h2 := (portLabel_le hne).trans hsum'
      exact Fin.ext ((clique_arith hwc hv h1 h2).1 hpi.symm).symm
    · intro j _ hj
      rw [hout (src j) (hsrc_le j) v (hsymm _ _ (hsrc_mem j hj))]
      congr 1
      rw [eq_comm, Equiv.symm_apply_eq]
      ext
      rw [hp _ (hsrc_le j) j hj, hsrc j hj]
  · have hcv : cliqueLoad n d v = 0 := by simp [cliqueLoad, hv]
    rw [hcv, A.keep_zero, zero_add]
    refine sum_eq_zero fun w hw => ?_
    by_cases hwc : w.val ≤ d / 2
    · rw [hout w hwc v (hsymm _ _ hw)]
      by_contra hne
      have hpi := hp w hwc _ hne
      rw [Equiv.apply_symm_apply] at hpi
      have := mod_succ_le (w.val + portLabel (A.send (d / 2)) ((port w).symm ⟨v, hsymm _ _ hw⟩)) (d / 2)
      simp only at hpi
      omega
    · exact hout0 w hwc v

lemma load_cliqueLoad {n : ℕ} (hdn : d < n) (A : StatelessAlg d)
    (port : ∀ v, Fin d ≃ (lbGraph n d).neighborFinset v) (hp : IsCliquePort A port) (t : ℕ) :
    (A.toBalancer (lbGraph n d) port).load (cliqueLoad n d) t = cliqueLoad n d := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [StatelessAlg.load_succ_toBalancer, ih]
    exact cliqueLoad_step hdn A port hp v

end LowerBound

/-- **Theorem 4.2** of Berenbrink et al. (PODC 2015): let `A` be an arbitrary deterministic and
stateless algorithm. For every even `n` (and every `d < n`) there exist a `d`-regular graph on `n`
nodes, a port numbering and an initial load distribution such that `A` never achieves discrepancy
better than `d/3` (the paper's `c·d` with `c = 1/3`). -/
theorem theorem_4_2 (n d : ℕ) (hn : Even n) (hdn : d < n) (A : StatelessAlg d) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧
      ∃ (port : ∀ v, Fin d ≃ G.neighborFinset v) (x₀ : Fin n → ℕ),
        ∀ t, d ≤ 3 * disc ((A.toBalancer G port).load x₀ t) := by
  refine ⟨lbGraph n d, inferInstance, lbGraph_isRegular hn hdn, ?_⟩
  obtain ⟨port, hp⟩ := exists_cliquePort hn hdn A
  refine ⟨port, ?_⟩
  rcases Nat.lt_or_ge (d / 2) 1 with hd | hd
  · -- `d ≤ 1`: one token on one node; `n ∤ 1` since `n ≥ 2`
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact ⟨fun _ => 0, fun _ => Nat.zero_le _⟩
    have hn2 : 2 ≤ n := by obtain ⟨r, rfl⟩ := hn; omega
    refine ⟨fun v => if v = ⟨0, by omega⟩ then 1 else 0, fun t => ?_⟩
    have h1 : 1 ≤ disc ((A.toBalancer (lbGraph n d) port).load
        (fun v => if v = ⟨0, by omega⟩ then 1 else 0) t) := by
      apply one_le_disc_of_not_dvd
      rw [Balancer.sum_load, Finset.sum_ite_eq' univ]
      simp only [mem_univ, ite_true, Fintype.card_fin]
      exact fun h => by have := Nat.le_of_dvd one_pos h; omega
    omega
  · -- `d ≥ 2`: the clique load is a fixed point of discrepancy `⌊d/2⌋ ≥ d/3`
    refine ⟨cliqueLoad n d, fun t => ?_⟩
    rw [load_cliqueLoad hdn A port hp t]
    have := sub_le_disc (cliqueLoad n d) ⟨0, by omega⟩ ⟨d / 2 + 1, by omega⟩
    simp only [cliqueLoad, Nat.zero_le, ite_true, show ¬ d / 2 + 1 ≤ d / 2 by omega, ite_false]
      at this
    omega

/-! ### Non-vacuity -/

/-- A concrete stateless algorithm with `d` ports: send `⌊x/(d+1)⌋` over every port, keep the rest
(a round-fair "send-floor" scheme). -/
def floorAlg (d : ℕ) : StatelessAlg d where
  keep x := x - d * (x / (d + 1))
  send x _ := x / (d + 1)
  conserve x := by
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    have : d * (x / (d + 1)) ≤ x :=
      (Nat.mul_le_mul_right _ (Nat.le_succ d)).trans (Nat.mul_div_le x (d + 1))
    omega

/-- Theorem 4.2 instantiated: on `8` nodes, the floor algorithm with `4` ports stays at
discrepancy `≥ 2` forever on some `4`-regular graph. -/
example : ∃ (G : SimpleGraph (Fin 8)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree 4 ∧
    ∃ (port : ∀ v, Fin 4 ≃ G.neighborFinset v) (x₀ : Fin 8 → ℕ),
      ∀ t, 4 ≤ 3 * disc (((floorAlg 4).toBalancer G port).load x₀ t) :=
  theorem_4_2 8 4 ⟨4, rfl⟩ (by norm_num) (floorAlg 4)

end Podc.DeterministicLoadBalancing
