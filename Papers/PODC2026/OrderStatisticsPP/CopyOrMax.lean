import Papers.PODC2026.OrderStatisticsPP.Fixation
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Copy-or-Max dynamics: geometric fixation law (Theorem 1, Propositions 5 and 6 (⇐))

Weighted population protocol (Section 4.2): in each round a directed edge `(u, v)` is activated
with probability `w u v / W` (`W = ∑ w`); agent `u` then copies `X_v` with probability `p`, and
otherwise sets `X_u ← max(X_u, X_v)`. The standard population protocol on the clique (Section 4.1,
"sample `u, v` u.a.r.", `v = u` allowed) is the case `w ≡ 1`.

Main results:
* `isCirculation_iff_cut` (Lemma 4.6);
* `copyOrMaxW_fixation`, `copyOrMaxW_fixation_injective` (Proposition 6 "if", Theorem 1(2)):
  on a connected circulation, fixation on the `k`-th smallest value has probability
  `(1-p) p^(n-k) / (1-p^n)`;
* `copyOrMax_fixation`, `copyOrMax_fixation_injective` (Proposition 5, Theorem 1(1)).
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]

/-! ### The geometric law -/

/-- The geometric law on ranks `1, …, n`: `π_k = (1-p) p^(n-k) / (1-p^n)`. -/
noncomputable def geomLaw (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := (1 - p) * p ^ (n - k) / (1 - p ^ n)

lemma cumul_eq_sum_range (π : ℕ → ℝ) (m : ℕ) : cumul π m = ∑ j ∈ range m, π (j + 1) := by
  induction m with
  | zero => simp [cumul_zero]
  | succ m ih => rw [cumul_succ, ih, Finset.sum_range_succ]

lemma cumul_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n) :
    cumul (geomLaw n p) n = 1 := by
  rw [cumul_eq_sum_range]
  have hpn : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 hn.ne'
  have h1 : ∑ j ∈ range n, geomLaw n p (j + 1) = ∑ j ∈ range n, (1 - p) * p ^ j / (1 - p ^ n) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    unfold geomLaw
    congr 3
    omega
  rw [h1, ← Finset.sum_div, ← Finset.mul_sum]
  have := geom_sum_mul p n
  rw [div_eq_one_iff_eq (by linarith)]
  linarith

lemma geomLaw_succ_mul {p : ℝ} {m : ℕ} (hm : m + 1 ≤ n) :
    geomLaw n p (m + 1) * p = geomLaw n p m := by
  unfold geomLaw
  have : n - m = (n - (m + 1)) + 1 := by omega
  rw [this, pow_succ]
  ring

lemma geomLaw_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hn : 0 < n) (k : ℕ) :
    0 < geomLaw n p k := by
  unfold geomLaw
  have hpn : p ^ n < 1 := pow_lt_one₀ hp0.le hp1 hn.ne'
  apply div_pos (mul_pos (by linarith) (pow_pos hp0 _)) (by linarith)

/-! ### Circulations (Definition 4.1, Lemma 4.6) -/

/-- A weighted digraph is a circulation if every node has equal in- and out-flow. -/
def IsCirculation (w : Fin n → Fin n → ℝ) : Prop := ∀ v, ∑ u, w u v = ∑ u, w v u

/-- **Lemma 4.6.** A weighted digraph is a circulation iff every cut has equal in- and out-flow. -/
theorem isCirculation_iff_cut (w : Fin n → Fin n → ℝ) :
    IsCirculation w ↔ ∀ S : Finset (Fin n), ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v = ∑ u ∈ S, ∑ v ∈ Sᶜ, w v u := by
  constructor
  · intro h S
    have e1 : ∀ u, ∑ v ∈ Sᶜ, w u v = ∑ v, w u v - ∑ v ∈ S, w u v := fun u => by
      rw [← Finset.sum_compl_add_sum S]; ring
    have e2 : ∀ u, ∑ v ∈ Sᶜ, w v u = ∑ v, w v u - ∑ v ∈ S, w v u := fun u => by
      rw [← Finset.sum_compl_add_sum S]; ring
    simp_rw [e1, e2, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := S) (t := S) (f := fun u v => w v u)]
    congr 1
    exact Finset.sum_congr rfl fun u _ => (h u).symm
  · intro h v
    have := h {v}
    simp only [Finset.sum_singleton] at this
    have e1 : ∑ u, w v u = w v v + ∑ u ∈ {v}ᶜ, w v u := by
      rw [← Finset.sum_compl_add_sum {v}]; simp [add_comm]
    have e2 : ∑ u, w u v = w v v + ∑ u ∈ {v}ᶜ, w u v := by
      rw [← Finset.sum_compl_add_sum {v}]; simp [add_comm]
    rw [e1, e2, this]

/-- The (undirected) support graph of the weights. -/
def supportGraph (w : Fin n → Fin n → ℝ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => 0 < w u v

/-- In a connected circulation, every nonempty proper cut has a positive edge leaving it. -/
lemma exists_out_edge {w : Fin n → Fin n → ℝ} (hw : ∀ u v, 0 ≤ w u v) (hcirc : IsCirculation w)
    (hconn : (supportGraph w).Connected) (S : Finset (Fin n)) {s t : Fin n} (hs : s ∈ S)
    (ht : t ∉ S) : ∃ u ∈ S, ∃ v ∉ S, 0 < w u v := by
  obtain ⟨p⟩ := hconn.preconnected s t
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (S : Set (Fin n)) hs ht
  have hadj := d.adj
  simp only [supportGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with h | h
  · exact ⟨_, hd1, _, hd2, h⟩
  · -- the cut has positive in-flow, hence positive out-flow
    have hin : 0 < ∑ u ∈ S, ∑ v ∈ Sᶜ, w v u :=
      Finset.sum_pos' (fun u _ => Finset.sum_nonneg fun v _ => hw v u)
        ⟨_, hd1, Finset.sum_pos' (fun v _ => hw v _) ⟨_, by simpa using hd2, h⟩⟩
    rw [← (isCirculation_iff_cut w).mp hcirc S] at hin
    obtain ⟨u, hu, hpos⟩ := exists_pos_of_sum_pos' hin
    obtain ⟨v, hv, hpos'⟩ := exists_pos_of_sum_pos' hpos
    exact ⟨u, hu, v, by simpa using hv, hpos'⟩

/-! ### The dynamics -/

/-- Weights of the random choices `(u, v, copy?)`. -/
noncomputable def comμ (w : Fin n → Fin n → ℝ) (p : ℝ) (ω : Fin n × Fin n × Bool) : ℝ :=
  w ω.1 ω.2.1 / (∑ i, ∑ j, w i j) * (if ω.2.2 then p else 1 - p)

/-- The new opinion of the activated agent `ω.1` after sampling `ω.2.1`. -/
def comNew (c : Config n α) (ω : Fin n × Fin n × Bool) : α :=
  if ω.2.2 then c ω.2.1 else max (c ω.1) (c ω.2.1)

/-- **Copy-or-Max dynamics** in the weighted population protocol (Section 4.2). -/
noncomputable def copyOrMaxW (w : Fin n → Fin n → ℝ) (p : ℝ) :
    Matrix (Config n α) (Config n α) ℝ :=
  randomMap (comμ w p) (fun ω c => Function.update c ω.1 (comNew c ω))

/-- **Copy-or-Max dynamics** on the clique (Section 4.1): `u, v` uniform and independent. -/
noncomputable def copyOrMax (n : ℕ) (α : Type*) [LinearOrder α] (p : ℝ) :
    Matrix (Config n α) (Config n α) ℝ :=
  copyOrMaxW (fun _ _ => (1 : ℝ)) p

section Weighted

variable {w : Fin n → Fin n → ℝ} {p : ℝ}

lemma comμ_nonneg (hw : ∀ u v, 0 ≤ w u v) (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Fin n × Fin n × Bool) : 0 ≤ comμ w p ω := by
  unfold comμ
  refine mul_nonneg (div_nonneg (hw _ _) hW.le) ?_
  split_ifs <;> linarith

lemma comμ_sum (hW : 0 < ∑ i, ∑ j, w i j) : ∑ ω, comμ w p ω = 1 := by
  unfold comμ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  simp_rw [← mul_add, add_sub_cancel, mul_one, ← Finset.sum_div]
  exact div_self hW.ne'

lemma copyOrMaxW_mem (hw : ∀ u v, 0 ≤ w u v) (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (copyOrMaxW w p : Matrix (Config n α) _ ℝ) ∈ rowStochastic ℝ _ :=
  randomMap_mem_rowStochastic (comμ_nonneg hw hW hp0 hp1) (comμ_sum hW) _

lemma copyOrMaxW_absorbing (z : α) (s : Config n α) (hs : s ≠ const z) :
    copyOrMaxW w p (const z) s = 0 :=
  randomMap_eq_zero_of_fixed (fun ω => by
    funext v; simp [comNew, const, Function.update_apply]) hs

lemma copyOrMaxW_reach (hn : 0 < n) (hw : ∀ u v, 0 ≤ w u v) (hW : 0 < ∑ i, ∑ j, w i j)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hcirc : IsCirculation w) (hconn : (supportGraph w).Connected)
    (c : Config n α) :
    ∃ z, Relation.ReflTransGen (fun a b => 0 < copyOrMaxW w p a b) c (const z) := by
  refine reach_const_of_step hn _ (fun c M hle hex hlt => ?_) c
  obtain ⟨t, ht⟩ := hex
  obtain ⟨s, hs⟩ := hlt
  obtain ⟨u, hu, v, hv, hpos⟩ := exists_out_edge hw hcirc hconn (univ.filter fun u => c u < M)
    (s := s) (t := t) (by simp [hs]) (by simp [ht])
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hu hv
  refine ⟨u, hu, ?_⟩
  have hcv : c v = M := le_antisymm (hle v) hv
  have := randomMap_pos (comμ_nonneg hw hW hp0.le hp1)
    (fun ω (c : Config n α) => Function.update c ω.1 (comNew c ω))
    (ω := (u, v, true)) (by unfold comμ; simp only [ite_true]; positivity) c
  unfold copyOrMaxW
  simpa [comNew, hcv] using this

/-- Up- and down-probabilities of Copy-or-Max for a lower set. -/
lemma com_upMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    upMass (comμ w p) (fun ω _ => ω.1) (fun ω c => comNew c ω) D c =
      p / (∑ i, ∑ j, w i j) * ∑ u, ∑ v, w u v * ((1 - ind D (c u)) * ind D (c v)) := by
  unfold upMass comμ comNew
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    ind_max hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rcases ind_zero_or_one D (c u) with h | h <;> rw [h] <;> ring

lemma com_downMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    downMass (comμ w p) (fun ω _ => ω.1) (fun ω c => comNew c ω) D c =
      1 / (∑ i, ∑ j, w i j) * ∑ u, ∑ v, w u v * (ind D (c u) * (1 - ind D (c v))) := by
  unfold downMass comμ comNew
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    ind_max hD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rcases ind_zero_or_one D (c u) with h | h <;> rw [h] <;> ring

/-- On a circulation, the flow into and out of the agents holding opinions in `D` coincide. -/
lemma circ_flow (hcirc : IsCirculation w) (I : Fin n → ℝ) :
    ∑ u, ∑ v, w u v * ((1 - I u) * I v) = ∑ u, ∑ v, w u v * (I u * (1 - I v)) := by
  have e0 : ∑ u, ∑ v, w u v * I v = ∑ v, I v * ∑ u, w u v := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
  have e1 : ∑ u, ∑ v, w u v * ((1 - I u) * I v) =
      ∑ v, I v * ∑ u, w u v - ∑ u, ∑ v, w u v * (I u * I v) := by
    rw [← e0, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have e2 : ∑ u, ∑ v, w u v * (I u * (1 - I v)) =
      ∑ u, I u * ∑ v, w u v - ∑ u, ∑ v, w u v * (I u * I v) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2]
  congr 1
  exact Finset.sum_congr rfl fun v _ => by rw [hcirc v]

lemma copyOrMaxW_harmonic (hW : 0 < ∑ i, ∑ j, w i j) (hcirc : IsCirculation w) (D : Set α)
    (hD : IsLowerSet D) :
    copyOrMaxW w p *ᵥ (fun c : Config n α => cumul (geomLaw n p) (cnt D c)) =
      fun c => cumul (geomLaw n p) (cnt D c) := by
  refine harmonic_of_balance (comμ w p) (comμ_sum hW) (fun ω _ => ω.1)
    (fun ω c => comNew c ω) _ D ?_
  · intro c
    rw [com_upMass hD, com_downMass hD, circ_flow hcirc]
    set X := ∑ u, ∑ v, w u v * (ind D (c u) * (1 - ind D (c v)))
    by_cases h0 : cnt D c = 0
    · have : X = 0 := Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
        rw [ind_not_mem ((cnt_eq_zero_iff D c).mp h0 u)]; ring
      rw [this]; ring
    by_cases hn' : cnt D c = n
    · have : X = 0 := Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => by
        rw [ind_mem ((cnt_eq_n_iff D c).mp hn' v)]; ring
      rw [this]; ring
    have hlt : cnt D c + 1 ≤ n := by have := cnt_le D c; omega
    rw [← geomLaw_succ_mul (p := p) hlt]
    ring

/-- **Proposition 6 (⇐), Theorem 1(2).** Copy-or-Max on a connected circulation with nonnegative
weights: from any configuration `c`, the probability of fixation on the opinion `x` is the sum of
the geometric weights `(1-p) p^(n-k) / (1-p^n)` over the ranks `k` of `x` in `c`, i.e. over
`#{u | c u < x} < k ≤ #{u | c u ≤ x}` (with ties this is the paper's "summing up the fixation
probabilities of identical values"). -/
theorem copyOrMaxW_fixation (hn : 0 < n) (hw : ∀ u v, 0 ≤ w u v) (hW : 0 < ∑ i, ∑ j, w i j)
    (hp0 : 0 < p) (hp1 : p < 1) (hcirc : IsCirculation w) (hconn : (supportGraph w).Connected)
    (c : Config n α) (x : α) :
    Tendsto (fun t => (copyOrMaxW w p ^ t) c (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), geomLaw n p k)) :=
  fixation_of_harmonic (copyOrMaxW_mem hw hW hp0.le hp1.le) hn _ (cumul_geomLaw hp0 hp1 hn)
    copyOrMaxW_absorbing (copyOrMaxW_reach hn hw hW hp0 hp1.le hcirc hconn)
    (fun D hD => copyOrMaxW_harmonic hW hcirc D hD) c x

/-- **Proposition 6 (⇐), Theorem 1(2)**, distinct initial opinions: fixation on the `k`-th
smallest initial opinion `x_(k)` has probability `(1-p) p^(n-k) / (1-p^n)`. -/
theorem copyOrMaxW_fixation_injective (hn : 0 < n) (hw : ∀ u v, 0 ≤ w u v)
    (hW : 0 < ∑ i, ∑ j, w i j) (hp0 : 0 < p) (hp1 : p < 1) (hcirc : IsCirculation w)
    (hconn : (supportGraph w).Connected) (c : Config n α) (hc : Function.Injective c)
    (u : Fin n) :
    Tendsto (fun t => (copyOrMaxW w p ^ t) c (const (c u))) atTop
      (𝓝 ((1 - p) * p ^ (n - rank c (c u)) / (1 - p ^ n))) :=
  fixation_of_harmonic_injective (copyOrMaxW_mem hw hW hp0.le hp1.le) hn _
    (cumul_geomLaw hp0 hp1 hn) copyOrMaxW_absorbing
    (copyOrMaxW_reach hn hw hW hp0 hp1.le hcirc hconn)
    (fun D hD => copyOrMaxW_harmonic hW hcirc D hD) c hc u

end Weighted

section Clique

variable {p : ℝ}

lemma clique_isCirculation : IsCirculation (fun _ _ : Fin n => (1 : ℝ)) := fun _ => rfl

lemma clique_connected (hn : 0 < n) : (supportGraph (fun _ _ : Fin n => (1 : ℝ))).Connected := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : supportGraph (fun _ _ : Fin n => (1 : ℝ)) = ⊤ := by
    ext u v
    simp [supportGraph, SimpleGraph.fromRel_adj]
  rw [this]
  exact SimpleGraph.connected_top

lemma clique_W_pos (hn : 0 < n) : 0 < ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
  simp [hn]

/-- **Proposition 5 / Theorem 1(1)** (general initial configurations, ties summed). -/
theorem copyOrMax_fixation (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1) (c : Config n α) (x : α) :
    Tendsto (fun t => (copyOrMax n α p ^ t) c (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), geomLaw n p k)) :=
  copyOrMaxW_fixation hn (fun _ _ => zero_le_one) (clique_W_pos hn) hp0 hp1 clique_isCirculation
    (clique_connected hn) c x

/-- **Proposition 5 / Theorem 1(1).** The Copy-or-Max dynamics on the clique converges to the
`k`-th smallest initial value `x_(k)` with probability `(1-p) p^(n-k) / (1-p^n)`
(distinct initial values; `rank c (c u) = k` iff `c u = x_(k)`). -/
theorem copyOrMax_fixation_injective (hn : 0 < n) (hp0 : 0 < p) (hp1 : p < 1)
    (c : Config n α) (hc : Function.Injective c) (u : Fin n) :
    Tendsto (fun t => (copyOrMax n α p ^ t) c (const (c u))) atTop
      (𝓝 ((1 - p) * p ^ (n - rank c (c u)) / (1 - p ^ n))) :=
  copyOrMaxW_fixation_injective hn (fun _ _ => zero_le_one) (clique_W_pos hn) hp0 hp1
    clique_isCirculation (clique_connected hn) c hc u

end Clique

end OrderStatisticsPP
