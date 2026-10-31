import Cslib.Probability.Finite.Uniform
import Mathlib

/-!
# Lemma 4.7 / Theorem 1.2 (size bound) are false for `Sampler` as written

In `Cluster_j` (Pseudocode 2, lines 4–6) every node `v` draws, **in every trial**,
`s_j = c² n^{2^j δ + ε} log³ n` edges uniformly at random (with replacement) from `X_v`, and keeps one
edge per queried neighbour in `F_v ⊆ S`. The threshold test `|F'_v| < c n^{2^j δ} log n` is made only
*between* trials, so a single trial may add up to `s_j` edges. The proof of Lemma 4.7 counts only
`O(n^{2^j δ} log³ n)` edges per trial and node, dropping the factor `n^ε`.

At level `0` the input `G_0 = G` is simple, all `n` nodes run the first trial (it is always executed:
`i = 1 ≤ 2h`, `F'_v = ∅`, `X_v = E(v) ≠ ∅`), and every sampled edge is kept in `F_v` (each neighbour has a
single edge). We show: **if every degree is at least `s`, then with probability at least `1/8` the
first trial of level `0` alone puts at least `n·s/8` edges into `S`** (`first_trial_large`).

With `k = 1`, `h = 2` (`δ = 1/3`, `ε = 1/2`) and `G = K_n`, this is `≳ n^{11/6}` edges with
probability `≥ 1/8`, while Theorem 1.2 / Lemma 4.7 claim `|S| = Õ(n^{1+δ}) = Õ(n^{4/3})` w.h.p.
(`theorem_1_2_size_false`).
-/

namespace Podc.LocalMessageReduction

open Finset Cslib.Probability

section Counting

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

lemma card_filter_forall_ne (s : ℕ) (y : Y) :
    #(univ.filter fun f : Fin s → Y => ∀ i, f i ≠ y) = (Fintype.card Y - 1) ^ s := by
  have : (univ.filter fun f : Fin s → Y => ∀ i, f i ≠ y) = Fintype.piFinset fun _ => univ.erase y := by
    ext f; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp [Finset.card_erase_of_mem]

/-- `∑_f |range f| = m (m^s − (m−1)^s)` over all `f : Fin s → Y`, `m = |Y|`. -/
lemma sum_card_image (s : ℕ) :
    ∑ f : Fin s → Y, #(univ.image f) =
      Fintype.card Y * (Fintype.card Y ^ s - (Fintype.card Y - 1) ^ s) := by
  have h1 : ∀ f : Fin s → Y, #(univ.image f) = ∑ y : Y, if ∃ i, f i = y then 1 else 0 := by
    intro f
    rw [← Finset.card_filter]
    congr 1
    ext y; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y : Y, (∑ f : Fin s → Y, if ∃ i, f i = y then 1 else 0) =
      Fintype.card Y ^ s - (Fintype.card Y - 1) ^ s := by
    intro y
    rw [← Finset.card_filter, ← card_filter_forall_ne s y]
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin s → Y))) (fun f => ∃ i, f i = y)
    simp only [card_univ, Fintype.card_fun, Fintype.card_fin, not_exists, ne_eq] at this ⊢
    omega
  simp_rw [h2]
  simp

/-- `(m − 1)^s (m + s) ≤ m^{s+1}` for real `m ≥ 1`. -/
lemma pow_sub_one_mul_le (m : ℝ) (hm : 1 ≤ m) (s : ℕ) : (m - 1) ^ s * (m + s) ≤ m ^ (s + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h0 : 0 ≤ (m - 1) ^ s := pow_nonneg (by linarith) _
    have key : (m - 1) * (m + (s + 1)) ≤ m * (m + s) := by nlinarith
    calc (m - 1) ^ (s + 1) * (m + ((s + 1 : ℕ) : ℝ))
        = (m - 1) ^ s * ((m - 1) * (m + (s + 1))) := by push_cast; ring
      _ ≤ (m - 1) ^ s * (m * (m + s)) := mul_le_mul_of_nonneg_left key h0
      _ = m * ((m - 1) ^ s * (m + s)) := by ring
      _ ≤ m * m ^ (s + 1) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = m ^ (s + 1 + 1) := by ring

/-- **Expected number of distinct values.** `s` uniform samples (with replacement) from a set of
`m ≥ s` elements hit at least `s/2` distinct elements on average:
`s · m^s ≤ 2 ∑_f |range f|`. -/
lemma mul_pow_le_two_mul_sum_card_image (s : ℕ) (hs : s ≤ Fintype.card Y) :
    (s : ℝ) * (Fintype.card Y : ℝ) ^ s ≤ 2 * ∑ f : Fin s → Y, (#(univ.image f) : ℝ) := by
  set m := Fintype.card Y with hm
  have hsum : ∑ f : Fin s → Y, (#(univ.image f) : ℝ) = m * ((m : ℝ) ^ s - ((m : ℝ) - 1) ^ s) := by
    rw [← Nat.cast_sum, sum_card_image, ← hm]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; simp
    · have : (m - 1) ^ s ≤ m ^ s := Nat.pow_le_pow_left (Nat.sub_le _ _) _
      rw [Nat.cast_mul, Nat.cast_sub this, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hpos,
        Nat.cast_one]
  rw [hsum]
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0; simp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hspos.trans_le hs
  have key := pow_sub_one_mul_le (m : ℝ) hm1 s
  have hsm : (s : ℝ) ≤ m := by exact_mod_cast hs
  have hpos : (0 : ℝ) < m + s := by positivity
  have hms : (0 : ℝ) ≤ (m : ℝ) ^ s := by positivity
  -- multiply the goal by `m + s > 0`
  have : (s : ℝ) * m ^ s * (m + s) ≤ 2 * (m * (m ^ s - (m - 1) ^ s)) * (m + s) := by
    have e : 2 * (m * ((m : ℝ) ^ s - (m - 1) ^ s)) * (m + s) =
        2 * m * m ^ s * (m + s) - 2 * m * ((m - 1) ^ s * (m + s)) := by ring
    rw [e, pow_succ] at *
    nlinarith [mul_nonneg hms (sub_nonneg.mpr hsm), mul_nonneg hms (Nat.cast_nonneg s : (0:ℝ) ≤ s)]
  exact le_of_mul_le_mul_right this hpos

end Counting

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- Summing a function of one coordinate over a product space. -/
lemma card_mul_sum_apply (v : ι) (g : β v → ℝ) :
    (Fintype.card (β v) : ℝ) * ∑ ω : (∀ i, β i), g (ω v) =
      (Fintype.card (∀ i, β i) : ℝ) * ∑ b, g b := by
  let e := Equiv.piSplitAt v β
  have h1 : ∑ ω : (∀ i, β i), g (ω v) = ∑ p : β v × (∀ j : {j // j ≠ v}, β j), g p.1 :=
    Fintype.sum_equiv e _ _ (fun ω => rfl)
  rw [h1, Fintype.sum_prod_type, Fintype.card_congr e, Fintype.card_prod]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  ring

end Pi

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The sample space of the first trial of `Cluster_0`: every node `v` draws `s` edges of `E(v)`
uniformly and independently with replacement (an edge `{v, u}` is identified with the neighbour
`u`). The uniform distribution on this finite type is the distribution of the trial. -/
abbrev FirstTrial (s : ℕ) := (v : V) → Fin s → G.neighborSet v

/-- The query edges of the first trial: `⋃_v {{v, ω_v(i)} | i < s}`. In the simple graph `G_0`, all
of them are kept in the sets `F_v` (line 11 of Pseudocode 2), hence end up in the output `S`. -/
def queryEdges {s : ℕ} (ω : FirstTrial G s) : Finset (Sym2 V) :=
  ((univ : Finset V).sigma fun v => univ.image fun i => (ω v i : V)).image fun p => s(p.1, p.2)

omit [DecidableRel G.Adj] in
lemma mem_queryEdges {s : ℕ} (ω : FirstTrial G s) (e : Sym2 V) :
    e ∈ queryEdges G ω ↔ ∃ v i, e = s(v, (ω v i : V)) := by
  simp only [queryEdges, mem_image, mem_sigma, mem_univ, true_and, Sigma.exists]
  constructor
  · rintro ⟨v, u, ⟨i, rfl⟩, rfl⟩; exact ⟨v, i, rfl⟩
  · rintro ⟨v, i, rfl⟩; exact ⟨v, _, ⟨i, rfl⟩, rfl⟩

omit [DecidableRel G.Adj] in
/-- Each node contributes at most `s` query edges. -/
lemma card_queryEdges_le {s : ℕ} (ω : FirstTrial G s) :
    #(queryEdges G ω) ≤ Fintype.card V * s := by
  unfold queryEdges
  refine card_image_le.trans ?_
  rw [card_sigma]
  calc ∑ v, #(univ.image fun i => (ω v i : V)) ≤ ∑ _v : V, s :=
        sum_le_sum fun v _ => card_image_le.trans (by simp)
    _ = Fintype.card V * s := by simp

omit [DecidableRel G.Adj] in
/-- Each unordered edge is counted at most twice by the ordered pairs `(v, u)`. -/
lemma sum_card_le_two_mul_card_queryEdges {s : ℕ} (ω : FirstTrial G s) :
    ∑ v, #(univ.image fun i => (ω v i : V)) ≤ 2 * #(queryEdges G ω) := by
  rw [← card_sigma]
  apply card_le_mul_card_image _ 2
  intro e _
  induction e using Sym2.inductionOn with
  | hf a b =>
  refine (card_le_card (t := {⟨a, b⟩, ⟨b, a⟩}) ?_).trans card_le_two
  rintro ⟨x, y⟩ hp
  simp only [mem_filter, Sym2.eq_iff] at hp
  rcases hp.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Expected size: `n·s/4 ≤ E|queryEdges|`, in counting form. -/
lemma sum_card_queryEdges_ge (s : ℕ) (hs : ∀ v, s ≤ G.degree v) :
    (Fintype.card V : ℝ) * s * Fintype.card (FirstTrial G s) ≤
      4 * ∑ ω : FirstTrial G s, (#(queryEdges G ω) : ℝ) := by
  have hv : ∀ v : V, (s : ℝ) * Fintype.card (FirstTrial G s) ≤
      2 * ∑ ω : FirstTrial G s, (#(univ.image fun i => (ω v i : V)) : ℝ) := by
    intro v
    have hdeg : s ≤ Fintype.card (G.neighborSet v) := by
      rw [SimpleGraph.card_neighborSet_eq_degree]; exact hs v
    have h1 := mul_pow_le_two_mul_sum_card_image (Y := G.neighborSet v) s hdeg
    have h2 := card_mul_sum_apply (β := fun v => Fin s → G.neighborSet v) v
      (fun f => (#(univ.image fun i => (f i : V)) : ℝ))
    have himg : ∀ f : Fin s → G.neighborSet v,
        #(univ.image fun i => (f i : V)) = #(univ.image f) := by
      intro f
      rw [show (fun i => (f i : V)) = Subtype.val ∘ f from rfl, ← Finset.image_image,
        card_image_of_injective _ Subtype.val_injective]
    simp only [himg] at h2 ⊢
    have hc : (Fintype.card (Fin s → G.neighborSet v) : ℝ) =
        (Fintype.card (G.neighborSet v) : ℝ) ^ s := by simp
    have hpos : (0 : ℝ) ≤ Fintype.card (FirstTrial G s) := by positivity
    have h0 : 0 < Fintype.card (Fin s → G.neighborSet v) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      rcases Nat.eq_zero_or_pos s with hs0 | hs0
      · simp [hs0]
      · exact pow_pos (lt_of_lt_of_le hs0 hdeg) _
    have h0' : (0 : ℝ) < Fintype.card (Fin s → G.neighborSet v) := by exact_mod_cast h0
    rw [← mul_le_mul_iff_of_pos_left h0']
    calc (Fintype.card (Fin s → G.neighborSet v) : ℝ) * (s * Fintype.card (FirstTrial G s))
        = Fintype.card (FirstTrial G s) * (s * (Fintype.card (G.neighborSet v) : ℝ) ^ s) := by
          rw [hc]; ring
      _ ≤ Fintype.card (FirstTrial G s) *
            (2 * ∑ f : Fin s → G.neighborSet v, (#(univ.image f) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hpos
      _ = 2 * (Fintype.card (Fin s → G.neighborSet v) *
            ∑ ω : FirstTrial G s, (#(univ.image (ω v)) : ℝ)) := by rw [h2]; ring
      _ = _ := by ring
  calc (Fintype.card V : ℝ) * s * Fintype.card (FirstTrial G s)
      = ∑ v : V, (s : ℝ) * Fintype.card (FirstTrial G s) := by simp; ring
    _ ≤ ∑ v : V, 2 * ∑ ω : FirstTrial G s, (#(univ.image fun i => (ω v i : V)) : ℝ) :=
        sum_le_sum fun v _ => hv v
    _ = 2 * ∑ ω : FirstTrial G s, ((∑ v, #(univ.image fun i => (ω v i : V)) : ℕ) : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_comm]; push_cast; rfl
    _ ≤ 2 * ∑ ω : FirstTrial G s, ((2 * #(queryEdges G ω) : ℕ) : ℝ) := by
        gcongr with ω
        exact_mod_cast sum_card_le_two_mul_card_queryEdges G ω
    _ = 4 * ∑ ω : FirstTrial G s, (#(queryEdges G ω) : ℝ) := by
        push_cast; rw [← Finset.mul_sum]; ring

/-- **The first trial of `Cluster_0` alone is too large.** If every node has degree at least
`s ≥ 1`, where `s` is the number of edges sampled per node and trial, then with probability at least
`1/8` the query edges of the first trial at level `0` (all of which belong to the output `S`) number
at least `n·s/8`. -/
theorem first_trial_large [Nonempty V] (s : ℕ) (hs1 : 1 ≤ s) (hs : ∀ v, s ≤ G.degree v) :
    1 / 8 ≤ uprob fun ω : FirstTrial G s =>
      (Fintype.card V : ℝ) * s / 8 ≤ #(queryEdges G ω) := by
  classical
  set n := Fintype.card V
  set N := Fintype.card (FirstTrial G s)
  set A := univ.filter fun ω : FirstTrial G s => (n : ℝ) * s / 8 ≤ #(queryEdges G ω)
  rw [uprob_eq_card_filter]
  -- reverse Markov
  have hsum := sum_card_queryEdges_ge G s hs
  have hsplit : ∑ ω : FirstTrial G s, (#(queryEdges G ω) : ℝ) ≤
      N * ((n : ℝ) * s / 8) + #A * ((n : ℝ) * s) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ
      (fun ω : FirstTrial G s => (n : ℝ) * s / 8 ≤ #(queryEdges G ω))]
    have hA : ∑ ω ∈ A, (#(queryEdges G ω) : ℝ) ≤ #A * ((n : ℝ) * s) := by
      rw [← nsmul_eq_mul]
      apply sum_le_card_nsmul
      intro ω _
      exact_mod_cast card_queryEdges_le G ω
    have hB : ∑ ω ∈ univ.filter (fun ω : FirstTrial G s => ¬ (n : ℝ) * s / 8 ≤ #(queryEdges G ω)),
        (#(queryEdges G ω) : ℝ) ≤ N * ((n : ℝ) * s / 8) := by
      calc _ ≤ ∑ ω ∈ univ.filter (fun ω : FirstTrial G s => ¬ (n : ℝ) * s / 8 ≤
              #(queryEdges G ω)), ((n : ℝ) * s / 8) :=
            sum_le_sum fun ω hω => (not_le.mp (mem_filter.mp hω).2).le
        _ ≤ ∑ ω : FirstTrial G s, ((n : ℝ) * s / 8) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
        _ = N * ((n : ℝ) * s / 8) := by simp [N]
    linarith
  have hn : 0 < n := Fintype.card_pos
  have hN : 0 < N := by
    simp only [N, Fintype.card_pi, SimpleGraph.card_neighborSet_eq_degree]
    exact Finset.prod_pos fun v _ => Finset.prod_pos fun _ _ => lt_of_lt_of_le hs1 (hs v)
  have hns : (0 : ℝ) < n * s := by positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hN']
  nlinarith

end Graph

section Asymptotics

open Filter Real Asymptotics

/-- The number of edges sampled per node in each trial of `Cluster_0` for `k = 1`, `h = 2`
(`δ = 1/(2^{k+1} − 1) = 1/3`, `ε = 1/h = 1/2`): `⌈c² n^{δ + ε} log³ n⌉`. -/
noncomputable def samples (c : ℝ) (n : ℕ) : ℕ := ⌈c ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3 + 1 / 2) * log n ^ 3⌉₊

/-- Eventually `1 ≤ samples c n ≤ n − 1` and `n · samples c n / 8 > C n^{4/3} (log n)^D`. -/
lemma samples_eventually (c C D : ℝ) (hc : 1 ≤ c) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ samples c n ∧ samples c n ≤ n - 1 ∧
      C * (n : ℝ) ^ ((4 : ℝ) / 3) * log n ^ D < (n : ℝ) * samples c n / 8 := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `log³ n = o(n^{1/6})` and `log^D n = o(n^{1/2})`
  have h3 := ((isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1 / 6)).comp_tendsto hn)
  have hD := ((isLittleO_log_rpow_rpow_atTop D (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hn)
  have e3 := h3.bound (c := 1 / (4 * c ^ 2)) (by positivity)
  have eD := hD.bound (c := 1 / (16 * (|C| + 1))) (by positivity)
  filter_upwards [e3, eD, eventually_ge_atTop 16] with n h3n hDn hn16
  simp only [Function.comp, norm_eq_abs] at h3n hDn
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 1 ≤ log n := by
    rw [le_log_iff_exp_le hnpos]
    exact (exp_one_lt_d9.le.trans (by norm_num)).trans hn'
  have hlog0 : 0 < log n := by linarith
  have hl3 : log n ^ (3 : ℝ) = log n ^ 3 := by exact_mod_cast rpow_natCast (log n) 3
  rw [abs_of_pos (rpow_pos_of_pos hlog0 _), abs_of_pos (rpow_pos_of_pos hnpos _)] at h3n hDn
  rw [hl3] at h3n
  have hsplit : (n : ℝ) ^ ((1 : ℝ) / 3 + 1 / 2) = n ^ (1 - (1 : ℝ) / 6) := by norm_num
  have hn1 : (n : ℝ) ^ (1 - (1 : ℝ) / 6) * n ^ ((1 : ℝ) / 6) = n := by
    rw [← rpow_add hnpos]; norm_num
  have hpos16 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := rpow_pos_of_pos hnpos _
  have hpos56 : 0 < (n : ℝ) ^ (1 - (1 : ℝ) / 6) := rpow_pos_of_pos hnpos _
  set x := c ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 3 + 1 / 2) * log n ^ 3 with hx
  -- `x ≤ n / 4`
  have hxle : x ≤ n / 4 := by
    rw [hx, hsplit]
    have hc2 : 0 < c ^ 2 := by positivity
    calc c ^ 2 * (n : ℝ) ^ (1 - (1 : ℝ) / 6) * log n ^ 3
        ≤ c ^ 2 * (n : ℝ) ^ (1 - (1 : ℝ) / 6) * (1 / (4 * c ^ 2) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
          gcongr
      _ = ((n : ℝ) ^ (1 - (1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 6)) / 4 := by field_simp
      _ = n / 4 := by rw [hn1]
  -- `x ≥ n^{5/6} ≥ 1`
  have hxge : (n : ℝ) ^ (1 - (1 : ℝ) / 6) ≤ x := by
    rw [hx, hsplit]
    have : 1 ≤ c ^ 2 * log n ^ 3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc) (one_le_pow₀ hlog)
    nlinarith
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (1 - (1 : ℝ) / 6) := one_le_rpow (by linarith) (by norm_num)
  have hs_ge : x ≤ (samples c n : ℝ) := Nat.le_ceil x
  have hs_le : (samples c n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (hone.trans hxge).trans hs_ge
  · have : (samples c n : ℝ) ≤ n - 1 := by linarith
    have h1n : 1 ≤ n := by omega
    exact_mod_cast (show (samples c n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) by push_cast [h1n]; linarith)
  · -- `C n^{4/3} log^D n ≤ |C| n^{4/3} n^{1/2} / (16(|C|+1)) < n^{11/6} / 8 ≤ n s / 8`
    have hlD : log n ^ D ≤ 1 / (16 * (|C| + 1)) * n ^ ((1 : ℝ) / 2) := hDn
    have hlD0 : 0 < log n ^ D := rpow_pos_of_pos hlog0 _
    have h43 : (0 : ℝ) < n ^ ((4 : ℝ) / 3) := rpow_pos_of_pos hnpos _
    have hprod : (n : ℝ) ^ ((4 : ℝ) / 3) * n ^ ((1 : ℝ) / 2) = n * n ^ (1 - (1 : ℝ) / 6) := by
      rw [← rpow_add hnpos]
      conv_rhs => rw [show (n : ℝ) * n ^ (1 - (1 : ℝ) / 6) = n ^ (1 : ℝ) * n ^ (1 - (1 : ℝ) / 6) by
        rw [rpow_one]]
      rw [← rpow_add hnpos]; norm_num
    calc C * (n : ℝ) ^ ((4 : ℝ) / 3) * log n ^ D
        ≤ |C| * n ^ ((4 : ℝ) / 3) * log n ^ D := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * n ^ ((4 : ℝ) / 3) * (1 / (16 * (|C| + 1)) * n ^ ((1 : ℝ) / 2)) := by gcongr
      _ = |C| / (16 * (|C| + 1)) * (n * n ^ (1 - (1 : ℝ) / 6)) := by rw [← hprod]; ring
      _ < 1 / 8 * (n * n ^ (1 - (1 : ℝ) / 6)) := by
          have hpos : 0 < (n : ℝ) * n ^ (1 - (1 : ℝ) / 6) := by positivity
          apply mul_lt_mul_of_pos_right _ hpos
          rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg C]
      _ ≤ 1 / 8 * (n * x) := by gcongr
      _ ≤ (n : ℝ) * samples c n / 8 := by
          rw [one_div_mul_eq_div]; gcongr

/-- **Theorem 1.2 / Lemma 4.7 (size bound) are false as stated.** Take `k = 1`, `h = 2` (allowed for
`n ≥ 16`: `1 ≤ k ≤ log log n`, `0 ≤ h ≤ log n`), so `δ = 1/3`, `ε = 1/2`, any constant `c ≥ 1`, and
the complete graph `K_n`. The first trial of `Cluster_0` makes every node sample
`⌈c² n^{δ+ε} log³ n⌉` edges, all of which are kept in `S`. For every `C` and `D`, for all large `n`,
with probability at least `1/8` these query edges alone are more than `C · n^{1+δ} · log^D n`. Hence
`|S| = Õ(n^{1+δ}) = Õ(n^{4/3})` does not hold w.h.p. (it fails with probability `≥ 1/8`). -/
theorem theorem_1_2_size_false (c C D : ℝ) (hc : 1 ≤ c) :
    ∀ᶠ n : ℕ in atTop, 1 / 8 ≤ uprob fun ω : FirstTrial (⊤ : SimpleGraph (Fin n)) (samples c n) =>
      C * (n : ℝ) ^ ((4 : ℝ) / 3) * log n ^ D < #(queryEdges ⊤ ω) := by
  filter_upwards [samples_eventually c C D hc, eventually_ge_atTop 1] with n ⟨h1, hle, hlt⟩ hn1
  have : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hdeg : ∀ v : Fin n, samples c n ≤ (⊤ : SimpleGraph (Fin n)).degree v := by
    intro v; rw [(SimpleGraph.IsRegularOfDegree.top (V := Fin n)).degree_eq v, Fintype.card_fin]; exact hle
  refine (first_trial_large (⊤ : SimpleGraph (Fin n)) (samples c n) h1 hdeg).trans
    (uprob_mono fun ω hω => ?_)
  simp only [Fintype.card_fin] at hω
  exact hlt.trans_le hω

end Asymptotics

end Podc.LocalMessageReduction
