import Papers.PODC2015.DeterministicLoadBalancing.Model

/-!
# Observation 3.2: `SEND([x/d⁺])` is a good `s`-balancer exactly for `s ≤ ⌈d⁺/2⌉ − d`

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, PODC 2015 (arXiv:1404.4344v4),
Observations 2.2 and 3.2.

`SEND([x/d⁺])`: a node with load `x` sends `[x/d⁺]` (`x/d⁺` rounded to the nearest integer, halves
rounded up) over each original edge and keeps the rest on its `d◦ ≥ d` self-loops (`d⁺ = d + d◦`).

Observation 3.2 claims that it is a good `(d⁺ − 2d)`-balancer for `d⁺ > 2d`. This is false as soon
as `d◦ ≥ d + 2`: when `x/d⁺` is rounded *up*, the `d` original edges take `d` of the
`e = x mod d⁺` extra tokens, and only `e − d` self-loops receive `⌈x/d⁺⌉`; for the smallest such
`e = ⌈d⁺/2⌉` this is `⌈d⁺/2⌉ − d < min{d⁺ − 2d, e}`. Smallest counterexample: `d = 1`, `d◦ = 4`,
`x = 3`: one token goes to the original edge, the four self-loops share two tokens, so only two of
them receive `⌈3/5⌉ = 1`, but `min{s, e} = min{3, 3} = 3` are required.

We prove the exact characterisation (`sendRound_isGood_iff`): for a `d`-regular graph with
`d < d◦`, `SEND([x/d⁺])` is a good `s`-balancer iff `1 ≤ s ≤ ⌈d⁺/2⌉ − d`. Since
`⌈d⁺/2⌉ − d ≥ (d◦ − d)/2`, the applications in Table 1 (`s = Ω(d)` when `d⁺ ≥ 3d`) survive.
We also prove the first part of Observation 2.2 for this algorithm (it is cumulatively `0`-fair).
-/

open Finset

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-- `[x/D]`: `x/D` rounded to the nearest integer (halves rounded up). -/
def roundDiv (x D : ℕ) : ℕ := (2 * x + D) / (2 * D)

lemma roundDiv_eq (x D : ℕ) (hD : 0 < D) :
    roundDiv x D = x / D + if D ≤ 2 * (x % D) then 1 else 0 := by
  unfold roundDiv
  have h1 := Nat.div_add_mod x D
  have h2 := Nat.mod_lt x hD
  have he : 2 * x + D = (2 * (x % D) + D) + 2 * D * (x / D) := by
    rw [mul_assoc]; omega
  rw [he, Nat.add_mul_div_left _ _ (by omega)]
  split_ifs with h
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    all_goals omega
  · rw [Nat.div_eq_of_lt (by omega)]
    all_goals omega

section SendRound

variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma degree_mul_roundDiv_le (dl : ℕ) (hdl : ∀ v, G.degree v ≤ dl) (v : V) (x : ℕ) :
    G.degree v * roundDiv x (G.degree v + dl) ≤ x := by
  rcases Nat.eq_zero_or_pos (G.degree v + dl) with h0 | hD
  · simp [show G.degree v = 0 by omega]
  rw [roundDiv_eq _ _ hD]
  have h1 := Nat.div_add_mod x (G.degree v + dl)
  have h3 := hdl v
  set q := x / (G.degree v + dl)
  set e := x % (G.degree v + dl)
  have : G.degree v * q ≤ (G.degree v + dl) * q := Nat.mul_le_mul_right _ (by omega)
  split_ifs with h
  · rw [Nat.mul_add, mul_one]; omega
  · rw [add_zero]; omega

/-- The stateless algorithm `SEND([x/d⁺])` with `dl` self-loops per node (`deg v ≤ dl`). -/
def sendRound (dl : ℕ) (hdl : ∀ v, G.degree v ≤ dl) : Balancer G :=
  Balancer.stateless G (fun v x _ => roundDiv x (G.degree v + dl))
    (fun v x => x - G.degree v * roundDiv x (G.degree v + dl))
    (by
      intro v x
      rw [Finset.sum_const, G.card_neighborFinset_eq_degree, smul_eq_mul]
      have := degree_mul_roundDiv_le G dl hdl v x
      omega)

/-- One step of `SEND([x/d⁺])` at a node of degree `d' ≤ dl` is a good `s`-step whenever
`s ≤ ⌈d⁺/2⌉ − d'`. -/
lemma goodStep_sendRound {d' dl s : ℕ} (hd : d' ≤ dl) (hdl : 0 < dl)
    (hs : s ≤ (d' + dl + 1) / 2 - d') (N : Finset V) (x : ℕ) :
    GoodStep dl s (d' + dl) x (fun _ => roundDiv x (d' + dl)) N
      (x - d' * roundDiv x (d' + dl)) := by
  set D := d' + dl with hD
  have hDpos : 0 < D := by omega
  rw [roundDiv_eq _ _ hDpos]
  have h1 := Nat.div_add_mod x D
  have h2 := Nat.mod_lt x hDpos
  set q := x / D
  set e := x % D
  have hDq : D * q = d' * q + dl * q := by rw [hD]; ring
  have hx : x = d' * q + dl * q + e := by rw [← hDq]; omega
  have hm1 : d' * (q + 1) = d' * q + d' := by ring
  by_cases h : D ≤ 2 * e
  · simp only [h, ite_true]
    have hkeep : x - d' * (q + 1) = dl * q + (e - d') := by omega
    refine ⟨fun w _ => Or.inr ⟨by omega, rfl⟩, fun i => q + if i.val < e - d' then 1 else 0, ?_,
      fun i => ?_, ?_⟩
    · rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
        Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin, min_eq_right (show e - d' ≤ dl by omega), hkeep]
      push_cast; ring
    · unfold FairShare; dsimp only
      split_ifs with hi
      · exact Or.inr ⟨by omega, rfl⟩
      · exact Or.inl (by simp [q])
    · have : #{i : Fin dl | (q + if i.val < e - d' then 1 else 0) = q + 1} =
          #{i : Fin dl | i.val < e - d'} := by
        congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
      rw [this, Fin.card_filter_val_lt, min_eq_right (show e - d' ≤ dl by omega)]
      omega
  · simp only [h, ite_false, add_zero]
    have hkeep : x - d' * q = dl * q + e := by omega
    refine ⟨fun w _ => Or.inl rfl, fun i => q + if i.val < e then 1 else 0, ?_,
      fun i => ?_, ?_⟩
    · rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
        Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin, min_eq_right (show e ≤ dl by omega), hkeep]
      push_cast; ring
    · unfold FairShare; dsimp only
      split_ifs with hi
      · exact Or.inr ⟨by omega, rfl⟩
      · exact Or.inl (by simp [q])
    · have : #{i : Fin dl | (q + if i.val < e then 1 else 0) = q + 1} =
          #{i : Fin dl | i.val < e} := by
        congr 1; ext i; simp only [mem_filter, mem_univ, true_and]; split_ifs <;> simp_all
      rw [this, Fin.card_filter_val_lt, min_eq_right (show e ≤ dl by omega)]
      omega

variable {G}

/-- Observation 3.2, corrected: on a `d`-regular graph with `d < d◦`, `SEND([x/d⁺])` is a good
`s`-balancer for every `1 ≤ s ≤ ⌈d⁺/2⌉ − d` (it is cumulatively `0`-fair, Observation 2.2). -/
theorem sendRound_isGood {d dl : ℕ} (hreg : G.IsRegularOfDegree d) (hd : d < dl) {s : ℕ}
    (hs1 : 1 ≤ s) (hs : s ≤ (d + dl + 1) / 2 - d) :
    (sendRound G dl (fun v => by rw [hreg v]; omega)).IsGood dl s := by
  have hstep : ∀ v x, GoodStep dl s (G.degree v + dl) x
      (fun _ => roundDiv x (G.degree v + dl)) (G.neighborFinset v)
      (x - G.degree v * roundDiv x (G.degree v + dl)) := fun v x => by
    rw [hreg v]; exact goodStep_sendRound hd.le (by omega) hs _ x
  refine ⟨hs1, by omega, fun x₀ t v => ⟨fun w _ => ?_, ?_, fun w₁ _ w₂ _ => ?_⟩, fun v _ x => hstep v x⟩
  · obtain ⟨h, -⟩ := hstep v (Balancer.load (sendRound G dl (fun v => by rw [hreg v]; omega)) x₀ t v)
    have := h w (by assumption)
    have hf : Balancer.flow (sendRound G dl (fun v => by rw [hreg v]; omega)) x₀ t v w =
        roundDiv (Balancer.load (sendRound G dl (fun v => by rw [hreg v]; omega)) x₀ t v)
          (G.degree v + dl) := rfl
    rw [hf]; unfold FairShare at this; beta_reduce at this; omega
  · obtain ⟨-, g, hg, hgf, -⟩ := hstep v (Balancer.load (sendRound G dl (fun v => by rw [hreg v]; omega)) x₀ t v)
    refine ⟨g, hg, fun i => ?_⟩
    have := hgf i; unfold FairShare at this; omega
  · simp [Balancer.cumFlow, Balancer.flow, sendRound, Balancer.stateless]

/-- Observation 3.2 is tight in the corrected form: for `s > ⌈d⁺/2⌉ − d` (and `d ≥ 1`),
`SEND([x/d⁺])` is not a good `s`-balancer (load `x = ⌈d⁺/2⌉` violates `s`-self-preference). -/
theorem sendRound_not_isGood {d dl : ℕ} [Nonempty V] (hreg : G.IsRegularOfDegree d) (hd1 : 1 ≤ d)
    (hd : d < dl) {s : ℕ} (hs : (d + dl + 1) / 2 - d < s) :
    ¬ (sendRound G dl (fun v => by rw [hreg v]; omega)).IsGood dl s := by
  rintro ⟨-, hsdl, -, hstep⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  set x := (d + dl + 1) / 2 with hx
  obtain ⟨-, g, hg, hgf, hpref⟩ := hstep v () x
  simp only [sendRound, Balancer.stateless] at hg
  rw [hreg v] at hg hgf hpref
  have hxD : x < d + dl := by omega
  have hq : x / (d + dl) = 0 := Nat.div_eq_of_lt hxD
  have he : x % (d + dl) = x := Nat.mod_eq_of_lt hxD
  have hr : roundDiv x (d + dl) = 1 := by
    rw [roundDiv_eq _ _ (by omega), hq, he]; split_ifs <;> omega
  rw [hr, mul_one] at hg
  rw [hq, he, zero_add] at hpref
  -- the number of self-loops receiving one token is at most the number of kept tokens
  have hcount : #{i | g i = 1} ≤ ∑ i, g i := by
    calc #{i | g i = 1} = ∑ i ∈ ({i | g i = 1} : Finset (Fin dl)), g i := by
          rw [Finset.card_eq_sum_ones]
          exact Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2.symm
      _ ≤ ∑ i, g i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

/-- Exact characterisation: `SEND([x/d⁺])` is a good `s`-balancer iff `1 ≤ s ≤ ⌈d⁺/2⌉ − d`. -/
theorem sendRound_isGood_iff {d dl : ℕ} [Nonempty V] (hreg : G.IsRegularOfDegree d)
    (hd1 : 1 ≤ d) (hd : d < dl) (s : ℕ) :
    (sendRound G dl (fun v => by rw [hreg v]; omega)).IsGood dl s ↔
      1 ≤ s ∧ s ≤ (d + dl + 1) / 2 - d := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hlt
    exact sendRound_not_isGood hreg hd1 hd (by omega) h
  · rintro ⟨h1, h2⟩
    exact sendRound_isGood hreg hd h1 h2

/-- **Observation 3.2 is false** (first claim) whenever `d◦ ≥ d + 2` and `d ≥ 1`:
`SEND([x/d⁺])` is not a good `(d⁺ − 2d)`-balancer. -/
theorem observation_3_2_false {d dl : ℕ} [Nonempty V] (hreg : G.IsRegularOfDegree d)
    (hd1 : 1 ≤ d) (hd : d + 2 ≤ dl) :
    ¬ (sendRound G dl (fun v => by rw [hreg v]; omega)).IsGood dl ((d + dl) - 2 * d) :=
  sendRound_not_isGood hreg hd1 (by omega) (by omega)

/-- The smallest instance: `K₂` (`d = 1`) with `d◦ = 4` self-loops, `d⁺ = 5 > 2d`; the paper claims
a good `3`-balancer. -/
example : ¬ (sendRound (⊤ : SimpleGraph (Fin 2)) 4
    (fun v => by rw [SimpleGraph.IsRegularOfDegree.top v]; simp)).IsGood 4 3 := by
  have := observation_3_2_false (G := (⊤ : SimpleGraph (Fin 2))) (d := 1) (dl := 4)
    (by simpa using SimpleGraph.IsRegularOfDegree.top (V := Fin 2)) le_rfl (by norm_num)
  exact this

end SendRound

end Podc.DeterministicLoadBalancing
