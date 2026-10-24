import Papers.PODC2024.DataCenterRouting.Section5

/-!
# Tightness of Theorem 5.4: the Doom-Switch routing (Example 5.3)

`g` copies of the gadget of Example 3.3 are stacked on the input switch `I_1` and the output
switch `O_1` of `C_n` (`2g + 1 ≤ n`), each with `q` type-2 flows:

* type 1: `(s_1^j, t_1^j)` for the `2g` servers `j = 2p + b` (`p < g`, `b < 2`, 0-based);
* type 2: `q` copies of `(s_1^{2p+1}, t_1^{2p})` for each `p < g` (0-based; the paper's
  `(s_1^j, t_1^{j-1})`, `j` even).

The Doom-Switch routing (Algorithm 1) sends the type-1 flow of server `j` through `M_j` (a maximum
matching routed link-disjointly) and all type-2 flows through the "doom" switch `M_{2g}`.
In `MS_n` every flow gets `1/(q+1)`, so `T^MmF = g (q+2)/(q+1)`; under the Doom-Switch routing,
type-1 flows get `1 - 1/g` and type-2 flows get `1/(gq)` (for `g ≥ 2`), so the throughput is
`2g - 1`.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

section Doom

variable {n g q : ℕ} (h : 2 * g + 1 ≤ n)

/-- The switch `I_1` / `O_1`. -/
def tor0 : Fin (2 * n) := ⟨0, by omega⟩

/-- Server `2p + b` (0-based) of a switch, and middle switch `M_{2p+b}`. -/
def srv (p : Fin g) (b : Fin 2) : Fin n := ⟨2 * p + b, by omega⟩

/-- The doom middle switch `M_{2g}` (0-based). -/
def doomSw : Fin n := ⟨2 * g, by omega⟩

variable {h} in
theorem srv_inj {p p' : Fin g} {b b' : Fin 2} : srv h p b = srv h p' b' ↔ p = p' ∧ b = b' := by
  simp only [srv, Fin.ext_iff]
  constructor
  · intro e
    have := b.isLt; have := b'.isLt
    constructor <;> omega
  · rintro ⟨e1, e2⟩; rw [e1, e2]

variable {h} in
theorem srv_ne_doomSw (p : Fin g) (b : Fin 2) : srv h p b ≠ doomSw h := by
  simp only [srv, doomSw, ne_eq, Fin.ext_iff]
  have := p.isLt; have := b.isLt
  omega

variable (g q) in
/-- Flow index type: `inl (p, b)` is the type-1 flow of server `2p + b`, `inr (p, c)` is copy `c`
of the type-2 flow of gadget `p`. -/
abbrev DFlow := (Fin g × Fin 2) ⊕ (Fin g × Fin q)

/-- The adversarial flows of Theorem 5.4. -/
def doom : Flows n (DFlow g q) where
  src
    | .inl (p, b) => (tor0 h, srv h p b)
    | .inr (p, _) => (tor0 h, srv h p 1)
  dst
    | .inl (p, b) => (tor0 h, srv h p b)
    | .inr (p, _) => (tor0 h, srv h p 0)

/-- The routing produced by the Doom-Switch algorithm. -/
def doomRouting : DFlow g q → Fin n
  | .inl (p, b) => srv h p b
  | .inr _ => doomSw h

/-! ### Loads -/

variable (a : DFlow g q → ℝ)

theorem doom_srcSum (p : Fin g) (b : Fin 2) :
    (∑ f, if (doom (q := q) h).src f = (tor0 h, srv h p b) then a f else 0) =
      a (.inl (p, b)) + if b = 1 then ∑ c, a (.inr (p, c)) else 0 := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_eq_single (p, b)]
    · simp [doom]
    · rintro ⟨p', b'⟩ _ hne
      rw [ite_eq_right]
      simp only [doom, Prod.mk.injEq, true_and, srv_inj]
      rintro ⟨rfl, rfl⟩; exact hne rfl
    · simp
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
    · by_cases hb : b = 1
      · subst hb; simp [doom]
      · simp only [doom, Prod.mk.injEq, true_and, srv_inj]
        simp [Ne.symm hb, hb]
    · intro p' _ hp'
      refine Finset.sum_eq_zero fun c _ => ite_eq_right ?_
      simp only [doom, Prod.mk.injEq, true_and, srv_inj]
      rintro ⟨rfl, -⟩; exact hp' rfl
    · simp

theorem doom_dstSum (p : Fin g) (b : Fin 2) :
    (∑ f, if (doom (q := q) h).dst f = (tor0 h, srv h p b) then a f else 0) =
      a (.inl (p, b)) + if b = 0 then ∑ c, a (.inr (p, c)) else 0 := by
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Finset.sum_eq_single (p, b)]
    · simp [doom]
    · rintro ⟨p', b'⟩ _ hne
      rw [ite_eq_right]
      simp only [doom, Prod.mk.injEq, true_and, srv_inj]
      rintro ⟨rfl, rfl⟩; exact hne rfl
    · simp
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
    · by_cases hb : b = 0
      · subst hb; simp [doom]
      · simp only [doom, Prod.mk.injEq, true_and, srv_inj]
        simp [Ne.symm hb, hb]
    · intro p' _ hp'
      refine Finset.sum_eq_zero fun c _ => ite_eq_right ?_
      simp only [doom, Prod.mk.injEq, true_and, srv_inj]
      rintro ⟨rfl, -⟩; exact hp' rfl
    · simp

/-- Every server of the gadgets is `(tor0, srv p b)`; the other servers carry no flow. -/
theorem doom_server_cases (s : Server n) :
    (∃ p b, s = (tor0 h, srv h p b)) ∨
      ((∀ f : DFlow g q, (doom h).src f ≠ s) ∧ ∀ f : DFlow g q, (doom h).dst f ≠ s) := by
  by_cases hs : ∃ p b, s = (tor0 h, srv h p b)
  · exact Or.inl hs
  · push Not at hs
    refine Or.inr ⟨fun f => ?_, fun f => ?_⟩ <;> rcases f with ⟨p, b⟩ | ⟨p, c⟩
    all_goals exact fun e => hs _ _ e.symm

theorem doom_upSum (x : Fin (2 * n)) (m : Fin n) :
    (∑ f, if ((doom (q := q) h).src f).1 = x ∧ doomRouting h f = m then a f else 0) =
      if x = tor0 h then ∑ f, (if doomRouting h f = m then a f else 0) else 0 := by
  split_ifs with hx
  · subst hx
    refine Finset.sum_congr rfl fun f _ => ?_
    rcases f with ⟨p, b⟩ | ⟨p, c⟩ <;> simp [doom]
  · refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
    rcases f with ⟨p, b⟩ | ⟨p, c⟩ <;> exact fun e => hx e.1.symm

theorem doom_downSum (x : Fin (2 * n)) (m : Fin n) :
    (∑ f, if doomRouting h f = m ∧ ((doom (q := q) h).dst f).1 = x then a f else 0) =
      if x = tor0 h then ∑ f, (if doomRouting h f = m then a f else 0) else 0 := by
  split_ifs with hx
  · subst hx
    refine Finset.sum_congr rfl fun f _ => ?_
    rcases f with ⟨p, b⟩ | ⟨p, c⟩ <;> simp [doom]
  · refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
    rcases f with ⟨p, b⟩ | ⟨p, c⟩ <;> exact fun e => hx e.2.symm

theorem doom_routeSum_srv (p : Fin g) (b : Fin 2) :
    (∑ f, if doomRouting h f = srv h p b then a f else 0) = a (.inl (p, b)) := by
  rw [Finset.sum_eq_single (.inl (p, b))]
  · simp [doomRouting]
  · rintro (⟨p', b'⟩ | ⟨p', c⟩) _ hne
    · rw [ite_eq_right]; simp only [doomRouting, srv_inj]; rintro ⟨rfl, rfl⟩; exact hne rfl
    · rw [ite_eq_right]; exact (srv_ne_doomSw p b).symm
  · simp

theorem doom_routeSum_doom :
    (∑ f, if doomRouting h f = doomSw h then a f else 0) = ∑ x : Fin g × Fin q, a (.inr x) := by
  rw [Fintype.sum_sum_type]
  simp [doomRouting, srv_ne_doomSw]

theorem doom_routeSum_other (m : Fin n) (hm1 : ∀ p b, m ≠ srv h p b) (hm2 : m ≠ doomSw h) :
    (∑ f, if doomRouting h f = m then a f else 0) = 0 := by
  refine Finset.sum_eq_zero fun f _ => ite_eq_right ?_
  rcases f with ⟨p, b⟩ | ⟨p, c⟩
  · exact fun e => hm1 p b e.symm
  · exact fun e => hm2 e.symm

/-! ### The max-min fair allocations -/

theorem doom_macroSwitch_isMaxMinFair :
    (macroSwitch (doom (q := q) h)).IsMaxMinFair (fun _ => 1 / (q + 1 : ℝ)) := by
  have hq : (0 : ℝ) < q + 1 := by positivity
  have hsum : ∑ _c : Fin q, 1 / (q + 1 : ℝ) = q / (q + 1) := by simp [div_eq_mul_inv]
  have hone : 1 / (q + 1 : ℝ) + q / (q + 1) = 1 := by field_simp; ring
  have hle : 1 / (q + 1 : ℝ) ≤ 1 := by rw [div_le_one hq]; linarith
  apply Network.isMaxMinFair_of_hasBottlenecks
  · refine ⟨fun _ => by positivity, fun ℓ => ?_⟩
    rw [macroSwitch_cap]
    cases ℓ with
    | srcLink s =>
      rw [macroSwitch_load_srcLink]
      rcases doom_server_cases h s with ⟨p, b, rfl⟩ | ⟨hs, -⟩
      · rw [doom_srcSum, hsum]; split_ifs <;> linarith
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | dstLink s =>
      rw [macroSwitch_load_dstLink]
      rcases doom_server_cases h s with ⟨p, b, rfl⟩ | ⟨-, hs⟩
      · rw [doom_dstSum, hsum]; split_ifs <;> linarith
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | up i m => rw [macroSwitch_load_up]; norm_num
    | down m o => rw [macroSwitch_load_down]; norm_num
  · rintro (⟨p, b⟩ | ⟨p, c⟩)
    · fin_cases b
      · refine ⟨.dstLink (tor0 h, srv h p 0), by simp [mem_macroSwitch_path, doom], ?_,
          fun _ _ => le_rfl⟩
        rw [macroSwitch_load_dstLink, doom_dstSum, ite_eq_left rfl, hsum, hone, macroSwitch_cap]
      · refine ⟨.srcLink (tor0 h, srv h p 1), by simp [mem_macroSwitch_path, doom], ?_,
          fun _ _ => le_rfl⟩
        rw [macroSwitch_load_srcLink, doom_srcSum, ite_eq_left rfl, hsum, hone, macroSwitch_cap]
    · refine ⟨.srcLink (tor0 h, srv h p 1), by simp [mem_macroSwitch_path, doom], ?_,
        fun _ _ => le_rfl⟩
      rw [macroSwitch_load_srcLink, doom_srcSum, ite_eq_left rfl, hsum, hone, macroSwitch_cap]

variable (g q) in
/-- The max-min fair allocation for the Doom-Switch routing: type 1 gets `1 - 1/g`, type 2 gets
`1/(gq)`. -/
noncomputable def aDoom : DFlow g q → ℝ
  | .inl _ => 1 - 1 / g
  | .inr _ => 1 / (g * q)

variable {h} in
theorem aDoom_le (hg : 2 ≤ g) (hq : 1 ≤ q) (f : DFlow g q) : aDoom g q f ≤ 1 - 1 / g := by
  rcases f with ⟨p, b⟩ | ⟨p, c⟩
  · exact le_rfl
  · simp only [aDoom]
    have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h1 : 1 / ((g : ℝ) * q) ≤ 1 / g :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : 1 / (g : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hg'
    linarith

theorem doom_clos_isMaxMinFair (hg : 2 ≤ g) (hq : 1 ≤ q) :
    (clos (doom (q := q) h) (doomRouting h)).IsMaxMinFair (aDoom g q) := by
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hgq : (g : ℝ) * q ≠ 0 := by positivity
  have hsum' : ∀ p : Fin g, ∑ c : Fin q, aDoom g q (.inr (p, c)) = 1 / g := by
    intro p
    simp only [aDoom, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hdoom : ∑ x : Fin g × Fin q, aDoom g q (.inr x) = 1 := by
    simp only [aDoom, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; field_simp
  have h1 : 0 ≤ 1 - 1 / (g : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hnonneg : ∀ f, 0 ≤ aDoom g q f := by
    rintro (⟨p, b⟩ | ⟨p, c⟩)
    · exact h1
    · simp only [aDoom]; positivity
  have hserv : ∀ (p : Fin g) (b : Fin 2) (c : Prop) [Decidable c],
      aDoom g q (.inl (p, b)) + (if c then ∑ c, aDoom g q (.inr (p, c)) else 0) ≤ 1 := by
    intro p b c _
    rw [hsum' p]
    simp only [aDoom]
    split_ifs <;> linarith [one_div_pos.2 (show (0 : ℝ) < g by linarith)]
  have hroute : ∀ m : Fin n, (∑ f, if doomRouting h f = m then aDoom g q f else 0) ≤ 1 := by
    intro m
    by_cases hm : ∃ p b, m = srv h p b
    · obtain ⟨p, b, rfl⟩ := hm
      rw [doom_routeSum_srv]; simp only [aDoom]
      linarith [one_div_pos.2 (show (0 : ℝ) < g by linarith)]
    · push Not at hm
      by_cases hm2 : m = doomSw h
      · subst hm2; rw [doom_routeSum_doom, hdoom]
      · rw [doom_routeSum_other h _ m hm hm2]; norm_num
  apply Network.isMaxMinFair_of_hasBottlenecks
  · refine ⟨hnonneg, fun ℓ => ?_⟩
    rw [clos_cap]
    cases ℓ with
    | srcLink s =>
      rw [clos_load_srcLink]
      rcases doom_server_cases h s with ⟨p, b, rfl⟩ | ⟨hs, -⟩
      · rw [doom_srcSum]; exact hserv p b _
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | dstLink s =>
      rw [clos_load_dstLink]
      rcases doom_server_cases h s with ⟨p, b, rfl⟩ | ⟨-, hs⟩
      · rw [doom_dstSum]; exact hserv p b _
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | up x m =>
      rw [clos_load_up, doom_upSum]
      split_ifs
      · exact hroute m
      · norm_num
    | down m x =>
      rw [clos_load_down, doom_downSum]
      split_ifs
      · exact hroute m
      · norm_num
  · rintro (⟨p, b⟩ | ⟨p, c⟩)
    · fin_cases b
      · refine ⟨.dstLink (tor0 h, srv h p 0), by simp [mem_clos_path, doom], ?_,
          fun g' _ => aDoom_le hg hq g'⟩
        rw [clos_load_dstLink, doom_dstSum, ite_eq_left rfl, hsum' p, clos_cap]
        simp [aDoom]
      · refine ⟨.srcLink (tor0 h, srv h p 1), by simp [mem_clos_path, doom], ?_,
          fun g' _ => aDoom_le hg hq g'⟩
        rw [clos_load_srcLink, doom_srcSum, ite_eq_left rfl, hsum' p, clos_cap]
        simp [aDoom]
    · refine ⟨.up (tor0 h) (doomSw h), by simp [mem_clos_path, doom, doomRouting], ?_,
        fun g' hg' => ?_⟩
      · rw [clos_load_up, doom_upSum, ite_eq_left rfl, doom_routeSum_doom, hdoom, clos_cap]
      · rw [mem_clos_path] at hg'
        rcases g' with ⟨p', b'⟩ | ⟨p', c'⟩
        · simp [doomRouting] at hg'
          exact absurd hg'.2.symm (srv_ne_doomSw p' b')
        · exact le_rfl

theorem throughput_doom_macroSwitch :
    throughput (fun _ : DFlow g q => 1 / (q + 1 : ℝ)) = g * (q + 2) / (q + 1) := by
  simp only [throughput, Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

theorem throughput_aDoom (hg : 1 ≤ g) (hq : 1 ≤ q) : throughput (aDoom g q) = 2 * g - 1 := by
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hg' : (g : ℝ) ≠ 0 := by positivity
  have hq' : (q : ℝ) ≠ 0 := by positivity
  simp only [throughput, Fintype.sum_sum_type, aDoom, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

end Doom

end Podc.DataCenterRouting

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

/-- **Example 5.3** (`n = 7`, three gadgets, one type-2 flow each): the max-min fair allocation in
`MS_7` has throughput `9/2`, the Doom-Switch routing yields a max-min fair allocation of throughput
`5`. -/
theorem example_5_3 :
    (macroSwitch (doom (n := 7) (g := 3) (q := 1) (by norm_num))).IsMaxMinFair
        (fun _ => 1 / (1 + 1 : ℝ)) ∧
      (clos (doom (n := 7) (g := 3) (q := 1) (by norm_num))
        (doomRouting (by norm_num))).IsMaxMinFair (aDoom 3 1) ∧
      throughput (fun _ : DFlow 3 1 => 1 / (1 + 1 : ℝ)) = 9 / 2 ∧
      throughput (aDoom 3 1) = 5 := by
  refine ⟨by exact_mod_cast doom_macroSwitch_isMaxMinFair (q := 1) (by norm_num),
    doom_clos_isMaxMinFair _ (by norm_num) le_rfl, ?_, ?_⟩
  · have := throughput_doom_macroSwitch (g := 3) (q := 1)
    norm_num at this ⊢; linarith
  · rw [throughput_aDoom (by norm_num) le_rfl]; norm_num

/-- **The rates claimed in the proof of Theorem 5.4 are wrong for `n = 3`** (one gadget, `g = 1`):
the proof asserts that under the Doom-Switch routing type-1 flows get `1 - 2/(n-1) = 0` and type-2
flows get `2/(q(n-1)) = 1/q`; this allocation is not max-min fair, because giving every flow
`1/(q+1)` is feasible for the same routing and lexicographically better. (The statement of
Theorem 5.4 is unaffected for `n = 3`, see `theorem_5_4_tight_odd`.) -/
theorem doom_paper_rates_not_isMaxMinFair {n q : ℕ} (h : 2 * 1 + 1 ≤ n) (hq : 1 ≤ q) :
    ¬ (clos (doom (q := q) h) (doomRouting h)).IsMaxMinFair (aDoom 1 q) := by
  intro ha
  have hq0 : (0 : ℝ) < q + 1 := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set b : DFlow 1 q → ℝ := fun _ => 1 / (q + 1 : ℝ)
  have hsum : ∑ _c : Fin q, 1 / (q + 1 : ℝ) = q / (q + 1) := by simp [div_eq_mul_inv]
  have hone : 1 / (q + 1 : ℝ) + q / (q + 1) = 1 := by field_simp; ring
  have hle : 1 / (q + 1 : ℝ) ≤ 1 := by rw [div_le_one hq0]; linarith
  have hle' : (q : ℝ) / (q + 1) ≤ 1 := by rw [div_le_one hq0]; linarith
  have hroute : ∀ m : Fin n, (∑ f, if doomRouting h f = m then b f else 0) ≤ 1 := by
    intro m
    by_cases hm : ∃ p b, m = srv h p b
    · obtain ⟨p, b', rfl⟩ := hm
      rw [doom_routeSum_srv]; exact hle
    · push Not at hm
      by_cases hm2 : m = doomSw h
      · subst hm2
        rw [doom_routeSum_doom]
        simp only [b, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          one_mul, nsmul_eq_mul]
        rw [← div_eq_mul_one_div]; exact hle'
      · rw [doom_routeSum_other h _ m hm hm2]; norm_num
  have hb : (clos (doom (q := q) h) (doomRouting h)).Feasible b := by
    refine ⟨fun _ => by positivity, fun ℓ => ?_⟩
    rw [clos_cap]
    cases ℓ with
    | srcLink s =>
      rw [clos_load_srcLink]
      rcases doom_server_cases h s with ⟨p, b', rfl⟩ | ⟨hs, -⟩
      · rw [doom_srcSum, hsum]; split_ifs <;> linarith
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | dstLink s =>
      rw [clos_load_dstLink]
      rcases doom_server_cases h s with ⟨p, b', rfl⟩ | ⟨-, hs⟩
      · rw [doom_dstSum, hsum]; split_ifs <;> linarith
      · rw [Finset.sum_eq_zero fun f _ => ite_eq_right (hs f)]; norm_num
    | up x m =>
      rw [clos_load_up, doom_upSum]
      split_ifs
      · exact hroute m
      · norm_num
    | down m x =>
      rw [clos_load_down, doom_downSum]
      split_ifs
      · exact hroute m
      · norm_num
  have hlt : sortedRates (aDoom 1 q) < sortedRates b := by
    refine sortedRates_lt_of_forall (fun e => ?_) fun f hf => ⟨.inl (0, 0), ?_, ?_⟩
    · have := congrFun e (.inl (0, 0))
      simp [b, aDoom] at this
      linarith
    · rcases f with ⟨p, b'⟩ | ⟨p, c⟩ <;> exact le_rfl
    · simp only [b, aDoom, Nat.cast_one, div_one, sub_self]; positivity
  exact absurd (ha.2 b hb) (not_le.2 hlt)

/-- A single flow of rate `1` is max-min fair in any network with unit capacities where its path is
nonempty. -/
theorem unit_isMaxMinFair {L : Type*} [DecidableEq L] (N : Network Unit L)
    (hcap : ∀ ℓ, N.cap ℓ = 1) (ℓ0 : L) (hℓ0 : ℓ0 ∈ N.path ()) :
    N.IsMaxMinFair (fun _ => 1) := by
  apply Network.isMaxMinFair_of_hasBottlenecks
  · refine ⟨fun _ => zero_le_one, fun ℓ => ?_⟩
    rw [Network.load_eq_sum_ite, Fintype.sum_unique, hcap]
    split_ifs <;> norm_num
  · intro u
    refine ⟨ℓ0, hℓ0, ?_, fun _ _ => le_rfl⟩
    rw [Network.load_eq_sum_ite, Fintype.sum_unique, ite_eq_left hℓ0, hcap]

/-- The stacked-gadget construction with `g` gadgets (`2g + 1 ≤ n`): for every `ε > 1/(2g)` some
routing has a max-min fair allocation of throughput at least `2(1 - ε) T^MmF`. -/
theorem tight_aux {n g : ℕ} (h : 2 * g + 1 ≤ n) (hg : 1 ≤ g) (ε : ℝ)
    (hε : 1 / (2 * g : ℝ) < ε) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (r : F → Fin n) (a aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧ (clos fl r).IsMaxMinFair a ∧
      2 * (1 - ε) * throughput aMS ≤ throughput a := by
  rcases Nat.lt_or_ge g 2 with hg2 | hg2
  · -- `g = 1`: a single flow already works, since `2(1 - ε) < 1`
    have hg1 : g = 1 := by omega
    subst hg1
    let fl : Flows n Unit := ⟨fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩),
      fun _ => (⟨0, by omega⟩, ⟨0, by omega⟩)⟩
    refine ⟨Unit, inferInstance, fl, fun _ => ⟨0, by omega⟩, fun _ => 1, fun _ => 1,
      unit_isMaxMinFair _ (fun _ => rfl) (.srcLink (fl.src ())) (by simp [macroSwitch]),
      unit_isMaxMinFair _ (fun _ => rfl) (.srcLink (fl.src ())) (by simp [clos]), ?_⟩
    simp only [throughput, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
    norm_num at hε
    linarith
  · -- `g ≥ 2`: the Doom-Switch routing with `q` large enough
    set δ : ℝ := 2 * (1 - ε) * g with hδ
    have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg2
    have hδlt : δ < 2 * g - 1 := by
      rw [div_lt_iff₀ (by positivity)] at hε
      rw [hδ]; nlinarith
    obtain ⟨q0, hq0⟩ := exists_nat_gt (2 * g / (2 * g - 1 - δ))
    set q := q0 + 1
    have hq1 : 1 ≤ q := by omega
    refine ⟨DFlow g q, inferInstance, doom (q := q) h, doomRouting h, aDoom g q, fun _ => 1 / (q + 1),
      doom_macroSwitch_isMaxMinFair h, doom_clos_isMaxMinFair h hg2 hq1, ?_⟩
    rw [throughput_doom_macroSwitch, throughput_aDoom hg hq1]
    have hq' : (q : ℝ) = q0 + 1 := by simp [q]
    have hpos : (0 : ℝ) < 2 * g - 1 - δ := by linarith
    have hqbig : 2 * g < (q : ℝ) * (2 * g - 1 - δ) := by
      rw [div_lt_iff₀ hpos] at hq0
      rw [hq']; nlinarith
    rw [show 2 * (1 - ε) * (g * (q + 2 : ℝ) / (q + 1)) = δ * (q + 2) / (q + 1) by
      rw [hδ]; ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **Theorem 5.4, second part, odd `n`** (the case treated in the paper). For every odd `n ≥ 3`
and every `ε > 1/(n-1)` there is a collection of flows in `C_n` and a routing whose max-min fair
allocation has throughput at least `2(1 - ε) T^MmF`; hence `T^{T-MmF} ≥ 2(1 - ε) T^MmF` for every
throughput-max-min fair allocation. -/
theorem theorem_5_4_tight_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (ε : ℝ)
    (hε : 1 / ((n : ℝ) - 1) < ε) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (r : F → Fin n) (a aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧ (clos fl r).IsMaxMinFair a ∧
      2 * (1 - ε) * throughput aMS ≤ throughput a ∧
      ∀ r' a', IsThroughputMaxMinFair fl r' a' → 2 * (1 - ε) * throughput aMS ≤ throughput a' := by
  obtain ⟨g, rfl⟩ := hodd
  obtain ⟨F, _, fl, r, a, aMS, hMS, ha, ht⟩ := tight_aux (n := 2 * g + 1) le_rfl (by omega) ε
    (by push_cast at hε; simpa using hε)
  exact ⟨F, _, fl, r, a, aMS, hMS, ha, ht, fun r' a' ha' => ht.trans (ha'.2 r a ha)⟩

/-- **Theorem 5.4, second part, even `n`.** The paper assumes "without loss of generality" that `n`
is odd. For even `n ≥ 4` the same construction (using `n - 1` middle switches) only gives
`ε > 1/(n-2)`. -/
theorem theorem_5_4_tight_even (n : ℕ) (hn : 4 ≤ n) (heven : Even n) (ε : ℝ)
    (hε : 1 / ((n : ℝ) - 2) < ε) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (r : F → Fin n) (a aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧ (clos fl r).IsMaxMinFair a ∧
      2 * (1 - ε) * throughput aMS ≤ throughput a ∧
      ∀ r' a', IsThroughputMaxMinFair fl r' a' → 2 * (1 - ε) * throughput aMS ≤ throughput a' := by
  obtain ⟨g, rfl⟩ := heven
  obtain ⟨F, _, fl, r, a, aMS, hMS, ha, ht⟩ := tight_aux (n := g + g) (g := g - 1) (by omega)
    (by omega) ε (by
      have : ((g - 1 : ℕ) : ℝ) = g - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]; push_cast at hε; convert hε using 2; ring)
  exact ⟨F, _, fl, r, a, aMS, hMS, ha, ht, fun r' a' ha' => ht.trans (ha'.2 r a ha)⟩

end Podc.DataCenterRouting
