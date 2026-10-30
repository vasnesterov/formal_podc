import Papers.PODC2012.WirelessPacketScheduling.Counting
import Papers.PODC2012.WirelessPacketScheduling.Numerics

/-!
# Theorem 1 is false

Instance: packet routing (`W` = identity) on `m = 200` links with `5100` packets on every link,
so `n = 1 020 000` and `I = ‖W · R‖∞ = 5100`; `φ = 1`. The static algorithm is "all or nothing":
if `‖W · R_S‖∞ ≤ I'` it delivers all of `S` (one packet per link and step, `f ≡ 1`), otherwise it
delivers nothing. It satisfies the hypothesis of Theorem 1 with success probability `1`.

Then `85 < χ < 86`, `ξ = 1` and `ψ₁ = 60`. In iteration 1 each packet gets a uniform delay in
`[60]`, so on every link a delay class receives `Bin(5100, 1/60)` packets, mean `85 < χ`. A class
is served only if *no* link carries more than `χ` (i.e. `≥ 86`) of its packets. On each link
this fails with probability `P(Bin(5100, 1/60) ≥ 86) ≥ P(= 86) ≥ 1/25`, independently over the
200 links. So with probability `≥ 1 - 60 · (24/25)^200 > 0.98` every class fails, nothing is
delivered, and the clean-up executions `𝒜(2φχ log n, n)` are run on an instance of interference
`5100 > 2φχ log n` and deliver nothing either. Hence Algorithm 1 fails with probability
`> 0.98 > 1/n^φ`.

The paper's proof breaks in Claim 2: with `ψ = ⌈2^{-i+1} I/χ⌉` delay values the expected load of a
delay class is up to `χ`, not `χ/2` as claimed, so a constant fraction of the classes is
overloaded. The statement fails for `log = log₂` and for `log = ln`.
-/

namespace Podc.WirelessPacketScheduling

open Finset

/-! ### Algorithm 1 with a deterministic static algorithm -/

section Deterministic

variable {P : Type*} [DecidableEq P]

/-- Union of the images of a list of sets. -/
def unionMap (g : Finset P → Finset P) (Ss : List (Finset P)) : Finset P :=
  (Ss.map g).foldr (· ∪ ·) ∅

lemma runGroups_pure (g : Finset P → Finset P) (Ss : List (Finset P)) :
    runGroups (fun S => PMF.pure (g S)) Ss = PMF.pure (unionMap g Ss) := by
  induction Ss with
  | nil => rfl
  | cons S Ss ih => simp [runGroups, ih, unionMap]

lemma iteration_pure [Fintype P] (g : Finset P → Finset P) (ψ : ℕ) (R : Finset P) :
    iteration (fun S => PMF.pure (g S)) ψ R =
      (PMF.uniformOfFintype (P → Fin (max ψ 1))).map fun d =>
        unionMap g ((List.finRange (max ψ 1)).map fun j => R.filter (fun p => d p = j)) := by
  simp only [iteration, runGroups_pure]
  rfl

lemma mem_unionMap {g : Finset P → Finset P} {Ss : List (Finset P)} {x : P} :
    x ∈ unionMap g Ss ↔ ∃ S ∈ Ss, x ∈ g S := by
  induction Ss with
  | nil => simp [unionMap]
  | cons S Ss ih =>
    simp only [unionMap, List.map_cons, List.foldr_cons, mem_union] at ih ⊢
    rw [ih]; simp

end Deterministic

/-! ### The instance -/

/-- Links. -/
abbrev E0 := Fin 200
/-- Packets: `5100` on each link. -/
abbrev P0 := Fin 200 × Fin 5100

/-- Packet routing on 200 links: `W` is the identity matrix. -/
noncomputable def X0 : Instance E0 P0 where
  link := Prod.fst
  W e e' := if e = e' then 1 else 0
  W_nonneg e e' := by split_ifs <;> norm_num
  W_le_one e e' := by split_ifs <;> norm_num
  W_self e := by simp

lemma X0_load (S : Finset P0) (e : E0) : X0.load S e = (S.filter (fun p => p.1 = e)).card := by
  simp only [Instance.load, X0]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 = e
  · simp [h]
  · simp [h, Ne.symm h]

open Classical in
/-- The deterministic "all or nothing" static algorithm. -/
noncomputable def a0 (I' : ℝ) (S : Finset P0) : Finset P0 := if X0.IntfLE S I' then ∅ else S

/-- `a0` as a `StaticAlg` (it ignores `n'`). -/
noncomputable def A0 : StaticAlg P0 := fun I' _ S => PMF.pure (a0 I' S)

/-- The all-or-nothing algorithm satisfies the hypothesis of Theorem 1. -/
lemma A0_good : A0.Good X0 where
  subset I' n' S R hR := by
    simp only [A0, PMF.support_pure, Set.mem_singleton_iff] at hR
    subst hR
    unfold a0; split_ifs <;> simp
  success I' n' S hS hn := by
    have h0 : (0 : ℝ) ≤ n' := le_trans (Nat.cast_nonneg _) hn
    simp only [A0, a0, ite_eq_left_of_eq_true _ _ (eq_true hS), PMF.pure_apply, ite_true, ENNReal.toReal_one]
    have : 0 ≤ 1 / n' := by positivity
    linarith

lemma X0_intfEq : X0.IntfEq Finset.univ 5100 := by
  have hl : ∀ e, X0.load Finset.univ e = 5100 := by
    intro e
    rw [X0_load]
    have : (Finset.univ.filter (fun p : P0 => p.1 = e)) = ({e} : Finset E0) ×ˢ Finset.univ := by
      ext ⟨a, b⟩; simp [Prod.ext_iff, eq_comm]
    rw [this]; simp
  exact ⟨fun e => (hl e).le, ⟨0, hl 0⟩⟩

/-! ### The probability computation -/

/-- Number of packets on link `e` with delay `j`. -/
def cnt (d : P0 → Fin 60) (e : E0) (j : Fin 60) : ℕ :=
  (Finset.univ.filter (fun i : Fin 5100 => d (e, i) = j)).card

lemma card_cnt_eq_86 (j : Fin 60) :
    (Finset.univ.filter (fun h : Fin 5100 → Fin 60 =>
      (Finset.univ.filter (fun i => h i = j)).card = 86)).card = Nat.choose 5100 86 * 59 ^ 5014 := by
  rw [card_filter_count_eq]; simp

/-- `60^5100 ≤ 25 · C(5100, 86) · 59^5014`, i.e. `P(Bin(5100, 1/60) = 86) ≥ 1/25`. -/
lemma binom_point_ge : 60 ^ 5100 ≤ 25 * (Nat.choose 5100 86 * 59 ^ 5014) := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

lemma key_nat : 25 * (60 ^ 5100 - Nat.choose 5100 86 * 59 ^ 5014) ≤ 24 * 60 ^ 5100 := by
  have h := binom_point_ge
  generalize 60 ^ 5100 = A at *
  generalize Nat.choose 5100 86 * 59 ^ 5014 = N at *
  omega

/-- For a fixed delay `j`, the number of delay assignments in which no link gets exactly `86`
packets of delay `j` is `(60^5100 - C(5100,86)·59^5014)^200`. -/
lemma card_forall_ne (j : Fin 60) :
    (Finset.univ.filter (fun d : P0 → Fin 60 => ∀ e, cnt d e j ≠ 86)).card =
      (60 ^ 5100 - Nat.choose 5100 86 * 59 ^ 5014) ^ 200 := by
  have hQ : (Finset.univ.filter (fun h : Fin 5100 → Fin 60 =>
      (Finset.univ.filter (fun i => h i = j)).card ≠ 86)).card =
        60 ^ 5100 - Nat.choose 5100 86 * 59 ^ 5014 := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
      card_cnt_eq_86]
    simp
  rw [← hQ, ← Fintype.card_subtype, ← Fintype.card_subtype]
  -- `{d // ∀ e, Q (curry d e)} ≃ (Fin 200 → {h // Q h})`
  have E : {x : P0 → Fin 60 // ∀ e, cnt x e j ≠ 86} ≃
      (Fin 200 → {h : Fin 5100 → Fin 60 // (Finset.univ.filter (fun i => h i = j)).card ≠ 86}) :=
    (Equiv.subtypeEquiv (p := fun x : P0 → Fin 60 => ∀ e, cnt x e j ≠ 86)
      (q := fun g : Fin 200 → Fin 5100 → Fin 60 =>
        ∀ e, (Finset.univ.filter (fun i => g e i = j)).card ≠ 86)
      (Equiv.curry (Fin 200) (Fin 5100) (Fin 60))
      (fun d => by simp only [cnt, Equiv.curry_apply, Function.curry_apply])).trans
      (Equiv.subtypePiEquivPi (β := fun _ : Fin 200 => Fin 5100 → Fin 60)
        (p := fun (_ : Fin 200) (h : Fin 5100 → Fin 60) =>
          (Finset.univ.filter (fun i => h i = j)).card ≠ 86))
  refine (Fintype.card_congr E).trans ?_
  rw [Fintype.card_fun, Fintype.card_fin]

/-- The undelivered packets after iteration 1, for the delay assignment `d`. -/
noncomputable def R1 (d : P0 → Fin 60) : Finset P0 :=
  unionMap (a0 (chi 200)) ((List.finRange 60).map fun j => Finset.univ.filter (fun p => d p = j))

/-- With `ξ = 1`, Algorithm 1 on our instance is a deterministic function of the delays. -/
lemma algorithm1_eq (b : ℝ) (hξ : xi b 200 1020000 5100 1 = 1) :
    algorithm1 A0 b 200 1020000 5100 1 = (PMF.uniformOfFintype (P0 → Fin 60)).map
      (fun d => a0 (finalParam b 200 1020000 1) (a0 (finalParam b 200 1020000 1) (R1 d))) := by
  simp only [algorithm1, hξ]
  have hA : ∀ x y : ℝ, A0 x y = fun S => PMF.pure (a0 x S) := fun _ _ => rfl
  simp only [Int.toNat_one, Nat.ceil_one, List.range_succ, List.range_zero,
    List.nil_append, List.singleton_append, List.foldl_cons, List.foldl_nil, PMF.pure_bind,
    zero_add, hA, psi_200_5100_one, iteration_pure]
  have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β), (p.bind fun a => PMF.pure (f a)) = p.map f :=
    fun p f => PMF.bind_pure_comp f p
  simp only [hbp, PMF.map_comp]
  rfl

lemma load_class (d : P0 → Fin 60) (j : Fin 60) (e : E0) :
    X0.load (Finset.univ.filter (fun p => d p = j)) e = cnt d e j := by
  have : Finset.univ.filter (fun p : P0 => d p = j ∧ p.1 = e) =
      (Finset.univ.filter (fun i : Fin 5100 => d (e, i) = j)).map
        ⟨fun i => (e, i), fun _ _ h => (Prod.ext_iff.1 h).2⟩ := by
    ext ⟨a, i⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨i, h1, rfl⟩
    · rintro ⟨i', h1, h2⟩
      have h3 : (e, i') = (a, i) := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      exact ⟨h1, rfl⟩
  rw [X0_load, Finset.filter_filter, this, Finset.card_map, cnt]

/-- If every delay class has a link with `86` of its packets, no class is served in
iteration 1. -/
lemma R1_eq_univ (d : P0 → Fin 60) (h : ∀ j, ∃ e, cnt d e j = 86) : R1 d = Finset.univ := by
  obtain ⟨c1, c2⟩ := chi_200_bounds
  have hj : ∀ j, a0 (chi 200) (Finset.univ.filter (fun p => d p = j)) =
      Finset.univ.filter (fun p => d p = j) := by
    intro j
    obtain ⟨e, he⟩ := h j
    unfold a0
    split_ifs with hle
    · exfalso
      have := hle e
      rw [load_class, he] at this
      norm_num at this
      linarith
    · rfl
  ext p
  simp only [R1, mem_unionMap, List.mem_map, List.mem_finRange, true_and, Finset.mem_univ,
    iff_true]
  refine ⟨_, ⟨d p, rfl⟩, ?_⟩
  rw [hj]; simp

/-- The clean-up executions deliver nothing when nothing was delivered before. -/
lemma a0_univ {T : ℝ} (hT : T < 5100) : a0 T Finset.univ = Finset.univ := by
  unfold a0
  split_ifs with hle
  · exfalso
    have := (X0_intfEq.2.choose_spec) ▸ hle X0_intfEq.2.choose
    linarith
  · rfl

/-- On our instance (with `ξ = 1` and `2φχ log n < 5100`), Algorithm 1 succeeds with probability
at most `60 · (24/25)^200 < 0.02`. -/
lemma algorithm1_success_le (b : ℝ) (hξ : xi b 200 1020000 5100 1 = 1)
    (hT : finalParam b 200 1020000 1 < 5100) :
    (algorithm1 A0 b 200 1020000 5100 1 ∅).toReal ≤ 60 * (24 / 25 : ℝ) ^ 200 := by
  rw [algorithm1_eq b hξ]
  set u := PMF.uniformOfFintype (P0 → Fin 60)
  set T := finalParam b 200 1020000 1
  set K : ℕ := (60 ^ 5100 - Nat.choose 5100 86 * 59 ^ 5014) ^ 200 with hK
  set B : Fin 60 → Set (P0 → Fin 60) := fun j => {d | ∀ e, cnt d e j ≠ 86}
  have hsub : (fun d => a0 T (a0 T (R1 d))) ⁻¹' {∅} ⊆ ⋃ j, B j := by
    intro d hd
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hd
    by_contra hc
    simp only [B, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_forall, not_not] at hc
    rw [R1_eq_univ d hc, a0_univ hT, a0_univ hT] at hd
    exact Finset.univ_nonempty.ne_empty hd
  have hB : ∀ j, u.toOuterMeasure (B j) = (K : ENNReal) / ((60 ^ (200 * 5100) : ℕ) : ENNReal) := by
    intro j
    rw [PMF.toOuterMeasure_uniformOfFintype_apply]
    have h1 : Fintype.card ↑(B j) = K := by
      have hBj : B j = ↑(Finset.univ.filter fun d : P0 → Fin 60 => ∀ e, cnt d e j ≠ 86) := by
        ext d; simp [B]
      rw [Fintype.card_eq_nat_card, hBj, Nat.card_coe_set_eq, Set.ncard_coe_finset,
        card_forall_ne j]
    have h2 : Fintype.card (P0 → Fin 60) = 60 ^ (200 * 5100) := by
      rw [Fintype.card_eq_nat_card, Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_fin]
    rw [h1, h2]
  have hle : (u.map fun d => a0 T (a0 T (R1 d))) ∅ ≤
      60 * ((K : ENNReal) / ((60 ^ (200 * 5100) : ℕ) : ENNReal)) := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    calc _ ≤ u.toOuterMeasure (⋃ j, B j) := MeasureTheory.measure_mono hsub
      _ ≤ ∑ j, u.toOuterMeasure (B j) := MeasureTheory.measure_iUnion_fintype_le _ _
      _ = _ := by
        rw [Finset.sum_congr rfl (fun j _ => hB j), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hM0 : ((60 ^ (200 * 5100) : ℕ) : ENNReal) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact pow_ne_zero _ (by norm_num)
  have hfin : 60 * ((K : ENNReal) / ((60 ^ (200 * 5100) : ℕ) : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top K) hM0)
  refine (ENNReal.toReal_mono hfin hle).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  gcongr
  set x : ℝ := ((60 ^ 5100 - Nat.choose 5100 86 * 59 ^ 5014 : ℕ) : ℝ) with hx
  have hy : ((60 ^ (200 * 5100) : ℕ) : ℝ) = ((60 : ℝ) ^ 5100) ^ 200 := by
    rw [Nat.cast_pow, ← pow_mul, mul_comm]; norm_num
  have hKx : (K : ℝ) = x ^ 200 := by rw [hK, Nat.cast_pow]
  rw [hKx, hy, ← div_pow]
  have hy0 : (0 : ℝ) < (60 : ℝ) ^ 5100 := by positivity
  have h25 : 25 * x ≤ 24 * (60 : ℝ) ^ 5100 := by
    have := key_nat
    rw [hx]; exact_mod_cast this
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hy0.le)
  rw [div_le_iff₀ hy0]; linarith

lemma theorem1_false_of (b : ℝ) (hξ : xi b 200 1020000 5100 1 = 1)
    (hT : finalParam b 200 1020000 1 < 5100) : ¬ Theorem1Claim b := by
  intro h
  have h1 := h E0 P0 X0 A0 5100 1 A0_good X0_intfEq one_pos
  have hE : Fintype.card E0 = 200 := by simp
  have hP : Fintype.card P0 = 1020000 := by simp
  rw [hE, hP] at h1
  have h2 := algorithm1_success_le b hξ hT
  rw [Real.rpow_one] at h1
  have h3 : (60 : ℝ) * (24 / 25) ^ 200 < 1 - 1 / ((1020000 : ℕ) : ℝ) := by norm_num
  linarith

/-- **Theorem 1 of [Kesselheim, PODC 2012] is false** (logarithms to base 2): on packet routing
with `200` links and `5100` packets per link, with `φ = 1` and the all-or-nothing static algorithm
(which satisfies the hypothesis with probability `1`), Algorithm 1 fails with probability
`≥ 1 - 60·(24/25)^200 > 0.98`, whereas the theorem claims success probability `≥ 1 - 1/n`. -/
theorem theorem1_false : ¬ Theorem1Claim 2 :=
  theorem1_false_of 2 xi_two (by linarith [finalParam_two_bounds.2])

/-- **Theorem 1 is false** also with natural logarithms. -/
theorem theorem1_false_ln : ¬ Theorem1Claim (Real.exp 1) :=
  theorem1_false_of (Real.exp 1) xi_e (by linarith [finalParam_e_bounds.2])

end Podc.WirelessPacketScheduling
