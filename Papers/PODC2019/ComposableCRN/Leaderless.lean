import Papers.PODC2019.ComposableCRN.OneDim
import Papers.PODC2019.ComposableCRN.Gadgets

/-!
# Theorem 9.2: leaderless oblivious computation in one dimension

`f : ℕ → ℕ` is obliviously-computable by a leaderless CRN iff it is semilinear and
superadditive (Severson–Haley–Doty, PODC 2019, §9).

"⇒" is Observation 9.1 (`LeaderlessObliviouslyComputable.superadditive`) together with Lemma 2.7
(cited from [10], taken as a hypothesis). For "⇐" we use a simplification of the paper's
construction. By `eventually_affine_of_semilinear_of_monotone` there are `N`, `P > 0`, `c` with
`f (x + P) = f x + c` for `x ≥ N`; let `red m = m` for `m < N + P` and `N + (m - N) mod P`
otherwise. The CRN has species `X`, `Y` and tokens `T_q`, `q < N + P`; a token `T_q` stands for
a block of `v` already consumed inputs with `red v = q`, whose output `f v` has been produced:

* `X → f(1) Y + T_{red 1}`;
* `T_a + T_b → (f(a+b) - f(a) - f(b)) Y + T_{red(a+b)}` for all `a, b < N + P`.

Since `red (v + w) = red (red v + red w)` and
`f (v + w) - f v - f w = f (red v + red w) - f (red v) - f (red w)`, merging the blocks `v` and
`w` produces exactly the missing output `f (v + w) - f v - f w ≥ 0`. Eventually all inputs are
consumed and at most one token remains, standing for the block `x`, with output `f x`. The
paper's construction also keeps the leader-automaton reactions of Theorem 3.1 (run by the
tokens); as the paper remarks, they are not needed.

The construction is proved correct once for any labelling `r : ℕ → Fin n` satisfying these two
identities (`Leaderless.stablyComputes`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ComposableCRN

namespace Leaderless

/-- Species of the leaderless CRN: input `X`, output `Y`, tokens `T q`. -/
inductive Sp (n : ℕ) where
  | X
  | Y
  | T (q : Fin n)
  deriving DecidableEq

/-- `Sp n ≃ Bool ⊕ Fin n`, for the `Fintype` instance. -/
def Sp.equiv (n : ℕ) : Sp n ≃ Bool ⊕ Fin n where
  toFun
    | .X => .inl true
    | .Y => .inl false
    | .T q => .inr q
  invFun
    | .inl true => .X
    | .inl false => .Y
    | .inr q => .T q
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with (_ | _) | q <;> rfl

instance (n : ℕ) : Fintype (Sp n) := Fintype.ofEquiv _ (Sp.equiv n).symm

variable {n : ℕ} (f : ℕ → ℕ) (r : ℕ → Fin n)

/-- The input reaction `X → f(1) Y + T_{r 1}`. -/
def inR : Reaction (Sp n) where
  reactants := Pi.single .X 1
  products := Pi.single .Y (f 1) + Pi.single (.T (r 1)) 1

/-- The merge reaction `T_a + T_b → (f(a+b) - f(a) - f(b)) Y + T_{r(a+b)}`. -/
def mergeR (a b : Fin n) : Reaction (Sp n) where
  reactants := Pi.single (.T a) 1 + Pi.single (.T b) 1
  products := Pi.single .Y (f ((a : ℕ) + b) - f a - f b) + Pi.single (.T (r ((a : ℕ) + b))) 1

/-- The leaderless CRN. -/
def crn : FunCRN (Sp n) (Fin 1) where
  reactions := {inR f r} ∪ Set.range (fun p : Fin n × Fin n => mergeR f r p.1 p.2)
  finite := (Set.finite_singleton _).union (Set.finite_range _)
  X _ := .X
  Y := .Y
  L := none
  X_injective _ _ _ := Subsingleton.elim _ _
  Y_ne_X _ := by simp
  L_ne_X := by simp
  L_ne_Y := by simp

/-- The configuration in which the blocks `vs` of inputs (out of `x`) have been consumed. -/
def good (x : ℕ) (vs : Multiset ℕ) : Config (Sp n) := fun s =>
  match s with
  | .X => x - vs.sum
  | .Y => (vs.map f).sum
  | .T q => vs.countP (fun v => r v = q)

theorem init_eq (x : Fin 1 → ℕ) : (crn f r).init x = good f r (x 0) 0 := by
  funext s
  cases s <;> simp [FunCRN.init, FunCRN.inputConf, FunCRN.leaderConf, crn, good]

variable {f r}

theorem good_inR (x : ℕ) (vs : Multiset ℕ) :
    good f r x vs - (inR f r).reactants + (inR f r).products = good f r x (1 ::ₘ vs) := by
  funext s
  cases s with
  | X => simp [good, inR]; omega
  | Y => simp [good, inR]; omega
  | T q =>
    simp only [good, inR, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Multiset.countP_cons]
    simp only [Sp.T.injEq, reduceCtorEq, ite_false, eq_comm (a := q)]
    split_ifs <;> omega

theorem le_inR {x : ℕ} {vs : Multiset ℕ} (h : vs.sum < x) : (inR f r).reactants ≤ good f r x vs := by
  intro s
  cases s <;> simp [good, inR]; omega

theorem le_mergeR (x v w : ℕ) (vs : Multiset ℕ) :
    (mergeR f r (r v) (r w)).reactants ≤ good f r x (v ::ₘ w ::ₘ vs) := by
  intro s
  cases s with
  | X => simp [mergeR]
  | Y => simp [mergeR]
  | T q =>
    simp only [good, mergeR, Pi.add_apply, Pi.single_apply, Multiset.countP_cons, Sp.T.injEq,
      eq_comm (a := q)]
    split_ifs <;> omega

theorem terminal_good {x : ℕ} {vs : Multiset ℕ} (hx : vs.sum = x) (hc : Multiset.card vs ≤ 1) :
    (crn f r).Terminal (good f r x vs) := by
  rintro ρ (rfl | ⟨⟨a, b⟩, rfl⟩) hle
  · have := hle .X
    simp [good, inR] at this
    omega
  · have hA := hle (.T a)
    have hB := hle (.T b)
    simp only [good, mergeR, Pi.add_apply, Pi.single_apply, Sp.T.injEq] at hA hB
    obtain h0 | h1 : Multiset.card vs = 0 ∨ Multiset.card vs = 1 := by omega
    · rw [Multiset.card_eq_zero.mp h0] at hA
      simp at hA
    · obtain ⟨v, rfl⟩ := Multiset.card_eq_one.mp h1
      rw [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero] at hA hB
      by_cases hab : a = b
      · subst hab; simp at hA; split_ifs at hA <;> omega
      · split_ifs at hA hB <;> omega

section

variable (hr : ∀ v w, r (v + w) = r ((r v : ℕ) + r w))
  (hD : ∀ v w, f (v + w) + f (r v) + f (r w) = f ((r v : ℕ) + r w) + f v + f w)
  (hsup : ∀ v w, f v + f w ≤ f (v + w))
include hr hD hsup

theorem good_mergeR (x v w : ℕ) (vs : Multiset ℕ) :
    good f r x (v ::ₘ w ::ₘ vs) - (mergeR f r (r v) (r w)).reactants +
      (mergeR f r (r v) (r w)).products = good f r x ((v + w) ::ₘ vs) := by
  funext s
  cases s with
  | X => simp [good, mergeR]; omega
  | Y =>
    have h1 := hD v w
    have h2 := hsup (r v) (r w)
    simp [good, mergeR]; omega
  | T q =>
    simp only [good, mergeR, Pi.add_apply, Pi.sub_apply, Pi.single_apply, Multiset.countP_cons,
      ← hr]
    simp only [Sp.T.injEq, reduceCtorEq, ite_false, eq_comm (a := q)]
    split_ifs <;> omega

theorem reach_final {x : ℕ} (m : ℕ) : ∀ (vs : Multiset ℕ), vs.sum ≤ x →
    2 * (x - vs.sum) + Multiset.card vs = m →
    ∃ vs', (crn f r).Reach (good f r x vs) (good f r x vs') ∧ vs'.sum = x ∧
      Multiset.card vs' ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro vs hle hm
  by_cases hx : vs.sum < x
  · obtain ⟨vs', h1, h2⟩ := ih (2 * (x - (1 ::ₘ vs).sum) + Multiset.card (1 ::ₘ vs))
      (by simp; omega) (1 ::ₘ vs) (by simp; omega) rfl
    exact ⟨vs', CRN.Reach.head ⟨inR f r, .inl rfl, le_inR hx, (good_inR x vs).symm⟩ h1, h2⟩
  by_cases hc : 2 ≤ Multiset.card vs
  · obtain ⟨v, hv⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card vs)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hv
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by simp at hc; omega : 0 < Multiset.card t)
    obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hw
    obtain ⟨vs', h1, h2⟩ := ih (2 * (x - ((v + w) ::ₘ rest).sum) + Multiset.card ((v + w) ::ₘ rest))
      (by simp at hm ⊢; omega) ((v + w) ::ₘ rest)
      (by simp at hle ⊢; omega) rfl
    refine ⟨vs', CRN.Reach.head ⟨mergeR f r (r v) (r w), .inr ⟨⟨r v, r w⟩, rfl⟩,
      le_mergeR x v w rest, (good_mergeR hr hD hsup x v w rest).symm⟩ h1, h2⟩
  · exact ⟨vs, .refl _, by omega, by omega⟩

theorem step_good {x : ℕ} {vs : Multiset ℕ} {D : Config (Sp n)}
    (hs : (crn f r).Step (good f r x vs) D) :
    (vs.sum < x ∧ D = good f r x (1 ::ₘ vs)) ∨
      ∃ v w rest, vs = v ::ₘ w ::ₘ rest ∧ D = good f r x ((v + w) ::ₘ rest) := by
  obtain ⟨ρ, hρ, hle, rfl⟩ := hs
  rcases hρ with rfl | ⟨⟨a, b⟩, rfl⟩
  · have := hle .X
    simp [good, inR] at this
    exact .inl ⟨by omega, good_inR x vs⟩
  · right
    have hA := hle (.T a)
    have hB := hle (.T b)
    simp only [good, mergeR, Pi.add_apply, Pi.single_apply, Sp.T.injEq] at hA hB
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ vs, r v = a :=
      Multiset.countP_pos.mp (by split_ifs at hA <;> omega)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hv
    rw [Multiset.countP_cons] at hB
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ t, r w = b :=
      Multiset.countP_pos.mp (by split_ifs at hB <;> omega)
    obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hw
    exact ⟨v, w, rest, rfl, good_mergeR hr hD hsup x v w rest⟩

/-- Correctness of the leaderless construction for any labelling `r` satisfying the two
identities `hr`, `hD`, for a superadditive `f` with `f 0 = 0`. -/
theorem stablyComputes (h0 : f 0 = 0) : (crn f r).StablyComputes (fun x => f (x 0)) := by
  refine Gadgets.stablyComputes_of_inv _ _
    (fun x D => ∃ vs : Multiset ℕ, vs.sum ≤ x 0 ∧ D = good f r (x 0) vs)
    (fun x => ⟨0, by simp, init_eq f r x⟩) ?_ ?_
  · rintro x D D' ⟨vs, hle, rfl⟩ hs
    rcases step_good hr hD hsup hs with ⟨hlt, rfl⟩ | ⟨v, w, rest, rfl, rfl⟩
    · exact ⟨_, by simp; omega, rfl⟩
    · exact ⟨_, by simp at hle ⊢; omega, rfl⟩
  · rintro x D ⟨vs, hle, rfl⟩
    obtain ⟨vs', h1, h2, h3⟩ := reach_final hr hD hsup _ vs hle rfl
    refine ⟨good f r (x 0) vs', h1, ?_, terminal_good h2 h3⟩
    show (vs'.map f).sum = f (x 0)
    obtain h0' | h1' : Multiset.card vs' = 0 ∨ Multiset.card vs' = 1 := by omega
    · rw [Multiset.card_eq_zero.mp h0'] at h2 ⊢
      simp at h2
      simp [← h2, h0]
    · obtain ⟨v, rfl⟩ := Multiset.card_eq_one.mp h1'
      simp at h2 ⊢
      rw [h2]

end

theorem outputOblivious : (crn f r).OutputOblivious := by
  rintro ρ (rfl | ⟨⟨a, b⟩, rfl⟩) <;> simp [crn, inR, mergeR]

/-! ### The labelling `red` -/

/-- `red m = m` for `m < N + P`, and `N + (m - N) mod P` otherwise. -/
def red (N P m : ℕ) : ℕ := if m < N + P then m else N + (m - N) % P

theorem red_lt {N P : ℕ} (hP : 0 < P) (m : ℕ) : red N P m < N + P := by
  unfold red; split_ifs with h
  · exact h
  · have := Nat.mod_lt (m - N) hP; omega

theorem red_of_ge {N P m : ℕ} (hm : N ≤ m) : red N P m = N + (m - N) % P := by
  unfold red; split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rfl

theorem red_add_mul {N P y : ℕ} (hy : N ≤ y) (k : ℕ) : red N P (y + P * k) = red N P y := by
  rw [red_of_ge hy, red_of_ge (by omega), show y + P * k - N = y - N + P * k by omega,
    Nat.add_mul_mod_self_left]

theorem eq_red_add {N P : ℕ} (m : ℕ) :
    ∃ k, m = red N P m + P * k ∧ (k = 0 ∨ N ≤ red N P m) := by
  by_cases hm : m < N
  · refine ⟨0, ?_, .inl rfl⟩
    simp [red, show m < N + P by omega]
  · push Not at hm
    refine ⟨(m - N) / P, ?_, .inr (by rw [red_of_ge hm]; omega)⟩
    rw [red_of_ge hm]
    have := Nat.mod_add_div (m - N) P
    omega

end Leaderless

open Leaderless in
/-- Theorem 9.2, "⇐": a semilinear superadditive `f : ℕ → ℕ` is obliviously-computable by a
leaderless CRN. We use a simplification of the paper's construction (see the module docstring):
the paper's CRN additionally runs the leader-automaton reactions of Theorem 3.1 on the tokens,
which (as the paper notes) is not needed. -/
theorem theorem_9_2_mpr (f : ℕ → ℕ) (hf : IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2})
    (hsup : ∀ x y, f x + f y ≤ f (x + y)) :
    LeaderlessObliviouslyComputable (fun x : Fin 1 → ℕ => f (x 0)) := by
  have h0 : f 0 = 0 := by have := hsup 0 0; simp at this; omega
  have hmono : Monotone f := fun a b hab => by
    have := hsup a (b - a); rw [Nat.add_sub_cancel' hab] at this; omega
  obtain ⟨N, P, c, hP, hNP⟩ := eventually_affine_of_semilinear_of_monotone f hf hmono
  have hkP : ∀ y ≥ N, ∀ k, f (y + P * k) = f y + k * c := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [show y + P * (k + 1) = y + P * k + P by ring, hNP _ (by omega), ih]; ring
  have hfk : ∀ m, ∃ k, m = red N P m + P * k ∧ f m = f (red N P m) + k * c ∧
      (k = 0 ∨ N ≤ red N P m) := fun m => by
    obtain ⟨k, hk, hk'⟩ := eq_red_add (N := N) (P := P) m
    refine ⟨k, hk, ?_, hk'⟩
    rcases hk' with rfl | hk'
    · simp at hk; rw [← hk]; simp
    · conv_lhs => rw [hk]
      exact hkP _ hk' k
  -- the two identities
  have hkey : ∀ v w, red N P (v + w) = red N P (red N P v + red N P w) ∧
      f (v + w) + f (red N P v) + f (red N P w) =
        f (red N P v + red N P w) + f v + f w := fun v w => by
    obtain ⟨k₁, hv, hfv, hk₁⟩ := hfk v
    obtain ⟨k₂, hw, hfw, hk₂⟩ := hfk w
    by_cases hk : k₁ = 0 ∧ k₂ = 0
    · obtain ⟨rfl, rfl⟩ := hk
      simp only [mul_zero, add_zero] at hv hw
      rw [← hv, ← hw]
      exact ⟨rfl, by ring⟩
    · have hu : N ≤ red N P v + red N P w := by
        rcases hk₁ with rfl | h1
        · rcases hk₂ with rfl | h2
          · exact absurd ⟨rfl, rfl⟩ hk
          · omega
        · omega
      have hvw : v + w = red N P v + red N P w + P * (k₁ + k₂) := by
        rw [mul_add]; linarith
      rw [hvw, red_add_mul hu, hkP _ hu, hfv, hfw]
      exact ⟨rfl, by ring⟩
  let r : ℕ → Fin (N + P) := fun m => ⟨red N P m, red_lt hP m⟩
  have hr : ∀ v w, r (v + w) = r ((r v : ℕ) + r w) := fun v w => Fin.ext (hkey v w).1
  have hD : ∀ v w, f (v + w) + f (r v) + f (r w) = f ((r v : ℕ) + r w) + f v + f w :=
    fun v w => (hkey v w).2
  exact ⟨Sp (N + P), inferInstance, inferInstance, crn f r, rfl, outputOblivious,
    stablyComputes hr hD hsup h0⟩

/-- A function obliviously-computable by a leaderless CRN is stably computable. -/
theorem LeaderlessObliviouslyComputable.stablyComputable {ι : Type} [Fintype ι]
    {f : (ι → ℕ) → ℕ} (h : LeaderlessObliviouslyComputable f) : StablyComputable f := by
  obtain ⟨S, i1, i2, C, -, -, hf⟩ := h
  exact ⟨S, i1, i2, C, hf⟩

/-- **Theorem 9.2.** `f : ℕ → ℕ` is obliviously-computable by a leaderless CRN iff it is
semilinear and superadditive. The "⇒" direction uses Lemma 2.7 (stably computable ⇒ semilinear,
[10]) as a hypothesis and Observation 9.1; "⇐" is `theorem_9_2_mpr`. -/
theorem theorem_9_2 (h27 : StablyComputableImpliesSemilinear) (f : ℕ → ℕ) :
    LeaderlessObliviouslyComputable (fun x : Fin 1 → ℕ => f (x 0)) ↔
      IsSemilinearSet {p : ℕ × ℕ | f p.1 = p.2} ∧ ∀ x y, f x + f y ≤ f (x + y) := by
  refine ⟨fun h => ⟨?_, fun a b => ?_⟩, fun h => theorem_9_2_mpr f h.1 h.2⟩
  · have hs := h27 (Fin 1) _ h.stablyComputable
    let φ : (Fin 1 → ℕ) × ℕ →+ ℕ × ℕ :=
      { toFun := fun p => (p.1 0, p.2), map_zero' := rfl, map_add' := fun _ _ => rfl }
    convert hs.image φ using 1
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists]
    constructor
    · rintro rfl
      exact ⟨fun _ => a, f a, rfl, rfl⟩
    · rintro ⟨x, y, hxy, hφ⟩
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq] at hφ
      rw [← hφ.1, ← hφ.2]; exact hxy
  · simpa using h.superadditive (fun _ => a) (fun _ => b)

end Podc.ComposableCRN
