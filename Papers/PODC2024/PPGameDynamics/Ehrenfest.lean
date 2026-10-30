import Mathlib
import Podc.Probability.Markov.Stationary

/-!
# High-dimensional weighted Ehrenfest processes (Section 2.3 and Appendix A of the paper)

[Alistarh, Chatterjee, Karrabi, Lazarsfeld, *Game Dynamics and Equilibrium Computation in the
Population Protocol Model*, PODC 2024]

The state space is `Δ_k^m = {x ∈ ℕ^k : ∑ x_i = m}` (`Simplex k m`); urns are indexed by `Fin k`,
i.e. urn `j` of the paper is `⟨j - 1, _⟩` here. We first treat a general *urn chain*
(`urnKernel r m`): with probability `r i j · x_i / m` a ball moves from urn `i` to urn `j`
(`Simplex.move`), otherwise the state is unchanged. The `(k, a, b, m)`-Ehrenfest process of
Definition 2.3 is the urn chain with nearest-neighbour rates `a` (up) and `b` (down)
(`ehrenfest`); `ehrenfest_apply_up/down/self/other` check that its entries are exactly those of
Definition 2.3.

* `urnKernel_detailedBalance`: if the rates are reversible w.r.t. `p` (`p i r i j = p j r j i`),
  the multinomial distribution with parameters `m, p` satisfies detailed balance;
* `theorem_2_4`: Theorem 2.4 — the (unique) stationary distribution of the
  `(k, a, b, m)`-Ehrenfest process is multinomial with `p_j ∝ λ^(j-1)`, `λ = a / b`;
* `proposition_A_1` / `remark_A_2` (`k = 2`) and `remark_A_4` (`k = 3`): the special cases.
-/

open Finset Matrix Cslib.Probability.Markov

namespace Podc.PPGameDynamics

/-- The discrete simplex `Δ_k^m = {x ∈ ℕ^k : ∑ x_i = m}`. -/
abbrev Simplex (k m : ℕ) := {x : Fin k → ℕ // ∑ i, x i = m}

instance (k m : ℕ) : Fintype (Simplex k m) :=
  Fintype.subtype ((univ : Finset (Fin k)).piAntidiag m) (by simp [mem_piAntidiag])

variable {k m : ℕ}

namespace Simplex

/-- Move one ball from urn `i` to urn `j` (the identity if urn `i` is empty or `i = j`). -/
def move (x : Simplex k m) (i j : Fin k) : Simplex k m :=
  if h : 0 < x.1 i ∧ i ≠ j then
    ⟨fun l => x.1 l + (if l = j then 1 else 0) - (if l = i then 1 else 0), by
      have hl : ∀ l, (x.1 l + (if l = j then 1 else 0) - (if l = i then 1 else 0)) +
          (if l = i then 1 else 0) = x.1 l + (if l = j then 1 else 0) := by
        intro l
        split_ifs with h1 h2 <;> subst_vars <;> omega
      have h2 := Finset.sum_congr (s₁ := (univ : Finset (Fin k))) rfl fun l _ => hl l
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, x.2] at h2
      simp at h2
      omega⟩
  else x

lemma move_val (x : Simplex k m) {i j : Fin k} (h : 0 < x.1 i) (hij : i ≠ j) (l : Fin k) :
    (x.move i j).1 l = x.1 l + (if l = j then 1 else 0) - (if l = i then 1 else 0) := by
  simp [move, h, hij]

lemma move_of_not (x : Simplex k m) {i j : Fin k} (h : ¬ (0 < x.1 i ∧ i ≠ j)) :
    x.move i j = x := by
  simp [move, h]

/-- Coordinates of a genuine move. -/
lemma move_val_add (x : Simplex k m) {i j : Fin k} (h : 0 < x.1 i) (hij : i ≠ j) (l : Fin k) :
    (x.move i j).1 l + (if l = i then 1 else 0) = x.1 l + (if l = j then 1 else 0) := by
  rw [move_val x h hij]
  split_ifs with h1 h2 <;> subst_vars <;> omega

lemma move_ne (x : Simplex k m) {i j : Fin k} (h : 0 < x.1 i) (hij : i ≠ j) : x.move i j ≠ x := by
  intro he
  have := move_val_add x h hij j
  rw [he] at this
  simp [hij.symm] at this

/-- If a move from `x` gives `y ≠ x`, then it is a genuine move. -/
lemma genuine_of_move_eq {x y : Simplex k m} {i j : Fin k} (h : x.move i j = y) (hxy : x ≠ y) :
    0 < x.1 i ∧ i ≠ j := by
  by_contra hc
  rw [move_of_not x hc] at h
  exact hxy h

/-- Moves are reversible. -/
lemma move_eq_iff {x y : Simplex k m} (hxy : x ≠ y) (i j : Fin k) :
    x.move i j = y ↔ y.move j i = x := by
  suffices H : ∀ {x y : Simplex k m} (i j : Fin k), x ≠ y → x.move i j = y → y.move j i = x from
    ⟨H i j hxy, H j i (Ne.symm hxy)⟩
  intro x y i j hxy h
  obtain ⟨hi, hij⟩ := genuine_of_move_eq h hxy
  have hy := move_val_add x hi hij
  rw [h] at hy
  have hyj : 0 < y.1 j := by have := hy j; simp [hij.symm] at this; omega
  apply Subtype.ext
  funext l
  rw [move_val y hyj hij.symm]
  have := hy l
  split_ifs at this ⊢ <;> omega

end Simplex

/-! ## Urn chains -/

/-- The urn chain on `Δ_k^m` with rates `r`: from `x`, a ball moves from urn `i` to urn `j` with
probability `r i j * x_i / m`; with the remaining probability the state stays. -/
noncomputable def urnKernel (r : Fin k → Fin k → ℝ) (m : ℕ) :
    Matrix (Simplex k m) (Simplex k m) ℝ :=
  fun x y => (if y = x then 1 else 0) +
    ∑ i, ∑ j, r i j * (x.1 i / m) * ((if x.move i j = y then 1 else 0) - (if y = x then 1 else 0))

lemma urnKernel_mulVec (r : Fin k → Fin k → ℝ) (g : Simplex k m → ℝ) (x : Simplex k m) :
    (urnKernel r m *ᵥ g) x = g x + ∑ i, ∑ j, r i j * (x.1 i / m) * (g (x.move i j) - g x) := by
  simp only [mulVec, dotProduct, urnKernel, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, ← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma urnKernel_offDiag (r : Fin k → Fin k → ℝ) {x y : Simplex k m} (hxy : x ≠ y) :
    urnKernel r m x y = ∑ i, ∑ j, if x.move i j = y then r i j * (x.1 i / m) else 0 := by
  simp [urnKernel, Ne.symm hxy]

lemma urnKernel_nonneg {r : Fin k → Fin k → ℝ} (hr0 : ∀ i j, 0 ≤ r i j)
    (hr1 : ∀ i, ∑ j, r i j ≤ 1) (x y : Simplex k m) : 0 ≤ urnKernel r m x y := by
  have hxm : ∀ i, 0 ≤ (x.1 i : ℝ) / m := fun i => by positivity
  by_cases hxy : x = y
  · subst hxy
    simp only [urnKernel, ite_true]
    have hle : ∀ i j, -(r i j * (x.1 i / m)) ≤
        r i j * (x.1 i / m) * ((if x.move i j = x then 1 else 0) - 1) := by
      intro i j
      have := mul_nonneg (hr0 i j) (hxm i)
      split_ifs <;> nlinarith
    have hsum : ∑ i, ∑ j, r i j * (x.1 i / m) ≤ 1 := by
      calc ∑ i, ∑ j, r i j * (x.1 i / m) = ∑ i, (∑ j, r i j) * (x.1 i / m) := by
            simp [Finset.sum_mul]
        _ ≤ ∑ i, (x.1 i : ℝ) / m :=
            Finset.sum_le_sum fun i _ => by nlinarith [hr1 i, hxm i]
        _ ≤ 1 := by
            rw [← Finset.sum_div]
            rcases Nat.eq_zero_or_pos m with hm | hm
            · simp [hm]
            · rw [div_le_one (by exact_mod_cast hm)]
              exact_mod_cast x.2.le
    have := Finset.sum_le_sum fun i (_ : i ∈ univ) => Finset.sum_le_sum fun j (_ : j ∈ univ) =>
      hle i j
    simp only [Finset.sum_neg_distrib] at this
    linarith
  · rw [urnKernel_offDiag r hxy]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact mul_nonneg (hr0 i j) (hxm i)
    · exact le_rfl

/-- Urn chains with nonnegative rates of total `≤ 1` per urn are row-stochastic. -/
theorem urnKernel_mem {r : Fin k → Fin k → ℝ} (hr0 : ∀ i j, 0 ≤ r i j)
    (hr1 : ∀ i, ∑ j, r i j ≤ 1) : urnKernel r m ∈ rowStochastic ℝ (Simplex k m) := by
  refine ⟨urnKernel_nonneg hr0 hr1, ?_⟩
  funext x
  rw [urnKernel_mulVec]
  simp

/-! ## The multinomial distribution -/

/-- The multinomial PMF with parameters `m` and `p`:
`ν(x) = m! / (x_1! ⋯ x_k!) · p_1^{x_1} ⋯ p_k^{x_k}`. -/
noncomputable def multinomialPMF (p : Fin k → ℝ) (x : Simplex k m) : ℝ :=
  (Nat.multinomial univ x.1 : ℝ) * ∏ i, p i ^ x.1 i

lemma multinomialPMF_eq (p : Fin k → ℝ) (x : Simplex k m) :
    multinomialPMF p x = (m.factorial : ℝ) * ∏ i, (p i ^ x.1 i / (x.1 i).factorial) := by
  have hspec := Nat.multinomial_spec (univ : Finset (Fin k)) x.1
  rw [x.2] at hspec
  have hspec' : (∏ i, ((x.1 i).factorial : ℝ)) * (Nat.multinomial univ x.1 : ℝ) =
      (m.factorial : ℝ) := by exact_mod_cast hspec
  have hpos : (∏ i, ((x.1 i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => by positivity
  rw [multinomialPMF, Finset.prod_div_distrib, ← hspec']
  field_simp

lemma sum_multinomialPMF (p : Fin k → ℝ) :
    ∑ x : Simplex k m, multinomialPMF p x = (∑ i, p i) ^ m := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  exact (Finset.sum_subtype ((univ : Finset (Fin k)).piAntidiag m)
    (p := fun x : Fin k → ℕ => ∑ i, x i = m) (fun x => by simp [mem_piAntidiag])
    (fun x => (Nat.multinomial univ x : ℝ) * ∏ i, p i ^ x i)).symm

lemma multinomialPMF_pos {p : Fin k → ℝ} (hp : ∀ i, 0 < p i) (x : Simplex k m) :
    0 < multinomialPMF p x := by
  unfold multinomialPMF
  have := Nat.multinomial_pos (univ : Finset (Fin k)) x.1
  have := Finset.prod_pos fun i (_ : i ∈ (univ : Finset (Fin k))) => pow_pos (hp i) (x.1 i)
  positivity

lemma isDistribution_multinomialPMF {p : Fin k → ℝ} (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    IsDistribution (multinomialPMF (m := m) p) := by
  refine ⟨fun x => ?_, by rw [sum_multinomialPMF, h1, one_pow]⟩
  unfold multinomialPMF
  have : ∀ i ∈ (univ : Finset (Fin k)), 0 ≤ p i ^ x.1 i := fun i _ => pow_nonneg (hp i) _
  have := Finset.prod_nonneg this
  positivity

/-- The ratio of multinomial masses across one move `i → j`:
`ν(y) · y_j · p_i = ν(x) · x_i · p_j` for `y = x - e_i + e_j`. -/
lemma multinomialPMF_move (p : Fin k → ℝ) (x : Simplex k m) {i j : Fin k} (hi : 0 < x.1 i)
    (hij : i ≠ j) :
    multinomialPMF p (x.move i j) * (x.move i j).1 j * p i =
      multinomialPMF p x * x.1 i * p j := by
  set y := x.move i j
  have hy := Simplex.move_val_add x hi hij
  have hyj : y.1 j = x.1 j + 1 := by have := hy j; simp [hij.symm] at this; omega
  have hyi : y.1 i + 1 = x.1 i := by have := hy i; simp [hij] at this; omega
  have hyl : ∀ l, l ≠ i → l ≠ j → y.1 l = x.1 l := by
    intro l h1 h2; have := hy l; simp [h1, h2] at this; omega
  let f : Fin k → ℕ → ℝ := fun l n => p l ^ n / n.factorial
  -- pointwise identity
  have hpt : ∀ l, f l (y.1 l) * ((if l = j then (y.1 j : ℝ) else 1) * (if l = i then p i else 1)) =
      f l (x.1 l) * ((if l = i then (x.1 i : ℝ) else 1) * (if l = j then p j else 1)) := by
    intro l
    by_cases hli : l = i
    · subst hli
      simp only [hij, ↓reduceIte, one_mul, mul_one, f]
      rw [← hyi, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    · by_cases hlj : l = j
      · subst hlj
        simp only [hli, ↓reduceIte, one_mul, mul_one, f]
        rw [hyj, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp
      · simp [hli, hlj, hyl l hli hlj]
  have hprod := congrArg (fun g => ∏ l, g l) (funext hpt)
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true] at hprod
  simp only [f] at hprod
  rw [multinomialPMF_eq, multinomialPMF_eq]
  calc (m.factorial : ℝ) * (∏ l, p l ^ y.1 l / ((y.1 l).factorial : ℝ)) * (y.1 j : ℝ) * p i
      = (m.factorial : ℝ) * ((∏ l, p l ^ y.1 l / ((y.1 l).factorial : ℝ)) * ((y.1 j : ℝ) * p i)) := by
        ring
    _ = (m.factorial : ℝ) * ((∏ l, p l ^ x.1 l / ((x.1 l).factorial : ℝ)) * ((x.1 i : ℝ) * p j)) := by
        rw [hprod]
    _ = _ := by ring

/-- **Detailed balance for urn chains.** If the rates are reversible with respect to `p`
(`p i * r i j = p j * r j i`), then the multinomial distribution with parameters `m, p`
satisfies the detailed balance equations of `urnKernel r m`. -/
theorem urnKernel_detailedBalance {r : Fin k → Fin k → ℝ} {p : Fin k → ℝ} (hp : ∀ i, 0 < p i)
    (hrev : ∀ i j, p i * r i j = p j * r j i) :
    DetailedBalance (urnKernel r m) (multinomialPMF p) := by
  intro x y
  by_cases hxy : x = y
  · subst hxy; rfl
  rw [urnKernel_offDiag r hxy, urnKernel_offDiag r (Ne.symm hxy)]
  simp_rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hm : x.move i j = y
  · have hm' := (Simplex.move_eq_iff hxy i j).1 hm
    simp only [hm, hm', ↓reduceIte]
    obtain ⟨hi, hij⟩ := Simplex.genuine_of_move_eq hm hxy
    have key := multinomialPMF_move p x hi hij
    rw [hm] at key
    have hpi := hp i
    have h2 := hrev i j
    -- π(x) r_ij x_i = π(y) r_ji y_j
    have : multinomialPMF p x * (r i j * x.1 i) = multinomialPMF p y * (r j i * y.1 j) := by
      have e1 : multinomialPMF p x * (r i j * x.1 i) * p i =
          multinomialPMF p y * (r j i * y.1 j) * p i := by
        calc multinomialPMF p x * (r i j * x.1 i) * p i
            = multinomialPMF p x * x.1 i * (p i * r i j) := by ring
          _ = multinomialPMF p x * x.1 i * p j * r j i := by rw [h2]; ring
          _ = multinomialPMF p y * y.1 j * p i * r j i := by rw [key]
          _ = _ := by ring
      exact mul_right_cancel₀ hpi.ne' e1
    calc multinomialPMF p x * (r i j * (x.1 i / m))
        = multinomialPMF p x * (r i j * x.1 i) / m := by ring
      _ = multinomialPMF p y * (r j i * y.1 j) / m := by rw [this]
      _ = _ := by ring
  · have hm' : ¬ y.move j i = x := fun h => hm ((Simplex.move_eq_iff hxy i j).2 h)
    simp only [hm, hm', ↓reduceIte, mul_zero]

/-! ## The `(k, a, b, m)`-Ehrenfest process (Definition 2.3) -/

/-- Nearest-neighbour rates: up (`j → j + 1`) with weight `a`, down (`j + 1 → j`) with weight
`b`. -/
def ehrRate (a b : ℝ) (i j : Fin k) : ℝ :=
  if j.val = i.val + 1 then a else if i.val = j.val + 1 then b else 0

/-- **Definition 2.3.** The transition matrix of the `(k, a, b, m)`-Ehrenfest process. -/
noncomputable def ehrenfest (k : ℕ) (a b : ℝ) (m : ℕ) : Matrix (Simplex k m) (Simplex k m) ℝ :=
  urnKernel (ehrRate (k := k) a b) m

lemma ehrRate_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : Fin k) : 0 ≤ ehrRate a b i j := by
  unfold ehrRate; split_ifs <;> first | assumption | exact le_rfl

lemma sum_ehrRate_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (i : Fin k) :
    ∑ j, ehrRate a b i j ≤ 1 := by
  have h1 : ∀ j, ehrRate a b i j ≤ (if j.val = i.val + 1 then a else 0) +
      (if i.val = j.val + 1 then b else 0) := by
    intro j; unfold ehrRate; split_ifs <;> linarith
  have hcard : ∀ (P : Fin k → Prop) [DecidablePred P], (∀ j j', P j → P j' → j = j') →
      (univ.filter P).card ≤ 1 := fun P _ h => Finset.card_le_one.2 fun j hj j' hj' =>
        h j j' (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2
  have hA : ∑ j : Fin k, (if j.val = i.val + 1 then a else 0) ≤ a := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have := hcard (fun j : Fin k => j.val = i.val + 1) (fun j j' h h' => Fin.ext (by omega))
    have : ((univ.filter fun j : Fin k => j.val = i.val + 1).card : ℝ) ≤ 1 := by exact_mod_cast this
    nlinarith
  have hB : ∑ j : Fin k, (if i.val = j.val + 1 then b else 0) ≤ b := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have := hcard (fun j : Fin k => i.val = j.val + 1) (fun j j' h h' => Fin.ext (by omega))
    have : ((univ.filter fun j : Fin k => i.val = j.val + 1).card : ℝ) ≤ 1 := by exact_mod_cast this
    nlinarith
  calc ∑ j, ehrRate a b i j ≤ ∑ j : Fin k, ((if j.val = i.val + 1 then a else 0) +
      (if i.val = j.val + 1 then b else 0)) := Finset.sum_le_sum fun j _ => h1 j
    _ ≤ 1 := by rw [Finset.sum_add_distrib]; linarith

/-- The Ehrenfest matrix is row-stochastic (this is where `a + b ≤ 1` is used). -/
theorem ehrenfest_mem {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    ehrenfest k a b m ∈ rowStochastic ℝ (Simplex k m) :=
  urnKernel_mem (ehrRate_nonneg ha hb) (sum_ehrRate_le ha hb hab)

/-! ### Entries of the urn chain and of the Ehrenfest matrix -/

/-- Genuine moves are determined by their result. -/
lemma Simplex.move_inj (x : Simplex k m) {i j i' j' : Fin k} (hi : 0 < x.1 i) (hij : i ≠ j)
    (h : x.move i' j' = x.move i j) : i' = i ∧ j' = j := by
  obtain ⟨hi', hij'⟩ := genuine_of_move_eq h (x.move_ne hi hij).symm
  have e1 := x.move_val_add hi hij
  have e2 := x.move_val_add hi' hij'
  rw [h] at e2
  have key : ∀ t, ((if t = i' then 1 else 0) : ℤ) - (if t = j' then 1 else 0) =
      (if t = i then 1 else 0) - (if t = j then 1 else 0) := by
    intro t
    have a1 := e1 t; have a2 := e2 t
    split_ifs at a1 a2 ⊢ <;> omega
  constructor
  · by_contra hne
    have := key i'
    simp only [hij', hne, ↓reduceIte] at this
    split_ifs at this <;> simp at this
  · by_contra hne
    have := key j'
    simp only [hij'.symm, hne, ↓reduceIte] at this
    split_ifs at this <;> simp at this

/-- The probability of a genuine move `i → j` is `r i j · x_i / m`. -/
theorem urnKernel_move (r : Fin k → Fin k → ℝ) (x : Simplex k m) {i j : Fin k} (hi : 0 < x.1 i)
    (hij : i ≠ j) : urnKernel r m x (x.move i j) = r i j * (x.1 i / m) := by
  rw [urnKernel_offDiag r (Ne.symm (x.move_ne hi hij))]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    rw [ite_eq_right]
    intro h
    exact hj' (x.move_inj hi hij h).2
  · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [ite_eq_right]
    intro h
    exact hi' (x.move_inj hi hij h).1
  · simp

/-- Off-diagonal positive entries of the urn chain come from moves. -/
lemma urnKernel_eq_zero_of_not_move (r : Fin k → Fin k → ℝ) {x y : Simplex k m} (hxy : x ≠ y)
    (h : ∀ i j, x.move i j ≠ y) : urnKernel r m x y = 0 := by
  rw [urnKernel_offDiag r hxy]
  simp [h]

/-- Diagonal entries of the urn chain when `r i i = 0`. -/
lemma urnKernel_self {r : Fin k → Fin k → ℝ} (hr : ∀ i, r i i = 0) (x : Simplex k m) :
    urnKernel r m x x = 1 - ∑ i, ∑ j, r i j * (x.1 i / m) := by
  simp only [urnKernel, ↓reduceIte]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : 0 < x.1 i ∧ i ≠ j
  · simp [x.move_ne h.1 h.2]
  · rcases not_and_or.1 h with h | h
    · have : x.1 i = 0 := by omega
      simp [this]
    · push Not at h; subst h; simp [hr]

variable {a b : ℝ}

/-- Def. 2.3, first line: `P(x, x - e_j + e_{j+1}) = a · x_j / m`. -/
theorem ehrenfest_apply_up (x : Simplex k m) {j j' : Fin k} (hj : j'.val = j.val + 1)
    (hx : 0 < x.1 j) : ehrenfest k a b m x (x.move j j') = a * (x.1 j / m) := by
  have hne : j ≠ j' := fun h => by subst h; omega
  rw [ehrenfest, urnKernel_move _ x hx hne, ehrRate, ite_eq_left hj]

/-- Def. 2.3, second line: `P(x, x + e_j - e_{j+1}) = b · x_{j+1} / m`. -/
theorem ehrenfest_apply_down (x : Simplex k m) {j j' : Fin k} (hj : j'.val = j.val + 1)
    (hx : 0 < x.1 j') : ehrenfest k a b m x (x.move j' j) = b * (x.1 j' / m) := by
  have hne : j' ≠ j := fun h => by subst h; omega
  rw [ehrenfest, urnKernel_move _ x hx hne, ehrRate, ite_eq_right (by omega), ite_eq_left hj]

/-- Def. 2.3, third line: `P(x, x) = 1 - ∑_{j ∈ [k-1]} (a x_j / m + b x_{j+1} / m)`. -/
theorem ehrenfest_apply_self (x : Simplex k m) :
    ehrenfest k a b m x x = 1 - ∑ j : Fin k, ∑ j' : Fin k,
      if j'.val = j.val + 1 then a * (x.1 j / m) + b * (x.1 j' / m) else 0 := by
  rw [ehrenfest, urnKernel_self (fun i => by simp [ehrRate])]
  congr 1
  have h : ∀ i j : Fin k, ehrRate a b i j * (x.1 i / m) =
      (if j.val = i.val + 1 then a * (x.1 i / m) else 0) +
      (if i.val = j.val + 1 then b * (x.1 i / m) else 0) := by
    intro i j; unfold ehrRate; split_ifs <;> first | (exfalso; omega) | ring
  simp_rw [h, Finset.sum_add_distrib]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Def. 2.3, last line: all other transitions have probability `0`. -/
theorem ehrenfest_apply_other {x y : Simplex k m} (hxy : x ≠ y)
    (h : ∀ j j' : Fin k, j'.val = j.val + 1 → x.move j j' ≠ y ∧ x.move j' j ≠ y) :
    ehrenfest k a b m x y = 0 := by
  rw [ehrenfest, urnKernel_offDiag _ hxy]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hm
  · unfold ehrRate
    split_ifs with h1 h2
    · exact absurd hm (h i j h1).1
    · exact absurd hm (h j i h2).2
    · simp
  · rfl

/-! ### Stationarity and uniqueness -/

/-- The parameters `p_j = λ^(j-1) / ∑_i λ^(i-1)` of Theorem 2.4 (urns indexed from `0`). -/
noncomputable def ehrParam (k : ℕ) (lam : ℝ) (j : Fin k) : ℝ :=
  lam ^ j.val / ∑ i : Fin k, lam ^ i.val

lemma ehrParam_pos {lam : ℝ} (hk : 0 < k) (hl : 0 < lam) (j : Fin k) : 0 < ehrParam k lam j := by
  unfold ehrParam
  have : 0 < ∑ i : Fin k, lam ^ i.val :=
    Finset.sum_pos (fun i _ => pow_pos hl _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  positivity

lemma sum_ehrParam {lam : ℝ} (hk : 0 < k) (hl : 0 < lam) : ∑ j, ehrParam k lam j = 1 := by
  unfold ehrParam
  have : 0 < ∑ i : Fin k, lam ^ i.val :=
    Finset.sum_pos (fun i _ => pow_pos hl _) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  rw [← Finset.sum_div, div_self this.ne']

/-- The nearest-neighbour rates are reversible w.r.t. `p_j ∝ (a/b)^j`. -/
lemma ehrRate_reversible (hb : 0 < b) (i j : Fin k) :
    ehrParam k (a / b) i * ehrRate a b i j = ehrParam k (a / b) j * ehrRate a b j i := by
  unfold ehrParam ehrRate
  split_ifs with h1 h2 h3 <;> try omega
  · rw [h1, pow_succ]; field_simp
  · rw [h3, pow_succ]; field_simp
  · simp

/-- The multinomial distribution of Theorem 2.4 satisfies detailed balance. -/
theorem ehrenfest_detailedBalance (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    DetailedBalance (ehrenfest k a b m) (multinomialPMF (ehrParam k (a / b))) :=
  urnKernel_detailedBalance (ehrParam_pos hk (div_pos ha hb)) (ehrRate_reversible hb)

/-- The multinomial distribution of Theorem 2.4 is stationary. -/
theorem ehrenfest_isStationary (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) (hk : 0 < k) :
    IsStationary (ehrenfest k a b m) (multinomialPMF (ehrParam k (a / b))) :=
  isStationary_of_detailedBalance (ehrenfest_mem ha.le hb.le hab) (ehrenfest_detailedBalance ha hb hk)

/-- All balls in the first urn. -/
def Simplex.base (hk : 0 < k) : Simplex k m :=
  ⟨Pi.single ⟨0, hk⟩ m, by simp⟩

/-- The potential `∑_l l · x_l`. -/
def Simplex.pot (x : Simplex k m) : ℕ := ∑ l, l.val * x.1 l

lemma Simplex.eq_base_of_pot (hk : 0 < k) (x : Simplex k m) (h : x.pot = 0) : x = Simplex.base hk := by
  have hz : ∀ l : Fin k, l ≠ ⟨0, hk⟩ → x.1 l = 0 := by
    intro l hl
    have := (Finset.sum_eq_zero_iff.1 h) l (Finset.mem_univ _)
    rcases Nat.mul_eq_zero.1 this with h0 | h0
    · exact absurd (Fin.ext h0) hl
    · exact h0
  have h0 : x.1 ⟨0, hk⟩ = m := by
    have := x.2
    rwa [Finset.sum_eq_single ⟨0, hk⟩ (fun l _ hl => hz l hl) (by simp)] at this
  apply Subtype.ext
  funext l
  by_cases hl : l = ⟨0, hk⟩
  · subst hl; simp [Simplex.base, h0]
  · simp [Simplex.base, hz l hl, hl]

lemma Simplex.pot_move (x : Simplex k m) {i j : Fin k} (hi : 0 < x.1 i) (hij : i ≠ j) :
    (x.move i j).pot + i.val = x.pot + j.val := by
  have h := x.move_val_add hi hij
  have := Finset.sum_congr (s₁ := (univ : Finset (Fin k))) rfl fun l _ =>
    congrArg (fun n => l.val * n) (h l)
  simp only [Nat.mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  exact this

/-- Every state of the Ehrenfest process reaches the base state (`b > 0`). -/
lemma ehrenfest_reach_base (hb : 0 < b) (hk : 0 < k) :
    ∀ x : Simplex k m, Relation.ReflTransGen (fun u v => 0 < ehrenfest k a b m u v) x
      (Simplex.base hk) := by
  suffices H : ∀ n, ∀ x : Simplex k m, x.pot = n →
      Relation.ReflTransGen (fun u v => 0 < ehrenfest k a b m u v) x (Simplex.base hk) from
    fun x => H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases hall : ∀ l : Fin k, l.val ≠ 0 → x.1 l = 0
    · have : x.pot = 0 := Finset.sum_eq_zero fun l _ => by
        by_cases hl : l.val = 0
        · simp [hl]
        · simp [hall l hl]
      rw [x.eq_base_of_pot hk this]
    · push Not at hall
      obtain ⟨l, hl0, hxl⟩ := hall
      have hxl' : 0 < x.1 l := Nat.pos_of_ne_zero hxl
      let l' : Fin k := ⟨l.val - 1, by omega⟩
      have hll' : l ≠ l' := fun h => by
        have := congrArg Fin.val h; simp [l'] at this; omega
      have hm : 0 < m := by
        have := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
        rw [x.2] at this; omega
      have hstep : 0 < ehrenfest k a b m x (x.move l l') := by
        have hj : l.val = l'.val + 1 := by simp [l']; omega
        have := ehrenfest_apply_down (a := a) (b := b) x hj hxl'
        rw [this]
        have : (0 : ℝ) < x.1 l := by exact_mod_cast hxl'
        positivity
      have hpot := x.pot_move hxl' hll'
      have hl'v : l'.val = l.val - 1 := rfl
      have hlt : (x.move l l').pot < n := by omega
      exact Relation.ReflTransGen.head hstep (ih _ hlt _ rfl)

/-- The `(k, a, b, m)`-Ehrenfest process is irreducible (`a, b > 0`). -/
theorem ehrenfest_isIrreducible (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    IsIrreducibleChain (ehrenfest k a b m) :=
  isIrreducibleChain_of_symm
    (fun _ _ h => (ehrenfest_detailedBalance ha hb hk).pos_symm
      (multinomialPMF_pos (ehrParam_pos hk (div_pos ha hb))) h)
    (Simplex.base hk) (ehrenfest_reach_base hb hk)

/-- Uniqueness and identification of the stationary distribution, for all `k ≥ 1`, `m ≥ 0`. -/
theorem ehrenfest_stationary_unique (hk : 0 < k) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (π : Simplex k m → ℝ) (hπ : IsDistribution π) (hstat : IsStationary (ehrenfest k a b m) π) :
    π = multinomialPMF (ehrParam k (a / b)) :=
  IsStationary.unique (fun _ _ => nonneg_of_mem_rowStochastic (ehrenfest_mem ha.le hb.le hab))
    (ehrenfest_isIrreducible ha hb hk) hπ hstat
    (isDistribution_multinomialPMF (fun j => (ehrParam_pos hk (div_pos ha hb) j).le)
      (sum_ehrParam hk (div_pos ha hb)))
    (ehrenfest_isStationary ha hb hab hk)

/-- **Theorem 2.4.** Fix `a, b > 0` with `a + b ≤ 1` and let `λ = a / b`. For `k, m ≥ 2`, let `π`
be the stationary distribution of the `(k, a, b, m)`-Ehrenfest process. Then `π` is multinomial
with parameters `m` and `p_j = λ^(j-1) / ∑_{i=1}^k λ^(i-1)` (urn `j` of the paper is index `j - 1`
here). The multinomial distribution is stationary (`ehrenfest_isStationary`), and it is the only
stationary distribution (this theorem). (It holds for all `k ≥ 1`, `m ≥ 0`:
`ehrenfest_stationary_unique`.) -/
theorem theorem_2_4 (hk : 2 ≤ k) (_hm : 2 ≤ m) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (π : Simplex k m → ℝ) (hπ : IsDistribution π) (hstat : IsStationary (ehrenfest k a b m) π) :
    π = multinomialPMF (ehrParam k (a / b)) :=
  ehrenfest_stationary_unique (by omega) ha hb hab π hπ hstat

end Podc.PPGameDynamics
