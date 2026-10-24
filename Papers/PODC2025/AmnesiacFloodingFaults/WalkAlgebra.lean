import Mathlib

/-!
# Additive functionals along walks; cycles and faux-even cycles span closed walks

Pure graph theory used by the termination dichotomy (Theorem 5.1) of
Austin–Gadouleau–Mertzios–Trehan, *Amnesiac Flooding: Easy to Break, Difficult to Escape*
(PODC 2025, arXiv 2502.06001).

For edge weights `g` (antisymmetric) and `o` (symmetric) we consider
* `walkFlow g p = Σ_k g(w_k, w_{k+1})` and
* `walkSig o p = Σ_k (-1)^k o(w_k, w_{k+1})`
along a walk `p = w_0 w_1 … w_ℓ`.

A faux-even cycle (`FEC`, Definition 5.1 of the paper) is a pair of odd cycles which either share
exactly one vertex, or are vertex-disjoint and joined by a path meeting them only at its endpoints.
`FEC.walk` is the closed walk `c₁ ++ p ++ c₂ ++ p⁻¹`, which traverses the paper's "even cycle
representation" `H²` (Definition 5.2).

Main results:
* `walkFlow_eq_zero_of_isCycle`: if `walkFlow g` vanishes on all cycles, it vanishes on all closed
  walks.
* `walkSig_eq_zero_of_isCycle_of_fec`: if `walkSig o` vanishes on all even cycles and on all
  faux-even cycles, it vanishes on all closed walks of even length. (This is the spanning property
  of the circuits of the signed-graphic matroid of the all-negative signed graph.)
-/

namespace AmnesiacFloodingFaults

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `walkSig o p = Σ_k (-1)^k o(w_k, w_{k+1})` along the walk `p = w_0 … w_ℓ`. -/
def walkSig (o : V → V → ℤ) : ∀ {u v : V}, G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := w) _ p => o u w - walkSig o p

/-- `walkFlow g p = Σ_k g(w_k, w_{k+1})` along the walk `p = w_0 … w_ℓ`. -/
def walkFlow (g : V → V → ℤ) : ∀ {u v : V}, G.Walk u v → ℤ
  | _, _, .nil => 0
  | u, _, .cons (v := w) _ p => g u w + walkFlow g p

variable (G) in
/-- A faux-even cycle (Definition 5.1): odd cycles `c₁` (at `u`) and `c₂` (at `v`) joined by a
path `p` from `u` to `v`. Either `p` is trivial and the cycles share exactly the vertex `u = v`, or
`p` is nontrivial, the cycles are vertex-disjoint, and `p` meets `c₁` only at `u` and `c₂` only
at `v`. -/
structure FEC where
  /-- The junction vertex on the first cycle. -/
  u : V
  /-- The junction vertex on the second cycle. -/
  v : V
  /-- The first odd cycle, based at `u`. -/
  c₁ : G.Walk u u
  /-- The connecting path. -/
  p : G.Walk u v
  /-- The second odd cycle, based at `v`. -/
  c₂ : G.Walk v v
  isCycle₁ : c₁.IsCycle
  isCycle₂ : c₂.IsCycle
  odd₁ : Odd c₁.length
  odd₂ : Odd c₂.length
  isPath : p.IsPath
  inter₁₂ : ∀ x, x ∈ c₁.support → x ∈ c₂.support → p.length = 0 ∧ x = u
  inter₁ : ∀ x ∈ p.support, x ∈ c₁.support → x = u
  inter₂ : ∀ x ∈ p.support, x ∈ c₂.support → x = v

/-- The closed walk `c₁ ++ p ++ c₂ ++ p⁻¹` around the even cycle representation of a faux-even
cycle (Definition 5.2). -/
def FEC.walk (F : FEC G) : G.Walk F.u F.u :=
  F.c₁.append (F.p.append (F.c₂.append F.p.reverse))

namespace WalkAlgebra

/-! ### Basic identities -/

@[simp] lemma walkSig_nil (o : V → V → ℤ) (u : V) :
    walkSig o (Walk.nil : G.Walk u u) = 0 := rfl

@[simp] lemma walkSig_cons (o : V → V → ℤ) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkSig o (Walk.cons h p) = o u v - walkSig o p := rfl

@[simp] lemma walkFlow_nil (g : V → V → ℤ) (u : V) :
    walkFlow g (Walk.nil : G.Walk u u) = 0 := rfl

@[simp] lemma walkFlow_cons (g : V → V → ℤ) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkFlow g (Walk.cons h p) = g u v + walkFlow g p := rfl

lemma walkSig_append (o : V → V → ℤ) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkSig o (p.append q) = walkSig o p + (-1) ^ p.length * walkSig o q := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [Walk.cons_append, walkSig_cons, ih, Walk.length_cons, pow_succ]; ring

lemma walkFlow_append (g : V → V → ℤ) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkFlow g (p.append q) = walkFlow g p + walkFlow g q := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [Walk.cons_append, walkFlow_cons, ih]; ring

lemma walkSig_reverse {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V} (p : G.Walk u v) :
    walkSig o p.reverse = -(-1) ^ p.length * walkSig o p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [Walk.reverse_cons, walkSig_append, ih, walkSig_cons, walkSig_nil,
      Walk.length_cons, Walk.length_reverse, pow_succ, ho]
    ring

lemma walkFlow_reverse {g : V → V → ℤ} (hg : ∀ x y, g x y = - g y x) {u v : V}
    (p : G.Walk u v) : walkFlow g p.reverse = - walkFlow g p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [Walk.reverse_cons, walkFlow_append, ih, walkFlow_cons, walkFlow_nil]
    rw [hg]
    ring

lemma neg_one_pow_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
  rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h]

lemma walkSig_append_reverse {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (p : G.Walk u v) : walkSig o (p.append p.reverse) = 0 := by
  rw [walkSig_append, walkSig_reverse ho]
  linear_combination (-walkSig o p) * neg_one_pow_mul_self p.length

/-- `σ(p ++ q⁻¹) = σ p - σ q` for walks of the same parity. -/
lemma walkSig_append_reverse_of_even {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (p q : G.Walk u v) (h : Even (p.length + q.length)) :
    walkSig o (p.append q.reverse) = walkSig o p - walkSig o q := by
  have hs : ((-1 : ℤ)) ^ (p.length + q.length) = 1 := h.neg_one_pow
  rw [pow_add] at hs
  rw [walkSig_append, walkSig_reverse ho]
  linear_combination (-walkSig o q) * hs

/-! ### Closed walks that are not cycles -/

lemma exists_split_of_duplicate {u v y : V} (p : G.Walk u v) (hy : List.Duplicate y p.support) :
    ∃ (Q : G.Walk u y) (R : G.Walk y y) (Q' : G.Walk y v),
      p = Q.append (R.append Q') ∧ R.length ≠ 0 := by
  classical
  induction p with
  | nil => exact absurd hy (List.not_duplicate_singleton _ _)
  | cons h p ih =>
    rw [Walk.support_cons, List.duplicate_cons_iff] at hy
    rcases hy with ⟨rfl, hy⟩ | hy
    · refine ⟨Walk.nil, Walk.cons h (p.takeUntil _ hy), p.dropUntil _ hy, ?_, by simp⟩
      simp [Walk.take_spec]
    · obtain ⟨Q, R, Q', rfl, hR⟩ := ih hy
      exact ⟨Walk.cons h Q, R, Q', by simp, hR⟩

lemma exists_split_of_not_nodup {u v : V} (p : G.Walk u v) (hp : ¬ p.support.Nodup) :
    ∃ (y : V) (Q : G.Walk u y) (R : G.Walk y y) (Q' : G.Walk y v),
      p = Q.append (R.append Q') ∧ R.length ≠ 0 := by
  rw [List.nodup_iff_forall_not_duplicate] at hp
  push Not at hp
  obtain ⟨y, hy⟩ := hp
  exact ⟨y, exists_split_of_duplicate p hy⟩

lemma length_eq_one_of_isPath_of_mem_edges {u w : V} (p : G.Walk w u) (hp : p.IsPath)
    (hadj : G.Adj u w) (he : s(u, w) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at he
  | cons h' q =>
    rename_i z
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact absurd hadj (G.irrefl)
      · have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hp.1)
        simp [this]
    · exact absurd (q.snd_mem_support_of_mem_edges he) hp.2

/-- A closed walk is a cycle, has length `0` or `2`, or splits as `A ++ B ++ A'` with `B` a
nonempty closed walk and `A` nonempty. -/
lemma closed_cases {u : V} (Z : G.Walk u u) :
    Z.IsCycle ∨ Z.length = 0 ∨ Z.length = 2 ∨
      ∃ (y : V) (A : G.Walk u y) (B : G.Walk y y) (A' : G.Walk y u),
        Z = A.append (B.append A') ∧ B.length ≠ 0 ∧ A.length ≠ 0 := by
  cases Z with
  | nil => simp
  | cons h p =>
    rename_i w
    by_cases hp : p.support.Nodup
    · have hpp : p.IsPath := (Walk.isPath_def p).2 hp
      by_cases he : s(u, w) ∈ p.edges
      · right; right; left
        simp [length_eq_one_of_isPath_of_mem_edges p hpp h he]
      · left
        exact (Walk.cons_isCycle_iff p h).2 ⟨hpp, he⟩
    · obtain ⟨y, Q, R, Q', rfl, hR⟩ := exists_split_of_not_nodup p hp
      right; right; right
      exact ⟨y, Walk.cons h Q, R, Q', by simp, hR, by simp⟩

lemma walkSig_eq_zero_of_length_two {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u : V}
    (Z : G.Walk u u) (hZ : Z.length = 2) : walkSig o Z = 0 := by
  cases Z with
  | nil => simp at hZ
  | cons h p =>
    cases p with
    | nil => simp at hZ
    | cons h' q =>
      cases q with
      | nil => simp [ho]
      | cons _ _ => simp at hZ

lemma walkFlow_eq_zero_of_length_two {g : V → V → ℤ} (hg : ∀ x y, g x y = - g y x) {u : V}
    (Z : G.Walk u u) (hZ : Z.length = 2) : walkFlow g Z = 0 := by
  cases Z with
  | nil => simp at hZ
  | cons h p =>
    cases p with
    | nil => simp at hZ
    | cons h' q =>
      cases q with
      | nil => simp [hg _ u]
      | cons _ _ => simp at hZ

lemma walkSig_eq_zero_of_length_zero (o : V → V → ℤ) {u : V}
    (Z : G.Walk u u) (hZ : Z.length = 0) : walkSig o Z = 0 := by
  cases Z with
  | nil => rfl
  | cons _ _ => simp at hZ

lemma walkFlow_eq_zero_of_length_zero (g : V → V → ℤ) {u : V}
    (Z : G.Walk u u) (hZ : Z.length = 0) : walkFlow g Z = 0 := by
  cases Z with
  | nil => rfl
  | cons _ _ => simp at hZ

/-! ### Handcuffs -/

/-- The value of `walkSig` on the generalized handcuff `Z₁ ++ P ++ Z₂ ++ P⁻¹` (for odd `Z₁`,
`Z₂`), see `walkSig_handcuff`. -/
def hcv (o : V → V → ℤ) {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) : ℤ :=
  walkSig o Z1 - 2 * walkSig o P - (-1) ^ P.length * walkSig o Z2

lemma walkSig_handcuff {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) :
    walkSig o (Z1.append (P.append (Z2.append P.reverse))) = hcv o Z1 P Z2 := by
  simp only [hcv, walkSig_append, walkSig_reverse ho, h1.neg_one_pow, h2.neg_one_pow]
  rcases neg_one_pow_eq_or ℤ P.length with h | h <;> simp only [h] <;> ring

lemma hcv_reverse_left {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length) :
    hcv o Z1.reverse P Z2 = hcv o Z1 P Z2 := by
  simp only [hcv, walkSig_reverse ho, h1.neg_one_pow]; ring

lemma hcv_reverse_right {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h2 : Odd Z2.length) :
    hcv o Z1 P Z2.reverse = hcv o Z1 P Z2 := by
  simp only [hcv, walkSig_reverse ho, h2.neg_one_pow]; ring

lemma hcv_swap {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) :
    hcv o Z2 P.reverse Z1 = -(-1) ^ P.length * hcv o Z1 P Z2 := by
  simp only [hcv, walkSig_reverse ho, Walk.length_reverse]
  rcases neg_one_pow_eq_or ℤ P.length with h | h <;> simp only [h] <;> ring

lemma hcv_swap_eq_zero_iff {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v : V}
    (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) :
    hcv o Z2 P.reverse Z1 = 0 ↔ hcv o Z1 P Z2 = 0 := by
  rw [hcv_swap ho]
  rcases neg_one_pow_eq_or ℤ P.length with h | h <;> simp [h]

lemma hcv_split_even (o : V → V → ℤ) {u v y : V} (A : G.Walk u y) (B : G.Walk y y)
    (A' : G.Walk y u) (P : G.Walk u v) (Z2 : G.Walk v v) (hB : Even B.length)
    (hB0 : walkSig o B = 0) :
    hcv o (A.append (B.append A')) P Z2 = hcv o (A.append A') P Z2 := by
  simp only [hcv, walkSig_append, hB.neg_one_pow, hB0]; ring

lemma hcv_split_odd {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v y : V} (A : G.Walk u y)
    (B : G.Walk y y) (A' : G.Walk y u) (P : G.Walk u v) (Z2 : G.Walk v v) (hB : Odd B.length)
    (hAA : walkSig o (A.append A') = 0) :
    hcv o (A.append (B.append A')) P Z2 = (-1) ^ A.length * hcv o B (A.reverse.append P) Z2 := by
  simp only [walkSig_append] at hAA
  simp only [hcv, walkSig_append, walkSig_reverse ho, hB.neg_one_pow, Walk.length_append,
    Walk.length_reverse, pow_add]
  rcases neg_one_pow_eq_or ℤ A.length with h | h <;>
    rcases neg_one_pow_eq_or ℤ P.length with h' | h' <;> simp only [h, h'] at hAA ⊢ <;> linarith

lemma hcv_path_even (o : V → V → ℤ) {u v y : V} (Z1 : G.Walk u u) (Q : G.Walk u y)
    (R : G.Walk y y) (Q' : G.Walk y v) (Z2 : G.Walk v v) (hR : Even R.length)
    (hR0 : walkSig o R = 0) :
    hcv o Z1 (Q.append (R.append Q')) Z2 = hcv o Z1 (Q.append Q') Z2 := by
  simp only [hcv, walkSig_append, hR.neg_one_pow, hR0, Walk.length_append, pow_add]; ring

lemma hcv_path_odd (o : V → V → ℤ) {u v y : V} (Z1 : G.Walk u u) (Q : G.Walk u y)
    (R : G.Walk y y) (Q' : G.Walk y v) (Z2 : G.Walk v v) (hR : Odd R.length) :
    hcv o Z1 (Q.append (R.append Q')) Z2 = hcv o Z1 Q R - (-1) ^ Q.length * hcv o R Q' Z2 := by
  simp only [hcv, walkSig_append, hR.neg_one_pow, Walk.length_append, pow_add]; ring

lemma hcv_path_change {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u v x : V}
    (Z1 : G.Walk u u) (Q a : G.Walk u x) (R : G.Walk x v) (Z2 : G.Walk v v)
    (h : Even (Q.length + a.length)) :
    hcv o Z1 (Q.append R) Z2 = hcv o Z1 (a.append R) Z2 - 2 * walkSig o (Q.append a.reverse) := by
  have hs : ((-1 : ℤ)) ^ (Q.length + a.length) = 1 := h.neg_one_pow
  rw [pow_add] at hs
  simp only [hcv, walkSig_append, walkSig_reverse ho, Walk.length_append, pow_add]
  rcases neg_one_pow_eq_or ℤ Q.length with h | h <;>
    rcases neg_one_pow_eq_or ℤ a.length with h' | h' <;> simp only [h, h'] at hs ⊢ <;>
    first | (norm_num at hs; done) | ring

lemma hcv_rot (o : V → V → ℤ) {u v x : V}
    (X1 : G.Walk u x) (X2 : G.Walk x u) (R : G.Walk x v) (Z2 : G.Walk v v)
    (h : Odd (X1.length + X2.length)) :
    hcv o (X1.append X2) (X1.append R) Z2 = (-1) ^ X1.length * hcv o (X2.append X1) R Z2 := by
  have hs : ((-1 : ℤ)) ^ (X1.length + X2.length) = -1 := h.neg_one_pow
  rw [pow_add] at hs
  simp only [hcv, walkSig_append, Walk.length_append, pow_add]
  rcases neg_one_pow_eq_or ℤ X1.length with h | h <;>
    rcases neg_one_pow_eq_or ℤ X2.length with h' | h' <;>
    rcases neg_one_pow_eq_or ℤ R.length with h'' | h'' <;> simp only [h, h', h''] at hs ⊢ <;>
    first | (norm_num at hs; done) | ring

lemma hcv_nil_split {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u x : V}
    (X1 Y1 : G.Walk u x) (X2 Y2 : G.Walk x u)
    (h1 : Odd (X1.length + X2.length)) (h2 : Odd (Y1.length + Y2.length))
    (h : Even (X1.length + Y1.length)) :
    hcv o (X1.append X2) Walk.nil (Y1.append Y2) =
      walkSig o (X1.append Y1.reverse) + (-1) ^ X1.length * walkSig o (X2.append Y2.reverse) := by
  have hs1 : ((-1 : ℤ)) ^ (X1.length + X2.length) = -1 := h1.neg_one_pow
  have hs2 : ((-1 : ℤ)) ^ (Y1.length + Y2.length) = -1 := h2.neg_one_pow
  have hs : ((-1 : ℤ)) ^ (X1.length + Y1.length) = 1 := h.neg_one_pow
  rw [pow_add] at hs1 hs2 hs
  simp only [hcv, walkSig_append, walkSig_reverse ho, Walk.length_nil, pow_zero, walkSig_nil]
  rcases neg_one_pow_eq_or ℤ X1.length with e1 | e1 <;>
    rcases neg_one_pow_eq_or ℤ X2.length with e2 | e2 <;>
    rcases neg_one_pow_eq_or ℤ Y1.length with e3 | e3 <;>
    rcases neg_one_pow_eq_or ℤ Y2.length with e4 | e4 <;>
    simp only [e1, e2, e3, e4] at hs1 hs2 hs ⊢ <;>
    first | (norm_num at hs1; done) | (norm_num at hs2; done) | (norm_num at hs; done) | ring

/-- Arithmetic closer for length/parity side goals. -/
local macro "wa_omega" : tactic =>
  `(tactic| ((try simp only [Walk.length_append, Walk.length_reverse, Walk.length_nil,
    Walk.length_cons, Nat.odd_iff, Nat.even_iff] at *) <;> omega))

/-- Rotating an odd closed walk `Z₁` to a vertex `x` on it, choosing the arc `a : u ⟶ x` of a
prescribed parity. -/
lemma exists_rot_arc {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {u x : V} (Z1 : G.Walk u u)
    (h1 : Odd Z1.length) (hx : x ∈ Z1.support) (m : ℕ) :
    ∃ (a : G.Walk u x) (Z' : G.Walk x x), Z'.length = Z1.length ∧ a.length ≤ Z1.length ∧
      Even (a.length + m) ∧ ∀ (v : V) (R : G.Walk x v) (Z2 : G.Walk v v),
        hcv o Z1 (a.append R) Z2 = (-1) ^ a.length * hcv o Z' R Z2 := by
  classical
  obtain ⟨X1, X2, rfl⟩ : ∃ (X1 : G.Walk u x) (X2 : G.Walk x u), Z1 = X1.append X2 :=
    ⟨_, _, (Z1.take_spec hx).symm⟩
  have h1' : Odd (X1.length + X2.length) := by simpa using h1
  rcases Nat.even_or_odd (X1.length + m) with he | ho'
  · exact ⟨X1, X2.append X1, by wa_omega, by wa_omega, he,
      fun v R Z2 => hcv_rot o X1 X2 R Z2 h1'⟩
  · refine ⟨X2.reverse, X1.reverse.append X2.reverse, by wa_omega, by wa_omega, by wa_omega,
      fun v R Z2 => ?_⟩
    rw [← hcv_reverse_left ho _ _ _ h1, Walk.reverse_append]
    exact hcv_rot o X2.reverse X1.reverse R Z2 (by wa_omega)

/-- `exists_rot_arc` for the second cycle of a handcuff. -/
lemma exists_rot_arc' {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x) {v x : V} (Z2 : G.Walk v v)
    (h2 : Odd Z2.length) (hx : x ∈ Z2.support) (m : ℕ) :
    ∃ (a : G.Walk x v) (Z' : G.Walk x x), Z'.length = Z2.length ∧ a.length ≤ Z2.length ∧
      Even (a.length + m) ∧ ∀ (u : V) (R : G.Walk u x) (Z1 : G.Walk u u),
        hcv o Z1 R Z' = 0 → hcv o Z1 (R.append a) Z2 = 0 := by
  obtain ⟨a, Z', hl, ha, he, H⟩ := exists_rot_arc ho Z2 h2 hx m
  refine ⟨a.reverse, Z', hl, by simpa using ha, by simpa using he, fun u R Z1 h => ?_⟩
  apply (hcv_swap_eq_zero_iff ho Z1 (R.append a.reverse) Z2).mp
  rw [Walk.reverse_append, Walk.reverse_reverse, H, (hcv_swap_eq_zero_iff ho Z1 R Z').mpr h,
    mul_zero]

section Cases

variable {o : V → V → ℤ} {n : ℕ}

/-- Case: the first closed walk of the handcuff is not a cycle. -/
lemma hcv_case_not_cycle (ho : ∀ x y, o x y = o y x)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n → hcv o Z1 P Z2 = 0)
    {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + 2 * P.length + Z2.length ≤ n)
    (hS : ∀ (u' v' : V) (Z1' : G.Walk u' u') (P' : G.Walk u' v') (Z2' : G.Walk v' v'),
      Odd Z1'.length → Odd Z2'.length → Z1'.length + 2 * P'.length + Z2'.length ≤ n →
      Z1'.length + Z2'.length < Z1.length + Z2.length → hcv o Z1' P' Z2' = 0)
    (hc : ¬ Z1.IsCycle) : hcv o Z1 P Z2 = 0 := by
  rcases closed_cases Z1 with hc' | h0 | h2' | ⟨y, A, B, A', rfl, hB, hA⟩
  · exact absurd hc' hc
  · rw [h0] at h1; exact absurd h1 (by decide)
  · rw [h2'] at h1; exact absurd h1 (by decide)
  · rcases Nat.even_or_odd B.length with hBe | hBo
    · rw [hcv_split_even o A B A' P Z2 hBe (hW _ B hBe (by wa_omega))]
      exact hH _ _ _ P Z2 (by wa_omega) h2 (by wa_omega)
    · have hAA : walkSig o (A.append A') = 0 := hW _ _ (by wa_omega) (by wa_omega)
      rcases le_total A.length A'.length with hle | hle
      · rw [hcv_split_odd ho A B A' P Z2 hBo hAA,
          hS _ _ B (A.reverse.append P) Z2 hBo h2 (by wa_omega) (by wa_omega), mul_zero]
      · rw [← hcv_reverse_left ho _ P Z2 h1, Walk.reverse_append, Walk.reverse_append,
          ← Walk.append_assoc]
        have hAA' : walkSig o (A'.reverse.append A.reverse) = 0 := by
          rw [← Walk.reverse_append, walkSig_reverse ho, hAA, mul_zero]
        rw [hcv_split_odd ho A'.reverse B.reverse A.reverse P Z2 (by simpa using hBo) hAA',
          Walk.reverse_reverse,
          hS _ _ B.reverse (A'.append P) Z2 (by simpa using hBo) h2 (by wa_omega) (by wa_omega),
          mul_zero]

/-- Case: the connecting walk of the handcuff is not a path. -/
lemma hcv_case_not_path
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n → hcv o Z1 P Z2 = 0)
    {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + 2 * P.length + Z2.length ≤ n)
    (hp : ¬ P.IsPath) : hcv o Z1 P Z2 = 0 := by
  rw [Walk.isPath_def] at hp
  obtain ⟨y, Q, R, Q', rfl, hR⟩ := exists_split_of_not_nodup P hp
  rcases Nat.even_or_odd R.length with hRe | hRo
  · rw [hcv_path_even o Z1 Q R Q' Z2 hRe (hW _ R hRe (by wa_omega))]
    exact hH _ _ Z1 _ Z2 h1 h2 (by wa_omega)
  · rw [hcv_path_odd o Z1 Q R Q' Z2 hRo, hH _ _ Z1 Q R h1 hRo (by wa_omega),
      hH _ _ R Q' Z2 hRo h2 (by wa_omega)]
    ring

/-- Case: the connecting walk meets the first closed walk at a vertex other than its base. -/
lemma hcv_case_meet (ho : ∀ x y, o x y = o y x)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n → hcv o Z1 P Z2 = 0)
    {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + 2 * P.length + Z2.length ≤ n) {x : V}
    (hxP : x ∈ P.support) (hxZ : x ∈ Z1.support) (hxu : x ≠ u) : hcv o Z1 P Z2 = 0 := by
  classical
  obtain ⟨Q, P', rfl⟩ : ∃ (Q : G.Walk u x) (P' : G.Walk x v), P = Q.append P' :=
    ⟨_, _, (P.take_spec hxP).symm⟩
  have hQ : Q.length ≠ 0 := fun h => hxu (Walk.eq_of_length_eq_zero h).symm
  obtain ⟨a, Z', hl, ha, he, H⟩ := exists_rot_arc ho Z1 h1 hxZ Q.length
  rw [hcv_path_change ho Z1 Q a P' Z2 (by rwa [add_comm]), H,
    hH _ _ Z' P' Z2 (hl ▸ h1) h2 (by wa_omega), hW _ _ (by wa_omega) (by wa_omega)]
  ring

/-- Case: the two odd closed walks (with a nontrivial connecting walk) meet. -/
lemma hcv_case_meet_both (ho : ∀ x y, o x y = o y x)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n → hcv o Z1 P Z2 = 0)
    {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + 2 * P.length + Z2.length ≤ n) (hP : 0 < P.length)
    {x : V} (hx1 : x ∈ Z1.support) (hx2 : x ∈ Z2.support) : hcv o Z1 P Z2 = 0 := by
  obtain ⟨a2, Z2', hl2, ha2, -, H2⟩ := exists_rot_arc' ho Z2 h2 hx2 0
  obtain ⟨a1, Z1', hl1, ha1, he1, H1⟩ := exists_rot_arc ho Z1 h1 hx1 (a2.length + P.length)
  have hc := hcv_path_change ho Z1 P (a1.append a2) Walk.nil Z2 (by wa_omega)
  simp only [Walk.append_nil] at hc
  have h0 := H2 _ Walk.nil Z1' (hH _ _ Z1' Walk.nil Z2' (hl1 ▸ h1) (hl2 ▸ h2) (by wa_omega))
  rw [Walk.nil_append] at h0
  rw [hc, H1, h0, hW _ _ (by wa_omega) (by wa_omega)]
  ring

/-- Case: two odd closed walks at the same base meeting at another vertex. -/
lemma hcv_case_nil_meet (ho : ∀ x y, o x y = o y x)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    {u : V} (Z1 Z2 : G.Walk u u) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + Z2.length ≤ n) {x : V}
    (hx1 : x ∈ Z1.support) (hx2 : x ∈ Z2.support) (hxu : x ≠ u) :
    hcv o Z1 Walk.nil Z2 = 0 := by
  classical
  obtain ⟨X1, X2, rfl⟩ : ∃ (X1 : G.Walk u x) (X2 : G.Walk x u), Z1 = X1.append X2 :=
    ⟨_, _, (Z1.take_spec hx1).symm⟩
  obtain ⟨Y1, Y2, rfl⟩ : ∃ (Y1 : G.Walk u x) (Y2 : G.Walk x u), Z2 = Y1.append Y2 :=
    ⟨_, _, (Z2.take_spec hx2).symm⟩
  have hX1 : X1.length ≠ 0 := fun h => hxu (Walk.eq_of_length_eq_zero h).symm
  have hX2 : X2.length ≠ 0 := fun h => hxu (Walk.eq_of_length_eq_zero h)
  have hY1 : Y1.length ≠ 0 := fun h => hxu (Walk.eq_of_length_eq_zero h).symm
  have hY2 : Y2.length ≠ 0 := fun h => hxu (Walk.eq_of_length_eq_zero h)
  rcases Nat.even_or_odd (X1.length + Y1.length) with he | he
  · rw [hcv_nil_split ho X1 Y1 X2 Y2 (by wa_omega) (by wa_omega) he,
      hW _ _ (by wa_omega) (by wa_omega), hW _ _ (by wa_omega) (by wa_omega)]
    ring
  · rw [← hcv_reverse_right ho _ _ _ h2, Walk.reverse_append,
      hcv_nil_split ho X1 Y2.reverse X2 Y1.reverse (by wa_omega) (by wa_omega) (by wa_omega),
      hW _ _ (by wa_omega) (by wa_omega), hW _ _ (by wa_omega) (by wa_omega)]
    ring

/-- One step of the handcuff induction. -/
lemma hcv_step (ho : ∀ x y, o x y = o y x) (hfec : ∀ F : FEC G, walkSig o F.walk = 0)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n → hcv o Z1 P Z2 = 0)
    {u v : V} (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v) (h1 : Odd Z1.length)
    (h2 : Odd Z2.length) (hT : Z1.length + 2 * P.length + Z2.length ≤ n)
    (hS : ∀ (u' v' : V) (Z1' : G.Walk u' u') (P' : G.Walk u' v') (Z2' : G.Walk v' v'),
      Odd Z1'.length → Odd Z2'.length → Z1'.length + 2 * P'.length + Z2'.length ≤ n →
      Z1'.length + Z2'.length < Z1.length + Z2.length → hcv o Z1' P' Z2' = 0) :
    hcv o Z1 P Z2 = 0 := by
  by_cases hc1 : Z1.IsCycle
  swap
  · exact hcv_case_not_cycle ho hW hH Z1 P Z2 h1 h2 hT hS hc1
  by_cases hc2 : Z2.IsCycle
  swap
  · rw [← hcv_swap_eq_zero_iff ho]
    exact hcv_case_not_cycle ho hW hH Z2 P.reverse Z1 h2 h1 (by wa_omega)
      (fun u' v' Z1' P' Z2' h1' h2' hT' hs' => hS u' v' Z1' P' Z2' h1' h2' hT' (by omega)) hc2
  by_cases hp : P.IsPath
  swap
  · exact hcv_case_not_path hW hH Z1 P Z2 h1 h2 hT hp
  by_cases hd : ∃ x ∈ P.support, x ∈ Z1.support ∧ x ≠ u
  · obtain ⟨x, hxP, hxZ, hxu⟩ := hd
    exact hcv_case_meet ho hW hH Z1 P Z2 h1 h2 hT hxP hxZ hxu
  by_cases he : ∃ x ∈ P.support, x ∈ Z2.support ∧ x ≠ v
  · obtain ⟨x, hxP, hxZ, hxv⟩ := he
    rw [← hcv_swap_eq_zero_iff ho]
    exact hcv_case_meet ho hW hH Z2 P.reverse Z1 h2 h1 (by wa_omega)
      (by simpa [Walk.support_reverse] using hxP) hxZ hxv
  by_cases hf : ∀ x, x ∈ Z1.support → x ∈ Z2.support → P.length = 0 ∧ x = u
  · push Not at hd he
    have := hfec ⟨u, v, Z1, P, Z2, hc1, hc2, h1, h2, hp, hf, hd, he⟩
    rwa [FEC.walk, walkSig_handcuff ho _ _ _ h1 h2] at this
  · push Not at hf
    obtain ⟨x, hx1, hx2, hx⟩ := hf
    rcases Nat.eq_zero_or_pos P.length with hP0 | hP0
    · cases P with
      | nil => exact hcv_case_nil_meet ho hW Z1 Z2 h1 h2 (by wa_omega) hx1 hx2 (hx rfl)
      | cons _ _ => simp at hP0
    · exact hcv_case_meet_both ho hW hH Z1 P Z2 h1 h2 hT hP0 hx1 hx2

/-- One step of the induction for even closed walks. -/
lemma even_step (ho : ∀ x y, o x y = o y x)
    (hcyc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → Even c.length → walkSig o c = 0)
    (hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0)
    (hHn : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
      Odd Z2.length → Z1.length + 2 * P.length + Z2.length ≤ n → hcv o Z1 P Z2 = 0)
    {u : V} (W : G.Walk u u) (he : Even W.length) (hn : W.length ≤ n) : walkSig o W = 0 := by
  rcases closed_cases W with hc | h0 | h2 | ⟨y, A, B, A', rfl, hB, hA⟩
  · exact hcyc u _ hc he
  · exact walkSig_eq_zero_of_length_zero o _ h0
  · exact walkSig_eq_zero_of_length_two ho _ h2
  · rcases Nat.even_or_odd B.length with hBe | hBo
    · have e1 := hW _ (A.append A') (by wa_omega) (by wa_omega)
      have e2 := hW _ B hBe (by wa_omega)
      rw [walkSig_append] at e1
      rw [walkSig_append, walkSig_append, e2, hBe.neg_one_pow]
      linear_combination e1
    · have hpar : Odd (A.length + A'.length) := by wa_omega
      have hs : ((-1 : ℤ)) ^ (A.length + A'.length) = -1 := hpar.neg_one_pow
      rw [pow_add] at hs
      have key : walkSig o (A.append (B.append A')) =
          (-1) ^ A.length * hcv o B Walk.nil (A'.append A) := by
        simp only [hcv, walkSig_append, hBo.neg_one_pow, Walk.length_nil, pow_zero, walkSig_nil]
        rcases neg_one_pow_eq_or ℤ A.length with e1 | e1 <;>
          rcases neg_one_pow_eq_or ℤ A'.length with e2 | e2 <;>
          simp only [e1, e2] at hs ⊢ <;> first | (norm_num at hs; done) | ring
      rw [key, hHn _ _ B Walk.nil (A'.append A) hBo (by wa_omega) (by wa_omega), mul_zero]

end Cases

end WalkAlgebra

open WalkAlgebra in
/-- If an antisymmetric flow vanishes on every cycle, it vanishes on every closed walk. -/
theorem walkFlow_eq_zero_of_isCycle {g : V → V → ℤ} (hg : ∀ x y, g x y = - g y x)
    (hcyc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → walkFlow g c = 0) :
    ∀ (u : V) (p : G.Walk u u), walkFlow g p = 0 := by
  suffices H : ∀ n (u : V) (p : G.Walk u u), p.length = n → walkFlow g p = 0 from
    fun u p => H _ u p rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u p hn
    rcases closed_cases p with hc | h0 | h2 | ⟨y, A, B, A', rfl, hB, hA⟩
    · exact hcyc u p hc
    · exact walkFlow_eq_zero_of_length_zero g p h0
    · exact walkFlow_eq_zero_of_length_two hg p h2
    · simp only [Walk.length_append] at hn
      have h1 := ih _ (by simp only [Walk.length_append]; omega) u (A.append A') rfl
      have h2 := ih _ (by omega) y B rfl
      rw [walkFlow_append] at h1
      rw [walkFlow_append, walkFlow_append]
      linarith

open WalkAlgebra in
/-- If a symmetric weight `o` has vanishing alternating sum `walkSig o` on all even cycles and on
all faux-even cycles, then `walkSig o` vanishes on every closed walk of even length. -/
theorem walkSig_eq_zero_of_isCycle_of_fec {o : V → V → ℤ} (ho : ∀ x y, o x y = o y x)
    (hcyc : ∀ (u : V) (c : G.Walk u u), c.IsCycle → Even c.length → walkSig o c = 0)
    (hfec : ∀ F : FEC G, walkSig o F.walk = 0) :
    ∀ (u : V) (p : G.Walk u u), Even p.length → walkSig o p = 0 := by
  have key : ∀ n, (∀ (u : V) (W : G.Walk u u), Even W.length → W.length = n →
      walkSig o W = 0) ∧
      (∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v), Odd Z1.length →
        Odd Z2.length → Z1.length + 2 * P.length + Z2.length = n → hcv o Z1 P Z2 = 0) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hW : ∀ (u : V) (W : G.Walk u u), Even W.length → W.length < n → walkSig o W = 0 :=
      fun u W he hl => (ih _ hl).1 u W he rfl
    have hH : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v),
        Odd Z1.length → Odd Z2.length → Z1.length + 2 * P.length + Z2.length < n →
        hcv o Z1 P Z2 = 0 :=
      fun u v Z1 P Z2 h1 h2 hl => (ih _ hl).2 u v Z1 P Z2 h1 h2 rfl
    have hHn : ∀ (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v),
        Odd Z1.length → Odd Z2.length → Z1.length + 2 * P.length + Z2.length ≤ n →
        hcv o Z1 P Z2 = 0 := by
      suffices H : ∀ s (u v : V) (Z1 : G.Walk u u) (P : G.Walk u v) (Z2 : G.Walk v v),
          Odd Z1.length → Odd Z2.length → Z1.length + 2 * P.length + Z2.length ≤ n →
          Z1.length + Z2.length = s → hcv o Z1 P Z2 = 0 from
        fun u v Z1 P Z2 h1 h2 hT => H _ u v Z1 P Z2 h1 h2 hT rfl
      intro s
      induction s using Nat.strong_induction_on with
      | _ s ihs =>
      intro u v Z1 P Z2 h1 h2 hT hs
      exact hcv_step ho hfec hW hH Z1 P Z2 h1 h2 hT
        (fun u' v' Z1' P' Z2' h1' h2' hT' hs' =>
          ihs _ (hs ▸ hs') u' v' Z1' P' Z2' h1' h2' hT' rfl)
    exact ⟨fun u W he hn => even_step ho hcyc hW hHn W he hn.le,
      fun u v Z1 P Z2 h1 h2 hT => hHn u v Z1 P Z2 h1 h2 hT.le⟩
  exact fun u p hp => (key _).1 u p hp rfl

end AmnesiacFloodingFaults
