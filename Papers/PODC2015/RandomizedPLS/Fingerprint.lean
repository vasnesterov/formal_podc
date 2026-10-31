import Mathlib
import Cslib.Probability.Finite.Uniform

/-!
# Fingerprinting: a one-way randomized protocol for equality (Lemma 3.3 of [BFP15])

M. Baruch, P. Fraigniaud, B. Patt-Shamir. *Randomized Proof-Labeling Schemes.* PODC 2015.

Lemma 3.3 asks for a one-way protocol for `EQ`: a *sender* holding a bit string `a` sends a short
random message, and a *decider* holding a bit string `b` decides `a = b` from it; equal strings are
always accepted and distinct strings are rejected with probability `> 2/3`; the message has
`O(log λ)` bits for `λ`-bit strings.

We use polynomial fingerprints over the Galois field `𝔽 = GF(2^m)`, `m = fpBits |a|` with
`2^m ≥ 3 (|a| + 1)`:

* `bitPoly a = X^|a| + ∑ aᵢ Xⁱ` encodes the bit string `a` injectively (the leading monomial
  encodes the length);
* `fpSend a x`, for a uniformly random `x ∈ 𝔽`, is the `2m`-bit string `enc x ++ enc (P_a(x))`;
* `fpDecide b r` accepts iff `r = fpSend b x` for some `x`, i.e. iff `r` has `2 · fpBits |b|`
  bits and decodes to a pair `(x, y)` with `P_b(x) = y`.

Our version is slightly more general than the paper's: `a` and `b` may have different lengths
(the message then has `2 · fpBits |a|` bits).

## Main statements

* `uprob_apply_eq` (marginal of a uniform product space; `CSLib candidate`).
* `card_filter_eval_eq_le` (two distinct polynomials agree on few points; `CSLib candidate`).
* `lemma_3_3`: Lemma 3.3 of [BFP15].
-/

namespace Podc.RandomizedPLS

open Polynomial Cslib.Probability Classical

/-! ### Marginals of uniform product spaces -/

-- CSLib candidate
/-- **Marginals of a uniform product space.** An event that depends on one coordinate of the
uniform product space `∀ j, α j` has the same probability as on that coordinate. -/
theorem uprob_apply_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (i : ι) (p : α i → Prop) :
    uprob (fun ω : ∀ j, α j => p (ω i)) = uprob p := by
  have e : (fun ω : ∀ j, α j => p (ω i)) = (fun ω => ∀ j, ∀ h : j = i, p (h ▸ ω j)) := by
    funext ω; apply propext; constructor
    · rintro hp j rfl; exact hp
    · intro h; exact h i rfl
  rw [e, uprob_pi (fun j x => ∀ h : j = i, p (h ▸ x)), Finset.prod_eq_single i]
  · congr 1; funext x; apply propext; exact ⟨fun h => h rfl, fun h _ => h⟩
  · intro j _ hj
    have : (fun x : α j => ∀ h : j = i, p (h ▸ x)) = fun _ => True := by
      funext x; apply propext; exact ⟨fun _ => trivial, fun _ h => absurd h hj⟩
    rw [this, uprob_true]; simp
  · simp

/-! ### Polynomial encodings of bit strings -/

section Poly

variable {K : Type*} [Field K]

/-- The polynomial `X^|a| + ∑_{i < |a|} aᵢ Xⁱ` of a bit string `a`. -/
noncomputable def bitPoly : List Bool → K[X]
  | [] => 1
  | b :: t => (if b then 1 else 0) + X * bitPoly t

lemma bitPoly_monic_natDegree (a : List Bool) :
    (bitPoly a : K[X]).Monic ∧ (bitPoly a : K[X]).natDegree = a.length := by
  induction a with
  | nil => simp [bitPoly]
  | cons b t ih =>
    obtain ⟨hm, hd⟩ := ih
    have hXm : (X * bitPoly t : K[X]).Monic := monic_X.mul hm
    have hXd : (X * bitPoly t : K[X]).natDegree = t.length + 1 := by
      rw [natDegree_X_mul hm.ne_zero, hd]
    have hc : ((if b then 1 else 0 : K[X])).natDegree < (X * bitPoly t : K[X]).natDegree := by
      rw [hXd]; split_ifs <;> simp
    refine ⟨hXm.add_of_right (degree_lt_degree hc), ?_⟩
    simp only [bitPoly, List.length_cons]
    rw [natDegree_add_eq_right_of_natDegree_lt hc, hXd]

lemma bitPoly_natDegree (a : List Bool) : (bitPoly a : K[X]).natDegree = a.length :=
  (bitPoly_monic_natDegree a).2

/-- Bit strings are encoded injectively. -/
lemma bitPoly_injective : Function.Injective (bitPoly : List Bool → K[X]) := by
  intro a b h
  induction a generalizing b with
  | nil =>
    have := congrArg natDegree h
    rw [bitPoly_natDegree, bitPoly_natDegree] at this
    exact (List.length_eq_zero_iff.mp this.symm).symm
  | cons x s ih =>
    cases b with
    | nil =>
      have := congrArg natDegree h
      rw [bitPoly_natDegree, bitPoly_natDegree] at this
      simp at this
    | cons y t =>
      have h0 := congrArg (coeff · 0) h
      have hxy : x = y := by
        cases x <;> cases y <;> simp [bitPoly] at h0 ⊢
      subst hxy
      have h' : X * bitPoly s = X * (bitPoly t : K[X]) := add_left_cancel h
      rw [ih (mul_left_cancel₀ X_ne_zero h')]

end Poly

-- CSLib candidate
/-- Two distinct polynomials over a finite field agree on at most `max (deg p) (deg q)` points. -/
lemma card_filter_eval_eq_le {K : Type*} [Field K] [Fintype K] {p q : K[X]} (hpq : p ≠ q) :
    (Finset.univ.filter fun x => p.eval x = q.eval x).card ≤ max p.natDegree q.natDegree := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc _ ≤ (p - q).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp [Multiset.mem_toFinset, mem_roots hne, hx]
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ _ := natDegree_sub_le _ _

/-! ### The fingerprinting protocol -/

/-- The field `GF(2^m)` is finite. -/
noncomputable scoped instance instFintypeGaloisField (m : ℕ) : Fintype (GaloisField 2 m) :=
  Fintype.ofFinite _

lemma card_galoisField {m : ℕ} (hm : m ≠ 0) : Fintype.card (GaloisField 2 m) = 2 ^ m := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 m hm]

/-- The exponent `m` of the field `GF(2^m)` used for strings of length `n`:
the least `m` with `3 (n + 1) ≤ 2^m`. -/
def fpBits (n : ℕ) : ℕ := Nat.clog 2 (3 * (n + 1))

lemma le_two_pow_fpBits (n : ℕ) : 3 * (n + 1) ≤ 2 ^ fpBits n := Nat.le_pow_clog one_lt_two _

lemma fpBits_ne_zero (n : ℕ) : fpBits n ≠ 0 := by
  intro h
  have := le_two_pow_fpBits n
  rw [h] at this
  omega

/-- `fpBits n = O(log n)`. -/
lemma fpBits_le (n : ℕ) : fpBits n ≤ Nat.log 2 n + 3 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.lt_pow_succ_log_self one_lt_two n
  rw [pow_add, pow_succ] at *
  omega

/-- A binary encoding of the elements of `GF(2^m)` by `m`-bit strings. -/
noncomputable def fpEnc (m : ℕ) (x : GaloisField 2 m) : List Bool :=
  if hm : m = 0 then [] else
    List.ofFn (Fintype.equivOfCardEq (α := GaloisField 2 m) (β := Fin m → Bool)
      (by rw [card_galoisField hm]; simp) x)

lemma fpEnc_length {m : ℕ} (hm : m ≠ 0) (x : GaloisField 2 m) : (fpEnc m x).length = m := by
  simp [fpEnc, hm]

lemma fpEnc_injective {m : ℕ} (hm : m ≠ 0) : Function.Injective (fpEnc m) := by
  intro x y h
  simp only [fpEnc, hm, dite_false] at h
  exact (Equiv.injective _) (List.ofFn_injective h)

/-- The message `enc x ++ enc (P_a(x))` for the evaluation point `x ∈ GF(2^m)`. -/
noncomputable def fpMsg (m : ℕ) (a : List Bool) (x : GaloisField 2 m) : List Bool :=
  fpEnc m x ++ fpEnc m ((bitPoly a).eval x)

lemma fpMsg_length {m : ℕ} (hm : m ≠ 0) (a : List Bool) (x : GaloisField 2 m) :
    (fpMsg m a x).length = 2 * m := by
  simp [fpMsg, fpEnc_length hm]; ring

lemma fpMsg_eq_iff {m : ℕ} (hm : m ≠ 0) (a b : List Bool) (x y : GaloisField 2 m) :
    fpMsg m b y = fpMsg m a x ↔ y = x ∧ (bitPoly b).eval y = (bitPoly a).eval x := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [fpEnc_length hm, fpEnc_length hm])
    exact ⟨fpEnc_injective hm h1, fpEnc_injective hm h2⟩
  · rintro ⟨rfl, h⟩
    simp [fpMsg, h]

/-- The sender of the protocol of Lemma 3.3: input `a`, random evaluation point `x`. -/
noncomputable def fpSend (a : List Bool) (x : GaloisField 2 (fpBits a.length)) : List Bool :=
  fpMsg _ a x

/-- The decider of the protocol of Lemma 3.3: input `b`, received message `r`. It accepts iff
`r` is of the form `enc x ++ enc (P_b(x))`. -/
noncomputable def fpDecide (b r : List Bool) : Bool :=
  decide (∃ x : GaloisField 2 (fpBits b.length), fpMsg _ b x = r)

lemma fpSend_length (a : List Bool) (x : GaloisField 2 (fpBits a.length)) :
    (fpSend a x).length = 2 * fpBits a.length :=
  fpMsg_length (fpBits_ne_zero _) a x

lemma fpDecide_fpSend (a : List Bool) (x : GaloisField 2 (fpBits a.length)) :
    fpDecide a (fpSend a x) = true := by
  simp only [fpDecide, decide_eq_true_eq]
  exact ⟨x, rfl⟩

/-- Counting form of soundness: the number of evaluation points fooling the decider is less than
a third of the field. -/
lemma card_fool_lt {ma mb : ℕ} (a b : List Bool) (hab : a ≠ b)
    (ha : 3 * (a.length + 1) ≤ 2 ^ ma) (hb : 3 * (b.length + 1) ≤ 2 ^ mb) :
    3 * (Finset.univ.filter fun x : GaloisField 2 ma =>
      ∃ y : GaloisField 2 mb, fpMsg mb b y = fpMsg ma a x).card < 2 ^ ma := by
  have hma : ma ≠ 0 := by rintro rfl; simp at ha; omega
  have hmb : mb ≠ 0 := by rintro rfl; simp at hb; omega
  by_cases hm : ma = mb
  · subst hm
    have hsub : (Finset.univ.filter fun x : GaloisField 2 ma =>
        ∃ y : GaloisField 2 ma, fpMsg ma b y = fpMsg ma a x) ⊆
        Finset.univ.filter fun x => (bitPoly a).eval x = (bitPoly b).eval x := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨y, hy⟩ := hx
      obtain ⟨rfl, h⟩ := (fpMsg_eq_iff hma a b x y).1 hy
      exact h.symm
    have h1 := (Finset.card_le_card hsub).trans
      (card_filter_eval_eq_le (fun h => hab (bitPoly_injective h)))
    rw [bitPoly_natDegree, bitPoly_natDegree] at h1
    rcases le_total a.length b.length with h | h
    · rw [max_eq_right h] at h1; omega
    · rw [max_eq_left h] at h1; omega
  · have : (Finset.univ.filter fun x : GaloisField 2 ma =>
        ∃ y : GaloisField 2 mb, fpMsg mb b y = fpMsg ma a x) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro x - ⟨y, hy⟩
      have := congrArg List.length hy
      rw [fpMsg_length hma, fpMsg_length hmb] at this
      omega
    rw [this]
    simp

/-- **Lemma 3.3 of [BFP15].** A one-way randomized protocol for equality with one-sided error:
the sender, holding `a`, draws a uniform `x ∈ GF(2^(fpBits |a|))` and sends `fpSend a x`; the
decider, holding `b`, outputs `fpDecide b (fpSend a x)`.
1. if `a = b` the decider always accepts;
2. if `a ≠ b` it rejects with probability `> 2/3`;
3. the message has `2 · fpBits |a|` bits, and `2 · fpBits λ ≤ 2 log₂ λ + 6 = O(log λ)`. -/
theorem lemma_3_3 :
    (∀ (a : List Bool) (x : GaloisField 2 (fpBits a.length)), fpDecide a (fpSend a x) = true) ∧
    (∀ a b : List Bool, a ≠ b →
      2 / 3 < uprob (fun x : GaloisField 2 (fpBits a.length) => fpDecide b (fpSend a x) = false)) ∧
    (∀ (a : List Bool) (x : GaloisField 2 (fpBits a.length)), (fpSend a x).length = 2 * fpBits a.length) ∧
    (∀ n, 2 * fpBits n ≤ 2 * Nat.log 2 n + 6) := by
  refine ⟨fpDecide_fpSend, ?_, fpSend_length, fun n => by have := fpBits_le n; omega⟩
  intro a b hab
  have hfalse : (fun x : GaloisField 2 (fpBits a.length) => fpDecide b (fpSend a x) = false) =
      fun x => ¬ (∃ y : GaloisField 2 (fpBits b.length), fpMsg _ b y = fpMsg _ a x) := by
    funext x
    simp only [fpDecide, fpSend]; exact propext decide_eq_false_iff_not
  rw [hfalse, uprob_not, uprob_eq_card_filter, card_galoisField (fpBits_ne_zero _)]
  have h := card_fool_lt (ma := fpBits a.length) (mb := fpBits b.length) a b hab
    (le_two_pow_fpBits _) (le_two_pow_fpBits _)
  have hpos : (0 : ℝ) < 2 ^ fpBits a.length := by positivity
  have h' : (3 : ℝ) * (Finset.univ.filter fun x : GaloisField 2 (fpBits a.length) =>
      ∃ y : GaloisField 2 (fpBits b.length), fpMsg _ b y = fpMsg _ a x).card <
      2 ^ fpBits a.length := by exact_mod_cast h
  push_cast
  rw [lt_sub_comm, div_lt_iff₀ hpos]
  linarith

end Podc.RandomizedPLS
