import Podc.Computability.CommunicationComplexity.OneRound

/-!
# Bit encodings for the messages of Algorithm 2

Messages are concatenations of *prefix codes* (`PrefixInj`): fixed-width codes (bit arrays,
binary numbers of a fixed width) and the unary code `1^a 0`. A concatenation of prefix codes can
be decoded from left to right (`PrefixInj.flatMap`, `PrefixInj.ofFn`), which gives the
injectivity of the message encodings; receivers decode with `Function.invFun`.
-/

namespace Podc.RoundEfficientColoring

open Cslib.CommunicationComplexity

variable {α : Type*}

/-- `code` is a prefix code: a codeword followed by anything determines the codeword and the rest.
-/
def PrefixInj (code : α → List Bool) : Prop :=
  ∀ ⦃a b : α⦄ ⦃l l' : List Bool⦄, code a ++ l = code b ++ l' → a = b ∧ l = l'

lemma prefixInj_of_length {code : α → List Bool} {m : ℕ} (hlen : ∀ a, (code a).length = m)
    (hinj : Function.Injective code) : PrefixInj code := by
  intro a b l l' h
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
  exact ⟨hinj h1, h2⟩

/-- The unary code `1^a 0`. -/
def unary (a : ℕ) : List Bool := List.replicate a true ++ [false]

lemma length_unary (a : ℕ) : (unary a).length = a + 1 := by simp [unary]

lemma prefixInj_unary : PrefixInj unary := by
  intro a
  induction a with
  | zero =>
    intro b l l' h
    cases b with
    | zero => simpa [unary] using h
    | succ b => simp [unary, List.replicate_succ] at h
  | succ a ih =>
    intro b l l' h
    cases b with
    | zero => simp [unary, List.replicate_succ] at h
    | succ b =>
      simp only [unary, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih (by simpa [unary] using h)
      exact ⟨by rw [h1], h2⟩

lemma PrefixInj.flatMap {code : α → List Bool} (hc : PrefixInj code) :
    ∀ {as bs : List α} {l l' : List Bool}, as.length = bs.length →
      as.flatMap code ++ l = bs.flatMap code ++ l' → as = bs ∧ l = l'
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | a :: as, b :: bs, l, l', hlen, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := hc h
    obtain ⟨rfl, h''⟩ := hc.flatMap (by simpa using hlen) h'
    exact ⟨rfl, h''⟩

lemma PrefixInj.ofFn {code : α → List Bool} (hc : PrefixInj code) {n : ℕ} {f g : Fin n → α}
    {l l' : List Bool} (h : (List.ofFn f).flatMap code ++ l = (List.ofFn g).flatMap code ++ l') :
    f = g ∧ l = l' := by
  obtain ⟨h1, h2⟩ := hc.flatMap (by simp) h
  exact ⟨List.ofFn_injective h1, h2⟩

lemma length_flatMap_const {code : α → List Bool} {m : ℕ} (hlen : ∀ a, (code a).length = m)
    (as : List α) : (as.flatMap code).length = as.length * m := by
  induction as with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, ih, hlen, Nat.succ_mul, Nat.add_comm]

lemma length_flatMap_ofFn_unary {n : ℕ} (f : Fin n → ℕ) :
    ((List.ofFn f).flatMap unary).length = ∑ i, (f i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons, List.length_append, length_unary, ih,
      Fin.sum_univ_succ]

/-- The bit `[b]`. -/
def bit (b : Bool) : List Bool := [b]

lemma prefixInj_bit : PrefixInj bit :=
  prefixInj_of_length (m := 1) (fun _ => rfl) (fun _ _ h => by simpa [bit] using h)

/-- A bit array of fixed length `m`. -/
def bitArray {m : ℕ} (f : Fin m → Bool) : List Bool := List.ofFn f

lemma prefixInj_bitArray {m : ℕ} : PrefixInj (bitArray (m := m)) :=
  prefixInj_of_length (m := m) (fun _ => by simp [bitArray])
    (fun _ _ h => List.ofFn_injective h)

/-- The number `c` in binary with exactly `w` digits (least significant first). -/
def binary : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, c => (c % 2 == 1) :: binary w (c / 2)

lemma length_binary (w c : ℕ) : (binary w c).length = w := by
  induction w generalizing c with
  | zero => rfl
  | succ w ih => simp [binary, ih]

lemma bitsVal_binary (w c : ℕ) : bitsVal (binary w c) = c % 2 ^ w := by
  induction w generalizing c with
  | zero => simp [binary, bitsVal, Nat.mod_one]
  | succ w ih =>
    simp only [binary, bitsVal, ih, pow_succ]
    rw [mul_comm (2 ^ w) 2, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

/-- Binary code of `Fin (2 ^ w)`. -/
def binaryFin {w : ℕ} (c : Fin (2 ^ w)) : List Bool := binary w c

lemma prefixInj_binaryFin {w : ℕ} : PrefixInj (binaryFin (w := w)) :=
  prefixInj_of_length (m := w) (fun _ => length_binary _ _) fun a b h => by
    have := congrArg bitsVal h
    simp only [binaryFin, bitsVal_binary, Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at this
    exact Fin.ext this

end Podc.RoundEfficientColoring
