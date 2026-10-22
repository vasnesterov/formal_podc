import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

-- CSLib candidate: Cslib/Foundations/Combinatorics/SidonSet.lean

/-!
# Sidon sets and the Erdős–Turán construction

A set `A` (in an additive commutative monoid) is a *Sidon set* if all sums `a + b` (with `a, b ∈ A`,
`a = b` allowed) are different, i.e. `a + b = c + d` forces `{a, b} = {c, d}` as multisets.
In a cancellative monoid a Sidon set is a *Golomb ruler*: all non-zero differences are distinct.

The Erdős–Turán construction: for an odd prime `p` and `K ≤ p`, the integers
`dᵢ = 2 i p + (i² mod p)` for `i < K` form a Sidon set of `K` elements, all smaller than
`(2K - 1) p ≤ 2 p²`. With Bertrand's postulate this gives, for every `K`, a Sidon set of `K` natural
numbers below `8 K²`.

## Main statements

* `Cslib.IsSidon`: the Sidon property.
* `Cslib.IsSidon.golomb`: Sidon sets are Golomb rulers.
* `Cslib.SidonSet.erdosTuran_isSidon`: the Erdős–Turán construction is a Sidon set.
* `Cslib.SidonSet.exists_sidon_lt`: for every `K` there is a `K`-element Sidon set in `{0, …, l - 1}`
  with `l ≤ 8 K²`.

## Implementation notes

Mathlib has no Sidon-set (or Golomb-ruler) notion at the time of writing; the closest related notion
is the additive energy `Finset.addEnergy` (a finite `A` is Sidon iff its energy is minimal,
`2 |A|² - |A|`). If Mathlib gains `IsSidon`, this file should be aligned with it.
-/

namespace Cslib

/-- `A` is a Sidon set: `a + b = c + d` with all four in `A` forces `{a, b} = {c, d}`.
(Sums `a + a` are included, as usual.) -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon set is a Golomb ruler: a non-zero difference `a - b` (written `a + d = c + b`)
determines the pair `(a, b)`. -/
theorem IsSidon.golomb {α : Type*} [Add α] {A : Set α} (hA : IsSidon A)
    {a b c d : α} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (h : a + d = c + b) (hab : a ≠ b) : a = c ∧ b = d := by
  rcases hA ha hd hc hb h with h1 | h1
  · exact ⟨h1.1, h1.2.symm⟩
  · exact absurd h1.1 hab

theorem IsSidon.mono {α : Type*} [Add α] {A B : Set α} (hB : IsSidon B) (h : A ⊆ B) :
    IsSidon A := fun _ ha _ hb _ hc _ hd => hB (h ha) (h hb) (h hc) (h hd)

namespace SidonSet

/-- The `i`-th element `2 i p + (i² mod p)` of the Erdős–Turán Sidon set. -/
def etElem (p i : ℕ) : ℕ := 2 * i * p + i ^ 2 % p

/-- The Erdős–Turán set `{2 i p + (i² mod p) : i < K}`. -/
def erdosTuran (p K : ℕ) : Finset ℕ := (Finset.range K).image (etElem p)

theorem etElem_div {p : ℕ} (hp : 0 < p) (i : ℕ) : etElem p i / (2 * p) = i := by
  unfold etElem
  have : i ^ 2 % p < 2 * p := by have := Nat.mod_lt (i ^ 2) hp; omega
  rw [show 2 * i * p + i ^ 2 % p = i ^ 2 % p + (2 * p) * i by ring,
    Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt this, zero_add]

theorem etElem_injective {p : ℕ} (hp : 0 < p) : Function.Injective (etElem p) := by
  intro i j h
  rw [← etElem_div hp i, ← etElem_div hp j, h]

theorem etElem_lt {p K i : ℕ} (hp : 0 < p) (hi : i < K) : etElem p i < (2 * K - 1) * p := by
  unfold etElem
  have h1 := Nat.mod_lt (i ^ 2) hp
  have h2 : 2 * i + 1 ≤ 2 * K - 1 := by omega
  calc 2 * i * p + i ^ 2 % p < 2 * i * p + p := by omega
    _ = (2 * i + 1) * p := by ring
    _ ≤ (2 * K - 1) * p := Nat.mul_le_mul_right _ h2

theorem card_erdosTuran {p : ℕ} (hp : 0 < p) (K : ℕ) : (erdosTuran p K).card = K := by
  rw [erdosTuran, Finset.card_image_of_injective _ (etElem_injective hp), Finset.card_range]

/-- The arithmetic core of the Erdős–Turán construction: for an odd prime `p`, the sum `i + j` and
the residue `i² + j² mod p` determine `{i, j}` among residues `< p`. -/
theorem pair_determined {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {i j i' j' : ℕ}
    (hi : i < p) (_hj : j < p) (hi' : i' < p) (hj' : j' < p) (hs : i + j = i' + j')
    (hq : ((i : ZMod p) ^ 2 + (j : ZMod p) ^ 2) = (i' : ZMod p) ^ 2 + (j' : ZMod p) ^ 2) :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have := Fact.mk hp
  have hs' : (i : ZMod p) + j = i' + j' := by exact_mod_cast congrArg (Nat.cast (R := ZMod p)) hs
  have key : (2 : ZMod p) * ((i : ZMod p) - i') * ((i : ZMod p) - j') = 0 := by
    linear_combination hq - ((j : ZMod p) + i' + j' - i) * hs'
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    exact hp2 this
  have cast_inj : ∀ {a b : ℕ}, a < p → b < p → (a : ZMod p) = b → a = b := by
    intro a b ha hb h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h h2
    · have := cast_inj hi hi' (sub_eq_zero.1 h); left; omega
  · have := cast_inj hi hj' (sub_eq_zero.1 h); right; omega

/-- **Erdős–Turán.** For an odd prime `p` and `K ≤ p`, the set `{2 i p + (i² mod p) : i < K}` is a
Sidon set. -/
theorem erdosTuran_isSidon {p K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : K ≤ p) :
    IsSidon (↑(erdosTuran p K) : Set ℕ) := by
  have hp0 := hp.pos
  intro a ha b hb c hc d hd h
  simp only [erdosTuran, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_range] at ha hb hc hd
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨i', hi', rfl⟩ := hc
  obtain ⟨j', hj', rfl⟩ := hd
  -- split the sum into its quotient and remainder modulo `2p`
  have split : ∀ x y : ℕ, etElem p x + etElem p y = (x ^ 2 % p + y ^ 2 % p) + 2 * p * (x + y) := by
    intro x y; unfold etElem; ring
  have small : ∀ x y : ℕ, x ^ 2 % p + y ^ 2 % p < 2 * p := by
    intro x y; have := Nat.mod_lt (x ^ 2) hp0; have := Nat.mod_lt (y ^ 2) hp0; omega
  rw [split, split] at h
  have hdiv := congrArg (· / (2 * p)) h
  have hmod := congrArg (· % (2 * p)) h
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt (small _ _), Nat.div_eq_of_lt (small _ _)] at hdiv
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (small _ _),
    Nat.mod_eq_of_lt (small _ _)] at hmod
  have hq : ((i : ZMod p) ^ 2 + (j : ZMod p) ^ 2) = (i' : ZMod p) ^ 2 + (j' : ZMod p) ^ 2 := by
    have := congrArg (Nat.cast (R := ZMod p)) hmod
    push_cast [ZMod.natCast_mod] at this
    exact this
  rcases pair_determined hp hp2 (by omega) (by omega) (by omega) (by omega) (by omega) hq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

/-- **Erdős–Turán**, with the size bounds: for an odd prime `p` with `K ≤ p ≤ 2K`, the set
`{2 i p + (i² mod p) : i < K}` is a Sidon set of `K` elements, all below `(2K - 1) p ≤ 2 p² ≤ 8 K²`. -/
theorem erdosTuran_spec {p K : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : K ≤ p) (hpK : p ≤ 2 * K) :
    IsSidon (↑(erdosTuran p K) : Set ℕ) ∧ (erdosTuran p K).card = K ∧
      (∀ d ∈ erdosTuran p K, d < 2 * p ^ 2) ∧ 2 * p ^ 2 ≤ 8 * K ^ 2 := by
  refine ⟨erdosTuran_isSidon hp hp2 hK, card_erdosTuran hp.pos K, ?_, ?_⟩
  · intro d hd
    simp only [erdosTuran, Finset.mem_image, Finset.mem_range] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    calc etElem p i < (2 * K - 1) * p := etElem_lt hp.pos hi
      _ ≤ (2 * p) * p := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * p ^ 2 := by ring
  · have : p ^ 2 ≤ (2 * K) ^ 2 := Nat.pow_le_pow_left hpK 2
    nlinarith

/-- For every `K` there is an odd prime `p` with `K ≤ p ≤ 2K`, provided `K ≥ 2`
(Bertrand–Chebyshev). -/
theorem exists_odd_prime_between {K : ℕ} (hK : 2 ≤ K) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ K ≤ p ∧ p ≤ 2 * K := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul K (by omega)
  exact ⟨p, hp, by omega, h1.le, h2⟩

/-- For every `K` there is a Sidon set of `K` natural numbers, all below `8 K²`, together with an
injective enumeration `e : ℕ → ℕ` (so `D = e '' {0, …, K-1}`). -/
theorem exists_sidon_enum (K : ℕ) :
    ∃ e : ℕ → ℕ, Function.Injective e ∧ IsSidon (↑((Finset.range K).image e) : Set ℕ) ∧
      ∀ i < K, e i < 8 * K ^ 2 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · -- `K ≤ 1`: take `e = id`
    refine ⟨id, Function.injective_id, ?_, ?_⟩
    · intro a ha b hb c hc d hd _
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range, id] at ha hb hc hd
      obtain ⟨_, _, rfl⟩ := ha; obtain ⟨_, _, rfl⟩ := hb
      obtain ⟨_, _, rfl⟩ := hc; obtain ⟨_, _, rfl⟩ := hd
      left; omega
    · intro i hi
      have : K = 1 := by omega
      subst this; simp only [id]; omega
  · obtain ⟨p, hp, hp2, h1, h2⟩ := exists_odd_prime_between hK
    obtain ⟨hS, -, hlt, hl⟩ := erdosTuran_spec hp hp2 h1 h2
    refine ⟨etElem p, etElem_injective hp.pos, hS, fun i hi => ?_⟩
    exact lt_of_lt_of_le (hlt _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hi))) hl

/-- For every `K` there is a Sidon set `D ⊆ {0, …, l - 1}` with `|D| = K` and `l ≤ 8 K²`. -/
theorem exists_sidon_lt (K : ℕ) :
    ∃ l ≤ 8 * K ^ 2, ∃ D : Finset ℕ, IsSidon (↑D : Set ℕ) ∧ D.card = K ∧ ∀ d ∈ D, d < l := by
  obtain ⟨e, he, hS, hlt⟩ := exists_sidon_enum K
  refine ⟨8 * K ^ 2, le_rfl, _, hS, by rw [Finset.card_image_of_injective _ he, Finset.card_range],
    ?_⟩
  intro d hd
  simp only [Finset.mem_image, Finset.mem_range] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  exact hlt i hi

end SidonSet

end Cslib
