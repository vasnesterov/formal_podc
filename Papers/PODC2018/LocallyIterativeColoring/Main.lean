import Papers.PODC2018.LocallyIterativeColoring.AG
import Cslib.Computability.Distributed.Local.ColorReduction
import Mathlib

/-!
# Corollaries 3.5 and 3.6 of [BEG18] with natural-number colours

* `enc`, `dec`: the paper's representation of a colour `i < q²` as the pair `⟨⌊i/q⌋, i mod q⟩`.
* `agNat q`: the AG algorithm acting on natural-number colours.
* `agNat_isProper`, `agNat_lt` (**Corollary 3.5**): from a proper `q²`-colouring, `2Δ < q`, `q`
  prime: every round is proper and after `q` rounds all colours are `< q`.
* `agPrime Δ k`: the least prime `q > max (2Δ) ⌊√k⌋`; by Bertrand's postulate
  `q ≤ 2 max (2Δ+1) (⌊√k⌋+1)`, i.e. `q = O(Δ)` for `k = O(Δ²)`.
* `begColoring Δ k`: AG for `q` rounds followed by the standard colour reduction from `q` to
  `Δ + 1` colours.
* `begColoring_isProper`, `begColoring_le` (**Corollary 3.6**, from an initial proper `k`-colouring):
  a locally-iterative algorithm keeping a proper colouring in every round and reaching a proper
  `(Δ + 1)`-colouring within `2q - (Δ + 1) ≤ 4 max (2Δ+1) (⌊√k⌋+1)` rounds. The initial
  `O(Δ²)`-colouring is Linial's (`O(log* n)` rounds), see `LinialComposition.lean` when available.
-/

namespace BEG18

open Cslib.LocallyIterative

variable {V : Type*} {G : SimpleGraph V}

section Encoding

variable (q : ℕ) [NeZero q]

/-- Encode a pair `⟨a, b⟩ ∈ GF(q)²` as the natural number `a q + b < q²`. -/
def enc (x : ZMod q × ZMod q) : ℕ := x.1.val * q + x.2.val

/-- Decode a natural number `i` as the pair `⟨⌊i/q⌋, i mod q⟩` (Section 3.1 of [BEG18]). -/
def dec (i : ℕ) : ZMod q × ZMod q := (((i / q : ℕ) : ZMod q), ((i : ℕ) : ZMod q))

theorem dec_enc (x : ZMod q × ZMod q) : dec q (enc q x) = x := by
  have hq : 0 < q := Nat.pos_of_neZero q
  obtain ⟨a, b⟩ := x
  simp only [dec, enc]
  have hb := ZMod.val_lt b
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hb, zero_add]
  ext <;> simp

theorem enc_dec {i : ℕ} (hi : i < q * q) : enc q (dec q i) = i := by
  have hq : 0 < q := Nat.pos_of_neZero q
  simp only [enc, dec, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hi)]
  exact Nat.div_add_mod' i q

theorem enc_lt (x : ZMod q × ZMod q) : enc q x < q * q := by
  have h1 := ZMod.val_lt x.1
  have h2 := ZMod.val_lt x.2
  simp only [enc]
  nlinarith

theorem enc_injective : Function.Injective (enc q) :=
  Function.LeftInverse.injective (dec_enc q)

omit [NeZero q] in
theorem enc_zero_fst (b : ZMod q) : enc q (0, b) = b.val := by simp [enc]

end Encoding

/-- The AG algorithm on natural-number colours `i < q²`, via `i ↦ ⟨⌊i/q⌋, i mod q⟩`. -/
noncomputable def agNat (q : ℕ) [NeZero q] : Algorithm ℕ :=
  (ag : Algorithm (ZMod q × ZMod q)).comap (enc q) (dec q)

section Nat

variable {q : ℕ} [NeZero q]

theorem agNat_run {φ : V → ℕ} (hφ : ∀ v, φ v < q * q) (t : ℕ) :
    (agNat q).run G φ t = enc q ∘ (ag : Algorithm (ZMod q × ZMod q)).run G (dec q ∘ φ) t := by
  have : φ = enc q ∘ (dec q ∘ φ) := funext fun v => (enc_dec q (hφ v)).symm
  conv_lhs => rw [this]
  exact Algorithm.run_comap _ (dec_enc q) _ t

theorem isProper_dec_comp {φ : V → ℕ} (hφ : ∀ v, φ v < q * q) (hp : IsProper G φ) :
    IsProper G (dec q ∘ φ) := fun u v huv h =>
  hp huv (by rw [← enc_dec q (hφ u), ← enc_dec q (hφ v)]; exact congrArg (enc q) h)

/-- Lemma 3.2 of [BEG18] with natural-number colours. -/
theorem agNat_isProper {φ : V → ℕ} (hφ : ∀ v, φ v < q * q) (hp : IsProper G φ) (t : ℕ) :
    IsProper G ((agNat q).run G φ t) := by
  rw [agNat_run hφ, isProper_comp_iff (enc_injective q)]
  exact ag_isProper (isProper_dec_comp hφ hp) t

theorem agNat_lt_sq {φ : V → ℕ} (hφ : ∀ v, φ v < q * q) (t : ℕ) (v : V) :
    (agNat q).run G φ t v < q * q := by
  rw [agNat_run hφ]; exact enc_lt q _

/-- **Corollary 3.5 of [BEG18].** `q` prime, `2Δ < q`, maximum degree `≤ Δ`: from a proper
`q²`-colouring, after `q` rounds of AG the colouring is a proper `q`-colouring. (Every intermediate
colouring is proper by `agNat_isProper`; every round needs one bit per edge since a vertex only
announces whether it finalized.) -/
theorem agNat_lt [Fact q.Prime] [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (hq : 2 * Δ < q) {φ : V → ℕ} (hφ : ∀ v, φ v < q * q) (hp : IsProper G φ) (v : V) :
    (agNat q).run G φ q v < q := by
  rw [agNat_run hφ, Function.comp_apply]
  have h := ag_final_of_two_mul_lt (isProper_dec_comp hφ hp) hΔ hq v
  have : (ag : Algorithm (ZMod q × ZMod q)).run G (dec q ∘ φ) q v =
      (0, ((ag : Algorithm (ZMod q × ZMod q)).run G (dec q ∘ φ) q v).2) := Prod.ext h rfl
  rw [this, enc_zero_fst]
  exact ZMod.val_lt _

end Nat

/-! ### Choosing the prime (Bertrand's postulate) -/

/-- The least prime `q > max (2Δ) ⌊√k⌋`. -/
noncomputable def agPrime (Δ k : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (max (2 * Δ) (Nat.sqrt k) + 1))

theorem agPrime_spec (Δ k : ℕ) :
    max (2 * Δ) (Nat.sqrt k) + 1 ≤ agPrime Δ k ∧ (agPrime Δ k).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes _)

theorem agPrime_prime (Δ k : ℕ) : (agPrime Δ k).Prime := (agPrime_spec Δ k).2

instance (Δ k : ℕ) : Fact (agPrime Δ k).Prime := ⟨agPrime_prime Δ k⟩

instance (Δ k : ℕ) : NeZero (agPrime Δ k) := ⟨(agPrime_prime Δ k).ne_zero⟩

theorem two_mul_lt_agPrime (Δ k : ℕ) : 2 * Δ < agPrime Δ k := by
  have := (agPrime_spec Δ k).1; omega

theorem lt_agPrime_sq (Δ k : ℕ) : k < agPrime Δ k * agPrime Δ k := by
  have h := (agPrime_spec Δ k).1
  have hs : Nat.sqrt k + 1 ≤ agPrime Δ k := by omega
  calc k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := Nat.lt_succ_sqrt k
    _ ≤ _ := Nat.mul_le_mul hs hs

/-- Bertrand's postulate: `q ≤ 2 max (2Δ + 1) (⌊√k⌋ + 1)`, so `q = O(Δ)` when `k = O(Δ²)`. -/
theorem agPrime_le (Δ k : ℕ) : agPrime Δ k ≤ 2 * max (2 * Δ + 1) (Nat.sqrt k + 1) := by
  set N := max (2 * Δ) (Nat.sqrt k)
  by_cases hN : N = 0
  · have : agPrime Δ k ≤ 2 := Nat.find_min' _ ⟨by omega, Nat.prime_two⟩
    omega
  · obtain ⟨p, hp, hNp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul N hN
    have : agPrime Δ k ≤ p := Nat.find_min' _ ⟨by omega, hp⟩
    omega

/-! ### Corollary 3.6 -/

/-- The locally-iterative `(Δ + 1)`-colouring algorithm of Corollary 3.6 of [BEG18], starting from a
proper `k`-colouring: `q = agPrime Δ k` rounds of AG, then the standard colour reduction from `q`
to `Δ + 1` colours. -/
noncomputable def begColoring (Δ k : ℕ) : Algorithm ℕ :=
  (agNat (agPrime Δ k)).seq (agPrime Δ k) (colorReduction (agPrime Δ k) Δ)

/-- Number of rounds of `begColoring Δ k`. -/
noncomputable def begRounds (Δ k : ℕ) : ℕ := agPrime Δ k + (agPrime Δ k - (Δ + 1))

theorem begRounds_le (Δ k : ℕ) : begRounds Δ k ≤ 4 * max (2 * Δ + 1) (Nat.sqrt k + 1) := by
  have := agPrime_le Δ k; unfold begRounds; omega

variable [G.LocallyFinite]

/-- **Corollary 3.6 of [BEG18] (locally-iterative property).** From a proper `k`-colouring of a graph
of maximum degree `≤ Δ`, every colouring computed by `begColoring Δ k` is proper. -/
theorem begColoring_isProper {Δ k : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {φ : V → ℕ}
    (hφ : ∀ v, φ v < k) (hp : IsProper G φ) (t : ℕ) :
    IsProper G ((begColoring Δ k).run G φ t) := by
  set q := agPrime Δ k
  have hφq : ∀ v, φ v < q * q := fun v => (hφ v).trans (lt_agPrime_sq Δ k)
  rcases le_or_gt t q with ht | ht
  · rw [begColoring, Algorithm.run_seq_of_le _ _ _ ht]
    exact agNat_isProper hφq hp t
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht.le
    rw [begColoring, Algorithm.run_seq_add]
    exact colorReduction_isProper hΔ (agNat_isProper hφq hp q)
      (agNat_lt hΔ (two_mul_lt_agPrime Δ k) hφq hp) s

/-- **Corollary 3.6 of [BEG18] (running time).** From a proper `k`-colouring of a graph of maximum
degree `≤ Δ`, after `begRounds Δ k ≤ 4 max (2Δ+1) (⌊√k⌋+1)` rounds (`= O(Δ)` for `k = O(Δ²)`),
`begColoring Δ k` has computed a proper `(Δ + 1)`-colouring (all colours `≤ Δ`); it stays so
afterwards. -/
theorem begColoring_le {Δ k : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {φ : V → ℕ}
    (hφ : ∀ v, φ v < k) (hp : IsProper G φ) {t : ℕ} (ht : begRounds Δ k ≤ t) (v : V) :
    (begColoring Δ k).run G φ t v ≤ Δ := by
  set q := agPrime Δ k
  have hφq : ∀ v, φ v < q * q := fun v => (hφ v).trans (lt_agPrime_sq Δ k)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show q ≤ t by unfold begRounds at ht; omega)
  rw [begColoring, Algorithm.run_seq_add]
  exact colorReduction_le hΔ (agNat_isProper hφq hp q)
    (agNat_lt hΔ (two_mul_lt_agPrime Δ k) hφq hp) (by unfold begRounds at ht; omega) v

end BEG18
