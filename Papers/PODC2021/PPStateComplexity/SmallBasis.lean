import Papers.PODC2021.PPStateComplexity.Model
import Podc.Computability.Distributed.PopulationProtocols.Multiset.Rackoff

/-!
# Mathematical structure of stable sets (Section 3)

* Lemma 3.1: `SC_b` (and `SC`) are downward closed (`Protocol.Stable.of_le`).
* Lemma 3.2: `SC_b` and `SC` have bases of norm `≤ β = 2^(2(2n+1)!+1)` with at most
  `ϑ(n) = 2^((2n+2)!)` elements (`Protocol.exists_small_basis_stable`,
  `Protocol.exists_small_basis_SC`). The proof uses the Rackoff-type bound
  `Cslib.PopulationProtocol.MReach.exists_short_cover` (covering sequences of length
  `≤ 2^(2(2n+1)!)`), proved in `Podc/Computability/PetriNets/Rackoff.lean`.

A *basis element* `(B, S)` of a set `X` of configurations is a pair with `B + ℕ^S ⊆ X`
(`IsBasisElem`); `InCone B S C` means `C ∈ B + ℕ^S`.
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol Finset

variable {Q : Type*} [DecidableEq Q]

/-- `C ∈ B + ℕ^S`. -/
def InCone (B : Multiset Q) (S : Finset Q) (C : Multiset Q) : Prop :=
  ∃ D : Multiset Q, (∀ q ∈ D, q ∈ S) ∧ C = B + D

/-- `(B, S)` is a basis element of `X`: `B + ℕ^S ⊆ X`. -/
def IsBasisElem (X : Multiset Q → Prop) (B : Multiset Q) (S : Finset Q) : Prop :=
  ∀ D : Multiset Q, (∀ q ∈ D, q ∈ S) → X (B + D)

theorem IsBasisElem.mem {X : Multiset Q → Prop} {B : Multiset Q} {S : Finset Q}
    (h : IsBasisElem X B S) {C : Multiset Q} (hC : InCone B S C) : X C := by
  obtain ⟨D, hD, rfl⟩ := hC
  exact h D hD

/-- The small basis constant `β = 2^(2(2n+1)!+1)` of Definition 3. -/
def beta (n : ℕ) : ℕ := 2 ^ (2 * (2 * n + 1).factorial + 1)

/-- The bound `ϑ(n) = 2^((2n+2)!)` on the number of basis elements (Lemma 3.2). -/
def vartheta (n : ℕ) : ℕ := 2 ^ (2 * n + 2).factorial

/-- The multiset with `f q` copies of each state `q`. -/
def ofCount [Fintype Q] (f : Q → ℕ) : Multiset Q := ∑ q : Q, Multiset.replicate (f q) q

@[simp] theorem count_ofCount [Fintype Q] (f : Q → ℕ) (a : Q) :
    (ofCount f).count a = f a := by
  rw [ofCount, Multiset.count_sum']
  simp [Multiset.count_replicate]

theorem count_pre_le_two (t : Transition Q) (q : Q) : t.pre.count q ≤ 2 :=
  (Multiset.count_le_card q _).trans (by simp)

/-- Removing agents from states that are `2|w|`-populated preserves a firing sequence `w`
("a transition moves at most two agents out of a given state", proof of Lemma 3.2). -/
theorem firesSeq_of_add {w : List (Transition Q)} {B D E : Multiset Q}
    (h : FiresSeq w (B + D) E) (hB : ∀ q ∈ D, 2 * w.length ≤ B.count q) :
    ∃ E', FiresSeq w B E' ∧ E = E' + D := by
  induction w generalizing B with
  | nil => exact ⟨B, rfl, h⟩
  | cons t w ih =>
    obtain ⟨C₁, ht, hw⟩ := h
    have hpre : t.pre ≤ B := by
      rw [Multiset.le_iff_count]
      intro q
      by_cases hq : q ∈ D
      · have := hB q hq; have := count_pre_le_two t q; simp at *; omega
      · have h1 := Multiset.count_le_of_le q ht.1
        rw [Multiset.count_add, Multiset.count_eq_zero.2 hq] at h1
        simpa using h1
    have hB₁ : t.Fires B (B - t.pre + t.post) := ⟨hpre, rfl⟩
    have hC₁ : C₁ = (B - t.pre + t.post) + D := by
      rw [ht.2]
      exact (Transition.Fires.add_right hB₁ D).2.symm
    subst hC₁
    obtain ⟨E', hE', rfl⟩ := ih hw (fun q hq => by
      have := hB q hq
      have := count_pre_le_two t q
      have := Multiset.count_le_of_le q hpre
      simp only [List.length_cons, Multiset.count_add, Multiset.count_sub] at *
      omega)
    exact ⟨E', ⟨_, hB₁, hE'⟩, rfl⟩

namespace Protocol

variable {P : Protocol Q}

/-- **Lemma 3.1.** `SC_b` is downward closed. -/
theorem Stable.of_le {b : Bool} {C C' : Multiset Q} (h : P.Stable b C) (hle : C' ≤ C) :
    P.Stable b C' := by
  intro C'' hC'' q hq
  have h1 : P.Reach C (C'' + (C - C')) := by
    have := MReach.add_right hC'' (C - C')
    rwa [add_tsub_cancel_of_le hle] at this
  exact h _ h1 q (Multiset.mem_add.2 (.inl hq))

/-- `SC` is downward closed. -/
theorem SC.of_le {C C' : Multiset Q} (h : P.SC C) (hle : C' ≤ C) : P.SC C' :=
  h.imp (fun h => h.of_le hle) (fun h => h.of_le hle)

/-- The truncation `(B, S)` of `C` at `k`: `S = {q | C(q) > k}`, `B(q) = min(C(q), k)`. -/
def trunc [Fintype Q] (k : ℕ) (C : Multiset Q) : Multiset Q × Finset Q :=
  (ofCount fun q => min (C.count q) k, univ.filter fun q => k < C.count q)

theorem trunc_le [Fintype Q] (k : ℕ) (C : Multiset Q) : (trunc k C).1 ≤ C := by
  rw [Multiset.le_iff_count]; intro q; simp [trunc]

theorem inCone_trunc [Fintype Q] (k : ℕ) (C : Multiset Q) :
    InCone (trunc k C).1 (trunc k C).2 C := by
  refine ⟨C - (trunc k C).1, fun q hq => ?_, (add_tsub_cancel_of_le (trunc_le k C)).symm⟩
  rw [← Multiset.count_pos] at hq
  simp only [trunc, Multiset.count_sub, count_ofCount, mem_filter, mem_univ, true_and] at hq ⊢
  omega

variable [Fintype Q]

/-- The Rackoff-type length bound for covering sequences, `2^(2(2n+1)!)`. -/
abbrev rackoff (n : ℕ) : ℕ := 2 ^ (2 * (2 * n + 1).factorial)

theorem beta_eq (n : ℕ) : beta n = 2 * rackoff n := by
  simp [beta, rackoff, pow_succ, mul_comm]

/-- **Lemma 3.2 (norm part).** If `C` is `b`-stable then its truncation at `β` is a basis element
of `SC_b` containing `C`. -/
theorem Stable.trunc_isBasisElem {b : Bool} {C : Multiset Q} (h : P.Stable b C) :
    IsBasisElem (P.Stable b) (trunc (beta (Fintype.card Q)) C).1
      (trunc (beta (Fintype.card Q)) C).2 := by
  set k := beta (Fintype.card Q)
  intro D hD C' hC' q hq
  obtain ⟨w, C'', hwT, hw, hqC'', hlen⟩ := MReach.exists_short_cover hC' hq
  obtain ⟨E', hE', rfl⟩ := firesSeq_of_add hw (fun s hs => by
    have := hD s hs
    simp only [trunc, mem_filter, mem_univ, true_and] at this
    simp only [trunc, count_ofCount]
    rw [min_eq_right this.le]
    have : k = 2 * 2 ^ (2 * (2 * Fintype.card Q + 1).factorial) := beta_eq _
    omega)
  rcases Multiset.mem_add.1 hqC'' with hq' | hq'
  · exact (h.of_le (trunc_le k C)) E' (hE'.mreach hwT) q hq'
  · have := hD q hq'
    simp only [trunc, mem_filter, mem_univ, true_and] at this
    exact h.out q (Multiset.count_pos.1 (by omega))

/-! ### Counting small basis elements -/

/-- Decoding a code `g : Q → Option (Fin (k+1))` into a pair `(B, S)`: `none` means `q ∈ S`
(and `B(q) = k`), `some j` means `q ∉ S` and `B(q) = j`. -/
def decode (k : ℕ) (g : Q → Option (Fin (k + 1))) : Multiset Q × Finset Q :=
  (ofCount fun q => (g q).elim k Fin.val, univ.filter fun q => g q = none)

/-- The code of the truncation of `C` at `k`. -/
def encode (k : ℕ) (C : Multiset Q) : Q → Option (Fin (k + 1)) := fun q =>
  if h : k < C.count q then none else some ⟨C.count q, by omega⟩

theorem decode_encode (k : ℕ) (C : Multiset Q) : decode k (encode k C) = trunc k C := by
  ext q
  · simp only [decode, trunc, count_ofCount, encode]
    split_ifs with h <;> simp <;> omega
  · simp only [decode, trunc, encode, mem_filter, mem_univ, true_and]
    by_cases h : k < C.count q <;> simp [h]

/-- The `(k + 2)^n` candidate pairs of norm at most `k`. -/
def cands (k : ℕ) : Finset (Multiset Q × Finset Q) := univ.image (decode k)

theorem card_cands (k : ℕ) : (cands (Q := Q) k).card ≤ (k + 2) ^ Fintype.card Q := by
  refine card_image_le.trans ?_
  simp [Fintype.card_fun, Fintype.card_option]

theorem count_le_of_mem_cands {k : ℕ} {p : Multiset Q × Finset Q} (hp : p ∈ cands k) (q : Q) :
    p.1.count q ≤ k := by
  obtain ⟨g, -, rfl⟩ := mem_image.1 hp
  simp only [decode, count_ofCount]
  cases g q <;> simp; omega

theorem trunc_mem_cands (k : ℕ) (C : Multiset Q) : trunc k C ∈ cands k :=
  mem_image.2 ⟨_, mem_univ _, decode_encode k C⟩

/-- `(β + 2)^n ≤ ϑ(n)`. -/
theorem beta_add_two_pow_le (n : ℕ) : (beta n + 2) ^ n ≤ vartheta n := by
  set a := 2 * (2 * n + 1).factorial
  have h1 : beta n + 2 ≤ 2 ^ (a + 2) := by
    have : 2 ≤ 2 ^ (a + 1) := Nat.le_self_pow (by omega) 2
    show 2 ^ (a + 1) + 2 ≤ 2 ^ (a + 2)
    rw [pow_succ 2 (a + 1)]; omega
  have h2 : n * (a + 2) ≤ (2 * n + 2).factorial := by
    have hf : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1).factorial :=
      Nat.factorial_succ _
    have : n ≤ (2 * n + 1).factorial :=
      (Nat.self_le_factorial n).trans (Nat.factorial_le (by omega))
    rw [hf]; simp only [a]; nlinarith
  calc (beta n + 2) ^ n ≤ (2 ^ (a + 2)) ^ n := Nat.pow_le_pow_left h1 n
    _ = 2 ^ (n * (a + 2)) := by rw [← pow_mul, mul_comm]
    _ ≤ vartheta n := Nat.pow_le_pow_right (by omega) h2

/-- **Small bases** (Lemma 3.2, generic form): if the truncation at `β` of every element of `X`
is a basis element of `X`, then `X` has a base of norm `≤ β` with at most `ϑ(n)` elements. -/
theorem exists_small_basis (X : Multiset Q → Prop)
    (hX : ∀ C, X C → IsBasisElem X (trunc (beta (Fintype.card Q)) C).1
      (trunc (beta (Fintype.card Q)) C).2) :
    ∃ Bs : Finset (Multiset Q × Finset Q), Bs.card ≤ vartheta (Fintype.card Q) ∧
      (∀ p ∈ Bs, (∀ q, p.1.count q ≤ beta (Fintype.card Q)) ∧ IsBasisElem X p.1 p.2) ∧
      ∀ C, X C ↔ ∃ p ∈ Bs, InCone p.1 p.2 C := by
  classical
  refine ⟨(cands (beta (Fintype.card Q))).filter fun p => IsBasisElem X p.1 p.2, ?_, ?_, ?_⟩
  · exact (card_filter_le _ _).trans ((card_cands _).trans (beta_add_two_pow_le _))
  · intro p hp
    rw [mem_filter] at hp
    exact ⟨count_le_of_mem_cands hp.1, hp.2⟩
  · intro C
    refine ⟨fun hC => ⟨_, mem_filter.2 ⟨trunc_mem_cands _ C, hX C hC⟩, inCone_trunc _ C⟩, ?_⟩
    rintro ⟨p, hp, hC⟩
    exact (mem_filter.1 hp).2.mem hC

/-- **Lemma 3.2** for `SC_b`: a base of norm `≤ β` with at most `ϑ(n)` elements. -/
theorem exists_small_basis_stable (b : Bool) :
    ∃ Bs : Finset (Multiset Q × Finset Q), Bs.card ≤ vartheta (Fintype.card Q) ∧
      (∀ p ∈ Bs, (∀ q, p.1.count q ≤ beta (Fintype.card Q)) ∧
        IsBasisElem (P.Stable b) p.1 p.2) ∧
      ∀ C, P.Stable b C ↔ ∃ p ∈ Bs, InCone p.1 p.2 C :=
  exists_small_basis _ fun _ hC => hC.trunc_isBasisElem

/-- **Lemma 3.2** for `SC = SC_0 ∪ SC_1`. -/
theorem exists_small_basis_SC :
    ∃ Bs : Finset (Multiset Q × Finset Q), Bs.card ≤ vartheta (Fintype.card Q) ∧
      (∀ p ∈ Bs, (∀ q, p.1.count q ≤ beta (Fintype.card Q)) ∧ IsBasisElem P.SC p.1 p.2) ∧
      ∀ C, P.SC C ↔ ∃ p ∈ Bs, InCone p.1 p.2 C := by
  refine exists_small_basis _ fun C hC D hD => ?_
  rcases hC with hC | hC
  · exact .inl (hC.trunc_isBasisElem D hD)
  · exact .inr (hC.trunc_isBasisElem D hD)

end Protocol

end Podc.PPStateComplexity
