import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 9 (`c`-Cliques): states and transition function

Protocol 9 of Michail–Spirakis (PODC 2014) partitions the population into `⌊n/c⌋` cliques of
order `c`. States (for `c ≥ 3`):

* `l i` = `l_i` (`0 ≤ i ≤ c − 2`): leader of a partial component with `i` followers;
* `fi j` = `f_j` (`1 ≤ j ≤ c − 2`): former leader, now a follower, still releasing `j` followers;
* `f`: follower of a partial component;
* `lbar i` = `l̄_i` (`0 ≤ i ≤ c − 2`): leader of a component of order `c` that has already
  numbered `i` of its followers;
* `lead` = `l`: leader of a completed component;
* `num k` = `k` (`1 ≤ k ≤ c − 1`): numbered follower of degree `k`;
* `lp k` = `l'_k` (`1 ≤ k ≤ c − 1`): numbered follower of degree `k` currently visited by its
  leader;
* `r`: leader whose token is visiting one of its followers.

Output states (not specified in the paper): `lead`, `r`, `num _`, `lp _` (the states of completed
components).
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 9 (`c`-Cliques). -/
inductive St (c : ℕ) where
  /-- `l_i`, `0 ≤ i ≤ c − 2`. -/
  | l (i : ℕ) (h : i ≤ c - 2)
  /-- `f_j`, `1 ≤ j ≤ c − 2`. -/
  | fi (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ c - 2)
  /-- `f`. -/
  | f
  /-- `l̄_i`, `0 ≤ i ≤ c − 2`. -/
  | lbar (i : ℕ) (h : i ≤ c - 2)
  /-- `l`. -/
  | lead
  /-- The number `k`, `1 ≤ k ≤ c − 1`. -/
  | num (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ c - 1)
  /-- `l'_k`, `1 ≤ k ≤ c − 1`. -/
  | lp (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ c - 1)
  /-- `r`. -/
  | r
  deriving DecidableEq

namespace St

variable {c : ℕ}

/-- Encoding of the states as (tag, index). -/
def encode : St c → Fin 8 × Fin (c + 1)
  | l i _ => (0, ⟨i, by omega⟩)
  | fi j _ _ => (1, ⟨j, by omega⟩)
  | f => (2, 0)
  | lbar i _ => (3, ⟨i, by omega⟩)
  | lead => (4, 0)
  | num k _ _ => (5, ⟨k, by omega⟩)
  | lp k _ _ => (6, ⟨k, by omega⟩)
  | r => (7, 0)

theorem encode_injective : Function.Injective (encode : St c → _) := by
  intro a b h
  cases a <;> cases b <;> simp_all [encode, Fin.ext_iff]

instance : Finite (St c) := Finite.of_injective _ encode_injective

/-- Roots of components: `l_i`, `l̄_i`, `l`, `r`. -/
def isRoot : St c → Bool
  | l .. => true
  | lbar .. => true
  | lead => true
  | r => true
  | _ => false

/-- Numbered followers: `k` and `l'_k`. -/
def isFol : St c → Bool
  | num .. => true
  | lp .. => true
  | _ => false

/-- Visited followers `l'_k`. -/
def isVis : St c → Bool
  | lp .. => true
  | _ => false

/-- Partial leaders `l_i`. -/
def isL : St c → Bool
  | l .. => true
  | _ => false

/-- Releasing followers `f_j`. -/
def isFi : St c → Bool
  | fi .. => true
  | _ => false

/-- Counting leaders `l̄_i`. -/
def isLbar : St c → Bool
  | lbar .. => true
  | _ => false

/-- Output states: those of completed components. -/
def out : St c → Bool
  | lead => true
  | r => true
  | num .. => true
  | lp .. => true
  | _ => false

/-- The number (= degree) of a numbered follower. -/
def idx : St c → ℕ
  | num k .. => k
  | lp k .. => k
  | _ => 0

/-- The number of children in the component forest. -/
def nkids : St c → ℕ
  | l i _ => i
  | fi j _ _ => j
  | lbar _ _ => c - 1
  | lead => c - 1
  | r => c - 1
  | _ => 0

/-- The number of numbered children. -/
def nfol : St c → ℕ
  | lbar i _ => i
  | lead => c - 1
  | r => c - 1
  | _ => 0

/-- The number of visited children. -/
def nvis : St c → ℕ
  | r => 1
  | _ => 0

end St

open St

/-- The transition function of Protocol 9 (`c`-Cliques); unlisted triples are ineffective.
The rule `(l'_i, l'_j, 1) → (l'_{i−1}, l'_{j−1}, 0)` is only given for `i, j ≥ 2` (`l'_0` is not a
state; the case never arises). -/
def δ (c : ℕ) (hc : 3 ≤ c) : St c → St c → Bool → St c × St c × Bool
  | .l i hi, .l j hj, false =>
    if j ≤ i then
      if h : i < c - 2 then
        (.l (i + 1) (by omega), if h0 : j = 0 then .f else .fi j (by omega) (by omega), true)
      else if h0 : j = 0 then (.lbar 1 (by omega), .num 1 le_rfl (by omega), true)
      else (.lbar 0 (by omega), .fi j (by omega) (by omega), true)
    else (.l i hi, .l j hj, false)
  | .fi i h1 h2, .f, true =>
    (if h : 1 < i then .fi (i - 1) (by omega) (by omega) else .f, .l 0 (by omega), false)
  | .lbar i hi, .f, true =>
    (if h : i < c - 2 then .lbar (i + 1) (by omega) else .lead, .num 1 le_rfl (by omega), true)
  | .num i h1 h2, .num j h3 h4, false =>
    if h : i < c - 1 ∧ j < c - 1 then
      (.num (i + 1) (by omega) (by omega), .num (j + 1) (by omega) (by omega), true)
    else (.num i h1 h2, .num j h3 h4, false)
  | .lead, .num i h1 h2, true => (.r, .lp i h1 h2, true)
  | .lp i h1 h2, .lp j h3 h4, true =>
    if h : 2 ≤ i ∧ 2 ≤ j then
      (.lp (i - 1) (by omega) (by omega), .lp (j - 1) (by omega) (by omega), false)
    else (.lp i h1 h2, .lp j h3 h4, true)
  | .lp i h1 h2, .r, true => (.num i h1 h2, .lead, true)
  | a, b, e => (a, b, e)

/-- **Protocol 9 (`c`-Cliques)**, for `c ≥ 3`: initial state `l_0`; output states `l`, `r`,
`1, …, c − 1`, `l'_1, …, l'_{c−1}`. -/
def cliques (c : ℕ) (hc : 3 ≤ c) : Protocol (St c) where
  init := .l 0 (Nat.zero_le _)
  out := St.out
  δ := δ c hc

/-- The effective rules of Protocol 9 (classification of `δ`). -/
theorem δ_cases {c : ℕ} (hc : 3 ≤ c) (a b : St c) (e : Bool) :
    δ c hc a b e = (a, b, e) ∨
    (∃ i hi j hj, a = .l i hi ∧ b = .l j hj ∧ j ≤ i ∧ e = false) ∨
    (∃ i h1 h2, a = .fi i h1 h2 ∧ b = .f ∧ e = true) ∨
    (∃ i hi, a = .lbar i hi ∧ b = .f ∧ e = true) ∨
    (∃ i h1 h2 j h3 h4, a = .num i h1 h2 ∧ b = .num j h3 h4 ∧ i < c - 1 ∧ j < c - 1 ∧
      e = false) ∨
    (∃ i h1 h2, a = .lead ∧ b = .num i h1 h2 ∧ e = true) ∨
    (∃ i h1 h2 j h3 h4, a = .lp i h1 h2 ∧ b = .lp j h3 h4 ∧ 2 ≤ i ∧ 2 ≤ j ∧ e = true) ∨
    (∃ i h1 h2, a = .lp i h1 h2 ∧ b = .r ∧ e = true) := by
  cases a <;> cases b <;> cases e <;> first | (left; rfl) | skip
  · rename_i i hi j hj
    by_cases h : j ≤ i
    · exact .inr (.inl ⟨_, _, _, _, rfl, rfl, h, rfl⟩)
    · exact .inl (by simp [δ, h])
  · exact .inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨_, _, rfl, rfl, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl⟩)))))
  · rename_i i h1 h2 j h3 h4
    by_cases h : i < c - 1 ∧ j < c - 1
    · exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, h.1, h.2, rfl⟩))))
    · exact .inl (by simp [δ, h])
  · rename_i i h1 h2 j h3 h4
    by_cases h : 2 ≤ i ∧ 2 ≤ j
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨_, _, _, _, _, _, rfl, rfl, h.1, h.2, rfl⟩))))))
    · exact .inl (by simp [δ, h])
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, _, _, rfl, rfl, rfl⟩))))))

end Podc.NetworkConstructors.Cliques
