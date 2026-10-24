import Papers.PODC2014.NetworkConstructors.KRCGraph

/-!
# Protocol 8 (kRC): the protocol and its transitions

Protocol 8 (kRC) of Michail–Spirakis constructs, for a fixed `k ≥ 2`, a connected spanning network
in which all but at most `k − 1` agents have degree `k` (Theorem 12). This file defines the
protocol and classifies its transitions; the proof of Theorem 12 is in `KRCInv.lean`, `KRCReach.lean`, `KRCMerge.lean`.

States: `q_i` (`0 ≤ i ≤ k`, non-leaders) and `l_i` (`1 ≤ i ≤ k + 1`, leaders); the index of a
state is the degree of the agent (`Inv` in `KRCInv.lean`).

**Typo fix.** The paper's rule `(l_{k+1}, l_i, 1) → (l_k, l_{i−1}, 0)` for `1 ≤ i ≤ k` produces
the non-existent state `l_0` for `i = 1`; as in Protocol 7 (2RC), whose rule is
`(l₃, l₁, 1) → (l₂, q₀, 0)`, we read `l_0` as `q_0`.
-/

namespace Podc.NetworkConstructors.KRC

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 8 (kRC): `q i _` is `q_i` (`0 ≤ i ≤ k`) and `l i _ _` is the leader state
`l_i` (`1 ≤ i ≤ k + 1`); `|Q| = 2(k + 1)`. -/
inductive St (k : ℕ) where
  | q (i : ℕ) (h : i ≤ k)
  | l (i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ k + 1)
  deriving DecidableEq

namespace St

variable {k : ℕ}

/-- The index of a state (the intended degree of the agent). -/
def idx : St k → ℕ
  | q i _ => i
  | l i _ _ => i

/-- Leader states `l_i`. -/
def isL : St k → Bool
  | q .. => false
  | l .. => true

@[simp] theorem idx_q (i : ℕ) (h : i ≤ k) : (q i h).idx = i := rfl
@[simp] theorem idx_l (i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ k + 1) : (l i h₁ h₂ : St k).idx = i := rfl
@[simp] theorem isL_q (i : ℕ) (h : i ≤ k) : (q i h).isL = false := rfl
@[simp] theorem isL_l (i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ k + 1) : (l i h₁ h₂ : St k).isL = true := rfl

theorem idx_le (s : St k) : s.idx ≤ k + 1 := by
  cases s <;> simp only [idx] <;> omega

/-- Only `l_{k+1}` has index `k + 1`. -/
theorem idx_le_of_not_isL {s : St k} (h : s.isL = false) : s.idx ≤ k := by
  cases s <;> simp_all [idx]

theorem one_le_idx_of_isL {s : St k} (h : s.isL = true) : 1 ≤ s.idx := by
  cases s <;> simp_all [idx]

theorem injective_isL_idx : Function.Injective fun s : St k => (s.isL, s.idx) := by
  rintro (⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩) (⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩) h <;> simp_all

end St

instance (k : ℕ) : Finite (St k) :=
  Finite.of_injective (fun s : St k => (s.isL, (⟨s.idx, Nat.lt_succ_of_le s.idx_le⟩ : Fin (k + 2))))
    (fun s t h => St.injective_isL_idx (by simpa using h))

open St

/-- The transition function of Protocol 8 (kRC), rule by rule (unlisted triples are
ineffective). The rule `(l_{k+1}, l_1, 1) → (l_k, l_0, 0)` is read as `(l_{k+1}, l_1, 1) →
(l_k, q_0, 0)` (typo fix). -/
def δ (k : ℕ) (hk : 2 ≤ k) : St k → St k → Bool → St k × St k × Bool
  | q i hi, q j hj, false =>
    -- `(q₀, q₀, 0) → (q₁, l₁, 1)`
    if i = 0 ∧ j = 0 then (q 1 (by omega), l 1 le_rfl (by omega), true)
    -- `(q_i, q_j, 0) → (q_{i+1}, q_{j+1}, 1)` for `1 ≤ i < k`, `j < k`
    else if h : 1 ≤ i ∧ i < k ∧ j < k then (q (i + 1) (by omega), q (j + 1) (by omega), true)
    else (q i hi, q j hj, false)
  | l i hi₁ hi₂, l j hj₁ hj₂, false =>
    -- `(l_i, l_j, 0) → (l_{i+1}, q_{j+1}, 1)` for `1 ≤ i, j < k`
    if h : i < k ∧ j < k then (l (i + 1) (by omega) (by omega), q (j + 1) (by omega), true)
    -- `(l_k, l_i, 0) → (l_{k+1}, q_{i+1}, 1)` for `1 ≤ i < k`
    else if h : i = k ∧ j < k then (l (k + 1) (by omega) le_rfl, q (j + 1) (by omega), true)
    -- `(l_k, l_k, 0) → (l_{k+1}, l_{k+1}, 1)`
    else if i = k ∧ j = k then (l (k + 1) (by omega) le_rfl, l (k + 1) (by omega) le_rfl, true)
    else (l i hi₁ hi₂, l j hj₁ hj₂, false)
  | l i hi₁ hi₂, q j hj, false =>
    -- `(l_i, q_j, 0) → (q_{i+1}, l_{j+1}, 1)` for `1 ≤ i < k`, `j < k`
    if h : i < k ∧ j < k then (q (i + 1) (by omega), l (j + 1) (by omega) (by omega), true)
    -- `(l_k, q₀, 0) → (l_{k+1}, q₁, 1)`
    else if i = k ∧ j = 0 then (l (k + 1) (by omega) le_rfl, q 1 (by omega), true)
    else (l i hi₁ hi₂, q j hj, false)
  | l i hi₁ hi₂, q j hj, true =>
    -- swapping: `(l_i, q_j, 1) → (q_i, l_j, 1)` for `1 ≤ i, j ≤ k`
    if h : i ≤ k ∧ 1 ≤ j then (q i h.1, l j h.2 (by omega), true)
    -- `(l_{k+1}, q₁, 1) → (l_k, q₀, 0)`
    else if i = k + 1 ∧ j = 1 then (l k (by omega) (by omega), q 0 (by omega), false)
    -- `(l_{k+1}, q_i, 1) → (l_k, l_{i−1}, 0)` for `2 ≤ i ≤ k`
    else if h : i = k + 1 ∧ 2 ≤ j then
      (l k (by omega) (by omega), l (j - 1) (by omega) (by omega), false)
    else (l i hi₁ hi₂, q j hj, true)
  | l i hi₁ hi₂, l j hj₁ hj₂, true =>
    -- leader elimination: `(l_i, l_j, 1) → (q_i, l_j, 1)` for `1 ≤ i, j ≤ k`
    if h : i ≤ k ∧ j ≤ k then (q i h.1, l j hj₁ hj₂, true)
    -- `(l_{k+1}, l₁, 1) → (l_k, q₀, 0)` (the paper's `l₀` read as `q₀`)
    else if i = k + 1 ∧ j = 1 then (l k (by omega) (by omega), q 0 (by omega), false)
    -- `(l_{k+1}, l_i, 1) → (l_k, l_{i−1}, 0)` for `2 ≤ i ≤ k`
    else if h : i = k + 1 ∧ 2 ≤ j ∧ j ≤ k then
      (l k (by omega) (by omega), l (j - 1) (by omega) (by omega), false)
    -- `(l_{k+1}, l_{k+1}, 1) → (l_k, l_k, 0)`
    else if i = k + 1 ∧ j = k + 1 then
      (l k (by omega) (by omega), l k (by omega) (by omega), false)
    else (l i hi₁ hi₂, l j hj₁ hj₂, true)
  | s, t, c => (s, t, c)

/-- **Protocol 8 (kRC)** of Michail–Spirakis, for `k ≥ 2`: initial state `q₀`, all states are
output states. -/
def kRC (k : ℕ) (hk : 2 ≤ k) : Protocol (St k) where
  init := q 0 (Nat.zero_le _)
  out _ := true
  δ := δ k hk

/-- The three kinds of transitions of kRC: ineffective on the edge (identity, or a leader moves /
is eliminated over an active edge), activation of an edge (both indices `+1`), and deactivation
of an edge by `l_{k+1}` (both indices `−1`). -/
def Kind (k : ℕ) (s t : St k) (c : Bool) (r : St k × St k × Bool) : Prop :=
  (r.2.2 = c ∧ r.1.idx = s.idx ∧ r.2.1.idx = t.idx ∧
      (r = (s, t, c) ∨ (c = true ∧ s.isL = true ∧ r.1.isL = false ∧ r.2.1.isL = true))) ∨
  (c = false ∧ r.2.2 = true ∧ r.1.idx = s.idx + 1 ∧ r.2.1.idx = t.idx + 1 ∧
      ((s.idx < k ∧ t.idx < k) ∨ (s.isL = true ∧ s.idx = k ∧ (t.idx = 0 ∨ t.isL = true))) ∧
      (r.1.isL = true ∨ r.2.1.isL = true ∨ (s.isL = false ∧ t.isL = false ∧ 1 ≤ s.idx))) ∨
  (c = true ∧ r.2.2 = false ∧ r.1.idx + 1 = s.idx ∧ r.2.1.idx + 1 = t.idx ∧ s.idx = k + 1 ∧
      r.1.isL = true ∧ (r.2.1.isL = true ∨ r.2.1.idx = 0))

variable {k : ℕ} (hk : 2 ≤ k)

theorem δ_kind (s t : St k) (c : Bool) : Kind k s t c (δ k hk s t c) := by
  rcases s with ⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩ <;>
    cases c <;> simp only [δ] <;> (try split_ifs) <;> simp [Kind] <;> omega

/-- Two deficient agents (index `< k`) with an inactive edge can activate it, in at least one of
the two orientations. -/
theorem δ_act {s t : St k} (hs : s.idx < k) (ht : t.idx < k) :
    (δ k hk s t false).2.2 = true ∨ (δ k hk t s false).2.2 = true := by
  rcases s with ⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩ <;>
    simp only [idx_q, idx_l] at hs ht <;> simp only [δ] <;> (try split_ifs) <;> (try simp) <;>
    omega

/-- A leader `l_k` opens an edge to `q₀` or to a leader `l_i` (`i ≤ k`). -/
theorem δ_open {s t : St k} (hs : s.isL = true) (hsk : s.idx = k)
    (ht : t.idx = 0 ∨ (t.isL = true ∧ t.idx ≤ k)) : (δ k hk s t false).2.2 = true := by
  rcases s with ⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩ <;>
    simp only [idx_q, idx_l, isL_q, isL_l] at hs hsk ht <;> simp only [δ] <;> (try split_ifs) <;>
    (try simp) <;> first | omega | simp_all

/-- `l_{k+1}` drops any active edge. -/
theorem δ_drop {s t : St k} (hs : s.idx = k + 1) (ht : 1 ≤ t.idx) :
    (δ k hk s t true).2.2 = false := by
  rcases s with ⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩ <;>
    simp only [idx_q, idx_l] at hs ht <;> simp only [δ] <;> (try split_ifs) <;> (try simp) <;>
    omega

/-- A leader `l_i` (`i ≤ k`) moves over an active edge to a non-isolated agent (swap or
elimination). -/
theorem δ_move {s t : St k} (hs : s.isL = true) (hsk : s.idx ≤ k) (ht : 1 ≤ t.idx)
    (htk : t.idx ≤ k) : (δ k hk s t true).1.isL = false ∧ (δ k hk s t true).2.1.isL = true := by
  rcases s with ⟨i, hi⟩ | ⟨i, hi₁, hi₂⟩ <;> rcases t with ⟨j, hj⟩ | ⟨j, hj₁, hj₂⟩ <;>
    simp only [idx_q, idx_l, isL_q, isL_l] at hs hsk ht htk <;> simp only [δ] <;> (try split_ifs) <;>
    (try simp) <;> first | omega | simp_all

end Podc.NetworkConstructors.KRC
