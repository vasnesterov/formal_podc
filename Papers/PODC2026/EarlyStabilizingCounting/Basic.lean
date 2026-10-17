import Cslib.Computability.Distributed.Byzantine.SyncCounting.Model
import Mathlib

/-!
# Early-Stabilizing Counting: basic definitions

Lenzen, Loss, *Early-Stabilizing Counting*, PODC 2026 (arXiv 2605.18171) [LL26].

Node set `Fin n`, faulty set `F` with `3 |F| < n` (i.e. `|F| ≤ t := ⌊(n-1)/3⌋`, `res n`).
Time `t ∈ ℕ` is the end of round `t`; time `0` is the arbitrary initial state.

* Counting received values (`cnt`, `Agree`) and quorum facts used by all subroutines.
* Specifications at the level of traces of the correct nodes:
  Definition 2.1 (`CountsFrom`, `OCountsFrom`), the crusader-agreement half of Definition 2.2
  (`Crusader`, with an explicit window), Definition 2.6 (`KCSpec`).
* The leader encoded by a filtered clock value (Algorithm 1, line 2): `leader`.
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

open Finset

/-- The resilience `t = ⌊(n - 1)/3⌋` used by all thresholds. -/
def res (n : ℕ) : ℕ := (n - 1) / 3

/-- Number of indices at which `s` holds `a`. -/
def cnt {n : ℕ} {α : Type*} [DecidableEq α] (s : Fin n → α) (a : α) : ℕ :=
  (univ.filter fun w => s w = a).card

/-- The received vector `m` agrees with the true values `x` on the correct nodes. -/
def Agree {n : ℕ} {α : Type*} (F : Finset (Fin n)) (m x : Fin n → α) : Prop :=
  ∀ w, w ∉ F → m w = x w

/-! ### Specifications -/

/-- Definition 2.1 (`C`-counting from time `s`): the (reduced) outputs of all correct nodes agree
and increase by one modulo `C` per round from time `s` on. -/
def CountsFrom {n : ℕ} (F : Finset (Fin n)) (C : ℕ) (out : ℕ → Fin n → ℕ) (s : ℕ) : Prop :=
  ∃ c₀, ∀ j, ∀ v, v ∉ F → out (s + j) v % C = (c₀ + j) % C

/-- `C`-counting for outputs in `[C] ∪ {⊥}` (filter outputs): from time `s` on, no correct node
outputs `⊥` and the outputs count modulo `K`. -/
def OCountsFrom {n : ℕ} (F : Finset (Fin n)) (K : ℕ) (out : ℕ → Fin n → Option ℕ) (s : ℕ) :
    Prop :=
  ∃ c₀, ∀ j, ∀ v, v ∉ F → out (s + j) v = some ((c₀ + j) % K)

/-- The `W`-round crusader agreement property of Definition 2.2, from time `s` on: if a correct
node outputs `c` at time `τ ≥ s`, then at times `τ + j`, `j ≤ W`, every correct node outputs `⊥`
or `c + j mod K`. (Definition 2.2 of [LL26] uses the window `j ≤ X` for `X`-filtering.) -/
def Crusader {n : ℕ} (F : Finset (Fin n)) (K W s : ℕ) (out : ℕ → Fin n → Option ℕ) : Prop :=
  ∀ τ, s ≤ τ → ∀ v, v ∉ F → ∀ c, out τ v = some c → ∀ j, j ≤ W → ∀ w, w ∉ F →
    out (τ + j) w = none ∨ out (τ + j) w = some ((c + j) % K)

/-- Definition 2.6 (King Consensus), as a property of the inputs `(x v, l v)` and outputs `y v`
of the correct nodes (`none` is `⊥`). -/
structure KCSpec {n : ℕ} (F : Finset (Fin n)) (x : Fin n → ℕ) (l : Fin n → Option (Fin n))
    (y : Fin n → Option ℕ) : Prop where
  /-- Validity: if all correct inputs are `c`, every correct output is `c` or `⊥`. -/
  validity : ∀ c, (∀ v, v ∉ F → x v = c) → ∀ v, v ∉ F → y v = none ∨ y v = some c
  /-- Default: if all correct nodes have no leader, all correct outputs are `⊥`. -/
  default : (∀ v, v ∉ F → l v = none) → ∀ v, v ∉ F → y v = none
  /-- King agreement: if all correct nodes have the same correct leader `ℓ`, every correct output
  equals the leader's output, which is not `⊥`. -/
  king : ∀ ℓ, ℓ ∉ F → (∀ v, v ∉ F → l v = some ℓ) → y ℓ ≠ none ∧ ∀ v, v ∉ F → y v = y ℓ

/-- Algorithm 1, line 2: the leader encoded by a filtered clock value `φ ∈ [a n]`:
node `φ / a` if `φ ≡ 0 mod a`, and `⊥` otherwise (values are read modulo `a n`). -/
def leader (a n : ℕ) (o : Option ℕ) : Option (Fin n) :=
  match o with
  | none => none
  | some φ => if h : φ % a = 0 ∧ φ % (a * n) / a < n then some ⟨φ % (a * n) / a, h.2⟩ else none

/-! ### Counting lemmas -/

section Counting

variable {n : ℕ} {α : Type*} [DecidableEq α]

theorem cnt_le (s : Fin n → α) (a : α) : cnt s a ≤ n := by
  unfold cnt
  exact (card_le_univ _).trans (by simp)

/-- At least the correct nodes holding `a` are counted. -/
theorem cnt_ge_correct (F : Finset (Fin n)) {m x : Fin n → α} (h : Agree F m x) (a : α) :
    (univ.filter fun w => w ∉ F ∧ x w = a).card ≤ cnt m a := by
  unfold cnt
  refine card_le_card fun w hw => ?_
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  rw [h w hw.1]; exact hw.2

/-- At most the correct nodes holding `a` plus the faulty nodes are counted. -/
theorem cnt_le_correct_add (F : Finset (Fin n)) {m x : Fin n → α} (h : Agree F m x) (a : α) :
    cnt m a ≤ (univ.filter fun w => w ∉ F ∧ x w = a).card + F.card := by
  unfold cnt
  calc (univ.filter fun w => m w = a).card
      ≤ ((univ.filter fun w => w ∉ F ∧ x w = a) ∪ F).card := by
        refine card_le_card fun w hw => ?_
        simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
        by_cases hwF : w ∈ F
        · exact Or.inr hwF
        · exact Or.inl ⟨hwF, (h w hwF) ▸ hw⟩
    _ ≤ _ := card_union_le _ _

/-- The number of correct nodes is `n - |F|`. -/
theorem card_correct (F : Finset (Fin n)) :
    (univ.filter fun w : Fin n => w ∉ F).card = n - F.card := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun w => w ∈ F)
  have h2 : (univ.filter fun w : Fin n => w ∈ F) = F := by ext; simp
  rw [h2] at this
  simp only [card_univ, Fintype.card_fin] at this
  omega

/-- `3 |F| < n` gives `|F| ≤ t`. -/
theorem card_le_res {F : Finset (Fin n)} (hF : 3 * F.card < n) : F.card ≤ res n := by
  unfold res; omega

/-- If all correct nodes hold `a`, then `a` is received at least `n - t` times. -/
theorem cnt_all {F : Finset (Fin n)} (hF : 3 * F.card < n) {m x : Fin n → α} (h : Agree F m x)
    {a : α} (ha : ∀ w, w ∉ F → x w = a) : n - res n ≤ cnt m a := by
  have h1 := cnt_ge_correct F h a
  have h2 : (univ.filter fun w => w ∉ F ∧ x w = a) = univ.filter fun w : Fin n => w ∉ F := by
    ext w; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.1, fun hw => ⟨hw, ha w hw⟩⟩
  rw [h2, card_correct] at h1
  have := card_le_res hF
  omega

/-- Two sets of at least `n - t` senders share a correct sender (`n > 3t`, `|F| ≤ t`). -/
theorem exists_correct_of_two_quorums {F : Finset (Fin n)} (hF : 3 * F.card < n)
    {A B : Finset (Fin n)} (hA : n - res n ≤ A.card) (hB : n - res n ≤ B.card) :
    ∃ w, w ∈ A ∧ w ∈ B ∧ w ∉ F := by
  by_contra hcon
  push Not at hcon
  have hsub : A ∩ B ⊆ F := fun w hw => by
    rw [mem_inter] at hw
    exact hcon w hw.1 hw.2
  have h1 := card_le_card hsub
  have h2 := card_union_add_card_inter A B
  have h3 : (A ∪ B).card ≤ n := (card_le_univ _).trans (by simp)
  have := card_le_res hF
  unfold res at *
  omega

end Counting

end EarlyStabilizingCounting
