import Mathlib
import Cslib.Computability.Distributed.Byzantine.KingPhase
import Cslib.Foundations.Data.Finset.Quorum
import Podc.Foundations.Data.Finset.Quorum

/-!
# The phase-king layer (§3.4, Table 2, Lemmas 4 and 5)

Every node `v` has an output register `a[v] ∈ [C] ∪ {∞}` (`Option (Fin C)`, `none = ∞`) and an
auxiliary bit `d[v]`. In each round it executes one of three instruction sets (`I₃ℓ`, `I₃ℓ₊₁`,
`I₃ℓ₊₂`, selected by `r % 3`) for a king `ℓ`, on the vector `ma` of received `a`-values.

* `I₃ℓ`:   if fewer than `N - F` nodes sent `a[v]`, `a[v] ← ∞`; increment `a[v]`.
* `I₃ℓ₊₁`: `z_j` = number of received `j`; `d[v] ← [z_{a[v]} ≥ N - F]`;
           `a[v] ← min {j ∈ [C] : z_j > F}` (`∞` if there is none); increment `a[v]`.
* `I₃ℓ₊₂`: if `a[v] = ∞` or `d[v] = 0`, `a[v] ← min {C, a[ℓ]}`; `d[v] ← 1`; increment `a[v]`.

"Increment" is `+1 mod C` on `[C]` and does nothing on `∞`. The paper does not say what
`min ∅` is in `I₃ℓ₊₁`; we use `∞`. In `I₃ℓ₊₂`, `min {C, ∞} = C` and `C + 1 mod C` is used
literally.
-/

namespace SynchronousCounting

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {C : ℕ}

/-- `x + 1 mod C` on `Fin C`. -/
def incr (x : Fin C) : Fin C := ⟨(x.val + 1) % C, Nat.mod_lt _ (Nat.zero_lt_of_lt x.isLt)⟩

/-- "increment a[v]". -/
def inc : Option (Fin C) → Option (Fin C) := Option.map incr

/-- Number of received copies of the value `a`. -/
abbrev cntA (ma : V → Option (Fin C)) (a : Option (Fin C)) : ℕ := univ.countEq ma a

/-- `min {j ∈ [C] : z_j > F}`, `∞` (`none`) if there is no such `j`. -/
def firstHeavy (F : ℕ) (ma : V → Option (Fin C)) : Option (Fin C) :=
  (List.finRange C).find? fun j => decide (F < cntA ma (some j))

/-- `min {C, a}` for `a ∈ [C] ∪ {∞}`. -/
def kingVal : Option (Fin C) → ℕ
  | some x => x.val
  | none => C

/-! ### Counting lemmas -/

variable (Fa : Finset V)

/-- Values held by all correct nodes are received at least `N - |Fa|` times. -/
lemma cntA_of_all (ma : V → Option (Fin C)) (a : Option (Fin C)) (h : ∀ u ∉ Fa, ma u = a) :
    Fintype.card V - Fa.card ≤ cntA ma a := by
  simpa using card_sub_card_le_countEq (s := univ) (f := ma) fun u _ hu => h u hu

omit [DecidableEq V] in
/-- Values held by no correct node are received at most `|Fa|` times. -/
lemma cntA_of_none (ma : V → Option (Fin C)) (a : Option (Fin C)) (h : ∀ u ∉ Fa, ma u ≠ a) :
    cntA ma a ≤ Fa.card := by
  by_contra hlt
  obtain ⟨u, -, hu, hua⟩ := exists_mem_notMem_of_card_lt_countEq (not_le.1 hlt)
  exact h u hu hua

omit [DecidableEq V] in
lemma firstHeavy_eq_none (F : ℕ) (ma : V → Option (Fin C)) (h : ∀ j, cntA ma (some j) ≤ F) :
    firstHeavy F ma = none := by
  unfold firstHeavy
  rw [List.find?_eq_none]
  intro j _; simp only [decide_eq_true_eq, not_lt]; exact h j

omit [DecidableEq V] in
lemma firstHeavy_eq_some (F : ℕ) (ma : V → Option (Fin C)) (x : Fin C) (hx : F < cntA ma (some x))
    (h : ∀ j, j ≠ x → cntA ma (some j) ≤ F) : firstHeavy F ma = some x := by
  unfold firstHeavy
  cases hfind : (List.finRange C).find? (fun j => decide (F < cntA ma (some j))) with
  | none =>
    rw [List.find?_eq_none] at hfind
    have := hfind x (List.mem_finRange x)
    simp only [decide_eq_true_eq] at this
    exact absurd hx this
  | some j =>
    have := List.find?_some hfind
    simp only [decide_eq_true_eq] at this
    by_cases hj : j = x
    · rw [hj]
    · exact absurd this (not_lt.2 (h j hj))

omit [DecidableEq V] in
lemma firstHeavy_mem (F : ℕ) (ma : V → Option (Fin C)) {j : Fin C} (h : firstHeavy F ma = some j) :
    F < cntA ma (some j) := by
  unfold firstHeavy at h
  have := List.find?_some h
  simpa using this

variable [NeZero C]

/-- `min {C, a} + 1 mod C`, the value adopted from the king. -/
def fromKing (a : Option (Fin C)) : Fin C :=
  ⟨(kingVal a + 1) % C, Nat.mod_lt _ (Nat.pos_of_neZero C)⟩

/-- One phase-king step of a node with register values `a`, `d`, receiving `ma`, executing the
instruction set number `r % 3` with king `king`. -/
def pkStep (F : ℕ) (king : V) (r : ℕ) (ma : V → Option (Fin C)) (a : Option (Fin C)) (d : Bool) :
    Option (Fin C) × Bool :=
  if r % 3 = 0 then
    (inc (if cntA ma a < Fintype.card V - F then none else a), d)
  else if r % 3 = 1 then
    (inc (firstHeavy F ma), decide (Fintype.card V - F ≤ cntA ma a))
  else
    (if a = none ∨ d = false then some (fromKing (ma king)) else inc a, true)

/-! ### The step relation of the correct nodes -/

/-- All correct nodes move from `(a, d)` to `(a', d')` by executing instruction set `r % 3` with
king `king`, each on some received vector that agrees with `a` on the correct nodes. -/
def PKStep (F : ℕ) (king : V) (r : ℕ) (a : V → Option (Fin C)) (d : V → Bool)
    (a' : V → Option (Fin C)) (d' : V → Bool) : Prop :=
  ∀ v ∉ Fa, ∃ ma : V → Option (Fin C), (∀ u ∉ Fa, ma u = a u) ∧
    (a' v, d' v) = pkStep F king r ma (a v) (d v)

omit [DecidableEq V] in
/-- The computation behind Lemma 5: a node with `a = x`, `d = 1` that receives `x` at least
`N - F` times and every other value of `[C]` at most `F` times (with `F < N - F`) moves to
`a = x + 1`, `d = 1`, whatever instruction set it executes. -/
theorem pkStep_of_dominant {F : ℕ} (king : V) (r : ℕ) (ma : V → Option (Fin C)) (x : Fin C)
    (hx : Fintype.card V - F ≤ cntA ma (some x)) (hother : ∀ j, j ≠ x → cntA ma (some j) ≤ F)
    (hN : F < Fintype.card V - F) :
    pkStep F king r ma (some x) true = (some (incr x), true) := by
  have hfirst : firstHeavy F ma = some x := firstHeavy_eq_some _ _ _ (by omega) hother
  unfold pkStep
  by_cases h0 : r % 3 = 0
  · rw [ite_eq_left h0, ite_eq_right (show ¬ cntA ma (some x) < Fintype.card V - F by omega)]
    rfl
  · rw [ite_eq_right h0]
    by_cases h1 : r % 3 = 1
    · rw [ite_eq_left h1, hfirst]
      simp only [Prod.mk.injEq, decide_eq_true_eq]
      exact ⟨rfl, hx⟩
    · rw [ite_eq_right h1, ite_eq_right (by simp)]
      rfl

/-- **Lemma 5** (agreement persists, whatever instruction set each node executes). If all correct
nodes have `a = x ∈ [C]` and `d = 1`, a correct node executing any instruction set moves to
`a = x + 1 mod C`, `d = 1`. Needs only `N > 2F`. -/
theorem lemma5 {F : ℕ} (hFa : Fa.card ≤ F) (hN : 2 * F < Fintype.card V) (king : V) (r : ℕ)
    (ma : V → Option (Fin C)) (x : Fin C) (hma : ∀ u ∉ Fa, ma u = some x) :
    pkStep F king r ma (some x) true = (some (incr x), true) :=
  pkStep_of_dominant king r ma x (by have := cntA_of_all Fa ma _ hma; omega)
    (fun j hj => (cntA_of_none Fa ma _ fun u hu h =>
      hj (Option.some_injective _ ((hma u hu).symm.trans h).symm)).trans hFa) (by omega)

/-- **Lemma 5** for whole configurations. -/
theorem lemma5_step {F : ℕ} (hFa : Fa.card ≤ F) (hN : 2 * F < Fintype.card V) {king : V} {r : ℕ}
    {a : V → Option (Fin C)} {d : V → Bool} {a' : V → Option (Fin C)} {d' : V → Bool}
    (hstep : PKStep Fa F king r a d a' d') (x : Fin C) (ha : ∀ v ∉ Fa, a v = some x)
    (hd : ∀ v ∉ Fa, d v = true) : ∀ v ∉ Fa, a' v = some (incr x) ∧ d' v = true := by
  intro v hv
  obtain ⟨ma, hma, he⟩ := hstep v hv
  rw [ha v hv, hd v hv, lemma5 Fa hFa hN king r ma x (fun u hu => (hma u hu).trans (ha u hu))] at he
  simp only [Prod.mk.injEq] at he
  exact ⟨he.1, he.2⟩

/-- **Lemma 4** (a correct king establishes agreement). If all correct nodes execute `I₃ℓ`,
`I₃ℓ₊₁`, `I₃ℓ₊₂` in three consecutive rounds and the king `ℓ` is correct, then afterwards all
correct nodes have the same `a ∈ [C]` and `d = 1`. Needs `N > 3F`. -/
theorem lemma4 {F : ℕ} (hFa : Fa.card ≤ F) (hN : 3 * F < Fintype.card V) {king : V}
    (hking : king ∉ Fa) {r : ℕ} (hr : r % 3 = 0) {k₀ k₁ : V}
    {a₀ a₁ a₂ a₃ : V → Option (Fin C)} {d₀ d₁ d₂ d₃ : V → Bool}
    (h₀ : PKStep Fa F k₀ r a₀ d₀ a₁ d₁) (h₁ : PKStep Fa F k₁ (r + 1) a₁ d₁ a₂ d₂)
    (h₂ : PKStep Fa F king (r + 2) a₂ d₂ a₃ d₃) :
    ∃ y : Fin C, ∀ v ∉ Fa, a₃ v = some y ∧ d₃ v = true := by
  have hcard := card_filter_notMem_univ Fa
  have hFaV := card_le_univ Fa
  have hr1 : (r + 1) % 3 = 1 := by omega
  have hr2 : (r + 2) % 3 = 2 := by omega
  -- (a) after `I₃ℓ` the finite values of correct nodes agree
  have hA : ∀ v ∉ Fa, ∀ x, a₁ v = some x →
      ∃ x', x = incr x' ∧ Fintype.card V - F - Fa.card ≤
        (univ.filter fun u => u ∉ Fa ∧ a₀ u = some x').card := by
    intro v hv x hx
    obtain ⟨ma, hma, he⟩ := h₀ v hv
    unfold pkStep at he
    rw [ite_eq_left hr] at he
    simp only [Prod.mk.injEq] at he
    split_ifs at he with hlt
    · rw [he.1] at hx; simp [inc] at hx
    · cases ha : a₀ v with
      | none => rw [he.1, ha] at hx; simp [inc] at hx
      | some x' =>
        rw [he.1, ha] at hx
        simp only [inc, Option.map_some, Option.some.injEq] at hx
        refine ⟨x', hx.symm, ?_⟩
        have h1 : cntA ma (some x') ≤
            (univ.filter fun u => u ∉ Fa ∧ a₀ u = some x').card + Fa.card :=
          countEq_le_card_filter_notMem_and_add_card (fun u _ hu => hma u hu) _
        rw [ha] at hlt
        omega
  have hagree : ∀ v ∉ Fa, ∀ w ∉ Fa, ∀ x y, a₁ v = some x → a₁ w = some y → x = y := by
    intro v hv w hw x y hx hy
    obtain ⟨x', rfl, hx'⟩ := hA v hv x hx
    obtain ⟨y', rfl, hy'⟩ := hA w hw y hy
    by_contra hne
    have hne' : x' ≠ y' := fun h => hne (h ▸ rfl)
    have hdisj : Disjoint (univ.filter fun u => u ∉ Fa ∧ a₀ u = some x')
        (univ.filter fun u => u ∉ Fa ∧ a₀ u = some y') := by
      rw [disjoint_filter]; rintro u _ ⟨_, h1⟩ ⟨_, h2⟩
      exact hne' (Option.some_injective _ (h1.symm.trans h2))
    have hsub : (univ.filter fun u => u ∉ Fa ∧ a₀ u = some x') ∪
        (univ.filter fun u => u ∉ Fa ∧ a₀ u = some y') ⊆ univ.filter fun u => u ∉ Fa := by
      intro u; simp only [mem_union, mem_filter, mem_univ, true_and]; tauto
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at this
    omega
  -- a common candidate value `x`
  obtain ⟨x, hx⟩ : ∃ x : Fin C, ∀ v ∉ Fa, a₁ v = none ∨ a₁ v = some x := by
    by_cases hex : ∃ v ∉ Fa, ∃ x, a₁ v = some x
    · obtain ⟨v, hv, x, hvx⟩ := hex
      refine ⟨x, fun w hw => ?_⟩
      cases hw' : a₁ w with
      | none => exact Or.inl rfl
      | some y => exact Or.inr (by rw [hagree w hw v hv y x hw' hvx])
    · push Not at hex
      refine ⟨⟨0, Nat.pos_of_neZero C⟩, fun v hv => Or.inl ?_⟩
      cases h : a₁ v with
      | none => rfl
      | some y => exact absurd h (hex v hv y)
  -- (b) after `I₃ℓ₊₁`
  have hB : ∀ v ∉ Fa, ∀ ma : V → Option (Fin C), (∀ u ∉ Fa, ma u = a₁ u) →
      firstHeavy F ma = none ∨ firstHeavy F ma = some x := by
    intro v _ ma hma
    cases h : firstHeavy F ma with
    | none => exact Or.inl rfl
    | some j =>
      right
      by_contra hjx
      have hj := firstHeavy_mem F ma h
      have : cntA ma (some j) ≤ Fa.card := by
        apply cntA_of_none
        intro u hu hmu
        rw [hma u hu] at hmu
        rcases hx u hu with h' | h' <;> rw [h'] at hmu
        · simp at hmu
        · exact hjx (by rw [Option.some_injective _ hmu])
      omega
  have h2val : ∀ v ∉ Fa, a₂ v = none ∨ a₂ v = some (incr x) := by
    intro v hv
    obtain ⟨ma, hma, he⟩ := h₁ v hv
    unfold pkStep at he
    rw [ite_eq_right (by omega), ite_eq_left hr1] at he
    simp only [Prod.mk.injEq] at he
    rw [he.1]
    rcases hB v hv ma hma with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- (c) coherence: a correct node that keeps its value (`a ≠ ∞`, `d = 1`) holds the value of
  -- every correct node
  have hcoh : ∀ w ∉ Fa, ¬ (a₂ w = none ∨ d₂ w = false) → ∀ v ∉ Fa, a₂ v = a₂ w := by
    intro w hw hall
    push Not at hall
    obtain ⟨hwa, hwd⟩ := hall
    have hwa' : a₂ w = some (incr x) := (h2val w hw).resolve_left hwa
    -- `w` had `d = 1`: it saw `a₁ w` at least `N - F` times
    obtain ⟨ma, hma, he⟩ := h₁ w hw
    unfold pkStep at he
    rw [ite_eq_right (by omega), ite_eq_left hr1] at he
    simp only [Prod.mk.injEq] at he
    have hdw : Fintype.card V - F ≤ cntA ma (a₁ w) := by
      have := he.2; simp only [ne_eq, Bool.not_eq_false] at hwd; rw [hwd] at this
      simpa using this.symm
    have ha1w : a₁ w = some x := by
      rcases hx w hw with h | h
      · exfalso
        rw [h] at hdw
        have : firstHeavy F ma = none := by
          apply firstHeavy_eq_none; intro j
          have : cntA ma none + cntA ma (some j) ≤ Fintype.card V :=
            card_univ (α := V) ▸ countEq_add_countEq_le (by simp)
          omega
        rw [he.1, this] at hwa'; simp [inc] at hwa'
      · exact h
    rw [ha1w] at hdw
    -- many correct nodes hold `x` after round `q - 1`
    have hmany : Fintype.card V - F - Fa.card ≤
        (univ.filter fun u => u ∉ Fa ∧ a₁ u = some x).card := by
      have h1 : cntA ma (some x) ≤
          (univ.filter fun u => u ∉ Fa ∧ a₁ u = some x).card + Fa.card :=
        countEq_le_card_filter_notMem_and_add_card (fun u _ hu => hma u hu) _
      omega
    -- hence every correct node computes `x` in `I₃ℓ₊₁`
    have hall2 : ∀ v ∉ Fa, a₂ v = some (incr x) := by
      intro v hv
      obtain ⟨mb, hmb, hev⟩ := h₁ v hv
      unfold pkStep at hev
      rw [ite_eq_right (by omega), ite_eq_left hr1] at hev
      simp only [Prod.mk.injEq] at hev
      have hfx : firstHeavy F mb = some x := by
        apply firstHeavy_eq_some
        · have : (univ.filter fun u => u ∉ Fa ∧ a₁ u = some x).card ≤ cntA mb (some x) :=
            card_filter_notMem_and_le_countEq (fun u _ hu => hmb u hu) _
          omega
        · intro j hj
          refine (cntA_of_none Fa mb _ fun u hu hmu => ?_).trans hFa
          rw [hmb u hu] at hmu
          rcases hx u hu with h' | h' <;> rw [h'] at hmu
          · simp at hmu
          · exact hj (Option.some_injective _ hmu).symm
      rw [hev.1, hfx]; rfl
    intro v hv
    rw [hall2 v hv, hall2 w hw]
  -- (d) the king round: a node that keeps its value increments it, the others adopt
  -- `min {C, a[ℓ]} + 1 mod C` from the correct king (`Cslib.Byzantine.kingPhase_agreement`)
  have hround : ∀ v ∉ Fa, (a₃ v, d₃ v) =
      if a₂ v = none ∨ d₂ v = false then (some (fromKing (a₂ king)), true)
      else (inc (a₂ v), true) := by
    intro v hv
    obtain ⟨mc, hmc, hev⟩ := h₂ v hv
    unfold pkStep at hev
    rw [ite_eq_right (by omega), ite_eq_right (by omega), hmc king hking] at hev
    rw [hev]
    split_ifs <;> rfl
  refine ⟨fromKing (a₂ king), fun v hv => Prod.ext_iff.1 <|
    Cslib.Byzantine.kingPhase_agreement (H := (↑Fa : Set V)ᶜ) (val := a₂)
      (strong := fun v => ¬ (a₂ v = none ∨ d₂ v = false)) (out := fun v => (a₃ v, d₃ v))
      (keep := fun a => (inc a, true)) (adopt := fun a => (some (fromKing a), true))
      (fun w hw hs => hcoh w hw hs king hking) (fun v hv hs => (hround v hv).trans (ite_eq_right hs))
      (fun v hv hs => (hround v hv).trans (ite_eq_left (not_not.1 hs))) (fun v _ hs => ?_) v hv⟩
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 fun h => hs (Or.inl h)
  simp only [hy]
  rfl

end SynchronousCounting
