import Papers.PODC2017.LCLGrids.Theorem9

/-!
# Non-vacuity: a `2n`-round 3-colouring algorithm for odd tori

The hypotheses of Theorem 9 are satisfiable: `globalAlg n` is a `2n`-round algorithm
(`globalAlg_local`) that properly 3-colours every oriented `n × n` torus with distinct
identifiers, for every odd `n ≥ 3` (`globalAlg_colours3`). Each node sees the whole torus, takes
the node `u₀` with the smallest identifier as the origin and outputs the colour of its own
position relative to `u₀` in a fixed proper 3-colouring `κ` of the torus. So the lower bound
`n ≤ 8T + 8` of `theorem9` is tight up to a constant factor.
-/

namespace Podc.LCLGrids

open Finset

variable {n : ℕ}

/-- A proper 3-colouring of the cycle `ℤ/n` for odd `n ≥ 3`: alternate `0, 1`, and use `2` at
`n - 1`. -/
def φ (x : ZMod n) : ZMod 3 := if x.val + 1 = n then 2 else ((x.val % 2 : ℕ) : ZMod 3)

lemma φ_succ_ne [NeZero n] (hn : Odd n) (h3 : 3 ≤ n) (x : ZMod n) : φ (x + 1) ≠ φ x := by
  have hx := x.val_lt
  obtain ⟨k, rfl⟩ := hn
  have hval : (x + 1).val = if x.val + 1 = 2 * k + 1 then 0 else x.val + 1 := by
    rw [ZMod.val_add, ZMod.val_one'' (by omega)]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  unfold φ
  rw [hval]
  have h2 : ∀ a : ℕ, a % 2 = 0 ∨ a % 2 = 1 := fun a => Nat.mod_two_eq_zero_or_one a
  by_cases h1 : x.val + 1 = 2 * k + 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h1)]
    simp only [Nat.zero_mod, Nat.cast_zero]; decide
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h4 : x.val + 1 + 1 = 2 * k + 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h4), ite_eq_right_of_eq_false _ _ (eq_false h1)]
      have : x.val % 2 = 1 := by omega
      rw [this]; decide
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h4), ite_eq_right_of_eq_false _ _ (eq_false h1)]
      rcases h2 x.val with h | h
      · rw [h, show (x.val + 1) % 2 = 1 by omega]; decide
      · rw [h, show (x.val + 1) % 2 = 0 by omega]; decide

/-- The colour of a residue mod 3. -/
def toCol (a : ZMod 3) : Col := if a = 0 then .one else if a = 1 then .two else .three

lemma toCol_injective : Function.Injective toCol := by decide

/-- A proper 3-colouring of the torus (odd `n ≥ 3`). -/
def κ (p : Pos n) : Col := toCol (φ p.1 + φ p.2)

/-- The offsets `[0, n)²`, which reach every node exactly once. -/
def box (n : ℕ) : Finset (ℤ × ℤ) := Finset.Ico (0 : ℤ) n ×ˢ Finset.Ico (0 : ℤ) n

lemma mem_box {d : ℤ × ℤ} : d ∈ box n ↔ 0 ≤ d.1 ∧ d.1 < n ∧ 0 ≤ d.2 ∧ d.2 < n := by
  simp [box, and_assoc]

/-- The offsets of `[0, n)²` carrying the smallest identifier. -/
def IsMinOff (n : ℕ) (g : ℤ × ℤ → ℕ) (d : ℤ × ℤ) : Prop := d ∈ box n ∧ ∀ d' ∈ box n, g d ≤ g d'

/-- The global algorithm: pick an offset `d ∈ [0, n)²` with the smallest identifier and output
the colour `κ(-d)` of the own position relative to that node. -/
noncomputable def globalAlg (n : ℕ) (g : ℤ × ℤ → ℕ) : Col :=
  κ (((-(Classical.epsilon (IsMinOff n g)).1 : ℤ) : ZMod n),
    ((-(Classical.epsilon (IsMinOff n g)).2 : ℤ) : ZMod n))

lemma globalAlg_local : GridLocal (2 * n) (globalAlg n) := by
  intro g h hgh
  have hb : ∀ d ∈ box n, g d = h d := fun d hd => by
    rw [mem_box] at hd
    exact hgh d (by rw [abs_of_nonneg hd.1, abs_of_nonneg hd.2.2.1]; push_cast; omega)
  have hP : IsMinOff n g = IsMinOff n h := by
    funext d
    apply propext
    constructor
    · rintro ⟨hd, hm⟩; exact ⟨hd, fun d' hd' => by rw [← hb d hd, ← hb d' hd']; exact hm d' hd'⟩
    · rintro ⟨hd, hm⟩; exact ⟨hd, fun d' hd' => by rw [hb d hd, hb d' hd']; exact hm d' hd'⟩
  unfold globalAlg
  rw [hP]

lemma globalAlg_colours3 (hn : Odd n) (h3 : 3 ≤ n) (B : ℕ) : Colours3 n B (globalAlg n) := by
  have : NeZero n := ⟨by omega⟩
  intro I hI _
  -- the node with the smallest identifier
  obtain ⟨u₀, -, hu₀⟩ := exists_min_image (univ : Finset (Pos n)) I univ_nonempty
  have hoff : ∀ v : Pos n, ∃ d ∈ box n, sh v d.1 d.2 = u₀ ∧ ∀ d' ∈ box n,
      gview I v d ≤ gview I v d' := by
    intro v
    refine ⟨(((u₀ - v).1.val : ℤ), ((u₀ - v).2.val : ℤ)), ?_, ?_, ?_⟩
    · rw [mem_box]; have := (u₀ - v).1.val_lt; have := (u₀ - v).2.val_lt; omega
    · simp [sh]
    · intro d' _
      simp only [gview]
      have : sh v ((((u₀ - v).1.val : ℤ), ((u₀ - v).2.val : ℤ)) : ℤ × ℤ).1
          ((((u₀ - v).1.val : ℤ), ((u₀ - v).2.val : ℤ)) : ℤ × ℤ).2 = u₀ := by simp [sh]
      rw [this]; exact hu₀ _ (mem_univ _)
  -- every node computes its position relative to `u₀`
  have hout : ∀ v : Pos n, colouring (globalAlg n) I v = κ (v - u₀) := by
    intro v
    have hex : ∃ d, IsMinOff n (gview I v) d := by
      obtain ⟨d, hd, -, hm⟩ := hoff v; exact ⟨d, hd, hm⟩
    simp only [colouring, globalAlg]
    obtain ⟨hd, hm⟩ := Classical.epsilon_spec hex
    obtain ⟨d₀, hd₀, he₀, -⟩ := hoff v
    set d := Classical.epsilon (IsMinOff n (gview I v))
    have hle : I (sh v d.1 d.2) ≤ I u₀ := by
      have := hm d₀ hd₀; simp only [gview] at this; rwa [he₀] at this
    have heq : sh v d.1 d.2 = u₀ :=
      hI (le_antisymm hle (hu₀ _ (mem_univ _)))
    congr 1
    rw [← heq]
    ext <;> simp [sh]
  intro v
  simp only [hout]
  constructor
  · intro h
    have := toCol_injective h
    have e : (sh v 1 0 - u₀).1 = (v - u₀).1 + 1 := by simp [sh]; ring
    have e2 : (sh v 1 0 - u₀).2 = (v - u₀).2 := by simp [sh]
    rw [e, e2] at this
    exact φ_succ_ne hn h3 _ (add_right_cancel this).symm
  · intro h
    have := toCol_injective h
    have e : (sh v 0 1 - u₀).2 = (v - u₀).2 + 1 := by simp [sh]; ring
    have e2 : (sh v 0 1 - u₀).1 = (v - u₀).1 := by simp [sh]
    rw [e, e2] at this
    exact φ_succ_ne hn h3 _ (add_left_cancel this).symm

/-- The hypotheses of Theorem 9 are satisfiable, with `T = 2n` rounds. -/
example (hn : Odd n) (h3 : 3 ≤ n) :
    GridLocal (2 * n) (globalAlg n) ∧ Colours3 n (8 * n ^ 2) (globalAlg n) :=
  ⟨globalAlg_local, globalAlg_colours3 hn h3 _⟩

end Podc.LCLGrids
