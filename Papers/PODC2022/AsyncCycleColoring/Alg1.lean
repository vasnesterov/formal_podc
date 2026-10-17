import Papers.PODC2022.AsyncCycleColoring.Simulation
import Papers.PODC2022.AsyncCycleColoring.Mex
import Papers.PODC2022.AsyncCycleColoring.Changes

/-!
# Algorithm 1 (6-colouring): definition, correctness, palette, symmetry

Section 3.1 of the paper. Code for process `p` with neighbours `q`, `q'`:

```
Input: X_p ∈ ℕ;  Initially c_p = (a_p, b_p) ← (0, 0)
Forever:
  write(X_p, c_p) and read((X_q, c_q), (X_q', c_q'))
  if c_p ∉ {c_q, c_q'} then return(c_p)
  else
    a_p ← min ℕ ∖ { a_u | u ∼ p, X_u > X_p }
    b_p ← min ℕ ∖ { b_u | u ∼ p, X_u < X_p }
```

A neighbour whose register is still `⊥` contributes nothing. We allow identifiers in an arbitrary
linear order `ι` (the paper: `ℕ`); this makes the symmetry `a ↔ b`, `X ↦ toDual X` available
(`alg1_dual_step`).
-/

namespace AsyncCycle

variable {ι : Type*} [LinearOrder ι]

/-- Local state of Algorithm 1 (also the register content). -/
structure St1 (ι : Type*) where
  X : ι
  a : ℕ
  b : ℕ
deriving DecidableEq

/-- The colour `c = (a, b)` of a state. -/
def St1.col (u : St1 ι) : ℕ × ℕ := (u.a, u.b)

/-- Awake neighbours (registers different from `⊥`). -/
def awake {α : Type*} (l r : Option α) : List α := [l, r].filterMap id

/-- New `a`: `min ℕ ∖ { a_u | u awake neighbour, X_u > X }`. -/
def upA (x : ι) (l r : Option (St1 ι)) : ℕ := mex (((awake l r).filter (fun u => x < u.X)).map St1.a)

/-- New `b`: `min ℕ ∖ { b_u | u awake neighbour, X_u < X }`. -/
def downB (x : ι) (l r : Option (St1 ι)) : ℕ := mex (((awake l r).filter (fun u => u.X < x)).map St1.b)

/-- One round of Algorithm 1. -/
def alg1Step (s : St1 ι) (l r : Option (St1 ι)) : St1 ι ⊕ (ℕ × ℕ) :=
  if s.col ∉ (awake l r).map St1.col then Sum.inr s.col
  else Sum.inl ⟨s.X, upA s.X l r, downB s.X l r⟩

/-- Algorithm 1. -/
def alg1 (ι : Type*) [LinearOrder ι] : Alg (St1 ι) (ℕ × ℕ) := ⟨alg1Step⟩

/-- Initial states: identifier `X p`, colour `(0, 0)`. -/
def init1 {n : ℕ} (X : ZMod n → ι) : ZMod n → St1 ι := fun p => ⟨X p, 0, 0⟩

/-! ### Correctness and palette (Theorem 3.1, second and third items) -/

lemma alg1_claimSafe : ClaimSafe (alg1 ι) (fun s => {s.col}) := by
  intro s l r o h
  simp only [alg1, alg1Step] at h
  split_ifs at h with h1
  cases h
  refine ⟨rfl, ?_, ?_⟩ <;> rintro x rfl hx <;> simp only [Set.mem_singleton_iff] at hx <;>
    exact h1 (List.mem_map.2 ⟨x, by simp [awake], hx.symm⟩)

/-- Theorem 3.1, correctness: the outputs properly colour the terminated processes. -/
theorem alg1_properOutputs {n : ℕ} (X : ZMod n → ι) : ProperOutputs (alg1 ι) (init1 X) :=
  properOutputs_of_claimSafe alg1_claimSafe

lemma length_awake_le {α : Type*} (l r : Option α) : (awake l r).length ≤ 2 :=
  (List.length_filterMap_le _ _).trans (by simp)

lemma length_awake_filter_add (x : ι) (l r : Option (St1 ι)) :
    ((awake l r).filter (fun u => x < u.X)).length +
      ((awake l r).filter (fun u => u.X < x)).length ≤ 2 := by
  refine le_trans ?_ (length_awake_le l r)
  induction (awake l r) with
  | nil => simp
  | cons u t ih =>
    simp only [List.filter_cons, List.length_cons]
    by_cases h1 : x < u.X
    · have h2 : ¬ u.X < x := not_lt.2 h1.le
      simp [h1, h2]; omega
    · by_cases h2 : u.X < x
      · simp [h1, h2]; omega
      · simp [h1, h2]; omega

/-- Theorem 3.1, palette: every output `(a, b)` satisfies `a + b ≤ 2` (six colours). -/
theorem alg1_outputs_six {n : ℕ} (X : ZMod n → ι) :
    OutputsIn (alg1 ι) (init1 X) {c | c.1 + c.2 ≤ 2} := by
  refine outputsIn_of_inv (Inv := fun s => s.a + s.b ≤ 2) (fun _ => by simp [init1]) ?_ ?_
  · intro s l r s' _ h
    simp only [alg1, alg1Step] at h
    split_ifs at h
    cases h
    have h1 := mex_le_length (((awake l r).filter (fun u => s.X < u.X)).map St1.a)
    have h2 := mex_le_length (((awake l r).filter (fun u => u.X < s.X)).map St1.b)
    have h3 := length_awake_filter_add s.X l r
    simp only [List.length_map] at h1 h2
    simp only [upA, downB]
    omega
  · intro s l r o hs h
    simp only [alg1, alg1Step] at h
    split_ifs at h
    cases h
    simpa [St1.col] using hs

/-! ### Symmetry: exchanging `a` and `b` and reversing the order of identifiers -/

/-- The dual state: identifier in the dual order, colours swapped. -/
def St1.dual (s : St1 ι) : St1 ιᵒᵈ := ⟨OrderDual.toDual s.X, s.b, s.a⟩

lemma awake_map {α β : Type*} (φ : α → β) (l r : Option α) :
    awake (l.map φ) (r.map φ) = (awake l r).map φ := by
  cases l <;> cases r <;> rfl

lemma alg1_dual_step (s : St1 ι) (l r : Option (St1 ι)) :
    (alg1 ιᵒᵈ).step s.dual (l.map St1.dual) (r.map St1.dual) =
      Sum.map St1.dual Prod.swap ((alg1 ι).step s l r) := by
  simp only [alg1, alg1Step]
  have hmem : s.dual.col ∈ (awake (l.map St1.dual) (r.map St1.dual)).map St1.col ↔
      s.col ∈ (awake l r).map St1.col := by
    rw [awake_map, List.map_map]
    simp only [List.mem_map, Function.comp, St1.col, St1.dual, Prod.mk.injEq]
    constructor <;> rintro ⟨u, hu, h1, h2⟩ <;> exact ⟨u, hu, h2, h1⟩
  by_cases h : s.col ∈ (awake l r).map St1.col
  · rw [ite_eq_right (by simpa [hmem] using h), ite_eq_right (by simpa using h)]
    simp only [Sum.map_inl, St1.dual, upA, downB, Sum.inl.injEq, St1.mk.injEq, true_and]
    rw [awake_map]
    constructor
    · congr 1
      rw [List.filter_map, List.map_map]
      refine congrArg₂ List.map rfl (List.filter_congr fun u _ => ?_)
      simp [St1.dual]
    · congr 1
      rw [List.filter_map, List.map_map]
      refine congrArg₂ List.map rfl (List.filter_congr fun u _ => ?_)
      simp [St1.dual]
  · rw [ite_eq_left (by simpa [hmem] using h), ite_eq_left (by simpa using h)]
    rfl

/-- Executions of Algorithm 1 for `X` and for the reversed order are the same up to swapping
`a` and `b`. -/
theorem run_alg1_dual {n : ℕ} (X : ZMod n → ι) (σ : ℕ → Finset (ZMod n)) (t : ℕ) :
    run (alg1 ιᵒᵈ) (init1 (fun p => OrderDual.toDual (X p))) σ t =
      (run (alg1 ι) (init1 X) σ t).map St1.dual Prod.swap :=
  run_map St1.dual Prod.swap alg1_dual_step (init1 X) σ t

theorem actsAt_alg1_dual {n : ℕ} (X : ZMod n → ι) (σ : ℕ → Finset (ZMod n)) (t : ℕ)
    (p : ZMod n) :
    ActsAt (alg1 ιᵒᵈ) (init1 (fun p => OrderDual.toDual (X p))) σ t p ↔
      ActsAt (alg1 ι) (init1 X) σ t p :=
  actsAt_map St1.dual Prod.swap alg1_dual_step (init1 X) σ t p

theorem workActs_alg1_dual {n : ℕ} (X : ZMod n → ι) (σ : ℕ → Finset (ZMod n)) (p : ZMod n)
    (T : ℕ) :
    workActs (alg1 ιᵒᵈ) (init1 (fun p => OrderDual.toDual (X p))) σ p T =
      workActs (alg1 ι) (init1 X) σ p T :=
  workActs_map St1.dual Prod.swap alg1_dual_step (init1 X) σ p T

end AsyncCycle
