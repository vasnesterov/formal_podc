import Papers.PODC2019.AutomaticSpeedup.Theorem1

/-!
# Superweak `k`-colouring and its trit description (Brandt, PODC 2019, §5.1)

* `superweak k`: each node outputs a colour from `Fin k` (the paper's `{1, …, k}`) and, at each
  port, a pointer kind: demanding `→` (`Ptr.demand`), accepting `⊸` (`Ptr.accept`) or none `•`
  (`Ptr.none`). Node configurations (regular graphs of degree `Δ`): exactly `Δ` labels, one colour,
  and `#⊸ < min (k + 1) #→`. Edge configurations: different colours, or both `•`, or some `⊸`.
* `Trit k = Fin k → Fin 3`: trit sequences of length `k`.
* `tritHalf k`: the paper's "equivalent description" of `Π'_{1/2}` (derived from superweak
  `k`-colouring): labels are trit sequences; an edge is good iff the tritwise sum is `22…2`; a node
  configuration (of `Δ` sequences) is good iff some position `j` has at most `k` zeros and strictly
  more twos than zeros.
* `tritOne k = (tritHalf k).nodeStepMax`: the paper's description of `Π'_1` (Properties A and B).
* `toTrit`: the paper's bijection between the usable `Π'_{1/2}` labels and trit sequences (`0` for
  `{⊸}`, `1` for `{⊸, •}`, `2` for `{→, ⊸, •}` in each colour).
-/

namespace AutomaticSpeedup

open Problem

/-- Pointer kinds of superweak colouring: demanding (`→`), accepting (`⊸`), none (`•`). -/
inductive Ptr
  | demand
  | accept
  | none
  deriving DecidableEq, Repr

instance : Fintype Ptr := ⟨{.demand, .accept, .none}, by intro x; cases x <;> simp⟩

/-- Superweak `k`-colouring (§5.1), for `Δ`-regular graphs. -/
def superweak (k : ℕ) : Problem (Fin k × Ptr) where
  f _ := Set.univ
  g _ := {m | ∃ a b : Fin k × Ptr, m = {a, b} ∧
    (a.1 ≠ b.1 ∨ (a.2 = .none ∧ b.2 = .none) ∨ a.2 = .accept ∨ b.2 = .accept)}
  h Δ := {m | Multiset.card m = Δ ∧ (∃ c, ∀ x ∈ m, x.1 = c) ∧
    Multiset.card (m.filter (·.2 = .accept)) < min (k + 1) (Multiset.card (m.filter (·.2 = .demand)))}

/-- Trit sequences of length `k`. -/
abbrev Trit (k : ℕ) := Fin k → Fin 3

/-- The all-ones trit sequence `11…1`. -/
def ones (k : ℕ) : Trit k := fun _ => 1

/-- Number of sequences in `m` with trit `x` at position `j`. -/
def countAt {k : ℕ} (m : Multiset (Trit k)) (j : Fin k) (x : Fin 3) : ℕ :=
  Multiset.card (m.filter fun a => a j = x)

/-- The trit description of `Π'_{1/2}` for superweak `k`-colouring (§5.1, "An Equivalent
Description"). -/
def tritHalf (k : ℕ) : Problem (Trit k) where
  f _ := Set.univ
  g _ := {m | ∃ a b : Trit k, m = {a, b} ∧ ∀ j, (a j).val + (b j).val = 2}
  h Δ := {m | Multiset.card m = Δ ∧ ∃ j, countAt m j 0 ≤ k ∧ countAt m j 0 < countAt m j 2}

/-- The trit description of `Π'_1` for superweak `k`-colouring (§5.1, "Problem `Π'_1`"):
edges `{W, X}` with some `w ∈ W`, `x ∈ X` summing to `22…2`; nodes: Properties A (every choice
is good for `tritHalf`) and B (maximality). -/
def tritOne (k : ℕ) : Problem (Set (Trit k)) := (tritHalf k).nodeStepMax

/-- The map from `Π'_{1/2}` labels (sets of superweak labels) to trit sequences: in colour `c`,
`2` if `(c, →)` is present, else `1` if `(c, •)` is present, else `0`. On the usable labels this is
the paper's bijection. -/
noncomputable def toTrit {k : ℕ} (Y : Set (Fin k × Ptr)) : Trit k := by
  classical
  exact fun c => if (c, Ptr.demand) ∈ Y then 2 else if (c, Ptr.none) ∈ Y then 1 else 0

end AutomaticSpeedup
