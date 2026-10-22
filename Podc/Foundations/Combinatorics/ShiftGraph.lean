import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

-- CSLib candidate: Cslib/Foundations/Combinatorics/ShiftGraph.lean

/-!
# Colourings of shift graphs

For a linearly ordered set `S` and `k : ℕ`, the *shift graph* on `S` has as vertices the strictly
increasing `(k + 1)`-tuples from `S`, and joins `(a₀, …, a_k)` to `(a₁, …, a_{k+1})` whenever
`a₀ < a₁ < ⋯ < a_{k+1}`. Erdős–Hajnal showed that its chromatic number grows like an iterated
logarithm of `|S|`; this is the combinatorial core of Linial's `Ω(log* n)` lower bound for
colouring rings in the LOCAL model (a `t`-round algorithm on a ring with identifiers from `S`
yields a proper colouring of the shift graph with `k = 2t`).

We state colourings as plain functions `φ : (Fin (k + 1) → α) → C` (their values on tuples that
are not strictly increasing or not from `S` are irrelevant).

## Main statements

* `Cslib.ShiftGraph.card_le_iterate_of_proper`: if `φ` properly colours the shift graph on `S` of
  order `k` with colours `C`, then `|S| ≤ (2 ^ ·)^[k] |C|`.
-/

namespace Cslib.ShiftGraph

/-- `φ : (Fin (k + 1) → α) → C` is a proper colouring of the shift graph of order `k` on `S`:
for every strictly increasing `(k + 2)`-tuple `a` from `S`, the colours of its first `k + 1` and
its last `k + 1` entries differ. -/
def IsProper {α C : Type*} [Preorder α] (S : Set α) (k : ℕ) (φ : (Fin (k + 1) → α) → C) : Prop :=
  ∀ a : Fin (k + 2) → α, StrictMono a → (∀ i, a i ∈ S) → φ (a ∘ Fin.castSucc) ≠ φ (a ∘ Fin.succ)

theorem _root_.Fin.snoc_comp_succ {β : Type*} {n : ℕ} (a : Fin (n + 1) → β) (x : β) :
    (Fin.snoc a x : Fin (n + 2) → β) ∘ Fin.succ = Fin.snoc (a ∘ Fin.succ) x := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [Function.comp_apply, Fin.succ_last, Fin.snoc_last]
  | cast j => simp only [Function.comp_apply, Fin.succ_castSucc, Fin.snoc_castSucc]

theorem _root_.Fin.strictMono_snoc {α : Type*} [Preorder α] {n : ℕ} {a : Fin (n + 1) → α}
    (ha : StrictMono a) {x : α} (hx : a (Fin.last n) < x) :
    StrictMono (Fin.snoc a x : Fin (n + 2) → α) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  induction i using Fin.lastCases with
  | last => simpa [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last] using hx
  | cast j =>
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact ha (Fin.castSucc_lt_succ (i := j))

/-- Shift-graph colouring bound (Erdős–Hajnal, Linial): a proper colouring of the shift graph of
order `k` on `S` with colours `C` forces `|S| ≤ (2 ^ ·)^[k] |C|`.

Proof by induction on `k`: colour a `(k + 1)`-tuple `b` by the *set* of colours of its extensions
`snoc b x` with `x ∈ S`, `x > b_k`; this is a proper colouring of order `k - 1` with `2 ^ |C|`
colours. For `k = 0`, `x ↦ φ (fun _ => x)` is injective on `S`. -/
theorem card_le_iterate_of_proper {α : Type*} [LinearOrder α] (S : Finset α) (k : ℕ) :
    ∀ {C : Type*} [Fintype C] (φ : (Fin (k + 1) → α) → C), IsProper (S : Set α) k φ →
      S.card ≤ (fun c => 2 ^ c)^[k] (Fintype.card C) := by
  induction k with
  | zero =>
    intro C _ φ hφ
    simp only [Function.iterate_zero, id]
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun x => φ (fun _ => x)) (by simp) ?_
    have key : ∀ x ∈ S, ∀ y ∈ S, x < y → φ (fun _ => x) ≠ φ (fun _ => y) := by
      intro x hx y hy hlt hxy
      refine hφ ![x, y] ?_ ?_ ?_
      · rw [Fin.strictMono_iff_lt_succ]
        intro i; fin_cases i; simpa using hlt
      · intro i; fin_cases i <;> simpa
      · convert hxy using 2 <;> funext i <;> fin_cases i <;> rfl
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key x hx y hy hlt hxy
    · exact key y hy x hx hlt hxy.symm
  | succ k ih =>
    intro C _ φ hφ
    classical
    let ψ : (Fin (k + 1) → α) → Finset C := fun b =>
      (S.filter fun x => b (Fin.last k) < x).image fun x => φ (Fin.snoc b x)
    have hψ : IsProper (S : Set α) k ψ := by
      intro a ha hS heq
      -- `φ a` is a colour of an extension of `a ∘ castSucc`
      have hmem : φ a ∈ ψ (a ∘ Fin.castSucc) := by
        refine Finset.mem_image.2 ⟨a (Fin.last _), Finset.mem_filter.2 ⟨hS _, ?_⟩, ?_⟩
        · exact ha (by simp [Fin.lt_def])
        · congr 1
          conv_rhs => rw [← Fin.snoc_init_self a]
          rfl
      rw [heq] at hmem
      obtain ⟨x, hx, hφx⟩ := Finset.mem_image.1 hmem
      obtain ⟨hxS, hlt⟩ := Finset.mem_filter.1 hx
      have hlt' : a (Fin.last (k + 1)) < x := by simpa using hlt
      refine hφ (Fin.snoc a x) (Fin.strictMono_snoc ha hlt') ?_ ?_
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hxS
        | cast j => simpa [Fin.snoc_castSucc] using hS j
      · rw [Fin.snoc_comp_castSucc, Fin.snoc_comp_succ, hφx]
    have := ih ψ hψ
    rw [Fintype.card_finset] at this
    rwa [Function.iterate_succ_apply]

end Cslib.ShiftGraph
