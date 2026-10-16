import Papers.PODC2025.UniqueIDsBoundedRegisters.Defs

/-!
# Anonymity is necessary for the lower bound

Without anonymity the problem is trivial: process `p` returns `⟪p, c⟫` (Cantor pairing) where `c`
counts its own previous calls. This uses **no shared register at all** (`k = 0`), is wait-free and
returns distinct identifiers in every execution, for any number of calls (`nonAnonymous_correct`).
So the hypothesis `Anonymous` of `theorem_4_1` cannot be dropped (the paper assumes anonymity in
its model, §2).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory Impl

variable (m : ℕ) [NeZero m]

/-- Process `p` returns `Nat.pair p c` for its `c`-th call. No shared memory. -/
def idAlg : Impl uidObj (fun _ : Fin 0 => bReg m) ℕ ℕ where
  memInit i := i.elim0
  locInit _ := 0
  invoke _ c _ := c
  act p c := .ret (Nat.pair p c) (c + 1)

lemma idAlg_inv : ∀ (α : List (Label ℕ uidObj)) (C : Config uidObj (fun _ : Fin 0 => bReg m) ℕ ℕ),
    (idAlg m).run α = some C → ∀ p, respsOf α p = (List.range (C.loc p)).map (Nat.pair p) := by
  intro α
  induction α using List.reverseRecOn with
  | nil => intro C h p; simp only [run_nil, Option.some.injEq] at h; subst h; rfl
  | append_singleton α ℓ ih =>
    intro C h p
    obtain ⟨C₀, h₀, h₁⟩ := (idAlg m).runFrom_eq_some_of_append h
    rw [runFrom_singleton] at h₁
    have ih' := ih C₀ h₀
    rw [respsOf_append]
    cases ℓ with
    | inv q o =>
      obtain ⟨-, -, -, hl, -⟩ := step_inv h₁
      rw [ih' p, hl]
      by_cases hq : q = p
      · subst hq; simp [idAlg]
      · simp [Function.update_of_ne (Ne.symm hq), Label.retOf]
    | tau q =>
      obtain ⟨-, -, i, -, -, -, -, -⟩ := step_tau h₁
      exact i.elim0
    | ret q r =>
      obtain ⟨-, -, -, l, hact, hl⟩ := step_ret h₁
      simp only [idAlg, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      rw [ih' p, hl]
      by_cases hq : q = p
      · subst hq; simp [List.range_succ, Label.retOf]
      · simp [Function.update_of_ne (Ne.symm hq), Label.retOf, hq]

/-- The non-anonymous algorithm is wait-free and correct for any number of calls, with `k = 0`
registers. -/
theorem nonAnonymous_correct : (idAlg m).WaitFree ∧ ∀ N, CorrectUpTo (idAlg m) N := by
  refine ⟨fun e p n _ => ⟨0, fun t _ ht => ?_⟩, fun N α hα _ x y hx hy hxy => ?_⟩
  · have hs := e.step_eq t
    rw [ht] at hs
    obtain ⟨-, -, i, -, -, -, -, -⟩ := step_tau hs
    exact i.elim0
  · obtain ⟨C, hC⟩ := hα
    have hr := idAlg_inv m α C hC
    obtain ⟨p, a⟩ := x
    obtain ⟨q, b⟩ := y
    simp only [Completed, hr, List.length_map, List.length_range] at hx hy
    simp only [respOf, hr, List.getElem?_map, List.getElem?_range hx, List.getElem?_range hy,
      Option.map_some, ne_eq, Option.some.injEq]
    intro h
    have := Nat.pair_eq_pair.1 h
    exact hxy (Prod.ext this.1 this.2)

end Cslib.SharedMemory.UniqueIDs
