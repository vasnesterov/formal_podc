import Papers.PODC2020.LongLivedSnapshotsPolylog.BoundedIncrement

/-!
# Write logs along executions

Generic facts about the write log `wlogFrom I w C α` of `BoundedIncrement.lean`: it is the
concatenation of the writes of the individual steps (`wlogFrom_append`), it only depends on the
longest valid prefix of `α` (`exists_valid_prefix`), and a criterion for `StepBounded`
(`writesTo_stepBounded`): if the state `mv C` of a max register is the maximum of the values
written to it so far, and every write of `v` performed in a reachable configuration `C`
satisfies `v ≤ mv C + ℓ`, then the sequence of written values is `ℓ`-step-bounded.
-/

namespace Podc.LongLivedSnapshotsPolylog.Section4

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
variable {κ : Type}

/-- The writes performed by the step `ℓ` from `C` (at most one). -/
def stepLog (w : P → L → Option (κ × ℕ)) (C : Config A B P L) : Label P A → List (κ × ℕ)
  | .tau p => (w p (C.loc p)).toList
  | _ => []

/-- Selecting the values written to the register `k`. -/
def selK [DecidableEq κ] (k : κ) (e : κ × ℕ) : Option ℕ := if e.1 = k then some e.2 else none

section

variable (I : Impl A B P L) (w : P → L → Option (κ × ℕ))

lemma wlogFrom_cons_of_step {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C')
    (α : List (Label P A)) :
    wlogFrom I w C (ℓ :: α) = stepLog w C ℓ ++ wlogFrom I w C' α := by
  simp only [wlogFrom, h]; cases ℓ <;> rfl

lemma wlogFrom_cons_of_none {C : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = none)
    (α : List (Label P A)) : wlogFrom I w C (ℓ :: α) = [] := by
  simp only [wlogFrom, h]

lemma wlogFrom_append : ∀ (α : List (Label P A)) {C C' : Config A B P L},
    I.runFrom C α = some C' → ∀ β, wlogFrom I w C (α ++ β) = wlogFrom I w C α ++ wlogFrom I w C' β
  | [], C, C', h, β => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp [wlogFrom]
  | ℓ :: α, C, C', h, β => by
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [List.cons_append, wlogFrom_cons_of_step I w hs, wlogFrom_cons_of_step I w hs,
        wlogFrom_append α h β, List.append_assoc]

lemma wlogFrom_singleton {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') :
    wlogFrom I w C [ℓ] = stepLog w C ℓ := by
  rw [wlogFrom_cons_of_step I w h]; simp [wlogFrom]

/-- The write log of `α` is the write log of a valid prefix of `α`. -/
lemma exists_valid_prefix : ∀ (α : List (Label P A)) (C : Config A B P L),
    ∃ β C', I.runFrom C β = some C' ∧ wlogFrom I w C α = wlogFrom I w C β
  | [], C => ⟨[], C, rfl, rfl⟩
  | ℓ :: α, C => by
    cases hs : I.step C ℓ with
    | none => exact ⟨[], C, rfl, by rw [wlogFrom_cons_of_none I w hs]; rfl⟩
    | some C₁ =>
      obtain ⟨β, C', h, he⟩ := exists_valid_prefix α C₁
      refine ⟨ℓ :: β, C', by simp [hs, h], ?_⟩
      rw [wlogFrom_cons_of_step I w hs, wlogFrom_cons_of_step I w hs, he]

end

lemma stepBounded_append {ℓ : ℕ} {ws : List ℕ} {v : ℕ} (h : StepBounded ℓ ws)
    (hv : v ≤ lmax ws + ℓ) : StepBounded ℓ (ws ++ [v]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i ws.length with hlt | hge
  · rw [List.getElem_append_left hlt, List.take_append_of_le_length hlt.le]
    exact h i hlt
  · have hi' : i = ws.length := by omega
    subst hi'
    simpa using hv

/-- **Criterion for `StepBounded`.** Let `mv C` be the state of the max register `k` in the
configuration `C`: initially `0`, and after each step the maximum of its old state and the value
written by the step (if any). If every write of `v` to `k` from a reachable configuration `C`
satisfies `v ≤ mv C + bd`, then in every (not necessarily valid) sequence of labels the
values written to `k` are `bd`-step-bounded. -/
theorem writesTo_stepBounded [DecidableEq κ] (I : Impl A B P L) (w : P → L → Option (κ × ℕ))
    (k : κ) (mv : Config A B P L → ℕ) (bd : ℕ) (h0 : mv I.initCfg = 0)
    (hmv : ∀ α C ℓ C', I.run α = some C → I.step C ℓ = some C' →
      mv C' = max (mv C) (lmax ((stepLog w C ℓ).filterMap (selK k))))
    (hb : ∀ α C p C' v, I.run α = some C → I.step C (.tau p) = some C' →
      w p (C.loc p) = some (k, v) → v ≤ mv C + bd)
    (α : List (Label P A)) : StepBounded bd (writesTo I w α k) := by
  have hws : ∀ α, writesTo I w α k = (wlogFrom I w I.initCfg α).filterMap (selK k) :=
    fun _ => rfl
  obtain ⟨β, C, hβ, he⟩ := exists_valid_prefix I w α I.initCfg
  rw [hws, he, ← hws]
  refine (Impl.run_induction (Q := fun β C => StepBounded bd (writesTo I w β k) ∧
    lmax (writesTo I w β k) = mv C) ⟨fun i hi => by simp [writesTo, wlogFrom] at hi, by
      simp [writesTo, wlogFrom, h0]⟩ ?_ hβ).1
  intro β C ℓ C' hβ ⟨ih1, ih2⟩ hs
  have hlog : writesTo I w (β ++ [ℓ]) k =
      writesTo I w β k ++ (stepLog w C ℓ).filterMap (selK k) := by
    rw [hws, hws, wlogFrom_append I w β hβ, wlogFrom_singleton I w hs, List.filterMap_append]
  rw [hlog, hmv β C ℓ C' hβ hs, ← ih2]
  cases ℓ with
  | inv p o => simp [stepLog]; exact ih1
  | ret p r => simp [stepLog]; exact ih1
  | tau p =>
    cases hw : w p (C.loc p) with
    | none => simp [stepLog, hw]; exact ih1
    | some e =>
      obtain ⟨k', v⟩ := e
      by_cases hk : k' = k
      · subst hk
        simp only [stepLog, hw, Option.toList_some, List.filterMap_cons, selK, ite_true,
          List.filterMap_nil, lmax_cons, lmax_nil]
        refine ⟨stepBounded_append ih1 ?_, by rw [lmax_append]; simp⟩
        rw [ih2]; exact hb β C p C' v hβ hs hw
      · simp [stepLog, hw, selK, hk]; exact ih1

end Podc.LongLivedSnapshotsPolylog.Section4
