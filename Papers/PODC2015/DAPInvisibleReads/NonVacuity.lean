import Papers.PODC2015.DAPInvisibleReads.Impossibility

/-!
# Non-vacuity of the hypotheses of Theorems 1 and 2

The trivial TM `trivTM` answers every operation immediately, without touching shared memory:
reads return the initial value, writes and `tryC` succeed. It is WDAP, has obstruction-free
(hence isolated-commit) write transactions, wait-free invisible read-only transactions and legal
reads. So the hypotheses of `theorem_1` and `theorem_2` (other than the RTO conclusion they refute)
are satisfiable together; by Theorem 1, `trivTM` violates RTO — as it obviously does.
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

variable {X V P : Type} [DecidableEq P]

/-- No base objects are needed: a single dummy one. -/
abbrev unitObj : ObjSpec := ⟨Unit, Unit, Unit, (), fun _ _ => ((), ())⟩

/-- The response of the trivial TM to an operation. -/
def trivResp (v₀ : X → V) (u : V) : TOp X V → V
  | .read x => v₀ x
  | .write _ v => v
  | .tryC => u

/-- The trivial TM: a process remembers its pending operation and answers it at once. -/
def trivTM (v₀ : X → V) (u : V) : Impl (tmSpec X V) (fun _ : Unit => unitObj) P (Option (TOp X V)) where
  memInit := fun _ => ()
  locInit := fun _ => none
  invoke := fun _ _ o => some o
  act := fun _ l => match l with
    | some o => .ret (some (trivResp v₀ u o)) none
    | none => .ret none none

variable (v₀ : X → V) (u : V)

omit [DecidableEq P] in
lemma trivTM_act_ne_access (p : P) (l : Option (TOp X V)) (i : Unit) (o : unitObj.Op) k :
    (trivTM (P := P) v₀ u).act p l ≠ .access i o k := by
  cases l <;> simp [trivTM]

lemma trivTM_solo (C : Config (tmSpec X V) (fun _ : Unit => unitObj) P (Option (TOp X V)))
    (p : P) (hp : C.pend p = none) (o : TOp X V) :
    SoloCompletes (trivTM v₀ u) C p o (trivResp v₀ u o) := by
  refine ⟨[], by simp, ?_⟩
  have h1 := Impl.step_inv_eq_some (I := trivTM v₀ u) (o := o) hp trivial
  simp only [List.nil_append, List.cons_append, Impl.runFrom_cons, h1, Option.bind_some]
  rw [Impl.step_ret_eq_some (by simp) (l := none) (by simp [trivTM])]
  simp

/-- The trivial TM satisfies all hypotheses of Theorems 1 and 2. -/
theorem trivTM_hyps :
    WDAP (trivTM (P := P) v₀ u) ∧ ObstructionFreeWrites (trivTM (P := P) v₀ u) ∧
    IsolatedWritesCommit (trivTM (P := P) v₀ u) ∧ WaitFreeReadOnly (trivTM (P := P) v₀ u) ∧
    InvisibleReads (trivTM (P := P) v₀ u) ∧ LegalReads (trivTM (P := P) v₀ u) v₀ := by
  have hof : ObstructionFreeWrites (trivTM (P := P) v₀ u) :=
    fun _ _ C p o _ _ _ hp _ => ⟨_, trivTM_solo v₀ u C p hp o⟩
  refine ⟨?_, hof, hof.isolated, fun _ C p o _ hp _ _ => ⟨_, trivTM_solo v₀ u C p hp o⟩,
    ?_, ?_⟩
  · intro _ C _ a _ _ _ _ i o _ k _ h
    exact absurd h (trivTM_act_ne_access v₀ u _ _ _ _ _)
  · intro _ C p _ _ _ _ i o k h
    exact absurd h (trivTM_act_ne_access v₀ u _ _ _ _ _)
  · intro α C p x v l hα hp hact
    -- the local state of a process is its pending operation
    have inv : ∀ q, C.loc q = C.pend q := by
      refine Impl.invariant_of_run (I := trivTM v₀ u) (Inv := fun C => ∀ q, C.loc q = C.pend q)
        (fun _ => rfl) ?_ hα
      intro C ℓ C' hC hs q
      cases ℓ with
      | inv r o =>
        obtain ⟨-, -, h1, h2, -⟩ := Impl.step_inv hs
        rw [h1, h2]; by_cases hq : q = r
        · subst hq; simp [trivTM]
        · simp [Function.update_of_ne hq, hC q]
      | tau r =>
        obtain ⟨-, -, i, o, k, h, -⟩ := Impl.step_tau hs
        exact absurd h (trivTM_act_ne_access v₀ u _ _ _ _ _)
      | ret r w =>
        obtain ⟨-, h1, -, l, hl, h2⟩ := Impl.step_ret hs
        rw [h1, h2]; by_cases hq : q = r
        · subst hq
          have : l = none := by
            cases hc : C.loc q <;> simp [trivTM, hc] at hl <;> exact hl.2.symm
          simp [this]
        · simp [Function.update_of_ne hq, hC q]
    rw [inv p, hp] at hact
    simp only [trivTM, trivResp, Action.ret.injEq, Option.some.injEq] at hact
    exact Or.inl hact.1.symm

/-- Sanity check: with three processes and two objects, the trivial TM does not ensure RTO
(Theorem 1). -/
example : ¬ EnsuresRTO (trivTM (P := Fin 3) (X := Fin 2) (fun _ => (0 : ℕ)) 0) (fun _ => 0) := by
  obtain ⟨hW, hOF, -, hWF, -, hL⟩ := trivTM_hyps (P := Fin 3) (X := Fin 2) (fun _ => (0 : ℕ)) 0
  exact theorem_1 (a := 0) (b := 1) (c := 2) (x := 0) (y := 1) _ hW hOF hWF hL
    (by decide) (by decide) (by decide) (by decide) ⟨1, by decide, by decide⟩

end Podc.DAPInvisibleReads
