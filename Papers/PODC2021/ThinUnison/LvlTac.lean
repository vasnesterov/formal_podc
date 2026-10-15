import Papers.PODC2021.ThinUnison.Step

/-!
# A decision tactic for level arithmetic

`lvl_omega` unfolds the level predicates (`IsLevel`, `LAdj`, `Outward`, `FarOut`, `OutEq`),
adds the defining case split of every occurrence of `fwd k ℓ`, `inw ℓ`, `outw ℓ` (treated as atoms)
and calls `omega`.
-/

namespace ThinUnison

theorem fwd_spec (k : ℕ) (ℓ : ℤ) : (ℓ = -1 ∧ fwd k ℓ = 1) ∨ (ℓ ≠ -1 ∧ ℓ = k ∧ fwd k ℓ = -k) ∨
    (ℓ ≠ -1 ∧ ℓ ≠ k ∧ fwd k ℓ = ℓ + 1) := by
  unfold fwd; split_ifs <;> omega

theorem inw_spec (ℓ : ℤ) : (0 < ℓ ∧ inw ℓ = ℓ - 1) ∨ (ℓ ≤ 0 ∧ inw ℓ = ℓ + 1) := by
  unfold inw; split_ifs <;> omega

theorem outw_spec (ℓ : ℤ) : (0 < ℓ ∧ outw ℓ = ℓ + 1) ∨ (ℓ ≤ 0 ∧ outw ℓ = ℓ - 1) := by
  unfold outw; split_ifs <;> omega

open Lean Meta Elab Tactic

/-- Collect the subterms `fwd k ℓ`, `inw ℓ`, `outw ℓ` (without loose bound variables). -/
partial def collectLvlAtoms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    if e.hasLooseBVars then acc else
    match e.getAppFnArgs with
    | (``ThinUnison.fwd, #[_, _]) => if acc.contains e then acc else acc.push e
    | (``ThinUnison.inw, #[_]) => if acc.contains e then acc else acc.push e
    | (``ThinUnison.outw, #[_]) => if acc.contains e then acc else acc.push e
    | _ => acc
  match e with
  | .app f a => collectLvlAtoms a (collectLvlAtoms f acc)
  | .lam _ t b _ => collectLvlAtoms b (collectLvlAtoms t acc)
  | .forallE _ t b _ => collectLvlAtoms b (collectLvlAtoms t acc)
  | .letE _ t v b _ => collectLvlAtoms b (collectLvlAtoms v (collectLvlAtoms t acc))
  | .mdata _ b => collectLvlAtoms b acc
  | .proj _ _ b => collectLvlAtoms b acc
  | _ => acc

/-- Add the case-split specification of every `fwd`/`inw`/`outw` atom to the context. -/
elab "add_lvl_specs" : tactic => withMainContext do
  let mut atoms : Array Expr := #[]
  atoms := collectLvlAtoms (← instantiateMVars (← getMainTarget)) atoms
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      atoms := collectLvlAtoms (← instantiateMVars d.type) atoms
  for a in atoms do
    let pf ← match a.getAppFnArgs with
      | (``ThinUnison.fwd, #[k, l]) => mkAppM ``fwd_spec #[k, l]
      | (``ThinUnison.inw, #[l]) => mkAppM ``inw_spec #[l]
      | (``ThinUnison.outw, #[l]) => mkAppM ``outw_spec #[l]
      | _ => throwError "unexpected atom"
    let ty ← inferType pf
    liftMetaTactic fun g => do
      let g ← g.assert `hspec ty pf
      let (_, g) ← g.intro1P
      return [g]

/-- Decide level arithmetic: unfold, add atom specifications, `omega`. -/
macro "lvl_omega" : tactic => `(tactic|
  ((try simp only [IsLevel, LAdj, Outward, FarOut, OutEq, MoveRel, true_or, or_true, true_and,
      and_true, false_or, or_false, false_and, and_false, not_true_eq_false, not_false_eq_true,
      Bool.false_eq_true, Bool.true_eq_false, true_implies, false_implies,
      IsEmpty.forall_iff] at *) <;>
   (add_lvl_specs; omega)))

end ThinUnison
