import Papers.PODC2019.AnonymousMutex.Alg2

/-!
# Algorithm 2 is symmetric

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, PODC 2019 (arXiv:1810.03723), Section 5.

Identifier renamings `σ : Equiv.Perm Id` act on local states by renaming the own identifier and
the entries of the view. Algorithm 2 is equivariant under this action (`alg2_symmetric`:
*symmetry with equality*, identifiers are only stored and compared).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} {m : ℕ}

/-- Identifier renamings act on local states (own identifier and view entries). -/
instance : MulAction (Equiv.Perm Id) (St Id m) where
  smul σ s := ⟨σ s.me, s.pc, fun x => (s.view x).map σ⟩
  one_smul s := by
    cases s
    change St.mk _ _ _ = _
    simp
  mul_smul σ τ s := by
    change St.mk _ _ _ = St.mk _ _ _
    congr 1
    funext x
    change _ = Option.map σ (Option.map τ (s.view x))
    cases s.view x <;> rfl

@[simp] lemma smul_me (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).me = σ s.me := rfl
@[simp] lemma smul_pc (σ : Equiv.Perm Id) (s : St Id m) : (σ • s).pc = s.pc := rfl
@[simp] lemma smul_view (σ : Equiv.Perm Id) (s : St Id m) (x : Fin m) :
    (σ • s).view x = (s.view x).map σ := rfl

lemma map_eq_some_smul_iff (σ : Equiv.Perm Id) (v : Option Id) (a : Id) :
    v.map σ = some (σ a) ↔ v = some a := by
  cases v <;> simp

variable [DecidableEq Id]

lemma nextOwn_smul (σ : Equiv.Perm Id) (view : Fin m → Option Id) (me : Id) (i : ℕ) :
    nextOwn (fun x => (view x).map σ) (σ me) i = nextOwn view me i := by
  simp only [nextOwn, map_eq_some_smul_iff]

lemma owned_smul (σ : Equiv.Perm Id) (view : Fin m → Option Id) (me : Id) :
    owned (fun x => (view x).map σ) (σ me) = owned view me := by
  simp only [owned, map_eq_some_smul_iff]

lemma mostPresent_smul (σ : Equiv.Perm Id) (view : Fin m → Option Id) :
    mostPresent (fun x => (view x).map σ) = mostPresent view := by
  simp only [mostPresent, Option.map_eq_none_iff,
    (Option.map_injective σ.injective).eq_iff]

lemma wrFrom_smul (σ : Equiv.Perm Id) (s : St Id m) (i : ℕ) :
    wrFrom (σ • s) i = σ • wrFrom s i := by
  have h : nextOwn (σ • s).view (σ • s).me i = nextOwn s.view s.me i :=
    nextOwn_smul σ s.view s.me i
  unfold wrFrom
  rw [h]
  split_ifs <;> rfl

lemma afterRead_smul (σ : Equiv.Perm Id) (s : St Id m) (w : Fin m → Option Id) :
    afterRead (σ • s) (σ • w) = σ • afterRead s w := by
  have hw : (σ • w) = fun x => (w x).map σ := rfl
  have hown : owned (σ • w) (σ • s).me = owned w s.me := by
    rw [hw, smul_me, owned_smul]
  have hmp : mostPresent (σ • w) = mostPresent w := by rw [hw, mostPresent_smul]
  have hsw : ({ σ • s with view := σ • w } : St Id m) = σ • { s with view := w } := rfl
  unfold afterRead
  rw [hown, hmp]
  split_ifs
  · rw [hsw, wrFrom_smul]
  · rfl
  · rfl

lemma update_smul (σ : Equiv.Perm Id) (s : St Id m) (x : Fin m) (v : Option Id) :
    Function.update (σ • s).view x v = σ • Function.update s.view x (σ⁻¹ • v) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp
  · simp [Function.update_of_ne hy]

/-- Algorithm 2 is symmetric (with equality): initial states, invocations and actions are
equivariant under identifier renamings, and `⊥` is not an identifier. -/
theorem alg2_symmetric : (alg2 Id m).Symmetric where
  bot σ := rfl
  init σ a := rfl
  invoke σ s o := by
    simp only [alg2, smul_pc]
    cases s.pc <;> cases o <;> rfl
  act σ s := by
    simp only [alg2, smul_pc]
    cases hpc : s.pc with
    | cas i =>
      dsimp only
      by_cases hi : i < m
      · rw [dite_eq_left hi, dite_eq_left hi]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and]
        refine ⟨?_, ?_⟩
        · funext v
          cases v <;> simp
        · funext v
          by_cases h : i + 1 < m
          · rw [ite_eq_left h, ite_eq_left h]; rfl
          · rw [ite_eq_right h, ite_eq_right h]; rfl
      · rw [dite_eq_right hi, dite_eq_right hi]; rfl
    | read i =>
      dsimp only
      by_cases hi : i < m
      · rw [dite_eq_left hi, dite_eq_left hi]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and, smul_inv_smul]
        funext v
        rw [update_smul]
        by_cases h : i + 1 < m
        · rw [ite_eq_left h, ite_eq_left h]; rfl
        · rw [ite_eq_right h, ite_eq_right h]; exact afterRead_smul σ s _
      · rw [dite_eq_right hi, dite_eq_right hi]; rfl
    | wr i =>
      dsimp only
      by_cases hi : i < m
      · rw [dite_eq_left hi, dite_eq_left hi]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and]
        refine ⟨rfl, ?_⟩
        funext v
        rw [wrFrom_smul]
      · rw [dite_eq_right hi, dite_eq_right hi]; rfl
    | wait i ab =>
      dsimp only
      by_cases hi : i < m
      · rw [dite_eq_left hi, dite_eq_left hi]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and, smul_inv_smul]
        funext v
        have hv : (σ⁻¹ • v == none) = (v == none) := by cases v <;> rfl
        rw [hv]
        split_ifs <;> rfl
      · rw [dite_eq_right hi, dite_eq_right hi]; rfl
    | un i =>
      dsimp only
      by_cases hi : i < m
      · rw [dite_eq_left hi, dite_eq_left hi]
        simp only [SymAction.smul, SymAction.rmw.injEq, true_and]
        refine ⟨?_, ?_⟩
        · funext v
          have hv : (σ⁻¹ • v = some s.me) ↔ v = some (σ s.me) := by
            rw [inv_smul_eq_iff]; rfl
          by_cases h : v = some (σ s.me)
          · rw [ite_eq_left (by simpa using h), ite_eq_left (hv.mpr h)]; rfl
          · rw [ite_eq_right (by simpa using h), ite_eq_right (fun h' => h (hv.mp h')),
              smul_inv_smul]
        · funext v
          by_cases h : i + 1 < m
          · rw [ite_eq_left h, ite_eq_left h]; rfl
          · rw [ite_eq_right h, ite_eq_right h]; rfl
      · rw [dite_eq_right hi, dite_eq_right hi]; rfl
    | _ => rfl

end AnonymousMutex.Alg2
