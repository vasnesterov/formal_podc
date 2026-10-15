import Papers.PODC2019.AnonymousMutex.Alg1

/-!
# Algorithm 1 is symmetric and uses only reads, writes and snapshots

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, PODC 2019 (arXiv:1810.03723), Section 3.

Identifier renamings `σ : Equiv.Perm Id` act on local states by renaming the own identifier and
the entries of the last snapshot. Algorithm 1 is equivariant under this action
(`alg1_symmetric`: *symmetry with equality*, identifiers are only stored and compared), and every
read-modify-write it performs is a plain read or a plain write (`alg1_readWrite`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg1

variable {Id : Type} {m : ℕ}

/-- Identifier renamings act on local states (own identifier and snapshot entries). -/
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

lemma smul_with_pc (σ : Equiv.Perm Id) (s : St Id m) (pc : PC m) :
    ({ σ • s with pc := pc } : St Id m) = σ • { s with pc := pc } := rfl

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

lemma cnt_smul (σ : Equiv.Perm Id) (view : Fin m → Option Id) :
    cnt (fun x => (view x).map σ) = cnt view := by
  unfold cnt
  have : (Finset.univ.image fun x => (view x).map σ) =
      (Finset.univ.image view).image (Option.map σ) := by
    rw [Finset.image_image]; rfl
  rw [this, Finset.card_image_of_injective _ (Option.map_injective σ.injective)]

lemma firstBot_smul (σ : Equiv.Perm Id) (view : Fin m → Option Id) :
    firstBot (fun x => (view x).map σ) = firstBot view := by
  simp only [firstBot, Option.map_eq_none_iff]

lemma shrinkFrom_smul (σ : Equiv.Perm Id) (s : St Id m) (i : ℕ) (unl : Bool) :
    shrinkFrom (σ • s) i unl = σ • shrinkFrom s i unl := by
  have h : nextOwn (σ • s).view (σ • s).me i = nextOwn s.view s.me i :=
    nextOwn_smul σ s.view s.me i
  unfold shrinkFrom
  rw [h]
  split_ifs <;> rfl

lemma afterSnap_smul (σ : Equiv.Perm Id) (s : St Id m) (w : Fin m → Option Id) :
    afterSnap (σ • s) (σ • w) = σ • afterSnap s w := by
  have hw : (σ • w) = fun x => (w x).map σ := rfl
  have hown : owned (σ • w) (σ • s).me = owned w s.me := by
    rw [hw, smul_me, owned_smul]
  have hcnt : cnt (σ • w) = cnt w := by rw [hw, cnt_smul]
  have hfb : firstBot (σ • w) = firstBot w := by rw [hw, firstBot_smul]
  have hall : (∀ x, (σ • w) x = none) ↔ ∀ x, w x = none := by
    simp
  have hsw : ({ σ • s with view := σ • w } : St Id m) = σ • { s with view := w } := rfl
  unfold afterSnap
  rw [hown, hcnt, hfb]
  simp only [hall]
  generalize firstBot w = fb
  by_cases h1 : 0 < owned w s.me ∨ ∀ x, w x = none
  · rw [ite_eq_left h1, ite_eq_left h1]
    cases fb with
    | some x => rfl
    | none =>
      simp only
      by_cases h2 : owned w s.me = m
      · rw [ite_eq_left h2, ite_eq_left h2]; rfl
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : owned w s.me * cnt w < m
        · rw [ite_eq_left h3, ite_eq_left h3, hsw, shrinkFrom_smul]
        · rw [ite_eq_right h3, ite_eq_right h3]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]; rfl

/-- Algorithm 1 is symmetric (with equality): initial states, invocations and actions are
equivariant under identifier renamings, and `⊥` is not an identifier. -/
theorem alg1_symmetric : (alg1 Id m).Symmetric where
  bot σ := rfl
  init σ a := rfl
  invoke σ s o := by
    simp only [alg1, smul_pc]
    cases s.pc <;> cases o <;> first | rfl | exact shrinkFrom_smul σ s 0 true
  act σ s := by
    simp only [alg1, smul_pc]
    cases hpc : s.pc with
    | snap =>
      simp only [SymAction.smul, SymAction.snap.injEq]
      funext w
      rw [← afterSnap_smul, smul_inv_smul]
    | write x =>
      simp only [SymAction.smul]
      rfl
    | shRead i unl =>
      dsimp only
      split_ifs with hi
      · simp only [SymAction.smul, smul_inv_smul, SymAction.rmw.injEq, true_and]
        funext v
        have hv : (σ⁻¹ • v = some s.me) ↔ v = some (σ s.me) := by
          rw [inv_smul_eq_iff]; rfl
        by_cases h : v = some (σ s.me)
        · rw [ite_eq_left (by simpa using h), ite_eq_left (hv.mpr h)]; rfl
        · rw [ite_eq_right (by simpa using h), ite_eq_right (fun h' => h (hv.mp h')), shrinkFrom_smul]
      · rfl
    | shWrite i unl =>
      dsimp only
      split_ifs with hi
      · simp only [SymAction.smul, SymAction.rmw.injEq, true_and]
        refine ⟨rfl, ?_⟩
        funext v
        rw [shrinkFrom_smul]
      · rfl
    | _ => rfl

/-- Algorithm 1 only uses atomic reads, writes and snapshots. -/
theorem alg1_readWrite : (alg1 Id m).ReadWrite := by
  intro s x f k h
  simp only [alg1] at h
  cases hpc : s.pc with
  | write y =>
    rw [hpc] at h
    simp only [SymAction.rmw.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inr ⟨_, _, fun _ => rfl, fun _ => rfl⟩
  | shRead i unl =>
    rw [hpc] at h
    dsimp only at h
    split_ifs at h with hi
    simp only [SymAction.rmw.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inl fun _ => rfl
  | shWrite i unl =>
    rw [hpc] at h
    dsimp only at h
    split_ifs at h with hi
    simp only [SymAction.rmw.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inr ⟨_, _, fun _ => rfl, fun _ => rfl⟩
  | _ => rw [hpc] at h; simp at h

end AnonymousMutex.Alg1
