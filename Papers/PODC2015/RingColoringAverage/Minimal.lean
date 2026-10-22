import Papers.PODC2015.RingColoringAverage.Model

/-!
# Existence of minimal algorithms

[Feuilloley, *Brief Announcement: Average Complexity for the LOCAL Model*, PODC 2015], §3, says
"without loss of generality we prove the theorem only for minimal algorithms" without further
argument. This file supplies the missing existence argument: every valid algorithm `A` (with a
finite set of colours) has a minimal valid algorithm `B` below it, i.e. `B` uses at most the radius
of `A` at every node of every ring (`Alg.exists_isMinimal_le`).

The proof is by Zorn's lemma on radius functions `IdRing → ℤ → ℕ` (pointwise order). The key step
is that a nonempty chain of radius functions of valid algorithms has a lower bound realised by a
valid algorithm (`exists_valid_le_of_isChain`):

* the new algorithm stops on a view `f` at the least radius at which some algorithm of the chain
  stops on `f` (`MinimalAux.chainAlg`); at ring nodes this is the pointwise infimum of the chain;
* its output at radius `t` is `col (t, f|[-t,t])` for a colour table `col`; a table making the
  colouring proper exists by compactness (Tychonoff on `ℕ × (ℤ → ℕ) → C` with `C` discrete and
  finite): the sets of tables that are proper at all edges where a given member of the chain
  attains the infimum at both endpoints are closed, nonempty (use that member's own outputs) and
  directed, hence have a common point.
-/

namespace Podc.RingColoringAverage

namespace Alg

variable {C : Type*}

/-- The radius function of an algorithm, `(R, v) ↦ A.radAt R v`. -/
noncomputable def radFun (A : Alg C) : IdRing → ℤ → ℕ := fun R v => A.radAt R v

@[simp] theorem radFun_apply (A : Alg C) (R : IdRing) (v : ℤ) : A.radFun R v = A.radAt R v := rfl

end Alg

namespace MinimalAux

/-- The view `f` restricted to the window `[-t, t]` (padded with `0` outside). -/
def trunc (t : ℕ) (f : ℤ → ℕ) : ℤ → ℕ := fun j => if |j| ≤ t then f j else 0

theorem agreeOn_trunc (t : ℕ) (f : ℤ → ℕ) : AgreeOn t (trunc t f) f := fun _ hj => by simp [trunc, hj]

theorem trunc_congr {t : ℕ} {f g : ℤ → ℕ} (h : AgreeOn t f g) : trunc t f = trunc t g := by
  funext j
  unfold trunc
  split_ifs with hj
  · exact h j hj
  · rfl

variable (C : Type*) [Inhabited C] (c : Set (IdRing → ℤ → ℕ))

/-- The radii at which some valid algorithm whose radius function lies in `c` stops on view `f`. -/
def stopSet (f : ℤ → ℕ) : Set ℕ :=
  {t | ∃ B : Alg C, B.Valid ∧ B.radFun ∈ c ∧ (B.out t f).isSome}

/-- The least radius at which some algorithm of the family stops on view `f`. -/
noncomputable def infRad (f : ℤ → ℕ) : ℕ := sInf (stopSet C c f)

theorem stopSet_congr {f g : ℤ → ℕ} {t : ℕ} (h : AgreeOn t f g) {s : ℕ} (hs : s ≤ t) :
    s ∈ stopSet C c f ↔ s ∈ stopSet C c g := by
  simp only [stopSet, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨B, hB, hBc, h'⟩ <;> refine ⟨B, hB, hBc, ?_⟩
  · rwa [← B.out_congr s f g (h.mono hs)]
  · rwa [B.out_congr s f g (h.mono hs)]

open Classical in
/-- The algorithm built from the family `c` and a colour table `col`: it stops on `f` at the
least radius `t` at which some algorithm of the family stops, and outputs `col (t, f|[-t,t])`. -/
noncomputable def chainAlg (col : ℕ × (ℤ → ℕ) → C) : Alg C where
  out t f := if t ∈ stopSet C c f ∧ ∀ s < t, s ∉ stopSet C c f then
    some (col (t, trunc t f)) else none
  out_congr t f g h := by
    have hc : (t ∈ stopSet C c f ∧ ∀ s < t, s ∉ stopSet C c f) ↔
        (t ∈ stopSet C c g ∧ ∀ s < t, s ∉ stopSet C c g) := by
      rw [stopSet_congr C c h le_rfl]
      exact and_congr_right fun _ => forall₂_congr fun s hs =>
        not_congr (stopSet_congr C c h hs.le)
    simp only [hc, trunc_congr h]

variable {C c}

theorem chainAlg_stops_rad {col : ℕ × (ℤ → ℕ) → C} {f : ℤ → ℕ}
    (hne : (stopSet C c f).Nonempty) :
    (chainAlg C c col).Stops f ∧ (chainAlg C c col).rad f = infRad C c f ∧
      (chainAlg C c col).out (infRad C c f) f = some (col (infRad C c f, trunc (infRad C c f) f)) := by
  classical
  have hmem : infRad C c f ∈ stopSet C c f := Nat.sInf_mem hne
  have hlt : ∀ s < infRad C c f, s ∉ stopSet C c f := fun s hs => Nat.notMem_of_lt_sInf hs
  have hout : (chainAlg C c col).out (infRad C c f) f =
      some (col (infRad C c f, trunc (infRad C c f) f)) := by
    simp only [chainAlg]
    simpa [hmem] using hlt
  have hstops : (chainAlg C c col).Stops f := ⟨_, by rw [hout]; rfl⟩
  refine ⟨hstops, le_antisymm (Alg.rad_le (by rw [hout]; rfl)) ?_, hout⟩
  have hs := Alg.rad_spec hstops
  simp only [chainAlg] at hs
  split_ifs at hs with h
  · exact Nat.sInf_le h.1
  · simp at hs

variable (hcs : ∀ ρ ∈ c, ∃ B : Alg C, B.Valid ∧ B.radFun = ρ)
include hcs

theorem stopSet_nonempty (hne : c.Nonempty) (R : IdRing) (v : ℤ) :
    (stopSet C c (R.view v)).Nonempty := by
  obtain ⟨ρ, hρ⟩ := hne
  obtain ⟨B, hB, hBρ⟩ := hcs ρ hρ
  exact ⟨_, B, hB, hBρ ▸ hρ, Alg.rad_spec (hB.stops R v)⟩

theorem infRad_le {ρ} (hρ : ρ ∈ c) (R : IdRing) (v : ℤ) : infRad C c (R.view v) ≤ ρ R v := by
  obtain ⟨B, hB, hBρ⟩ := hcs ρ hρ
  rw [← hBρ]
  exact Nat.sInf_le ⟨B, hB, hBρ ▸ hρ, Alg.rad_spec (hB.stops R v)⟩

theorem exists_attains (hne : c.Nonempty) (R : IdRing) (v : ℤ) :
    ∃ ρ ∈ c, ρ R v = infRad C c (R.view v) := by
  obtain ⟨B, hB, hBc, h⟩ := Nat.sInf_mem (stopSet_nonempty hcs hne R v)
  refine ⟨B.radFun, hBc, le_antisymm (Alg.rad_le h) (infRad_le hcs hBc R v)⟩

theorem attains_of_le {ρ₁ ρ₂ : IdRing → ℤ → ℕ} (h₁ : ρ₁ ∈ c) (hle : ρ₁ ≤ ρ₂) {R : IdRing}
    {v : ℤ} (h₂ : ρ₂ R v = infRad C c (R.view v)) : ρ₁ R v = infRad C c (R.view v) :=
  le_antisymm ((hle R v).trans h₂.le) (infRad_le hcs h₁ R v)

end MinimalAux

open MinimalAux

/-- A nonempty chain of radius functions of valid algorithms (with finitely many colours) has a
lower bound that is the radius function of a valid algorithm. -/
theorem exists_valid_le_of_isChain {C : Type*} [Finite C] [Inhabited C]
    (c : Set (IdRing → ℤ → ℕ)) (hcs : ∀ ρ ∈ c, ∃ B : Alg C, B.Valid ∧ B.radFun = ρ)
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ B : Alg C, B.Valid ∧ ∀ ρ ∈ c, B.radFun ≤ ρ := by
  let _ : TopologicalSpace C := ⊥
  have : DiscreteTopology C := ⟨rfl⟩
  let m : (ℤ → ℕ) → ℕ := infRad C c
  let k : (ℤ → ℕ) → ℕ × (ℤ → ℕ) := fun f => (m f, trunc (m f) f)
  let L : c → Set (ℕ × (ℤ → ℕ) → C) := fun ρ =>
    {col | ∀ (R : IdRing) (v : ℤ), ρ.1 R v = m (R.view v) → ρ.1 R (v + 1) = m (R.view (v + 1)) →
      col (k (R.view v)) ≠ col (k (R.view (v + 1)))}
  have hLclosed : ∀ ρ, IsClosed (L ρ) := by
    intro ρ
    simp only [L, Set.ofPred_forall]
    refine isClosed_iInter fun R => isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => ?_
    have hd : IsClosed {p : C × C | p.1 ≠ p.2} := isClosed_discrete _
    exact hd.preimage (f := fun col : ℕ × (ℤ → ℕ) → C => (col _, col _)) (by fun_prop)
  have hLne : ∀ ρ, (L ρ).Nonempty := by
    rintro ⟨ρ, hρ⟩
    obtain ⟨B, hB, hBρ⟩ := hcs ρ hρ
    refine ⟨fun p => (B.out p.1 p.2).getD default, ?_⟩
    have key : ∀ (R : IdRing) (v : ℤ), ρ R v = m (R.view v) →
        (B.out (k (R.view v)).1 (k (R.view v)).2).getD default = B.outAt R v := by
      intro R v h
      simp only [k]
      rw [B.out_congr _ _ _ (agreeOn_trunc _ _), ← h, ← hBρ]
      rfl
    intro R v h₁ h₂
    simp only
    rw [key R v h₁, key R (v + 1) h₂]
    exact hB.proper R v
  have hLdir : Directed (· ⊇ ·) L := by
    rintro ⟨ρ₁, h₁⟩ ⟨ρ₂, h₂⟩
    have sub : ∀ {σ τ : IdRing → ℤ → ℕ} (hσ : σ ∈ c) (hτ : τ ∈ c), σ ≤ τ →
        L ⟨σ, hσ⟩ ⊆ L ⟨τ, hτ⟩ := by
      intro σ τ hσ hτ hστ col hcol R v e₁ e₂
      exact hcol R v (attains_of_le hcs hσ hστ e₁) (attains_of_le hcs hσ hστ e₂)
    rcases hc.total h₁ h₂ with h | h
    · exact ⟨⟨ρ₁, h₁⟩, le_rfl, sub h₁ h₂ h⟩
    · exact ⟨⟨ρ₂, h₂⟩, sub h₂ h₁ h, le_rfl⟩
  have : Nonempty c := hne.to_subtype
  obtain ⟨col, hcol⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed L hLdir
    hLne (fun ρ => (hLclosed ρ).isCompact) hLclosed
  rw [Set.mem_iInter] at hcol
  have hrad : ∀ (R : IdRing) (v : ℤ), (chainAlg C c col).Stops (R.view v) ∧
      (chainAlg C c col).radAt R v = m (R.view v) ∧
      (chainAlg C c col).outAt R v = col (k (R.view v)) := by
    intro R v
    obtain ⟨hs, hr, ho⟩ := chainAlg_stops_rad (col := col) (stopSet_nonempty hcs hne R v)
    refine ⟨hs, hr, ?_⟩
    simp only [Alg.outAt, Alg.output, hr, ho]
    rfl
  refine ⟨chainAlg C c col, ⟨fun R v => (hrad R v).1, fun R v => ?_⟩, fun ρ hρ R v => ?_⟩
  · rw [(hrad R v).2.2, (hrad R (v + 1)).2.2]
    obtain ⟨ρ₁, h₁, e₁⟩ := exists_attains hcs hne R v
    obtain ⟨ρ₂, h₂, e₂⟩ := exists_attains hcs hne R (v + 1)
    rcases hc.total h₁ h₂ with h | h
    · exact hcol ⟨ρ₁, h₁⟩ R v e₁ (attains_of_le hcs h₁ h e₂)
    · exact hcol ⟨ρ₂, h₂⟩ R v (attains_of_le hcs h₂ h e₁) e₂
  · simp only [Alg.radFun_apply, (hrad R v).2.1]
    exact infRad_le hcs hρ R v

/-- Every valid algorithm `A` (with a finite set of colours) has a minimal valid algorithm `B`
below it: `B` uses at most the radius of `A` at every node of every ring. This justifies the
"without loss of generality, minimal algorithms" step of [Feuilloley, PODC 2015], §3. -/
theorem Alg.exists_isMinimal_le {C : Type*} [Finite C] [Inhabited C] (A : Alg C)
    (hA : A.Valid) :
    ∃ B : Alg C, B.IsMinimal ∧ ∀ (R : IdRing) (v : ℤ), B.radAt R v ≤ A.radAt R v := by
  let s : Set (IdRing → ℤ → ℕ) := {ρ | ∃ B : Alg C, B.Valid ∧ B.radFun = ρ}
  obtain ⟨ρ, hρA, hρmin⟩ := zorn_ge_nonempty₀ s (fun c hcs hc y hy => by
    obtain ⟨B, hB, hBc⟩ := exists_valid_le_of_isChain c hcs hc.symm ⟨y, hy⟩
    exact ⟨B.radFun, ⟨B, hB, rfl⟩, hBc⟩) A.radFun ⟨A, hA, rfl⟩
  obtain ⟨B, hB, rfl⟩ := hρmin.prop
  refine ⟨B, ⟨hB, fun B' hB' hle R v => ?_⟩, fun R v => hρA R v⟩
  have h := hρmin.2 (y := B'.radFun) ⟨B', hB', rfl⟩ (fun R v => hle R v)
  exact le_antisymm (hle R v) (h R v)

end Podc.RingColoringAverage
