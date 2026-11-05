import Papers.PODC2012.LimitedUseSnapshots.SnapshotWm

/-!
# Algorithm 3 is linearizable (Theorem 4.2 of Aspnes–Attiya–Censor-Hillel–Ellen)

The base objects (`MaxArray`s, the root `MaxReg`, the `view` registers) are atomic, the tree is
any binary tree whose leaves are exactly the processes (`BTree.WF`).
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-- One step preserves the invariant (with a larger ghost `R`). -/
theorem inv_step (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀}
    {R : List Bool → Set (ℕ × ℕ)} {L : Lin v₀} {s₀ : P → ℕ} (hα : (alg3 T v₀).run α = some C)
    (hI : Inv T α C R L s₀) {ℓ : Label P (swSnap P V v₀)}
    (h : (alg3 T v₀).step C ℓ = some C') :
    ∃ R' L' s₀', Inv T (α ++ [ℓ]) C' R' L' s₀' ∧ ∀ a, R a ⊆ R' a := by
  cases ℓ with
  | inv p o => exact ⟨R, L, s₀, inv_step_inv hα hI h, fun _ => subset_rfl⟩
  | ret p r => exact ⟨R, L, s₀, inv_step_ret hα hI h, fun _ => subset_rfl⟩
  | tau p =>
    have hP := hI.proc p
    have hstep := Impl.step_tau h
    cases hpc : (C.loc p).pc with
    | idle => simp only [PInv, hpc] at hP; exact absurd hP.1 hstep.1
    | lw v => exact ⟨R, L, s₀, inv_step_lw hT hI hpc h, fun _ => subset_rfl⟩
    | up a ptr =>
      obtain ⟨R', h1, h2⟩ := inv_step_up hT hI hpc h
      exact ⟨R', L, s₀, h1, h2⟩
    | sc q => exact ⟨R, L, s₀, inv_step_sc hT hI hpc h, fun _ => subset_rfl⟩
    | rl q x y => exact ⟨R, L, s₀, inv_step_rl hI hpc h, fun _ => subset_rfl⟩
    | rr q x y lv => exact ⟨R, L, s₀, inv_step_rr hT hI hpc h, fun _ => subset_rfl⟩
    | wv q k val => exact ⟨R, L, s₀, inv_step_wv hT hI hpc h, fun _ => subset_rfl⟩
    | wm d =>
      obtain ⟨L', s₀', h1⟩ := inv_step_wm hT hα hI hpc h
      exact ⟨R, L', s₀', h1, fun _ => subset_rfl⟩
    | s0 => exact ⟨R, _, s₀, inv_step_s0 hT hα hI hpc h, fun _ => subset_rfl⟩
    | s1 d => exact ⟨R, L, s₀, inv_step_s1 hT hI hpc h, fun _ => subset_rfl⟩
    | ackU =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := hstep
      simp [act, hpc] at hact
    | retS val =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := hstep
      simp [act, hpc] at hact

/-- The invariant holds in every reachable configuration. -/
theorem exists_inv (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) : ∃ R L s₀, Inv T α C R L s₀ :=
  Impl.run_induction (Q := fun α C => ∃ R L s₀, Inv T α C R L s₀) ⟨R₀, [], 0, inv_init⟩
    (fun _ _ _ _ hα ⟨_, _, _, hI⟩ hs =>
      let ⟨R', L', s₀', hI', _⟩ := inv_step hT hα hI hs; ⟨R', L', s₀', hI'⟩) h

/-- The invariant along an extension of an execution, with a growing ghost `R`. -/
theorem inv_runFrom (hT : T.WF) :
    ∀ (γ : List (Label P (swSnap P V v₀))) {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀}
      {R : List Bool → Set (ℕ × ℕ)} {L : Lin v₀} {s₀ : P → ℕ},
      (alg3 T v₀).run α = some C → Inv T α C R L s₀ → (alg3 T v₀).runFrom C γ = some C' →
      ∃ R' L' s₀', Inv T (α ++ γ) C' R' L' s₀' ∧ ∀ a, R a ⊆ R' a
  | [], _, _, _, R, L, s₀, _, hI, h => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h
    exact ⟨R, L, s₀, by simpa using hI, fun _ => subset_rfl⟩
  | ℓ :: γ, α, C, C', R, L, s₀, hα, hI, h => by
    simp only [Impl.runFrom_cons] at h
    cases hs : (alg3 T v₀).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨R₁, L₁, s₁, hI₁, hR₁⟩ := inv_step hT hα hI hs
      have hα₁ : (alg3 T v₀).run (α ++ [ℓ]) = some C₁ := by
        rw [Impl.run_concat, hα, Option.bind_some, hs]
      obtain ⟨R', L', s', hI', hR'⟩ := inv_runFrom hT γ hα₁ hI₁ h
      exact ⟨R', L', s', by simpa using hI', fun a => (hR₁ a).trans (hR' a)⟩

/-- **Theorem 4.2** of [Aspnes–Attiya–Censor-Hillel–Ellen]: Algorithm 3 (with atomic max arrays,
max register and registers) is a linearizable implementation of a single-writer snapshot, for
every binary tree whose leaves are exactly the processes. Every finite execution has a
linearization. -/
theorem theorem_4_2_exists (hT : T.WF) (α : List (Label P (swSnap P V v₀))) (C : Cfg v₀)
    (h : (alg3 T v₀).run α = some C) : ∃ L, IsLinearization α L :=
  let ⟨_, L, _, hI⟩ := exists_inv hT h; ⟨L, hI.lin⟩

/-- **Theorem 4.2** of [Aspnes–Attiya–Censor-Hillel–Ellen]: Algorithm 3 is linearizable. -/
theorem theorem_4_2 (hT : T.WF) : (alg3 T v₀).Linearizable :=
  Impl.linearizable_of_run (theorem_4_2_exists hT)

end Podc.LimitedUseSnapshots.Snapshot
