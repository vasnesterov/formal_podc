import Papers.PODC2012.TMLiveness.Schedulers

/-!
# On the Liveness of Transactional Memory (PODC 2012): main results

Bushkov, Guerraoui, Kapałka. *On the liveness of transactional memory.* PODC 2012.

* `lemma_1` — Lemma 1: against a TM ensuring strict serializability and a nonblocking TM-liveness
  property in a fault-prone system, the environment can produce an admissible infinite execution
  with at least two correct processes in which at most one process makes progress.
* `theorem_2` — Theorem 2: no TM ensures a strictly serializable safety property together with a
  nonblocking biprogressing TM-liveness property in a fault-prone system.
* `theorem_1` — Theorem 1: no TM ensures both local progress and opacity in a fault-prone system
  (also with strict serializability in place of opacity: `theorem_1_ss`).
* `lemma_1_serializable`, `theorem_2_serializable` — the same with (non-strict) serializability,
  as claimed in the introduction of the PODC version.

Assumptions: finitely many processes, at least two of them (`p₁ ≠ p₂`); at least one t-variable
`x`; infinitely many values (the paper's proof writes `v + 1`). The initial values `init` are
arbitrary.
-/

namespace Podc.TMLiveness

variable {P X V : Type*} [Fintype P] [DecidableEq P] [DecidableEq X] [DecidableEq V] [Infinite V]

/-- The parameters of the environment's strategy. -/
noncomputable def mkSetup (x : X) (p₁ p₂ : P) (hp : p₁ ≠ p₂) : Setup P X V where
  x := x
  p₁ := p₁
  p₂ := p₂
  hp := hp
  bump v := (exists_ne v).choose
  bump_ne v := (exists_ne v).choose_spec
  pick l := (Infinite.exists_notMem_finset l.toFinset).choose
  pick_not_mem l := by simpa using (Infinite.exists_notMem_finset l.toFinset).choose_spec

omit [Fintype P] [DecidableEq P] [DecidableEq X] [DecidableEq V] [Infinite V] in
/-- Local progress is a TM-liveness property. -/
theorem isTMLiveness_localProgress : IsTMLiveness (LocalProgress (P := P) (X := X) (V := V)) :=
  fun _ h => h

omit [Fintype P] [DecidableEq P] [DecidableEq X] [DecidableEq V] [Infinite V] in
/-- Local progress is nonblocking. -/
theorem nonBlocking_localProgress : NonBlocking (LocalProgress (P := P) (X := X) (V := V)) :=
  fun _ hα k hk => hα k hk.1

omit [Fintype P] [DecidableEq P] [DecidableEq X] [DecidableEq V] [Infinite V] in
/-- Local progress is biprogressing. -/
theorem biprogressing_localProgress : Biprogressing (LocalProgress (P := P) (X := X) (V := V)) :=
  fun _ hα ⟨k₁, k₂, hne, h₁, h₂⟩ => ⟨k₁, k₂, hne, hα k₁ h₁, hα k₂ h₂⟩

/-- Lemma 1 holds for (non-strict) serializability as well. -/
theorem lemma_1_serializable (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne) {init : X → V}
    {M : TM P X V} {L : (ℕ → Step P X V) → Prop} (hL : NonBlocking L)
    (hS : EnsuresSafety M (Serializable init)) (hML : EnsuresLiveness M sys L) :
    ∃ α, IsExec M α ∧ sys.Admissible α ∧
      (∃ k₁ k₂, k₁ ≠ k₂ ∧ Correct α k₁ ∧ Correct α k₂) ∧
      ∀ k₁ k₂, Progress α k₁ → Progress α k₂ → k₁ = k₂ := by
  set S : Setup P X V := mkSetup x p₁ p₂ hp
  cases sys with
  | crashOrParasitic =>
    obtain ⟨α, h1, -, h3, h4⟩ :=
      lemma1_parasiticFree S hS (fun α hα _ => hL α (hML α hα trivial))
    exact ⟨α, h1, trivial, h3, h4⟩
  | parasiticFree =>
    exact lemma1_parasiticFree S hS (fun α hα hadm => hL α (hML α hα hadm))
  | crashFree =>
    exact lemma1_crashFree S hS (fun α hα hadm => hL α (hML α hα hadm))

/-- **Lemma 1** (§5.2). For every fault-prone system and every TM implementation that ensures
strict serializability and a nonblocking TM-liveness property in that system, there is an infinite
execution of the implementation, admitted by the system, in which at least two processes are
correct and at most one process makes progress. -/
theorem lemma_1 (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne) {init : X → V}
    {M : TM P X V} {L : (ℕ → Step P X V) → Prop} (hL : NonBlocking L)
    (hS : EnsuresSafety M (StrictlySerializable init)) (hML : EnsuresLiveness M sys L) :
    ∃ α, IsExec M α ∧ sys.Admissible α ∧
      (∃ k₁ k₂, k₁ ≠ k₂ ∧ Correct α k₁ ∧ Correct α k₂) ∧
      ∀ k₁ k₂, Progress α k₁ → Progress α k₂ → k₁ = k₂ := by
  exact lemma_1_serializable x hp sys hL hS.serializable_of_ss hML

/-- **Theorem 2** (§5.2). For every fault-prone system and every TM-liveness property `L` which is
nonblocking and biprogressing, no TM implementation ensures a strictly serializable safety property
`Sf` (one such that every TM ensuring `Sf` ensures strict serializability) and `L` in that
system. -/
theorem theorem_2 (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne) {init : X → V}
    {L : (ℕ → Step P X V) → Prop} (hnb : NonBlocking L) (hbi : Biprogressing L)
    {Sf : List (Ev P X V) → Prop}
    (hSf : ∀ M : TM P X V, EnsuresSafety M Sf → EnsuresSafety M (StrictlySerializable init)) :
    ¬ ∃ M : TM P X V, EnsuresSafety M Sf ∧ EnsuresLiveness M sys L := by
  rintro ⟨M, hS, hML⟩
  obtain ⟨α, hα, hadm, h2, h1⟩ := lemma_1 x hp sys hnb (hSf M hS) hML
  obtain ⟨k₁, k₂, hne, hp₁, hp₂⟩ := hbi α (hML α hα hadm) h2
  exact hne (h1 k₁ k₂ hp₁ hp₂)

/-- **Theorem 2 for serializability** (the claim of the introduction of the PODC version: "any
safety property that is at least as strong as serializability"). -/
theorem theorem_2_serializable (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne)
    {init : X → V} {L : (ℕ → Step P X V) → Prop} (hnb : NonBlocking L) (hbi : Biprogressing L)
    {Sf : List (Ev P X V) → Prop}
    (hSf : ∀ M : TM P X V, EnsuresSafety M Sf → EnsuresSafety M (Serializable init)) :
    ¬ ∃ M : TM P X V, EnsuresSafety M Sf ∧ EnsuresLiveness M sys L := by
  rintro ⟨M, hS, hML⟩
  obtain ⟨α, hα, hadm, h2, h1⟩ := lemma_1_serializable x hp sys hnb (hSf M hS) hML
  obtain ⟨k₁, k₂, hne, hp₁, hp₂⟩ := hbi α (hML α hα hadm) h2
  exact hne (h1 k₁ k₂ hp₁ hp₂)

/-- **Theorem 1**, with strict serializability (as the proof shows). -/
theorem theorem_1_ss (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne) (init : X → V) :
    ¬ ∃ M : TM P X V, EnsuresLiveness M sys LocalProgress ∧
      EnsuresSafety M (StrictlySerializable init) := by
  rintro ⟨M, hL, hS⟩
  exact theorem_2 x hp sys nonBlocking_localProgress biprogressing_localProgress
    (fun _ h => h) ⟨M, hS, hL⟩

/-- **Theorem 1** (§4). For every fault-prone system, there is no TM implementation that ensures
both local progress and opacity in that system. -/
theorem theorem_1 (x : X) {p₁ p₂ : P} (hp : p₁ ≠ p₂) (sys : FaultProne) (init : X → V) :
    ¬ ∃ M : TM P X V, EnsuresLiveness M sys LocalProgress ∧ EnsuresSafety M (Opaque init) := by
  rintro ⟨M, hL, hS⟩
  exact theorem_1_ss x hp sys init ⟨M, hL, hS.ss_of_opaque⟩

end Podc.TMLiveness
