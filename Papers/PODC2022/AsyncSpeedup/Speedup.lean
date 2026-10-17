import Cslib.Computability.Distributed.IteratedModel.Patterns

/-!
# Closure of a task and the asynchronous speedup theorem (Sections 3 and 4)

Fraigniaud, Paz, Rajsbaum. *A Speedup Theorem for Asynchronous Computation with Applications to
Consensus and Approximate Agreement.* PODC 2022 (arXiv:2206.05356v2).

* `localTask T I x τ` — Definition 1 (local task `Π_{τ,σ}` for `σ = (I, x)`).
* `closure M T` — Definition 2 (`CL_M(Π)`), `closureβ M T β` — the closure "with respect to `β`" of
  Section 5.3 (the local task must be solved with box inputs `β`).
* `closure_contains` — Remark after Definition 2 (`Δ(σ) ⊆ Δ'(σ)`).
* `speedup` — Theorem 2 (iterated model augmented with a black box), `speedup_noBox` — Theorem 1.
* `speedup_idOnly` — Claim 5 (box inputs depending only on process id and round).
* `solvable_zero_of_fixedPoint` — Lemma 1.
* `solvable_succ_of_reduction` — the converse direction used for the tightness remark after
  Corollary 3 (only for *uniform* one-round reductions; the converse of the speedup theorem fails
  in general, cf. the conclusion of the paper).
-/

set_option linter.unusedSectionVars false

namespace AsyncSpeedup

open Cslib.Iterated

variable {P X Y Z A B : Type} [DecidableEq P]

/-- `τ ⊆ V(Δ(σ))`: every value of `τ` (on `I`) is the value of the same process in some legal
output for `σ = (I, x)`. -/
def InVertices (T : Task P X Y) (I : Finset P) (x : P → X) (τ : P → Y) : Prop :=
  ∀ i ∈ I, ∃ y ∈ T.Δ I x, y i = τ i

/-- **Definition 1** (local task `Π_{τ,σ}`), for `σ = (I, x)`: inputs are the faces of `τ`; a
participating set `J` with `|J| = 1` must output its input, a larger `J` must output a face of a
legal output for `σ` (`proj_J Δ(σ)`). -/
def localTask (T : Task P X Y) (I : Finset P) (x : P → X) (τ : P → Y) : Task P Y Y where
  Inp := {σ | σ.1.Nonempty ∧ σ.1 ⊆ I ∧ σ.2 = τ}
  Δ J _ := {y | (J.card = 1 → ∀ j ∈ J, y j = τ j) ∧
    (J.card ≠ 1 → ∃ y' ∈ T.Δ I x, ∀ j ∈ J, y j = y' j)}

/-- **Definition 2** (closure `CL_M(Π)`): `τ ∈ Δ'(σ)` iff `τ ⊆ V(Δ(σ))` and the local task
`Π_{τ,σ}` is solvable in one round of `M`. (Solvability in at most one round is the same thing,
see `Solvable.succ`.) -/
def closure (M : Model P A B) (T : Task P X Y) : Task P X Y where
  Inp := T.Inp
  Δ I x := {τ | InVertices T I x τ ∧ Solvable M (localTask T I x τ) 1}

/-- Closure with respect to fixed box inputs `β` (Section 5.3, `CL_M(Π | β)`). -/
def closureβ (M : Model P A B) (T : Task P X Y) (β : P → A) : Task P X Y where
  Inp := T.Inp
  Δ I x := {τ | InVertices T I x τ ∧ ∃ alg : Alg P Y A B Y 1,
    (∀ r i v, alg.inp r i v = β i) ∧ Solves M (localTask T I x τ) alg}

/-- An algorithm whose box inputs depend only on the round and the process id. -/
def IdOnly {t : ℕ} (alg : Alg P X A B Y t) : Prop :=
  ∃ γ : ℕ → P → A, ∀ r i v, alg.inp r i v = γ r i

/-- Solvability by an algorithm whose box inputs depend only on the round and the process id. -/
def SolvableIdOnly (M : Model P A B) (T : Task P X Y) (t : ℕ) : Prop :=
  ∃ alg : Alg P X A B Y t, IdOnly alg ∧ Solves M T alg

/-! ### Remark after Definition 2: `Δ(σ) ⊆ Δ'(σ)` -/

/-- The one-round algorithm of a local task that outputs the (hard-coded) values `y`. -/
def constAlg (a : P → A) (y : P → Y) : Alg P Y A B Y 1 where
  inp _ i _ := a i
  dec i _ := y i

lemma constAlg_solves (M : Model P A B) (T : Task P X Y) {I : Finset P} {x : P → X} {y : P → Y}
    (hy : y ∈ T.Δ I x) (a : P → A) : Solves M (localTask T I x y) (constAlg a y) := by
  intro J τ _ W _
  exact ⟨y, ⟨fun _ _ _ => rfl, fun _ => ⟨y, hy, fun _ _ => rfl⟩⟩, fun _ _ => rfl⟩

/-- **Remark after Definition 2**: `Δ(σ) ⊆ Δ'(σ)`; the closure is not harder than the task. -/
theorem closure_contains [Inhabited A] (M : Model P A B) (T : Task P X Y) {I : Finset P}
    {x : P → X} : T.Δ I x ⊆ (closure M T).Δ I x :=
  fun y hy => ⟨fun _ _ => ⟨y, hy, rfl⟩, constAlg (fun _ => default) y, constAlg_solves M T hy _⟩

lemma closureβ_contains (M : Model P A B) (T : Task P X Y) (β : P → A) {I : Finset P}
    {x : P → X} : T.Δ I x ⊆ (closureβ M T β).Δ I x :=
  fun y hy => ⟨fun _ _ => ⟨y, hy, rfl⟩, constAlg β y, fun _ _ _ => rfl, constAlg_solves M T hy _⟩

/-! ### The speedup construction (proof of Theorems 1 and 2) -/

/-- The view `(b, {(i, v)})` of process `i` after running solo in a round, with box answer `b`. -/
def soloView {r : ℕ} (b : B) (i : P) (v : View P X B r) : View P X B (r + 1) :=
  ((b, fun j => if j = i then some v else none) : B × (P → Option (View P X B r)))

/-- The sped-up algorithm `f'`: run the first `t` rounds, then decide what the `(t+1)`-round
algorithm would decide if the process ran solo in round `t + 1` (box answer `b₀`). -/
def speedAlg (b₀ : P → A → B) {t : ℕ} (alg : Alg P X A B Y (t + 1)) : Alg P X A B Y t where
  inp := alg.inp
  dec i v := alg.dec i (soloView (b₀ i (alg.inp t i v)) i v)

/-- The one-round algorithm `g = f ∘ χ` solving the local task `Π_{τ,σ}` for `τ = f'(ρ)`
(`ρ = V`, hard-coded): a process seeing the processes `J` decides as the `(t+1)`-round algorithm
would after seeing the round-`t` views of `J` in `ρ`; it calls the box as it would in round
`t + 1`. -/
def localAlg {t : ℕ} (alg : Alg P X A B Y (t + 1)) (V : P → View P X B t) : Alg P Y A B Y 1 where
  inp _ i _ := alg.inp t i (V i)
  dec i w :=
    let w' : B × (P → Option Y) := w
    alg.dec i ((w'.1, fun j => (w'.2 j).map fun _ => V j) : B × (P → Option (View P X B t)))

lemma localAlg_dec_step {t : ℕ} (alg : Alg P X A B Y (t + 1)) (V : P → View P X B t)
    (τ : P → Y) (p : Pattern P B) (i : P) :
    (localAlg alg V).dec i (step (X := Y) (r := 0) τ p i) = alg.dec i (step V p i) := by
  simp only [localAlg, step]
  congr 2
  funext j
  split_ifs <;> rfl

lemma step_eq_soloView {r : ℕ} (V : P → View P X B r) (p : Pattern P B) (i : P)
    (hs : p.sees i = {i}) : step V p i = soloView (p.out i) i (V i) := by
  simp only [step, soloView, hs, Finset.mem_singleton]
  congr 1
  funext j
  split_ifs with h
  · subst h; rfl
  · rfl

variable {M : Model P A B}

/-- Core of the proof of Theorems 1/2: for `ρ = V` reachable in `t` rounds from `σ = (I, x)`,
`τ = f'(ρ)` lies in `V(Δ(σ))` and `g = localAlg alg V` solves the local task `Π_{τ,σ}` in one
round. -/
theorem speedup_core (hwf : M.WellFormed) (hsolo : M.AllowsSolo) {b₀ : P → A → B}
    (hdet : M.SoloDet b₀) (hext : M.Extendable) {T : Task P X Y} {t : ℕ}
    {alg : Alg P X A B Y (t + 1)} (h : Solves M T alg) {I : Finset P} {x : P → X}
    (hI : (I, x) ∈ T.Inp) {V : P → View P X B t} (hV : Reach M alg.inp I x t V) :
    InVertices T I x (fun i => (speedAlg b₀ alg).dec i (V i)) ∧
      Solves M (localTask T I x (fun i => (speedAlg b₀ alg).dec i (V i))) (localAlg alg V) := by
  -- the solo decision of `i` in round `t + 1`
  have hsoloDec : ∀ (J : Finset P) (p : Pattern P B), p ∈ M.Pat J (fun i => alg.inp t i (V i)) →
      ∀ i ∈ J, p.sees i = {i} → alg.dec i (step V p i) = (speedAlg b₀ alg).dec i (V i) := by
    intro J p hp i hi hs
    rw [step_eq_soloView V p i hs, hdet J _ p hp i hi hs]
    rfl
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨p, hp, hs⟩ := hsolo I (fun i => alg.inp t i (V i)) i hi
    obtain ⟨y, hy, hdec⟩ := h I x hI _ (Reach.succ p hV hp)
    exact ⟨y, hy, (hdec i hi).symm.trans (hsoloDec I p hp i hi hs)⟩
  · rintro J τ ⟨hJne, hJI, rfl⟩ W hW
    obtain ⟨W₀, p, hW₀, hp, rfl⟩ := reach_succ_iff.1 hW
    rw [reach_zero_iff] at hW₀
    subst hW₀
    refine ⟨fun j => (localAlg alg V).dec j (step (X := Y) (r := 0) (fun i =>
      (speedAlg b₀ alg).dec i (V i)) p j), ⟨fun hcard j hj => ?_, fun hcard => ?_⟩,
      fun _ _ => rfl⟩
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
      rw [Finset.mem_singleton] at hj
      subst hj
      have hwf' := hwf _ _ p hp j (Finset.mem_singleton_self j)
      have hs : p.sees j = {j} :=
        Finset.Subset.antisymm hwf'.2 (Finset.singleton_subset_iff.2 hwf'.1)
      exact (localAlg_dec_step alg V _ p j).trans
        (hsoloDec {j} p hp j (Finset.mem_singleton_self j) hs)
    · obtain ⟨p', hp', hagree⟩ := hext J I hJI _ p hp
      obtain ⟨y', hy', hdec⟩ := h I x hI _ (Reach.succ p' hV hp')
      refine ⟨y', hy', fun j hj => ?_⟩
      refine (localAlg_dec_step alg V _ p j).trans ?_
      rw [← hdec j (hJI hj)]
      simp only [step, (hagree j hj).1, (hagree j hj).2]

/-- **Theorem 2** (asynchronous speedup theorem, iterated models augmented with a black box): in a
well-formed, extendable iterated model allowing solo executions whose box answers to solo callers
are determined, if `Π` is solvable in `t + 1` rounds then `CL_M(Π)` is solvable in `t` rounds. -/
theorem speedup (hwf : M.WellFormed) (hsolo : M.AllowsSolo) {b₀ : P → A → B}
    (hdet : M.SoloDet b₀) (hext : M.Extendable) {T : Task P X Y} {t : ℕ}
    (h : Solvable M T (t + 1)) : Solvable M (closure M T) t := by
  obtain ⟨alg, halg⟩ := h
  refine ⟨speedAlg b₀ alg, fun I x hI V hV => ?_⟩
  have hcore := speedup_core hwf hsolo hdet hext halg hI hV
  exact ⟨_, ⟨hcore.1, localAlg alg V, hcore.2⟩, fun _ _ => rfl⟩

/-- **Theorem 1** (asynchronous speedup theorem): the special case of models without black box. -/
theorem speedup_noBox {M : Model P Unit Unit} (hwf : M.WellFormed) (hsolo : M.AllowsSolo)
    (hext : M.Extendable) {T : Task P X Y} {t : ℕ} (h : Solvable M T (t + 1)) :
    Solvable M (closure M T) t :=
  speedup hwf hsolo (b₀ := fun _ _ => ()) (fun _ _ _ _ _ _ _ => rfl) hext h

/-- **Claim 5**: if the box inputs depend only on the process id and the round, the closure with
respect to `β = α(·, t+1)` is solvable in `t` rounds (by an algorithm of the same kind). -/
theorem speedup_idOnly (hwf : M.WellFormed) (hsolo : M.AllowsSolo) {b₀ : P → A → B}
    (hdet : M.SoloDet b₀) (hext : M.Extendable) {T : Task P X Y} {t : ℕ}
    (h : SolvableIdOnly M T (t + 1)) : ∃ β : P → A, SolvableIdOnly M (closureβ M T β) t := by
  obtain ⟨alg, ⟨γ, hγ⟩, halg⟩ := h
  refine ⟨γ t, speedAlg b₀ alg, ⟨γ, hγ⟩, fun I x hI V hV => ?_⟩
  have hcore := speedup_core hwf hsolo hdet hext halg hI hV
  exact ⟨_, ⟨hcore.1, localAlg alg V, fun _ i _ => hγ t i _, hcore.2⟩, fun _ _ => rfl⟩

/-- Solvable in `t` rounds ⇒ solvable in `t + 1` rounds (a process recovers its previous view from
its own entry). In particular "solvable in at most one round" (Definition 2) is the same as
"solvable in one round". -/
theorem Solvable.succ [Nonempty Y] (hwf : M.WellFormed) {T : Task P X Y} {t : ℕ}
    (h : Solvable M T t) : Solvable M T (t + 1) := by
  classical
  obtain ⟨alg, halg⟩ := h
  let alg' : Alg P X A B Y (t + 1) :=
    { inp := alg.inp
      dec := fun i W =>
        let W' : B × (P → Option (View P X B t)) := W
        match W'.2 i with
        | some v => alg.dec i v
        | none => Classical.arbitrary Y }
  refine ⟨alg', fun I x hI W hW => ?_⟩
  obtain ⟨V, p, hV, hp, rfl⟩ := reach_succ_iff.1 hW
  obtain ⟨y, hy, hdec⟩ := halg I x hI V hV
  refine ⟨y, hy, fun i hi => ?_⟩
  have hii : i ∈ p.sees i := (hwf I _ p hp i hi).1
  rw [← hdec i hi]
  simp [alg', step, hii]

/-- **Lemma 1**: a task that is a fixed point of the closure (it suffices that `CL_M(Π)` is not
easier than `Π`) is solvable in some number of rounds only if it is solvable in zero rounds. -/
theorem solvable_zero_of_fixedPoint (hwf : M.WellFormed) (hsolo : M.AllowsSolo)
    {b₀ : P → A → B} (hdet : M.SoloDet b₀) (hext : M.Extendable) {T : Task P X Y}
    (hfix : ∀ I x, (I, x) ∈ T.Inp → (closure M T).Δ I x ⊆ T.Δ I x) {t : ℕ}
    (h : Solvable M T t) : Solvable M T 0 := by
  induction t with
  | zero => exact h
  | succ t ih =>
    exact ih ((speedup hwf hsolo hdet hext h).mono (Task.Easier.of_subset le_rfl hfix))

/-! ### A converse for uniform one-round reductions (used for tightness) -/

/-- Composition: if `T₂` is solvable in `t` rounds, and a fixed one-round algorithm (`a₀`, `h`)
turns any legal output of `T₂` into a legal output of `T₁`, then `T₁` is solvable in `t + 1`
rounds. Unlike the local task of Definition 1, the one-round algorithm may not depend on `σ`. -/
theorem solvable_succ_of_reduction {T₁ : Task P X Z} {T₂ : Task P X Y} {t : ℕ}
    (hInp : T₁.Inp ⊆ T₂.Inp) (h₂ : Solvable M T₂ t) (a₀ : P → Y → A)
    (h : P → B × (P → Option Y) → Z)
    (hred : ∀ I x, (I, x) ∈ T₁.Inp → ∀ d : P → Y, (∃ y ∈ T₂.Δ I x, ∀ i ∈ I, d i = y i) →
      ∀ p ∈ M.Pat I (fun i => a₀ i (d i)), ∃ z ∈ T₁.Δ I x, ∀ i ∈ I,
        h i (p.out i, fun j => if j ∈ p.sees i then some (d j) else none) = z i) :
    Solvable M T₁ (t + 1) := by
  classical
  obtain ⟨alg, halg⟩ := h₂
  let alg' : Alg P X A B Z (t + 1) :=
    { inp := fun r i v => if hr : r = t then a₀ i (alg.dec i (hr ▸ v)) else alg.inp r i v
      dec := fun i W =>
        let W' : B × (P → Option (View P X B t)) := W
        h i (W'.1, fun j => (W'.2 j).map (alg.dec j)) }
  refine ⟨alg', fun I x hI W hW => ?_⟩
  obtain ⟨V, p, hV, hp, rfl⟩ := reach_succ_iff.1 hW
  have hV' : Reach M alg.inp I x t V :=
    hV.congr_inp fun s hs => by
      funext i v; simp [alg', Nat.ne_of_lt hs]
  obtain ⟨y, hy, hdec⟩ := halg I x (hInp hI) V hV'
  have hp' : p ∈ M.Pat I (fun i => a₀ i (alg.dec i (V i))) := by simpa [alg'] using hp
  obtain ⟨z, hz, hhz⟩ := hred I x hI (fun j => alg.dec j (V j)) ⟨y, hy, hdec⟩ p hp'
  refine ⟨z, hz, fun i hi => ?_⟩
  rw [← hhz i hi]
  simp only [alg', step]
  congr 2
  funext j
  split_ifs <;> rfl

end AsyncSpeedup
