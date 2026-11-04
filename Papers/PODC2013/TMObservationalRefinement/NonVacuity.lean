import Papers.PODC2013.TMObservationalRefinement.Sufficiency

/-!
# Non-vacuity: a minimal language instance

`MinCmd T`: the primitive commands the paper requires (`assume(b)`, `assume(e = n)`, `x := n`,
`g := x`, `x := g`), with Boolean/integer expressions given semantically. This is an instance of
`Lang` (so all hypotheses on the language are satisfiable), and all its commands are deterministic.
We also check that the opacity relation is reflexive, so `theorem_21` applies non-trivially.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act

variable {T : Type}

/-- Boolean expressions over the local variables (`ℕ`-indexed) of a thread. -/
abbrev MinBE := (ℕ → ℤ) → Bool
/-- Integer expressions over the local variables of a thread. -/
abbrev MinIE := (ℕ → ℤ) → ℤ

/-- The minimal set of primitive commands. -/
inductive MinCmd (T : Type) where
  | assume (t : T) (b : MinBE) (p : Bool)
  | assumeEq (t : T) (e : MinIE) (n : ℤ)
  | assign (t : T) (x : ℕ) (n : ℤ)
  | setG (t : T) (g : ℕ) (x : ℕ)
  | getG (t : T) (x : ℕ) (g : ℕ)

namespace MinCmd

def thr : MinCmd T → T
  | assume t .. | assumeEq t .. | assign t .. | setG t .. | getG t .. => t

def glob : MinCmd T → Bool
  | setG .. | getG .. => true
  | _ => false

variable [DecidableEq T]

/-- The semantics. -/
def sem : MinCmd T → State T ℕ ℕ → Set (State T ℕ ℕ)
  | assume t b p, s => {s' | s' = s ∧ b (locals s t) = p}
  | assumeEq t e n, s => {s' | s' = s ∧ e (locals s t) = n}
  | assign t x n, s => {Function.update s (.inr (t, x)) n}
  | setG t g x, s => {Function.update s (.inl g) (s (.inr (t, x)))}
  | getG t x g, s => {Function.update s (.inr (t, x)) (s (.inl g))}

end MinCmd

section lift
variable {LV GV : Type}

lemma liftedFrom_det (A : Var T LV GV → Prop) (g : State T LV GV → State T LV GV)
    (hg1 : ∀ s v, ¬ A v → g s v = s v)
    (hg2 : ∀ s s', (∀ v, A v → s v = s' v) → ∀ v, A v → g s v = g s' v) :
    LiftedFrom A (fun s => {g s}) := by
  refine ⟨fun q => {r | ∃ s, (fun v : Subtype A => s v.1) = q ∧ r = fun v => g s v.1}, ?_⟩
  intro s s'
  simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro rfl; exact ⟨fun v hv => hg1 s v hv, s, rfl, rfl⟩
  · rintro ⟨h1, s₀, hs₀, hr⟩
    funext v
    by_cases hv : A v
    · have e1 := congrFun hr ⟨v, hv⟩
      simp only at e1
      rw [e1]
      exact hg2 s₀ s (fun w hw => congrFun hs₀ ⟨w, hw⟩) v hv
    · rw [h1 v hv, hg1 s v hv]

lemma liftedFrom_filter (A : Var T LV GV → Prop) (P : State T LV GV → Prop)
    (hP : ∀ s s', (∀ v, A v → s v = s' v) → (P s ↔ P s')) :
    LiftedFrom A (fun s => {s' | s' = s ∧ P s}) := by
  refine ⟨fun q => {r | r = q ∧ ∃ s, (fun v : Subtype A => s v.1) = q ∧ P s}, ?_⟩
  intro s s'
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨fun _ _ => by rw [h], by rw [h], s, rfl, hp⟩
  · rintro ⟨h1, h2, s₀, hs₀, hp⟩
    have hs : s' = s := by
      funext v
      by_cases hv : A v
      · exact congrFun h2 ⟨v, hv⟩
      · exact h1 v hv
    exact ⟨hs, (hP s₀ s (fun w hw => congrFun hs₀ ⟨w, hw⟩)).mp hp⟩

end lift

variable [DecidableEq T]

instance instLangMinCmd : Lang T ℕ ℕ MinBE MinIE (MinCmd T) where
  thr := MinCmd.thr
  glob := MinCmd.glob
  sem := MinCmd.sem
  sem_lifted := by
    intro c
    cases c with
    | assume t b p =>
      exact liftedFrom_filter _ _ (fun s s' h => by
        have : locals s t = locals s' t := funext fun x => h (.inr (t, x)) rfl
        simp [this])
    | assumeEq t e n =>
      exact liftedFrom_filter _ _ (fun s s' h => by
        have : locals s t = locals s' t := funext fun x => h (.inr (t, x)) rfl
        simp [this])
    | assign t x n =>
      refine liftedFrom_det _ _ (fun s v hv => ?_) (fun s s' h v hv => ?_)
      · rw [Function.update_of_ne]; rintro rfl; exact hv rfl
      · by_cases e : v = .inr (t, x)
        · subst e; simp
        · simp [Function.update_of_ne e, h v hv]
    | setG t g x =>
      refine liftedFrom_det _ _ (fun s v hv => ?_) (fun s s' h v hv => ?_)
      · rw [Function.update_of_ne]; rintro rfl; exact hv rfl
      · by_cases e : v = .inl g
        · subst e; simp [h (.inr (t, x)) rfl]
        · simp [Function.update_of_ne e, h v hv]
    | getG t x g =>
      refine liftedFrom_det _ _ (fun s v hv => ?_) (fun s s' h v hv => ?_)
      · rw [Function.update_of_ne]; rintro rfl; exact hv rfl
      · by_cases e : v = .inr (t, x)
        · subst e; simp [h (.inl g) rfl]
        · simp [Function.update_of_ne e, h v hv]
  bval b q := b q
  ival e q := e q
  cst n := fun _ => n
  ival_cst _ _ := rfl
  assume := MinCmd.assume
  assumeEq := MinCmd.assumeEq
  assign := MinCmd.assign
  setG := MinCmd.setG
  getG := MinCmd.getG
  thr_assume _ _ _ := rfl
  thr_assumeEq _ _ _ := rfl
  thr_assign _ _ _ := rfl
  thr_setG _ _ _ := rfl
  thr_getG _ _ _ := rfl
  glob_assume _ _ _ := rfl
  glob_assumeEq _ _ _ := rfl
  glob_assign _ _ _ := rfl
  glob_setG _ _ _ := rfl
  glob_getG _ _ _ := rfl
  sem_assume _ _ _ _ := rfl
  sem_assumeEq _ _ _ _ := rfl
  sem_assign _ _ _ _ := by
    simp only [MinCmd.sem]; congr; funext a b; exact Subsingleton.elim _ _
  sem_setG _ _ _ _ := by
    simp only [MinCmd.sem]; congr; funext a b; exact Subsingleton.elim _ _
  sem_getG _ _ _ _ := by
    simp only [MinCmd.sem]; congr; funext a b; exact Subsingleton.elim _ _
  vCom := 1
  vAb := 0
  vCom_ne_vAb := by decide

/-- All commands of the minimal language are deterministic. -/
theorem minCmd_det (c : MinCmd T) (s : State T ℕ ℕ) : (Lang.sem c s).Subsingleton := by
  cases c <;> simp [Lang.sem, MinCmd.sem, Set.Subsingleton] <;> intros <;> simp_all

/-- The opacity relation is reflexive. -/
theorem Opac.refl {O M : Type} (H : List (IAct T O M)) : Opac H H :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ _ h _ => h⟩

/-- Non-vacuity of `theorem_21`: every system is in the opacity relation with itself, hence (if its
histories are well-formed) observationally refines itself. -/
example {O M : Type} [Fintype T] (H : Set (List (IAct T O M))) (hH : ∀ h ∈ H, WellFormed h) :
    TraceRef (LV := ℕ) (GV := ℕ) (C := MinCmd T) (BE := MinBE) (IE := MinIE) O M H H :=
  theorem_21 hH (fun h hh => ⟨h, hh, Opac.refl h⟩)

end Podc.TMObservationalRefinement
