import Papers.PODC2010.AsymmetricProgress.Critical

/-!
# `(n, X)`-live consensus objects as base objects

* `ConsObj n` — a consensus object as seen by its users (operation `propose v`, response the
  decided value, possibly withheld), `ConsObj.toBObj`;
* `useOnce B` — the algorithm "propose your input to `B` and decide the response"; a consensus
  object `B` is a legal `(n, X)`-live consensus object (`ConsObj.IsLive B X`) iff `useOnce B`
  satisfies validity, agreement, wait-free termination for `X` and obstruction-free termination
  for everybody — the definition of Section 2 of the paper;
* `advCons X` — a concrete, adversarial `(n, X)`-live consensus object: processes in `X` get an
  answer at once; any other process gets an answer only at a step that directly follows its own
  previous step on the object (so a process running alone gets an answer after two steps, but two
  processes outside `X` that alternate never do). `advCons_isLive`: it is a legal
  `(n, X)`-live consensus object. It is used in Theorem 2 as the behaviour of the base objects
  chosen by the adversary.
-/

namespace Podc.AsymmetricProgress

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- A (binary) consensus object of an `n`-process system: `propose v` by process `p` in state `s`
gives a new state and possibly (`some d`) the decided value. -/
structure ConsObj (n : ℕ) where
  /-- States. -/
  State : Type
  /-- Initial state. -/
  init : State
  /-- `propose v` by `p`. -/
  δ : State → Fin n → Bool → State × Option Bool

/-- The base object of a consensus object. -/
abbrev ConsObj.toBObj (B : ConsObj n) : BObj n := ⟨B.State, Bool, Bool, B.δ⟩

/-- Local states of `useOnce`: `inl v` — about to propose `v`; `inr w` — decided `w`. -/
abbrev UOState := Bool ⊕ Bool

/-- The algorithm that proposes the input to the consensus object `B` and decides the answer. -/
abbrev useOnce (B : ConsObj n) : Alg n (fun _ : Unit => B.toBObj) where
  L := UOState
  init _ v := .inl v
  act
    | .inl v => .access () v .inr
    | .inr w => .out w
  mem₀ _ := B.init

/-- `B` is a legal `(n, X)`-live consensus object: validity, agreement, wait-free termination for
the processes of `X`, obstruction-free termination for all processes. -/
def ConsObj.IsLive (B : ConsObj n) (X : Set (Fin n)) : Prop := Live (useOnce B) X

/-! ## The adversarial `(n, X)`-live consensus object -/

/-- State of `advCons`: the decided value (if any) and the last process that took a step. -/
@[ext]
structure LCState (n : ℕ) where
  /-- The decided value. -/
  dec : Option Bool
  /-- The process that took the last step on the object. -/
  last : Option (Fin n)

/-- The adversarial `(n, X)`-live consensus object: processes of `X` are answered at once; any
other process `p` is answered only if the previous step on the object was its own. -/
abbrev advCons (X : Finset (Fin n)) : ConsObj n where
  State := LCState n
  init := ⟨none, none⟩
  δ s p v :=
    if p ∈ X ∨ s.last = some p then (⟨some (s.dec.getD v), some p⟩, some (s.dec.getD v))
    else (⟨s.dec, some p⟩, none)

/-- The base object of `advCons X`. -/
abbrev liveCons (X : Finset (Fin n)) : BObj n := (advCons X).toBObj

section AdvCons

variable (X : Finset (Fin n))

/-- The invariant of `useOnce (advCons X)` from inputs `x`. -/
def AdvInv (x : Fin n → Bool) (C : Cfg (useOnce (advCons X))) : Prop :=
  (∀ p, C.loc p = .inl (x p) ∨ ∃ w, C.loc p = .inr w ∧ (C.mem ()).dec = some w) ∧
    ∀ d, (C.mem ()).dec = some d → ∃ q, x q = d

lemma advInv_init (x : Fin n → Bool) : AdvInv X x (initCfg _ x) :=
  ⟨fun p => Or.inl rfl, fun d h => by simp [initCfg, useOnce, advCons] at h⟩

lemma uo_out_iff {C : Cfg (useOnce (advCons X))} {p : Fin n} {v : Bool} :
    C.Out p v ↔ C.loc p = .inr v := by
  unfold Cfg.Out
  rcases h : C.loc p with u | u <;> simp [useOnce]

lemma uo_step_inl {C : Cfg (useOnce (advCons X))} {p : Fin n} {v : Bool}
    (h : C.loc p = .inl v) :
    C.step p =
      if p ∈ X ∨ (C.mem ()).last = some p then
        { loc := Function.update C.loc p (.inr ((C.mem ()).dec.getD v))
          mem := fun _ => ⟨some ((C.mem ()).dec.getD v), some p⟩ }
      else { loc := C.loc, mem := fun _ => ⟨(C.mem ()).dec, some p⟩ } := by
  have ha : (useOnce (advCons X)).act (C.loc p) = .access () v .inr := by rw [h]
  rw [step_of_access ha]
  split_ifs with hc
  · simp only [ConsObj.toBObj, advCons, hc, ↓reduceIte, Option.elim]
    congr 1
  · simp only [ConsObj.toBObj, advCons, hc, ↓reduceIte, Option.elim]
    congr 1

lemma advInv_step {x : Fin n → Bool} {C : Cfg (useOnce (advCons X))} (h : AdvInv X x C)
    (p : Fin n) : AdvInv X x (C.step p) := by
  obtain ⟨h1, h2⟩ := h
  rcases h1 p with hp | ⟨w, hp, hw⟩
  · rw [uo_step_inl X hp]
    split_ifs with hc
    · refine ⟨fun q => ?_, fun d hd => ?_⟩
      · by_cases hq : q = p
        · subst hq; right; simp
        · rcases h1 q with hq' | ⟨w, hq', hw⟩
          · left; simp [Function.update_of_ne hq, hq']
          · right; refine ⟨w, by simp [Function.update_of_ne hq, hq'], ?_⟩
            simp [hw]
      · simp only [Option.some.injEq] at hd
        subst hd
        rcases hdec : (C.mem ()).dec with _ | d
        · exact ⟨p, by simp⟩
        · simpa using h2 d hdec
    · exact ⟨h1, h2⟩
  · have : C.step p = C := step_of_out ((uo_out_iff X).2 hp)
    rw [this]; exact ⟨h1, h2⟩

lemma advInv_run {x : Fin n → Bool} {C : Cfg (useOnce (advCons X))} (h : AdvInv X x C)
    (σ : List (Fin n)) : AdvInv X x (run C σ) := by
  induction σ generalizing C with
  | nil => exact h
  | cons p σ ih => exact ih (advInv_step X h p)

lemma uo_inl_of_not_out {C : Cfg (useOnce (advCons X))} {p : Fin n}
    (h : ∀ v, ¬ C.Out p v) : ∃ v, C.loc p = .inl v := by
  rcases hc : C.loc p with v | v
  · exact ⟨v, rfl⟩
  · exact absurd ((uo_out_iff X).2 hc) (h v)

/-- A process of `X` is answered at its first step. -/
lemma advCons_out_step_mem {C : Cfg (useOnce (advCons X))} {p : Fin n} (hp : p ∈ X) :
    ∃ v, (C.step p).Out p v := by
  by_cases ho : ∃ v, C.Out p v
  · obtain ⟨v, hv⟩ := ho; exact ⟨v, hv.step p⟩
  · push Not at ho
    obtain ⟨v, hv⟩ := uo_inl_of_not_out X ho
    rw [uo_step_inl X hv, ite_eq_left (Or.inl hp)]
    exact ⟨_, (uo_out_iff X).2 (Function.update_self _ _ _)⟩

/-- Any process running alone is answered within two steps. -/
lemma advCons_out_two (C : Cfg (useOnce (advCons X))) (p : Fin n) :
    ∃ v, (run C [p, p]).Out p v := by
  by_cases ho : ∃ v, C.Out p v
  · obtain ⟨v, hv⟩ := ho; exact ⟨v, hv.run _⟩
  · push Not at ho
    obtain ⟨v, hv⟩ := uo_inl_of_not_out X ho
    simp only [run_cons, run_nil]
    rw [uo_step_inl X hv]
    split_ifs with hc
    · exact ⟨_, ((uo_out_iff X).2 (Function.update_self _ _ _)).step p⟩
    · rw [uo_step_inl X (C := { loc := C.loc, mem := fun _ => ⟨(C.mem ()).dec, some p⟩ }) hv,
        ite_eq_left (Or.inr rfl)]
      exact ⟨_, (uo_out_iff X).2 (Function.update_self _ _ _)⟩

/-- `advCons X` is a legal `(n, X)`-live consensus object. -/
theorem advCons_isLive : (advCons X).IsLive (X : Set (Fin n)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x σ p q v w hv hw
    obtain ⟨h1, -⟩ := advInv_run X (advInv_init X x) σ
    rw [uo_out_iff] at hv hw
    rcases h1 p with hp | ⟨u, hp, hu⟩
    · rw [hp] at hv; cases hv
    rcases h1 q with hq | ⟨u', hq, hu'⟩
    · rw [hq] at hw; cases hw
    rw [hp] at hv; rw [hq] at hw
    cases hv; cases hw
    rw [hu] at hu'; cases hu'; rfl
  · intro x σ p v hv
    obtain ⟨h1, h2⟩ := advInv_run X (advInv_init X x) σ
    rw [uo_out_iff] at hv
    rcases h1 p with hp | ⟨u, hp, hu⟩
    · rw [hp] at hv; cases hv
    rw [hp] at hv; cases hv
    exact h2 _ hu
  · intro p C _
    obtain ⟨v, hv⟩ := advCons_out_two X C p
    exact ⟨2, v, hv⟩
  · intro p hp x e he
    obtain ⟨t, -, ht⟩ := he 0
    obtain ⟨v, hv⟩ := advCons_out_step_mem X (C := run (initCfg _ x) (pre e t)) (Finset.mem_coe.1 hp)
    refine ⟨t + 1, v, ?_⟩
    rw [pre_succ, run_concat, ht]
    exact hv

end AdvCons

end Podc.AsymmetricProgress
