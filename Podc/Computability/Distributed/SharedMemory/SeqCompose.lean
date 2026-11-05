import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Computability.Distributed.SharedMemory.Potential

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/SeqCompose.lean

/-!
# Sequential composition of one-shot task implementations

Given an implementation `X` of a one-shot task with inputs `In` and outputs `O`, an
implementation `Y` of a one-shot task with inputs `M` and outputs `O`, and a *continuation map*
`cont : O → Option M`, the sequential composition `X.seqComp Y cont` runs `X`; when `X` returns
`o`, it returns `o` if `cont o = none`, and otherwise continues with `Y` on input `m` if
`cont o = some m`, returning `Y`'s output. The two implementations use disjoint base objects
(`Sum.elim BX BY`). The hand-over takes no extra step: the step in which `X` would return is
replaced by the first step of `Y`.

This is the operational version of Procedure Composition of Aspnes, *A modular approach to
shared-memory consensus* (PODC 2010), for deciding objects (`O = Decision × V`,
`cont (commit, v) = none`, `cont (adopt, v) = some v`).

## Main definitions

* `seqOutput cont oX oY`: the output of the composite, given the outputs of `X` and `Y`.
* `Impl.seqComp X Y cont`: the composite implementation; local states `LX × LY × Option M`
  (the last component is the phase: `none` = running `X`, `some m` = running `Y` on input `m`).
* `Impl.seqProjX`, `Impl.seqProjY`: projections of composite configurations.

## Main results

* `Impl.seqComp_project`: every valid one-shot execution `α` of the composite projects to a
  valid one-shot execution `αX` of `X` with the same inputs and a valid one-shot execution `αY`
  of `Y` whose participants are processes whose `X`-output `o` has `cont o = some m`, with input
  `m`; the outputs of `α` are `seqOutput cont (outputs αX p) (outputs αY p)`.
* `Impl.seqComp_solves`: if `X` and `Y` solve tasks with relations `RX`, `RY`, every one-shot
  execution of the composite is explained by inputs/outputs related by `RX` and `RY`.
* `Impl.seqComp_waitFree`, `Impl.seqComp_tauSteps_le`: wait-freedom and additive step
  complexity from local potentials of `X` and `Y` (`waitFree_of_potential`).

## Limitations

* Only one-shot executions are projected (each process invokes the composite at most once).
* Termination is only derived from potentials (bounded step complexity); there is no general
  `WaitFree X → WaitFree Y → WaitFree (X.seqComp Y cont)`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

variable {P In M O : Type} {ιX ιY : Type} {BX : ιX → ObjSpec} {BY : ιY → ObjSpec} {LX LY : Type}

/-- The output of the sequential composition for a process whose output from `X` is `oX` and
whose output from `Y` is `oY`: nothing if `X` has not returned; `X`'s output `o` if
`cont o = none`; otherwise `Y`'s output. -/
def seqOutput (cont : O → Option M) (oX oY : Option O) : Option O :=
  oX.bind fun o => (cont o).elim (some o) fun _ => oY

@[simp] lemma seqOutput_none (cont : O → Option M) (oY : Option O) :
    seqOutput cont none oY = none := rfl

lemma seqOutput_some (cont : O → Option M) (o : O) (oY : Option O) :
    seqOutput cont (some o) oY = (cont o).elim (some o) fun _ => oY := rfl

lemma seqOutput_of_none {cont : O → Option M} {oX oY : Option O} (h : oX = none) :
    seqOutput cont oX oY = none := by
  subst h; rfl

lemma seqOutput_of_cont_none {cont : O → Option M} {oX oY : Option O} {o : O}
    (h : oX = some o) (hc : cont o = none) : seqOutput cont oX oY = some o := by
  subst h; simp [seqOutput, hc]

lemma seqOutput_of_cont_some {cont : O → Option M} {oX oY : Option O} {o : O} {m : M}
    (h : oX = some o) (hc : cont o = some m) : seqOutput cont oX oY = oY := by
  subst h; simp [seqOutput, hc]

variable [Inhabited O]

namespace Impl

/-- The composite's action when `Y` is running (on input `m`) in local state `ly`, with `X`'s
final local state `lx`. -/
def seqCompYAct (Y : Impl (taskObj M O) BY P LY) (p : P) (lx : LX) (m : M) (ly : LY) :
    Action (taskObj In O) (Sum.elim BX BY) (LX × LY × Option M) :=
  match Y.act p ly with
  | .access i o k => .access (.inr i) o fun r => (lx, k r, some m)
  | .ret r ly' => .ret r (lx, ly', some m)

/-- **Sequential composition** `X; Y` of one-shot task implementations with continuation map
`cont`: run `X`; when `X` returns `o`, return `o` if `cont o = none`, otherwise run `Y` on input
`m` (where `cont o = some m`) and return its output. Local state: `X`'s, `Y`'s and the phase
(`none` = running `X`, `some m` = running `Y` on input `m`). -/
def seqComp (X : Impl (taskObj In O) BX P LX) (Y : Impl (taskObj M O) BY P LY)
    (cont : O → Option M) : Impl (taskObj In O) (Sum.elim BX BY) P (LX × LY × Option M) where
  memInit := fun i => match i with
    | .inl i => X.memInit i
    | .inr i => Y.memInit i
  locInit p := (X.locInit p, Y.locInit p, none)
  invoke p l i := (X.invoke p l.1 i, l.2.1, none)
  act p l := match l.2.2 with
    | none => match X.act p l.1 with
      | .access i o k => .access (.inl i) o fun r => (k r, l.2.1, none)
      | .ret r lx' => match cont r with
        | none => .ret r (lx', l.2.1, none)
        | some m => seqCompYAct Y p lx' m (Y.invoke p l.2.1 m)
    | some m => seqCompYAct Y p l.1 m l.2.1
  allowed := X.allowed

section Lemmas

variable (X : Impl (taskObj In O) BX P LX) (Y : Impl (taskObj M O) BY P LY) (cont : O → Option M)
  {p : P} {lx lx' : LX} {ly ly' : LY} {m : M} {r : O}

lemma seqCompYAct_access {i : ιY} {o : (BY i).Op} {k : (BY i).Resp → LY}
    (h : Y.act p ly = .access i o k) :
    (seqCompYAct (In := In) (BX := BX) Y p lx m ly) =
      .access (.inr i) o fun r => (lx, k r, some m) := by
  simp [seqCompYAct, h]

lemma seqCompYAct_ret (h : Y.act p ly = .ret r ly') :
    (seqCompYAct (In := In) (BX := BX) Y p lx m ly) = .ret r (lx, ly', some m) := by
  simp [seqCompYAct, h]

lemma seqComp_act_access {i : ιX} {o : (BX i).Op} {k : (BX i).Resp → LX}
    (h : X.act p lx = .access i o k) :
    (X.seqComp Y cont).act p (lx, ly, none) = .access (.inl i) o fun r => (k r, ly, none) := by
  simp [seqComp, h]

lemma seqComp_act_ret (h : X.act p lx = .ret r lx') (hc : cont r = none) :
    (X.seqComp Y cont).act p (lx, ly, none) = .ret r (lx', ly, none) := by
  simp [seqComp, h, hc]

lemma seqComp_act_handover (h : X.act p lx = .ret r lx') (hc : cont r = some m) :
    (X.seqComp Y cont).act p (lx, ly, none) = seqCompYAct Y p lx' m (Y.invoke p ly m) := by
  simp [seqComp, h, hc]

lemma seqComp_act_y : (X.seqComp Y cont).act p (lx, ly, some m) = seqCompYAct Y p lx m ly := rfl

end Lemmas

/-! ### Projections -/

/-- The projection of a composite configuration to `X`: `X`'s local states, `X`-objects, and the
pending operation of processes still running `X`. -/
def seqProjX (C : Config (taskObj In O) (Sum.elim BX BY) P (LX × LY × Option M)) :
    Config (taskObj In O) BX P LX where
  loc p := (C.loc p).1
  pend p := (C.loc p).2.2.elim (C.pend p) fun _ => none
  mem i := C.mem (.inl i)

/-- The projection of a composite configuration to `Y`: `Y`'s local states, `Y`-objects, and the
pending input `m` of processes running `Y` on `m`. -/
def seqProjY (C : Config (taskObj In O) (Sum.elim BX BY) P (LX × LY × Option M)) :
    Config (taskObj M O) BY P LY where
  loc p := (C.loc p).2.1
  pend p := (C.pend p).bind fun _ => (C.loc p).2.2
  mem i := C.mem (.inr i)

end Impl

/-! ### Auxiliary lemmas on executions -/

section Aux

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq P] [DecidableEq ι]

omit [DecidableEq P] [DecidableEq ι] in
private lemma cfg_ext {C D : Config A B P L} (h1 : C.loc = D.loc) (h2 : C.pend = D.pend)
    (h3 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp_all

/-- A process that has not invoked anything has no output. -/
lemma Impl.outputs_eq_none_of_opsOf_nil (I : Impl A B P L) {β : List (Label P A)}
    {D : Config A B P L} (h : I.run β = some D) {p : P} (hp : opsOf β p = []) :
    outputs β p = none := by
  have := I.run_resps_le_ops h p
  rw [hp] at this
  simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at this
  simp [outputs, this]

/-- A pending process that invoked at most one operation has no output yet. -/
lemma Impl.outputs_eq_none_of_pend (I : Impl A B P L) {β : List (Label P A)}
    {D : Config A B P L} (h : I.run β = some D) {p : P} (hp : D.pend p ≠ none)
    (h1 : (opsOf β p).length ≤ 1) : outputs β p = none := by
  have := I.run_pend_counts h hp
  have h0 : respsOf β p = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [outputs, h0]

/-- In a valid execution, a process with an output has an input. -/
lemma Impl.inputs_ne_none_of_outputs_ne_none (I : Impl A B P L) {β : List (Label P A)}
    (hβ : I.Valid β) {p : P} (hp : outputs β p ≠ none) : inputs β p ≠ none := by
  obtain ⟨D, hD⟩ := hβ
  intro hi
  have : opsOf β p = [] := by simpa [inputs] using hi
  exact hp (I.outputs_eq_none_of_opsOf_nil hD this)

omit [DecidableEq ι] in
private lemma opsOf_outputs_append_of_ne {γ δ : List (Label P A)} {p q : P}
    (hδ : ∀ ℓ ∈ δ, ℓ.proc = p) (hq : q ≠ p) :
    opsOf (γ ++ δ) q = opsOf γ q ∧ outputs (γ ++ δ) q = outputs γ q := by
  have hne : ∀ ℓ ∈ δ, ℓ.proc ≠ q := fun ℓ hℓ => by rw [hδ ℓ hℓ]; exact Ne.symm hq
  rw [opsOf_append, opsOf_eq_nil_of_proc_ne hne, outputs_append, outputs_eq_none_of_proc_ne hne]
  simp

omit [DecidableEq ι] in
private lemma opsOf_append_inv_tau (β : List (Label P A)) (p : P) (o : A.Op) :
    opsOf (β ++ [.inv p o, .tau p]) p = opsOf β p ++ [o] := by
  simp [opsOf]

omit [DecidableEq ι] in
private lemma outputs_append_inv_tau (β : List (Label P A)) (p : P) (o : A.Op) :
    outputs (β ++ [.inv p o, .tau p]) p = outputs β p := by
  rw [outputs_append]
  have : outputs ([.inv p o, .tau p] : List (Label P A)) p = none := by simp [outputs, respsOf]
  rw [this, Option.or_none]

omit [DecidableEq ι] in
private lemma opsOf_append_inv_ret (β : List (Label P A)) (p : P) (o : A.Op) (r : A.Resp) :
    opsOf (β ++ [.inv p o, .ret p r]) p = opsOf β p ++ [o] := by
  simp [opsOf]

omit [DecidableEq ι] in
private lemma outputs_append_inv_ret (β : List (Label P A)) (p : P) (o : A.Op) (r : A.Resp) :
    outputs (β ++ [.inv p o, .ret p r]) p = (outputs β p).or (some r) := by
  rw [outputs_append]
  have : outputs ([.inv p o, .ret p r] : List (Label P A)) p = some r := by
    simp [outputs, respsOf, List.findSome?_cons]
  rw [this]

omit [DecidableEq P] [DecidableEq ι] in
private lemma update_inl_comp [DecidableEq ιX] [DecidableEq ιY]
    (f : (i : ιX ⊕ ιY) → (Sum.elim BX BY i).State) (i : ιX) (v : (BX i).State) :
    (fun j => Function.update f (.inl i) v (.inl j)) = Function.update (fun j => f (.inl j)) i v :=
  Function.update_comp_eq_of_injective' f Sum.inl_injective i v

omit [DecidableEq P] [DecidableEq ι] in
private lemma update_inr_comp [DecidableEq ιX] [DecidableEq ιY]
    (f : (i : ιX ⊕ ιY) → (Sum.elim BX BY i).State) (i : ιY) (v : (BY i).State) :
    (fun j => Function.update f (.inr i) v (.inr j)) = Function.update (fun j => f (.inr j)) i v :=
  Function.update_comp_eq_of_injective' f Sum.inr_injective i v

omit [DecidableEq P] [DecidableEq ι] in
private lemma update_inl_inr [DecidableEq ιX] [DecidableEq ιY]
    (f : (i : ιX ⊕ ιY) → (Sum.elim BX BY i).State) (i : ιX) (v : (BX i).State) :
    (fun j => Function.update f (.inl i) v (.inr j)) = fun j => f (.inr j) :=
  funext fun _ => Function.update_of_ne Sum.inr_ne_inl _ _

omit [DecidableEq P] [DecidableEq ι] in
private lemma update_inr_inl [DecidableEq ιX] [DecidableEq ιY]
    (f : (i : ιX ⊕ ιY) → (Sum.elim BX BY i).State) (i : ιY) (v : (BY i).State) :
    (fun j => Function.update f (.inr i) v (.inl j)) = fun j => f (.inl j) :=
  funext fun _ => Function.update_of_ne Sum.inl_ne_inr _ _

end Aux

/-! ### Projection of executions -/

namespace Impl

variable [DecidableEq P] [DecidableEq ιX] [DecidableEq ιY]

/-- The per-process relation between a composite execution `α` and its projections `αX`, `αY`,
for a process in phase `ph`. -/
def SeqInvP (cont : O → Option M) (ph : Option M) (α αX : List (Label P (taskObj In O)))
    (αY : List (Label P (taskObj M O))) (p : P) : Prop :=
  opsOf αX p = opsOf α p ∧ outputs α p = seqOutput cont (outputs αX p) (outputs αY p) ∧
    ph.elim (opsOf αY p = []) fun m =>
      ∃ o, outputs αX p = some o ∧ cont o = some m ∧ opsOf αY p = [m]

lemma SeqInvP.append_of_ne {cont : O → Option M} {ph : Option M}
    {α αX β βX : List (Label P (taskObj In O))} {αY βY : List (Label P (taskObj M O))} {p q : P}
    (h : SeqInvP cont ph α αX αY q) (hq : q ≠ p) (hβ : ∀ ℓ ∈ β, ℓ.proc = p)
    (hβX : ∀ ℓ ∈ βX, ℓ.proc = p) (hβY : ∀ ℓ ∈ βY, ℓ.proc = p) :
    SeqInvP cont ph (α ++ β) (αX ++ βX) (αY ++ βY) q := by
  obtain ⟨a1, a2⟩ := opsOf_outputs_append_of_ne (γ := α) hβ hq
  obtain ⟨b1, b2⟩ := opsOf_outputs_append_of_ne (γ := αX) hβX hq
  obtain ⟨c1, c2⟩ := opsOf_outputs_append_of_ne (γ := αY) hβY hq
  unfold SeqInvP
  rw [a1, a2, b1, b2, c1, c2]
  exact h

variable (X : Impl (taskObj In O) BX P LX) (Y : Impl (taskObj M O) BY P LY) (cont : O → Option M)

lemma seqProjX_initCfg : seqProjX (X.seqComp Y cont).initCfg = X.initCfg := rfl

lemma seqProjY_initCfg : seqProjY (X.seqComp Y cont).initCfg = Y.initCfg := rfl

/-- **Simulation.** The configuration reached by a one-shot execution `α` of the composite
projects to configurations reached by executions `αX` of `X` and `αY` of `Y`, related to `α` by
`SeqInvP`. -/
theorem seqComp_sim (hY : ∀ p o m, cont o = some m → Y.allowed p m)
    {α : List (Label P (taskObj In O))}
    {C : Config (taskObj In O) (Sum.elim BX BY) P (LX × LY × Option M)}
    (h : (X.seqComp Y cont).run α = some C) (h1 : OneShot α) :
    ∃ αX αY, X.run αX = some (seqProjX C) ∧ Y.run αY = some (seqProjY C) ∧
      ∀ p, SeqInvP cont (C.loc p).2.2 α αX αY p := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [run_nil, Option.some.injEq] at h; subst h
    refine ⟨[], [], rfl, rfl, fun p => ?_⟩
    simp [SeqInvP, outputs, opsOf, seqComp, initCfg, seqOutput, Option.bind]; rfl
  | append_singleton α ℓ ih =>
    rw [run_concat] at h
    cases hα : (X.seqComp Y cont).run α with
    | none => simp [hα] at h
    | some C₀ =>
    simp only [hα, Option.bind_some] at h
    obtain ⟨αX, αY, hX, hYr, hinv⟩ := ih hα h1.of_append
    have hother : ∀ q, ℓ.proc ≠ q → C.loc q = C₀.loc q := fun q hq => (step_other h hq).1
    have h1p : ∀ p, (opsOf α p).length ≤ 1 := h1.of_append
    cases ℓ with
    | inv p i =>
      obtain ⟨hpend, hall, -⟩ := step_inv h
      rw [step_inv_eq_some hpend hall] at h
      cases h
      have hops : opsOf α p = [] := by
        have := h1 p
        simp only [opsOf_append, List.length_append] at this
        simpa using this
      obtain ⟨hiX, hoX, hph⟩ := hinv p
      have hXo : outputs αX p = none := X.outputs_eq_none_of_opsOf_nil hX (hiX.trans hops)
      have hph0 : (C₀.loc p).2.2 = none := by
        rcases hph' : (C₀.loc p).2.2 with _ | m
        · rfl
        · rw [hph'] at hph; obtain ⟨o, ho, -⟩ := hph; rw [hXo] at ho; cases ho
      have hYn : opsOf αY p = [] := by rw [hph0] at hph; exact hph
      refine ⟨αX ++ [.inv p i], αY ++ [], ?_, ?_, fun q => ?_⟩
      · rw [run_concat, hX, Option.bind_some,
          step_inv_eq_some (I := X) (by simp [seqProjX, hph0, hpend]) hall]
        congr 1
        refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
        · by_cases hq : q = p
          · subst hq; simp [seqProjX, seqComp]
          · simp [seqProjX, hq]
        · by_cases hq : q = p
          · subst hq; simp [seqProjX, seqComp]
          · simp [seqProjX, hq]
      · rw [List.append_nil, hYr]
        congr 1
        refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
        · by_cases hq : q = p
          · subst hq; simp [seqProjY, seqComp]
          · simp [seqProjY, hq]
        · by_cases hq : q = p
          · subst hq; simp [seqProjY, seqComp, hpend, Option.bind]; rfl
          · simp [seqProjY, hq]
      · by_cases hq : q = p
        · subst hq
          refine ⟨by simp [hiX], by simpa using hoX, ?_⟩
          simpa [seqComp] using hYn
        · rw [hother q (by simpa [Label.proc] using Ne.symm hq)]
          exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
            (by simp)
    | tau p =>
      have hpend := (step_tau h).1
      obtain ⟨hiX, hoX, hph⟩ := hinv p
      have hne : ∀ q, q ≠ p → (Label.tau p : Label P (taskObj In O)).proc ≠ q :=
        fun q hq => by simpa [Label.proc] using Ne.symm hq
      rcases hl : C₀.loc p with ⟨lx, ly, _ | m⟩
      · -- `p` is running `X`
        rw [hl] at hph
        have hYn : opsOf αY p = [] := hph
        have hpX : (seqProjX C₀).pend p ≠ none := by simpa [seqProjX, hl] using hpend
        have hXo : outputs αX p = none :=
          X.outputs_eq_none_of_pend hX hpX (by rw [hiX]; exact h1p p)
        have hYo : outputs αY p = none := Y.outputs_eq_none_of_opsOf_nil hYr hYn
        cases hXa : X.act p lx with
        | access i o k =>
          have hact := seqComp_act_access X Y cont (ly := ly) hXa
          rw [← hl] at hact
          rw [step_tau_eq_some hpend hact] at h
          cases h
          refine ⟨αX ++ [.tau p], αY ++ [], ?_, ?_, fun q => ?_⟩
          · rw [run_concat, hX, Option.bind_some, step_tau_eq_some (I := X) hpX
              (show X.act p (C₀.loc p).1 = _ by rw [hl]; exact hXa)]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
            · by_cases hq : q = p
              · subst hq; simp [seqProjX]
              · simp [seqProjX, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjX, hl]
              · simp [seqProjX, hq]
            · exact congrFun (update_inl_comp C₀.mem i _).symm j
          · rw [List.append_nil, hYr]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
            · by_cases hq : q = p
              · subst hq; simp [seqProjY, hl]
              · simp [seqProjY, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjY, hl]
              · simp [seqProjY, hq]
            · exact Eq.symm (Function.update_of_ne (Sum.inr_ne_inl : (Sum.inr j : ιX ⊕ ιY) ≠ .inl i)
                ((Sum.elim BX BY (Sum.inl i)).δ (C₀.mem (Sum.inl i)) o).1 C₀.mem)
          · by_cases hq : q = p
            · subst hq
              refine ⟨by simpa using hiX, by simpa using hoX, ?_⟩
              simpa [hl] using hYn
            · rw [hother q (hne q hq)]
              exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                (by simp)
        | ret r lx' =>
          cases hc : cont r with
          | none =>
            have hact := seqComp_act_ret X Y cont (ly := ly) hXa hc
            rw [← hl] at hact
            simp [step, hpend, hact] at h
          | some m =>
            have hact := seqComp_act_handover X Y cont (ly := ly) hXa hc
            rw [← hl] at hact
            cases hYa : Y.act p (Y.invoke p ly m) with
            | ret r' ly' =>
              rw [seqCompYAct_ret Y hYa] at hact
              simp [step, hpend, hact] at h
            | access i o k =>
              rw [seqCompYAct_access Y hYa] at hact
              rw [step_tau_eq_some hpend hact] at h
              cases h
              have hpY : (seqProjY C₀).pend p = none := by
                simp only [seqProjY, hl]; cases C₀.pend p <;> rfl
              refine ⟨αX ++ [.ret p r], αY ++ [.inv p m, .tau p], ?_, ?_, fun q => ?_⟩
              · rw [run_concat, hX, Option.bind_some, step_ret_eq_some (I := X) hpX
                  (show X.act p (C₀.loc p).1 = _ by rw [hl]; exact hXa)]
                congr 1
                refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
                · by_cases hq : q = p
                  · subst hq; simp [seqProjX]
                  · simp [seqProjX, hq]
                · by_cases hq : q = p
                  · subst hq; simp [seqProjX]
                  · simp [seqProjX, hq]
                · have hne' : (Sum.inl j : ιX ⊕ ιY) ≠ .inr i := Sum.inl_ne_inr
                  first
                  | exact Function.update_of_ne hne' _ C₀.mem
                  | exact Eq.symm (Function.update_of_ne hne'
                      ((Sum.elim BX BY (Sum.inr i)).δ (C₀.mem (Sum.inr i)) o).1 C₀.mem)
              · rw [Y.run_append_of_eq hYr, runFrom_cons, step_inv_eq_some hpY (hY p r m hc),
                  Option.bind_some, runFrom_cons,
                  step_tau_eq_some (I := Y) (by simp)
                    (show Y.act p (Function.update (seqProjY C₀).loc p
                      (Y.invoke p ((seqProjY C₀).loc p) m) p) = _ by
                        simp only [Function.update_self]; simp only [seqProjY, hl]; exact hYa),
                  Option.bind_some, runFrom_nil]
                congr 1
                refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
                · by_cases hq : q = p
                  · subst hq; simp [seqProjY, hl]
                  · simp [seqProjY, hq]
                · by_cases hq : q = p
                  · subst hq
                    obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hpend
                    simp [seqProjY, hi0, Option.bind]; rfl
                  · simp [seqProjY, hq]
                · exact congrFun (update_inr_comp C₀.mem i _).symm j
              · by_cases hq : q = p
                · subst hq
                  refine ⟨by simpa using hiX, ?_, ?_⟩
                  · have e1 : outputs (αX ++ [.ret q r]) q = some r := by
                      rw [outputs_concat, hXo]; simp
                    have e2 : outputs (αY ++ [.inv q m, .tau q]) q = none :=
                      (outputs_append_inv_tau _ _ _).trans hYo
                    rw [outputs_append_tau, hoX]
                    exact (seqOutput_of_none hXo).trans ((seqOutput_of_cont_some e1 hc).trans e2).symm
                  · simp only [Function.update_self, Option.elim]
                    refine ⟨r, ?_, hc, ?_⟩
                    · rw [outputs_concat, hXo]; simp
                    · exact (opsOf_append_inv_tau _ _ _).trans (by rw [hYn]; rfl)
                · rw [hother q (hne q hq)]
                  exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                    (by simp [Label.proc])
      · -- `p` is running `Y`
        rw [hl] at hph
        obtain ⟨o0, hoX0, hco, hYops⟩ := hph
        obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hpend
        have hpY : (seqProjY C₀).pend p ≠ none := by
          simp only [seqProjY, hl, hi0]; intro h; cases h
        have hYo : outputs αY p = none :=
          Y.outputs_eq_none_of_pend hYr hpY (by rw [hYops]; exact Nat.le_refl 1)
        cases hYa : Y.act p ly with
        | ret r' ly' =>
          have hact := (seqComp_act_y X Y cont (lx := lx) (ly := ly) (m := m)).trans
            (seqCompYAct_ret Y hYa)
          rw [← hl] at hact
          simp [step, hpend, hact] at h
        | access i o k =>
          have hact := (seqComp_act_y X Y cont (lx := lx) (ly := ly) (m := m)).trans
            (seqCompYAct_access Y hYa)
          rw [← hl] at hact
          rw [step_tau_eq_some hpend hact] at h
          cases h
          refine ⟨αX ++ [], αY ++ [.tau p], ?_, ?_, fun q => ?_⟩
          · rw [List.append_nil, hX]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
            · by_cases hq : q = p
              · subst hq; simp [seqProjX, hl]
              · simp [seqProjX, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjX, hl]
              · simp [seqProjX, hq]
            · have hne' : (Sum.inl j : ιX ⊕ ιY) ≠ .inr i := Sum.inl_ne_inr
              first
              | exact Function.update_of_ne hne' _ C₀.mem
              | exact Eq.symm (Function.update_of_ne hne'
                  ((Sum.elim BX BY (Sum.inr i)).δ (C₀.mem (Sum.inr i)) o).1 C₀.mem)
          · rw [run_concat, hYr, Option.bind_some, step_tau_eq_some (I := Y) hpY
              (show Y.act p (C₀.loc p).2.1 = _ by rw [hl]; exact hYa)]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) (funext fun j => ?_)
            · by_cases hq : q = p
              · subst hq; simp [seqProjY]
              · simp [seqProjY, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjY, hl]
              · simp [seqProjY, hq]
            · exact congrFun (update_inr_comp C₀.mem i _).symm j
          · by_cases hq : q = p
            · subst hq
              refine ⟨by simpa using hiX, by simpa using hoX, ?_⟩
              simp only [Function.update_self, Option.elim]
              exact ⟨o0, by simpa using hoX0, hco, by simpa using hYops⟩
            · rw [hother q (hne q hq)]
              exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                (by simp [Label.proc])
    | ret p r =>
      obtain ⟨hpend, -, -, l, hact0, -⟩ := step_ret h
      obtain ⟨hiX, hoX, hph⟩ := hinv p
      have hne : ∀ q, q ≠ p → (Label.ret p r : Label P (taskObj In O)).proc ≠ q :=
        fun q hq => by simpa [Label.proc] using Ne.symm hq
      rcases hl : C₀.loc p with ⟨lx, ly, _ | m⟩
      · -- `p` is running `X`
        rw [hl] at hph
        have hYn : opsOf αY p = [] := hph
        have hpX : (seqProjX C₀).pend p ≠ none := by simpa [seqProjX, hl] using hpend
        have hXo : outputs αX p = none :=
          X.outputs_eq_none_of_pend hX hpX (by rw [hiX]; exact h1p p)
        have hYo : outputs αY p = none := Y.outputs_eq_none_of_opsOf_nil hYr hYn
        have h0 : outputs α p = none := hoX.trans (seqOutput_of_none hXo)
        have hpY : (seqProjY C₀).pend p = none := by
          simp only [seqProjY, hl]; cases C₀.pend p <;> rfl
        cases hXa : X.act p lx with
        | access i o k =>
          have hact := seqComp_act_access X Y cont (ly := ly) hXa
          rw [← hl, hact0] at hact
          cases hact
        | ret r0 lx' =>
          cases hc : cont r0 with
          | none =>
            have hact := seqComp_act_ret X Y cont (ly := ly) hXa hc
            rw [← hl] at hact
            rw [hact] at hact0
            obtain ⟨hr, -⟩ := Action.ret.inj hact0
            subst hr
            rw [step_ret_eq_some hpend hact] at h
            cases h
            refine ⟨αX ++ [.ret p r0], αY ++ [], ?_, ?_, fun q => ?_⟩
            · rw [run_concat, hX, Option.bind_some, step_ret_eq_some (I := X) hpX
                (show X.act p (C₀.loc p).1 = _ by rw [hl]; exact hXa)]
              congr 1
              refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
              · by_cases hq : q = p
                · subst hq; simp [seqProjX]
                · simp [seqProjX, hq]
              · by_cases hq : q = p
                · subst hq; simp [seqProjX]
                · simp [seqProjX, hq]
            · rw [List.append_nil, hYr]
              congr 1
              refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
              · by_cases hq : q = p
                · subst hq; simp [seqProjY, hl]
                · simp [seqProjY, hq]
              · by_cases hq : q = p
                · subst hq; rw [hpY]; simp [seqProjY, Option.bind]
                · simp [seqProjY, hq]
            · by_cases hq : q = p
              · subst hq
                refine ⟨by simpa using hiX, ?_, ?_⟩
                · have e1 : outputs (αX ++ [.ret q r0]) q = some r0 := by
                    rw [outputs_concat, hXo]; simp
                  have e0 : outputs (α ++ [.ret q r0]) q = some r0 := by
                    rw [outputs_concat, h0]; simp
                  exact e0.trans (seqOutput_of_cont_none e1 hc).symm
                · simp only [Function.update_self, Option.elim]
                  simpa using hYn
              · rw [hother q (hne q hq)]
                exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                  (by simp)
          | some m =>
            have hact := seqComp_act_handover X Y cont (ly := ly) hXa hc
            rw [← hl] at hact
            cases hYa : Y.act p (Y.invoke p ly m) with
            | access i o k =>
              rw [seqCompYAct_access Y hYa] at hact
              rw [hact] at hact0
              cases hact0
            | ret r' ly' =>
              rw [seqCompYAct_ret Y hYa] at hact
              rw [hact] at hact0
              obtain ⟨hr, -⟩ := Action.ret.inj hact0
              subst hr
              rw [step_ret_eq_some hpend hact] at h
              cases h
              refine ⟨αX ++ [.ret p r0], αY ++ [.inv p m, .ret p r'], ?_, ?_, fun q => ?_⟩
              · rw [run_concat, hX, Option.bind_some, step_ret_eq_some (I := X) hpX
                  (show X.act p (C₀.loc p).1 = _ by rw [hl]; exact hXa)]
                congr 1
                refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
                · by_cases hq : q = p
                  · subst hq; simp [seqProjX]
                  · simp [seqProjX, hq]
                · by_cases hq : q = p
                  · subst hq; simp [seqProjX]
                  · simp [seqProjX, hq]
              · rw [Y.run_append_of_eq hYr, runFrom_cons, step_inv_eq_some hpY (hY p r0 m hc),
                  Option.bind_some, runFrom_cons,
                  step_ret_eq_some (I := Y) (by simp)
                    (show Y.act p (Function.update (seqProjY C₀).loc p
                      (Y.invoke p ((seqProjY C₀).loc p) m) p) = _ by
                        simp only [Function.update_self]; simp only [seqProjY, hl]; exact hYa),
                  Option.bind_some, runFrom_nil]
                congr 1
                refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
                · by_cases hq : q = p
                  · subst hq; simp [seqProjY, hl]
                  · simp [seqProjY, hq]
                · by_cases hq : q = p
                  · subst hq; simp [seqProjY, Option.bind]
                  · simp [seqProjY, hq]
              · by_cases hq : q = p
                · subst hq
                  have e1 : outputs (αX ++ [.ret q r0]) q = some r0 := by
                    rw [outputs_concat, hXo]; simp
                  refine ⟨(opsOf_append_ret _ _ _ _).trans
                    (hiX.trans (opsOf_append_ret _ _ _ _).symm), ?_, ?_⟩
                  · have e0 : outputs (α ++ [(Label.ret q r' : Label P (taskObj In O))]) q =
                        some r' := by
                      rw [outputs_concat, h0]; exact ite_eq_left_iff.2 fun h => absurd rfl h
                    have e2 : outputs (αY ++ [.inv q m, .ret q r']) q = some r' :=
                      (outputs_append_inv_ret _ _ _ _).trans (by rw [hYo]; rfl)
                    exact e0.trans ((seqOutput_of_cont_some e1 hc).trans e2).symm
                  · simp only [Function.update_self, Option.elim]
                    exact ⟨r0, e1, hc, (opsOf_append_inv_ret _ _ _ _).trans (by rw [hYn]; rfl)⟩
                · rw [hother q (hne q hq)]
                  exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                    (by simp [Label.proc])
      · -- `p` is running `Y`
        rw [hl] at hph
        obtain ⟨o0, hoX0, hco, hYops⟩ := hph
        obtain ⟨i0, hi0⟩ := Option.ne_none_iff_exists'.1 hpend
        have hpY : (seqProjY C₀).pend p ≠ none := by
          simp only [seqProjY, hl, hi0]; intro h; cases h
        have hYo : outputs αY p = none :=
          Y.outputs_eq_none_of_pend hYr hpY (by rw [hYops]; exact Nat.le_refl 1)
        have h0 : outputs α p = none := hoX.trans ((seqOutput_of_cont_some hoX0 hco).trans hYo)
        cases hYa : Y.act p ly with
        | access i o k =>
          have hact := (seqComp_act_y X Y cont (lx := lx) (ly := ly) (m := m)).trans
            (seqCompYAct_access Y hYa)
          rw [← hl, hact0] at hact
          cases hact
        | ret r' ly' =>
          have hact := (seqComp_act_y X Y cont (lx := lx) (ly := ly) (m := m)).trans
            (seqCompYAct_ret Y hYa)
          rw [← hl] at hact
          rw [hact] at hact0
          obtain ⟨hr, -⟩ := Action.ret.inj hact0
          subst hr
          rw [step_ret_eq_some hpend hact] at h
          cases h
          refine ⟨αX ++ [], αY ++ [.ret p r'], ?_, ?_, fun q => ?_⟩
          · rw [List.append_nil, hX]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
            · by_cases hq : q = p
              · subst hq; simp [seqProjX, hl]
              · simp [seqProjX, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjX, hl]
              · simp [seqProjX, hq]
          · rw [run_concat, hYr, Option.bind_some, step_ret_eq_some (I := Y) hpY
              (show Y.act p (C₀.loc p).2.1 = _ by rw [hl]; exact hYa)]
            congr 1
            refine cfg_ext (funext fun q => ?_) (funext fun q => ?_) rfl
            · by_cases hq : q = p
              · subst hq; simp [seqProjY]
              · simp [seqProjY, hq]
            · by_cases hq : q = p
              · subst hq; simp [seqProjY, Option.bind]
              · simp [seqProjY, hq]
          · by_cases hq : q = p
            · subst hq
              refine ⟨by rw [List.append_nil]; exact hiX.trans (opsOf_append_ret _ _ _ _).symm,
                ?_, ?_⟩
              · have e0 : outputs (α ++ [(Label.ret q r' : Label P (taskObj In O))]) q =
                    some r' := by
                  rw [outputs_concat, h0]; exact ite_eq_left_iff.2 fun h => absurd rfl h
                have e2 : outputs (αY ++ [.ret q r']) q = some r' := by
                  rw [outputs_concat, hYo]; simp
                exact e0.trans ((seqOutput_of_cont_some (by simpa using hoX0) hco).trans e2).symm
              · simp only [Function.update_self, Option.elim]
                exact ⟨o0, by simpa using hoX0, hco, by simpa using hYops⟩
            · rw [hother q (hne q hq)]
              exact (hinv q).append_of_ne hq (by simp [Label.proc]) (by simp [Label.proc])
                (by simp [Label.proc])

/-- **Projection of one-shot executions.** Every valid one-shot execution `α` of the sequential
composition `X.seqComp Y cont` projects to a valid one-shot execution `αX` of `X` with the same
inputs and a valid one-shot execution `αY` of `Y` such that

* a process invokes `Y` (on input `m`) only after `X` returned some `o` with `cont o = some m`;
* the output of each process in `α` is `X`'s output `o` if `cont o = none`, and `Y`'s output
  otherwise (`seqOutput`).

(`αX` consists of the steps of the processes running `X`, plus `X`'s response at the hand-over
step; `αY` of `Y`'s invocation at the hand-over step and the steps of the processes running `Y`.)
The hypothesis `hY` says that `Y` allows the invocations it receives. -/
theorem seqComp_project (hY : ∀ p o m, cont o = some m → Y.allowed p m)
    {α : List (Label P (taskObj In O))} (hα : (X.seqComp Y cont).Valid α) (h1 : OneShot α) :
    ∃ (αX : List (Label P (taskObj In O))) (αY : List (Label P (taskObj M O))),
      X.Valid αX ∧ OneShot αX ∧ Y.Valid αY ∧ OneShot αY ∧ inputs αX = inputs α ∧
      (∀ p m, inputs αY p = some m → ∃ o, outputs αX p = some o ∧ cont o = some m) ∧
      ∀ p, outputs α p = seqOutput cont (outputs αX p) (outputs αY p) := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨αX, αY, hX, hYr, hinv⟩ := seqComp_sim X Y cont hY hC h1
  refine ⟨αX, αY, ⟨_, hX⟩, fun p => ?_, ⟨_, hYr⟩, fun p => ?_, funext fun p => ?_,
    fun p m hm => ?_, fun p => (hinv p).2.1⟩
  · rw [(hinv p).1]; exact h1 p
  · obtain ⟨-, -, h⟩ := hinv p
    rcases hph : (C.loc p).2.2 with _ | m <;> rw [hph] at h
    · have h' : opsOf αY p = [] := h
      rw [h']; exact Nat.zero_le 1
    · obtain ⟨-, -, -, h⟩ := h; rw [h]; exact Nat.le_refl 1
  · simp only [inputs, (hinv p).1]
  · obtain ⟨-, -, h⟩ := hinv p
    rcases hph : (C.loc p).2.2 with _ | m' <;> rw [hph] at h
    · have h' : opsOf αY p = [] := h
      simp [inputs, h'] at hm
    · obtain ⟨o, ho, hc, hops⟩ := h
      have : (some m' : Option M) = some m := by rw [← hm]; unfold inputs; rw [hops]; rfl
      cases Option.some.inj this
      exact ⟨o, ho, hc⟩

/-- **Safety of the sequential composition.** If `X` solves a task with relation `RX` and `Y` a
task with relation `RY` (both with outputs in `O`), then the inputs and outputs of every valid
one-shot execution of `X.seqComp Y cont` are explained by an `RX`-related run of `X` and an
`RY`-related run of `Y`, linked by `cont`: a process participates in `Y` with input `m` only if
its `X`-output `o` has `cont o = some m`, only participants of `Y` get a `Y`-output, and the
composite output is `seqOutput cont (outX p) (outY p)`. -/
theorem seqComp_solves {RX : (P → Option In) → (P → Option O) → Prop}
    {RY : (P → Option M) → (P → Option O) → Prop}
    (hX : X.Solves ⟨In, O, RX⟩) (hYs : Y.Solves ⟨M, O, RY⟩)
    (hY : ∀ p o m, cont o = some m → Y.allowed p m)
    {α : List (Label P (taskObj In O))} (hα : (X.seqComp Y cont).Valid α) (h1 : OneShot α) :
    ∃ (outX : P → Option O) (inpY : P → Option M) (outY : P → Option O),
      RX (inputs α) outX ∧ RY inpY outY ∧
      (∀ p m, inpY p = some m → ∃ o, outX p = some o ∧ cont o = some m) ∧
      (∀ p, outY p ≠ none → inpY p ≠ none) ∧
      ∀ p, outputs α p = seqOutput cont (outX p) (outY p) := by
  obtain ⟨αX, αY, hvX, h1X, hvY, h1Y, hin, hlink, hout⟩ := seqComp_project X Y cont hY hα h1
  refine ⟨outputs αX, inputs αY, outputs αY, ?_, hYs αY hvY h1Y, hlink,
    fun p hp => Y.inputs_ne_none_of_outputs_ne_none hvY hp, hout⟩
  rw [← hin]; exact hX αX hvX h1X

/-! ### Termination and step complexity -/

/-- The potential of the composite, from potentials `μX` of `X` and `μY` of `Y` and a bound `KY`
on `Y`'s potential right after an invocation: while running `X`, `μX + KY`; while running `Y`,
`μY`. -/
def seqPotential (μX : P → LX → ℕ) (μY : P → LY → ℕ) (KY : ℕ) (p : P)
    (l : LX × LY × Option M) : ℕ :=
  l.2.2.elim (μX p l.1 + KY) fun _ => μY p l.2.1

/-- If the potentials of `X` and `Y` strictly decrease at every base-object access and `Y`'s
potential right after an invocation is at most `KY`, then `seqPotential μX μY KY` strictly
decreases at every base-object access of the composite. -/
theorem seqComp_potential (μX : P → LX → ℕ) (μY : P → LY → ℕ) (KY : ℕ)
    (hμX : ∀ p l i o k, X.act p l = .access i o k → ∀ x, μX p (k x) < μX p l)
    (hμY : ∀ p l i o k, Y.act p l = .access i o k → ∀ x, μY p (k x) < μY p l)
    (hK : ∀ p l m, μY p (Y.invoke p l m) ≤ KY) :
    ∀ p l i o k, (X.seqComp Y cont).act p l = .access i o k →
      ∀ x, seqPotential μX μY KY p (k x) < seqPotential μX μY KY p l := by
  rintro p ⟨lx, ly, _ | m⟩ i o k h x
  · cases hXa : X.act p lx with
    | access j o' k' =>
      rw [seqComp_act_access X Y cont hXa] at h
      cases h
      have := hμX p lx j o' k' hXa x
      simp only [seqPotential, Option.elim]
      omega
    | ret r lx' =>
      cases hc : cont r with
      | none => rw [seqComp_act_ret X Y cont hXa hc] at h; cases h
      | some m =>
        rw [seqComp_act_handover X Y cont hXa hc] at h
        cases hYa : Y.act p (Y.invoke p ly m) with
        | access j o' k' =>
          rw [seqCompYAct_access Y hYa] at h
          cases h
          have := hμY p _ j o' k' hYa x
          have := hK p ly m
          simp only [seqPotential, Option.elim]
          omega
        | ret r' ly' => rw [seqCompYAct_ret Y hYa] at h; cases h
  · rw [seqComp_act_y] at h
    cases hYa : Y.act p ly with
    | access j o' k' =>
      rw [seqCompYAct_access Y hYa] at h
      cases h
      have := hμY p ly j o' k' hYa x
      simp only [seqPotential, Option.elim]
      omega
    | ret r' ly' => rw [seqCompYAct_ret Y hYa] at h; cases h

/-- **Termination (wait-freedom) of the sequential composition** from potentials: if `X` and `Y`
have potentials on local states that strictly decrease at every base-object access, and `Y`'s
potential right after an invocation is bounded by `KY`, then `X.seqComp Y cont` is
wait-free. -/
theorem seqComp_waitFree (μX : P → LX → ℕ) (μY : P → LY → ℕ) (KY : ℕ)
    (hμX : ∀ p l i o k, X.act p l = .access i o k → ∀ x, μX p (k x) < μX p l)
    (hμY : ∀ p l i o k, Y.act p l = .access i o k → ∀ x, μY p (k x) < μY p l)
    (hK : ∀ p l m, μY p (Y.invoke p l m) ≤ KY) : (X.seqComp Y cont).WaitFree :=
  (X.seqComp Y cont).waitFree_of_potential (seqPotential μX μY KY)
    (seqComp_potential X Y cont μX μY KY hμX hμY hK)

/-- **Additive step complexity of the sequential composition.** Under the hypotheses of
`seqComp_waitFree`, after `p` invokes the composite with input `i`, it performs at most
`μX p (X.invoke p lx i) + KY` base-object accesses before it returns (for the local state `lx`
of `X` at the invocation): the accesses of `X` plus at most `KY` accesses of `Y`. -/
theorem seqComp_tauSteps_le (μX : P → LX → ℕ) (μY : P → LY → ℕ) (KY : ℕ)
    (hμX : ∀ p l i o k, X.act p l = .access i o k → ∀ x, μX p (k x) < μX p l)
    (hμY : ∀ p l i o k, Y.act p l = .access i o k → ∀ x, μY p (k x) < μY p l)
    (hK : ∀ p l m, μY p (Y.invoke p l m) ≤ KY)
    {α γ : List (Label P (taskObj In O))} {p : P} {i : In}
    (hv : (X.seqComp Y cont).Valid (α ++ .inv p i :: γ)) (hret : ∀ r, .ret p r ∉ γ) :
    ∃ lx, γ.countP (Label.isTauOf p) ≤ μX p (X.invoke p lx i) + KY := by
  obtain ⟨l, hl⟩ := (X.seqComp Y cont).tauSteps_le_potential_invoke (seqPotential μX μY KY)
    (seqComp_potential X Y cont μX μY KY hμX hμY hK) hv hret
  exact ⟨l.1, hl⟩

end Impl

end Cslib.SharedMemory
