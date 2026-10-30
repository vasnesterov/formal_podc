import Cslib.Computability.Distributed.SharedMemory.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/View.lean

/-!
# Local views, indistinguishability and effective operations

For an implementation `I : Impl A B P L` (CSLib's asynchronous shared-memory model), the *view* of
a process `p` in a finite execution `α` is the sequence of events of `p` in `α`, where every
internal step is recorded together with the response of the primitive it applied (`ProcObs`);
since processes are deterministic, this is everything `p` can know about `α` (paper: `α|p`).

Randomized algorithms are modelled by *families* `I : Θ → Impl A B P L` of implementations: the
parameter `θ : Θ` collects the random choices (e.g. one-time pads), which are fixed in the initial
local states. An execution is then a pair `(θ, α)`. Two executions are indistinguishable to `p`
(`Impl.IndistFam I p (θ, α) (θ', β)`) if `p` has the same initial local state and the same
observations in both.

* `Impl.EffectiveFam I θ α x r`: the operation instance `x` is `r`-*effective* after `α`
  (Attiya et al., PODC 2025, Definition 2): in every execution indistinguishable from `α` to the
  owner of `x`, and every extension of it in which `x` returns, `x` returns `r`.
* `Impl.UncompromisedFam I θ α x p`: the instance `x` (invoked with operation `o` in `α`) is
  *uncompromised* by `p` (Definition 3): some execution indistinguishable from `α` to `p` does not
  invoke `o` as instance `x`.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-- What a process observes at one of its events: the invoked operation, the response of the
primitive applied by an internal step (with the base object), or the returned response. -/
inductive ProcObs (A : ObjSpec) (B : ι → ObjSpec) where
  | inv (o : A.Op)
  | tau (i : ι) (r : (B i).Resp)
  | ret (r : A.Resp)

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- The observation of `p` at label `ℓ` taken from configuration `C` (`none` if `ℓ` is not an
event of `p`). -/
def obsStep (C : Config A B P L) (p : P) : Label P A → Option (ProcObs A B)
  | .inv q o => if q = p then some (.inv o) else none
  | .ret q r => if q = p then some (.ret r) else none
  | .tau q =>
    if q = p then
      match I.act q (C.loc q) with
      | .access i o _ => some (.tau i ((B i).δ (C.mem i) o).2)
      | .ret _ _ => none
    else none

/-- The observations of `p` along the labels `α` run from `C` (stopping at the first disabled
label). -/
noncomputable def obsFrom (p : P) : Config A B P L → List (Label P A) → List (ProcObs A B)
  | _, [] => []
  | C, ℓ :: α => (I.obsStep C p ℓ).toList ++
      match I.step C ℓ with
      | some C' => obsFrom p C' α
      | none => []

/-- The view of `p` in the execution `α`: its initial local state and its observations. -/
noncomputable def procView (p : P) (α : List (Label P A)) : L × List (ProcObs A B) :=
  (I.locInit p, I.obsFrom p I.initCfg α)

@[simp] lemma obsFrom_nil (p : P) (C : Config A B P L) : I.obsFrom p C [] = [] := rfl

lemma obsFrom_cons_of_step (p : P) {C C' : Config A B P L} {ℓ : Label P A}
    (h : I.step C ℓ = some C') (α : List (Label P A)) :
    I.obsFrom p C (ℓ :: α) = (I.obsStep C p ℓ).toList ++ I.obsFrom p C' α := by
  simp [obsFrom, h]

lemma obsFrom_append_of_runFrom (p : P) {C C' : Config A B P L} {α : List (Label P A)}
    (h : I.runFrom C α = some C') (β : List (Label P A)) :
    I.obsFrom p C (α ++ β) = I.obsFrom p C α ++ I.obsFrom p C' β := by
  induction α generalizing C with
  | nil => simp [runFrom] at h; subst h; simp
  | cons ℓ α ih =>
    simp only [runFrom] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some D =>
      rw [hs, Option.bind_some] at h
      rw [List.cons_append, obsFrom_cons_of_step I p hs, obsFrom_cons_of_step I p hs, ih h,
        List.append_assoc]

omit [DecidableEq ι] in
lemma obsStep_eq_none_of_proc_ne {p : P} (C : Config A B P L) {ℓ : Label P A}
    (h : ℓ.proc ≠ p) : I.obsStep C p ℓ = none := by
  cases ℓ <;> simp_all [obsStep, Label.proc]

/-- Replaying observations on a local state. -/
def replayObs (p : P) (l : L) : ProcObs A B → L
  | .inv o => I.invoke p l o
  | .tau i r => match I.act p l with
    | .access i' _ k => if h : i' = i then k (h ▸ r) else l
    | .ret _ _ => l
  | .ret _ => match I.act p l with
    | .access _ _ _ => l
    | .ret _ l' => l'

/-- Replaying a list of observations. -/
def replayView (p : P) (l : L) (obs : List (ProcObs A B)) : L := obs.foldl (I.replayObs p) l

lemma replay_obsStep {C C' : Config A B P L} {ℓ : Label P A} (h : I.step C ℓ = some C') (p : P) :
    (I.obsStep C p ℓ).toList.foldl (I.replayObs p) (C.loc p) = C'.loc p := by
  classical
  cases ℓ with
  | inv q o =>
    obtain ⟨-, -, -, hl, -⟩ := Impl.step_inv h
    by_cases hq : q = p
    · subst hq; simp [obsStep, replayObs, hl]
    · simp [obsStep, hq, hl, Function.update_of_ne (Ne.symm hq)]
  | ret q r =>
    obtain ⟨-, -, -, l, hact, hl⟩ := Impl.step_ret h
    by_cases hq : q = p
    · subst hq; simp [obsStep, replayObs, hl, hact]
    · simp [obsStep, hq, hl, Function.update_of_ne (Ne.symm hq)]
  | tau q =>
    obtain ⟨-, -, i, o, k, hact, -, hl⟩ := Impl.step_tau h
    by_cases hq : q = p
    · subst hq; simp [obsStep, replayObs, hl, hact]
    · simp [obsStep, hq, hl, Function.update_of_ne (Ne.symm hq)]

/-- The local state of `p` at the end of an execution is determined by its initial local state
and its observations. -/
lemma replay_obsFrom {C D : Config A B P L} {α : List (Label P A)} (h : I.runFrom C α = some D)
    (p : P) : I.replayView p (C.loc p) (I.obsFrom p C α) = D.loc p := by
  induction α generalizing C with
  | nil => simp [runFrom] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [runFrom] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C' =>
      rw [hs, Option.bind_some] at h
      rw [obsFrom_cons_of_step I p hs, replayView, List.foldl_append, replay_obsStep I hs p]
      exact ih h

/-- The invocations of `p` are read off its observations. -/
lemma opsOf_eq_obs {C D : Config A B P L} {α : List (Label P A)} (h : I.runFrom C α = some D)
    (p : P) : opsOf α p = (I.obsFrom p C α).filterMap
      (fun ob => match ob with | .inv o => some o | _ => none) := by
  induction α generalizing C with
  | nil => simp
  | cons ℓ α ih =>
    simp only [runFrom] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C' =>
      rw [hs, Option.bind_some] at h
      rw [obsFrom_cons_of_step I p hs, List.filterMap_append, ← ih h, opsOf_cons]
      congr 1
      cases ℓ with
      | inv q o => by_cases hq : q = p <;> simp [obsStep, hq]
      | ret q r => by_cases hq : q = p <;> simp [obsStep, hq]
      | tau q =>
        by_cases hq : q = p
        · subst hq; simp only [obsStep, if_true]; split <;> simp
        · simp [obsStep, hq]

/-- The responses of `p` are read off its observations. -/
lemma respsOf_eq_obs {C D : Config A B P L} {α : List (Label P A)} (h : I.runFrom C α = some D)
    (p : P) : respsOf α p = (I.obsFrom p C α).filterMap
      (fun ob => match ob with | .ret r => some r | _ => none) := by
  induction α generalizing C with
  | nil => simp
  | cons ℓ α ih =>
    simp only [runFrom] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C' =>
      rw [hs, Option.bind_some] at h
      rw [obsFrom_cons_of_step I p hs, List.filterMap_append, ← ih h, respsOf_cons]
      congr 1
      cases ℓ with
      | inv q o => by_cases hq : q = p <;> simp [obsStep, hq]
      | ret q r => by_cases hq : q = p <;> simp [obsStep, hq]
      | tau q =>
        by_cases hq : q = p
        · subst hq; simp only [obsStep, if_true]; split <;> simp
        · simp [obsStep, hq]

end Impl

section Family

variable {Θ : Type} [DecidableEq P] [DecidableEq ι]

namespace Impl

/-- Indistinguishability to `p` of executions of a family of implementations (paper: `α ∼_p β`):
same initial local state of `p` and the same observations. -/
def IndistFam (I : Θ → Impl A B P L) (p : P) (e e' : Θ × List (Label P A)) : Prop :=
  (I e.1).procView p e.2 = (I e'.1).procView p e'.2

lemma IndistFam.refl (I : Θ → Impl A B P L) (p : P) (e : Θ × List (Label P A)) :
    IndistFam I p e e := rfl

lemma IndistFam.symm {I : Θ → Impl A B P L} {p : P} {e e' : Θ × List (Label P A)}
    (h : IndistFam I p e e') : IndistFam I p e' e := Eq.symm h

lemma IndistFam.trans {I : Θ → Impl A B P L} {p : P} {e e' e'' : Θ × List (Label P A)}
    (h : IndistFam I p e e') (h' : IndistFam I p e' e'') : IndistFam I p e e'' := Eq.trans h h'

/-- Definition 2 of Attiya, Fernández Anta, Milani, Rapetti, Travers (PODC 2025): the operation
instance `x` (of process `x.1`) is `r`-effective after the finite execution `(θ, α)`: for every
execution `(θ', β)` indistinguishable from `(θ, α)` to `x.1`, `x` returns `r` in every extension
of `β` in which it returns. -/
def EffectiveFam (I : Θ → Impl A B P L) (θ : Θ) (α : List (Label P A)) (x : OpId P)
    (r : A.Resp) : Prop :=
  ∀ θ' β, (I θ').Valid β → IndistFam I x.1 (θ, α) (θ', β) →
    ∀ γ, (I θ').Valid (β ++ γ) → ∀ r', respOf (β ++ γ) x = some r' → r' = r

/-- Definition 3 (uncompromised operation): the instance `x`, invoked in `α` with operation `o`,
is uncompromised by `p` if some execution indistinguishable from `(θ, α)` to `p` does not invoke
`o` as instance `x` (either `x` is not invoked at all, or it is invoked with another operation,
e.g. a write with another input). -/
def UncompromisedFam (I : Θ → Impl A B P L) (θ : Θ) (α : List (Label P A)) (x : OpId P)
    (p : P) : Prop :=
  ∀ o, opOf α x = some o →
    ∃ θ' β, (I θ').Valid β ∧ IndistFam I p (θ, α) (θ', β) ∧ opOf β x ≠ some o

/-- Executions indistinguishable to `p` end with the same local state of `p` and give `p` the
same invocations and responses. -/
lemma IndistFam.loc_eq {I : Θ → Impl A B P L} {p : P} {θ θ' : Θ} {α β : List (Label P A)}
    {C D : Config A B P L} (hα : (I θ).run α = some C) (hβ : (I θ').run β = some D)
    (h : IndistFam I p (θ, α) (θ', β)) (hact : ∀ l, (I θ).act p l = (I θ').act p l)
    (hinv : ∀ l o, (I θ).invoke p l o = (I θ').invoke p l o) :
    C.loc p = D.loc p ∧ opsOf α p = opsOf β p ∧ respsOf α p = respsOf β p := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hr : (I θ).replayView p = (I θ').replayView p := by
    funext l obs
    unfold replayView
    congr 1
    funext l' ob
    cases ob <;> simp [replayObs, hact, hinv]
  refine ⟨?_, ?_, ?_⟩
  · rw [← (I θ).replay_obsFrom hα p, ← (I θ').replay_obsFrom hβ p]
    simp only [Impl.initCfg]
    simp only [procView] at h1 h2
    rw [h1, hr]; exact congrArg _ h2
  · rw [(I θ).opsOf_eq_obs hα p, (I θ').opsOf_eq_obs hβ p]
    simp only [procView] at h2; rw [h2]
  · rw [(I θ).respsOf_eq_obs hα p, (I θ').respsOf_eq_obs hβ p]
    simp only [procView] at h2; rw [h2]

end Impl

end Family

end Cslib.SharedMemory
