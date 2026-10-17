import Cslib.Computability.Distributed.SharedMemory.Model
import Podc.SharedMemory.History

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Model.lean

/-!
# Step and run API for `Impl`

Additions to CSLib's `Model.lean`:

* forward step equations `Impl.step_inv_eq_some`, `step_tau_eq_some`, `step_ret_eq_some` (CSLib only
  has the inversion lemmas `step_inv`/`step_tau`/`step_ret`);
* `Impl.run_concat`, the induction principle `Impl.run_induction` over executions and
  `Impl.invariant_of_run` (invariants of reachable configurations), `Impl.Reachable.step`;
* `Impl.pend_none_of_opsOf_nil`, `Impl.run_pend_curOp` (a pending operation is the current
  instance of its process, invoked and not completed);
* `Impl.exists_linFun_of_run`, `Impl.linearizable_of_run` — choosing a linearization function
  from an invariant of the finite executions.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] {I : Impl A B P L}

/-! ### Forward step equations -/

lemma step_inv_eq_some {C : Config A B P L} {p : P} {o : A.Op} (h : C.pend p = none)
    (ho : I.allowed p o) :
    I.step C (.inv p o) =
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) } := by
  classical
  simp [step, h, ho]

lemma step_tau_eq_some {C : Config A B P L} {p : P} (h : C.pend p ≠ none) {i : ι}
    {o : (B i).Op} {k : (B i).Resp → L} (hact : I.act p (C.loc p) = .access i o k) :
    I.step C (.tau p) =
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) } := by
  simp [step, h, hact]

lemma step_ret_eq_some {C : Config A B P L} {p : P} (h : C.pend p ≠ none) {r : A.Resp} {l : L}
    (hact : I.act p (C.loc p) = .ret r l) :
    I.step C (.ret p r) =
      some { C with pend := Function.update C.pend p none,
                    loc := Function.update C.loc p l } := by
  classical
  simp [step, h, hact]

/-! ### Runs -/

variable (I) in
lemma run_concat (α : List (Label P A)) (ℓ : Label P A) :
    I.run (α ++ [ℓ]) = (I.run α).bind (fun C => I.step C ℓ) := by
  simp only [run, runFrom_append]
  cases I.runFrom I.initCfg α <;> simp

/-- Induction principle for properties of executions and their final configurations. -/
lemma run_induction {Q : List (Label P A) → Config A B P L → Prop} (h0 : Q [] I.initCfg)
    (hs : ∀ α C ℓ C', I.run α = some C → Q α C → I.step C ℓ = some C' → Q (α ++ [ℓ]) C')
    {α : List (Label P A)} {C : Config A B P L} (h : I.run α = some C) : Q α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [run_nil, Option.some.injEq] at h; subst h; exact h0
  | append_singleton α ℓ ih =>
    rw [run_concat] at h
    cases hα : I.run α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some] at h
      exact hs α C₁ ℓ C hα (ih hα) h

/-- An invariant that holds initially and is preserved by all steps holds in every reachable
configuration. -/
lemma invariant_of_run {Inv : Config A B P L → Prop} (h0 : Inv I.initCfg)
    (hs : ∀ C ℓ C', Inv C → I.step C ℓ = some C' → Inv C') {α : List (Label P A)}
    {C : Config A B P L} (h : I.run α = some C) : Inv C :=
  run_induction (Q := fun _ C => Inv C) h0 (fun _ _ ℓ _ _ hC hs' => hs _ ℓ _ hC hs') h

lemma Reachable.step {C C' : Config A B P L} (hC : I.Reachable C) {ℓ : Label P A}
    (h : I.step C ℓ = some C') : I.Reachable C' := by
  obtain ⟨α, hα⟩ := hC
  exact ⟨α ++ [ℓ], by rw [run_concat, hα, Option.bind_some, h]⟩

/-! ### Pending operations -/

/-- A process that has not invoked anything has no pending operation. -/
lemma pend_none_of_opsOf_nil {α : List (Label P A)} {C : Config A B P L}
    (h : I.run α = some C) {p : P} (hp : opsOf α p = []) : C.pend p = none := by
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · rw [hp] at h2; simp at h2

/-- A pending operation is the current instance of its process: it has been invoked with this
operation and has not completed. -/
lemma run_pend_curOp {α : List (Label P A)} {C : Config A B P L} (h : I.run α = some C)
    {p : P} {o : A.Op} (hp : C.pend p = some o) :
    Invoked α (curOp α p) ∧ ¬ Completed α (curOp α p) ∧ opOf α (curOp α p) = some o := by
  have hlen : (opsOf α p).length = (respsOf α p).length + 1 := by
    rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
    · simp [h1] at hp
    · exact h2
  refine ⟨by simp [Invoked, hlen], by simp [Completed], ?_⟩
  have := I.run_pend h hp
  rw [List.getLast?_eq_getElem?] at this
  simpa [opOf, hlen] using this

/-! ### Linearization functions from invariants -/

/-- If every finite execution has a witness `L` satisfying `Inv α C L`, then the witnesses can be
chosen by a function of the execution. -/
lemma exists_linFun_of_run {X : Type} [Inhabited X]
    {Inv : List (Label P A) → Config A B P L → X → Prop}
    (h : ∀ α C, I.run α = some C → ∃ L, Inv α C L) :
    ∃ f : List (Label P A) → X, ∀ α C, I.run α = some C → Inv α C (f α) := by
  classical
  refine ⟨fun α => if hα : ∃ C, I.run α = some C then (h α _ hα.choose_spec).choose else default,
    fun α C hC => ?_⟩
  suffices ∀ C' (hC' : I.run α = some C'), Inv α C (h α C' hC').choose by
    have hα : ∃ C, I.run α = some C := ⟨C, hC⟩
    simp only [hα, ↓reduceDIte]
    exact this _ hα.choose_spec
  intro C' hC'
  obtain rfl : C' = C := Option.some.inj (hC'.symm.trans hC)
  exact (h α C' hC').choose_spec

/-- An implementation all of whose finite executions have a linearization is linearizable. -/
theorem linearizable_of_run
    (h : ∀ α C, I.run α = some C → ∃ L : List (OpId P × A.Op), IsLinearization α L) :
    I.Linearizable := by
  obtain ⟨f, hf⟩ := exists_linFun_of_run (Inv := fun α _ L => IsLinearization α L) h
  exact ⟨f, fun α ⟨C, hC⟩ => hf α C hC⟩

end Impl

end Cslib.SharedMemory
