import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.Task
import Podc.Computability.Distributed.SharedMemory.MObstructionFree

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Splice.lean

/-!
# Splicing and restarting executions

Two tools for covering-style lower bounds in `Cslib.SharedMemory`:

* **Hidden fragments.** If no execution of the processes of `Q` from `D` reaches a configuration
  in which a process of `Q` covers a base object outside `R`, and every primitive is read-only or
  a blind write, then executions of `Q` from `D` leave the objects outside `R` unchanged
  (`Impl.runFrom_mem_eq_of_not_covers`). Together with `Impl.blockWrite_agreeOn`, this lets one
  splice such an execution into an execution in which `R` is overwritten by a block write right
  after `D`.
* **Restarting** an implementation from a configuration with fewer allowed invocations: every
  step of the restricted implementation is a step of the original one (`Impl.step_of_allowed_imp`,
  `Impl.runFrom_of_allowed_imp`), so its executions are execution fragments of the original one,
  and `m`-obstruction-freedom of the original implementation makes the restricted one wait-free
  when at most `m` processes may invoke operations (`Impl.waitFree_of_restrict`).

## Main results

* `Impl.runFrom_mem_eq_of_not_covers`
* `Impl.step_of_allowed_imp`, `Impl.runFrom_of_allowed_imp`
* `Impl.restrict`, `Impl.restrict_run`, `Impl.restrict_proc_mem`, `Impl.waitFree_of_restrict`
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

namespace Impl

/-! ### Hidden fragments -/

/-- **Fragments that do not write outside `R`.** Suppose every primitive is read-only or a blind
write, and no execution of processes of `Q` from `D` reaches a configuration in which a process of
`Q` covers an object outside `R`. Then every execution of processes of `Q` from `D` leaves the
objects outside `R` unchanged. -/
theorem runFrom_mem_eq_of_not_covers {I : Impl A B P L}
    (hB : ∀ i (o : (B i).Op), (B i).ReadOnly o ∨ (B i).Overwrites o)
    {Q : Set P} {R : Set ι} {D : Config A B P L}
    (h : ∀ δ D' q i, (∀ ℓ ∈ δ, ℓ.proc ∈ Q) → I.runFrom D δ = some D' → q ∈ Q → i ∉ R →
      ¬ I.Covers D' q i) :
    ∀ {γ : List (Label P A)} {D' : Config A B P L}, (∀ ℓ ∈ γ, ℓ.proc ∈ Q) →
      I.runFrom D γ = some D' → ∀ i ∉ R, D'.mem i = D.mem i := by
  intro γ
  induction γ using List.reverseRecOn with
  | nil => intro D' _ hrun i _; simp only [runFrom_nil, Option.some.injEq] at hrun; rw [hrun]
  | append_singleton γ ℓ ih =>
    intro D' hγ hrun i hi
    obtain ⟨D₀, h0, h1⟩ := I.runFrom_eq_some_of_append hrun
    have hγ0 : ∀ ℓ' ∈ γ, ℓ'.proc ∈ Q := fun ℓ' hℓ' => hγ ℓ' (by simp [hℓ'])
    rw [← ih hγ0 h0 i hi]
    rw [runFrom_singleton] at h1
    cases ℓ with
    | inv p o => rw [(step_inv h1).2.2.2.2]
    | ret p r => rw [(step_ret h1).2.2.1]
    | tau p =>
      obtain ⟨hp, -, j, o, k, hact, hmem, -⟩ := step_tau h1
      rw [hmem]
      by_cases hij : i = j
      · subst hij
        rcases hB i o with hro | hov
        · simp [hro (D₀.mem i)]
        · exact absurd ⟨hp, o, k, hact, hov⟩
            (h γ D₀ p i hγ0 h0 (hγ (.tau p) (by simp)) hi)
      · simp [Function.update_of_ne hij]

/-! ### Restricting the allowed invocations -/

/-- If `J` runs the same programs as `I` and allows fewer invocations, every step of `J` is a step
of `I`. -/
lemma step_of_allowed_imp {I J : Impl A B P L} (hinv : J.invoke = I.invoke) (hact : J.act = I.act)
    (hall : ∀ p o, J.allowed p o → I.allowed p o) {C C' : Config A B P L} {ℓ : Label P A}
    (h : J.step C ℓ = some C') : I.step C ℓ = some C' := by
  classical
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv h
    have : I.step C (.inv p o) = some ⟨Function.update C.loc p (I.invoke p (C.loc p) o),
        Function.update C.pend p (some o), C.mem⟩ := by
      simp [step, h0, hall p o h1]
    rw [this, ← hinv]
    congr 1
    cases C'; simp_all
  | tau p => simpa [step, hact] using h
  | ret p r => simpa [step, hact] using h

/-- If `J` runs the same programs as `I` and allows fewer invocations, every execution fragment
of `J` is an execution fragment of `I`. -/
lemma runFrom_of_allowed_imp {I J : Impl A B P L} (hinv : J.invoke = I.invoke)
    (hact : J.act = I.act) (hall : ∀ p o, J.allowed p o → I.allowed p o) :
    ∀ {β : List (Label P A)} {C C' : Config A B P L}, J.runFrom C β = some C' →
      I.runFrom C β = some C' := by
  intro β
  induction β with
  | nil => intro C C' h; exact h
  | cons ℓ β ih =>
    intro C C' h
    simp only [runFrom_cons] at h ⊢
    cases hs : J.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [step_of_allowed_imp hinv hact hall hs, Option.bind_some]
      exact ih h

/-- `I` restarted from the configuration `C`, where only the invocations satisfying `al` are
allowed. -/
def restrict (I : Impl A B P L) (C : Config A B P L) (al : P → A.Op → Prop) : Impl A B P L where
  memInit := C.mem
  locInit := C.loc
  invoke := I.invoke
  act := I.act
  allowed := al

section Restrict

variable {I : Impl A B P L} {C : Config A B P L} {al : P → A.Op → Prop}

/-- In a configuration reached by the restarted implementation, only processes that are allowed
some invocation are pending. -/
lemma restrict_pend {Q : Set P} (hal : ∀ p o, al p o → p ∈ Q) {β : List (Label P A)}
    {X : Config A B P L} (h : (I.restrict C al).run β = some X) {p : P} (hp : X.pend p ≠ none) :
    p ∈ Q := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
  have h1 := (I.restrict C al).run_pend h ho
  have h2 : o ∈ opsOf β p := List.mem_of_getLast? h1
  exact hal p o ((I.restrict C al).allowed_of_mem_opsOf ⟨X, h⟩ h2)

/-- Every label of a step of the restarted implementation (from a reachable configuration) belongs
to a process that is allowed some invocation. -/
lemma restrict_step_proc {Q : Set P} (hal : ∀ p o, al p o → p ∈ Q) {β : List (Label P A)}
    {X X' : Config A B P L} (h : (I.restrict C al).run β = some X) {ℓ : Label P A}
    (hs : (I.restrict C al).step X ℓ = some X') : ℓ.proc ∈ Q := by
  cases ℓ with
  | inv p o => exact hal p o (step_inv hs).2.1
  | tau p => exact restrict_pend hal h (step_tau hs).1
  | ret p r => exact restrict_pend hal h (step_ret hs).1

/-- Every label of an execution of the restarted implementation belongs to a process that is
allowed some invocation. -/
lemma restrict_proc_mem {Q : Set P} (hal : ∀ p o, al p o → p ∈ Q) {β : List (Label P A)}
    (h : (I.restrict C al).Valid β) : ∀ ℓ ∈ β, ℓ.proc ∈ Q := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β ℓ ih =>
    obtain ⟨X', hX'⟩ := h
    rw [run, runFrom_append] at hX'
    cases hβ : (I.restrict C al).runFrom (I.restrict C al).initCfg β with
    | none => simp [hβ] at hX'
    | some X =>
      simp only [hβ, Option.bind_some, runFrom_singleton] at hX'
      intro ℓ' hℓ'
      rcases List.mem_append.1 hℓ' with hℓ' | hℓ'
      · exact ih ⟨X, hβ⟩ ℓ' hℓ'
      · simp only [List.mem_singleton] at hℓ'; subst hℓ'
        exact restrict_step_proc hal hβ hX'

/-- **Executions of the restarted implementation are fragments of `I` from `C`.** If the processes
allowed to invoke are idle in `C` and every allowed invocation is allowed in `I`, then every
execution of `I.restrict C al` is an execution fragment of `I` from `C`, ending in a configuration
that agrees on these processes. -/
theorem restrict_run {Q : Set P} (hal : ∀ p o, al p o → p ∈ Q ∧ I.allowed p o)
    (hidle : ∀ q ∈ Q, C.pend q = none) {β : List (Label P A)} {X : Config A B P L}
    (h : (I.restrict C al).run β = some X) :
    ∃ Y, I.runFrom C β = some Y ∧ AgreeOn Q X Y := by
  have hagree : AgreeOn Q (I.restrict C al).initCfg C :=
    ⟨rfl, fun _ _ => rfl, fun q hq => (hidle q hq).symm⟩
  have hβ := restrict_proc_mem (fun p o h => (hal p o h).1) ⟨X, h⟩
  have h' : I.runFrom (I.restrict C al).initCfg β = some X :=
    runFrom_of_allowed_imp (I := I) (J := I.restrict C al) rfl rfl (fun p o h => (hal p o h).2) h
  exact runFrom_agreeOn hagree hβ h'

/-- **Restarting preserves progress.** If `I` is `m`-obstruction-free on all executions, `C` is
reachable, and at most `m` processes (all idle in `C`) may invoke operations in the restarted
implementation, then the restarted implementation is wait-free. -/
theorem waitFree_of_restrict {m : ℕ} (hof : I.MObstructionFreeOn m (fun _ => True))
    {α : List (Label P A)} (hα : I.run α = some C) {Q : Set P} (hQ : Q.encard ≤ m)
    (hal : ∀ p o, al p o → p ∈ Q ∧ I.allowed p o) (hidle : ∀ q ∈ Q, C.pend q = none) :
    (I.restrict C al).WaitFree := by
  intro e p n hpend
  have halQ : ∀ p o, al p o → p ∈ Q := fun p o h => (hal p o h).1
  have hrunY : ∀ t, ∃ Y, I.run (α ++ e.pre t) = some Y ∧ AgreeOn Q (e.cfg t) Y := by
    intro t
    obtain ⟨Y, hY, hag⟩ := restrict_run hal hidle (e.run_pre t)
    exact ⟨Y, by rw [run_append_of_eq I hα, hY], hag⟩
  obtain ⟨e', hlbl, hcfg⟩ := I.exists_infExec_of_chain (fun t => α ++ e.pre t)
    (fun t => by rw [e.pre_succ, ← List.append_assoc]; exact List.prefix_append _ _)
    (fun t => by simp [InfExec.pre])
    (fun t => by obtain ⟨Y, hY, -⟩ := hrunY t; exact ⟨Y, hY⟩)
  have hlen : ∀ t, (α ++ e.pre t).length = α.length + t := fun t => by simp [InfExec.pre]
  -- labels of `e'` after `α` are those of `e`
  have hlbl' : ∀ t, e'.lbl (α.length + t) = e.lbl t := by
    intro t
    rw [hlbl (t + 1) (α.length + t) (by rw [hlen]; omega)]
    rw [List.getElem_append_right (by omega)]
    simp only [InfExec.pre, Nat.add_sub_cancel_left, List.getElem_map, List.getElem_range]
  have hcfg' : ∀ t, AgreeOn Q (e.cfg t) (e'.cfg (α.length + t)) := by
    intro t
    obtain ⟨Y, hY, hag⟩ := hrunY t
    have := hcfg t (α.length + t) (by rw [hlen])
    rw [List.take_of_length_le (by rw [hlen]), hY, Option.some.injEq] at this
    rwa [← this]
  -- labels of `e` are by processes of `Q`
  have hproc : ∀ t, (e.lbl t).proc ∈ Q := fun t =>
    restrict_step_proc halQ (e.run_pre t) (e.step_eq t)
  have hinf : e'.infSteppers ⊆ Q := by
    intro q hq
    obtain ⟨t, ht, hq⟩ := hq α.length
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [hlbl'] at hq
    exact hq ▸ hproc u
  have hpQ : p ∈ Q := restrict_pend halQ (e.run_pre n) (hpend n le_rfl)
  obtain ⟨N, hN⟩ := hof e' (fun _ => trivial) ((Set.encard_le_encard hinf).trans hQ) p
    (α.length + n) (fun t ht => by
      obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right _ _) ht)
      rw [← (hcfg' u).pend p hpQ]
      exact hpend u (by omega))
  refine ⟨N, fun t ht => ?_⟩
  rw [← hlbl']
  exact hN _ (by omega)

end Restrict

end Impl

end Cslib.SharedMemory
