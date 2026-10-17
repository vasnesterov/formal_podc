import Podc.StrongLin.Basic

/-!
# Correctness and progress restricted to a class of executions

Objects with a *usage discipline* (one-shot objects, objects whose operations may only be invoked
by designated processes, objects that may be used only after some event) need correctness and
progress only on the executions that respect the discipline. For a set `E` of finite executions
(intended to be prefix-closed):

* `Impl.StrongLinOn E` — a linearization function on the executions of `E`, prefix-closed
  within `E`; `Impl.NStrongLinOn S E` — the same for a nondeterministic specification `S`;
* `Impl.LockFreeOn E`, `Impl.WaitFreeOn E` — lock-freedom / wait-freedom for the infinite
  executions all of whose finite prefixes are in `E`.

Each is implied by its unrestricted version, so impossibility results proved for the restricted
notions are stronger. `InfExec.lbls e t` is the list of the first `t` labels of `e`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

-- CSLib candidate (whole file)

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- The first `t` labels of an infinite execution. -/
def InfExec.lbls {I : Impl A B P L} (e : I.InfExec) (t : ℕ) : List (Label P A) :=
  (List.range t).map e.lbl

lemma InfExec.lbls_succ {I : Impl A B P L} (e : I.InfExec) (t : ℕ) :
    e.lbls (t + 1) = e.lbls t ++ [e.lbl t] := by
  simp [InfExec.lbls, List.range_succ]

lemma InfExec.run_lbls {I : Impl A B P L} (e : I.InfExec) (t : ℕ) :
    I.run (e.lbls t) = some (e.cfg t) := by
  induction t with
  | zero => simp [InfExec.lbls, e.cfg_zero]
  | succ t ih =>
    rw [InfExec.lbls_succ, run_append_of_eq I ih, runFrom_singleton, e.step_eq]

lemma InfExec.lbls_prefix {I : Impl A B P L} (e : I.InfExec) {t t' : ℕ} (h : t ≤ t') :
    e.lbls t <+: e.lbls t' := by
  induction t', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t' _ ih => rw [InfExec.lbls_succ]; exact ih.trans (List.prefix_append _ _)

lemma InfExec.length_lbls {I : Impl A B P L} (e : I.InfExec) (t : ℕ) : (e.lbls t).length = t := by
  simp [InfExec.lbls]

/-- Strong linearizability on the executions of `E`. -/
def StrongLinOn (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op),
    (∀ α, I.Valid α → E α → IsLinearization α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

/-- Strong linearizability with respect to a nondeterministic specification, on the executions
of `E`. -/
def NStrongLinOn (S : NSpec A.Op A.Resp) (E : List (Label P A) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → E α → IsNLinearization S α (h α)) ∧
    ∀ α β, I.Valid β → E β → α <+: β → h α <+: h β

/-- Lock-freedom for the infinite executions whose prefixes are all in `E`. -/
def LockFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.lbls t)) → (∀ N, ∃ m ≥ N, (e.lbl m).IsStep) →
    ∀ N, ∃ m ≥ N, ∃ p r, e.lbl m = .ret p r

/-- Wait-freedom for the infinite executions whose prefixes are all in `E`. -/
def WaitFreeOn (E : List (Label P A) → Prop) : Prop :=
  ∀ e : I.InfExec, (∀ t, E (e.lbls t)) → ∀ (p : P) (n : ℕ),
    (∀ m ≥ n, (e.cfg m).pend p ≠ none) → ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau p

variable {I}

lemma StronglyLinearizable.strongLinOn (h : I.StronglyLinearizable) (E : List (Label P A) → Prop) :
    I.StrongLinOn E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma NStronglyLinearizable.nStrongLinOn {S : NSpec A.Op A.Resp} (h : I.NStronglyLinearizable S)
    (E : List (Label P A) → Prop) : I.NStrongLinOn S E := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα _ => hf α hα, fun α β hβ _ hαβ => hp α β hβ hαβ⟩

lemma LockFree.lockFreeOn (h : I.LockFree) (E : List (Label P A) → Prop) : I.LockFreeOn E :=
  fun e _ hs => h e hs

lemma WaitFree.waitFreeOn (h : I.WaitFree) (E : List (Label P A) → Prop) : I.WaitFreeOn E :=
  fun e _ => h e

lemma StrongLinOn.mono {E E' : List (Label P A) → Prop} (h : I.StrongLinOn E)
    (hE : ∀ α, E' α → E α) : I.StrongLinOn E' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα h' => hf α hα (hE α h'), fun α β hβ h' hαβ => hp α β hβ (hE β h') hαβ⟩

lemma LockFreeOn.mono {E E' : List (Label P A) → Prop} (h : I.LockFreeOn E)
    (hE : ∀ α, E' α → E α) : I.LockFreeOn E' :=
  fun e he hs => h e (fun t => hE _ (he t)) hs

/-- A process that is idle at `m₁` and pending at `m₂ ≥ m₁` invoked in between. -/
lemma InfExec.exists_inv_between (e : I.InfExec) {p : P} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (h₁ : (e.cfg m₁).pend p = none) (h₂ : (e.cfg m₂).pend p ≠ none) :
    ∃ t, m₁ ≤ t ∧ t < m₂ ∧ ∃ o, e.lbl t = .inv p o := by
  induction m₂, h using Nat.le_induction with
  | base => exact absurd h₁ h₂
  | succ m hle ih =>
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h₂
    rcases step_pend_some (e.step_eq m) ho with h | h
    · obtain ⟨t, ht1, ht2, o', ho'⟩ := ih (by rw [h]; simp)
      exact ⟨t, ht1, by omega, o', ho'⟩
    · exact ⟨m, hle, by omega, o, h⟩

lemma InfExec.opsOf_lbls_mono (e : I.InfExec) (p : P) {t t' : ℕ} (h : t ≤ t') :
    (opsOf (e.lbls t) p).length ≤ (opsOf (e.lbls t') p).length := by
  obtain ⟨γ, hγ⟩ := e.lbls_prefix h
  rw [← hγ, opsOf_append, List.length_append]; omega

/-- For one-shot executions with finitely many processes, wait-freedom implies lock-freedom. -/
theorem WaitFreeOn.lockFreeOn [Fintype P] {E : List (Label P A) → Prop} (h : I.WaitFreeOn E)
    (hos : ∀ α, E α → ∀ q, (opsOf α q).length ≤ 1) : I.LockFreeOn E := by
  classical
  intro e hE hsteps N₀
  by_contra hret
  push Not at hret
  -- some process takes infinitely many steps
  obtain ⟨p, hp⟩ : ∃ p, ∀ N, ∃ m ≥ N, (e.lbl m).IsStep ∧ (e.lbl m).proc = p := by
    by_contra hno
    push Not at hno
    choose Nf hNf using hno
    obtain ⟨m, hm, hs⟩ := hsteps (Finset.univ.sup Nf)
    exact hNf _ m (le_trans (Finset.le_sup (Finset.mem_univ _)) hm) hs rfl
  -- hence infinitely many `tau p` (there are no responses after `N₀`)
  have htau : ∀ N, ∃ m ≥ N, e.lbl m = .tau p := by
    intro N
    obtain ⟨m, hm, hs, hpr⟩ := hp (max N N₀)
    refine ⟨m, le_of_max_le_left hm, ?_⟩
    cases hl : e.lbl m with
    | inv q o => rw [hl] at hs; exact hs.elim
    | ret q r => exact absurd hl (hret m (le_of_max_le_right hm) q r)
    | tau q => rw [hl] at hpr; simp only [Label.proc] at hpr; rw [hpr]
  obtain ⟨m₀, -, hm₀⟩ := htau 0
  have hpend₀ : (e.cfg m₀).pend p ≠ none := by
    have hs := e.step_eq m₀; rw [hm₀] at hs; exact (step_tau hs).1
  have hinv₀ : 1 ≤ (opsOf (e.lbls m₀) p).length := by
    rcases I.run_counts (e.run_lbls m₀) p with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hpend₀
    · omega
  -- `p` stays pending forever after `m₀`
  have hpend : ∀ m ≥ m₀, (e.cfg m).pend p ≠ none := by
    intro m hm hidle
    obtain ⟨m₂, hm₂, hm₂'⟩ := htau m
    have hpend₂ : (e.cfg m₂).pend p ≠ none := by
      have hs := e.step_eq m₂; rw [hm₂'] at hs; exact (step_tau hs).1
    obtain ⟨t, ht1, -, o, ho⟩ := e.exists_inv_between hm₂ hidle hpend₂
    have hle := hos _ (hE (t + 1)) p
    rw [InfExec.lbls_succ, opsOf_append, ho] at hle
    have hmono := e.opsOf_lbls_mono p (hm.trans ht1)
    simp only [opsOf_cons, opsOf_nil, Label.invOf_inv, ite_true, Option.toList_some,
      List.append_nil, List.length_append, List.length_singleton] at hle
    omega
  obtain ⟨N, hN⟩ := h e hE p m₀ hpend
  obtain ⟨m, hm, hm'⟩ := htau N
  exact hN m hm hm'

end Impl

end Cslib.SharedMemory
