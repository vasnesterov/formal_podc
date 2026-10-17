import Cslib.Computability.Distributed.SharedMemory.Recoverable
import Podc.SharedMemory.ObjClasses

/-!
# Algorithms in the crash-recovery model: object families, access counts and correctness tools

Extensions of CSLib's crash-recovery shared-memory model `Cslib.SharedMemory.Recoverable`
(which also serves as the crash-stop model, through `WFConsensus` = consensus on crash-free
executions), shared by the consensus-number papers built on it.

## Objects

* `withRW R S` — the objects of an algorithm that uses read/write objects `R j` (`j : ιR`; in
  consensus-number statements `∀ j, (R j).RWLike`, see `ObjSpec.RWLike`) and objects of one type
  `S` (indexed by `ιS`).

## Counting accesses

* `objOf C p` — the object process `p` is poised to access in `C`;
* `accCount C α p i` — the number of operations `p` applies to object `i` along `α` from `C`
  (`accCount_append`, `accCount_single`).

## Correctness tools

* `Cfg.Out.run`, `Dec.exists_out`: outputs persist along executions without crashes of the
  deciding process;
* `inv_run_crashFree`: invariants preserved by steps hold along crash-free executions;
* `pre_crashFree_iff`: an infinite execution is crash-free iff none of its events is a crash;
* `prog_of_rank`: progress — and thus (recoverable) wait-freedom — from a ranking of local
  states that decreases at every access;
* `wfConsensus_of_inv`: wait-free consensus from an invariant (all outputs are the input of one
  process) and a ranking function.
-/

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Recoverable.lean

namespace Cslib.SharedMemory.Recoverable

/-- The objects of an algorithm that uses read/write objects `R j` (`j : ιR`) and objects of type
`S` (indexed by `ιS`). -/
abbrev withRW {ιR ιS : Type} (R : ιR → ObjSpec) (S : ObjSpec) : ιR ⊕ ιS → ObjSpec :=
  Sum.elim R (fun _ => S)

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-! ## Counting accesses -/

/-- The object process `p` is poised to access in `C` (`none` if `p` is in an output state). -/
def objOf (C : Cfg A) (p : Fin n) : Option ι :=
  match A.act (C.loc p) with
  | .access i _ _ => some i
  | .out _ => none

/-- Number of operations applied by process `p` to object `i` in the execution `α` from `C`. -/
def accCount : Cfg A → List (Ev n) → Fin n → ι → ℕ
  | _, [], _, _ => 0
  | C, e :: α, p, i =>
    (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i

/-- No accesses along the empty execution. -/
@[simp] lemma accCount_nil (C : Cfg A) (p : Fin n) (i : ι) : accCount C [] p i = 0 := rfl

/-- Unfolding `accCount` at the first event. -/
lemma accCount_cons (C : Cfg A) (e : Ev n) (α : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (e :: α) p i =
      (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i := rfl

/-- Access counts are additive along concatenated executions. -/
lemma accCount_append (C : Cfg A) (α β : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (α ++ β) p i = accCount C α p i + accCount (run C α) β p i := by
  induction α generalizing C with
  | nil => simp
  | cons e α ih => simp only [List.cons_append, accCount_cons, ih, run_cons]; omega

/-- The access count of a single step. -/
lemma accCount_single (C : Cfg A) (p q : Fin n) (i : ι) :
    accCount C [.step p] q i = if q = p ∧ objOf C p = some i then 1 else 0 := by
  rw [accCount_cons, accCount_nil, Nat.add_zero]
  by_cases h : q = p
  · subst h; simp
  · have : (Ev.step p : Ev n) ≠ .step q := by simpa [eq_comm] using h
    simp [this, h]

/-! ## Persistence of outputs and invariants -/

/-- An output state persists along every execution in which its process does not crash. -/
lemma Cfg.Out.run {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) {β : List (Ev n)}
    (hβ : Ev.crash p ∉ β) : (run C β).Out p v := by
  induction β generalizing C with
  | nil => exact h
  | cons e β ih =>
    rw [run_cons]
    refine ih ?_ (fun hm => hβ (List.mem_cons_of_mem _ hm))
    rcases e with q | q
    · by_cases hq : q = p
      · subst hq; simp only [Cfg.next, stepP_of_out C h]; exact h
      · unfold Cfg.Out; rw [next_loc_other C _ (by simpa [eq_comm] using hq)]; exact h
    · have hq : q ≠ p := by rintro rfl; exact hβ List.mem_cons_self
      unfold Cfg.Out; rw [next_loc_other C _ (by simpa [eq_comm] using hq)]; exact h

/-- A value decided in a crash-free execution is output at its end. -/
lemma Dec.exists_out {C : Cfg A} {α : List (Ev n)} {v : Bool} (h : Dec C α v)
    (hα : CrashFree α) : ∃ p, (run C α).Out p v := by
  obtain ⟨m, -, p, hp⟩ := h
  refine ⟨p, ?_⟩
  rw [← List.take_append_drop m α, run_append]
  exact hp.run (fun hm => hα p (List.mem_of_mem_drop hm))

/-- An invariant of configurations preserved by all steps holds along crash-free executions. -/
lemma inv_run_crashFree (Inv : Cfg A → Prop) (hstep : ∀ C p, Inv C → Inv (C.stepP p)) :
    ∀ (α : List (Ev n)) (C : Cfg A), Inv C → CrashFree α → Inv (run C α) := by
  intro α
  induction α with
  | nil => intro C h _; simpa using h
  | cons e α ih =>
    intro C hC hα
    rw [run_cons]
    apply ih _ _ (fun q hq => hα q (by simp [hq]))
    rcases e with q | q
    · exact hstep C q hC
    · exact absurd (by simp) (hα q)

/-! ## Progress -/

/-- All prefixes of an infinite execution are crash-free iff none of its events is a crash. -/
lemma pre_crashFree_iff (e : ℕ → Ev n) :
    (∀ t, CrashFree (pre e t)) ↔ ∀ t, ∀ p, e t ≠ .crash p := by
  constructor
  · intro h t p hp
    apply h (t + 1) p
    simp only [pre, List.mem_map, List.mem_range]
    exact ⟨t, by omega, hp⟩
  · intro h t p hp
    simp only [pre, List.mem_map, List.mem_range] at hp
    obtain ⟨t', -, ht'⟩ := hp
    exact h t' p ht'

/-- **Progress from a ranking function**: if every access strictly decreases a rank of the local
state, a process that takes infinitely many steps and does not crash after time `N` is in an
output state at some time `≥ N` (in any infinite execution from any configuration). This is the
progress condition of `Solves`, for any set of admissible executions. -/
theorem prog_of_rank (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l)
    (C : Cfg A) (e : ℕ → Ev n) (p : Fin n) (N : ℕ) (hinf : ∀ M, ∃ t ≥ M, e t = .step p)
    (hN : ∀ t ≥ N, e t ≠ .crash p) : ∃ t ≥ N, ∃ v, (run C (pre e t)).Out p v := by
  set Cf : ℕ → Cfg A := fun t => run C (pre e t) with hCf
  have hsucc : ∀ t, Cf (t + 1) = (Cf t).next (e t) := by
    intro t; simp [hCf, pre_succ, run_concat]
  by_contra hno
  push Not at hno
  -- the rank of `p` along the execution
  set r : ℕ → ℕ := fun t => rank ((Cf t).loc p) with hr
  have hstepP : ∀ t ≥ N, rank (((Cf t).stepP p).loc p) < r t := by
    intro t ht
    rcases hact : A.act ((Cf t).loc p) with ⟨i, o, κ⟩ | v
    · rw [stepP_of_access _ hact]
      simpa [hr] using hrank _ i o κ _ hact
    · exact absurd hact (hno t ht v)
  have hle : ∀ t ≥ N, r (t + 1) ≤ r t := by
    intro t ht
    simp only [hr, hsucc]
    rcases he : e t with q | q
    · by_cases hq : q = p
      · subst hq; exact (hstepP t ht).le
      · rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
    · have hq : q ≠ p := by rintro rfl; exact hN t ht he
      rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
  have hmono : ∀ t ≥ N, ∀ d, r (t + d) ≤ r t := by
    intro t ht d
    induction d with
    | zero => simp
    | succ d ih => exact (hle (t + d) (by omega)).trans ih
  have key : ∀ j, ∃ t ≥ N, r t + j ≤ r N := by
    intro j
    induction j with
    | zero => exact ⟨N, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨t, ht, hj⟩ := ih
      obtain ⟨t', ht', he⟩ := hinf t
      refine ⟨t' + 1, by omega, ?_⟩
      have h1 : r (t' + 1) < r t' := by
        simp only [hr, hsucc, he, Cfg.next]; exact hstepP t' (by omega)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht'
      have h2 := hmono t ht d
      omega
  obtain ⟨t, -, ht⟩ := key (r N + 1)
  omega

/-! ## Wait-free consensus from an invariant -/

/-- **Wait-free consensus from an invariant.** If an invariant of the configurations reached from
the initial configuration with inputs `x` implies that all output values are the input of a
single process, and a rank strictly decreases at each access, the algorithm solves wait-free
consensus. -/
theorem wfConsensus_of_inv (Inv : (Fin n → Bool) → Cfg A → Prop)
    (hinit : ∀ x, Inv x (initCfg A x))
    (hstep : ∀ x C p, Inv x C → Inv x (C.stepP p))
    (hout : ∀ x C, Inv x C → ∃ q, ∀ p w, C.Out p w → w = x q)
    (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l) :
    WFConsensus A := by
  have reach : ∀ x (α : List (Ev n)), CrashFree α → Inv x (run (initCfg A x) α) :=
    fun x α hα => inv_run_crashFree (Inv x) (hstep x) α _ (hinit x) hα
  refine ⟨?_, ?_, ?_⟩
  · intro x γ hγ v w hv hw
    obtain ⟨p, hp⟩ := hv.exists_out hγ
    obtain ⟨p', hp'⟩ := hw.exists_out hγ
    obtain ⟨q, hq⟩ := hout x _ (reach x γ hγ)
    rw [hq p v hp, hq p' w hp']
  · intro x γ hγ v hv
    obtain ⟨p, hp⟩ := hv.exists_out hγ
    obtain ⟨q, hq⟩ := hout x _ (reach x γ hγ)
    exact ⟨q, (hq p v hp).symm⟩
  · intro x e p N _ hinf hN
    exact prog_of_rank rank hrank _ e p N hinf hN

end Cslib.SharedMemory.Recoverable
