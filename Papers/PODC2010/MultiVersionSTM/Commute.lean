import Papers.PODC2010.MultiVersionSTM.Basic

/-!
# Frame and commutation lemmas for STM executions

Generic facts about the base-object semantics of `STM.run` (Section 3 of Perelman–Fan–Keidar,
PODC 2010), used in the proof of Theorem 2.

* **Traces.** `applyTrace m tr` is the memory `m` after the writes of the trace `tr`, and
  `TraceOK m tr` says that `tr` is consistent with `m` (every access reads the current value).
  The run of a program (`Prog.run_mem`, `Prog.run_traceOK`), of a step and of a schedule
  (`STM.run_mem`, `STM.run_traceOK`) produces a consistent trace, and its final memory is the
  initial memory updated along the trace.
* **Frame lemma** (`Prog.run_congr`, `STM.run_congr`): a run depends only on the private states
  of its threads and on the values of the base objects it accesses.
* **Commutation** (`STM.run_comm`): if two schedules `A` and `B` run by disjoint sets of threads
  only share base objects that neither of them changes, then running `B` then `A` gives the same
  steps (events and traces) for each part and the same final configuration as running `A` then
  `B`.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-! ### Traces -/

section Trace

variable {B M : Type}

/-- The memory `m` after the writes of the trace `tr`. -/
noncomputable def applyTrace (m : B → M) (tr : List (Access B M)) : B → M :=
  tr.foldl (fun m a => Function.update m a.b a.new) m

/-- The trace `tr` is consistent with the memory `m`: every access reads the current value. -/
def TraceOK : (B → M) → List (Access B M) → Prop
  | _, [] => True
  | m, a :: tr => a.old = m a.b ∧ TraceOK (Function.update m a.b a.new) tr

@[simp] lemma applyTrace_nil (m : B → M) : applyTrace m [] = m := rfl

@[simp] lemma applyTrace_cons (m : B → M) (a : Access B M) (tr : List (Access B M)) :
    applyTrace m (a :: tr) = applyTrace (Function.update m a.b a.new) tr := rfl

lemma applyTrace_append (m : B → M) (tr₁ tr₂ : List (Access B M)) :
    applyTrace m (tr₁ ++ tr₂) = applyTrace (applyTrace m tr₁) tr₂ := by
  simp [applyTrace, List.foldl_append]

@[simp] lemma traceOK_nil (m : B → M) : TraceOK m [] := trivial

@[simp] lemma traceOK_cons (m : B → M) (a : Access B M) (tr : List (Access B M)) :
    TraceOK m (a :: tr) ↔ a.old = m a.b ∧ TraceOK (Function.update m a.b a.new) tr := Iff.rfl

lemma traceOK_append (m : B → M) (tr₁ tr₂ : List (Access B M)) :
    TraceOK m (tr₁ ++ tr₂) ↔ TraceOK m tr₁ ∧ TraceOK (applyTrace m tr₁) tr₂ := by
  induction tr₁ generalizing m with
  | nil => simp
  | cons a tr ih => simp [ih, and_assoc]

/-- A base object not accessed by a trace keeps its value. -/
lemma applyTrace_of_not_mem {m : B → M} {tr : List (Access B M)} {b : B}
    (h : ∀ a ∈ tr, a.b ≠ b) : applyTrace m tr b = m b := by
  induction tr generalizing m with
  | nil => rfl
  | cons a tr ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    rw [applyTrace_cons, ih h.2, Function.update_of_ne h.1.symm]

/-- **Key fact.** If no access of a consistent trace changes the base object `b`, then `b` keeps
its value. -/
lemma applyTrace_of_unchanged {m : B → M} {tr : List (Access B M)} {b : B} (hok : TraceOK m tr)
    (h : ∀ a ∈ tr, a.b = b → a.old = a.new) : applyTrace m tr b = m b := by
  induction tr generalizing m with
  | nil => rfl
  | cons a tr ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hok₁, hok₂⟩ := hok
    rw [applyTrace_cons, ih hok₂ h.2]
    by_cases hb : a.b = b
    · subst hb; rw [Function.update_self, ← h.1 rfl, hok₁]
    · rw [Function.update_of_ne (Ne.symm hb)]

/-- The value of a base object after a trace depends on the initial memory only at that object,
and not at all if the trace writes it. -/
lemma applyTrace_congr {m₁ m₂ : B → M} {tr : List (Access B M)} {b : B}
    (h : m₁ b = m₂ b ∨ ∃ a ∈ tr, a.b = b) : applyTrace m₁ tr b = applyTrace m₂ tr b := by
  induction tr generalizing m₁ m₂ with
  | nil =>
    rcases h with h | ⟨a, ha, -⟩
    · exact h
    · simp at ha
  | cons a tr ih =>
    rw [applyTrace_cons, applyTrace_cons]
    apply ih
    by_cases hb : a.b = b
    · subst hb; left; simp
    · rw [Function.update_of_ne (Ne.symm hb), Function.update_of_ne (Ne.symm hb)]
      rcases h with h | ⟨a', ha', hab⟩
      · exact Or.inl h
      · rcases List.mem_cons.1 ha' with rfl | ha'
        · exact absurd hab hb
        · exact Or.inr ⟨a', ha', hab⟩

end Trace

/-! ### Programs -/

namespace Prog

variable {B M α : Type}

/-- The final memory of a program run is the initial memory updated along its trace. -/
lemma run_mem (p : Prog B M α) (m : B → M) : (p.run m).2.1 = applyTrace m (p.run m).2.2 := by
  induction p generalizing m with
  | ret a => rfl
  | access b f k ih => exact ih (m b) _

/-- The trace of a program run is consistent with the initial memory. -/
lemma run_traceOK (p : Prog B M α) (m : B → M) : TraceOK m (p.run m).2.2 := by
  induction p generalizing m with
  | ret a => trivial
  | access b f k ih => exact ⟨rfl, ih (m b) _⟩

/-- **Frame lemma for programs.** Running a program from a memory that agrees with `m₁` on every
base object accessed by the run from `m₁` gives the same result and the same trace. -/
lemma run_congr (p : Prog B M α) {m₁ m₂ : B → M}
    (h : ∀ a ∈ (p.run m₁).2.2, m₂ a.b = m₁ a.b) :
    (p.run m₂).1 = (p.run m₁).1 ∧ (p.run m₂).2.2 = (p.run m₁).2.2 := by
  induction p generalizing m₁ m₂ with
  | ret a => exact ⟨rfl, rfl⟩
  | access b f k ih =>
    simp only [run, List.mem_cons, forall_eq_or_imp] at h ⊢
    obtain ⟨hb, h⟩ := h
    rw [hb]
    obtain ⟨h1, h2⟩ := ih (m₁ b) (m₁ := Function.update m₁ b (f (m₁ b)))
      (m₂ := Function.update m₂ b (f (m₁ b))) (by
        intro a ha
        by_cases hab : a.b = b
        · rw [hab, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hab, Function.update_of_ne hab]; exact h a ha)
    exact ⟨h1, by rw [h2]⟩

end Prog

/-! ### Steps and runs -/

/-- Configurations are equal if their memories and private states are. -/
lemma Config.ext' {X : STM Tx O P} {C C' : Config X} (h₁ : C.mem = C'.mem) (h₂ : C.loc = C'.loc) :
    C = C' := by
  cases C; cases C'; simp_all

namespace STM

variable (X : STM Tx O P)

/-- The concatenated base-step trace of a list of steps. -/
def traceOf (l : List (Event Tx O × X.Trace)) : X.Trace := l.flatMap Prod.snd

@[simp] lemma traceOf_nil : X.traceOf [] = [] := rfl

@[simp] lemma traceOf_cons (s : Event Tx O × X.Trace) (l : List (Event Tx O × X.Trace)) :
    X.traceOf (s :: l) = s.2 ++ X.traceOf l := rfl

lemma mem_traceOf {l : List (Event Tx O × X.Trace)} {a : Access X.B X.M} :
    a ∈ X.traceOf l ↔ ∃ s ∈ l, a ∈ s.2 := by
  simp [traceOf, List.mem_flatMap]

variable [TxSys Tx P]

lemma step_mem (C : Config X) (i : Inv Tx O) :
    (X.step C i).1.mem = applyTrace C.mem (X.step C i).2.2 :=
  Prog.run_mem _ _

lemma step_traceOK (C : Config X) (i : Inv Tx O) : TraceOK C.mem (X.step C i).2.2 :=
  Prog.run_traceOK _ _

lemma step_loc_of_ne (C : Config X) (i : Inv Tx O) {p : P} (hp : p ≠ thr i.tx) :
    (X.step C i).1.loc p = C.loc p := by
  simp [step, Function.update_of_ne hp]

/-- Frame lemma for one transactional step. -/
lemma step_congr {C₁ C₂ : Config X} (i : Inv Tx O) (hl : C₂.loc (thr i.tx) = C₁.loc (thr i.tx))
    (hm : ∀ a ∈ (X.step C₁ i).2.2, C₂.mem a.b = C₁.mem a.b) :
    (X.step C₂ i).2 = (X.step C₁ i).2 ∧
      (X.step C₂ i).1.loc (thr i.tx) = (X.step C₁ i).1.loc (thr i.tx) := by
  simp only [step] at hm ⊢
  rw [hl] at ⊢
  obtain ⟨h1, h2⟩ := Prog.run_congr _ hm
  simp [h1, h2]

/-- The final memory of a run is the initial memory updated along its trace. -/
lemma run_mem (C : Config X) (σ : List (Inv Tx O)) :
    (X.run C σ).1.mem = applyTrace C.mem (X.traceOf (X.run C σ).2) := by
  induction σ generalizing C with
  | nil => rfl
  | cons i τ ih =>
    rw [run_cons]
    simp only [traceOf_cons, applyTrace_append]
    rw [ih, step_mem]

/-- The trace of a run is consistent with the initial memory. -/
lemma run_traceOK (C : Config X) (σ : List (Inv Tx O)) :
    TraceOK C.mem (X.traceOf (X.run C σ).2) := by
  induction σ generalizing C with
  | nil => trivial
  | cons i τ ih =>
    rw [run_cons]
    simp only [traceOf_cons, traceOK_append]
    refine ⟨X.step_traceOK C i, ?_⟩
    rw [← step_mem]; exact ih _

/-- A thread that runs no step of `σ` keeps its private state. -/
lemma run_loc_of_not_mem (C : Config X) (σ : List (Inv Tx O)) {p : P}
    (hp : ∀ i ∈ σ, thr i.tx ≠ p) : (X.run C σ).1.loc p = C.loc p := by
  induction σ generalizing C with
  | nil => rfl
  | cons i τ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hp
    rw [run_cons, ih _ hp.2, step_loc_of_ne _ _ _ (Ne.symm hp.1)]

/-- The invocation of a step of a run belongs to the schedule. -/
lemma inv_mem_of_mem_run {C : Config X} {σ : List (Inv Tx O)} {s : Event Tx O × X.Trace}
    (hs : s ∈ (X.run C σ).2) : s.1.inv ∈ σ := by
  rw [← X.map_inv_run C σ]; exact List.mem_map_of_mem hs

/-- **Frame lemma for runs.** Running a schedule `σ` from configurations `C₁`, `C₂` that agree on
the private states of the threads of `σ` and on every base object accessed by the run from `C₁`
gives the same steps (events and traces), and the final private states agree wherever the initial
ones do. -/
lemma run_congr {C₁ C₂ : Config X} (σ : List (Inv Tx O))
    (hl : ∀ i ∈ σ, C₂.loc (thr i.tx) = C₁.loc (thr i.tx))
    (hm : ∀ a ∈ X.traceOf (X.run C₁ σ).2, C₂.mem a.b = C₁.mem a.b) :
    (X.run C₂ σ).2 = (X.run C₁ σ).2 ∧
      ∀ p, C₂.loc p = C₁.loc p → (X.run C₂ σ).1.loc p = (X.run C₁ σ).1.loc p := by
  induction σ generalizing C₁ C₂ with
  | nil => exact ⟨rfl, fun p hp => hp⟩
  | cons i τ ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rw [run_cons] at hm
    simp only [traceOf_cons, List.mem_append] at hm
    obtain ⟨hs1, hs2⟩ := X.step_congr i hl.1 (fun a ha => hm a (Or.inl ha))
    have hloc : ∀ p, C₂.loc p = C₁.loc p → (X.step C₂ i).1.loc p = (X.step C₁ i).1.loc p := by
      intro p hp
      by_cases hpi : p = thr i.tx
      · subst hpi; exact hs2
      · rw [step_loc_of_ne _ _ _ hpi, step_loc_of_ne _ _ _ hpi, hp]
    obtain ⟨ih1, ih2⟩ := ih (C₁ := (X.step C₁ i).1) (C₂ := (X.step C₂ i).1)
      (fun j hj => by
        by_cases hji : thr j.tx = thr i.tx
        · rw [hji]; exact hs2
        · rw [step_loc_of_ne _ _ _ hji, step_loc_of_ne _ _ _ hji]; exact hl.2 j hj)
      (fun a ha => by
        rw [step_mem, step_mem, hs1]
        exact applyTrace_congr (Or.inl (hm a (Or.inr ha))))
    refine ⟨?_, fun p hp => ?_⟩
    · rw [run_cons, run_cons, ih1, hs1]
    · rw [run_cons, run_cons]; exact ih2 p (hloc p hp)

/-- **Commutation.** Let `A` and `B` be schedules run by disjoint sets of threads, such that in
the run of `A ++ B` from `C`, any two base steps of the `A`-part and of the `B`-part that access a
common base object leave it unchanged. Then in the run of `B ++ A` from `C`, the `B`-part and the
`A`-part have the same steps (events with their traces) as in the run of `A ++ B`, and the final
configurations are equal. -/
theorem run_comm (C : Config X) (A B : List (Inv Tx O))
    (hthr : ∀ i ∈ A, ∀ j ∈ B, thr i.tx ≠ thr j.tx)
    (hacc : ∀ a ∈ X.traceOf (X.run C A).2, ∀ a' ∈ X.traceOf (X.run (X.run C A).1 B).2,
      a.b = a'.b → a.old = a.new ∧ a'.old = a'.new) :
    (X.run C B).2 = (X.run (X.run C A).1 B).2 ∧
    (X.run (X.run C B).1 A).2 = (X.run C A).2 ∧
    (X.run (X.run C B).1 A).1 = (X.run (X.run C A).1 B).1 := by
  set CA := (X.run C A).1 with hCA
  set CB := (X.run C B).1 with hCB
  set trA := X.traceOf (X.run C A).2 with htrA
  set trB := X.traceOf (X.run CA B).2 with htrB
  -- the private states of the threads of `B` are not changed by `A`, and conversely
  have hlocA : ∀ p, (∀ i ∈ A, thr i.tx ≠ p) → CA.loc p = C.loc p :=
    fun p hp => X.run_loc_of_not_mem C A hp
  have hlocB : ∀ p, (∀ j ∈ B, thr j.tx ≠ p) → CB.loc p = C.loc p :=
    fun p hp => X.run_loc_of_not_mem C B hp
  have hokA : TraceOK C.mem trA := X.run_traceOK C A
  have hmemA : CA.mem = applyTrace C.mem trA := X.run_mem C A
  -- the `B`-part runs from `C` as from `CA`
  obtain ⟨hB1, hB2⟩ := X.run_congr (C₁ := CA) (C₂ := C) B
    (fun j hj => (hlocA _ (fun i hi => hthr i hi j hj)).symm)
    (fun a' ha' => by
      rw [hmemA, applyTrace_of_unchanged hokA (fun a ha hab => (hacc a ha a' ha' hab).1)])
  have htrB' : X.traceOf (X.run C B).2 = trB := by rw [hB1]
  have hokB : TraceOK C.mem trB := htrB' ▸ X.run_traceOK C B
  have hmemB : CB.mem = applyTrace C.mem trB := by rw [hCB, run_mem, htrB']
  -- the `A`-part runs from `CB` as from `C`
  obtain ⟨hA1, hA2⟩ := X.run_congr (C₁ := C) (C₂ := CB) A
    (fun i hi => hlocB _ (fun j hj => (hthr i hi j hj).symm))
    (fun a ha => by
      rw [hmemB, applyTrace_of_unchanged hokB (fun a' ha' hab => (hacc a ha a' ha' hab.symm).2)])
  refine ⟨hB1, hA1, Config.ext' ?_ ?_⟩
  · -- memories
    have hokA' : TraceOK CB.mem trA := by
      have := X.run_traceOK CB A; rwa [hA1] at this
    have hokB' : TraceOK CA.mem trB := X.run_traceOK CA B
    rw [X.run_mem CB A, X.run_mem CA B, hA1]
    change applyTrace CB.mem trA = applyTrace CA.mem trB
    funext b
    by_cases hbA : ∃ a ∈ trA, a.b = b
    · by_cases hbB : ∃ a' ∈ trB, a'.b = b
      · obtain ⟨a, ha, rfl⟩ := hbA
        obtain ⟨a', ha', hab⟩ := hbB
        rw [applyTrace_of_unchanged hokA'
            (fun a₁ ha₁ hab₁ => (hacc a₁ ha₁ a' ha' (hab₁.trans hab.symm)).1),
          applyTrace_of_unchanged hokB' (fun a₁ ha₁ hab₁ => (hacc a ha a₁ ha₁ hab₁.symm).2),
          hmemB, hmemA,
          applyTrace_of_unchanged hokB (fun a₁ ha₁ hab₁ => (hacc a ha a₁ ha₁ hab₁.symm).2),
          applyTrace_of_unchanged hokA
            (fun a₁ ha₁ hab₁ => (hacc a₁ ha₁ a' ha' (hab₁.trans hab.symm)).1)]
      · simp only [not_exists, not_and] at hbB
        rw [applyTrace_of_not_mem hbB, hmemA, hmemB]
        exact applyTrace_congr (Or.inr hbA)
    · simp only [not_exists, not_and] at hbA
      rw [applyTrace_of_not_mem hbA, hmemB]
      exact applyTrace_congr (Or.inl (by rw [hmemA, applyTrace_of_not_mem hbA]))
  · -- private states
    funext p
    by_cases hpA : ∃ i ∈ A, thr i.tx = p
    · obtain ⟨i, hi, rfl⟩ := hpA
      have hnB : ∀ j ∈ B, thr j.tx ≠ thr i.tx := fun j hj => (hthr i hi j hj).symm
      rw [hA2 _ (hlocB _ hnB), X.run_loc_of_not_mem CA B hnB]
    · simp only [not_exists, not_and] at hpA
      rw [X.run_loc_of_not_mem CB A hpA, hB2 _ (hlocA _ hpA).symm]

end STM

end Podc.MultiVersionSTM
