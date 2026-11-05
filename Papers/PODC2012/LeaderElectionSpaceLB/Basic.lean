import Papers.PODC2012.LeaderElectionSpaceLB.Model

-- CSLib candidate: nondeterministic read/write shared memory + covering toolkit

/-!
# Basic facts about executions

Concatenation of executions, locality of steps, persistence of returning, the sees relation of a
concatenation, and the characterization of closed sets by the sees relation.
-/

namespace Podc.LeaderElectionSpaceLB

set_option linter.unusedSectionVars false

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg]

namespace Alg

variable (A : Alg P Reg V L)

@[simp] lemma run_nil (C : Config P Reg V L) : A.run C [] = C := rfl

@[simp] lemma run_cons (C : Config P Reg V L) (e : P × L) (es : List (P × L)) :
    A.run C (e :: es) = A.run (A.apply C e) es := rfl

lemma run_append (C : Config P Reg V L) (es fs : List (P × L)) :
    A.run C (es ++ fs) = A.run (A.run C es) fs := by
  simp [run, List.foldl_append]

@[simp] lemma valid_nil (C : Config P Reg V L) : A.Valid C [] := trivial

@[simp] lemma valid_cons (C : Config P Reg V L) (e : P × L) (es : List (P × L)) :
    A.Valid C (e :: es) ↔ A.Enabled C e ∧ A.Valid (A.apply C e) es := Iff.rfl

lemma valid_append (C : Config P Reg V L) (es fs : List (P × L)) :
    A.Valid C (es ++ fs) ↔ A.Valid C es ∧ A.Valid (A.run C es) fs := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => simp [ih, and_assoc]

@[simp] lemma seesIn_nil (C : Config P Reg V L) (p q : P) : ¬ A.SeesIn C [] p q := id

lemma seesIn_cons (C : Config P Reg V L) (e : P × L) (es : List (P × L)) (p q : P) :
    A.SeesIn C (e :: es) p q ↔ (e.1 = p ∧ A.SeesStep C e q) ∨ A.SeesIn (A.apply C e) es p q :=
  Iff.rfl

lemma seesIn_append (C : Config P Reg V L) (es fs : List (P × L)) (p q : P) :
    A.SeesIn C (es ++ fs) p q ↔ A.SeesIn C es p q ∨ A.SeesIn (A.run C es) fs p q := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => simp [seesIn_cons, ih, or_assoc]

lemma writesIn_cons (C : Config P Reg V L) (e : P × L) (es : List (P × L)) (S : Set Reg) :
    A.WritesIn C (e :: es) S ↔
      (∃ r v, A.act (C.loc e.1) = .write r v ∧ r ∈ S) ∨ A.WritesIn (A.apply C e) es S :=
  Iff.rfl

lemma writesIn_append (C : Config P Reg V L) (es fs : List (P × L)) (S : Set Reg) :
    A.WritesIn C (es ++ fs) S ↔ A.WritesIn C es S ∨ A.WritesIn (A.run C es) fs S := by
  induction es generalizing C with
  | nil => simp [WritesIn]
  | cons e es ih => simp [writesIn_cons, ih, or_assoc]

/-- A step changes only the local state of the stepping process. -/
lemma apply_loc (C : Config P Reg V L) (e : P × L) :
    (A.apply C e).loc = Function.update C.loc e.1 e.2 := by
  unfold apply; split <;> rfl

lemma apply_loc_of_ne (C : Config P Reg V L) (e : P × L) {p : P} (h : p ≠ e.1) :
    (A.apply C e).loc p = C.loc p := by
  rw [apply_loc, Function.update_of_ne h]

lemma apply_loc_self (C : Config P Reg V L) (e : P × L) : (A.apply C e).loc e.1 = e.2 := by
  rw [apply_loc, Function.update_self]

/-- Memory after a step that is not a write. -/
lemma apply_mem_of_not_write (C : Config P Reg V L) (e : P × L)
    (h : ∀ r v, A.act (C.loc e.1) ≠ .write r v) :
    (A.apply C e).val = C.val ∧ (A.apply C e).wr = C.wr := by
  unfold apply; split
  · next r v hw => exact absurd hw (h r v)
  · exact ⟨rfl, rfl⟩

/-- Memory after a write step. -/
lemma apply_mem_of_write (C : Config P Reg V L) (e : P × L) {r : Reg} {v : V}
    (h : A.act (C.loc e.1) = .write r v) :
    (A.apply C e).val = Function.update C.val r v ∧
      (A.apply C e).wr = Function.update C.wr r (some e.1) := by
  unfold apply; rw [h]; exact ⟨rfl, rfl⟩

/-- A register other than the one written is unchanged by a step. -/
lemma apply_mem_other (C : Config P Reg V L) (e : P × L) (r : Reg)
    (h : ∀ v, A.act (C.loc e.1) ≠ .write r v) :
    (A.apply C e).val r = C.val r ∧ (A.apply C e).wr r = C.wr r := by
  rcases hact : A.act (C.loc e.1) with r' | ⟨r', v⟩ | b
  · obtain ⟨h1, h2⟩ := A.apply_mem_of_not_write C e (by intro r v; rw [hact]; simp)
    simp [h1, h2]
  · obtain ⟨h1, h2⟩ := A.apply_mem_of_write C e hact
    have : r ≠ r' := by rintro rfl; exact h v hact
    simp [h1, h2, Function.update_of_ne this]
  · obtain ⟨h1, h2⟩ := A.apply_mem_of_not_write C e (by intro r v; rw [hact]; simp)
    simp [h1, h2]

/-- Processes that take no step keep their local state. -/
lemma run_loc_of_not_mem (C : Config P Reg V L) (es : List (P × L)) (p : P)
    (h : ∀ e ∈ es, e.1 ≠ p) : (A.run C es).loc p = C.loc p := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simp only [run_cons]
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      A.apply_loc_of_ne C e (fun h' => h e List.mem_cons_self h'.symm)]

/-- Registers not written during `es` keep their value and last writer. -/
lemma run_mem_of_not_writesIn (C : Config P Reg V L) (es : List (P × L)) (r : Reg)
    (h : ¬ A.WritesIn C es {r}) : (A.run C es).val r = C.val r ∧ (A.run C es).wr r = C.wr r := by
  induction es generalizing C with
  | nil => exact ⟨rfl, rfl⟩
  | cons e es ih =>
    rw [writesIn_cons] at h
    simp only [not_or, not_exists, not_and] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih _ h2
    obtain ⟨a1, a2⟩ := A.apply_mem_other C e r (fun v hv => h1 r v hv rfl)
    simp only [run_cons]; exact ⟨ih1.trans a1, ih2.trans a2⟩

/-- A returned process takes no step. -/
lemma not_enabled_of_finished {C : Config P Reg V L} {e : P × L} (h : A.Finished C e.1) :
    ¬ A.Enabled C e := by
  obtain ⟨b, hb⟩ := h
  unfold Enabled; rw [hb]; exact id

/-- Returning is permanent; a returned process takes no steps. -/
lemma finished_run {C : Config P Reg V L} {es : List (P × L)} (hv : A.Valid C es) {p : P}
    (h : A.Finished C p) : A.Finished (A.run C es) p ∧ ∀ e ∈ es, e.1 ≠ p := by
  induction es generalizing C with
  | nil => exact ⟨h, by simp⟩
  | cons e es ih =>
    obtain ⟨he, hv⟩ := hv
    have hne : e.1 ≠ p := by
      rintro rfl; exact A.not_enabled_of_finished h he
    have h' : A.Finished (A.apply C e) p := by
      unfold Finished; rwa [A.apply_loc_of_ne C e hne.symm]
    obtain ⟨ih1, ih2⟩ := ih hv h'
    refine ⟨ih1, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact hne
    · exact ih2 e' he'

lemma won_finished {C : Config P Reg V L} {p : P} (h : A.Won C p) : A.Finished C p := ⟨true, h⟩

lemma reachable_run {C : Config P Reg V L} (hC : A.Reachable C) {es : List (P × L)}
    (hv : A.Valid C es) : A.Reachable (A.run C es) := by
  obtain ⟨C₀, es₀, h0, hv0, rfl⟩ := hC
  exact ⟨C₀, es₀ ++ es, h0, (A.valid_append _ _ _).2 ⟨hv0, hv⟩, A.run_append _ _ _⟩

lemma reachable_apply {C : Config P Reg V L} (hC : A.Reachable C) {e : P × L}
    (he : A.Enabled C e) : A.Reachable (A.apply C e) :=
  A.reachable_run hC (es := [e]) (show A.Valid C [e] from ⟨he, trivial⟩)

lemma isInit_reachable {C : Config P Reg V L} (h : A.IsInit C) : A.Reachable C :=
  ⟨C, [], h, trivial, rfl⟩

/-- Closedness w.r.t. `≡_E` only depends on the sees relation. -/
lemma closed_iff (C : Config P Reg V L) (es : List (P × L)) (Q : Set P) :
    A.Closed C es Q ↔ ∀ p q, A.SeesIn C es p q → (p ∈ Q ↔ q ∈ Q) := by
  constructor
  · intro h p q hs
    exact h p q (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hs)))
  · intro h p q hpq
    induction hpq with
    | rel a b hab =>
      rcases hab with rfl | hs | hs
      · rfl
      · exact h a b hs
      · exact (h b a hs).symm
    | refl => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

/-- A process that has not returned in a reachable configuration has an enabled step (from
solo-termination). -/
lemma exists_enabled (hST : A.SoloTerminating) {C : Config P Reg V L} (hC : A.Reachable C)
    {p : P} (hp : ¬ A.Finished C p) : ∃ l, A.Enabled C (p, l) := by
  obtain ⟨es, hes, hv, hf⟩ := hST C hC p
  cases es with
  | nil => exact absurd hf hp
  | cons e es =>
    obtain ⟨he, -⟩ := hv
    have : e.1 = p := hes e List.mem_cons_self
    obtain ⟨p', l⟩ := e
    subst this
    exact ⟨l, he⟩

end Alg

end Podc.LeaderElectionSpaceLB
