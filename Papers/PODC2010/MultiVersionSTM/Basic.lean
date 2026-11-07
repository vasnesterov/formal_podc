import Papers.PODC2010.MultiVersionSTM.STM

/-!
# Basic lemmas: executions, histories, well-formedness
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-! ### History predicates on appended histories -/

section Hist

variable {h h' : Hist Tx O} {e : Event Tx O} {T : Tx} {o : O}

@[simp] lemma began_nil : ¬ Began ([] : Hist Tx O) T := by simp [Began]
@[simp] lemma committed_nil : ¬ Committed ([] : Hist Tx O) T := by simp [Committed]
@[simp] lemma aborted_nil : ¬ Aborted ([] : Hist Tx O) T := by simp [Aborted]
@[simp] lemma terminated_nil : ¬ Terminated ([] : Hist Tx O) T := by simp [Terminated]
@[simp] lemma writes_nil : ¬ Writes ([] : Hist Tx O) T o := by simp [Writes]
@[simp] lemma accesses_nil : ¬ Accesses ([] : Hist Tx O) T o := by simp [Accesses]

lemma began_append : Began (h ++ h') T ↔ Began h T ∨ Began h' T := by
  simp only [Began, List.mem_append]; aesop

lemma committed_append : Committed (h ++ h') T ↔ Committed h T ∨ Committed h' T := by
  simp only [Committed, List.mem_append]; aesop

lemma aborted_append : Aborted (h ++ h') T ↔ Aborted h T ∨ Aborted h' T := by
  simp only [Aborted, List.mem_append]; aesop

lemma terminated_append : Terminated (h ++ h') T ↔ Terminated h T ∨ Terminated h' T := by
  simp only [Terminated, committed_append, aborted_append]; tauto

lemma writes_append : Writes (h ++ h') T o ↔ Writes h T o ∨ Writes h' T o := by
  simp only [Writes, List.mem_append]; aesop

lemma accesses_append : Accesses (h ++ h') T o ↔ Accesses h T o ∨ Accesses h' T o := by
  simp only [Accesses, List.mem_append]; aesop

@[simp] lemma began_cons : Began (e :: h) T ↔ e.inv.tx = T ∨ Began h T := by
  simp [Began]

@[simp] lemma committed_cons : Committed (e :: h) T ↔ (∃ r, e = ⟨.commit T, some r⟩) ∨ Committed h T := by
  simp only [Committed, List.mem_cons]; aesop

@[simp] lemma aborted_cons : Aborted (e :: h) T ↔ (e.inv.tx = T ∧ e.resp = none) ∨ Aborted h T := by
  simp [Aborted]

@[simp] lemma writes_cons : Writes (e :: h) T o ↔ e.inv = .write T o ∨ Writes h T o := by
  simp only [Writes, List.mem_cons]
  constructor
  · rintro ⟨r, rfl | hr⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨r, hr⟩
  · rintro (he | ⟨r, hr⟩)
    · exact ⟨e.resp, Or.inl (by cases e; simp_all)⟩
    · exact ⟨r, Or.inr hr⟩

@[simp] lemma accesses_cons : Accesses (e :: h) T o ↔ (e.inv.tx = T ∧ e.inv.obj? = some o) ∨ Accesses h T o := by
  simp [Accesses]

lemma terminated_cons : Terminated (e :: h) T ↔
    ((∃ r, e = ⟨.commit T, some r⟩) ∨ (e.inv.tx = T ∧ e.resp = none)) ∨ Terminated h T := by
  simp only [Terminated, committed_cons, aborted_cons]; tauto

lemma Began.mono (hb : Began h T) (h' : Hist Tx O) : Began (h ++ h') T :=
  began_append.2 (Or.inl hb)
lemma Committed.mono (hb : Committed h T) (h' : Hist Tx O) : Committed (h ++ h') T :=
  committed_append.2 (Or.inl hb)
lemma Terminated.mono (hb : Terminated h T) (h' : Hist Tx O) : Terminated (h ++ h') T :=
  terminated_append.2 (Or.inl hb)
lemma Writes.mono (hb : Writes h T o) (h' : Hist Tx O) : Writes (h ++ h') T o :=
  writes_append.2 (Or.inl hb)
lemma Accesses.mono (hb : Accesses h T o) (h' : Hist Tx O) : Accesses (h ++ h') T o :=
  accesses_append.2 (Or.inl hb)

lemma Committed.began (hc : Committed h T) : Began h T := by
  obtain ⟨r, hr⟩ := hc; exact ⟨_, hr, rfl⟩

lemma Writes.began (hc : Writes h T o) : Began h T := by
  obtain ⟨r, hr⟩ := hc; exact ⟨_, hr, rfl⟩

lemma Accesses.began (hc : Accesses h T o) : Began h T := by
  obtain ⟨e, he, h1, _⟩ := hc; exact ⟨e, he, h1⟩

lemma Terminated.began (hc : Terminated h T) : Began h T := by
  rcases hc with hc | ⟨e, he, h1, _⟩
  · exact hc.began
  · exact ⟨e, he, h1⟩

lemma Writes.accesses (hc : Writes h T o) : Accesses h T o := by
  obtain ⟨r, hr⟩ := hc; exact ⟨_, hr, rfl, rfl⟩

end Hist

/-! ### Well-formedness -/

section WF

variable [TxSys Tx P] {h : Hist Tx O}

lemma WF.nil : WF ([] : Hist Tx O) := by
  intro h₁ e h₂ he; simp at he

lemma WF.of_append {h₁ h₂ : Hist Tx O} (hw : WF (h₁ ++ h₂)) : WF h₁ := by
  intro a e b hab
  exact hw a e (b ++ h₂) (by simp [hab])

lemma WF.snoc (hw : WF h) (e : Event Tx O) (hok : OKNext h e.inv) : WF (h ++ [e]) := by
  intro a e' b hab
  rcases List.eq_nil_or_concat b with rfl | ⟨b', x, rfl⟩
  · obtain ⟨rfl, rfl⟩ : h = a ∧ e = e' := by simpa using hab
    exact hok
  · have : h = a ++ e' :: b' := by
      have := hab; simp only [List.concat_eq_append] at this
      rw [show a ++ e' :: (b' ++ [x]) = (a ++ e' :: b') ++ [x] by simp] at this
      exact (List.append_inj' this rfl).1
    exact hw a e' b' this

lemma WF.snoc_iff (e : Event Tx O) : WF (h ++ [e]) ↔ WF h ∧ OKNext h e.inv :=
  ⟨fun hw => ⟨hw.of_append, hw h e [] rfl⟩, fun ⟨hw, hok⟩ => hw.snoc e hok⟩

end WF

/-! ### Executions -/

namespace STM

variable (X : STM Tx O P) [TxSys Tx P]

lemma run_nil (C : Config X) : X.run C [] = (C, []) := rfl

lemma run_append (C : Config X) (σ τ : List (Inv Tx O)) :
    X.run C (σ ++ τ) = ((X.run (X.run C σ).1 τ).1, (X.run C σ).2 ++ (X.run (X.run C σ).1 τ).2) := by
  unfold run
  rw [List.foldl_append]
  generalize List.foldl _ (C, []) σ = s
  obtain ⟨C', l⟩ := s
  simp only
  induction τ generalizing C' l with
  | nil => simp
  | cons i τ ih =>
    simp only [List.foldl_cons]
    rw [ih _ (l ++ _), ih _ ([] ++ _)]
    simp

lemma run_snoc (C : Config X) (σ : List (Inv Tx O)) (i : Inv Tx O) :
    X.run C (σ ++ [i]) = ((X.step (X.run C σ).1 i).1,
      (X.run C σ).2 ++ [(⟨i, (X.step (X.run C σ).1 i).2.1⟩, (X.step (X.run C σ).1 i).2.2)]) := by
  rw [run_append]; rfl

lemma run_cons (C : Config X) (i : Inv Tx O) (τ : List (Inv Tx O)) :
    X.run C (i :: τ) = ((X.run (X.step C i).1 τ).1,
      (⟨i, (X.step C i).2.1⟩, (X.step C i).2.2) :: (X.run (X.step C i).1 τ).2) := by
  rw [show i :: τ = [i] ++ τ from rfl, run_append]; rfl

@[simp] lemma exec_nil : X.exec [] = (X.init, []) := rfl
@[simp] lemma hist_nil : X.hist [] = [] := rfl
@[simp] lemma conf_nil : X.conf [] = X.init := rfl

lemma exec_append (σ τ : List (Inv Tx O)) :
    X.exec (σ ++ τ) = ((X.run (X.conf σ) τ).1, (X.exec σ).2 ++ (X.run (X.conf σ) τ).2) :=
  X.run_append _ σ τ

lemma hist_append (σ τ : List (Inv Tx O)) :
    X.hist (σ ++ τ) = X.hist σ ++ (X.run (X.conf σ) τ).2.map Prod.fst := by
  simp [hist, exec_append]

lemma conf_append (σ τ : List (Inv Tx O)) :
    X.conf (σ ++ τ) = (X.run (X.conf σ) τ).1 := by
  simp [conf, exec_append]

@[simp] lemma hist_snoc (σ : List (Inv Tx O)) (i : Inv Tx O) :
    X.hist (σ ++ [i]) = X.hist σ ++ [⟨i, X.resp σ i⟩] := by
  simp [hist, exec, run_snoc, resp, conf]

lemma conf_snoc (σ : List (Inv Tx O)) (i : Inv Tx O) :
    X.conf (σ ++ [i]) = (X.step (X.conf σ) i).1 := by
  simp [conf, exec, run_snoc]

@[simp] lemma length_run (C : Config X) (σ : List (Inv Tx O)) : (X.run C σ).2.length = σ.length := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ i ih => simp [run_snoc, ih]

@[simp] lemma length_hist (σ : List (Inv Tx O)) : (X.hist σ).length = σ.length := by
  simp [hist, exec]

lemma map_inv_run (C : Config X) (σ : List (Inv Tx O)) :
    (X.run C σ).2.map (fun s => s.1.inv) = σ := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ i ih => simp [run_snoc, ih]

lemma map_inv_hist (σ : List (Inv Tx O)) : (X.hist σ).map Event.inv = σ := by
  have := X.map_inv_run X.init σ
  simpa [hist, exec, List.map_map, Function.comp_def] using this

/-- The events of the steps `τ` run after the schedule `p`. -/
noncomputable def histFrom (p : List (Inv Tx O)) : List (Inv Tx O) → Hist Tx O
  | [] => []
  | i :: τ => ⟨i, X.resp p i⟩ :: histFrom (p ++ [i]) τ

lemma hist_append_histFrom (p τ : List (Inv Tx O)) :
    X.hist (p ++ τ) = X.hist p ++ X.histFrom p τ := by
  induction τ generalizing p with
  | nil => simp [histFrom]
  | cons i τ ih =>
    rw [show p ++ i :: τ = (p ++ [i]) ++ τ by simp, ih, hist_snoc]; simp [histFrom]

/-- The history of a schedule, event by event. -/
lemma hist_eq_histFrom (σ : List (Inv Tx O)) : X.hist σ = X.histFrom [] σ := by
  simpa using X.hist_append_histFrom [] σ


end STM

end Podc.MultiVersionSTM
