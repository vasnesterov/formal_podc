import Papers.PODC2015.EventualConsistencyLimits.Lemma5

/-!
# Building executions from client/network actions

To construct the executions of Theorem 12 we describe the local behaviour of a replica by a list
of *actions* (receive a given message, read an object, write a value, send the pending message if
any); `Store.acts` turns it into the actual local events, choosing the responses (and the message
sent) that the data store allows. `IsExec.append_block` appends such a block of local events to
an execution.
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

/-- Actions of a replica. -/
inductive Act (Obj V M : Type*) where
  | rcv (m : M)
  | rd (o : Obj)
  | wr (o : Obj) (v : V)
  | snd

namespace Store

variable (D : Store ι Obj V M St) (hAv : D.Available) (hRecv : D.RecvEnabled) [Nonempty M]

open scoped Classical in
/-- The message sent by `i` in state `σ` (if any message is pending). -/
noncomputable def sendOf (i : ι) (σ : St) : M :=
  if h : D.Pending i σ then Classical.choose h else Classical.arbitrary M

open scoped Classical in
/-- Local events and new state for one action. -/
noncomputable def act1 (i : ι) (σ : St) : Act Obj V M → List (Ev Obj V M) × St
  | .rcv m => ([.recv m], Classical.choose (hRecv i σ m))
  | .rd o => ([.do_ ⟨o, .read, Classical.choose (hAv i σ o .read)⟩],
      Classical.choose (Classical.choose_spec (hAv i σ o .read)))
  | .wr o v => ([.do_ ⟨o, .write v, Classical.choose (hAv i σ o (.write v))⟩],
      Classical.choose (Classical.choose_spec (hAv i σ o (.write v))))
  | .snd => if h : D.Pending i σ then ([.send (D.sendOf i σ)],
      Classical.choose (Classical.choose_spec h)) else ([], σ)

/-- Local events and final state for a list of actions. -/
noncomputable def acts (i : ι) : St → List (Act Obj V M) → List (Ev Obj V M) × St
  | σ, [] => ([], σ)
  | σ, a :: l => ((D.act1 hAv hRecv i σ a).1 ++ (acts i (D.act1 hAv hRecv i σ a).2 l).1,
      (acts i (D.act1 hAv hRecv i σ a).2 l).2)

variable {D hAv hRecv}

lemma act1_snd_of_pending {i : ι} {σ : St} (h : D.Pending i σ) :
    (D.act1 hAv hRecv i σ .snd).1 = [.send (D.sendOf i σ)] ∧
      D.step i σ (.send (D.sendOf i σ)) = some (D.act1 hAv hRecv i σ .snd).2 := by
  refine ⟨by simp [act1, h], ?_⟩
  have := Classical.choose_spec (Classical.choose_spec h)
  simp only [act1, h, dite_true]
  simpa [sendOf, h] using this

lemma act1_run (i : ι) (σ : St) (a : Act Obj V M) :
    (D.act1 hAv hRecv i σ a).1.foldlM (D.step i) σ = some (D.act1 hAv hRecv i σ a).2 := by
  cases a with
  | rcv m => simpa [act1] using Classical.choose_spec (hRecv i σ m)
  | rd o => simpa [act1] using Classical.choose_spec (Classical.choose_spec (hAv i σ o .read))
  | wr o v =>
    simpa [act1] using Classical.choose_spec (Classical.choose_spec (hAv i σ o (.write v)))
  | snd =>
    by_cases h : D.Pending i σ
    · obtain ⟨h1, h2⟩ := act1_snd_of_pending (hAv := hAv) (hRecv := hRecv) h
      rw [h1]
      simp [h2]
    · simp [act1, h]

lemma acts_run (i : ι) (σ : St) (l : List (Act Obj V M)) :
    (D.acts hAv hRecv i σ l).1.foldlM (D.step i) σ = some (D.acts hAv hRecv i σ l).2 := by
  induction l generalizing σ with
  | nil => rfl
  | cons a l ih =>
    simp only [acts, List.foldlM_append, act1_run, Option.bind_eq_bind, Option.bind_some]
    exact ih _

@[simp] lemma acts_nil (i : ι) (σ : St) : D.acts hAv hRecv i σ ([] : List (Act Obj V M)) = ([], σ) :=
  rfl

lemma acts_append (i : ι) (σ : St) (l₁ l₂ : List (Act Obj V M)) :
    D.acts hAv hRecv i σ (l₁ ++ l₂) =
      ((D.acts hAv hRecv i σ l₁).1 ++ (D.acts hAv hRecv i (D.acts hAv hRecv i σ l₁).2 l₂).1,
        (D.acts hAv hRecv i (D.acts hAv hRecv i σ l₁).2 l₂).2) := by
  induction l₁ generalizing σ with
  | nil => simp
  | cons a l ih => simp [acts, ih]

lemma acts_cons (i : ι) (σ : St) (a : Act Obj V M) (l : List (Act Obj V M)) :
    D.acts hAv hRecv i σ (a :: l) =
      ((D.act1 hAv hRecv i σ a).1 ++ (D.acts hAv hRecv i (D.act1 hAv hRecv i σ a).2 l).1,
        (D.acts hAv hRecv i (D.act1 hAv hRecv i σ a).2 l).2) := rfl

lemma act1_rd (i : ι) (σ : St) (o : Obj) :
    ∃ r, (D.act1 hAv hRecv i σ (.rd o)).1 = [.do_ ⟨o, .read, r⟩] ∧
      D.step i σ (.do_ ⟨o, .read, r⟩) = some (D.act1 hAv hRecv i σ (.rd o)).2 :=
  ⟨_, rfl, Classical.choose_spec (Classical.choose_spec (hAv i σ o .read))⟩

lemma act1_wr (i : ι) (σ : St) (o : Obj) (v : V) :
    ∃ r, (D.act1 hAv hRecv i σ (.wr o v)).1 = [.do_ ⟨o, .write v, r⟩] ∧
      D.step i σ (.do_ ⟨o, .write v, r⟩) = some (D.act1 hAv hRecv i σ (.wr o v)).2 :=
  ⟨_, rfl, Classical.choose_spec (Classical.choose_spec (hAv i σ o (.write v)))⟩

lemma act1_rcv (i : ι) (σ : St) (m : M) : (D.act1 hAv hRecv i σ (.rcv m)).1 = [.recv m] := rfl

lemma act1_rd_state (hIR : D.InvisibleReads) (i : ι) (σ : St) (o : Obj) :
    (D.act1 hAv hRecv i σ (.rd o)).2 = σ := by
  obtain ⟨r, -, h⟩ := act1_rd (D := D) (hAv := hAv) (hRecv := hRecv) i σ o
  exact hIR _ _ _ _ _ h

/-- The events of an action list are receipts of the `rcv` messages, do-events and sends. -/
lemma mem_acts_recv {i : ι} {σ : St} {l : List (Act Obj V M)} {m : M}
    (h : Ev.recv m ∈ (D.acts hAv hRecv i σ l).1) : Act.rcv m ∈ l := by
  induction l generalizing σ with
  | nil => simp at h
  | cons a l ih =>
    rw [acts_cons, List.mem_append] at h
    rcases h with h | h
    · cases a with
      | rcv m' => simp [act1] at h; simp [h]
      | rd o => simp [act1] at h
      | wr o v => simp [act1] at h
      | snd =>
        by_cases hp : D.Pending i σ
        · simp [act1, hp] at h
        · simp [act1, hp] at h
    · exact List.mem_cons_of_mem _ (ih h)

lemma mem_acts_of_rcv {i : ι} {σ : St} {l : List (Act Obj V M)} {m : M}
    (h : Act.rcv m ∈ l) : Ev.recv m ∈ (D.acts hAv hRecv i σ l).1 := by
  induction l generalizing σ with
  | nil => simp at h
  | cons a l ih =>
    rw [acts_cons, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · left; simp [act1]
    · exact Or.inr (ih h)

/-- Receiving and reading keep a replica without pending messages. -/
lemma not_pending_acts (hOD : D.OpDriven) (hIR : D.InvisibleReads) {i : ι} {σ : St}
    {l : List (Act Obj V M)} (hl : ∀ a ∈ l, (∃ m, a = .rcv m) ∨ ∃ o, a = .rd o)
    (hσ : ¬ D.Pending i σ) : ¬ D.Pending i (D.acts hAv hRecv i σ l).2 := by
  induction l generalizing σ with
  | nil => exact hσ
  | cons a l ih =>
    rw [acts_cons]
    apply ih (fun a ha => hl a (by simp [ha]))
    rcases hl a (by simp) with ⟨m, rfl⟩ | ⟨o, rfl⟩
    · exact hOD.2 i σ m _ (Classical.choose_spec (hRecv i σ m)) hσ
    · rw [act1_rd_state hIR]; exact hσ

/-- Events produced by receive/read actions. -/
lemma acts_rcv_rd_events {i : ι} {σ : St} {l : List (Act Obj V M)}
    (hl : ∀ a ∈ l, (∃ m, a = .rcv m) ∨ ∃ o, a = .rd o) {e : Ev Obj V M}
    (he : e ∈ (D.acts hAv hRecv i σ l).1) :
    (∃ m, e = .recv m ∧ Act.rcv m ∈ l) ∨ ∃ o r, e = .do_ ⟨o, .read, r⟩ := by
  induction l generalizing σ with
  | nil => simp at he
  | cons a l ih =>
    rw [acts_cons, List.mem_append] at he
    rcases he with he | he
    · rcases hl a (by simp) with ⟨m, rfl⟩ | ⟨o, rfl⟩
      · simp [act1] at he; exact Or.inl ⟨m, he, by simp⟩
      · simp [act1] at he; exact Or.inr ⟨o, _, he⟩
    · rcases ih (fun a ha => hl a (by simp [ha])) he with ⟨m, h1, h2⟩ | h
      · exact Or.inl ⟨m, h1, List.mem_cons_of_mem _ h2⟩
      · exact Or.inr h

end Store

/-- Tag local events with their replica. -/
def tag (i : ι) (l : List (Ev Obj V M)) : List (ι × Ev Obj V M) := l.map fun e => (i, e)

@[simp] lemma tag_nil (i : ι) : tag i ([] : List (Ev Obj V M)) = [] := rfl

@[simp] lemma tag_append (i : ι) (l₁ l₂ : List (Ev Obj V M)) :
    tag i (l₁ ++ l₂) = tag i l₁ ++ tag i l₂ := by simp [tag]

@[simp] lemma tag_cons (i : ι) (e : Ev Obj V M) (l : List (Ev Obj V M)) :
    tag i (e :: l) = (i, e) :: tag i l := rfl

@[simp] lemma length_tag (i : ι) (l : List (Ev Obj V M)) : (tag i l).length = l.length := by
  simp [tag]

lemma mem_tag {i : ι} {l : List (Ev Obj V M)} {x : ι × Ev Obj V M} :
    x ∈ tag i l ↔ x.1 = i ∧ x.2 ∈ l := by
  obtain ⟨j, e⟩ := x
  simp [tag, eq_comm, and_comm]

@[simp] lemma proj_tag_self (i : ι) (l : List (Ev Obj V M)) : proj i (tag i l) = l := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [ih]

lemma proj_tag_ne {i j : ι} (h : j ≠ i) (l : List (Ev Obj V M)) : proj i (tag j l) = [] :=
  proj_eq_nil fun x hx => by rw [(mem_tag.1 hx).1]; exact h

namespace Store

variable {D : Store ι Obj V M St}

/-- Appending a block of local events of `i` that runs from `i`'s current state. -/
lemma IsExec.append_block {α : List (ι × Ev Obj V M)} {i : ι} {σ σ' : St}
    {l : List (Ev Obj V M)} (hα : D.IsExec α) (hσ : D.state i α = some σ)
    (hl : l.foldlM (D.step i) σ = some σ')
    (hr : ∀ m, Ev.recv m ∈ l → ∃ j, j ≠ i ∧ (j, .send m) ∈ α) :
    D.IsExec (α ++ tag i l) ∧ D.state i (α ++ tag i l) = some σ' := by
  induction l generalizing α σ with
  | nil => simp at hl; subst hl; simpa using ⟨hα, hσ⟩
  | cons e l ih =>
    simp only [List.foldlM_cons] at hl
    obtain ⟨σ₁, h₁, hl'⟩ : ∃ σ₁, D.step i σ e = some σ₁ ∧ l.foldlM (D.step i) σ₁ = some σ' := by
      cases h : D.step i σ e with
      | none => simp [h] at hl
      | some σ₁ => exact ⟨σ₁, rfl, by simpa [h] using hl⟩
    have hα' : D.IsExec (α ++ [(i, e)]) := .snoc hα hσ h₁ fun m hm => by
      subst hm; exact hr m (by simp)
    have hσ' : D.state i (α ++ [(i, e)]) = some σ₁ := by rw [state_snoc_self D hσ, h₁]
    have := ih hα' hσ' hl' fun m hm => by
      obtain ⟨j, hj, hjα⟩ := hr m (by simp [hm])
      exact ⟨j, hj, by simp [hjα]⟩
    simpa [tag, List.append_assoc] using this

end Store

/-! ### Written values -/

/-- The value written by an event, if it is a write. -/
def wv : ι × Ev Obj V M → Option V
  | (_, .do_ ⟨_, .write v, _⟩) => some v
  | _ => none

/-- The values written in a finite execution, in order. -/
def wvals (α : List (ι × Ev Obj V M)) : List V := α.filterMap wv

@[simp] lemma wvals_append (α β : List (ι × Ev Obj V M)) :
    wvals (α ++ β) = wvals α ++ wvals β := by simp [wvals]

lemma wvals_eq_nil {α : List (ι × Ev Obj V M)}
    (h : ∀ x ∈ α, ∀ o v r, x.2 ≠ .do_ ⟨o, .write v, r⟩) : wvals α = [] := by
  simp only [wvals, List.filterMap_eq_nil_iff]
  rintro ⟨i, e⟩ hx
  rcases e with ⟨o, op, r⟩ | m | m
  · cases op with
    | read => rfl
    | write v => exact absurd rfl (h _ hx o v r)
  · rfl
  · rfl

lemma mem_wvals {α : List (ι × Ev Obj V M)} {i : ι} {o : Obj} {v : V} {r : Resp V}
    (h : (i, .do_ ⟨o, .write v, r⟩) ∈ α) : v ∈ wvals α :=
  List.mem_filterMap.2 ⟨_, h, rfl⟩

lemma fresh_of_not_mem_wvals {α : List (ι × Ev Obj V M)} {v : V} (h : v ∉ wvals α) :
    ∀ x ∈ α, ∀ o' r', x.2 ≠ .do_ ⟨o', .write v, r'⟩ := by
  rintro ⟨i, e⟩ hx o' r' rfl
  exact h (mem_wvals hx)

lemma dist_of_nodup_wvals {α : List (ι × Ev Obj V M)} (h : (wvals α).Nodup) :
    ∀ p q (hp : p < α.length) (hq : q < α.length) i j o₁ o₂ u r₁ r₂,
      α[p] = (i, .do_ ⟨o₁, .write u, r₁⟩) → α[q] = (j, .do_ ⟨o₂, .write u, r₂⟩) → p = q := by
  induction α with
  | nil => intro p; simp
  | cons z α ih =>
    intro p q hp hq i j o₁ o₂ u r₁ r₂ h₁ h₂
    have hw : wvals (z :: α) = (wv z).toList ++ wvals α := by
      simp only [wvals, List.filterMap_cons]; cases wv z <;> rfl
    rw [hw, List.nodup_append] at h
    rcases p with _ | p <;> rcases q with _ | q
    · rfl
    · exfalso
      simp only [List.getElem_cons_zero] at h₁
      simp only [List.getElem_cons_succ] at h₂
      have hz : wv z = some u := by rw [h₁]; rfl
      have hu : u ∈ wvals α := mem_wvals (h₂ ▸ List.getElem_mem _)
      exact h.2.2 u (by simp [hz]) u hu rfl
    · exfalso
      simp only [List.getElem_cons_zero] at h₂
      simp only [List.getElem_cons_succ] at h₁
      have hz : wv z = some u := by rw [h₂]; rfl
      have hu : u ∈ wvals α := mem_wvals (h₁ ▸ List.getElem_mem _)
      exact h.2.2 u (by simp [hz]) u hu rfl
    · simp only [List.getElem_cons_succ] at h₁ h₂
      simp only [List.length_cons] at hp hq
      have := ih h.2.1 p q (by omega) (by omega) i j o₁ o₂ u r₁ r₂ h₁ h₂
      omega

end Podc.EventualConsistencyLimits
