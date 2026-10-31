import Papers.PODC2015.EventualConsistencyLimits.Final

/-!
# Corollary 4: every execution has a quiescent extension

**Corollary 4 of [AEM15].** In an eventually consistent data store with invisible reads and
op-driven messages, every finite execution `α` can be extended to a quiescent execution `α β`;
hence (Lemma 3) reads of the same object at any two replicas at the end of `α β` return the same
response.

Construction of `β`: first every replica that has a message pending sends it (`flushAll`; after a
send nothing is pending, `SendClears`), then every message sent so far is delivered to every
replica other than its sender (`deliverEvery`; receipts keep replicas non-pending,
`OpDriven`).
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

namespace Store

variable (D : Store ι Obj V M St)

open scoped Classical in
/-- The `send` of replica `j` at the end of `α`, if it has a message pending. -/
noncomputable def flush1 (α : List (ι × Ev Obj V M)) (j : ι) : List (ι × Ev Obj V M) :=
  if h : ∃ m σ σ', D.state j α = some σ ∧ D.step j σ (.send m) = some σ' then
    [(j, .send h.choose)] else []

/-- Every replica of `l` that has a message pending at the end of `α` sends it. -/
noncomputable def flushAll (α : List (ι × Ev Obj V M)) (l : List ι) : List (ι × Ev Obj V M) :=
  l.flatMap (D.flush1 α)

/-- Deliver every message sent in `α` to every replica other than its sender. -/
noncomputable def deliverEvery [Fintype ι] (α : List (ι × Ev Obj V M)) :
    List (ι × Ev Obj V M) :=
  α.flatMap fun x => match x.2 with
    | .send m => ((Finset.univ : Finset ι).toList.filter fun i => i ≠ x.1).map
        fun i => (i, .recv m)
    | _ => []

variable {D}

lemma mem_flush1 {α : List (ι × Ev Obj V M)} {j : ι} {x : ι × Ev Obj V M}
    (hx : x ∈ D.flush1 α j) : x.1 = j ∧ ∃ m, x.2 = .send m := by
  unfold flush1 at hx
  split_ifs at hx
  · simp only [List.mem_singleton] at hx; subst hx; exact ⟨rfl, _, rfl⟩
  · simp at hx

lemma mem_deliverEvery [Fintype ι] {α : List (ι × Ev Obj V M)} {x : ι × Ev Obj V M}
    (hx : x ∈ deliverEvery α) : ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ α := by
  simp only [deliverEvery, List.mem_flatMap] at hx
  obtain ⟨⟨j, e⟩, hjα, hx⟩ := hx
  cases e with
  | do_ d => simp at hx
  | recv m => simp at hx
  | send m =>
    simp only [List.mem_map, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
      decide_eq_true_eq] at hx
    obtain ⟨i, hij, rfl⟩ := hx
    exact ⟨m, rfl, j, fun h => hij h.symm, hjα⟩

lemma recv_mem_deliverEvery [Fintype ι] {α : List (ι × Ev Obj V M)} {j i : ι} {m : M}
    (hj : (j, .send m) ∈ α) (hij : i ≠ j) : (i, .recv m) ∈ deliverEvery α := by
  simp only [deliverEvery, List.mem_flatMap]
  refine ⟨(j, .send m), hj, ?_⟩
  simp [hij]

/-- Flushing the replicas of a duplicate-free list `l`: the result is an execution, the replicas
of `l` have nothing pending, the others are unchanged. -/
lemma flushAll_spec (hSC : D.SendClears) {α : List (ι × Ev Obj V M)} (hα : D.IsExec α)
    (l : List ι) (hl : l.Nodup) :
    D.IsExec (α ++ D.flushAll α l) ∧
      (∀ i, i ∉ l → D.state i (α ++ D.flushAll α l) = D.state i α) ∧
      (∀ i ∈ l, ∀ σ, D.state i (α ++ D.flushAll α l) = some σ → ¬ D.Pending i σ) := by
  induction l using List.reverseRecOn with
  | nil => simp [flushAll, hα]
  | append_singleton l j ih =>
    rw [List.nodup_append] at hl
    have hjl : j ∉ l := fun h => hl.2.2 j h j (by simp) rfl
    obtain ⟨hE, hout, hin⟩ := ih hl.1
    have hF : D.flushAll α (l ++ [j]) = D.flushAll α l ++ D.flush1 α j := by
      simp [flushAll]
    rw [hF, ← List.append_assoc]
    have hjst : D.state j (α ++ D.flushAll α l) = D.state j α := hout j hjl
    have hother : ∀ i, i ≠ j → D.state i (α ++ D.flushAll α l ++ D.flush1 α j) =
        D.state i (α ++ D.flushAll α l) := fun i hij =>
      state_append_of_not_mem _ _ _ fun x hx h => hij (h ▸ (mem_flush1 hx).1)
    obtain ⟨σj, hσj⟩ := hα.state_isSome j
    refine ⟨?_, fun i hi => ?_, fun i hi σ hσ => ?_⟩
    · unfold flush1
      split_ifs with h
      · obtain ⟨σ, σ', h1, h2⟩ := h.choose_spec
        exact .snoc hE (hjst.trans h1) h2 fun m hm => by cases hm
      · simpa using hE
    · simp only [List.mem_append, List.mem_singleton, not_or] at hi
      rw [hother i hi.2, hout i hi.1]
    · by_cases hij : i = j
      · subst hij
        unfold flush1 at hσ
        split_ifs at hσ with h
        · obtain ⟨σ₀, σ', h1, h2⟩ := h.choose_spec
          rw [state_snoc_self _ (hjst.trans h1), h2] at hσ
          cases hσ
          exact hSC _ _ _ _ h2
        · rintro ⟨m, σ', hm⟩
          rw [List.append_nil, hjst] at hσ
          exact h ⟨m, σ, σ', hσ, hm⟩
      · rw [hother i hij] at hσ
        simp only [List.mem_append, List.mem_singleton] at hi
        exact hin i (hi.resolve_right hij) σ hσ

/-- The quiescent extension of `α`: flush all replicas, then deliver every message. -/
noncomputable def quiesce [Fintype ι] (D : Store ι Obj V M St) (α : List (ι × Ev Obj V M)) :
    List (ι × Ev Obj V M) :=
  D.flushAll α (Finset.univ : Finset ι).toList ++
    deliverEvery (α ++ D.flushAll α (Finset.univ : Finset ι).toList)

lemma quiesce_spec [Fintype ι] (hOD : D.OpDriven) (hSC : D.SendClears) (hRecv : D.RecvEnabled)
    {α : List (ι × Ev Obj V M)} (hα : D.IsExec α) :
    D.IsExec (α ++ D.quiesce α) ∧ D.Quiescent (α ++ D.quiesce α) ∧
      ∀ x ∈ D.quiesce α, ∃ m, x.2 = .send m ∨ x.2 = .recv m := by
  set γ := α ++ D.flushAll α (Finset.univ : Finset ι).toList with hγ
  obtain ⟨hE, -, hin⟩ := flushAll_spec hSC hα _ (Finset.nodup_toList _)
  have heq : α ++ D.quiesce α = γ ++ deliverEvery γ := by simp [quiesce, hγ]
  have hδmem : ∀ x ∈ deliverEvery γ, ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ γ :=
    fun x hx => mem_deliverEvery hx
  rw [heq]
  refine ⟨hE.append_recvs hRecv hδmem, ⟨fun i σ h => not_pending_append_recvs hOD
    (fun x hx => let ⟨m, hm, _⟩ := hδmem x hx; ⟨m, hm⟩)
    (hin i (by simp)) σ h, ?_⟩, ?_⟩
  · intro j m hj i hij
    have hjγ : (j, Ev.send m) ∈ γ := by
      rcases List.mem_append.1 hj with hj | hj
      · exact hj
      · obtain ⟨m', hm', -⟩ := hδmem _ hj; cases hm'
    exact List.mem_append_right _ (recv_mem_deliverEvery hjγ hij)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · simp only [flushAll, List.mem_flatMap] at hx
      obtain ⟨j, -, hx⟩ := hx
      obtain ⟨-, m, hm⟩ := mem_flush1 hx
      exact ⟨m, .inl hm⟩
    · obtain ⟨m, hm, -⟩ := hδmem x hx
      exact ⟨m, .inr hm⟩

end Store

open Store

variable {D : Store ι Obj V M St}

/-- **Corollary 4 of [AEM15].** In an eventually consistent data store with invisible reads,
op-driven messages, and in which a send relays everything pending and receipts are always
enabled, every finite execution `α` extends, by sends and receipts only, to a quiescent
execution `α β`; at the end of `α β` any two reads of the same object, at any two replicas,
return the same response. -/
theorem corollary4 [Fintype ι] {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    (hIR : D.InvisibleReads) (hOD : D.OpDriven) (hSC : D.SendClears) (hRecv : D.RecvEnabled)
    {α : List (ι × Ev Obj V M)} (hα : D.IsExec α) :
    ∃ β : List (ι × Ev Obj V M), (∀ x ∈ β, ∃ m, x.2 = .send m ∨ x.2 = .recv m) ∧
      D.IsExec (α ++ β) ∧ D.Quiescent (α ++ β) ∧
      ∀ (R₁ R₂ : ι) (o : Obj) (r₁ r₂ : Resp V) (σ₁ σ₂ σ₁' σ₂' : St),
        D.state R₁ (α ++ β) = some σ₁ → D.step R₁ σ₁ (rd o r₁) = some σ₁' →
        D.state R₂ (α ++ β) = some σ₂ → D.step R₂ σ₂ (rd o r₂) = some σ₂' → r₁ = r₂ := by
  obtain ⟨hE, hq, hβ⟩ := quiesce_spec hOD hSC hRecv hα
  exact ⟨D.quiesce α, hβ, hE, hq, fun R₁ R₂ o r₁ r₂ σ₁ σ₂ σ₁' σ₂' h₁ h₁' h₂ h₂' =>
    lemma3 hEC hIR hE hq h₁ h₁' h₂ h₂'⟩

end Podc.EventualConsistencyLimits
