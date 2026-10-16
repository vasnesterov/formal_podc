import Papers.PODC2025.TwoStepConsensusLB.Impl

/-!
# Basic facts about the handlers of Figure 1

* `Grows s s'`: the monotone components of the local state only grow (ballot, received messages,
  outbox; `initial_val`, `val` and `decided` never return to `⊥`). Every handler, `invoke` and
  `timer` satisfy it.
* `NoPending`: a process that has not decided has no enabled decision (line 9) — established
  after every message handler by `tryDecide`.
* Fold lemmas for processing a list of messages.
* `proposal_ne_none`, `proposal_mem`: properties of the leader's proposal (lines 26–38).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-! ### Folds -/

section Fold

variable {α β : Type*}

theorem foldl_inv (h : α → β → α) (J : α → Prop) {l : List β}
    (hJ : ∀ s x, x ∈ l → J s → J (h s x)) {s : α} (hs : J s) : J (l.foldl h s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons y l ih =>
    exact ih (fun s x hx => hJ s x (List.mem_cons_of_mem _ hx)) (hJ s y List.mem_cons_self hs)

/-- If handling `x₀ ∈ l` establishes `Q` (from any state satisfying the invariant `J`) and every
handler preserves `Q` (under `J`), then `Q` holds after processing `l`. -/
theorem foldl_mem (h : α → β → α) (J Q : α → Prop) {l : List β}
    (hJ : ∀ s x, x ∈ l → J s → J (h s x)) (hQ : ∀ s x, x ∈ l → J s → Q s → Q (h s x))
    {x₀ : β} (hx₀ : x₀ ∈ l) (h₀ : ∀ s, J s → Q (h s x₀)) {s : α} (hs : J s) :
    Q (l.foldl h s) := by
  induction l generalizing s with
  | nil => simp at hx₀
  | cons y l ih =>
    simp only [List.foldl_cons]
    have hJ' : ∀ s x, x ∈ l → J s → J (h s x) := fun s x hx => hJ s x (List.mem_cons_of_mem _ hx)
    have hQ' : ∀ s x, x ∈ l → J s → Q s → Q (h s x) :=
      fun s x hx => hQ s x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.1 hx₀ with rfl | hx
    · refine foldl_inv h (fun s => J s ∧ Q s) (fun s x hx hs => ⟨hJ' s x hx hs.1,
        hQ' s x hx hs.1 hs.2⟩) ⟨hJ s x₀ List.mem_cons_self hs, h₀ s hs⟩ |>.2
    · exact ih hJ' hQ' hx (hJ s y List.mem_cons_self hs)

/-- **Crossing.** If every handler that takes a counter from below `N` to at least `N` establishes
`Q` (which is then preserved), then a list taking the counter from below `N`
to at least `N` establishes `Q`. -/
theorem foldl_cross (h : α → β → α) (J Q : α → Prop) (cnt : α → ℕ) (N : ℕ) {l : List β}
    (hJ : ∀ s x, x ∈ l → J s → J (h s x)) (hQ : ∀ s x, x ∈ l → J s → Q s → Q (h s x))
    (hcross : ∀ s x, x ∈ l → J s → cnt s < N → N ≤ cnt (h s x) → Q (h s x))
    {s : α} (hs : J s) (hlt : cnt s < N) (hge : N ≤ cnt (l.foldl h s)) : Q (l.foldl h s) := by
  have := foldl_inv h (fun s => J s ∧ (Q s ∨ cnt s < N)) (l := l) (fun s x hx ⟨h1, h2⟩ => by
    refine ⟨hJ s x hx h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl (hQ s x hx h1 h2)
    · by_cases h3 : N ≤ cnt (h s x)
      · exact Or.inl (hcross s x hx h1 h2 h3)
      · exact Or.inr (by omega)) ⟨hs, Or.inr hlt⟩
  rcases this.2 with h | h
  · exact h
  · omega

end Fold

/-! ### Growth of the local state -/

/-- The monotone components of the state only grow from `s` to `s'`. -/
structure Grows (s s' : St P V) : Prop where
  bal : s.bal ≤ s'.bal
  initVal : s.initVal ≠ none → s'.initVal ≠ none
  val : s.val ≠ none → s'.val ≠ none
  decided : s.decided ≠ none → s'.decided ≠ none
  twoBs : ∀ x ∈ s.twoBs, x ∈ s'.twoBs
  oneBs : ∀ x ∈ s.oneBs, x ∈ s'.oneBs
  out : s.out <+: s'.out

theorem Grows.refl (s : St P V) : Grows s s :=
  ⟨le_rfl, id, id, id, fun _ h => h, fun _ h => h, List.prefix_refl _⟩

theorem Grows.trans {s s' s'' : St P V} (h : Grows s s') (h' : Grows s' s'') : Grows s s'' :=
  ⟨h.bal.trans h'.bal, h'.initVal ∘ h.initVal, h'.val ∘ h.val, h'.decided ∘ h.decided,
    fun x hx => h'.twoBs x (h.twoBs x hx), fun x hx => h'.oneBs x (h.oneBs x hx),
    h.out.trans h'.out⟩

section Handlers

variable (c : Cfg P) (p : P)

theorem Grows.of_eq {s s' : St P V} (h : s = s') : Grows s s' := h ▸ Grows.refl s

theorem grows_lead (b : ℕ) (s : St P V) : Grows s (lead c b s) := by
  unfold lead
  split
  · exact ⟨le_rfl, id, id, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
  · exact Grows.refl s

theorem grows_decideV (v : V) (s : St P V) : Grows s (decideV v s) :=
  ⟨le_rfl, id, by simp [decideV], by simp [decideV], fun _ h => h, fun _ h => h,
    List.prefix_append _ _⟩

theorem tryDecide_cases (s : St P V) :
    tryDecide c p s = s ∨ ∃ v, tryDecide c p s = decideV v s := by
  unfold tryDecide
  split_ifs
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem grows_tryDecide (s : St P V) : Grows s (tryDecide c p s) := by
  rcases tryDecide_cases c p s with h | ⟨v, h⟩ <;> rw [h]
  · exact Grows.refl s
  · exact grows_decideV v s

theorem grows_handleRaw (s : St P V) (qm : P × Msg P V) : Grows s (handleRaw c s qm) := by
  obtain ⟨q, m⟩ := qm
  cases m with
  | propose v =>
    simp only [handleRaw, onPropose]
    split_ifs with h
    · exact ⟨le_rfl, id, by simp, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
    · exact Grows.refl s
  | twoB b v =>
    exact ⟨le_rfl, id, id, id, fun _ h => by simp [handleRaw, onTwoB, h], fun _ h => h,
      List.prefix_refl _⟩
  | decide b v => exact ⟨le_rfl, id, by simp [handleRaw, onDecide], by simp [handleRaw, onDecide],
      fun _ h => h,
      fun _ h => h, List.prefix_refl _⟩
  | oneA b =>
    simp only [handleRaw, onOneA]
    split_ifs with h
    · exact ⟨h.le, id, id, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
    · exact Grows.refl s
  | oneB b d =>
    simp only [handleRaw, onOneB]
    have hg : Grows s { s with oneBs := s.oneBs ++ [(q, b, d)] } :=
      ⟨le_rfl, id, id, id, fun _ h => h, fun _ h => by simp [h], List.prefix_refl _⟩
    split_ifs
    · exact Grows.refl s
    · exact hg.trans (grows_lead c b _)
    · exact hg
  | twoA b v =>
    simp only [handleRaw, onTwoA]
    split_ifs with h
    · exact ⟨h, id, by simp, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
    · exact Grows.refl s

theorem grows_handle (s : St P V) (qm : P × Msg P V) : Grows s (handle c p s qm) :=
  (grows_handleRaw c s qm).trans (grows_tryDecide c p _)

theorem grows_foldl (s : St P V) (l : List (P × Msg P V)) : Grows s (l.foldl (handle c p) s) := by
  induction l generalizing s with
  | nil => exact Grows.refl s
  | cons x l ih => exact (grows_handle c p s x).trans (ih _)

theorem grows_timer (τ : ℕ) (s : St P V) : Grows s (timer c p τ s) := by
  unfold timer
  split_ifs
  · exact ⟨le_rfl, id, id, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
  · exact Grows.refl s

theorem grows_invoke (inv : Option V) (s : St P V) : Grows s (invoke inv s) := by
  cases inv with
  | none => exact Grows.refl s
  | some v =>
    simp only [invoke, onInv]
    split_ifs
    · exact ⟨le_rfl, by simp, id, id, fun _ h => h, fun _ h => h, List.prefix_append _ _⟩
    · exact Grows.refl s

/-- A step only grows the state, except for the outbox, which is cleared first. -/
theorem grows_stepFn (τ : ℕ) (s : St P V) (inv : Option V) (l : List (P × Msg P V)) :
    Grows { s with out := [] } (stepFn c p τ s inv l) :=
  ((grows_invoke inv _).trans (grows_foldl c p _ l)).trans (grows_timer c p τ _)

theorem stepFn_bal_ge (τ : ℕ) (s : St P V) (inv : Option V) (l : List (P × Msg P V)) :
    s.bal ≤ (stepFn c p τ s inv l).bal := (grows_stepFn c p τ s inv l).bal

/-- The outbox after a step: the messages produced by the handlers. -/
theorem out_stepFn (τ : ℕ) (s : St P V) (inv : Option V) (l : List (P × Msg P V)) :
    (stepFn c p τ s inv l).out =
      (timer c p τ (l.foldl (handle c p) (invoke inv { s with out := [] }))).out := rfl

/-! ### No pending decision -/

/-- A process that has not decided has no enabled decision handler (line 9). -/
def NoPending (s : St P V) : Prop :=
  s.decided = none → ∀ x ∈ s.twoBs, ¬ (x.2.1 = s.bal ∧ canDecide c p s s.bal x.2.2 = true)

theorem noPending_tryDecide (s : St P V) : NoPending c p (tryDecide c p s) := by
  unfold tryDecide
  by_cases h : s.decided = none
  · simp only [h, ite_true]
    split
    · intro hd; simp [decideV] at hd
    · rename_i hf
      rw [List.find?_eq_none] at hf
      intro _ x hx ⟨h1, h2⟩
      exact hf x hx (by simp [h1, h2])
  · simp only [h, ite_false]
    intro hd; exact absurd hd h

theorem noPending_handle (s : St P V) (qm : P × Msg P V) : NoPending c p (handle c p s qm) :=
  noPending_tryDecide c p _

theorem noPending_foldl {s : St P V} (hs : NoPending c p s) (l : List (P × Msg P V)) :
    NoPending c p (l.foldl (handle c p) s) :=
  foldl_inv _ _ (fun _ _ _ _ => noPending_handle c p _ _) hs

theorem canDecide_congr {s s' : St P V} (h1 : s.twoBs = s'.twoBs) (h2 : s.val = s'.val) (b : ℕ)
    (v : V) : canDecide c p s b v = canDecide c p s' b v := by
  simp [canDecide, senders2B, h1, h2]

theorem noPending_congr {s s' : St P V} (h1 : s.twoBs = s'.twoBs) (h2 : s.val = s'.val)
    (h3 : s.bal = s'.bal) (h4 : s.decided = s'.decided) (h : NoPending c p s) :
    NoPending c p s' := by
  intro hd x hx
  rw [← h3, ← canDecide_congr c p h1 h2]
  exact h (h4 ▸ hd) x (h1 ▸ hx)

theorem noPending_timer (τ : ℕ) {s : St P V} (h : NoPending c p s) :
    NoPending c p (timer c p τ s) := by
  unfold timer; split_ifs
  · exact noPending_congr c p rfl rfl rfl rfl h
  · exact h

theorem noPending_invoke (inv : Option V) {s : St P V} (h : NoPending c p s) :
    NoPending c p (invoke inv s) := by
  cases inv with
  | none => exact h
  | some v =>
    simp only [invoke, onInv]; split_ifs
    · exact noPending_congr c p rfl rfl rfl rfl h
    · exact h

theorem noPending_stepFn (τ : ℕ) {s : St P V} (h : NoPending c p s) (inv : Option V)
    (l : List (P × Msg P V)) : NoPending c p (stepFn c p τ s inv l) :=
  noPending_timer c p τ (noPending_foldl c p (noPending_invoke c p inv
    (noPending_congr c p (s' := { s with out := [] }) rfl rfl rfl rfl h)) l)

/-- If a process has not decided, no `2B(bal, v)` quorum satisfying line 10 has been received. -/
theorem decided_of_noPending {s : St P V} (h : NoPending c p s) {x : P × ℕ × V}
    (hx : x ∈ s.twoBs) (hb : x.2.1 = s.bal) (hc : canDecide c p s s.bal x.2.2 = true) :
    s.decided ≠ none := fun hd => h hd x hx ⟨hb, hc⟩

end Handlers

/-! ### The proposal of lines 26–38 -/

theorem foldr_max_mem {l : List ℕ} (h : 0 < l.foldr max 0) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons] at h ⊢
    rcases le_total a (l.foldr max 0) with h' | h'
    · rw [max_eq_right h'] at h ⊢
      exact List.mem_cons_of_mem _ (ih h)
    · rw [max_eq_left h']; exact List.mem_cons_self

/-- The proposal is not `⊥` if the fallback is not `⊥` and every reported vote in a slow
ballot carries a value. -/
theorem proposal_ne_none (n f e : ℕ) {Q : List (P × OneB P V)} {fb : Option V} (hfb : fb ≠ none)
    (hQ : ∀ x ∈ Q, x.2.vbal ≠ 0 → x.2.val ≠ none) : proposal n f e Q fb ≠ none := by
  unfold proposal
  split
  · simp
  · simp only
    split_ifs with h
    · have hm := foldr_max_mem h
      rw [List.mem_map] at hm
      obtain ⟨y, hy, hyv⟩ := hm
      obtain ⟨z, hz⟩ : ∃ z, (Q.find? fun x => x.2.vbal = (Q.map fun x => x.2.vbal).foldr max 0) =
          some z := by
        rw [← Option.isSome_iff_exists, List.find?_isSome]
        exact ⟨y, hy, by simp [hyv]⟩
      have hz1 := List.mem_of_find?_eq_some hz
      have hz2 := List.find?_some hz
      simp only [decide_eq_true_eq] at hz2
      rw [hz]
      have := hQ z hz1 (by omega)
      simpa [Option.bind] using this
    · split
      · simp
      · split
        · simp
        · exact hfb

/-- The proposal is a decision or a vote reported in `Q`, or the fallback. -/
theorem proposal_mem (n f e : ℕ) {Q : List (P × OneB P V)} {fb : Option V} {v : V}
    (h : proposal n f e Q fb = some v) :
    (∃ x ∈ Q, x.2.dec = some v ∨ x.2.val = some v) ∨ fb = some v := by
  unfold proposal at h
  split at h
  · rename_i d hd
    obtain ⟨x, hx, hxd⟩ := List.exists_of_findSome?_eq_some hd
    cases h
    exact Or.inl ⟨x, hx, Or.inl hxd⟩
  · simp only at h
    split_ifs at h
    · obtain ⟨z, hz, hzv⟩ := Option.bind_eq_some_iff.1 h
      exact Or.inl ⟨z, List.mem_of_find?_eq_some hz, Or.inr hzv⟩
    · split at h
      · rename_i w hw
        cases h
        have := List.mem_of_mem_filter (List.max?_mem hw)
        obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.1 this
        exact Or.inl ⟨x, List.mem_of_mem_filter hx, Or.inr hxv⟩
      · split at h
        · rename_i w hw
          cases h
          have := List.mem_of_mem_filter (List.max?_mem hw)
          obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.1 this
          exact Or.inl ⟨x, List.mem_of_mem_filter hx, Or.inr hxv⟩
        · exact Or.inr h

end TwoStepConsensus.Impl
