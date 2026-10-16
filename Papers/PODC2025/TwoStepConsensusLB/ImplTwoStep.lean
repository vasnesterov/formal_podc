import Papers.PODC2025.TwoStepConsensusLB.ImplTermination

/-!
# The protocol of Figure 1 is `e`-two-step (Definitions 4 and 5)

In an `E`-faulty synchronous run in which the processes are ordered so that the `Propose`
message of a chosen process `p ∉ E` is processed first (`pFirst p`), every other correct process
votes for `p`'s value `v` at time `1` (it has not voted yet and `v` passes line 6), and `p` itself
never votes for another value. At time `2`, `p` receives `2B(0, v)` from all `n - e - 1` other
correct processes and decides on the fast path (line 10), i.e. by `2Δ` (`sync_decides`).

For Definition 4 (1) (task), `p` is a correct process with the maximal input; for (2), any `p`.
For Definition 5 (object), `p` is the given process.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus.Impl

open _root_.Cslib.CrashPartialSync

variable {P V : Type*} [Fintype P] [DecidableEq P] [LinearOrder V]

/-- Delivery order: the messages from `p` first. -/
def pFirst (p : P) : P → ℕ → List (P × Msg P V) → List (P × Msg P V) :=
  fun _ _ l => l.filter (fun qm => decide (qm.1 = p)) ++ l.filter (fun qm => !decide (qm.1 = p))

theorem pFirst_isOrder (p : P) : IsOrder (pFirst (V := V) p) :=
  fun _ _ l => List.filter_append_perm _ l

section Handlers

variable (c : Cfg P) (p : P)

@[simp] theorem tryDecide_initVal (s : St P V) : (tryDecide c p s).initVal = s.initVal := by
  rcases tryDecide_cases c p s with h | ⟨v, h⟩ <;> rw [h]; rfl

theorem handle_initVal (s : St P V) (qm : P × Msg P V) :
    (handle c p s qm).initVal = s.initVal := by
  obtain ⟨q, m⟩ := qm
  simp only [handle, tryDecide_initVal]
  cases m with
  | propose v => simp only [handleRaw, onPropose]; split_ifs <;> rfl
  | twoB b v => rfl
  | decide b v => rfl
  | oneA b => simp only [handleRaw, onOneA]; split_ifs <;> rfl
  | oneB b d =>
    simp only [handleRaw, onOneB]
    split_ifs
    · rfl
    · unfold lead; split <;> rfl
    · rfl
  | twoA b v => simp only [handleRaw, onTwoA]; split_ifs <;> rfl

/-- A process in the fast ballot without a vote accepts `Propose(v)` if `v` passes line 6. -/
theorem handle_propose_out {s : St P V} {q : P} {v : V} (hb : s.bal = 0)
    (hok : okProp c.obj s.initVal v = true)
    (hv : s.val = none ∨ (Dest.to q, Msg.twoB 0 v) ∈ s.out) :
    (Dest.to q, Msg.twoB 0 v) ∈ (handle c p s (q, .propose v)).out := by
  unfold handle
  refine (grows_tryDecide c p _).out.subset ?_
  rcases hv with hv | hv
  · simp [handleRaw, onPropose, hb, hv, hok]
  · exact (grows_handleRaw c s _).out.subset hv

/-- Invariant of the fast proposer `p` (initial value `v`) during the first rounds: it has decided,
or it has not voted for another value than `v`. -/
def FastInv (v : V) (s : St P V) : Prop := s.decided ≠ none ∨ s.val = none ∨ s.val = some v

theorem FastInv.handle {v : V} {s : St P V} (h : FastInv v s) (hi : s.initVal = some v)
    {q : P} {m : Msg P V} (hprop : ∀ w, m = .propose w → w ≤ v) (h2A : ∀ b w, m ≠ .twoA b w) :
    FastInv v (Impl.handle c p s (q, m)) := by
  have hraw : FastInv v (handleRaw c s (q, m)) := by
    cases m with
    | propose w =>
      simp only [handleRaw, onPropose]
      split_ifs with h'
      · obtain ⟨-, -, hok⟩ := h'
        rw [hi] at hok
        simp only [okProp, Bool.and_eq_true, decide_eq_true_eq] at hok
        have := hprop w rfl
        right; right; simp only [Option.some.injEq]; exact le_antisymm this hok.1
      · exact h
    | twoB b w => exact h
    | decide b w => left; simp [handleRaw, onDecide]
    | oneA b => simp only [handleRaw, onOneA]; split_ifs <;> exact h
    | oneB b d =>
      simp only [handleRaw, onOneB]
      split_ifs
      · exact h
      · unfold lead; split <;> exact h
      · exact h
    | twoA b w => exact absurd rfl (h2A b w)
  unfold Impl.handle
  rcases tryDecide_cases c p (handleRaw c s (q, m)) with h' | ⟨w, h'⟩ <;> rw [h']
  · exact hraw
  · left; simp [decideV]

end Handlers

section Sync

variable {c : Cfg P} {R : Run P V (Msg P V)}

/-- The state after the step at time `0`: only the invocation has been processed. -/
theorem st_one (hR : IsOrder R.ord) {x : P} (hx : R.alive x 0) :
    R.st (fig1 c) 1 x = invoke (R.inv x 0) {} := by
  rw [Run.st_succ_of_alive _ _ hx]
  have : R.inbox (fig1 c) x 0 = [] := by
    unfold Run.inbox; rw [Run.canon_zero, hR.nil]
  rw [this]
  simp only [fig1, stepFn, List.foldl_nil, Run.st_zero]
  unfold timer
  rw [ite_eq_right (by simp)]

variable {E : Finset P} {inv : P → ℕ → Option V} {p : P} {v : V}

/-- **Fast path in a synchronous run.** In the `E`-faulty synchronous run where the messages of
`p ∉ E` are processed first, if `p` proposes `v` at time `0`, nobody invokes later, and every other
correct process's own proposal lets it accept `v` (line 6), then `p` decides at its step at time
`2` (it exhibits a decision at time `3`, i.e. at `2Δ`). -/
theorem sync_decides (c : Cfg P) (hE : E.card ≤ c.e) (hn : c.e + 2 ≤ Fintype.card P) (hp : p ∉ E)
    (hpv : inv p 0 = some v)
    (hlate : ∀ x τ, inv x (τ + 1) = none)
    (hok : ∀ x ∉ E, x ≠ p → okProp c.obj (inv x 0) v = true) :
    ((syncRun E inv (pFirst p)).st (fig1 c) 3 p).decided ≠ none := by
  set R : Run P V (Msg P V) := syncRun E inv (pFirst p) with hRdef
  have hord : IsOrder R.ord := pFirst_isOrder p
  have halive : ∀ x ∉ E, ∀ τ, R.alive x τ := fun x hx τ =>
    R.alive_of_crash_none (syncRun_crash_of_not_mem hx) τ
  have hcrash : ∀ x ∉ E, R.crash x = none := fun x hx => syncRun_crash_of_not_mem hx
  have hinv0 : ∀ x τ, R.alive x τ → ∀ w, R.inv x τ = some w → τ = 0 := by
    intro x τ _ w h
    rcases τ with _ | τ
    · rfl
    · simp [R, syncRun, hlate] at h
  -- every proposed value is at most `v`
  have hle : ∀ τ w, Invoked R τ w → w ≤ v := by
    rintro τ w ⟨x, τ₁, -, hal, hw⟩
    obtain rfl := hinv0 x τ₁ hal w hw
    have hx : x ∉ E := by
      intro hx; simp [R, Run.alive, syncRun, hx] at hal
    by_cases hxp : x = p
    · subst hxp; change inv x 0 = some w at hw; rw [hpv] at hw; cases hw; exact le_rfl
    · have := hok x hx hxp
      change R.inv x 0 = some w at hw
      simp only [R, syncRun] at hw
      rw [hw] at this
      simp only [okProp, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
  -- the states at time `1`
  have hst1 : ∀ x ∉ E, R.st (fig1 c) 1 x = invoke (inv x 0) {} := fun x hx =>
    st_one hord (halive x hx 0)
  -- the proposer's messages at time `0`
  have hout0 : ∀ x m, m ∈ R.out (fig1 c) p 0 x → m = .propose v := by
    intro x m hm
    rw [Run.out_of_alive _ _ (halive p hp 0), mem_send, hst1 p hp] at hm
    obtain ⟨d, hd, -⟩ := hm
    simp only [hpv, invoke, onInv, ite_true, List.nil_append, List.mem_singleton,
      Prod.mk.injEq] at hd
    exact hd.2
  -- every correct `x ≠ p` replies `2B(0, v)` to `p` at time `1`
  have h2B : ∀ x ∉ E, x ≠ p → (Dest.to p, Msg.twoB 0 v) ∈ (R.st (fig1 c) 2 x).out := by
    intro x hx hxp
    rw [st_succ_correct (hcrash x hx), stepFn]
    refine (grows_timer c x 1 _).out.subset ?_
    have hinbox : R.inbox (fig1 c) x 1 =
        (R.canon (fig1 c) x 1).filter (fun qm => decide (qm.1 = p)) ++
          (R.canon (fig1 c) x 1).filter (fun qm => !decide (qm.1 = p)) := rfl
    rw [hinbox, List.foldl_append]
    refine (grows_foldl c x _ _).out.subset ?_
    have hmem : (p, Msg.propose v) ∈
        (R.canon (fig1 c) x 1).filter (fun qm => decide (qm.1 = p)) := by
      refine List.mem_filter.2 ⟨(Run.mem_canon _ R).2 ⟨0, by omega, rfl, ?_⟩, by simp⟩
      rw [Run.out_of_alive _ _ (halive p hp 0), mem_send, hst1 p hp]
      refine ⟨Dest.others, ?_, by simp [Dest.incl, hxp]⟩
      simp [hpv, invoke, onInv]
    have hL1 : ∀ qm ∈ (R.canon (fig1 c) x 1).filter (fun qm => decide (qm.1 = p)),
        qm = (p, Msg.propose v) := by
      rintro ⟨q, m⟩ hqm
      obtain ⟨h1, h2⟩ := List.mem_filter.1 hqm
      simp only [decide_eq_true_eq] at h2
      subst h2
      obtain ⟨τ', hτ', -, hm⟩ := (Run.mem_canon _ R).1 h1
      obtain rfl : τ' = 0 := by omega
      rw [hout0 x m hm]
    set s₀ := invoke (R.inv x 1) { R.st (fig1 c) 1 x with out := [] }
    have hs₀ : s₀.bal = 0 ∧ okProp c.obj s₀.initVal v = true ∧ s₀.val = none := by
      have hi : R.inv x 1 = none := hlate x 0
      simp only [s₀, hi, invoke, hst1 x hx]
      rcases h : inv x 0 with _ | w
      · simp [okProp]
      · have := hok x hx hxp
        rw [h] at this
        simp [onInv, this]
    refine foldl_mem (handle c x)
      (fun s => s.bal = 0 ∧ okProp c.obj s.initVal v = true ∧
        (s.val = none ∨ (Dest.to p, Msg.twoB 0 v) ∈ s.out))
      (fun s => (Dest.to p, Msg.twoB 0 v) ∈ s.out) ?_ ?_ hmem ?_ ⟨hs₀.1, hs₀.2.1, Or.inl hs₀.2.2⟩
    · intro s qm hqm ⟨h1, h2, h3⟩
      obtain rfl := hL1 qm hqm
      refine ⟨?_, by rw [handle_initVal]; exact h2, Or.inr (handle_propose_out c x h1 h2 h3)⟩
      rcases handle_bal_cases c x s p (.propose v) with h | ⟨_, h, -⟩ | ⟨_, _, h, -⟩
      · rw [h, h1]
      · cases h
      · cases h
    · intro s qm _ _ hs
      exact (grows_handle c x s qm).out.subset hs
    · intro s ⟨h1, h2, h3⟩
      exact handle_propose_out c x h1 h2 h3
  -- the proposer keeps `FastInv v` until time `3`
  have hi : ∀ τ, 1 ≤ τ → (R.st (fig1 c) τ p).initVal = some v := by
    intro τ hτ
    have h1 : (R.st (fig1 c) 1 p).initVal = some v := by
      rw [hst1 p hp]; simp [hpv, invoke, onInv]
    induction τ, hτ using Nat.le_induction with
    | base => exact h1
    | succ τ hτ ih =>
      rw [st_succ_correct (hcrash p hp), stepFn]
      have hl : R.inv p τ = none := by
        obtain ⟨τ, rfl⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
        exact hlate p τ
      rw [hl]
      have : ∀ s : St P V, (timer c p τ s).initVal = s.initVal := by
        intro s; unfold timer; split_ifs <;> rfl
      rw [this, foldl_inv (handle c p) (fun s => s.initVal = some v) (fun s qm _ h => by
        rw [handle_initVal]; exact h) (s := invoke none { R.st (fig1 c) τ p with out := [] }) ih]
  have hfast : ∀ τ ≤ 3, FastInv v (R.st (fig1 c) τ p) := by
    intro τ hτ
    induction τ with
    | zero => right; left; rfl
    | succ τ ih =>
      have ih := ih (by omega)
      rw [st_succ_correct (hcrash p hp), stepFn]
      have hT : ∀ s : St P V, FastInv v s → FastInv v (timer c p τ s) := by
        intro s hs; unfold timer; split_ifs
        · exact hs
        · exact hs
      apply hT
      rcases τ with _ | τ
      · -- time `0`: empty inbox
        have : R.inbox (fig1 c) p 0 = [] := by
          unfold Run.inbox; rw [Run.canon_zero, hord.nil]
        have hpv' : R.inv p 0 = some v := hpv
        rw [this, List.foldl_nil, hpv']
        right; left; simp [invoke, onInv, fig1]
      · have hl : R.inv p (τ + 1) = none := hlate p τ
        rw [hl]
        refine (foldl_inv (handle c p) (fun s => FastInv v s ∧ s.initVal = some v)
          (s := invoke none { R.st (fig1 c) (τ + 1) p with out := [] }) ?_
          ⟨ih, hi (τ + 1) (by omega)⟩).1
        rintro s ⟨q, m⟩ hqm ⟨h1, h2⟩
        refine ⟨h1.handle c p h2 ?_ ?_, by rw [handle_initVal]; exact h2⟩
        · rintro w rfl
          exact hle _ w (values_inbox hord hqm)
        · rintro b w rfl
          obtain ⟨τ', hτ', hm⟩ := timing_inbox hord hqm
          simp only [MsgT] at hm
          unfold ballotStart at hm; omega
  -- at time `2`, `p` receives `2B(0, v)` from all other correct processes
  have hmem : ∀ x ∉ E, x ≠ p → (x, 0, v) ∈ (R.st (fig1 c) 3 p).twoBs := by
    intro x hx hxp
    have hdel : (x, Msg.twoB 0 v) ∈ R.inbox (fig1 c) p 2 := by
      rw [Run.mem_inbox _ R hord]
      refine ⟨1, by omega, rfl, ?_⟩
      rw [Run.out_of_alive _ _ (halive x hx 1), mem_send]
      exact ⟨_, h2B x hx hxp, by simp [Dest.incl]⟩
    exact step_mem (hcrash p hp) (fun _ => True) _ (fun s s' h hs => h.twoBs _ hs) trivial
      (fun _ _ _ _ => trivial) hdel (fun s _ => handle_twoB_mem c p s x 0 v)
  have hbal : (R.st (fig1 c) 3 p).bal = 0 := by
    rcases (timing_st (c := c) hord 3 p).1 with h | h
    · exact h
    · unfold ballotStart at h; omega
  intro hd
  -- the fast-path condition of line 10 holds
  have hcard : Fintype.card P - c.e ≤ (insert p (senders2B (R.st (fig1 c) 3 p) 0 v)).card := by
    have hsub : Eᶜ ⊆ insert p (senders2B (R.st (fig1 c) 3 p) 0 v) := by
      intro x hx
      rw [Finset.mem_compl] at hx
      by_cases hxp : x = p
      · simp [hxp]
      · refine Finset.mem_insert_of_mem ?_
        simp only [senders2B, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨(x, 0, v), ⟨hmem x hx hxp, by simp⟩, rfl⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_compl] at this
    omega
  have hval : (R.st (fig1 c) 3 p).val = none ∨ (R.st (fig1 c) 3 p).val = some v := by
    rcases hfast 3 le_rfl with h | h
    · exact absurd hd h
    · exact h
  -- some other process is correct (`n - e ≥ 2`)
  obtain ⟨x, hx, hxp⟩ : ∃ x ∉ E, x ≠ p := by
    by_contra hne
    push Not at hne
    have : Eᶜ ⊆ {p} := fun x hx => by
      rw [Finset.mem_compl] at hx; simp [hne x hx]
    have := Finset.card_le_card this
    rw [Finset.card_compl, Finset.card_singleton] at this
    omega
  refine noPending_st (c := c) (R := R) 3 p hd (x, 0, v) (hmem x hx hxp) ⟨hbal.symm, ?_⟩
  · rw [hbal]
    simp [canDecide, hcard, hval]

end Sync

theorem decidedBy2_of {c : Cfg P} {R : Run P V (Msg P V)} {p : P}
    (h : (R.st (fig1 c) 3 p).decided ≠ none) : R.DecidedBy2 (fig1 c) p := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  exact ⟨3, le_rfl, w, hw⟩

/-- **The task version of Figure 1 is `e`-two-step** (Definition 4; §3 and §C.2), for
`n ≥ e + 2` (which follows from `n ≥ max (2e + f) (2f + 1)` except in the degenerate case
`n = 1`). For (1), the fast proposer is a correct process with the maximal input; for (2),
any correct process. -/
theorem task_twoStep (c : Cfg P) (hobj : c.obj = false) (hn : c.e + 2 ≤ Fintype.card P) :
    TwoStepTask (fig1 (V := V) c) c.e := by
  intro E hE
  have hlate : ∀ (I : P → V) x τ, taskInv I x (τ + 1) = none := fun I x τ => by simp [taskInv]
  refine ⟨fun I => ?_, fun I hI p hp => ?_⟩
  · obtain ⟨p, hp, hmax⟩ := Eᶜ.exists_max_image I (by
      rw [← Finset.card_pos, Finset.card_compl]; omega)
    rw [Finset.mem_compl] at hp
    refine ⟨pFirst p, pFirst_isOrder p, p, decidedBy2_of ?_⟩
    refine sync_decides c hE.le hn hp (v := I p) (by simp [taskInv]) (hlate I) fun x hx _ => ?_
    simp [taskInv, okProp, hobj, hmax x (Finset.mem_compl.2 hx)]
  · refine ⟨pFirst p, pFirst_isOrder p, decidedBy2_of ?_⟩
    refine sync_decides c hE.le hn hp (v := I p) (by simp [taskInv]) (hlate I) fun x hx _ => ?_
    simp [taskInv, okProp, hI x hx p hp]

theorem respondedBy2_of {c : Cfg P} {R : Run P V (Msg P V)} {p : P} {v : V}
    (hinv : R.inv p 0 = some v)
    (h : (R.st (fig1 c) 3 p).decided ≠ none) : R.RespondedBy2 (fig1 c) p := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  exact ⟨3, le_rfl, w, ⟨0, by omega, by simp [hinv]⟩, hw⟩

/-- **The object version of Figure 1 is `e`-two-step** (Definition 5; §C.3), for `n ≥ e + 2`. In
(1) the single invocation is at time `0`. -/
theorem object_twoStep (c : Cfg P) (hn : c.e + 2 ≤ Fintype.card P) :
    TwoStepObject (fig1 (V := V) c) c.e := by
  intro E hE
  refine ⟨fun v p hp => ⟨0, pFirst p, pFirst_isOrder p, ?_⟩, fun v p hp =>
    ⟨pFirst p, pFirst_isOrder p, ?_⟩⟩
  · refine respondedBy2_of (v := v) (by simp [syncRun, singleInv]) ?_
    refine sync_decides c hE.le hn hp (v := v) (by simp [singleInv])
      (fun x τ => by simp [singleInv])
      fun x _ hxp => ?_
    simp [singleInv, hxp, okProp]
  · refine respondedBy2_of (v := v) (by simp [syncRun, allInv, hp]) ?_
    refine sync_decides c hE.le hn hp (v := v) (by simp [allInv, hp]) (fun x τ => by simp [allInv])
      fun x hx _ => ?_
    simp [allInv, hx, okProp]

end TwoStepConsensus.Impl
