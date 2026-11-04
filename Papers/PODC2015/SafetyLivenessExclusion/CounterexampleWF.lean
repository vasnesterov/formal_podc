import Papers.PODC2015.SafetyLivenessExclusion.Counterexample

/-!
# The counterexample to Theorem 4.9 with `Lmax` = wait-freedom

`Counterexample.lean` refutes Theorem 4.9 with an ad-hoc `Lmax`. Here `Lmax` is the paper's own
example of a strongest liveness requirement, **wait-freedom** (`WaitFree`: every invocation of a
process that does not crash eventually returns). With the same safety property `S` and the same
implementation `Is`:

* every fair history of `Is` is wait-free, except the finite histories `Y` in which `p₁`
  crashed (possibly after invoking), `p₀` invoked once and waits forever, and nobody received a
  response (`Is_fairH_subset`, a liveness analysis of `Is` under the paper's fairness);
* every history of `Y` is fair for *every* valid implementation ensuring `S`
  (`Y_subset_fairH`): after it, the state is the same as after `crash₁ · inv₀` (the inputs of
  `p₁` only touch `p₁`'s local state, which the crash erases), and there no answer to `p₀` is
  allowed by `S`.

Hence `WaitFree ∪ Y` is the strongest liveness property that does not exclude `S`, and it is not
`WaitFree` (`theorem_4_9_false_waitFree`).
-/

namespace Podc.SafetyLivenessExclusion.Counterexample

open Hist Impl

/-! ## Input-only histories lead to a canonical state -/

section Canon

variable {I : Impl 2 Unit Unit} (c₀ : I.Cfg) (Q' : Fin 2 → I.Q)

/-- The state reached from `c₀` by input-only histories with final statuses `σ`. -/
def canon (σ : Fin 2 → PStat) : I.Cfg :=
  ⟨fun i => match σ i with
    | .idle => c₀.loc i
    | .pend => some (Q' i)
    | .dead => none, c₀.mem⟩

theorem run_canon (hQ : ∀ i, ∃ q, c₀.loc i = some q ∧ I.invT i q () (Q' i))
    {l : List E} (hl : ∀ e ∈ l, ¬ e.IsRes) {σ : Fin 2 → PStat} (hσ : runStat l = some σ) :
    I.Run (canon c₀ Q' (fun _ => .idle)) (l.map Act.ext) (canon c₀ Q' σ) := by
  induction l using List.reverseRecOn generalizing σ with
  | nil =>
    simp only [runStat_nil, Option.some.injEq] at hσ
    subst hσ; exact .nil _
  | append_singleton l e ih =>
    obtain ⟨σ₀, h₀, he⟩ := runStat_append_eq_some.1 hσ
    have hr := ih (fun e h => hl e (List.mem_append_left _ h)) h₀
    rw [List.map_append]
    refine hr.snoc ?_
    cases e with
    | inv i x =>
      cases x
      obtain ⟨hi, rfl⟩ := stepStat_inv.1 he
      obtain ⟨q, hq, hq'⟩ := hQ i
      have hloc : (canon c₀ Q' σ₀).loc i = some q := by simp [canon, hi, hq]
      have heq : canon c₀ Q' (Function.update σ₀ i .pend) =
          ⟨Function.update (canon c₀ Q' σ₀).loc i (some (Q' i)), (canon c₀ Q' σ₀).mem⟩ := by
        simp only [canon, Impl.Cfg.mk.injEq, and_true]
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [heq]; exact Trans.inv hloc hq'
    | res i r => exact absurd trivial (hl (.res i r) (by simp))
    | crash i =>
      obtain ⟨hi, rfl⟩ := stepStat_crash.1 he
      obtain ⟨q, hq, -⟩ := hQ i
      have hloc : ∃ q', (canon c₀ Q' σ₀).loc i = some q' := by
        simp only [canon]
        cases h : σ₀ i
        · exact ⟨q, hq⟩
        · exact ⟨_, rfl⟩
        · exact absurd h hi
      obtain ⟨q', hq'⟩ := hloc
      have heq : canon c₀ Q' (Function.update σ₀ i .dead) =
          ⟨Function.update (canon c₀ Q' σ₀).loc i none, (canon c₀ Q' σ₀).mem⟩ := by
        simp only [canon, Impl.Cfg.mk.injEq, and_true]
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      rw [heq]; exact Trans.crash hq'

theorem canon_idle : canon c₀ Q' (fun _ => .idle) = c₀ := by
  obtain ⟨loc, mem⟩ := c₀
  rfl

end Canon

/-- The statuses after `crash₁ · inv₀`. -/
def σh0 : Fin 2 → PStat := Function.update (Function.update (fun _ => .idle) 1 .dead) 0 .pend

theorem runStat_h0 : runStat h0 = some σh0 := by decide

/-- The histories `Y`: `p₁` crashed (possibly after invoking), `p₀` invoked and waits, and there
is no response. -/
def Y : Set (Hist E) :=
  {h | ∃ l, h = .fin l ∧ (∀ e ∈ l, ¬ e.IsRes) ∧ runStat l = some σh0}

/-- Every history of `Y` is fair for every valid implementation ensuring `S`. -/
theorem Y_subset_fairH {I : Impl 2 Unit Unit} (hV : I.Valid) (hS : I.EnsuresS S) :
    Y ⊆ I.fairH := by
  rintro _ ⟨l, rfl, hl, hσ⟩
  obtain ⟨c₀, hc₀⟩ := hV.1
  have hQ : ∀ i, ∃ q', ∃ q, c₀.loc i = some q ∧ I.invT i q () q' := by
    intro i
    obtain ⟨c', ht⟩ := hV.2.2 c₀ [] (Reach.init hc₀) (fun _ => .idle) rfl i rfl ()
    cases ht with
    | inv hq ht => exact ⟨_, _, hq, ht⟩
  choose Q' hQ' using hQ
  have h1 : I.Reach (canon c₀ Q' σh0) l := by
    have := run_canon c₀ Q' hQ' hl hσ
    rw [canon_idle] at this
    exact ⟨c₀, _, hc₀, this, by simp⟩
  have h2 : I.Reach (canon c₀ Q' σh0) h0 := by
    have := run_canon c₀ Q' hQ' (l := h0) (by simp [h0, Ext.IsRes]) runStat_h0
    rw [canon_idle] at this
    exact ⟨c₀, _, hc₀, this, by simp⟩
  exact fin_mem_fairH_of_quiet h1 0 (quiet_h0 hS h2)

/-! ## Wait-freedom -/

/-- Wait-freedom as a set of histories: well-formed, and every pending invocation is eventually
followed by a response or a crash of its process. -/
def WaitFree : Set (Hist E) :=
  {h | h ∈ U ∧ ∀ l, FinPrefix l h → ∀ σ, runStat l = some σ → ∀ i, σ i = .pend →
    ∃ l' σ', FinPrefix l' h ∧ l <+: l' ∧ runStat l' = some σ' ∧ σ' i ≠ .pend}

theorem waitFree_assumptions : LmaxAssumptions WaitFree where
  subset_U _ h := h.1
  ext l hl := by
    obtain ⟨σ, hσ⟩ := hl.exists
    -- crash every process that is still alive
    let t : List E := (if σ 0 = .dead then [] else [.crash 0]) ++
      (if σ 1 = .dead then [] else [.crash 1])
    have hdead : ∃ σ', runStat (l ++ t) = some σ' ∧ ∀ i, σ' i = .dead := by
      by_cases h0 : σ 0 = .dead <;> by_cases h1 : σ 1 = .dead
      · refine ⟨σ, by simp [t, h0, h1, hσ], fun i => ?_⟩
        rcases fin2_cases i with rfl | rfl <;> assumption
      · refine ⟨Function.update σ 1 .dead, ?_, fun i => ?_⟩
        · simp only [t, h0, h1, ite_true, ite_false, List.nil_append]
          rw [runStat_append, hσ]; simp [stepStat, h1]
        · rcases fin2_cases i with rfl | rfl
          · rw [upd10]; exact h0
          · simp
      · refine ⟨Function.update σ 0 .dead, ?_, fun i => ?_⟩
        · simp only [t, h0, h1, ite_true, ite_false, List.append_nil]
          rw [runStat_append, hσ]; simp [stepStat, h0]
        · rcases fin2_cases i with rfl | rfl
          · simp
          · rw [upd01]; exact h1
      · refine ⟨Function.update (Function.update σ 0 .dead) 1 .dead, ?_, fun i => ?_⟩
        · simp only [t, h0, h1, ite_false, List.singleton_append]
          rw [show l ++ [Ext.crash 0, Ext.crash 1] = l ++ [Ext.crash 0] ++ [Ext.crash 1] by simp,
            runStat_append, runStat_append, hσ]
          simp [stepStat, h0, h1]
        · rcases fin2_cases i with rfl | rfl
          · rw [upd10]; simp
          · simp
    obtain ⟨σ', hσ', hd⟩ := hdead
    refine ⟨.fin (l ++ t), ⟨fin_mem_U.2 (by simp [WF, hσ']), ?_⟩, List.prefix_append _ _⟩
    intro l₁ hl₁ σ₁ hσ₁ i hi
    exact ⟨l ++ t, σ', List.prefix_refl _, hl₁, hσ', by rw [hd i]; decide⟩

theorem h0_not_waitFree : Hist.fin h0 ∉ WaitFree := by
  rintro ⟨-, h⟩
  obtain ⟨l', σ', hl', hpre, hσ', hne⟩ := h h0 (List.prefix_refl _) σh0 runStat_h0 0 (by decide)
  have : l' = h0 := List.IsPrefix.eq_of_length hl' (le_antisymm hl'.length_le hpre.length_le)
  subst this
  rw [runStat_h0] at hσ'; cases hσ'
  exact hne (by decide)

/-! ## Liveness analysis of `Is` -/

section Liveness

-- CSLib candidate (Foundations/Data/Nat/Descent)
/-- A potential that never increases and strictly decreases infinitely often is impossible. -/
theorem no_infinite_descent {φ : ℕ → ℕ} {K : ℕ} {P : ℕ → Prop}
    (hanti : ∀ k ≥ K, φ (k + 1) ≤ φ k) (hstrict : ∀ k ≥ K, P k → φ (k + 1) < φ k)
    (hinf : ∀ K', ∃ k ≥ K', P k) : False := by
  have mono : ∀ k ≥ K, ∀ d, φ (k + d) ≤ φ k := by
    intro k hk d
    induction d with
    | zero => simp
    | succ d ih => exact (hanti (k + d) (by omega)).trans ih
  have key : ∀ j, ∃ k ≥ K, φ k + j ≤ φ K := by
    intro j
    induction j with
    | zero => exact ⟨K, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨k, hk, hφ⟩ := ih
      obtain ⟨k', hk', hP⟩ := hinf k
      have h1 := hstrict k' (by omega) hP
      have h2 := mono k hk (k' - k)
      rw [show k + (k' - k) = k' by omega] at h2
      exact ⟨k' + 1, by omega, by omega⟩
  obtain ⟨k, -, hk⟩ := key (φ K + 1)
  omega

theorem Is_trans_mem {c c' : Is.Cfg} {a : Act 2 Unit Unit} (ht : Is.Trans c a c') :
    c.mem.1 ≤ c'.mem.1 ∧ (c.mem.2 = true → c'.mem.2 = true) := by
  cases ht with
  | step _ hs =>
    rcases hs with ⟨-, rfl, -⟩ | ⟨v, -, rfl, -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  | base hb =>
    have : _ = c.mem := hb
    rw [this]; simp
  | _ => simp

/-- Pending local states of `p₀`. -/
def P0pend (o : Option HQ) : Prop :=
  o = some .wRead ∨ (∃ v, o = some (.wWait v)) ∨ o = some .ready0

theorem p0pend_of_fits {o : Option HQ} (h : Fits0 o .pend) : P0pend o := by
  rcases o with _ | q
  · simp [Fits0] at h
  · cases q <;> simp_all [Fits0, P0pend]

theorem fits_of_p0pend {o : Option HQ} {s : PStat} (h : Fits0 o s) (hp : P0pend o) :
    s = .pend := by
  rcases hp with rfl | ⟨v, rfl⟩ | rfl <;> simpa [Fits0] using h

/-- Pending local states of `p₁`. -/
def P1pend (o : Option HQ) : Prop := o = some .pend1 ∨ o = some .ready1

theorem p1pend_of_fits {o : Option HQ} (h : Fits1 o .pend) : P1pend o := by
  rcases o with _ | q
  · simp [Fits1] at h
  · cases q <;> simp_all [Fits1, P1pend]

theorem fits_of_p1pend {o : Option HQ} {s : PStat} (h : Fits1 o s) (hp : P1pend o) :
    s = .pend := by
  rcases hp with rfl | rfl <;> simpa [Fits1] using h

/-- After an action of `p₀` from a pending state, `p₀` is in a pending state of a later phase,
or it responded, or it crashed. -/
theorem trans_p0 {c c' : Is.Cfg} {a : Act 2 Unit Unit} (ht : Is.Trans c a c') (ha : a.IsProc 0) :
    (c.loc 0 = some .ready0 → c'.loc 0 = some .done0 ∨ c'.loc 0 = none) ∧
    (c.loc 0 = some .wRead → c'.loc 0 = some .ready0 ∨ (∃ v, c'.loc 0 = some (.wWait v)) ∨
      c'.loc 0 = none) ∧
    (∀ v, c.loc 0 = some (.wWait v) → c'.loc 0 = some .ready0 ∨ c'.loc 0 = none) := by
  cases ht with
  | @inv i x q q' hq ht =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq]
    refine ⟨fun h => ?_, fun h => ?_, fun v h => ?_⟩ <;> rw [hq] at h <;> cases h <;>
      rcases ht with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
  | @res i r q q' hq ht =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq]
    refine ⟨fun h => ?_, fun h => ?_, fun v h => ?_⟩ <;> rw [hq] at h <;> cases h <;>
      rcases ht with ⟨h, h'⟩ | ⟨h, -⟩ <;> first | (cases h; done) | (left; exact h')
  | @crash i q hq =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp
  | @step i q q' b' hq hs =>
    simp only [Act.IsProc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq]
    refine ⟨fun h => ?_, fun h => ?_, fun v h => ?_⟩ <;> rw [hq] at h <;> cases h
    · rcases hs with ⟨h, -⟩ | ⟨v, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    · rcases hs with ⟨-, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩ | ⟨v, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · left; rfl
      · right; left; exact ⟨_, rfl⟩
      all_goals cases h
    · rcases hs with ⟨h, -⟩ | ⟨w, -, -, -, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · cases h
      · left; rfl
      all_goals cases h
  | base => simp [Act.IsProc] at ha

theorem upd10' {α : Type} (f : Fin 2 → α) (v : α) : Function.update f 1 v 0 = f 0 :=
  Function.update_of_ne (by decide) _ _

theorem trans_p1 {c c' : Is.Cfg} {a : Act 2 Unit Unit} (ht : Is.Trans c a c') (ha : a.IsProc 1) :
    (c.loc 1 = some .pend1 → (a = .step 1 ∧ c'.loc 1 = some .ready1) ∨ c'.loc 1 = none) ∧
    (c.loc 1 = some .ready1 → c'.loc 1 = some .h1 ∨ c'.loc 1 = none) ∧
    (c.loc 1 = some .h1 → a = .step 1 ∨ c'.loc 1 = some .pend1 ∨ c'.loc 1 = none) := by
  cases ht with
  | @inv i x q q' hq ht =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq, reduceCtorEq, false_and, false_or,
      or_false]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hq] at h <;> cases h <;>
      rcases ht with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> first | (cases h; done) | exact h'
  | @res i r q q' hq ht =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq, reduceCtorEq, false_and, false_or,
      or_false]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hq] at h <;> cases h <;>
      rcases ht with ⟨h, h'⟩ | ⟨h, h'⟩ <;> first | (cases h; done) | exact h'
  | @crash i q hq =>
    simp only [Act.IsProc, Ext.proc] at ha; subst ha
    simp
  | @step i q q' b' hq hs =>
    simp only [Act.IsProc] at ha; subst ha
    simp only [Function.update_self, Option.some.injEq, reduceCtorEq, or_false, true_or,
      implies_true, and_true, true_and]
    rw [hq]
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> cases h <;>
      rcases hs with ⟨h, -⟩ | ⟨v, h, -⟩ | ⟨h, -⟩ | ⟨h0, h, -⟩ <;>
      first | (cases h; done) | (cases h0; done) | exact h
  | base => simp [Act.IsProc] at ha

theorem step1_counter {c c' : Is.Cfg} (ht : Is.Trans c (.step 1) c')
    (hl : c.loc 1 = some .h1 ∨ c.loc 1 = some .pend1) : c'.mem.1 = c.mem.1 + 1 := by
  cases ht with
  | @step _ q q' b' hq hs =>
    rcases hl with hl | hl <;> rw [hl] at hq <;> cases hq <;>
      rcases hs with ⟨h, -⟩ | ⟨v, h, -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> first | (cases h) | rfl

theorem en0 {c : Is.Cfg}
    (h : c.loc 0 = some .wRead ∨ c.loc 0 = some .ready0 ∨
      ∃ v, c.loc 0 = some (.wWait v) ∧ (c.mem.2 = true ∨ c.mem.1 ≠ v)) :
    Is.NonCrashEnabled c 0 := by
  rcases h with h | h | ⟨v, h, hv⟩
  · cases hb : c.mem.2
    · exact ⟨.step 0, rfl, id, _, .step (q' := HQ.wWait c.mem.1) (b' := c.mem) h
        (Or.inl ⟨rfl, rfl, Or.inr ⟨hb, rfl⟩⟩)⟩
    · exact ⟨.step 0, rfl, id, _, .step (q' := HQ.ready0) (b' := c.mem) h
        (Or.inl ⟨rfl, rfl, Or.inl ⟨hb, rfl⟩⟩)⟩
  · exact ⟨.ext (.res 0 ()), rfl, id, _, .res (q' := HQ.done0) h (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨.step 0, rfl, id, _, .step (q' := HQ.ready0) (b' := c.mem) h
      (Or.inr (Or.inl ⟨v, rfl, rfl, hv, rfl⟩))⟩

theorem en1 {c : Is.Cfg}
    (h : c.loc 1 = some .h1 ∨ c.loc 1 = some .pend1 ∨ c.loc 1 = some .ready1) :
    Is.NonCrashEnabled c 1 := by
  rcases h with h | h | h
  · exact ⟨.step 1, rfl, id, _, .step (q' := HQ.h1) (b' := (c.mem.1 + 1, c.mem.2)) h
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
  · exact ⟨.step 1, rfl, id, _, .step (q' := HQ.ready1) (b' := (c.mem.1 + 1, true)) h
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))⟩
  · exact ⟨.ext (.res 1 ()), rfl, id, _, .res (q' := HQ.h1) h (Or.inr ⟨rfl, rfl⟩)⟩

/-- History facts of `Is`: a response to `p₁` sets the flag, and `p₀` has received no response
while it is in its first operation. -/
theorem reach_resp {c : Is.Cfg} {l : List E} (hc : Is.Reach c l) :
    (∀ r, Ext.res 1 r ∈ l → c.mem.2 = true) ∧
    (c.loc 0 = some .w0 ∨ c.loc 0 = some .wRead ∨ (∃ v, c.loc 0 = some (.wWait v)) →
      ∀ r, Ext.res 0 r ∉ l) := by
  refine Reach.induct (P := fun (c : Is.Cfg) (l : List E) =>
    (∀ r, Ext.res 1 r ∈ l → c.mem.2 = true) ∧
    (c.loc 0 = some HQ.w0 ∨ c.loc 0 = some HQ.wRead ∨ (∃ v, c.loc 0 = some (HQ.wWait v)) →
      ∀ r, Ext.res 0 r ∉ l)) ?_ ?_ hc
  · intro c _; simp
  · rintro c l a c' hreach ⟨ih1, ih2⟩ ht
    obtain ⟨m, -, hI⟩ := reach_inv hreach
    have hmem := Is_trans_mem ht
    cases ht with
    | @inv i x q q' hq ht =>
      simp only [hist_single_ext, List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      refine ⟨ih1, fun hp => ?_⟩
      rcases fin2_cases i with rfl | rfl
      · simp only [Function.update_self, Option.some.injEq] at hp
        rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih2 (Or.inl hq)
        · simp at hp
        · simp at hp
      · simp only [upd10'] at hp
        exact ih2 hp
    | @res i r q q' hq ht =>
      rcases fin2_cases i with rfl | rfl
      · have hq0 : q = .ready0 := by
          have := hI.f0; rw [hq] at this
          rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · rfl
          · simp [Fits0] at this
        subst hq0
        rcases ht with ⟨-, rfl⟩ | ⟨h, -⟩
        · refine ⟨fun r' hr' => ?_, fun hp => ?_⟩
          · simp only [hist_single_ext, List.mem_append, List.mem_singleton] at hr'
            rcases hr' with hr' | hr'
            · exact ih1 r' hr'
            · cases hr'
          · simp at hp
        · cases h
      · have hq1 : q = .ready1 := by
          have := hI.f1; rw [hq] at this
          rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · simp [Fits1] at this
          · rfl
        subst hq1
        refine ⟨fun r' _ => hI.r1f hq, fun hp r' hr' => ?_⟩
        simp only [upd10'] at hp
        simp only [hist_single_ext, List.mem_append, List.mem_singleton] at hr'
        rcases hr' with hr' | hr'
        · exact ih2 hp r' hr'
        · cases hr'
    | @crash i q hq =>
      simp only [hist_single_ext, List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      refine ⟨ih1, fun hp => ?_⟩
      rcases fin2_cases i with rfl | rfl
      · simp at hp
      · simp only [upd10'] at hp; exact ih2 hp
    | @step i q q' b' hq hs =>
      simp only [hist_single_step, List.append_nil]
      refine ⟨fun r hr => hmem.2 (ih1 r hr), fun hp => ?_⟩
      rcases fin2_cases i with rfl | rfl
      · simp only [Function.update_self, Option.some.injEq] at hp
        rcases hs with ⟨rfl, -, -⟩ | ⟨v, rfl, -, -, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
        · exact ih2 (Or.inr (Or.inl hq))
        · simp at hp
        · simp at hp
        · simp at hp
      · simp only [upd10'] at hp; exact ih2 hp
    | base hb =>
      simp only [hist_single_base, List.append_nil]
      exact ⟨fun r hr => hmem.2 (ih1 r hr), ih2⟩

theorem step1_from {c c' : Is.Cfg} (ht : Is.Trans c (.step 1) c') {s : PStat}
    (hf : Fits1 (c.loc 1) s) : c.loc 1 = some .h1 ∨ c.loc 1 = some .pend1 := by
  cases ht with
  | @step _ q q' b' hq hs =>
    rw [hq] at hf ⊢
    rcases hs with ⟨rfl, -⟩ | ⟨v, rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp [Fits1] at hf
    · simp [Fits1] at hf
    · left; rfl
    · right; rfl

section Exec

variable {n : ℕ} {Inv Res : Type} {I : Impl n Inv Res} {e : I.InfExec}
  {h : Hist (Ext n Inv Res)}

theorem finPrefix_of_hasHist (he : e.HasHist h) (k : ℕ) : FinPrefix (hist (e.pre k)) h := by
  cases h with
  | fin l =>
    obtain ⟨K, hK⟩ := he
    dsimp only at hK
    have := hist_prefix (e.pre_prefix (le_max_left k K))
    rw [hK _ (le_max_right _ _)] at this
    exact this
  | inf f => exact he.1 k

theorem exists_prefix_of_hasHist (he : e.HasHist h) {l : List (Ext n Inv Res)}
    (hl : FinPrefix l h) : ∃ K, l <+: hist (e.pre K) := by
  cases h with
  | fin l' =>
    obtain ⟨K, hK⟩ := he
    dsimp only at hK
    exact ⟨K, by rw [hK K le_rfl]; exact hl⟩
  | inf f =>
    obtain ⟨K, hK⟩ := he.2 l.length
    refine ⟨K, ?_⟩
    rw [finPrefix_inf_iff.1 hl]
    exact pfx_prefix (he.1 K) hK

theorem eq_fin_of_hasHist (he : e.HasHist h) {K : ℕ} {l : List (Ext n Inv Res)}
    (hK : ∀ k ≥ K, hist (e.pre k) = l) : h = .fin l := by
  cases h with
  | fin l' =>
    obtain ⟨K', hK'⟩ := he
    dsimp only at hK'
    rw [← hK' (max K K') (le_max_right _ _), hK _ (le_max_left _ _)]
  | inf f =>
    exfalso
    obtain ⟨k, hk⟩ := he.2 (l.length + 1)
    dsimp only at hk
    have := (hist_prefix (e.pre_prefix (le_max_left k K))).length_le
    rw [hK _ (le_max_right _ _)] at this
    omega

end Exec

theorem Is_mem_mono (e : Is.InfExec) {k k' : ℕ} (h : k ≤ k') :
    (e.cfg k).mem.1 ≤ (e.cfg k').mem.1 ∧
      ((e.cfg k).mem.2 = true → (e.cfg k').mem.2 = true) := by
  induction k', h using Nat.le_induction with
  | base => exact ⟨le_rfl, id⟩
  | succ k' _ ih =>
    have := Is_trans_mem (e.trans k')
    exact ⟨ih.1.trans this.1, fun hb => this.2 (ih.2 hb)⟩

/-- **Liveness of `Is`.** Every fair history of `Is` is wait-free, or it is one of the histories
`Y` (`p₁` crashed, `p₀` waits forever in its first operation, no response at all). -/
theorem Is_fairH_subset : Is.fairH ⊆ WaitFree ∪ Y := by
  rintro h (⟨c, l, hc, hfin, rfl⟩ | ⟨e, hfair, he⟩)
  · exact absurd (hfin _ _ (Trans.base (I := Is) (c := c) (b' := c.mem) rfl)) id
  by_cases hW : h ∈ WaitFree
  · exact Or.inl hW
  right
  have hU : h ∈ U := fairH_subset_U Is_valid.2.1 (Or.inr ⟨e, hfair, he⟩)
  have hW' : ∃ l, FinPrefix l h ∧ ∃ σ, runStat l = some σ ∧ ∃ i, σ i = .pend ∧
      ∀ l' σ', FinPrefix l' h → l <+: l' → runStat l' = some σ' → σ' i = .pend := by
    by_contra hcon
    apply hW
    refine ⟨hU, fun l hl σ hσ i hi => ?_⟩
    by_contra hcon'
    apply hcon
    refine ⟨l, hl, σ, hσ, i, hi, fun l' σ' h1 h2 h3 => ?_⟩
    by_contra hne
    exact hcon' ⟨l', σ', h1, h2, h3, hne⟩
  obtain ⟨l, hl, σ, hσ, i, hi, hno⟩ := hW'
  obtain ⟨K, hK⟩ := exists_prefix_of_hasHist he hl
  have hreach : ∀ k, Is.Reach (e.cfg k) (hist (e.pre k)) :=
    fun k => ⟨e.cfg 0, e.pre k, e.init, e.run_pre k, rfl⟩
  have hinv : ∀ k, ∃ m, runMon (hist (e.pre k)) = some m ∧ Inv (e.cfg k) m :=
    fun k => reach_inv (hreach k)
  have hpend : ∀ k ≥ K, ∀ m, runMon (hist (e.pre k)) = some m → m.σ i = .pend := by
    intro k hk m hm
    exact hno _ _ (finPrefix_of_hasHist he k)
      (hK.trans (hist_prefix (e.pre_prefix hk))) (runMon_runStat hm)
  rcases fin2_cases i with rfl | rfl
  · ---------------- `p₀` waits forever
    have hP0 : ∀ k ≥ K, P0pend ((e.cfg k).loc 0) := by
      intro k hk
      obtain ⟨m, hm, hI⟩ := hinv k
      have := hI.f0
      rw [hpend k hk m hm] at this
      exact p0pend_of_fits this
    have hnP0 : ∀ k ≥ K, ¬ P0pend (some HQ.done0) ∧ ¬ P0pend (none : Option HQ) := by
      intro _ _; simp [P0pend]
    -- `p₀` never becomes ready
    have hnr : ∀ k ≥ K, (e.cfg k).loc 0 ≠ some .ready0 := by
      intro k₁ hk₁ h₁
      have noact : ∀ k ≥ K, (e.cfg k).loc 0 = some .ready0 → ¬ (e.act k).IsProc 0 := by
        intro k hk hr hp
        rcases (trans_p0 (e.trans k) hp).1 hr with h' | h' <;>
          · have := hP0 (k + 1) (by omega); rw [h'] at this; simp [P0pend] at this
      have stay : ∀ k ≥ k₁, (e.cfg k).loc 0 = some .ready0 := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact h₁
        | succ k hk ih => rw [(e.trans k).loc_eq (noact k (by omega) ih)]; exact ih
      rcases hfair 0 with h' | h'
      · obtain ⟨k, hk, hp⟩ := h' k₁
        exact noact k (by omega) (stay k hk) hp
      · obtain ⟨k, hk, hne⟩ := h' k₁
        exact hne (en0 (Or.inr (Or.inl (stay k hk))))
    -- `p₀` eventually waits for the counter
    have hww : ∃ K₁ ≥ K, ∃ v, (e.cfg K₁).loc 0 = some (.wWait v) := by
      by_contra hcon
      push Not at hcon
      have hrd : ∀ k ≥ K, (e.cfg k).loc 0 = some .wRead := by
        intro k hk
        rcases hP0 k hk with h' | ⟨v, h'⟩ | h'
        · exact h'
        · exact absurd h' (hcon k hk v)
        · exact absurd h' (hnr k hk)
      have noact : ∀ k ≥ K, ¬ (e.act k).IsProc 0 := by
        intro k hk hp
        rcases (trans_p0 (e.trans k) hp).2.1 (hrd k hk) with h' | ⟨v, h'⟩ | h'
        · exact hnr (k + 1) (by omega) h'
        · exact hcon (k + 1) (by omega) v h'
        · have := hP0 (k + 1) (by omega); rw [h'] at this; simp [P0pend] at this
      rcases hfair 0 with h' | h'
      · obtain ⟨k, hk, hp⟩ := h' K
        exact noact k hk hp
      · obtain ⟨k, hk, hne⟩ := h' K
        exact hne (en0 (Or.inl (hrd k hk)))
    obtain ⟨K₁, hK₁, v, hv⟩ := hww
    have hstay : ∀ k ≥ K₁, (e.cfg k).loc 0 = some (.wWait v) ∧ ¬ (e.act k).IsProc 0 := by
      have noact : ∀ k ≥ K₁, (e.cfg k).loc 0 = some (.wWait v) → ¬ (e.act k).IsProc 0 := by
        intro k hk hw hp
        rcases (trans_p0 (e.trans k) hp).2.2 v hw with h' | h'
        · exact hnr (k + 1) (by omega) h'
        · have := hP0 (k + 1) (by omega); rw [h'] at this; simp [P0pend] at this
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hv, noact K₁ le_rfl hv⟩
      | succ k hk ih =>
        have h' : (e.cfg (k + 1)).loc 0 = some (.wWait v) := by
          rw [(e.trans k).loc_eq ih.2]; exact ih.1
        exact ⟨h', noact (k + 1) (by omega) h'⟩
    have hdis : ∀ K', ∃ k ≥ K', ¬ Is.NonCrashEnabled (e.cfg k) 0 := by
      rcases hfair 0 with h' | h'
      · obtain ⟨k, hk, hp⟩ := h' K₁
        exact absurd hp (hstay k hk).2
      · exact h'
    have hfc : ∀ k ≥ K₁, (e.cfg k).mem.2 = false ∧ (e.cfg k).mem.1 = v := by
      intro k hk
      obtain ⟨k', hk', hne⟩ := hdis k
      have hw := (hstay k' (by omega)).1
      have hb : ¬ ((e.cfg k').mem.2 = true ∨ (e.cfg k').mem.1 ≠ v) :=
        fun h' => hne (en0 (Or.inr (Or.inr ⟨v, hw, h'⟩)))
      push Not at hb
      have hmono := Is_mem_mono e hk'
      obtain ⟨m, -, hI⟩ := hinv k
      have hle := (hI.wait v (hstay k hk).1).1
      refine ⟨?_, by omega⟩
      cases hf : (e.cfg k).mem.2
      · rfl
      · have := hmono.2 hf; exact absurd this hb.1
    -- `p₁` takes no step any more
    have hns : ∀ k ≥ K₁, e.act k ≠ .step 1 := by
      intro k hk hst
      have ht := e.trans k
      rw [hst] at ht
      obtain ⟨m, -, hI⟩ := hinv k
      have := step1_counter ht (step1_from ht hI.f1)
      have h1 := (hfc k hk).2
      have h2 := (hfc (k + 1) (by omega)).2
      omega
    -- hence `p₁` eventually crashes
    have hdead : ∃ K₂ ≥ K₁, (e.cfg K₂).loc 1 = none := by
      by_contra hcon
      push Not at hcon
      have hl1 : ∀ k ≥ K₁, (e.cfg k).loc 1 = some .h1 ∨ (e.cfg k).loc 1 = some .pend1 ∨
          (e.cfg k).loc 1 = some .ready1 := by
        intro k hk
        obtain ⟨m, -, hI⟩ := hinv k
        have hf := hI.f1
        rcases h' : (e.cfg k).loc 1 with _ | q
        · exact absurd h' (hcon k hk)
        · rw [h'] at hf
          cases q <;> simp_all [Fits1]
      have hinf : ∀ K', ∃ k ≥ K', (e.act k).IsProc 1 := by
        rcases hfair 1 with h' | h'
        · exact h'
        · intro K'
          obtain ⟨k, hk, hne⟩ := h' (max K₁ K')
          exact absurd (en1 (hl1 k (by omega))) hne
      let φ : ℕ → ℕ := fun k =>
        if (e.cfg k).loc 1 = some .ready1 then 2 else if (e.cfg k).loc 1 = some .h1 then 1 else 0
      have hstep : ∀ k ≥ K₁, (e.act k).IsProc 1 → φ (k + 1) < φ k := by
        intro k hk hp
        obtain ⟨hpd, hrd, hh1⟩ := trans_p1 (e.trans k) hp
        rcases hl1 k hk with h' | h' | h'
        · rcases hh1 h' with h'' | h'' | h''
          · exact absurd h'' (hns k hk)
          · simp [φ, h', h'']
          · exact absurd h'' (hcon (k + 1) (by omega))
        · rcases hpd h' with h'' | h''
          · exact absurd h''.1 (hns k hk)
          · exact absurd h'' (hcon (k + 1) (by omega))
        · rcases hrd h' with h'' | h''
          · simp [φ, h', h'']
          · exact absurd h'' (hcon (k + 1) (by omega))
      refine no_infinite_descent (φ := φ) (K := K₁) (P := fun k => (e.act k).IsProc 1)
        (fun k hk => ?_) hstep hinf
      by_cases hp : (e.act k).IsProc 1
      · exact (hstep k hk hp).le
      · simp only [φ, (e.trans k).loc_eq hp]; exact le_rfl
    obtain ⟨K₂, hK₂, hn⟩ := hdead
    have hdead' : ∀ k ≥ K₂, (e.cfg k).loc 1 = none ∧ ¬ (e.act k).IsProc 1 := by
      have noact : ∀ k, (e.cfg k).loc 1 = none → ¬ (e.act k).IsProc 1 := by
        intro k hk hp
        have := (e.trans k).loc_isSome hp
        rw [hk] at this; cases this
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hn, noact _ hn⟩
      | succ k hk ih =>
        have h' : (e.cfg (k + 1)).loc 1 = none := by rw [(e.trans k).loc_eq ih.2]; exact ih.1
        exact ⟨h', noact _ h'⟩
    -- no external action any more
    have hconst : ∀ k ≥ K₂, hist (e.pre k) = hist (e.pre K₂) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [e.pre_succ, hist_append, ih]
        cases ha : e.act k with
        | ext e' =>
          exfalso
          rcases fin2_cases e'.proc with h' | h'
          · exact (hstay k (by omega)).2 (by rw [ha]; exact h')
          · exact (hdead' k hk).2 (by rw [ha]; exact h')
        | step j => simp
        | base => simp
    have hh := eq_fin_of_hasHist he hconst
    subst hh
    refine ⟨_, rfl, ?_, ?_⟩
    · obtain ⟨hr1, hr0⟩ := reach_resp (hreach K₂)
      intro e' he' hres
      cases e' with
      | inv => exact hres
      | crash => exact hres
      | res j r =>
        rcases fin2_cases j with rfl | rfl
        · exact hr0 (Or.inr (Or.inr ⟨v, (hstay K₂ hK₂).1⟩)) r he'
        · have := hr1 r he'
          rw [(hfc K₂ hK₂).1] at this; cases this
    · obtain ⟨m, hm, hI⟩ := hinv K₂
      rw [runMon_runStat hm]
      congr 1
      funext j
      rcases fin2_cases j with rfl | rfl
      · have := hI.f0
        rw [(hstay K₂ hK₂).1] at this
        simp only [Fits0] at this
        rw [this]; decide
      · have := hI.f1
        rw [(hdead' K₂ le_rfl).1] at this
        simp only [Fits1] at this
        rw [this]; decide
  · ---------------- `p₁` waits forever: impossible
    exfalso
    have hP1 : ∀ k ≥ K, P1pend ((e.cfg k).loc 1) := by
      intro k hk
      obtain ⟨m, hm, hI⟩ := hinv k
      have := hI.f1
      rw [hpend k hk m hm] at this
      exact p1pend_of_fits this
    have hinf : ∀ K', ∃ k ≥ K', (e.act k).IsProc 1 := by
      rcases hfair 1 with h' | h'
      · exact h'
      · intro K'
        obtain ⟨k, hk, hne⟩ := h' (max K K')
        rcases hP1 k (by omega) with h'' | h''
        · exact absurd (en1 (Or.inr (Or.inl h''))) hne
        · exact absurd (en1 (Or.inr (Or.inr h''))) hne
    let φ : ℕ → ℕ := fun k => if (e.cfg k).loc 1 = some .pend1 then 1 else 0
    have hstep : ∀ k ≥ K, (e.act k).IsProc 1 → φ (k + 1) < φ k := by
      intro k hk hp
      obtain ⟨hpd, hrd, -⟩ := trans_p1 (e.trans k) hp
      have hnext := hP1 (k + 1) (by omega)
      rcases hP1 k hk with h' | h'
      · rcases hpd h' with h'' | h''
        · simp [φ, h', h''.2]
        · rw [h''] at hnext; simp [P1pend] at hnext
      · rcases hrd h' with h'' | h'' <;> (rw [h''] at hnext; simp [P1pend] at hnext)
    refine no_infinite_descent (φ := φ) (K := K) (P := fun k => (e.act k).IsProc 1)
      (fun k hk => ?_) hstep hinf
    by_cases hp : (e.act k).IsProc 1
    · exact (hstep k hk hp).le
    · simp only [φ, (e.trans k).loc_eq hp]; exact le_rfl

end Liveness


/-! ## Theorem 4.9 fails with `Lmax` = wait-freedom -/

/-- With `Lmax` = wait-freedom, `WaitFree ∪ Y` is the strongest liveness property that does not
exclude `S` (over all valid implementations). -/
theorem isStrongestNonExcl_waitFree_Y :
    (setting {I : Impl 2 Unit Unit | I.Valid} S WaitFree).IsStrongestNonExcl (WaitFree ∪ Y) := by
  have hY : Y ⊆ (setting {I : Impl 2 Unit Unit | I.Valid} S WaitFree).core :=
    fun h hh I hI => Y_subset_fairH hI.1 hI.2 hh
  have hcore : (setting {I : Impl 2 Unit Unit | I.Valid} S WaitFree).core ⊆ WaitFree ∪ Y :=
    fun h hh => Is_fairH_subset (hh Is ⟨Is_valid, Is_ensuresS⟩)
  rw [Setting.isStrongestNonExcl_iff]
  refine ⟨?_, Is, ⟨Is_valid, Is_ensuresS⟩, fun h hh => ?_⟩
  · apply Set.Subset.antisymm
    · exact Set.union_subset Set.subset_union_left (hY.trans Set.subset_union_right)
    · exact Set.union_subset Set.subset_union_left hcore
  · rcases Is_fairH_subset hh with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hY h')

/-- **Theorem 4.9 is false, with `Lmax` = wait-freedom.** For two processes and the safety
property `S` (which satisfies all the paper's assumptions), the strongest liveness property that
does not exclude `S` exists (it is `WaitFree ∪ Y`) but it is not wait-freedom. The implementations
are all valid implementations of the paper's I/O-automaton model, in which processes may take
steps while idle. -/
theorem theorem_4_9_false_waitFree :
    SafetyAssumptions {I : Impl 2 Unit Unit | I.Valid} S ∧ LmaxAssumptions WaitFree ∧
      (∃ L, (setting {I : Impl 2 Unit Unit | I.Valid} S WaitFree).IsStrongestNonExcl L) ∧
      ∀ L, (setting {I : Impl 2 Unit Unit | I.Valid} S WaitFree).IsStrongestNonExcl L →
        L ≠ WaitFree := by
  refine ⟨S_assumptions, waitFree_assumptions, ⟨_, isStrongestNonExcl_waitFree_Y⟩, ?_⟩
  intro L hL hLeq
  have hL' := ((Setting.isStrongestNonExcl_iff _ L).1 hL).1
  have : Hist.fin h0 ∈ L := by
    rw [hL']
    exact Or.inr fun I hI => h0_mem_fairH hI.1 hI.2
  rw [hLeq] at this
  exact h0_not_waitFree this

/-- `Is` is not reactive: `p₁` steps while idle (the heartbeat). This is exactly what
Theorem 4.9 needs to exclude (`theorem_4_9_reactive`). -/
theorem Is_not_reactive : ¬ Is.Reactive := by
  intro h
  exact h _ [] (Reach.init mk_init) _ rfl 1 rfl
    ⟨_, tstep1 (l0 := some HQ.w0) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩

end Podc.SafetyLivenessExclusion.Counterexample
