import Papers.PODC2015.SafetyLivenessExclusion.Model

/-!
# Generic lemmas about the model

Induction over reachable states, the status monitor, crash bookkeeping, input-only extensions of
executions, and the *frame lemma*: actions that do not belong to a process `j` commute with any
change of `j`'s local state (the composition structure of the I/O-automaton model).
-/

namespace Podc.SafetyLivenessExclusion

open Hist

variable {n : ℕ} {Inv Res : Type}

/-! ## The status monitor -/

@[simp] theorem stepStat_inv {σ σ' : Fin n → PStat} {i : Fin n} {x : Inv} :
    stepStat (Res := Res) σ (.inv i x) = some σ' ↔ σ i = .idle ∧ σ' = Function.update σ i .pend := by
  simp only [stepStat]; split_ifs with h <;> simp [h, eq_comm]

@[simp] theorem stepStat_res {σ σ' : Fin n → PStat} {i : Fin n} {r : Res} :
    stepStat (Inv := Inv) σ (.res i r) = some σ' ↔ σ i = .pend ∧ σ' = Function.update σ i .idle := by
  simp only [stepStat]; split_ifs with h <;> simp [h, eq_comm]

@[simp] theorem stepStat_crash {σ σ' : Fin n → PStat} {i : Fin n} :
    stepStat (Inv := Inv) (Res := Res) σ (.crash i) = some σ' ↔
      σ i ≠ .dead ∧ σ' = Function.update σ i .dead := by
  simp only [stepStat]; split_ifs with h <;> simp [h, eq_comm]

theorem runStat_append_eq_some {l : List (Ext n Inv Res)} {e : Ext n Inv Res}
    {σ' : Fin n → PStat} :
    runStat (l ++ [e]) = some σ' ↔ ∃ σ, runStat l = some σ ∧ stepStat σ e = some σ' := by
  rw [runStat_append]; cases runStat l <;> simp

theorem WF.of_append {l m : List (Ext n Inv Res)} (h : WF (l ++ m)) : WF l :=
  runStat_prefix (List.prefix_append l m) h

theorem WF.exists {l : List (Ext n Inv Res)} (h : WF l) : ∃ σ, runStat l = some σ :=
  Option.isSome_iff_exists.1 h

/-- Other processes' statuses do not change. -/
theorem stepStat_ne {σ σ' : Fin n → PStat} {e : Ext n Inv Res} (h : stepStat σ e = some σ')
    {j : Fin n} (hj : e.proc ≠ j) : σ' j = σ j := by
  cases e with
  | inv i x =>
    simp only [Ext.proc] at hj
    rw [stepStat_inv] at h; rw [h.2, Function.update_of_ne (Ne.symm hj)]
  | res i r =>
    simp only [Ext.proc] at hj
    rw [stepStat_res] at h; rw [h.2, Function.update_of_ne (Ne.symm hj)]
  | crash i =>
    simp only [Ext.proc] at hj
    rw [stepStat_crash] at h; rw [h.2, Function.update_of_ne (Ne.symm hj)]

/-- No event is possible for a crashed process. -/
theorem stepStat_dead {σ : Fin n → PStat} {e : Ext n Inv Res} (h : σ e.proc = .dead) :
    stepStat σ e = none := by
  cases e <;> simp_all [stepStat, Ext.proc]

/-- `e` is a response. -/
def Ext.IsRes : Ext n Inv Res → Prop
  | .res _ _ => True
  | _ => False

/-- The projection `l|p_i` of a history on a process. -/
def proj (l : List (Ext n Inv Res)) (i : Fin n) : List (Ext n Inv Res) :=
  l.filter (fun e => decide (e.proc = i))

@[simp] theorem proj_nil (i : Fin n) : proj ([] : List (Ext n Inv Res)) i = [] := rfl

theorem proj_snoc_of_eq (l : List (Ext n Inv Res)) {e : Ext n Inv Res} {i : Fin n}
    (h : e.proc = i) : proj (l ++ [e]) i = proj l i ++ [e] := by
  simp [proj, List.filter_append, h]

theorem proj_snoc_of_ne (l : List (Ext n Inv Res)) {e : Ext n Inv Res} {i : Fin n}
    (h : e.proc ≠ i) : proj (l ++ [e]) i = proj l i := by
  simp [proj, List.filter_append, h]

/-- No-response histories: per process, the projection is `[]`, `[inv x]` or ends with a crash. -/
theorem noRes_proj {l : List (Ext n Inv Res)} (hl : ∀ e ∈ l, ¬ e.IsRes) {σ : Fin n → PStat}
    (hσ : runStat l = some σ) (i : Fin n) :
    (σ i = .idle → proj l i = []) ∧ (σ i = .pend → ∃ x, proj l i = [.inv i x]) := by
  induction l using List.reverseRecOn generalizing σ with
  | nil =>
    simp only [runStat_nil, Option.some.injEq] at hσ
    subst hσ; simp
  | append_singleton l e ih =>
    obtain ⟨σ₀, h₀, he⟩ := runStat_append_eq_some.1 hσ
    have ih' := ih (fun e he => hl e (List.mem_append_left _ he)) h₀
    by_cases hp : e.proc = i
    · cases e with
      | inv j x =>
        simp only [Ext.proc] at hp; subst hp
        rw [stepStat_inv] at he
        obtain ⟨hidle, rfl⟩ := he
        refine ⟨by simp, fun _ => ⟨x, ?_⟩⟩
        rw [proj_snoc_of_eq (e := Ext.inv j x) (i := j) _ rfl, ih'.1 hidle]; rfl
      | res j r => exact absurd trivial (hl (.res j r) (by simp))
      | crash j =>
        simp only [Ext.proc] at hp; subst hp
        rw [stepStat_crash] at he
        obtain ⟨-, rfl⟩ := he
        simp
    · rw [stepStat_ne he hp, proj_snoc_of_ne _ hp]
      exact ih'

@[simp] theorem hist_map_ext (m : List (Ext n Inv Res)) : hist (m.map Act.ext) = m := by
  induction m with
  | nil => rfl
  | cons e m ih => simp [ih]

namespace Impl

variable {I : Impl n Inv Res}

@[simp] theorem hist_single_ext (e : Ext n Inv Res) : hist [Act.ext e] = [e] := rfl
@[simp] theorem hist_single_step (i : Fin n) : hist [(Act.step i : Act n Inv Res)] = [] := rfl
@[simp] theorem hist_single_base : hist [(Act.base : Act n Inv Res)] = [] := rfl

/-- Induction over reachable states. -/
theorem Reach.induct {P : I.Cfg → List (Ext n Inv Res) → Prop}
    (h0 : ∀ c, I.IsInit c → P c [])
    (hs : ∀ c l a c', I.Reach c l → P c l → I.Trans c a c' → P c' (l ++ hist [a]))
    {c : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l) : P c l := by
  obtain ⟨c₀, as, hi, hr, rfl⟩ := hc
  induction as using List.reverseRecOn generalizing c with
  | nil => cases hr; exact h0 _ hi
  | append_singleton as a ih =>
    obtain ⟨c', h1, h2⟩ := Run.of_append hr
    cases h2 with
    | cons ht hn =>
      cases hn
      rw [hist_append]
      exact hs _ _ _ _ ⟨c₀, as, hi, h1, rfl⟩ (ih h1) ht

theorem Reach.init {c : I.Cfg} (hc : I.IsInit c) : I.Reach c [] := ⟨c, [], hc, .nil _, rfl⟩

/-- Transitions not belonging to `j` leave `j`'s local state unchanged. -/
theorem Trans.loc_eq {c c' : I.Cfg} {a : Act n Inv Res} (h : I.Trans c a c') {j : Fin n}
    (hj : ¬ a.IsProc j) : c'.loc j = c.loc j := by
  cases h <;> simp_all [Act.IsProc, Ext.proc, Function.update_of_ne (Ne.symm _)]

/-- A crashed process has no enabled action. -/
theorem Trans.loc_isSome {c c' : I.Cfg} {a : Act n Inv Res} (h : I.Trans c a c') {j : Fin n}
    (hj : a.IsProc j) : (c.loc j).isSome := by
  cases h <;> simp_all [Act.IsProc, Ext.proc]

/-- In a reachable state, a process is crashed iff its status is `dead`. -/
theorem Reach.loc_eq_none_iff {c : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    {σ : Fin n → PStat} (hσ : runStat l = some σ) (i : Fin n) :
    c.loc i = none ↔ σ i = .dead := by
  suffices H : ∀ σ, runStat l = some σ → ∀ i, c.loc i = none ↔ σ i = .dead from H σ hσ i
  refine Reach.induct (P := fun c l => ∀ σ, runStat l = some σ → ∀ i, c.loc i = none ↔ σ i = .dead)
    ?_ ?_ hc
  · intro c hc σ hσ i
    simp only [runStat_nil, Option.some.injEq] at hσ
    subst hσ
    obtain ⟨q, hq, -⟩ := hc.1 i
    simp [hq]
  · intro c l a c' _ ih ht σ' hσ' i
    cases ht with
    | @inv j x q q' hq _ =>
      obtain ⟨σ, h₀, he⟩ := runStat_append_eq_some.1 hσ'
      rw [stepStat_inv] at he
      obtain ⟨-, rfl⟩ := he
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, ih σ h₀ i]
    | @res j r q q' hq _ =>
      obtain ⟨σ, h₀, he⟩ := runStat_append_eq_some.1 hσ'
      rw [stepStat_res] at he
      obtain ⟨-, rfl⟩ := he
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, ih σ h₀ i]
    | @crash j q hq =>
      obtain ⟨σ, h₀, he⟩ := runStat_append_eq_some.1 hσ'
      rw [stepStat_crash] at he
      obtain ⟨-, rfl⟩ := he
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, ih σ h₀ i]
    | @step j q q' b hq _ =>
      simp only [hist_single_step, List.append_nil] at hσ'
      by_cases hij : i = j
      · subst hij
        have := (ih σ' hσ' i).not.1 (by simp [hq])
        simp [this]
      · simp [Function.update_of_ne hij, ih σ' hσ' i]
    | base =>
      simp only [hist_single_base, List.append_nil] at hσ'
      exact ih σ' hσ' i

/-- Applying an input action (invocation or crash) that keeps the history well-formed is always
possible in a valid implementation. -/
theorem Reach.input {c : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    (hI : I.InputEnabled) {e : Ext n Inv Res} (he : ¬ e.IsRes) (hwf : WF (l ++ [e])) :
    ∃ c', I.Trans c (.ext e) c' := by
  obtain ⟨σ', hσ'⟩ := hwf.exists
  obtain ⟨σ, h₀, hs⟩ := runStat_append_eq_some.1 hσ'
  cases e with
  | inv i x => exact hI c l hc σ h₀ i (stepStat_inv.1 hs).1 x
  | res => exact absurd trivial he
  | crash i =>
    have hd := (stepStat_crash.1 hs).1
    cases hq : c.loc i with
    | none => exact absurd ((hc.loc_eq_none_iff h₀ i).1 hq) hd
    | some q => exact ⟨_, .crash hq⟩

/-- A well-formed sequence of input actions can always be applied. -/
theorem Reach.inputs {c : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    (hI : I.InputEnabled) {m : List (Ext n Inv Res)} (hm : ∀ e ∈ m, ¬ e.IsRes)
    (hwf : WF (l ++ m)) : ∃ c', I.Run c (m.map Act.ext) c' := by
  induction m using List.reverseRecOn with
  | nil => exact ⟨c, .nil _⟩
  | append_singleton m e ih =>
    obtain ⟨c', hc'⟩ := ih (fun e he => hm e (List.mem_append_left _ he))
      (by rw [← List.append_assoc] at hwf; exact hwf.of_append)
    have hreach : I.Reach c' (l ++ m) := by
      simpa using hc.run hc'
    obtain ⟨c'', ht⟩ := hreach.input hI (hm e (by simp)) (by simpa using hwf)
    exact ⟨c'', by simpa using hc'.snoc ht⟩

/-- Every well-formed history without responses is a finite history of a valid implementation. -/
theorem Valid.finHist_of_noRes (hI : I.Valid) {m : List (Ext n Inv Res)}
    (hm : ∀ e ∈ m, ¬ e.IsRes) (hwf : WF m) : I.FinHist m := by
  obtain ⟨c₀, h₀⟩ := hI.1
  obtain ⟨c', hc'⟩ := (Reach.init h₀).inputs hI.2.2 hm (by simpa using hwf)
  exact ⟨c', c₀, _, h₀, hc', by simp⟩

/-- `a` belongs to process `l₀` or to the base objects. -/
def _root_.Podc.SafetyLivenessExclusion.Act.Only (l₀ : Fin n) : Act n Inv Res → Prop
  | .ext e => e.proc = l₀
  | .step i => i = l₀
  | .base => True

/-- **Frame lemma.** A run made of actions of `l₀` and of the base objects can be replayed from
any configuration that agrees on `l₀`'s local state and on the base objects; the other local
states are untouched. -/
theorem Run.frame {l₀ : Fin n} {c₁ c₂ : I.Cfg} {as : List (Act n Inv Res)}
    (h : I.Run c₁ as c₂) (has : ∀ a ∈ as, a.Only l₀) {d₁ : I.Cfg}
    (hl : d₁.loc l₀ = c₁.loc l₀) (hm : d₁.mem = c₁.mem) :
    ∃ d₂, I.Run d₁ as d₂ ∧ d₂.loc l₀ = c₂.loc l₀ ∧ d₂.mem = c₂.mem ∧
      ∀ j, j ≠ l₀ → d₂.loc j = d₁.loc j := by
  induction h generalizing d₁ with
  | nil c => exact ⟨d₁, .nil _, hl, hm, fun _ _ => rfl⟩
  | @cons c c' c'' a as ht hr ih =>
    have ha := has a (by simp)
    have hrest : ∀ a ∈ as, a.Only l₀ := fun a h => has a (by simp [h])
    -- replay the first transition
    obtain ⟨d', ht', hl', hm', hj'⟩ : ∃ d', I.Trans d₁ a d' ∧ d'.loc l₀ = c'.loc l₀ ∧
        d'.mem = c'.mem ∧ ∀ j, j ≠ l₀ → d'.loc j = d₁.loc j := by
      cases ht with
      | @inv i x q q' hq ht =>
        simp only [Act.Only, Ext.proc] at ha; subst ha
        refine ⟨_, .inv (hl.trans hq) ht, by simp, by simp [hm], fun j hj => ?_⟩
        simp [Function.update_of_ne hj]
      | @res i r q q' hq ht =>
        simp only [Act.Only, Ext.proc] at ha; subst ha
        refine ⟨_, .res (hl.trans hq) ht, by simp, by simp [hm], fun j hj => ?_⟩
        simp [Function.update_of_ne hj]
      | @crash i q hq =>
        simp only [Act.Only, Ext.proc] at ha; subst ha
        refine ⟨_, .crash (hl.trans hq), by simp, by simp [hm], fun j hj => ?_⟩
        simp [Function.update_of_ne hj]
      | @step i q q' b' hq ht =>
        simp only [Act.Only] at ha; subst ha
        refine ⟨⟨Function.update d₁.loc i (some q'), b'⟩, .step (hl.trans hq) (hm ▸ ht),
          by simp, rfl, fun j hj => ?_⟩
        simp [Function.update_of_ne hj]
      | @base b' ht =>
        exact ⟨⟨d₁.loc, b'⟩, .base (hm ▸ ht), hl, rfl, fun _ _ => rfl⟩
    obtain ⟨d₂, hr', hl₂, hm₂, hj₂⟩ := ih hrest hl' hm'
    exact ⟨d₂, .cons ht' hr', hl₂, hm₂, fun j hj => (hj₂ j hj).trans (hj' j hj)⟩

/-- Splitting a run at its first external action. -/
theorem hist_eq_cons {as : List (Act n Inv Res)} {e : Ext n Inv Res} {l : List (Ext n Inv Res)}
    (h : hist as = e :: l) :
    ∃ α β, as = α ++ Act.ext e :: β ∧ hist α = [] ∧ hist β = l := by
  induction as with
  | nil => simp at h
  | cons a as ih =>
    cases a with
    | ext e' =>
      simp only [hist_cons_ext, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], as, rfl, rfl, rfl⟩
    | step i =>
      obtain ⟨α, β, rfl, h1, h2⟩ := ih (by simpa using h)
      exact ⟨Act.step i :: α, β, rfl, by simpa using h1, h2⟩
    | base =>
      obtain ⟨α, β, rfl, h1, h2⟩ := ih (by simpa using h)
      exact ⟨Act.base :: α, β, rfl, by simpa using h1, h2⟩

/-- In a reactive implementation, an internal run from a state where every process other than
`l₀` is idle only contains actions of `l₀` and of the base objects. -/
theorem Reach.only_of_reactive (hR : I.Reactive) {c c' : I.Cfg} {l : List (Ext n Inv Res)}
    (hc : I.Reach c l) {σ : Fin n → PStat} (hσ : runStat l = some σ) {l₀ : Fin n}
    (hidle : ∀ j, j ≠ l₀ → σ j = .idle) {as : List (Act n Inv Res)} (hr : I.Run c as c')
    (has : hist as = []) : ∀ a ∈ as, a.Only l₀ := by
  induction hr with
  | nil => simp
  | @cons c₁ c₂ c₃ a as ht hr ih =>
    have hha : hist [a] = [] ∧ hist as = [] := by
      have : hist (a :: as) = hist [a] ++ hist as := by
        rw [← hist_append]; rfl
      rw [this, List.append_eq_nil_iff] at has; exact has
    have hreach : I.Reach c₂ l := by simpa [hha.1] using hc.trans ht
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · cases b with
      | ext e => exact absurd hha.1 (by simp [hist, Act.ext?])
      | step i =>
        by_contra hne
        exact hR c₁ l hc σ hσ i (hidle i hne) ⟨_, ht⟩
      | base => trivial
    · exact ih hreach hha.2 b hb

/-! ## Infinite paths and fair extensions -/

variable (I) in
/-- Infinite paths starting at a given state. -/
structure Path (c : I.Cfg) where
  /-- States. -/
  cfg : ℕ → I.Cfg
  /-- Actions. -/
  act : ℕ → Act n Inv Res
  start : cfg 0 = c
  trans : ∀ k, I.Trans (cfg k) (act k) (cfg (k + 1))

/-- Prepending one transition to a path. -/
def Path.cons {c c' : I.Cfg} {a : Act n Inv Res} (ht : I.Trans c a c') (p : I.Path c') :
    I.Path c where
  cfg k := match k with
    | 0 => c
    | k + 1 => p.cfg k
  act k := match k with
    | 0 => a
    | k + 1 => p.act k
  start := rfl
  trans k := by
    cases k with
    | zero => simpa [p.start] using ht
    | succ k => exact p.trans k

/-- Prepending a finite run to a path. -/
theorem exists_path_append {c c' : I.Cfg} {as : List (Act n Inv Res)} (h : I.Run c as c')
    (q : I.Path c') : ∃ p : I.Path c, (∀ k (hk : k < as.length), p.act k = as[k]) ∧
      ∀ k, p.cfg (as.length + k) = q.cfg k ∧ p.act (as.length + k) = q.act k := by
  induction h with
  | nil c => exact ⟨q, fun k hk => by simp at hk, fun k => by simp⟩
  | @cons c₁ c₂ c₃ a as ht hr ih =>
    obtain ⟨p, hp1, hp2⟩ := ih q
    refine ⟨Path.cons ht p, fun k hk => ?_, fun k => ?_⟩
    · cases k with
      | zero => rfl
      | succ k => exact hp1 k (by simpa using hk)
    · have : (a :: as).length + k = (as.length + k) + 1 := by simp; omega
      rw [this]
      exact hp2 k

/-- An infinite execution from a path starting at an initial state. -/
def Path.toInfExec {c : I.Cfg} (p : I.Path c) (hc : I.IsInit c) : I.InfExec where
  cfg := p.cfg
  act := p.act
  init := by rw [p.start]; exact hc
  trans := p.trans

theorem hist_eq_nil_of_internal {as : List (Act n Inv Res)}
    (h : ∀ a ∈ as, a = Act.base ∨ ∃ i, a = Act.step i) : hist as = [] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rcases h a (by simp) with rfl | ⟨i, rfl⟩
    · simpa using ih fun b hb => h b (by simp [hb])
    · simpa using ih fun b hb => h b (by simp [hb])

/-- **Fair extension.** Suppose that from a reachable state `c`, along every internal
continuation, no external action other than a crash and no step of a process other than `i₀`
is ever enabled. Then the history of `c` is fair: a scheduler that runs `i₀` whenever it can
(and otherwise the base objects) produces a fair execution without further external actions. -/
theorem fin_mem_fairH_of_quiet {c : I.Cfg} {l : List (Ext n Inv Res)} (hc : I.Reach c l)
    (i₀ : Fin n)
    (hq : ∀ d as, I.Run c as d → hist as = [] →
      (∀ e : Ext n Inv Res, ¬ (Act.ext e).IsCrash → ¬ I.Enabled d (.ext e)) ∧
        ∀ j, j ≠ i₀ → ¬ I.Enabled d (.step j)) :
    Hist.fin l ∈ I.fairH := by
  classical
  let nxt : I.Cfg → Option (Act n Inv Res × I.Cfg) := fun d =>
    if h : ∃ d', I.Trans d (.step i₀) d' then some (.step i₀, h.choose)
    else if h : ∃ d', I.Trans d .base d' then some (.base, h.choose) else none
  have hnxt : ∀ d a d', nxt d = some (a, d') → I.Trans d a d' ∧ (a = .base ∨ ∃ i, a = .step i) := by
    intro d a d' h
    simp only [nxt] at h
    split_ifs at h with h1 h2
    · cases h; exact ⟨h1.choose_spec, Or.inr ⟨_, rfl⟩⟩
    · cases h; exact ⟨h2.choose_spec, Or.inl rfl⟩
  let st : ℕ → I.Cfg := fun k => Nat.rec c (fun _ d => match nxt d with
    | some (_, d') => d'
    | none => d) k
  let ac : ℕ → Act n Inv Res := fun k => match nxt (st k) with
    | some (a, _) => a
    | none => .base
  have hstep : ∀ k, nxt (st k) ≠ none → I.Trans (st k) (ac k) (st (k + 1)) ∧
      (ac k = .base ∨ ∃ i, ac k = .step i) := by
    intro k hk
    obtain ⟨⟨a, d'⟩, hs⟩ := Option.ne_none_iff_exists'.1 hk
    have h1 : st (k + 1) = d' := by simp only [st]; rw [hs]
    have h2 : ac k = a := by simp only [ac]; rw [hs]
    rw [h1, h2]; exact hnxt _ _ _ hs
  -- the run up to `m`, as long as the scheduler has not stopped
  have hrun : ∀ m, (∀ k < m, nxt (st k) ≠ none) →
      I.Run c ((List.range m).map ac) (st m) ∧ hist ((List.range m).map ac) = [] := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simpa [st] using Run.nil c, rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih fun k hk => hm k (by omega)
      obtain ⟨h3, h4⟩ := hstep m (hm m (by omega))
      rw [List.range_succ, List.map_append, List.map_singleton]
      refine ⟨h1.snoc h3, ?_⟩
      rw [hist_append, h2, hist_eq_nil_of_internal (by simpa using h4)]; rfl
  obtain ⟨c₀, as, h₀, hr₀, rfl⟩ := hc
  by_cases hstop : ∃ k, nxt (st k) = none
  · -- the scheduler stops: a finite fair execution
    let k₀ := Nat.find hstop
    have hk₀ : nxt (st k₀) = none := Nat.find_spec hstop
    obtain ⟨h1, h2⟩ := hrun k₀ fun k hk => Nat.find_min hstop hk
    refine Or.inl ⟨st k₀, hist as, ⟨c₀, as ++ (List.range k₀).map ac, h₀, hr₀.append h1,
      by simp [h2]⟩, ?_, rfl⟩
    intro a d' ht
    have hq' := hq _ _ h1 h2
    cases a with
    | ext e =>
      by_contra hne
      exact hq'.1 e hne ⟨d', ht⟩
    | step j =>
      by_cases hj : j = i₀
      · subst hj; simp only [nxt, dite_eq_left_of_eq_true (eq_true (⟨d', ht⟩ : ∃ d', I.Trans (st k₀) (.step j) d'))] at hk₀
        cases hk₀
      · exact absurd ⟨d', ht⟩ (hq'.2 j hj)
    | base =>
      have : ¬ ∃ d', I.Trans (st k₀) (.step i₀) d' := by
        intro h; simp only [nxt, dite_eq_left_of_eq_true (eq_true h)] at hk₀; cases hk₀
      simp only [nxt, dite_eq_right_of_eq_false (eq_false this), dite_eq_left_of_eq_true (eq_true (⟨d', ht⟩ : ∃ d', I.Trans (st k₀) .base d'))] at hk₀
      cases hk₀
  · -- the scheduler never stops: an infinite fair execution
    push Not at hstop
    have hst : ∀ k, I.Trans (st k) (ac k) (st (k + 1)) := fun k => (hstep k (hstop k)).1
    let q : I.Path c := ⟨st, ac, rfl, hst⟩
    obtain ⟨p, hp1, hp2⟩ := exists_path_append hr₀ q
    let e := p.toInfExec h₀
    have hreach : ∀ k, I.Run c ((List.range k).map ac) (st k) ∧
        hist ((List.range k).map ac) = [] := fun k => hrun k fun j _ => hstop j
    have hquiet : ∀ k, (∀ e : Ext n Inv Res, ¬ (Act.ext e).IsCrash →
        ¬ I.Enabled (st k) (.ext e)) ∧ ∀ j, j ≠ i₀ → ¬ I.Enabled (st k) (.step j) :=
      fun k => hq _ _ (hreach k).1 (hreach k).2
    have hpre : ∀ k, e.pre (as.length + k) = as ++ (List.range k).map ac := by
      intro k
      apply List.ext_getElem (by simp [InfExec.pre])
      intro m h1 h2
      simp only [InfExec.pre, List.getElem_map, List.getElem_range, e, Path.toInfExec]
      by_cases hm : m < as.length
      · rw [List.getElem_append_left hm, hp1 m hm]
      · have h3 := (hp2 (m - as.length)).2
        rw [show as.length + (m - as.length) = m by omega] at h3
        rw [List.getElem_append_right (by omega), h3]
        simp [q]
    refine Or.inr ⟨e, fun i => ?_, ⟨as.length, fun k hk => ?_⟩⟩
    · by_cases hinf : ∀ K, ∃ k ≥ K, ac k = .step i₀
      · by_cases hi : i = i₀
        · subst hi
          left
          intro K
          obtain ⟨k, hk, hk'⟩ := hinf K
          refine ⟨as.length + k, by omega, ?_⟩
          show (p.act (as.length + k)).IsProc i
          rw [(hp2 k).2]; show (ac k).IsProc i; rw [hk']; rfl
        · right
          intro K
          refine ⟨as.length + K, by omega, ?_⟩
          show ¬ I.NonCrashEnabled (p.cfg (as.length + K)) i
          rw [(hp2 K).1]
          rintro ⟨a, ha, hnc, hen⟩
          cases a with
          | ext e' => exact (hquiet K).1 e' hnc hen
          | step j =>
            simp only [Act.IsProc] at ha; subst ha
            exact (hquiet K).2 j hi hen
          | base => exact ha
      · push Not at hinf
        obtain ⟨K, hK⟩ := hinf
        right
        intro K'
        refine ⟨as.length + max K K', by omega, ?_⟩
        show ¬ I.NonCrashEnabled (p.cfg (as.length + max K K')) i
        rw [(hp2 _).1]
        rintro ⟨a, ha, hnc, hen⟩
        cases a with
        | ext e' => exact (hquiet _).1 e' hnc hen
        | step j =>
          simp only [Act.IsProc] at ha; subst ha
          by_cases hj : j = i₀
          · subst hj
            apply hK (max K K') (le_max_left _ _)
            have hen' : ∃ d', I.Trans (st (max K K')) (.step j) d' := hen
            show (match nxt (st (max K K')) with | some (a, _) => a | none => .base) = _
            simp only [nxt]; rw [dite_eq_left_of_eq_true (eq_true hen')]
          · exact (hquiet _).2 j hj hen
        | base => exact ha
    · show hist (e.pre k) = hist as
      obtain ⟨k', rfl⟩ : ∃ k', k = as.length + k' := ⟨k - as.length, by omega⟩
      rw [hpre, hist_append, (hreach k').2, List.append_nil]

theorem InfExec.pre_succ (e : I.InfExec) (k : ℕ) : e.pre (k + 1) = e.pre k ++ [e.act k] := by
  simp [InfExec.pre, List.range_succ]

theorem InfExec.pre_prefix (e : I.InfExec) {k m : ℕ} (h : k ≤ m) : e.pre k <+: e.pre m := by
  induction m with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [e.pre_succ]; exact (ih (by omega)).trans (List.prefix_append _ _)
    · exact List.prefix_refl _

theorem hist_prefix {as bs : List (Act n Inv Res)} (h : as <+: bs) : hist as <+: hist bs := by
  obtain ⟨t, rfl⟩ := h
  rw [hist_append]; exact List.prefix_append _ _

/-- An infinite execution assembled from blocks of three actions, block `k` producing the
external action `f k`. -/
theorem exists_infExec_of_blocks {f : ℕ → Ext n Inv Res} {P : ℕ → I.Cfg → Prop} {c₀ : I.Cfg}
    (h₀ : I.IsInit c₀) (hP₀ : P 0 c₀)
    (hstep : ∀ k c, P k c → ∃ a₀ a₁ a₂ c₁ c₂ c₃, I.Trans c a₀ c₁ ∧ I.Trans c₁ a₁ c₂ ∧
      I.Trans c₂ a₂ c₃ ∧ hist [a₀, a₁, a₂] = [f k] ∧ P (k + 1) c₃) :
    ∃ e : I.InfExec, e.HasHist (.inf f) := by
  classical
  -- a non-dependent choice of the blocks
  choose A₀ A₁ A₂ C₁ C₂ C₃ hT₀ hT₁ hT₂ hH hP using hstep
  let a₀ : ℕ → I.Cfg → Act n Inv Res := fun k c => if h : P k c then A₀ k c h else .base
  let a₁ : ℕ → I.Cfg → Act n Inv Res := fun k c => if h : P k c then A₁ k c h else .base
  let a₂ : ℕ → I.Cfg → Act n Inv Res := fun k c => if h : P k c then A₂ k c h else .base
  let d₁ : ℕ → I.Cfg → I.Cfg := fun k c => if h : P k c then C₁ k c h else c
  let d₂ : ℕ → I.Cfg → I.Cfg := fun k c => if h : P k c then C₂ k c h else c
  let d₃ : ℕ → I.Cfg → I.Cfg := fun k c => if h : P k c then C₃ k c h else c
  have hB : ∀ k c, P k c → I.Trans c (a₀ k c) (d₁ k c) ∧ I.Trans (d₁ k c) (a₁ k c) (d₂ k c) ∧
      I.Trans (d₂ k c) (a₂ k c) (d₃ k c) ∧ hist [a₀ k c, a₁ k c, a₂ k c] = [f k] ∧
      P (k + 1) (d₃ k c) := by
    intro k c h
    simp only [a₀, a₁, a₂, d₁, d₂, d₃, dite_eq_left_of_eq_true (eq_true h)]
    exact ⟨hT₀ k c h, hT₁ k c h, hT₂ k c h, hH k c h, hP k c h⟩
  let g : ℕ → I.Cfg := fun k => Nat.rec c₀ (fun k c => d₃ k c) k
  have hg : ∀ k, P k (g k) := by
    intro k
    induction k with
    | zero => exact hP₀
    | succ k ih => exact (hB k _ ih).2.2.2.2
  have hg' : ∀ k, g (k + 1) = d₃ k (g k) := fun k => rfl
  let F : ℕ → ℕ → I.Cfg := fun k j => match j with
    | 0 => g k
    | 1 => d₁ k (g k)
    | _ => d₂ k (g k)
  let A : ℕ → ℕ → Act n Inv Res := fun k j => match j with
    | 0 => a₀ k (g k)
    | 1 => a₁ k (g k)
    | _ => a₂ k (g k)
  let cfg : ℕ → I.Cfg := fun m => F (m / 3) (m % 3)
  let act : ℕ → Act n Inv Res := fun m => A (m / 3) (m % 3)
  have htr : ∀ m, I.Trans (cfg m) (act m) (cfg (m + 1)) := by
    intro m
    obtain ⟨hT0, hT1, hT2, -, -⟩ := hB _ _ (hg (m / 3))
    have hm := Nat.mod_lt m (show 3 > 0 by omega)
    rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
    · have e1 : (m + 1) % 3 = 1 := by omega
      have e2 : (m + 1) / 3 = m / 3 := by omega
      simp only [cfg, act, F, A, e1, e2, h]
      exact hT0
    · have e1 : (m + 1) % 3 = 2 := by omega
      have e2 : (m + 1) / 3 = m / 3 := by omega
      simp only [cfg, act, F, A, e1, e2, h]
      exact hT1
    · have e1 : (m + 1) % 3 = 0 := by omega
      have e2 : (m + 1) / 3 = m / 3 + 1 := by omega
      simp only [cfg, act, F, A, e1, e2, h, hg']
      exact hT2
  have h0 : cfg 0 = c₀ := rfl
  let e : I.InfExec := ⟨cfg, act, by rw [h0]; exact h₀, htr⟩
  have hblock : ∀ k, hist (e.pre (3 * k)) = pfx f k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk : e.pre (3 * (k + 1)) =
          e.pre (3 * k) ++ [a₀ k (g k), a₁ k (g k), a₂ k (g k)] := by
        rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, e.pre_succ, e.pre_succ, e.pre_succ]
        have x0 : e.act (3 * k) = a₀ k (g k) := by
          show A ((3 * k) / 3) ((3 * k) % 3) = _
          rw [show (3 * k) / 3 = k by omega, show (3 * k) % 3 = 0 by omega]; rfl
        have x1 : e.act (3 * k + 1) = a₁ k (g k) := by
          show A ((3 * k + 1) / 3) ((3 * k + 1) % 3) = _
          rw [show (3 * k + 1) / 3 = k by omega, show (3 * k + 1) % 3 = 1 by omega]; rfl
        have x2 : e.act (3 * k + 2) = a₂ k (g k) := by
          show A ((3 * k + 2) / 3) ((3 * k + 2) % 3) = _
          rw [show (3 * k + 2) / 3 = k by omega, show (3 * k + 2) % 3 = 2 by omega]; rfl
        rw [x0, x1, x2]; simp
      rw [hk, hist_append, ih, pfx_succ]
      exact congrArg _ (hB k _ (hg k)).2.2.2.1
  refine ⟨e, fun m => ?_, fun m => ⟨3 * m, ?_⟩⟩
  · have := hist_prefix (e.pre_prefix (show m ≤ 3 * m by omega))
    rw [hblock] at this
    exact FinPrefix.trans this (finPrefix_pfx f m)
  · show m ≤ (hist (e.pre (3 * m))).length
    rw [hblock]; simp

end Impl

end Podc.SafetyLivenessExclusion
