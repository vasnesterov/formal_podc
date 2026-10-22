import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Canonical

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Solo.lean

/-!
# Solo executions

A finite execution `E` followed by the canonical continuation under `f` is a fair `f`-execution
(`fair_extend_canon`). Hence, if an algorithm is `(f, T)`-obstruction-free and `p ∈ T` is correct,
then after any finite prefix without invocations an operation invoked by `p` and followed by the
canonical continuation eventually returns (`soloTerm_of_obstructionFree`). Such a *solo* execution
has history `[inv p o, ret p r]` (`hist_solo`).
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]

/-! ### Concatenating a finite and an infinite sequence -/

/-- The infinite sequence `E` followed by `s`. -/
def extend (E : List (Event P A)) (s : ℕ → Event P A) (t : ℕ) : Event P A :=
  if h : t < E.length then E[t] else s (t - E.length)

omit [DecidableEq P] in
@[simp] lemma extend_add (E : List (Event P A)) (s : ℕ → Event P A) (t : ℕ) :
    extend E s (E.length + t) = s t := by
  simp [extend]

omit [DecidableEq P] in
lemma pre_extend_length (E : List (Event P A)) (s : ℕ → Event P A) :
    Algorithm.pre (extend E s) E.length = E :=
  List.ext_getElem (by simp [Algorithm.pre]) fun i h1 h2 => by simp [Algorithm.pre, extend, h2]

omit [DecidableEq P] in
lemma pre_extend_add (E : List (Event P A)) (s : ℕ → Event P A) (t : ℕ) :
    Algorithm.pre (extend E s) (E.length + t) = E ++ Algorithm.pre s t := by
  rw [pre_add, pre_extend_length]
  congr 1
  simp [Algorithm.pre]

/-! ### Clock readings -/

/-- Clock readings of the same process do not decrease from `e` to `e'`. -/
def ClockLe (e e' : Event P A) : Prop := ∀ p c c', e = .tick p c → e' = .tick p c' → c ≤ c'

/-- All clock readings in `E` are at most `K`. -/
def ClockBound (E : List (Event P A)) (K : ℕ) : Prop := ∀ e ∈ E, ∀ p c, e = .tick p c → c ≤ K

/-! ### Pending operations -/

section Pending

variable (Alg : Algorithm P A M L)

/-- No process has a pending operation. -/
def Config.NoPend (C : Config P A M L) : Prop := ∀ q, C.pend q = none

omit [DecidableEq P] in
lemma noPend_initCfg : (Alg.initCfg).NoPend := fun _ => rfl

lemma pend_apply_ne (C : Config P A M L) {p q : P} (h : q ≠ p)
    (r : L × List (P × M) × Option A.Resp) : (C.apply p r).1.pend q = C.pend q := by
  simp [Config.apply, Function.update_of_ne h]

/-- A step does not change the pending operations of the other processes. -/
lemma pend_step_ne (C : Config P A M L) (e : Event P A) {q : P} (h : q ≠ e.owner) :
    (Alg.step C e).1.pend q = C.pend q := by
  cases e with
  | invoke p o =>
    simp only [Event.owner] at h
    simp only [Algorithm.step]
    split
    · rfl
    · rw [pend_apply_ne _ h]; simp [Function.update_of_ne h]
  | tick p c => exact pend_apply_ne _ h _
  | deliver a p =>
    simp only [Event.owner] at h
    simp only [Algorithm.step]
    split
    · rfl
    · rw [pend_apply_ne _ h]; rfl

lemma step_noPend {C : Config P A M L} (hC : C.NoPend) {e : Event P A} (he : ¬ e.IsInvoke) :
    (Alg.step C e).1.NoPend ∧ (Alg.step C e).2 = [] := by
  have key : ∀ (C' : Config P A M L) (p : P) (r : L × List (P × M) × Option A.Resp),
      C'.NoPend → (C'.apply p r).1.NoPend ∧ (C'.apply p r).2 = [] := by
    intro C' p r h
    refine ⟨fun q => ?_, ?_⟩
    · simp only [Config.apply]
      by_cases hq : q = p
      · subst hq; simp [h q, pendAfter]
      · simp [Function.update_of_ne hq, h q]
    · simp [Config.apply, h p, respOut]
  cases e with
  | invoke p o => exact absurd trivial he
  | tick p c => exact key _ _ _ hC
  | deliver a p =>
    simp only [Algorithm.step]
    split
    · exact ⟨hC, rfl⟩
    · exact key _ _ _ hC

lemma run_noPend {C : Config P A M L} (hC : C.NoPend) {E : List (Event P A)}
    (hE : ∀ e ∈ E, ¬ e.IsInvoke) : (Alg.run C E).NoPend ∧ Alg.hist C E = [] := by
  induction E generalizing C with
  | nil => exact ⟨hC, rfl⟩
  | cons e E ih =>
    obtain ⟨h1, h2⟩ := step_noPend Alg hC (hE e List.mem_cons_self)
    obtain ⟨h3, h4⟩ := ih h1 fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    exact ⟨h3, by simp [h2, h4]⟩

/-- With only `p` possibly pending and no invocations, the history is `[]` or one response
of `p`. -/
lemma hist_onePend {p : P} {C : Config P A M L} (hC : ∀ q ≠ p, C.pend q = none)
    {E : List (Event P A)} (hE : ∀ e ∈ E, ¬ e.IsInvoke) :
    Alg.hist C E = [] ∨ ∃ r, Alg.hist C E = [.ret p r] := by
  induction E generalizing C with
  | nil => exact Or.inl rfl
  | cons e E ih =>
    have hE' : ∀ e' ∈ E, ¬ e'.IsInvoke := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    have he : ¬ e.IsInvoke := hE e List.mem_cons_self
    by_cases hown : e.owner = p
    · -- the step of `p`: either no label, or the response
      have key : ∀ (C' : Config P A M L) (r : L × List (P × M) × Option A.Resp),
          (∀ q ≠ p, C'.pend q = none) →
          ((C'.apply p r).2 = [] ∧ ∀ q ≠ p, (C'.apply p r).1.pend q = none) ∨
          ∃ x, (C'.apply p r).2 = [.ret p x] ∧ (C'.apply p r).1.NoPend := by
        intro C' r h
        rcases hp : C'.pend p with _ | o
        · left
          refine ⟨by simp [Config.apply, hp, respOut], fun q hq => ?_⟩
          rw [pend_apply_ne _ hq]; exact h q hq
        · rcases hr : r.2.2 with _ | x
          · left
            refine ⟨by simp [Config.apply, hp, hr, respOut], fun q hq => ?_⟩
            rw [pend_apply_ne _ hq]; exact h q hq
          · right
            refine ⟨x, by simp [Config.apply, hp, hr, respOut], fun q => ?_⟩
            by_cases hq : q = p
            · subst hq; simp [Config.apply, hp, hr, pendAfter]
            · rw [pend_apply_ne _ hq]; exact h q hq
      have hcases : ((Alg.step C e).2 = [] ∧ ∀ q ≠ p, (Alg.step C e).1.pend q = none) ∨
          ∃ x, (Alg.step C e).2 = [.ret p x] ∧ (Alg.step C e).1.NoPend := by
        cases e with
        | invoke a o => exact absurd trivial he
        | tick a c =>
          simp only [Event.owner] at hown; subst hown; exact key _ _ hC
        | deliver a b =>
          simp only [Event.owner] at hown; subst hown
          simp only [Algorithm.step]
          split
          · exact Or.inl ⟨rfl, hC⟩
          · exact key _ _ hC
      rcases hcases with ⟨h1, h2⟩ | ⟨x, h1, h2⟩
      · simpa [h1] using ih h2 hE'
      · right; exact ⟨x, by simp [h1, (run_noPend Alg h2 hE').2]⟩
    · have hnp : C.pend e.owner = none := hC _ hown
      have h1 : (Alg.step C e).2 = [] := by
        have hall : ∀ l ∈ (Alg.step C e).2, False := by
          intro l hl
          cases e with
          | invoke a o => exact he trivial
          | tick a c =>
            simp only [Algorithm.step, Config.apply] at hl
            simp only [Event.owner] at hnp
            simp [hnp, respOut] at hl
          | deliver a b =>
            simp only [Event.owner] at hnp
            simp only [Algorithm.step] at hl
            split at hl
            · simp at hl
            · simp [Config.apply, Config.pop, hnp, respOut] at hl
        exact List.eq_nil_iff_forall_not_mem.2 hall
      have h2 : ∀ q ≠ p, (Alg.step C e).1.pend q = none := by
        intro q hq
        by_cases hqo : q = e.owner
        · subst hqo
          cases e with
          | invoke a o => exact absurd trivial he
          | tick a c =>
            simp only [Algorithm.step, Config.apply, Event.owner] at hnp ⊢
            simp [hnp, pendAfter]
          | deliver a b =>
            simp only [Event.owner] at hnp ⊢
            simp only [Algorithm.step]
            split
            · exact hnp
            · simp [Config.apply, Config.pop, hnp, pendAfter]
        · rw [pend_step_ne Alg C e hqo]; exact hC q hq
      simpa [h1] using ih h2 hE'

/-- **Solo histories.** From a configuration without pending operations, an invocation of `p`
followed by events without invocations has history `[inv p o]` or `[inv p o, ret p r]`. -/
lemma hist_solo {C : Config P A M L} (hC : C.NoPend) (p : P) (o : A.Op) {E : List (Event P A)}
    (hE : ∀ e ∈ E, ¬ e.IsInvoke) {r : A.Resp}
    (hr : Label.ret p r ∈ Alg.hist C (.invoke p o :: E)) :
    Alg.hist C (.invoke p o :: E) = [.inv p o, .ret p r] := by
  have h1 : ∀ q ≠ p, ({ C with pend := Function.update C.pend p (some o) } : Config P A M L).pend q
      = none := fun q hq => by simp [Function.update_of_ne hq, hC q]
  set C' : Config P A M L := { C with pend := Function.update C.pend p (some o) }
  have hstep : Alg.step C (.invoke p o) =
      ((C'.apply p (Alg.handle p (.invoke o) (C.loc p))).1,
        .inv p o :: (C'.apply p (Alg.handle p (.invoke o) (C.loc p))).2) := by
    simp [Algorithm.step, hC p, C']
  have hpend : ∀ q ≠ p, (C'.apply p (Alg.handle p (.invoke o) (C.loc p))).1.pend q = none :=
    fun q hq => by rw [pend_apply_ne _ hq]; exact h1 q hq
  have hlab : (C'.apply p (Alg.handle p (.invoke o) (C.loc p))).2 = [] ∨
      ∃ x, (C'.apply p (Alg.handle p (.invoke o) (C.loc p))).2 = [.ret p x] ∧
        (C'.apply p (Alg.handle p (.invoke o) (C.loc p))).1.NoPend := by
    rcases hx : (Alg.handle p (.invoke o) (C.loc p)).2.2 with _ | x
    · left; simp [Config.apply, hx, respOut]
    · right
      refine ⟨x, by simp [Config.apply, hx, respOut, C'], fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp [Config.apply, hx, pendAfter, C']
      · exact hpend q hq
  rw [Algorithm.hist_cons, hstep] at hr ⊢
  simp only at hr ⊢
  rcases hlab with h | ⟨x, h, hnp⟩
  · rw [h] at hr ⊢
    rcases hist_onePend Alg hpend hE with h' | ⟨y, h'⟩
    · rw [h'] at hr; simp at hr
    · rw [h'] at hr ⊢; simp at hr; simp [hr]
  · rw [h] at hr ⊢
    rw [(run_noPend Alg hnp hE).2] at hr ⊢
    simp at hr; simp [hr]

end Pending

/-! ### Fairness of the canonical extension -/

section Fair

variable (Alg : Algorithm P A M L)

lemma hist_pre (ev : ℕ → Event P A) (n : ℕ) :
    Alg.hist Alg.initCfg (Algorithm.pre ev n) = (List.range n).flatMap (Alg.labAt ev) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Algorithm.pre_succ, Algorithm.hist_append, ih, ← Algorithm.cfgAt_eq_run, List.range_succ,
      List.flatMap_append]
    simp [Algorithm.labAt]

lemma cfgAt_add (ev : ℕ → Event P A) (T n : ℕ) :
    Alg.cfgAt ev (T + n) = Alg.run (Alg.cfgAt ev T) ((List.range n).map fun i => ev (T + i)) := by
  rw [Algorithm.cfgAt_eq_run, Algorithm.cfgAt_eq_run, pre_add, Algorithm.run_append]

omit [DecidableEq P] in
lemma canonEvent_not_invoke {f : FailurePattern P} {e : Event P A} (h : CanonEvent f e) :
    ¬ e.IsInvoke := by
  cases e <;> simp_all [CanonEvent, Event.IsInvoke]

variable [Fintype P] {f : FailurePattern P} {K : ℕ} {p₀ : P}

/-- In the canonical extension, exactly the processes of `f.procs` crash. -/
lemma crashed_extend_canon (hp₀ : p₀ ∉ f.procs) (E : List (Event P A)) {q : P}
    (hq : q ∈ f.procs) :
    Algorithm.Crashed f (extend E (canon Alg f K p₀ (Alg.run Alg.initCfg E))) q := by
  refine ⟨hq, E.length, fun t ht => ?_⟩
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [extend_add]
  intro hown
  have := canon_spec (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E) u
  generalize canon Alg f K p₀ (Alg.run Alg.initCfg E) u = e at this hown
  cases e <;> simp_all [CanonEvent, FailurePattern.Edge]

/-- **A finite execution followed by the canonical continuation is fair.** -/
theorem fair_extend_canon (hp₀ : p₀ ∉ f.procs) (E : List (Event P A)) :
    Alg.Fair f (extend E (canon Alg f K p₀ (Alg.run Alg.initCfg E))) := by
  set s := canon Alg f K p₀ (Alg.run Alg.initCfg E)
  have hcr : ∀ q, ¬ Algorithm.Crashed f (extend E s) q → q ∉ f.procs :=
    fun q h hq => h (crashed_extend_canon Alg hp₀ E hq)
  refine ⟨fun q hq T => ?_, fun q p hq hp hqp T hT => ?_⟩
  · obtain ⟨t, ht, -, htick⟩ := canon_tick (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E)
      (hcr q hq) (T - E.length)
    exact ⟨E.length + t, by omega, _, by rw [extend_add]; exact htick⟩
  · have hedge : f.Edge q p := ⟨hcr q hq, hcr p hp, hqp⟩
    by_contra hcon
    push Not at hcon
    set u := T - E.length
    have hT' : T + (E.length + u - T) = E.length + u := by omega
    have hpref := chan_prefix_run Alg (Alg.cfgAt (extend E s) T)
      ((List.range (E.length + u - T)).map fun i => extend E s (T + i)) (by
        intro e he
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
        exact hcon _ (by omega))
    have hc : Alg.cfgAt (extend E s) (E.length + u) =
        Alg.run (Alg.run Alg.initCfg E) (Algorithm.pre s u) := by
      rw [Algorithm.cfgAt_eq_run, pre_extend_add, Algorithm.run_append]
    rw [← cfgAt_add, hT', hc] at hpref
    have hne : (Alg.run (Alg.run Alg.initCfg E) (Algorithm.pre s u)).chan q p ≠ [] := by
      intro h; rw [h] at hpref; exact hT (List.prefix_nil.1 hpref)
    obtain ⟨t, ht, hdel⟩ := canon_deliver (Alg := Alg) (K := K) hp₀ _ hedge u hne
    exact hcon (E.length + t) (by omega) (by rw [extend_add]; exact hdel)

end Fair

/-! ### Solo termination -/

section SoloTerm

variable (Alg : Algorithm P A M L) [Fintype P]

/-- The solo continuation: `p` invokes `o` after `E₀`, then the canonical continuation under `f`
(clock readings above `K`) runs for `N` steps. -/
noncomputable def soloEvents (f : FailurePattern P) (K : ℕ) (E₀ : List (Event P A)) (p : P)
    (o : A.Op) (N : ℕ) : List (Event P A) :=
  .invoke p o :: Algorithm.pre (canon Alg f K p (Alg.run Alg.initCfg (E₀ ++ [.invoke p o]))) N

/-- **Solo termination** of `o` at `p` under `f`: after any finite prefix without invocations
(with monotone clock readings bounded by `K`), the solo continuation of `p` returns. -/
def SoloTerm (f : FailurePattern P) (p : P) (o : A.Op) : Prop :=
  ∀ E₀ : List (Event P A), (∀ e ∈ E₀, ¬ e.IsInvoke) → E₀.Pairwise ClockLe → ∀ K, ClockBound E₀ K →
    ∃ N r, Label.ret p r ∈ Alg.hist (Alg.run Alg.initCfg E₀) (soloEvents Alg f K E₀ p o N)

lemma soloEvents_not_invoke {f : FailurePattern P} {K : ℕ} {E₀ : List (Event P A)} {p : P}
    (hp : p ∉ f.procs) {o : A.Op} {N : ℕ} :
    ∀ e ∈ (soloEvents Alg f K E₀ p o N).tail, ¬ e.IsInvoke := by
  intro e he
  simp only [soloEvents, List.tail_cons, Algorithm.pre, List.mem_map] at he
  obtain ⟨i, -, rfl⟩ := he
  exact canonEvent_not_invoke (canon_spec hp _ i)

/-- The history of a solo execution that returns. -/
lemma hist_soloEvents {f : FailurePattern P} {K : ℕ} {E₀ : List (Event P A)} {p : P}
    (hp : p ∉ f.procs) {o : A.Op} {N : ℕ} (hE₀ : ∀ e ∈ E₀, ¬ e.IsInvoke) {r : A.Resp}
    (hr : Label.ret p r ∈ Alg.hist (Alg.run Alg.initCfg E₀) (soloEvents Alg f K E₀ p o N)) :
    Alg.hist (Alg.run Alg.initCfg E₀) (soloEvents Alg f K E₀ p o N) = [.inv p o, .ret p r] :=
  hist_solo Alg (run_noPend Alg (noPend_initCfg Alg) hE₀).1 p o
    (soloEvents_not_invoke Alg hp) hr

/-- The solo execution as an infinite execution, and its basic properties used to apply
liveness assumptions. -/
lemma solo_setup {f : FailurePattern P} {K : ℕ} {E₀ : List (Event P A)} {p : P}
    (hp : p ∉ f.procs) {o : A.Op} (hE₀ : ∀ e ∈ E₀, ¬ e.IsInvoke) :
    let ev := extend (E₀ ++ [.invoke p o]) (canon Alg f K p (Alg.run Alg.initCfg (E₀ ++ [.invoke p o])))
    ev E₀.length = .invoke p o ∧ (Alg.cfgAt ev E₀.length).pend p = none ∧
      Alg.EventuallySolo f ev p E₀.length ∧
      (Alg.Returns ev p E₀.length →
        ∃ N r, Label.ret p r ∈ Alg.hist (Alg.run Alg.initCfg E₀) (soloEvents Alg f K E₀ p o N)) := by
  intro ev
  set s := canon Alg f K p (Alg.run Alg.initCfg (E₀ ++ [.invoke p o]))
  have hlen : (E₀ ++ [Event.invoke p o]).length = E₀.length + 1 := by simp
  have hcfg0 : Alg.cfgAt ev E₀.length = Alg.run Alg.initCfg E₀ := by
    rw [Algorithm.cfgAt_eq_run]
    congr 1
    apply List.ext_getElem (by simp [Algorithm.pre])
    intro i h1 h2
    simp only [Algorithm.pre, List.length_map, List.length_range] at h1
    simp only [Algorithm.pre, List.getElem_map, List.getElem_range, ev, extend]
    have hi : i < (E₀ ++ [Event.invoke p o]).length := by simp; omega
    simp only [hi, dite_true]
    rw [List.getElem_append_left h1]
  have hnp := (run_noPend Alg (noPend_initCfg Alg) hE₀).1
  refine ⟨by simp [ev, extend], by rw [hcfg0]; exact hnp p, ⟨E₀.length + 1, by omega, ?_, ?_⟩, ?_⟩
  · rintro t ht q ⟨o', ho', -⟩
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [← hlen] at ho'
    simp only [ev, extend_add] at ho'
    have := canon_spec (Alg := Alg) (K := K) hp (Alg.run Alg.initCfg (E₀ ++ [.invoke p o])) u
    rw [ho'] at this; exact absurd this (by simp [CanonEvent])
  · intro q hq hpend
    exfalso; apply hpend
    rw [← hlen, Algorithm.cfgAt_eq_run, pre_extend_length, Algorithm.run_append]
    simp only [Algorithm.run_cons, Algorithm.run_nil]
    rw [pend_step_ne Alg _ _ (by simpa using hq)]
    exact hnp q
  · rintro ⟨t, ht, r, hr⟩
    refine ⟨t - E₀.length, r, ?_⟩
    have h1 : Label.ret p r ∈ Alg.hist Alg.initCfg (Algorithm.pre ev (t + 1)) := by
      rw [hist_pre]; exact List.mem_flatMap.2 ⟨t, by simp, hr⟩
    have heq : t + 1 = (E₀ ++ [Event.invoke p o]).length + (t - E₀.length) := by simp; omega
    rw [heq, pre_extend_add, List.append_assoc, Algorithm.hist_append,
      (run_noPend Alg (noPend_initCfg Alg) hE₀).2, List.nil_append] at h1
    simpa [soloEvents] using h1

/-- `(f, T)`-obstruction-freedom gives solo termination at correct processes of `T`. -/
theorem soloTerm_of_obstructionFree {f : FailurePattern P} {T : Set P}
    (hOF : Alg.ObstructionFree f T) {p : P} (hpT : p ∈ T) (hp : p ∉ f.procs) (o : A.Op) :
    SoloTerm Alg f p o := by
  intro E₀ hE₀ _ K _
  obtain ⟨h1, h2, h3, h4⟩ := solo_setup Alg (K := K) hp (o := o) hE₀
  exact h4 (hOF _ (fair_extend_canon Alg hp _) p hpT _ o h1 h2 h3)

end SoloTerm

end Cslib.ChannelFailures
