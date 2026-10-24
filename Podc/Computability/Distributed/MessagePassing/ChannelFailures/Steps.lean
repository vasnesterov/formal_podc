import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Solo
import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Restrict

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Steps.lean

/-!
# Step-level facts for the `ChannelFailures` model

* `loc_step_ne`: a step changes only the local state of its owner.
* `chan_step_of_ne`: a channel `q → p` changes only by steps of `q` or deliveries on `q → p`.
* `chan_step_deliver`: delivering the head `m` of `q → p` leaves the rest of that channel as a
  prefix of the new contents.
* **Histories are well formed** (`wellFormed_hist`), with the pending-operation accounting
  `(opsOf h p).length = (respsOf h p).length + pendCount C p` (`acc_run`).
* `opsOf_hist_eq_nil`: without invocation events no operation is invoked.
* `labAt_extend_subset`: labels of an extended execution after the prefix appear in the history
  of the extension.
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]
variable (Alg : Algorithm P A M L)

/-- A step does not change the local states of the other processes. -/
lemma loc_step_ne (C : Config P A M L) (e : Event P A) {q : P} (h : q ≠ e.owner) :
    (Alg.step C e).1.loc q = C.loc q := by
  have := agree_step_left Alg (Agree.refl (X := {q}) C) e (by simpa [eq_comm] using h)
  exact (this.1 q rfl).1

/-- A step neither of `q` nor delivering on `q → p` does not change the channel `q → p`. -/
lemma chan_step_of_ne (C : Config P A M L) (e : Event P A) {q p : P} (h1 : e.owner ≠ q)
    (h2 : e ≠ .deliver q p) : (Alg.step C e).1.chan q p = C.chan q p := by
  have key : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
      a ≠ q → (C'.apply a r).1.chan q p = C'.chan q p := by
    intro C' a r ha
    simp [Config.apply, Ne.symm ha]
  cases e with
  | invoke a o =>
    simp only [Algorithm.step]
    split
    · rfl
    · exact key _ _ _ h1
  | tick a c => exact key _ _ _ h1
  | deliver a b =>
    simp only [Algorithm.step]
    split
    · rfl
    · rename_i m rest _
      have hab : ¬ (a = q ∧ b = p) := by
        rintro ⟨rfl, rfl⟩; exact h2 rfl
      exact (key _ _ _ (by simpa using h1)).trans (by simp only [Config.pop]; rw [ite_eq_right (fun h => hab ⟨h.1.symm, h.2.symm⟩)])

/-- Delivering the head of `q → p`: the rest of the channel is a prefix of the new contents. -/
lemma chan_step_deliver (C : Config P A M L) {q p : P} {m : M} {rest : List M}
    (h : C.chan q p = m :: rest) : rest <+: (Alg.step C (.deliver q p)).1.chan q p := by
  simp only [Algorithm.step, h]
  simp only [Config.apply, Config.pop, and_self, ite_true]
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- Number of pending operations (`0` or `1`) of `p`. -/
def pendCount (C : Config P A M L) (p : P) : ℕ := if (C.pend p).isNone then 0 else 1

/-- Accounting between a history and a configuration: invocations = responses + pending. -/
def Acc (h : List (Label P A)) (C : Config P A M L) : Prop :=
  ∀ p, (opsOf h p).length = (respsOf h p).length + pendCount C p

lemma acc_apply {h : List (Label P A)} {C : Config P A M L} (hw : WellFormed h) (ha : Acc h C)
    (p : P) (r : L × List (P × M) × Option A.Resp) :
    WellFormed (h ++ (C.apply p r).2) ∧ Acc (h ++ (C.apply p r).2) (C.apply p r).1 := by
  simp only [Config.apply]
  rcases hp : C.pend p with _ | o <;> rcases hr : r.2.2 with _ | x
  · simp only [respOut, List.append_nil]
    refine ⟨hw, fun q => ?_⟩
    have := ha q
    by_cases hq : q = p
    · subst hq; simp [pendCount, hp, pendAfter] at this ⊢; omega
    · simpa [pendCount, Function.update_of_ne hq] using this
  · simp only [respOut, List.append_nil]
    refine ⟨hw, fun q => ?_⟩
    have := ha q
    by_cases hq : q = p
    · subst hq; simp [pendCount, hp, pendAfter] at this ⊢; omega
    · simpa [pendCount, Function.update_of_ne hq] using this
  · simp only [respOut, List.append_nil]
    refine ⟨hw, fun q => ?_⟩
    have := ha q
    by_cases hq : q = p
    · subst hq; simp [pendCount, hp, pendAfter] at this ⊢; omega
    · simpa [pendCount, Function.update_of_ne hq] using this
  · simp only [respOut]
    have hp' : (opsOf h p).length = (respsOf h p).length + 1 := by
      simpa [pendCount, hp] using ha p
    refine ⟨hw.append_ret hp', fun q => ?_⟩
    have := ha q
    by_cases hq : q = p
    · subst hq; simp [pendCount, pendAfter, hp'] at this ⊢
    · simp [pendCount, Function.update_of_ne hq, Ne.symm hq] at this ⊢; omega

lemma acc_step {h : List (Label P A)} {C : Config P A M L} (hw : WellFormed h) (ha : Acc h C)
    (e : Event P A) :
    WellFormed (h ++ (Alg.step C e).2) ∧ Acc (h ++ (Alg.step C e).2) (Alg.step C e).1 := by
  cases e with
  | invoke p o =>
    simp only [Algorithm.step]
    split
    · simpa using ⟨hw, ha⟩
    · rename_i hp
      have hp' : (opsOf h p).length = (respsOf h p).length := by
        simpa [pendCount, hp] using ha p
      have hw' := hw.append_inv (o := o) hp'
      have ha' : Acc (h ++ [.inv p o])
          ({ C with pend := Function.update C.pend p (some o) } : Config P A M L) := by
        intro q
        by_cases hq : q = p
        · subst hq; simp [pendCount, hp']
        · have := ha q
          simp [pendCount, Function.update_of_ne hq, Ne.symm hq] at this ⊢; omega
      have := acc_apply hw' ha' p (Alg.handle p (.invoke o) (C.loc p))
      simpa [List.append_assoc] using this
  | tick p c => exact acc_apply hw ha _ _
  | deliver q p =>
    simp only [Algorithm.step]
    split
    · simpa using ⟨hw, ha⟩
    · rename_i m rest _
      exact acc_apply hw (fun x => by simpa [pendCount, Config.pop] using ha x) _ _

lemma acc_run {h : List (Label P A)} {C : Config P A M L} (hw : WellFormed h) (ha : Acc h C)
    (E : List (Event P A)) :
    WellFormed (h ++ Alg.hist C E) ∧ Acc (h ++ Alg.hist C E) (Alg.run C E) := by
  induction E generalizing h C with
  | nil => simpa using ⟨hw, ha⟩
  | cons e E ih =>
    obtain ⟨h1, h2⟩ := acc_step Alg hw ha e
    have := ih h1 h2
    simpa [List.append_assoc] using this

lemma wellFormed_nil : WellFormed ([] : List (Label P A)) := by
  intro β ℓ γ h; simp at h

lemma acc_init : Acc ([] : List (Label P A)) Alg.initCfg := by
  intro p; simp [pendCount, Algorithm.initCfg]

/-- **Histories of the model are well formed.** -/
theorem wellFormed_hist (E : List (Event P A)) : WellFormed (Alg.hist Alg.initCfg E) := by
  simpa using (acc_run Alg wellFormed_nil (acc_init Alg) E).1

/-- Pending accounting along a run from the initial configuration. -/
theorem acc_hist (E : List (Event P A)) :
    Acc (Alg.hist Alg.initCfg E) (Alg.run Alg.initCfg E) := by
  simpa using (acc_run Alg wellFormed_nil (acc_init Alg) E).2

/-- Accounting for a run from any configuration (counts only). -/
lemma acc_run_counts (C : Config P A M L) (E : List (Event P A)) (p : P) :
    (opsOf (Alg.hist C E) p).length + pendCount C p =
      (respsOf (Alg.hist C E) p).length + pendCount (Alg.run C E) p := by
  induction E generalizing C with
  | nil => simp
  | cons e E ih =>
    have key : (opsOf (Alg.step C e).2 p).length + pendCount C p =
        (respsOf (Alg.step C e).2 p).length + pendCount (Alg.step C e).1 p := by
      have hap : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
          (opsOf (C'.apply a r).2 p).length + pendCount C' p =
            (respsOf (C'.apply a r).2 p).length + pendCount (C'.apply a r).1 p := by
        intro C' a r
        simp only [Config.apply]
        by_cases hq : p = a
        · subst hq
          rcases hp : C'.pend p with _ | o <;> rcases hr : r.2.2 with _ | x <;>
            simp [respOut, pendAfter, pendCount, hp, opsOf, respsOf, Label.invOf,
              Label.retOf]
        · have : ∀ l ∈ respOut a (C'.pend a) r.2.2, l.proc ≠ p := by
            intro l hl
            unfold respOut at hl
            split at hl
            · simp only [List.mem_singleton] at hl; subst hl; exact Ne.symm hq
            · simp at hl
          rw [opsOf_eq_nil_of_proc_ne this, respsOf_eq_nil_of_proc_ne this]
          simp [pendCount, Function.update_of_ne hq]
      cases e with
      | invoke a o =>
        simp only [Algorithm.step]
        split
        · simp
        · rename_i hp
          have := hap ({ C with pend := Function.update C.pend a (some o) } : Config P A M L) a
            (Alg.handle a (.invoke o) (C.loc a))
          by_cases hq : p = a
          · subst hq
            simp only [opsOf_cons, respsOf_cons, List.length_append] at this ⊢
            simp [pendCount, hp, Label.invOf, Label.retOf] at this ⊢; omega
          · simp only [opsOf_cons, respsOf_cons, List.length_append] at this ⊢
            simp [pendCount, Function.update_of_ne hq, Label.invOf, Label.retOf,
              Ne.symm hq] at this ⊢; omega
      | tick a c => exact hap _ _ _
      | deliver q a =>
        simp only [Algorithm.step]
        split
        · simp
        · rename_i m rest _
          have := hap (C.pop q a rest) a (Alg.handle a (.recv q m) (C.loc a))
          simpa [pendCount, Config.pop] using this
    have := ih (Alg.step C e).1
    simp only [Algorithm.hist_cons, Algorithm.run_cons, opsOf_append, respsOf_append,
      List.length_append]
    omega

/-- Non-invocation events produce no invocation labels. -/
lemma invOf_step_eq_none {C : Config P A M L} {e : Event P A} (he : ¬ e.IsInvoke)
    {l : Label P A} (hl : l ∈ (Alg.step C e).2) (p : P) : l.invOf p = none := by
  have key : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
      l ∈ (C'.apply a r).2 → l.invOf p = none := by
    intro C' a r hl
    simp only [Config.apply] at hl
    unfold respOut at hl
    split at hl
    · simp only [List.mem_singleton] at hl; subst hl; rfl
    · simp at hl
  cases e with
  | invoke a o => exact absurd trivial he
  | tick a c => exact key _ _ _ hl
  | deliver q a =>
    simp only [Algorithm.step] at hl
    split at hl
    · simp at hl
    · exact key _ _ _ hl

/-- Without invocation events, no operation is invoked. -/
lemma opsOf_hist_eq_nil (C : Config P A M L) {E : List (Event P A)}
    (hE : ∀ e ∈ E, ¬ e.IsInvoke) (p : P) : opsOf (Alg.hist C E) p = [] := by
  induction E generalizing C with
  | nil => rfl
  | cons e E ih =>
    simp only [Algorithm.hist_cons, opsOf_append, ih _ (fun e' he' => hE e' (by simp [he'])),
      List.append_nil]
    simp only [opsOf, List.filterMap_eq_nil_iff]
    exact fun l hl => invOf_step_eq_none Alg (hE e (by simp)) hl p

/-- An effective invocation produces the invocation label first. -/
lemma step_invoke_of_pend_none (C : Config P A M L) {p : P} {o : A.Op} (hp : C.pend p = none) :
    ∃ r, (Alg.step C (.invoke p o)).2 = .inv p o :: r ∧ ∀ l ∈ r, ∀ q, l.invOf q = none := by
  simp only [Algorithm.step, hp]
  refine ⟨_, rfl, fun l hl q => ?_⟩
  simp only [Config.apply] at hl
  unfold respOut at hl
  split at hl
  · simp only [List.mem_singleton] at hl; subst hl; rfl
  · simp at hl

/-- A pending operation stays pending in a step without a response of its process. -/
lemma pend_step_of_no_ret {C : Config P A M L} {p : P} (hp : C.pend p ≠ none) (e : Event P A)
    (hr : ∀ x, Label.ret p x ∉ (Alg.step C e).2) : (Alg.step C e).1.pend p ≠ none := by
  have key : ∀ (C' : Config P A M L) (r : L × List (P × M) × Option A.Resp), C'.pend p ≠ none →
      (∀ x, Label.ret p x ∉ (C'.apply p r).2) → (C'.apply p r).1.pend p ≠ none := by
    intro C' r h1 h2
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h1
    simp only [Config.apply, Function.update_self]
    rcases hx : r.2.2 with _ | x
    · simp [pendAfter, ho]
    · exfalso; apply h2 x; simp [Config.apply, respOut, ho, hx]
  by_cases ho : p = e.owner
  · cases e with
    | invoke q o =>
      simp only [Event.owner] at ho; subst ho
      obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 hp
      have : Alg.step C (.invoke p o) = (C, []) := by simp [Algorithm.step, ho']
      rw [this]; exact hp
    | tick q c =>
      simp only [Event.owner] at ho; subst ho
      exact key _ _ hp hr
    | deliver a q =>
      simp only [Event.owner] at ho; subst ho
      simp only [Algorithm.step] at hr ⊢
      split
      · exact hp
      · rename_i m rest h
        rw [h] at hr
        exact key _ _ (by simpa [Config.pop] using hp) hr
  · rw [pend_step_ne Alg C e ho]; exact hp

/-- Invocation labels come from invocation events. -/
lemma mem_opsOf_hist {C : Config P A M L} {E : List (Event P A)} {p : P} {o : A.Op}
    (h : o ∈ opsOf (Alg.hist C E) p) : Event.invoke p o ∈ E := by
  induction E generalizing C with
  | nil => simp at h
  | cons e E ih =>
    simp only [Algorithm.hist_cons, opsOf_append, List.mem_append] at h
    rcases h with h | h
    · simp only [opsOf, List.mem_filterMap] at h
      obtain ⟨l, hl, hlo⟩ := h
      by_cases he : e.IsInvoke
      · cases e with
        | invoke q o' =>
          simp only [Algorithm.step] at hl
          split at hl
          · simp at hl
          · simp only [List.mem_cons] at hl
            rcases hl with rfl | hl
            · simp only [Label.invOf] at hlo
              split_ifs at hlo with hq
              · simp only [Option.some.injEq] at hlo; subst hq; subst hlo; simp
            · simp only [Config.apply] at hl
              unfold respOut at hl
              split at hl
              · simp only [List.mem_singleton] at hl; subst hl; simp [Label.invOf] at hlo
              · simp at hl
        | tick => exact absurd he (by simp [Event.IsInvoke])
        | deliver => exact absurd he (by simp [Event.IsInvoke])
      · rw [invOf_step_eq_none Alg he hl p] at hlo; simp at hlo
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every label of a run belongs to the owner of some event of the run. -/
lemma proc_of_mem_hist {C : Config P A M L} {E : List (Event P A)} {l : Label P A}
    (hl : l ∈ Alg.hist C E) : ∃ e ∈ E, l.proc = e.owner := by
  induction E generalizing C with
  | nil => simp at hl
  | cons e E ih =>
    simp only [Algorithm.hist_cons, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ⟨e, by simp, proc_of_mem_step Alg hl⟩
    · obtain ⟨e', he', h⟩ := ih hl
      exact ⟨e', by simp [he'], h⟩

/-! ### Extended executions -/

/-- Labels of an extended execution produced after the prefix belong to the history of the
extension from the end of the prefix. -/
lemma labAt_extend_subset (E : List (Event P A)) (s : ℕ → Event P A) (u : ℕ) :
    Alg.labAt (extend E s) (E.length + u) =
      (Alg.step (Alg.run (Alg.run Alg.initCfg E) (Algorithm.pre s u)) (s u)).2 := by
  have hc : Alg.cfgAt (extend E s) (E.length + u) =
      Alg.run (Alg.run Alg.initCfg E) (Algorithm.pre s u) := by
    rw [Algorithm.cfgAt_eq_run, pre_extend_add, Algorithm.run_append]
  simp only [Algorithm.labAt, hc, extend_add]

lemma mem_hist_pre_succ (C : Config P A M L) (s : ℕ → Event P A) (u : ℕ) {l : Label P A}
    (hl : l ∈ (Alg.step (Alg.run C (Algorithm.pre s u)) (s u)).2) :
    l ∈ Alg.hist C (Algorithm.pre s (u + 1)) := by
  rw [Algorithm.pre_succ, Algorithm.hist_append]
  simp [hl]

omit [DecidableEq P] in
lemma pre_extend_of_le (E : List (Event P A)) (s : ℕ → Event P A) {t : ℕ} (ht : t ≤ E.length) :
    Algorithm.pre (extend E s) t = E.take t := by
  apply List.ext_getElem (by simp [Algorithm.pre]; omega)
  intro i h1 h2
  simp only [Algorithm.pre, List.length_map, List.length_range] at h1
  simp only [Algorithm.pre, List.getElem_map, List.getElem_range, extend, List.getElem_take]
  have hi : i < E.length := by omega
  simp [hi]

/-- **From a liveness guarantee to a finite extension.** Run `E`, invoke `o` at `p`, then the
canonical continuation under `f`. If the operation returns, it returns within a finite prefix of
canonical events. -/
theorem exists_canon_ret [Fintype P] {f : FailurePattern P} {p₀ : P} (hp₀ : p₀ ∉ f.procs)
    (K : ℕ) (E : List (Event P A)) (p : P) (o : A.Op) :
    let ev := extend (E ++ [.invoke p o])
      (canon Alg f K p₀ (Alg.run Alg.initCfg (E ++ [.invoke p o])))
    ev E.length = .invoke p o ∧ Alg.cfgAt ev E.length = Alg.run Alg.initCfg E ∧
      Alg.Fair f ev ∧ (∀ t, t < E.length → ev t ∈ E) ∧ (∀ t, E.length < t → CanonEvent f (ev t)) ∧
      (Alg.Returns ev p E.length → ∃ F : List (Event P A), (∀ e ∈ F, CanonEvent f e) ∧
        ∃ r, Label.ret p r ∈ Alg.hist (Alg.run Alg.initCfg E) (.invoke p o :: F)) := by
  intro ev
  set s := canon Alg f K p₀ (Alg.run Alg.initCfg (E ++ [.invoke p o]))
  have hlen : (E ++ [Event.invoke p o]).length = E.length + 1 := by simp
  have hcfg0 : Alg.cfgAt ev E.length = Alg.run Alg.initCfg E := by
    rw [Algorithm.cfgAt_eq_run, pre_extend_of_le _ _ (by simp)]
    simp
  refine ⟨by simp [ev, extend], hcfg0, fair_extend_canon Alg hp₀ _, fun t ht => ?_,
    fun t ht => ?_, ?_⟩
  · simp only [ev, extend, hlen, show t < E.length + 1 by omega, dite_true]
    rw [List.getElem_append_left ht]; exact List.getElem_mem _
  · obtain ⟨u, rfl⟩ : ∃ u, t = (E ++ [Event.invoke p o]).length + u := ⟨t - E.length - 1, by
      simp; omega⟩
    simp only [ev, extend_add]
    exact canon_spec hp₀ _ u
  · rintro ⟨t, ht, r, hr⟩
    rcases Nat.lt_or_ge t (E.length + 1) with h | h
    · have ht' : t = E.length := by omega
      subst ht'
      refine ⟨[], by simp, r, ?_⟩
      simp only [Algorithm.labAt, hcfg0] at hr
      have : ev E.length = .invoke p o := by simp [ev, extend]
      rw [this] at hr
      simpa using hr
    · obtain ⟨u, rfl⟩ : ∃ u, t = (E ++ [Event.invoke p o]).length + u := ⟨t - E.length - 1, by
        simp; omega⟩
      rw [labAt_extend_subset] at hr
      have hmem := mem_hist_pre_succ Alg _ s u hr
      refine ⟨Algorithm.pre s (u + 1), fun e he => ?_, r, ?_⟩
      · simp only [Algorithm.pre, List.mem_map] at he
        obtain ⟨i, -, rfl⟩ := he
        exact canon_spec hp₀ _ i
      · rw [Algorithm.hist_cons, Algorithm.run_append] at *
        simp only [Algorithm.run_cons, Algorithm.run_nil] at hmem
        exact List.mem_append_right _ hmem

end Cslib.ChannelFailures
