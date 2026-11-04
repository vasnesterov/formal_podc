import Papers.PODC2013.TMObservationalRefinement.NonVacuity

/-!
# Theorem 24 is false

Theorem 24 of the paper claims `H_C ⊑_state H_A ⟹ H_C|complete ⊑ H_A|complete`. We show that it
fails whenever all primitive commands are deterministic (`theorem_24_false`).

The counterexample: a single thread `t` and a single object method `o.f`.
* `H_C` is the set of prefixes of `H = (t,txbegin) (t,OK) (t,call o.f(1)) (t,aborted)`;
* `H_A` is the set of prefixes of `S_v = (t,txbegin) (t,OK) (t,call o.f(1)) (t,ret(v) o.f)
  (t,txcommit) (t,aborted)`, for all `v`.

`H` is complete, but no complete history of `H_A` has the same length, so
`H_C|complete ⋢ H_A|complete`. Still `H_C ⊑_state H_A`: in a trace with history `H` the abort of
the call comes from the rule for aborted calls of Figure 2, `y := o.f(e)`. Replacing it with a
successful call returning the current value `v` of `y` (and, if the call was the last command of
its atomic block, letting the block request a commit that gets aborted) gives a trace of the same
program with a history in `H_A` and the same final states: the assignment `y := v` does not change
the (unique, by determinism) current state.
-/

set_option linter.unusedSectionVars false

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C]

lemma t24_mem_of_eq {α : Type} {l A B : List α} {x : α} (h : l = A ++ x :: B) : x ∈ l := by
  rw [h]; simp

/-- In a trace of `A(C)_t`, a method call is immediately followed by an interface action. -/
lemma Tr.t24_next_of_call {t : T} {Cm : Cmd LV O M C BE IE} {γ : List (Act T O M C)} (h : Tr t Cm γ)
    {o : O} {f : M} {n : ℤ} :
    ∀ α δ, γ = α ++ iface t (.call o f n) :: δ → ∃ k δ', δ = iface t k :: δ' := by
  induction h with
  | prim c => intro α δ e; have := t24_mem_of_eq e; simp at this
  | seq h₁ h₂ ih₁ ih₂ =>
    intro α δ e
    rcases split_append_cons e with ⟨B', e1, rfl⟩ | ⟨A', -, e2⟩
    · obtain ⟨k, δ', rfl⟩ := ih₁ α B' e1; exact ⟨k, δ' ++ _, rfl⟩
    · exact ih₂ A' δ e2
  | iteT _ ih | iteF _ ih =>
    intro α δ e
    rcases α with _ | ⟨a, α⟩
    · simp at e
    · simp only [List.cons_append, List.cons.injEq] at e; exact ih α δ e.2
  | whileF => intro α δ e; have := t24_mem_of_eq e; simp at this
  | whileT h₁ h₂ ih₁ ih₂ =>
    intro α δ e
    rcases α with _ | ⟨a, α⟩
    · simp at e
    · simp only [List.cons_append, List.cons.injEq] at e
      rcases split_append_cons e.2 with ⟨B', e1, rfl⟩ | ⟨A', -, e2⟩
      · obtain ⟨k, δ', rfl⟩ := ih₁ α B' e1; exact ⟨k, δ' ++ _, rfl⟩
      · exact ih₂ A' δ e2
  | callRet n n' =>
    intro α δ e
    rcases α with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, α⟩⟩⟩⟩ <;> simp at e
    exact ⟨_, _, e.2.2.symm⟩
  | callAbort n =>
    intro α δ e
    rcases α with _ | ⟨a, _ | ⟨b, _ | ⟨c, α⟩⟩⟩ <;> simp at e
    exact ⟨_, _, e.2.2.symm⟩
  | @atomicAbort x Cb τ h ih =>
    intro α δ e
    rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
    · simp at e
    · simp at e
    · simp only [List.cons_append, List.cons.injEq] at e
      have e' : (τ ++ [iface t aborted]) ++ [cmd t (assign t x (vAb C))] =
          α ++ iface t (.call o f n) :: δ := by simpa using e.2.2
      rcases split_append_cons e' with ⟨B', e1, rfl⟩ | ⟨A', -, e2⟩
      · obtain ⟨k, δ', rfl⟩ := ih α B' e1; exact ⟨k, _, rfl⟩
      · have := t24_mem_of_eq e2; simp at this
  | atomicCommit h _ ih | atomicCommitAbort h _ ih =>
    intro α δ e
    rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
    · simp at e
    · simp at e
    · simp only [List.cons_append, List.cons.injEq] at e
      rcases split_append_cons e.2.2 with ⟨B', e1, rfl⟩ | ⟨A', -, e2⟩
      · obtain ⟨k, δ', rfl⟩ := ih α B' e1; exact ⟨k, _, rfl⟩
      · have := t24_mem_of_eq e2; simp at this

/-- Replacement of an aborted call `call o.f(n) aborted` by a successful one returning `v` and
assigning `v` to the target variable `y`. -/
def t24Ya (t : T) (y : LV) (v : ℤ) (o : O) (f : M) : List (Act T O M C) :=
  [iface t (.ret v o f), cmd t (assign t y v)]

/-- As `t24Ya`, followed by a commit request that is aborted (when the call ended its atomic block). -/
def t24Yb (t : T) (y : LV) (v : ℤ) (o : O) (f : M) : List (Act T O M C) :=
  [iface t (.ret v o f), cmd t (assign t y v), iface t txcommit, iface t aborted]

/-- The result of the surgery: for some target variable `y` and every value `v`, replacing the
`aborted` after the call by `t24Ya` or `t24Yb` gives a list satisfying `R`. -/
def T24SurgOK (R : List (Act T O M C) → Prop) (t : T) (o : O) (f : M) (n : ℤ)
    (α β : List (Act T O M C)) : Prop :=
  ∃ y : LV, ∀ v, ∃ Y, (Y = t24Ya t y v o f ∨ Y = t24Yb t y v o f) ∧
    R (α ++ iface t (.call o f n) :: (Y ++ β))

lemma t24_not_end_of {α : Type} {X Y β : List α} {a : α} (hX : ∀ τ', X ++ β ≠ τ' ++ [a])
    (hβ : β ≠ []) : ∀ τ', Y ++ β ≠ τ' ++ [a] := by
  obtain ⟨β₀, b, rfl⟩ := (List.eq_nil_or_concat β).resolve_left hβ
  intro τ' h
  have hb : b = a := by have := congrArg List.getLast? h; simpa using this
  subst hb; exact hX (X ++ β₀) (by simp)

lemma t24_surg_append {R₁ R₂ : List (Act T O M C) → Prop} {τ₁ τ₂ : List (Act T O M C)} {t : T}
    {o : O} {f : M} {n : ℤ} (h₁ : R₁ τ₁) (h₂ : R₂ τ₂)
    (N₁ : ∀ α δ, τ₁ = α ++ iface t (.call o f n) :: δ → ∃ k δ', δ = iface t k :: δ')
    (ih₁ : ∀ α β, τ₁ = α ++ iface t (.call o f n) :: iface t aborted :: β →
      T24SurgOK (LV := LV) R₁ t o f n α β)
    (ih₂ : ∀ α β, τ₂ = α ++ iface t (.call o f n) :: iface t aborted :: β →
      T24SurgOK (LV := LV) R₂ t o f n α β)
    {α β : List (Act T O M C)} (e : τ₁ ++ τ₂ = α ++ iface t (.call o f n) :: iface t aborted :: β) :
    T24SurgOK (LV := LV) (fun l => ∃ l₁ l₂, R₁ l₁ ∧ R₂ l₂ ∧ l = l₁ ++ l₂) t o f n α β := by
  have e' : τ₁ ++ τ₂ = (α ++ [iface t (.call o f n)]) ++ iface t aborted :: β := by simpa using e
  rcases split_append_cons e' with ⟨B', e1, rfl⟩ | ⟨A', e1, e2⟩
  · obtain ⟨y, hy⟩ := ih₁ α B' (by simpa using e1)
    refine ⟨y, fun v => ?_⟩
    obtain ⟨Y, hY, htr⟩ := hy v
    exact ⟨Y, hY, _, _, htr, h₂, by simp⟩
  · rcases List.eq_nil_or_concat A' with rfl | ⟨A'', z, rfl⟩
    · obtain ⟨k, δ', h⟩ := N₁ α [] (by simpa using e1.symm)
      simp at h
    · have e1' : α ++ [iface t (.call o f n)] = (τ₁ ++ A'') ++ [z] := by simpa using e1
      obtain ⟨rfl, e4⟩ := List.append_inj' e1' rfl
      simp only [List.cons.injEq, and_true] at e4
      subst e4
      obtain ⟨y, hy⟩ := ih₂ A'' β (by simpa using e2)
      refine ⟨y, fun v => ?_⟩
      obtain ⟨Y, hY, htr⟩ := hy v
      exact ⟨Y, hY, _, _, h₁, htr, by simp⟩

/-- **Derivation surgery.** If a trace of `A(C)_t` contains an aborted call `call o.f(n) aborted`
(which comes from the rule for aborted calls of Figure 2, with some target variable `y`), then
replacing `aborted` by `ret(v) o.f` followed by `y := v` — and, if the call was the last command
of its atomic block, also by a commit request that is aborted — gives a trace of `A(C)_t`. -/
lemma Tr.t24_surgery {t : T} {Cm : Cmd LV O M C BE IE} {γ : List (Act T O M C)} (h : Tr t Cm γ)
    {o : O} {f : M} {n : ℤ} :
    ∀ α β, γ = α ++ iface t (.call o f n) :: iface t aborted :: β →
      T24SurgOK (LV := LV) (Tr t Cm) t o f n α β := by
  induction h with
  | prim c => intro α β hE; have := t24_mem_of_eq hE; simp at this
  | seq h₁ h₂ ih₁ ih₂ =>
    intro α β hE
    obtain ⟨y, hy⟩ := t24_surg_append h₁ h₂ h₁.t24_next_of_call ih₁ ih₂ hE
    refine ⟨y, fun v => ?_⟩
    obtain ⟨Y, hY, l₁, l₂, r₁, r₂, he⟩ := hy v
    exact ⟨Y, hY, he ▸ Tr.seq r₁ r₂⟩
  | iteT h ih =>
    intro α β hE
    rcases α with _ | ⟨a, α⟩
    · simp at hE
    · simp only [List.cons_append, List.cons.injEq] at hE
      obtain ⟨rfl, hE⟩ := hE
      obtain ⟨y, hy⟩ := ih α β hE
      refine ⟨y, fun v => ?_⟩
      obtain ⟨Y, hY, htr⟩ := hy v
      exact ⟨Y, hY, by simpa using Tr.iteT htr⟩
  | iteF h ih =>
    intro α β hE
    rcases α with _ | ⟨a, α⟩
    · simp at hE
    · simp only [List.cons_append, List.cons.injEq] at hE
      obtain ⟨rfl, hE⟩ := hE
      obtain ⟨y, hy⟩ := ih α β hE
      refine ⟨y, fun v => ?_⟩
      obtain ⟨Y, hY, htr⟩ := hy v
      exact ⟨Y, hY, by simpa using Tr.iteF htr⟩
  | whileF => intro α β hE; have := t24_mem_of_eq hE; simp at this
  | whileT h₁ h₂ ih₁ ih₂ =>
    intro α β hE
    rcases α with _ | ⟨a, α⟩
    · simp at hE
    · simp only [List.cons_append, List.cons.injEq] at hE
      obtain ⟨rfl, hE⟩ := hE
      obtain ⟨y, hy⟩ := t24_surg_append h₁ h₂ h₁.t24_next_of_call ih₁ ih₂ hE
      refine ⟨y, fun v => ?_⟩
      obtain ⟨Y, hY, l₁, l₂, r₁, r₂, he⟩ := hy v
      exact ⟨Y, hY, by simpa [he] using Tr.whileT r₁ r₂⟩
  | callRet n n' =>
    intro α β hE
    have := t24_mem_of_eq ((List.append_cons _ _ _).symm.trans hE.symm).symm
    simp at this
  | @callAbort x o' f' e n₀ =>
    intro α β hE
    rcases α with _ | ⟨a, _ | ⟨b, _ | ⟨c, α⟩⟩⟩ <;> simp at hE
    obtain ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl⟩ := hE
    refine ⟨x, fun v => ⟨t24Ya t x v o' f', Or.inl rfl, ?_⟩⟩
    have : Tr t (Cmd.call x o' f' e : Cmd LV O M C BE IE) _ := Tr.callRet n₀ v
    simpa [t24Ya] using this
  | @atomicAbort x Cb τ h ih =>
    intro α β hE
    have e' : (iface t txbegin :: iface t ok :: τ) ++
        [iface t aborted, cmd t (assign t x (vAb C))] =
        (α ++ [iface t (.call o f n)]) ++ iface t aborted :: β := by simpa using hE
    rcases split_append_cons e' with ⟨B', e1, rfl⟩ | ⟨A', e1, e2⟩
    · rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
      · simp at e1
      · simp at e1
      · simp only [List.cons_append, List.cons.injEq] at e1
        obtain ⟨rfl, rfl, e1⟩ := e1
        obtain ⟨y, hy⟩ := ih α (B' ++ [iface t aborted]) (by simp [e1])
        refine ⟨y, fun v => ?_⟩
        obtain ⟨Y, hY, htr⟩ := hy v
        have := Tr.atomicAbort (x := x) (τ := α ++ iface t (.call o f n) :: (Y ++ B'))
          (by simpa using htr)
        exact ⟨Y, hY, by simpa using this⟩
    · rcases A' with _ | ⟨a', _ | ⟨b', A'⟩⟩ <;> simp at e2
      subst e2
      rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
      · simp at e1
      · simp at e1
      · simp only [List.cons_append, List.cons.injEq, List.append_nil] at e1
        obtain ⟨rfl, rfl, e1⟩ := e1
        obtain ⟨y, hy⟩ := ih α [] (by simp [← e1])
        refine ⟨y, fun v => ⟨t24Yb t y v o f, Or.inr rfl, ?_⟩⟩
        obtain ⟨Y, hY | hY, htr⟩ := hy v <;> subst hY
        · have := Tr.atomicCommitAbort (x := x) htr (by
            intro τ' h; have := congrArg List.getLast? h; simp [t24Ya] at this)
          simpa [t24Ya, t24Yb] using this
        · have := Tr.atomicAbort (x := x) (τ := α ++ [iface t (.call o f n), iface t (.ret v o f),
            cmd t (assign t y v), iface t txcommit]) (by simpa [t24Yb] using htr)
          simpa [t24Yb] using this
  | @atomicCommit x Cb τ h hn ih =>
    intro α β hE
    have e' : (iface t txbegin :: iface t ok :: τ) ++
        [iface t txcommit, iface t committed, cmd t (assign t x (vCom C))] =
        (α ++ [iface t (.call o f n)]) ++ iface t aborted :: β := by simpa using hE
    rcases split_append_cons e' with ⟨B', e1, rfl⟩ | ⟨A', e1, e2⟩
    · rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
      · simp at e1
      · simp at e1
      · simp only [List.cons_append, List.cons.injEq] at e1
        obtain ⟨rfl, rfl, e1⟩ := e1
        have e1' : τ = (α ++ [iface t (.call o f n), iface t aborted]) ++ B' := by simp [e1]
        have hB' : B' ≠ [] := by
          rintro rfl; exact hn (α ++ [iface t (.call o f n)]) (by simp [e1])
        obtain ⟨y, hy⟩ := ih α B' (by simp [e1])
        refine ⟨y, fun v => ?_⟩
        obtain ⟨Y, hY, htr⟩ := hy v
        have hn' := t24_not_end_of (Y := α ++ iface t (.call o f n) :: Y) (e1' ▸ hn) hB'
        have := Tr.atomicCommit (x := x) htr (by simpa using hn')
        exact ⟨Y, hY, by simpa using this⟩
    · have := t24_mem_of_eq e2; simp at this
  | @atomicCommitAbort x Cb τ h hn ih =>
    intro α β hE
    have e' : (iface t txbegin :: iface t ok :: τ) ++
        [iface t txcommit, iface t aborted, cmd t (assign t x (vAb C))] =
        (α ++ [iface t (.call o f n)]) ++ iface t aborted :: β := by simpa using hE
    rcases split_append_cons e' with ⟨B', e1, rfl⟩ | ⟨A', e1, e2⟩
    · rcases α with _ | ⟨a, _ | ⟨b, α⟩⟩
      · simp at e1
      · simp at e1
      · simp only [List.cons_append, List.cons.injEq] at e1
        obtain ⟨rfl, rfl, e1⟩ := e1
        have e1' : τ = (α ++ [iface t (.call o f n), iface t aborted]) ++ B' := by simp [e1]
        have hB' : B' ≠ [] := by
          rintro rfl; exact hn (α ++ [iface t (.call o f n)]) (by simp [e1])
        obtain ⟨y, hy⟩ := ih α B' (by simp [e1])
        refine ⟨y, fun v => ?_⟩
        obtain ⟨Y, hY, htr⟩ := hy v
        have hn' := t24_not_end_of (Y := α ++ iface t (.call o f n) :: Y) (e1' ▸ hn) hB'
        have := Tr.atomicCommitAbort (x := x) htr (by simpa using hn')
        exact ⟨Y, hY, by simpa using this⟩
    · rcases A' with _ | ⟨a', _ | ⟨b', _ | ⟨c', A'⟩⟩⟩ <;> simp at e2
      · obtain ⟨rfl, -⟩ := e2
        have e1' : α ++ [iface t (.call o f n)] =
            (iface t txbegin :: iface t ok :: τ) ++ [iface t txcommit] := by simpa using e1
        have := (List.append_inj' e1' rfl).2
        simp at this

/-! ### The counterexample -/

section main

open TState

variable [DecidableEq T]

/-- The concrete complete history `H`: a transaction whose only call is aborted. -/
def t24H (t : T) (o : O) (f : M) : List (IAct T O M) :=
  [(t, txbegin), (t, ok), (t, .call o f 1), (t, aborted)]

/-- The abstract histories `S_v`: the call returns `v`, the commit request is aborted. -/
def t24S (t : T) (o : O) (f : M) (v : ℤ) : List (IAct T O M) :=
  [(t, txbegin), (t, ok), (t, .call o f 1), (t, .ret v o f), (t, txcommit), (t, aborted)]

lemma t24_wf_prefix {h h' : List (IAct T O M)} (hw : WellFormed h) (hp : h' <+: h) :
    WellFormed h' := by
  rw [wellFormed_iff_run] at hw ⊢
  intro u
  obtain ⟨r, hr⟩ : proj u h' <+: proj u h := (hp.filter _).map _
  have := hw u
  rw [← hr, run_append] at this
  cases e : run idle (proj u h') <;> simp_all

lemma t24_wf_H (t : T) (o : O) (f : M) : WellFormed (t24H t o f) := by
  rw [wellFormed_iff_run]
  intro u
  by_cases hu : u = t
  · subst hu; simp [proj, t24H, step]
  · simp [proj, t24H, Ne.symm hu]

lemma t24_wf_S (t : T) (o : O) (f : M) (v : ℤ) : WellFormed (t24S t o f v) := by
  rw [wellFormed_iff_run]
  intro u
  by_cases hu : u = t
  · subst hu; simp [proj, t24S, step]
  · simp [proj, t24S, Ne.symm hu]

lemma t24_complete_H (t : T) (o : O) (f : M) : Complete (t24H t o f) := by
  intro H₁ u H₂ h
  rcases H₁ with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, H₁⟩⟩⟩⟩ <;> simp [t24H] at h
  obtain ⟨rfl, rfl⟩ := h
  simp

lemma t24_opac_length {H S : List (IAct T O M)} (h : Opac H S) : H.length = S.length :=
  Fin.equiv_iff_eq.mp ⟨h.choose⟩

lemma t24_prefix_S {t : T} {o : O} {f : M} {h : List (IAct T O M)} (hp : h <+: t24H t o f)
    (hne : h ≠ t24H t o f) : h <+: t24S t o f 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, h = (t24H t o f).take k := ⟨_, List.prefix_iff_eq_take.mp hp⟩
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k <;> simp [t24H, t24S]
  · exact absurd (List.take_of_length_le (by simpa [t24H] using hk)) hne

lemma t24_evalSet_empty (l : List (Act T O M C)) :
    evalSet (∅ : Set (State T LV GV)) l = ∅ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have : evalStep (∅ : Set (State T LV GV)) a = ∅ := by ext; simp [evalStep]
    simp only [evalSet, this, ih]

lemma t24_evalSet_sub (hdet : ∀ (c : C) (s : State T LV GV), (Lang.sem c s).Subsingleton)
    (l : List (Act T O M C)) {S : Set (State T LV GV)} (hS : S.Subsingleton) :
    (evalSet S l).Subsingleton := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih =>
    apply ih
    rintro x ⟨s₁, hs₁, hx⟩ y ⟨s₂, hs₂, hy⟩
    obtain rfl := hS hs₁ hs₂
    cases a with
    | iface u k => simp only [eval1, Set.mem_singleton_iff] at hx hy; rw [hx, hy]
    | cmd u c => exact hdet c s₁ hx hy

lemma t24_evalStep_iface (S : Set (State T LV GV)) (u : T) (k : IKind O M) :
    evalStep S (iface u k : Act T O M C) = S := by
  ext; simp [evalStep, eval1]

lemma t24_evalSet_Y (σ : State T LV GV) (t : T) (y : LV) (o : O) (f : M) (Y : List (Act T O M C))
    (hY : Y = t24Ya t y (σ (.inr (t, y))) o f ∨ Y = t24Yb t y (σ (.inr (t, y))) o f) :
    evalSet {σ} Y = {σ} := by
  have h2 : evalStep {σ} (cmd t (assign t y (σ (.inr (t, y)))) : Act T O M C) = {σ} := by
    ext; simp [evalStep, eval1, sem_assign]
  rcases hY with rfl | rfl <;> simp [t24Ya, t24Yb, evalSet, t24_evalStep_iface, h2]

variable [Fintype T]

/-- `H_C ⊑_state H_A` for the counterexample, when primitive commands are deterministic. -/
lemma t24_stateRef (hdet : ∀ (c : C) (s : State T LV GV), (Lang.sem c s).Subsingleton)
    (t : T) (o : O) (f : M) :
    StateRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M
      {h | h <+: t24H t o f} {h | ∃ v, h <+: t24S t o f v} := by
  rintro P - s τ ⟨⟨hA, hne⟩, hH⟩
  by_cases hfull : history τ = t24H t o f
  swap
  · exact ⟨τ, ⟨⟨hA, hne⟩, 0, t24_prefix_S hH hfull⟩, rfl⟩
  obtain ⟨A, B, rfl, hAh, hBh⟩ := history_eq_append_cons
    (A := [(t, txbegin), (t, ok), (t, .call o f 1)]) (ψ := (t, aborted)) (B := []) hfull
  obtain ⟨τ₀, ⟨r, rfl⟩, htr⟩ := hA
  simp only at htr hne
  have hprojA : history (tproj t A) = [(t, txbegin), (t, ok)] ++ (t, .call o f 1) :: [] := by
    simp only [tproj]; rw [history_filter (fun u => decide (u = t))]; rw [hAh]; simp
  obtain ⟨α, δ, hαδ, -, hδ⟩ := history_eq_append_cons hprojA
  have htt := htr t
  have e0 : tproj t ((A ++ iface t aborted :: B) ++ r) =
      α ++ iface t (.call o f 1) :: (δ ++ iface t aborted :: (tproj t B ++ tproj t r)) := by
    have h' := hαδ
    rw [tproj_append, tproj_append]
    simp [tproj] at h' ⊢
    simp [h']
  rw [e0] at htt
  obtain rfl : δ = [] := by
    rcases δ with _ | ⟨x, δ₁⟩
    · rfl
    · obtain ⟨k, δ', h⟩ := htt.t24_next_of_call α _ rfl
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp at hδ
  obtain ⟨y, hy⟩ := htt.t24_surgery α (tproj t B ++ tproj t r) rfl
  have hτeval : eval s (A ++ iface t aborted :: B) = evalSet (eval s A) B := by
    simp only [eval, evalSet_append, evalSet, t24_evalStep_iface]
  have hAne : (eval s A).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    exact hne (by rw [hτeval, h0, t24_evalSet_empty])
  obtain ⟨σ, hσ⟩ := hAne
  have hAσ : eval s A = {σ} :=
    (t24_evalSet_sub hdet A Set.subsingleton_singleton).eq_singleton_of_mem hσ
  obtain ⟨Y, hY, hYtr⟩ := hy (σ (.inr (t, y)))
  have hYthr : ∀ x ∈ Y, x.thread = t := by rcases hY with rfl | rfl <;> simp [t24Ya, t24Yb]
  have heq : eval s (A ++ iface t aborted :: B) = eval s (A ++ Y ++ B) := by
    rw [hτeval]
    simp only [eval] at hAσ ⊢
    rw [evalSet_append, evalSet_append, hAσ, t24_evalSet_Y σ t y o f Y hY]
  refine ⟨A ++ Y ++ B, ⟨⟨?_, heq ▸ hne⟩, ?_⟩, heq⟩
  · apply inA_of_ext
    intro u
    refine ⟨tproj u r, ?_⟩
    by_cases hu : u = t
    · subst hu
      have hYp : tproj u Y = Y := List.filter_eq_self.mpr (fun x hx => by simp [hYthr x hx])
      rw [tproj_append, tproj_append, hYp, hαδ]
      simpa using hYtr
    · have hYp : tproj u Y = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [hYthr x hx, Ne.symm hu])
      have e1 : tproj u (A ++ iface t aborted :: B) = tproj u A ++ tproj u B := by
        simp [tproj, List.filter_append, Ne.symm hu]
      have := htr u
      rw [tproj_append, e1] at this
      rw [tproj_append, tproj_append, hYp]
      simpa using this
  · refine ⟨σ (.inr (t, y)), ?_⟩
    rcases hY with rfl | rfl <;> simp [hAh, hBh, t24Ya, t24Yb, t24S]

/-- **Theorem 24 of [paper] is false** for languages whose primitive commands are deterministic
(e.g. the minimal language of the paper, `theorem_24_false_minLang`): there are transactional
systems `H_C`, `H_A` with `H_C ⊑_state H_A` (Definition 14) but `H_C|complete ⋢ H_A|complete`.
`H_C` = prefixes of `(t,txbegin) (t,OK) (t,call o.f(1)) (t,aborted)`, `H_A` = prefixes of
`(t,txbegin) (t,OK) (t,call o.f(1)) (t,ret(v) o.f) (t,txcommit) (t,aborted)` for all `v`.
With deterministic commands, the final states cannot distinguish a call aborted by the TM from a
call that returns the current value of its target variable followed by an aborted commit request
(`Tr.t24_surgery`). -/
theorem theorem_24_false (hdet : ∀ (c : C) (s : State T LV GV), (Lang.sem c s).Subsingleton)
    (t : T) (o : O) (f : M) :
    ∃ HC HA : Set (List (IAct T O M)), IsTS HC ∧ IsTS HA ∧
      StateRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA ∧
      ¬ OpacRel (completeSub HC) (completeSub HA) := by
  refine ⟨{h | h <+: t24H t o f}, {h | ∃ v, h <+: t24S t o f v}, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    t24_stateRef hdet t o f, ?_⟩
  · intro h hh; exact t24_wf_prefix (t24_wf_H t o f) hh
  · intro h hh h' hp; exact hp.trans hh
  · rintro h ⟨v, hv⟩; exact t24_wf_prefix (t24_wf_S t o f v) hv
  · rintro h ⟨v, hv⟩ h' hp; exact ⟨v, hp.trans hv⟩
  · intro hop
    obtain ⟨S, ⟨⟨v, hS⟩, hSc⟩, hHS⟩ :=
      hop (t24H t o f) ⟨List.prefix_refl _, t24_complete_H t o f⟩
    have hl := t24_opac_length hHS
    have hS' : S = [(t, txbegin), (t, ok), (t, .call o f 1), (t, .ret v o f)] := by
      rw [List.prefix_iff_eq_take.mp hS, ← hl]; rfl
    subst hS'
    have := hSc [] t _ rfl
    simp at this

end main

/-- `theorem_24_false` for the minimal (deterministic) language of `NonVacuity`. -/
theorem theorem_24_false_minLang {T O M : Type} [DecidableEq T] [Fintype T] (t : T) (o : O)
    (f : M) :
    ∃ HC HA : Set (List (IAct T O M)), IsTS HC ∧ IsTS HA ∧
      StateRef (LV := ℕ) (GV := ℕ) (C := MinCmd T) (BE := MinBE) (IE := MinIE) O M HC HA ∧
      ¬ OpacRel (completeSub HC) (completeSub HA) :=
  theorem_24_false minCmd_det t o f

end Podc.TMObservationalRefinement
