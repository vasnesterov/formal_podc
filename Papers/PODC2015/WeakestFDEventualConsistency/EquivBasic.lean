import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Auxiliary lemmas for the EC ⇔ ETOB transformations (Theorem 1)

Generic facts used by `ECtoETOB.lean` and `ETOBtoEC.lean`:

* one step of the failure-detector model seen from one process;
* bounds over a finite set of processes (faulty processes eventually stop taking steps);
* counters that grow by at most one per step (discrete intermediate value theorem);
* lists: the relation `Before` and its interaction with prefixes and `Nodup`.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

section Model

variable {P R M I O S : Type*} [DecidableEq P] {A : Algorithm P R M I O S} (r : Run P R I)

-- Model candidate
/-- **One step, seen from one process.** Either `p` does not (effectively) move at time `t`, or it
takes a resolved step consuming some event `e`; the outputs of `p` at `t` are those of that
step. -/
lemma st_succ_cases (t : ℕ) (p : P) :
    (A.st r p (t + 1) = A.st r p t ∧ ∀ o, ¬ A.Out r p o t) ∨
    ∃ c e, r.σ t = some (p, c) ∧ (A.cfg r t).event c = some e ∧
      A.st r p (t + 1) = (A.step p (r.H p t) (A.st r p t) e).1 ∧
      ∀ o, A.Out r p o t ↔ o ∈ (A.step p (r.H p t) (A.st r p t) e).2.2 := by
  by_cases hq : ∀ c, r.σ t ≠ some (p, c)
  · exact Or.inl ⟨Algorithm.loc_succ_of_ne r t p hq, fun o ho => hq _ ho.1.choose_spec⟩
  · push Not at hq
    obtain ⟨c, hσ⟩ := hq
    rcases he : (A.cfg r t).event c with _ | e
    · refine Or.inl ⟨by rw [Algorithm.st, (Algorithm.cfg_succ_of_event_none r t p c hσ he).1],
        fun o ho => ?_⟩
      have := ho.2
      rw [(Algorithm.cfg_succ_of_event_none r t p c hσ he).2] at this
      simp at this
    · refine Or.inr ⟨c, e, hσ, he, (Algorithm.cfg_succ_of_event r t p c e hσ he).1, fun o => ?_⟩
      rw [Algorithm.out_iff]
      constructor
      · rintro ⟨c', e', hσ', he', ho⟩
        rw [hσ] at hσ'
        cases hσ'
        rw [he] at he'
        cases he'
        exact ho
      · intro ho
        exact ⟨c, e, hσ, he, ho⟩

-- Model candidate
/-- An event resolved to an input comes from an input choice. -/
lemma event_eq_input {C : Config P M S} {c : Choice P I} {i : I}
    (h : C.event c = some (.input i)) : c = .input i := by
  cases c with
  | recv q s =>
    simp only [Config.event] at h
    rcases hs : C.msg s with _ | ⟨q', m'⟩
    · simp [hs] at h
    · simp only [hs] at h; split_ifs at h; simp at h
  | tick => simp [Config.event] at h
  | input i' => simp only [Config.event, Option.some.injEq, Event.input.injEq] at h; rw [h]

-- Model candidate
/-- A process taking a step after all faulty processes have crashed is correct. -/
lemma correct_of_step_of_le {r : Run P R I} (hA : A.Admissible r) {T t : ℕ}
    (hT : ∀ p, ¬ r.F.Correct p → p ∈ r.F.crashed T) (ht : T ≤ t) {p : P} {c : Choice P I}
    (hσ : r.σ t = some (p, c)) : r.F.Correct p := by
  by_contra hp
  exact hA.alive t p c hσ (r.F.mono ht (hT p hp))

end Model

/-- A function on a finite type is bounded. -/
lemma exists_bound {P : Type*} [Finite P] (g : P → ℕ) : ∃ T, ∀ p, g p ≤ T := by
  obtain ⟨T, hT⟩ := (Set.finite_range g).bddAbove
  exact ⟨T, fun p => hT ⟨p, rfl⟩⟩

/-! ### Counters -/

/-- A counter that is monotone and grows by at most one per step passes through every value in
between: if `f t ≤ n < f t'`, the step from `n` to `n + 1` happens at some `s ∈ [t, t')`. -/
lemma exists_step_of_le_lt {f : ℕ → ℕ} (hmono : Monotone f) (hf : ∀ t, f (t + 1) ≤ f t + 1)
    {t t' n : ℕ} (h1 : f t ≤ n) (h2 : n < f t') :
    ∃ s, t ≤ s ∧ s < t' ∧ f s = n ∧ f (s + 1) = n + 1 := by
  induction t' with
  | zero => exact absurd (hmono (Nat.zero_le t)) (by omega)
  | succ t' ih =>
    by_cases h : n < f t'
    · obtain ⟨s, hs1, hs2, hs3⟩ := ih h
      exact ⟨s, hs1, by omega, hs3⟩
    · have ht : t ≤ t' := by
        by_contra hc
        have := hmono (show t' + 1 ≤ t by omega)
        omega
      have := hf t'
      exact ⟨t', ht, by omega, by omega, by omega⟩

/-! ### The relation `Before` on lists -/

section Before

open List

variable {M : Type*} {a b x : M} {l l₁ l₂ : List M}

lemma before_cons_iff : Before a b (x :: l) ↔ (x = a ∧ b ∈ l) ∨ Before a b l := by
  unfold Before
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inr h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inl ⟨rfl, List.singleton_sublist.mp h⟩
  · rintro (⟨rfl, h⟩ | h)
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.mpr h⟩
    · exact Or.inl h

lemma Before.mem_left (h : Before a b l) : a ∈ l := h.subset (by simp)

lemma Before.mem_right (h : Before a b l) : b ∈ l := h.subset (by simp)

lemma Before.mono (h : Before a b l₁) (h' : l₁ <+ l₂) : Before a b l₂ := List.Sublist.trans h h'

lemma Before.of_prefix (h : Before a b l₁) (h' : l₁ <+: l₂) : Before a b l₂ := h.mono h'.sublist

lemma before_append (ha : a ∈ l₁) (hb : b ∈ l₂) : Before a b (l₁ ++ l₂) :=
  show [a] ++ [b] <+ l₁ ++ l₂ from
    (List.singleton_sublist.mpr ha).append (List.singleton_sublist.mpr hb)

lemma before_or_before (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : Before a b l ∨ Before b a l := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [before_cons_iff]
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (Or.inl ⟨rfl, hb'⟩)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (Or.inl ⟨rfl, ha'⟩)
      · rcases ih ha' hb' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

lemma not_before_of_before (hl : l.Nodup) (h : Before a b l) : ¬ Before b a l := by
  induction l with
  | nil => simp [Before] at h
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [before_cons_iff] at h ⊢
    rintro (⟨rfl, ha⟩ | h')
    · rcases h with ⟨rfl, -⟩ | h
      · exact hl.1 ha
      · exact hl.1 h.mem_right
    · rcases h with ⟨rfl, -⟩ | h
      · exact hl.1 h'.mem_right
      · exact ih hl.2 h h'

/-- `Before` is reflected by prefixes of duplicate-free lists. -/
lemma Before.of_prefix_of_mem (h : Before a b l₂) (h' : l₁ <+: l₂) (hl : l₂.Nodup) (ha : a ∈ l₁)
    (hb : b ∈ l₁) : Before a b l₁ := by
  by_cases hab : a = b
  · subst hab
    exact absurd h (not_before_of_before hl h)
  rcases before_or_before ha hb hab with h1 | h1
  · exact h1
  · exact absurd h (not_before_of_before hl (h1.of_prefix h'))

/-- The first element satisfying a predicate comes before every other such element. -/
lemma before_of_find?_eq_some {p : M → Bool} (h : l.find? p = some a) (hb : b ∈ l) (hpb : p b)
    (hab : b ≠ a) : Before a b l := by
  obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.mp h
  rw [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | rfl | hb
  · exact absurd hpb (by simpa using has b hb)
  · exact absurd rfl hab
  · exact (before_append (List.mem_singleton_self a) hb).mono
      (List.sublist_append_right as _)

/-- Variant of `before_of_find?_eq_some` across a prefix extension. -/
lemma before_of_find?_of_prefix {p : M → Bool} (h : l₁.find? p = some a) (hl : l₁ <+: l₂)
    (hb : b ∈ l₂) (hpb : p b) (hab : b ≠ a) : Before a b l₂ := by
  obtain ⟨u, rfl⟩ := hl
  rcases List.mem_append.mp hb with hb | hb
  · exact (before_of_find?_eq_some h hb hpb hab).mono (List.sublist_append_left _ _)
  · exact before_append (List.mem_of_find?_eq_some h) hb

end Before

end Podc.WeakestFDEventualConsistency
