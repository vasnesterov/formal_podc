import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Model

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Canonical.lean

/-!
# The canonical round-robin continuation

Given a failure pattern `f`, the *canonical continuation* from a configuration `C₀` runs in rounds:
in round `r` every process outside `f.procs` takes a spontaneous step (clock reading `K + r + 1`),
then every channel `q → p` that is an edge of `G \ f` delivers all the messages that were in
transit at the beginning of the round. Processes of `f.procs` never act (they crash) and the
channels of `f.chans` never deliver (they disconnect).

This file sets up the round structure (`canonAux`, `canon`) and its basic properties:
the events are spontaneous steps of correct processes and deliveries along edges of `G \ f`
(`canon_spec`), every correct process ticks in every round, and every message in transit at the
beginning of a round is delivered by the end of the round.
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]

/-! ### Elementary facts about steps -/

section Basic

variable (Alg : Algorithm P A M L)

/-- `e` delivers on the channel `q → p`. -/
def Event.isDel (q p : P) : Event P A → Bool
  | .deliver a b => decide (a = q ∧ b = p)
  | _ => false

lemma Event.isDel_iff {q p : P} {e : Event P A} : e.isDel q p = true ↔ e = .deliver q p := by
  cases e <;> simp [Event.isDel]

/-- A step that does not deliver on `q → p` only appends to that channel. -/
lemma chan_prefix_step (C : Config P A M L) {q p : P} (e : Event P A)
    (he : e ≠ .deliver q p) : C.chan q p <+: (Alg.step C e).1.chan q p := by
  have key : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
      C'.chan q p <+: (C'.apply a r).1.chan q p := by
    intro C' a r
    simp only [Config.apply]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  cases e with
  | invoke a o =>
    simp only [Algorithm.step]
    split
    · exact List.prefix_refl _
    · exact key _ _ _
  | tick a c => exact key _ _ _
  | deliver a b =>
    simp only [Algorithm.step]
    split
    · exact List.prefix_refl _
    · rename_i m rest _
      have hab : ¬ (q = a ∧ p = b) := by
        rintro ⟨rfl, rfl⟩; exact he rfl
      have := key (C.pop a b rest) b (Alg.handle b (.recv a m) (C.loc b))
      simpa [Config.pop, hab] using this

/-- The ghost counters are monotone. -/
lemma sent_le_step (C : Config P A M L) (q p : P) (e : Event P A) :
    C.sent q p ≤ (Alg.step C e).1.sent q p ∧ C.dlv q p ≤ (Alg.step C e).1.dlv q p := by
  have key : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
      C'.sent q p ≤ (C'.apply a r).1.sent q p ∧ C'.dlv q p ≤ (C'.apply a r).1.dlv q p := by
    intro C' a r
    simp only [Config.apply]
    split_ifs <;> simp
  cases e with
  | invoke a o =>
    simp only [Algorithm.step]
    split
    · simp
    · exact key _ _ _
  | tick a c => exact key _ _ _
  | deliver a b =>
    simp only [Algorithm.step]
    split
    · simp
    · rename_i m rest _
      have h := key (C.pop a b rest) b (Alg.handle b (.recv a m) (C.loc b))
      refine ⟨le_trans ?_ h.1, le_trans ?_ h.2⟩
      · simp [Config.pop]
      · simp only [Config.pop]; split_ifs <;> omega

lemma sent_le_run (C : Config P A M L) (q p : P) (E : List (Event P A)) :
    C.sent q p ≤ (Alg.run C E).sent q p ∧ C.dlv q p ≤ (Alg.run C E).dlv q p := by
  induction E generalizing C with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons e E ih =>
    exact ⟨(sent_le_step Alg C q p e).1.trans (ih _).1, (sent_le_step Alg C q p e).2.trans (ih _).2⟩

/-- Channel bookkeeping: messages in transit = sent - delivered. -/
def Config.Counted (C : Config P A M L) : Prop :=
  ∀ q p, (C.chan q p).length + C.dlv q p = C.sent q p

omit [DecidableEq P] in
lemma counted_initCfg : (Alg.initCfg).Counted := fun _ _ => rfl

lemma Config.Counted.step {C : Config P A M L} (hC : C.Counted) (e : Event P A) :
    (Alg.step C e).1.Counted := by
  have key : ∀ (C' : Config P A M L) (a : P) (r : L × List (P × M) × Option A.Resp),
      C'.Counted → (C'.apply a r).1.Counted := by
    intro C' a r h q p
    simp only [Config.apply]
    split_ifs
    · simp only [List.length_append]; have := h q p; omega
    · exact h q p
  cases e with
  | invoke a o =>
    simp only [Algorithm.step]
    split
    · exact hC
    · exact key _ _ _ hC
  | tick a c => exact key _ _ _ hC
  | deliver a b =>
    simp only [Algorithm.step]
    split
    · exact hC
    · rename_i m rest hm
      refine key _ _ _ ?_
      intro q p
      simp only [Config.pop]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        have := hC q p; rw [hm] at this; simp at this; omega
      · exact hC q p

lemma Config.Counted.run {C : Config P A M L} (hC : C.Counted) (E : List (Event P A)) :
    (Alg.run C E).Counted := by
  induction E generalizing C with
  | nil => exact hC
  | cons e E ih => exact ih (hC.step Alg e)

/-- Running a list with at least `k` deliveries on `q → p` delivers at least
`min k (initial length)` messages on that channel. -/
lemma dlv_run_ge (C : Config P A M L) (q p : P) (E : List (Event P A)) :
    C.dlv q p + min (E.countP (Event.isDel q p)) (C.chan q p).length ≤
      (Alg.run C E).dlv q p := by
  induction E generalizing C with
  | nil => simp
  | cons e E ih =>
    by_cases he : e = .deliver q p
    · subst he
      have hc : (Event.deliver q p : Event P A).isDel q p = true := by simp [Event.isDel]
      rw [List.countP_cons_of_pos hc]
      cases hch : C.chan q p with
      | nil => simpa [hch] using (sent_le_run Alg C q p (Event.deliver q p :: E)).2
      | cons m rest =>
        have hstep : (Alg.step C (.deliver q p)).1 =
            ((C.pop q p rest).apply p (Alg.handle p (.recv q m) (C.loc p))).1 := by
          simp [Algorithm.step, hch]
        have h1 := ih (Alg.step C (.deliver q p)).1
        have hd : (Alg.step C (.deliver q p)).1.dlv q p = C.dlv q p + 1 := by
          rw [hstep]; simp [Config.apply, Config.pop]
        have hl : rest.length ≤ ((Alg.step C (.deliver q p)).1.chan q p).length := by
          rw [hstep]; simp only [Config.apply, Config.pop, and_self, ite_true]
          split_ifs <;> simp
        rw [hd] at h1
        rw [Algorithm.run_cons, List.length_cons]
        have : min (E.countP (Event.isDel q p)) rest.length ≤
            min (E.countP (Event.isDel q p)) ((Alg.step C (.deliver q p)).1.chan q p).length :=
          min_le_min_left _ hl
        omega
    · have hc : e.isDel q p = false := by
        cases h : e.isDel q p
        · rfl
        · exact absurd (Event.isDel_iff.1 h) he
      rw [List.countP_cons_of_neg (by simp [hc])]
      have h1 := ih (Alg.step C e).1
      have hp := chan_prefix_step Alg C e he
      have hd := (sent_le_step Alg C q p e).2
      have : min (E.countP (Event.isDel q p)) (C.chan q p).length ≤
          min (E.countP (Event.isDel q p)) ((Alg.step C e).1.chan q p).length :=
        min_le_min_left _ hp.length_le
      rw [Algorithm.run_cons]
      omega

/-- Running a list without deliveries on `q → p` keeps a non-empty channel non-empty. -/
lemma chan_prefix_run (C : Config P A M L) {q p : P} (E : List (Event P A))
    (hE : ∀ e ∈ E, e ≠ .deliver q p) : C.chan q p <+: (Alg.run C E).chan q p := by
  induction E generalizing C with
  | nil => exact List.prefix_refl _
  | cons e E ih =>
    exact (chan_prefix_step Alg C e (hE e List.mem_cons_self)).trans
      (ih _ fun e' he' => hE e' (List.mem_cons_of_mem _ he'))

end Basic

/-! ### The canonical continuation -/

variable [Fintype P] (Alg : Algorithm P A M L) (f : FailurePattern P) (K : ℕ) (p₀ : P)

open Classical in
/-- The processes outside `f.procs`. -/
noncomputable def correctList : List P := (Finset.univ.filter fun p => p ∉ f.procs).toList

open Classical in
/-- The edges of `G \ f`. -/
noncomputable def edgeList : List (P × P) := (Finset.univ.filter fun e : P × P => f.Edge e.1 e.2).toList

omit [DecidableEq P] in
lemma mem_correctList {p : P} : p ∈ correctList f ↔ p ∉ f.procs := by
  simp [correctList]

omit [DecidableEq P] in
lemma mem_edgeList {q p : P} : (q, p) ∈ edgeList f ↔ f.Edge q p := by
  simp [edgeList]

/-- The events of round `r` started in configuration `C`. -/
noncomputable def plan (r : ℕ) (C : Config P A M L) : List (Event P A) :=
  (correctList f).map (fun p => .tick p (K + r + 1)) ++
    (edgeList f).flatMap fun e => List.replicate (C.chan e.1 e.2).length (.deliver e.1 e.2)

/-- State of the canonical scheduler: configuration, remaining events of the round, round. -/
structure CState (P : Type) (A : ObjSpec) (M L : Type) where
  /-- Current configuration. -/
  cfg : Config P A M L
  /-- Remaining events of the current round. -/
  rest : List (Event P A)
  /-- Current round. -/
  round : ℕ

/-- The canonical scheduler from `C₀` (`p₀` only provides a dummy event). -/
noncomputable def canonAux (C₀ : Config P A M L) : ℕ → CState P A M L
  | 0 => ⟨C₀, plan f K 0 C₀, 0⟩
  | t + 1 =>
    let s := canonAux C₀ t
    let C' := (Alg.step s.cfg (s.rest.headD (.tick p₀ 0))).1
    if s.rest.tail = [] then ⟨C', plan f K (s.round + 1) C', s.round + 1⟩
    else ⟨C', s.rest.tail, s.round⟩

/-- The canonical continuation from `C₀`. -/
noncomputable def canon (C₀ : Config P A M L) (t : ℕ) : Event P A :=
  (canonAux Alg f K p₀ C₀ t).rest.headD (.tick p₀ 0)

variable {Alg f K p₀}

lemma canonAux_cfg (C₀ : Config P A M L) (t : ℕ) :
    (canonAux Alg f K p₀ C₀ t).cfg = Alg.run C₀ (Algorithm.pre (canon Alg f K p₀ C₀) t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Algorithm.pre_succ, Algorithm.run_append, ← ih]
    simp only [canonAux, canon]
    split_ifs <;> rfl

omit [DecidableEq P] in
lemma plan_ne_nil (hp₀ : p₀ ∉ f.procs) (r : ℕ) (C : Config P A M L) : plan f K r C ≠ [] := by
  have : p₀ ∈ correctList f := (mem_correctList f).2 hp₀
  intro h
  simp only [plan, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  rw [h.1] at this; simp at this

lemma canonAux_rest_ne_nil (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (t : ℕ) :
    (canonAux Alg f K p₀ C₀ t).rest ≠ [] := by
  induction t with
  | zero => exact (plan_ne_nil hp₀ _ _ : plan f K 0 C₀ ≠ [])
  | succ t ih =>
    simp only [canonAux]
    split_ifs with h
    · exact plan_ne_nil hp₀ _ _
    · exact h

/-- An event of the canonical continuation: a tick of a correct process or a delivery along an
edge of `G \ f`. -/
def CanonEvent (f : FailurePattern P) : Event P A → Prop
  | .invoke _ _ => False
  | .tick p _ => p ∉ f.procs
  | .deliver q p => f.Edge q p

omit [DecidableEq P] in
lemma canonEvent_of_mem_plan {r : ℕ} {C : Config P A M L} {e : Event P A}
    (he : e ∈ plan f K r C) : CanonEvent f e := by
  simp only [plan, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_replicate] at he
  rcases he with ⟨p, hp, rfl⟩ | ⟨⟨q, p⟩, hqp, -, rfl⟩
  · exact (mem_correctList f).1 hp
  · exact (mem_edgeList f).1 hqp

lemma canonAux_rest_canon (C₀ : Config P A M L) (t : ℕ) :
    ∀ e ∈ (canonAux Alg f K p₀ C₀ t).rest, CanonEvent f e := by
  induction t with
  | zero => exact fun e he => canonEvent_of_mem_plan (r := 0) (C := C₀) he
  | succ t ih =>
    simp only [canonAux]
    split_ifs
    · exact fun e he => canonEvent_of_mem_plan he
    · exact fun e he => ih e (List.mem_of_mem_tail he)

lemma canon_spec (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (t : ℕ) :
    CanonEvent f (canon Alg f K p₀ C₀ t) := by
  have hne := canonAux_rest_ne_nil (Alg := Alg) (K := K) hp₀ C₀ t
  obtain ⟨e, l, hel⟩ := List.exists_cons_of_ne_nil hne
  have := canonAux_rest_canon (Alg := Alg) (K := K) (p₀ := p₀) C₀ t e (by rw [hel]; simp)
  simpa [canon, hel] using this

/-- Inside a round: after `i` more steps the remaining events are `rest.drop i`. -/
lemma canonAux_add (C₀ : Config P A M L) (t : ℕ) :
    ∀ i < (canonAux Alg f K p₀ C₀ t).rest.length,
      (canonAux Alg f K p₀ C₀ (t + i)).rest = (canonAux Alg f K p₀ C₀ t).rest.drop i ∧
      (canonAux Alg f K p₀ C₀ (t + i)).round = (canonAux Alg f K p₀ C₀ t).round := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [← add_assoc]
    simp only [canonAux]
    have htail : (canonAux Alg f K p₀ C₀ (t + i)).rest.tail ≠ [] := by
      rw [h1, List.tail_drop]
      intro h
      have := congrArg List.length h
      simp at this; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false htail)]
    exact ⟨by rw [h1, List.tail_drop], h2⟩

/-- At the end of a round, the next round starts with its full plan. -/
lemma canonAux_next (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (t : ℕ) :
    let s := canonAux Alg f K p₀ C₀ (t + (canonAux Alg f K p₀ C₀ t).rest.length)
    s.rest = plan f K s.round s.cfg ∧ s.round = (canonAux Alg f K p₀ C₀ t).round + 1 := by
  have hne := canonAux_rest_ne_nil (Alg := Alg) (K := K) hp₀ C₀ t
  set n := (canonAux Alg f K p₀ C₀ t).rest.length with hn
  have hpos : 0 < n := List.length_pos_of_ne_nil hne
  obtain ⟨h1, h2⟩ := canonAux_add (Alg := Alg) (f := f) (K := K) (p₀ := p₀) C₀ t (n - 1)
    (by omega)
  have heq : t + n = t + (n - 1) + 1 := by omega
  simp only
  rw [heq]
  simp only [canonAux]
  have htail : (canonAux Alg f K p₀ C₀ (t + (n - 1))).rest.tail = [] := by
    rw [h1, List.tail_drop]
    apply List.eq_nil_of_length_eq_zero
    simp; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true htail)]
  exact ⟨rfl, by rw [h2]⟩

/-- Within a round, the events are those of the round's list, in order. -/
lemma canon_add (C₀ : Config P A M L) (t i : ℕ)
    (hi : i < (canonAux Alg f K p₀ C₀ t).rest.length) :
    canon Alg f K p₀ C₀ (t + i) = (canonAux Alg f K p₀ C₀ t).rest[i] := by
  simp only [canon, (canonAux_add C₀ t i hi).1]
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hi]
  rfl

omit [DecidableEq P] [Fintype P] in
lemma pre_add (ev : ℕ → Event P A) (t n : ℕ) :
    Algorithm.pre ev (t + n) = Algorithm.pre ev t ++ (List.range n).map (fun i => ev (t + i)) := by
  simp [Algorithm.pre, List.range_add, List.map_map, Function.comp_def]

lemma pre_canon_add (C₀ : Config P A M L) (t : ℕ) :
    Algorithm.pre (canon Alg f K p₀ C₀) (t + (canonAux Alg f K p₀ C₀ t).rest.length) =
      Algorithm.pre (canon Alg f K p₀ C₀) t ++ (canonAux Alg f K p₀ C₀ t).rest := by
  rw [pre_add]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact canon_add C₀ t i h2

/-- Every correct process ticks in every round: from any time on it ticks again. -/
lemma canon_tick (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) {p : P} (hp : p ∉ f.procs) (T : ℕ) :
    ∃ t ≥ T, t < T + (canonAux Alg f K p₀ C₀ T).rest.length +
        (canonAux Alg f K p₀ C₀ (T + (canonAux Alg f K p₀ C₀ T).rest.length)).rest.length ∧
      canon Alg f K p₀ C₀ t = .tick p (K + ((canonAux Alg f K p₀ C₀ T).round + 1) + 1) := by
  set T' := T + (canonAux Alg f K p₀ C₀ T).rest.length
  obtain ⟨hplan, hround⟩ := canonAux_next (Alg := Alg) (K := K) hp₀ C₀ T
  have hmem : (Event.tick p (K + ((canonAux Alg f K p₀ C₀ T).round + 1) + 1) : Event P A) ∈
      (canonAux Alg f K p₀ C₀ T').rest := by
    rw [hplan, hround]
    simp only [plan, List.mem_append, List.mem_map]
    exact Or.inl ⟨p, (mem_correctList f).2 hp, rfl⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hmem
  refine ⟨T' + i, by omega, by omega, ?_⟩
  rw [canon_add C₀ T' i hi, hget]

/-- A channel along an edge of `G \ f` that is non-empty at time `T` is served later. -/
lemma canon_deliver (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) {q p : P} (hqp : f.Edge q p)
    (T : ℕ) (hT : (Alg.run C₀ (Algorithm.pre (canon Alg f K p₀ C₀) T)).chan q p ≠ []) :
    ∃ t ≥ T, canon Alg f K p₀ C₀ t = .deliver q p := by
  by_contra hcon
  push Not at hcon
  set T' := T + (canonAux Alg f K p₀ C₀ T).rest.length
  have hpre := pre_canon_add (Alg := Alg) (f := f) (K := K) (p₀ := p₀) C₀ T
  have hnot : ∀ e ∈ (canonAux Alg f K p₀ C₀ T).rest, e ≠ .deliver q p := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
    rw [← canon_add C₀ T i hi]
    exact hcon _ (by omega)
  have hpref := chan_prefix_run Alg (Alg.run C₀ (Algorithm.pre (canon Alg f K p₀ C₀) T)) _ hnot
  rw [← Algorithm.run_append, ← hpre] at hpref
  have hne : (Alg.run C₀ (Algorithm.pre (canon Alg f K p₀ C₀) T')).chan q p ≠ [] := by
    intro h; rw [h] at hpref; exact hT (List.prefix_nil.1 hpref)
  obtain ⟨hplan, -⟩ := canonAux_next (Alg := Alg) (K := K) hp₀ C₀ T
  have hmem : (Event.deliver q p : Event P A) ∈ (canonAux Alg f K p₀ C₀ T').rest := by
    rw [hplan]
    simp only [plan, List.mem_append, List.mem_flatMap, List.mem_replicate]
    refine Or.inr ⟨(q, p), (mem_edgeList f).2 hqp, ?_, rfl⟩
    rw [canonAux_cfg]
    exact List.length_pos_of_ne_nil hne |>.ne'
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hmem
  exact hcon (T' + i) (by omega) (by rw [canon_add C₀ T' i hi, hget])

end Cslib.ChannelFailures
