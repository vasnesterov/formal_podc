import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Glue

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/PartialSync.lean

/-!
# The canonical extension is partially synchronous

A finite execution `E` with monotone clock readings bounded by `K`, followed by the canonical
continuation, is partially synchronous when event `t` of the continuation happens at time
`round(t) + 1` and the events of `E` at time `0` (`ps_extend_canon`): `GST = 1`, clocks read
`time + K` after GST, every correct process ticks at every time unit, and messages are delivered
within `Δ = 2`. Hence obstruction-freedom under partial synchrony also gives solo termination
(`soloTerm_of_obstructionFreePS`).
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P] [Fintype P]
variable {Alg : Algorithm P A M L} {f : FailurePattern P} {K : ℕ} {p₀ : P}

/-- Every round starts at some time. -/
lemma exists_round_start (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (r : ℕ) :
    ∃ u, (canonAux Alg f K p₀ C₀ u).round = r ∧
      (canonAux Alg f K p₀ C₀ u).rest = plan f K r (canonAux Alg f K p₀ C₀ u).cfg := by
  induction r with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ r ih =>
    obtain ⟨u, hr, -⟩ := ih
    obtain ⟨h1, h2⟩ := canonAux_next (Alg := Alg) (K := K) hp₀ C₀ u
    exact ⟨_, by rw [h2, hr], by rw [h1, h2, hr]⟩

omit [DecidableEq P] [Fintype P] in
lemma sublist_flatMap_of_mem' {α β : Type*} {l : List α} (f : α → List β) {a : α} (h : a ∈ l) :
    (f a).Sublist (l.flatMap f) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

lemma countP_plan_ge {q p : P} (hqp : f.Edge q p) (r : ℕ) (C : Config P A M L) :
    (C.chan q p).length ≤ (plan f K r C).countP (Event.isDel q p) := by
  have hsub : (List.replicate (C.chan q p).length (Event.deliver q p : Event P A)).Sublist
      (plan f K r C) := by
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    exact sublist_flatMap_of_mem' (fun e : P × P =>
      List.replicate (C.chan e.1 e.2).length (Event.deliver e.1 e.2 : Event P A))
      ((mem_edgeList f).2 hqp)
  have := hsub.countP_le (p := Event.isDel q p)
  rw [List.countP_replicate] at this
  simpa [Event.isDel] using this

variable (Alg f K p₀) in
/-- Times of the canonical extension: `0` on the prefix, `round + 1` afterwards. -/
noncomputable def canonTime (E : List (Event P A)) (t : ℕ) : ℕ :=
  if t < E.length then 0 else (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) (t - E.length)).round + 1

lemma canonTime_add (E : List (Event P A)) (u : ℕ) :
    canonTime Alg f K p₀ E (E.length + u) =
      (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).round + 1 := by
  simp [canonTime]

lemma cfgAt_extend_canon (E : List (Event P A)) (u : ℕ) :
    Alg.cfgAt (extend E (canon Alg f K p₀ (Alg.run Alg.initCfg E))) (E.length + u) =
      (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).cfg := by
  rw [Algorithm.cfgAt_eq_run, pre_extend_add, Algorithm.run_append, canonAux_cfg]

/-- **The canonical extension is partially synchronous.** -/
theorem ps_extend_canon (hp₀ : p₀ ∉ f.procs) (E : List (Event P A)) (hpw : E.Pairwise ClockLe)
    (hK : ClockBound E K) :
    Alg.PartiallySynchronous f (extend E (canon Alg f K p₀ (Alg.run Alg.initCfg E)))
      (canonTime Alg f K p₀ E) := by
  have hmono := canonAux_round_mono (Alg := Alg) (f := f) (K := K) (p₀ := p₀) (Alg.run Alg.initCfg E)
  have hcr : ∀ q, ¬ Algorithm.Crashed f (extend E (canon Alg f K p₀ (Alg.run Alg.initCfg E))) q → q ∉ f.procs :=
    fun q h hq => h (crashed_extend_canon Alg hp₀ E hq)
  -- writing times `≥ |E|` as `|E| + u`
  have hsplit : ∀ t, t < E.length ∨ ∃ u, t = E.length + u := fun t => by
    by_cases h : t < E.length
    · exact Or.inl h
    · exact Or.inr ⟨t - E.length, by omega⟩
  refine ⟨?_, ?_, ?_, 1, 2, ?_, ?_, ?_⟩
  · -- monotone time
    intro t t' htt'
    rcases hsplit t with ht | ⟨u, rfl⟩
    · simp [canonTime, ht]
    · obtain ⟨u', rfl⟩ : ∃ u', t' = E.length + u' := ⟨t' - E.length, by omega⟩
      rw [canonTime_add, canonTime_add]
      have := hmono (show u ≤ u' by omega)
      simp only at this; omega
  · -- unbounded time
    intro T
    obtain ⟨u, hu, -⟩ := exists_round_start (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E) T
    exact ⟨E.length + u, by rw [canonTime_add, hu]; omega⟩
  · -- monotone clocks
    intro p t t' c c' htt' h h'
    rcases hsplit t' with ht' | ⟨u', rfl⟩
    · have ht : t < E.length := by omega
      simp only [extend, ht, ht', dite_true] at h h'
      rcases htt'.lt_or_eq with hlt | rfl
      · exact List.pairwise_iff_getElem.1 hpw t t' ht ht' hlt p c c' h h'
      · rw [h] at h'; cases h'; rfl
    · rw [extend_add] at h'
      have hc' := canon_clock hp₀ (Alg.run Alg.initCfg E) u' h'
      rcases hsplit t with ht | ⟨u, rfl⟩
      · simp only [extend, ht, dite_true] at h
        have := hK _ (List.getElem_mem ht) p c h
        omega
      · rw [extend_add] at h
        have hc := canon_clock hp₀ (Alg.run Alg.initCfg E) u h
        have := hmono (show u ≤ u' by omega)
        simp only at this; omega
  · -- no drift after GST
    intro p _
    refine ⟨K, fun t c ht h => ?_⟩
    rcases hsplit t with htl | ⟨u, rfl⟩
    · simp [canonTime, htl] at ht
    · rw [extend_add] at h
      rw [canonTime_add, canon_clock hp₀ (Alg.run Alg.initCfg E) u h]; omega
  · -- a tick at every time unit
    intro p hp T hT
    obtain ⟨u, hu, hplan⟩ := exists_round_start (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E) (T - 1)
    have hmem : (Event.tick p (K + (T - 1) + 1) : Event P A) ∈ (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).rest := by
      rw [hplan]
      simp only [plan, List.mem_append, List.mem_map]
      exact Or.inl ⟨p, (mem_correctList f).2 (hcr p hp), rfl⟩
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 hmem
    refine ⟨E.length + (u + i), ?_, _, by rw [extend_add, canon_add (Alg.run Alg.initCfg E) u i hi, hget]⟩
    rw [canonTime_add, (canonAux_add (Alg.run Alg.initCfg E) u i hi).2, hu]; omega
  · -- timely delivery
    intro q p hq hp hqp i hi
    have hedge : f.Edge q p := ⟨hcr q hq, hcr p hp, hqp⟩
    rcases hsplit i with hil | ⟨u, rfl⟩
    · simp [canonTime, hil] at hi
    set T' := u + (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).rest.length
    set T'' := T' + (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').rest.length
    obtain ⟨hpl', hr'⟩ := canonAux_next (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E) u
    obtain ⟨-, hr''⟩ := canonAux_next (Alg := Alg) (K := K) hp₀ (Alg.run Alg.initCfg E) T'
    refine ⟨E.length + T'', ?_, ?_⟩
    · rw [canonTime_add, canonTime_add, hr'', hr']
    · rw [cfgAt_extend_canon, cfgAt_extend_canon]
      -- `sent` at `u` ≤ `sent` at `T'` = in transit + delivered at `T'` ≤ delivered at `T''`
      have hc' : (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').cfg =
          Alg.run (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).cfg (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).rest := by
        rw [canonAux_cfg, canonAux_cfg, pre_canon_add, Algorithm.run_append]
      have hc'' : (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T'').cfg =
          Alg.run (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').cfg (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').rest := by
        rw [canonAux_cfg, canonAux_cfg, pre_canon_add, Algorithm.run_append]
      have h1 := (sent_le_run Alg (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).cfg q p
        (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) u).rest).1
      rw [← hc'] at h1
      have hcount : (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').cfg.Counted := by
        rw [canonAux_cfg]
        exact ((counted_initCfg Alg).run Alg E).run Alg _
      have h2 := hcount q p
      have h3 := dlv_run_ge Alg (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').cfg q p (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').rest
      rw [← hc''] at h3
      have h4 : ((canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').cfg.chan q p).length ≤
          (canonAux Alg f K p₀ (Alg.run Alg.initCfg E) T').rest.countP (Event.isDel q p) := by
        rw [hpl']; exact countP_plan_ge hedge _ _
      rw [min_eq_right h4] at h3
      omega

/-- Obstruction-freedom under partial synchrony gives solo termination at correct processes. -/
theorem soloTerm_of_obstructionFreePS {T : Set P} (hOF : Alg.ObstructionFreePS f T) {p : P}
    (hpT : p ∈ T) (hp : p ∉ f.procs) (o : A.Op) : SoloTerm Alg f p o := by
  intro E₀ hE₀ hpw K hK
  obtain ⟨h1, h2, h3, h4⟩ := solo_setup Alg (K := K) hp (o := o) hE₀
  refine h4 (hOF _ _ (fair_extend_canon Alg hp _) (ps_extend_canon hp _ ?_ ?_) p hpT _ o h1 h2 h3)
  · rw [List.pairwise_append]
    refine ⟨hpw, by simp, fun a _ b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    intro q c c' _ h; cases h
  · intro e he q c hc
    rw [List.mem_append] at he
    rcases he with he | he
    · exact hK e he q c hc
    · simp at he; subst he; cases hc

end Cslib.ChannelFailures
