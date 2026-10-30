import Papers.PODC2019.RDMAAgreement.RB.Validity
import Mathlib.Data.List.GetD

/-!
# Algorithm 2 — non-vacuity

Every correct delivery thread always has an enabled step, so fair executions exist; in
particular, for any `F` with a correct process `p₀`, there is a fair execution in which `p₀`
broadcasts `(1, m₀)` (and hence, by validity, every correct process delivers it).
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- Pending reads have non-empty candidate sets. -/
def CandNE (s : St P M) : Prop :=
  ∀ p q r, (s.pc p q).rd q (s.key p q) = some r → (s.cand p q).Nonempty

lemma CandNE.init [Inhabited P] : CandNE (St.init : St P M) := fun p q r _ => by
  simp [St.init]

lemma CandNE.step {s s' : St P M} {ℓ : Label P M} (I : CandNE s) (h : Step F f s ℓ s') :
    CandNE s' := by
  intro p' q' r hr
  by_cases hT : ∃ p q, ℓ = .thr p q
  · obtain ⟨p, q, rfl⟩ := hT
    have E := h.thrEffect
    by_cases hpq : p' = p ∧ q' = q
    · obtain ⟨rfl, rfl⟩ := hpq; exact ⟨_, E.cand_mem r hr⟩
    · have hl := h.frame_thr.1 p' q' hpq
      simp only [St.loc, Loc.mk.injEq] at hl
      have hk : s'.key p' q' = s.key p' q' := by simp [St.key, hl.2.1]
      rw [hl.1, hk] at hr
      obtain ⟨v, hv⟩ := I p' q' r hr
      exact ⟨v, E.cand_mono p' q' hpq hv⟩
  · push_neg at hT
    have hl := (h.frame_other hT).1 p' q'
    simp only [St.loc, Loc.mk.injEq] at hl
    have hk : s'.key p' q' = s.key p' q' := by simp [St.key, hl.2.1]
    rw [hl.1, hk] at hr
    obtain ⟨v, hv⟩ := I p' q' r hr
    refine ⟨v, ?_⟩
    cases h with
    | bcast => simp only [St.tick, St.doBcast, mem_addCand]; exact Or.inl hv
    | byz => simp only [St.tick, St.write, mem_addCand]; exact Or.inl hv
    | bret => simpa [St.tick, St.write] using hv
    | bretIdle => simpa [St.tick] using hv
    | _ => exact absurd rfl (hT _ _)

lemma CandNE.reach [Inhabited P] {s : St P M} (h : Reachable F f s) : CandNE s := by
  induction h with
  | init => exact CandNE.init
  | step _ hs ih => exact ih.step hs

/-- Every delivery thread of a correct process has an enabled step in every reachable state. -/
theorem thr_enabled [Inhabited P] {s : St P M} (hs : Reachable F f s) {p : P} (hp : p ∉ F)
    (q : P) : ∃ s', Step F f s (.thr p q) s' := by
  classical
  have hne := CandNE.reach hs p q
  cases hpc : s.pc p q with
  | rdL2 i todo =>
    obtain ⟨v, hv⟩ := hne _ (by rw [hpc]; rfl)
    by_cases hval : ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key p q) m ρ
    · obtain ⟨ρ, m, hρ, hm⟩ := hval
      exact ⟨_, Step.l2Found hp hpc hv hρ hm⟩
    · by_cases ht : todo.Nonempty
      · obtain ⟨j, hj⟩ := ht
        exact ⟨_, Step.l2Next hp hpc hv hval hj⟩
      · rw [Finset.not_nonempty_iff_eq_empty] at ht; subst ht
        cases hph : s.phase p q with
        | wfs => exact ⟨_, Step.l2EndS hp hpc hv hval hph⟩
        | wfl1 => exact ⟨_, Step.l2EndV (j := default) hp hpc hv hval hph⟩
        | wfl2 => exact ⟨_, Step.l2EndL (j := default) hp hpc hv hval hph⟩
  | wrCopy ρ m => exact ⟨_, Step.copyDone (j := default) hp hpc⟩
  | rdSnd =>
    obtain ⟨v, hv⟩ := hne _ (by rw [hpc]; rfl)
    by_cases hok : ∃ c, v = .cp c ∧ c.base.sender = q ∧ c.base.key = s.key p q
    · obtain ⟨c, hc, hs', hk⟩ := hok
      exact ⟨_, Step.sndOk hp hpc hv hc hs' hk⟩
    · exact ⟨_, Step.sndBad (j := default) hp hpc hv hok⟩
  | wrEcho b => exact ⟨_, Step.echoDone (j := default) hp hpc⟩
  | rdVal i todo acc =>
    obtain ⟨v, hv⟩ := hne _ (by rw [hpc]; rfl)
    by_cases ht : todo.Nonempty
    · obtain ⟨j, hj⟩ := ht
      exact ⟨_, Step.valNext hp hpc hv hj⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at ht; subst ht
      by_cases hok : f + 1 ≤ (addVal i q (s.key p q) v acc).card ∧
          ∃ b, ∀ c ∈ addVal i q (s.key p q) v acc, c.base = b
      · obtain ⟨hc, b, hb⟩ := hok
        exact ⟨_, Step.valOk hp hpc hv hc hb⟩
      · exact ⟨_, Step.valBad (j := default) hp hpc hv hok⟩
  | wrL1 π => exact ⟨_, Step.l1Done (j := default) hp hpc⟩
  | rdL1 i todo acc =>
    obtain ⟨v, hv⟩ := hne _ (by rw [hpc]; rfl)
    by_cases ht : todo.Nonempty
    · obtain ⟨j, hj⟩ := ht
      exact ⟨_, Step.l1Next hp hpc hv hj⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at ht; subst ht
      by_cases hok : ∃ S m, S ⊆ addL1 v acc ∧ L2Valid f q (s.key p q) m ⟨p, S⟩
      · obtain ⟨S, m, hS, hm⟩ := hok
        exact ⟨_, Step.l1Ok hp hpc hv hS hm⟩
      · exact ⟨_, Step.l1Bad (j := default) hp hpc hv hok⟩
  | wrL2 ρ => exact ⟨_, Step.l2Done (j := default) hp hpc⟩

lemma bret_enabled {s : St P M} {p : P} (hp : p ∉ F) : ∃ s', Step F f s (.bret p) s' := by
  cases hb : s.bpend p with
  | none => exact ⟨_, Step.bretIdle hp hb⟩
  | some b => exact ⟨_, Step.bret hp hb⟩

/-- The round-robin list of the correct processes' labels. -/
noncomputable def rrList (F : Finset P) : List (Label P M) :=
  (Finset.univ.filter (· ∉ F)).toList.flatMap fun p =>
    (Finset.univ : Finset P).toList.map (fun q => Label.thr p q) ++ [Label.bret p]

/-- Schedule: broadcast `(1, m₀)` by `p₀` first, then round robin. -/
noncomputable def sched (F : Finset P) (p₀ : P) (m₀ : M) (t : ℕ) : Label P M :=
  match t with
  | 0 => .bcast p₀ m₀
  | t + 1 => (rrList (M := M) F).getD (t % (rrList (M := M) F).length) (.bret p₀)

open Classical in
/-- The states of the constructed execution. -/
noncomputable def schedState [Inhabited P] (F : Finset P) (f : ℕ) (p₀ : P) (m₀ : M) :
    ℕ → St P M
  | 0 => St.init
  | t + 1 =>
    let s := schedState F f p₀ m₀ t
    if h : ∃ s', Step F f s (sched F p₀ m₀ t) s' then h.choose else s

open Classical in
lemma schedState_succ [Inhabited P] (p₀ : P) (m₀ : M) (t : ℕ) :
    schedState F f p₀ m₀ (t + 1) =
      if h : ∃ s', Step F f (schedState F f p₀ m₀ t) (sched F p₀ m₀ t) s' then h.choose
      else schedState F f p₀ m₀ t := by
  rfl

lemma rrList_mem {p : P} (hp : p ∉ F) (ℓ : Label P M) (hℓ : ℓ = .bret p ∨ ∃ q, ℓ = .thr p q) :
    ℓ ∈ rrList (M := M) F := by
  simp only [rrList, List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and, List.mem_append, List.mem_map, List.mem_singleton]
  refine ⟨p, hp, ?_⟩
  rcases hℓ with rfl | ⟨q, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨q, rfl⟩

lemma rrList_correct {ℓ : Label P M} (h : ℓ ∈ rrList (M := M) F) :
    (∃ p ∉ F, ℓ = .bret p) ∨ ∃ p ∉ F, ∃ q, ℓ = .thr p q := by
  simp only [rrList, List.mem_flatMap, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and, List.mem_append, List.mem_map, List.mem_singleton] at h
  obtain ⟨p, hp, ⟨q, -, rfl⟩ | rfl⟩ := h
  · exact Or.inr ⟨p, hp, q, rfl⟩
  · exact Or.inl ⟨p, hp, rfl⟩

/-- **Non-vacuity.** For every Byzantine set `F` with a correct process `p₀` and every message
`m₀` there is a fair execution in which `p₀` broadcasts `(1, m₀)`. -/
theorem exists_fair_exec [Inhabited P] (p₀ : P) (hp₀ : p₀ ∉ F) (m₀ : M) :
    ∃ e : Exec (M := M) F f, e.Fair ∧ (e.s 1).bc p₀ 1 = some m₀ := by
  classical
  have hlen : 0 < (rrList (M := M) F).length :=
    List.length_pos_of_mem (rrList_mem hp₀ _ (Or.inl rfl))
  -- every scheduled label is enabled
  have hstep : ∀ t, Reachable F f (schedState F f p₀ m₀ t) ∧
      Step F f (schedState F f p₀ m₀ t) (sched F p₀ m₀ t) (schedState F f p₀ m₀ (t + 1)) := by
    intro t
    induction t with
    | zero =>
      have hen : ∃ s', Step F f (schedState F f p₀ m₀ 0) (sched F p₀ m₀ 0) s' :=
        ⟨_, Step.bcast (m := m₀) hp₀ (by simp [schedState, St.init])⟩
      refine ⟨by simp only [schedState]; exact .init, ?_⟩
      rw [schedState_succ, dif_pos hen]; exact hen.choose_spec
    | succ t ih =>
      have hr : Reachable F f (schedState F f p₀ m₀ (t + 1)) := .step ih.1 ih.2
      have hen : ∃ s', Step F f (schedState F f p₀ m₀ (t + 1)) (sched F p₀ m₀ (t + 1)) s' := by
        have hmem : sched F p₀ m₀ (t + 1) ∈ rrList (M := M) F := by
          simp only [sched]
          rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
          exact List.getElem_mem _
        rcases rrList_correct hmem with ⟨p, hp, he⟩ | ⟨p, hp, q, he⟩
        · rw [he]; exact bret_enabled hp
        · rw [he]; exact thr_enabled hr hp q
      refine ⟨hr, ?_⟩
      rw [schedState_succ (t := t + 1), dif_pos hen]; exact hen.choose_spec
  have hfairL : ∀ ℓ ∈ rrList (M := M) F, ∀ t, ∃ t' ≥ t, sched F p₀ m₀ t' = ℓ := by
    intro ℓ hℓ t
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hℓ
    refine ⟨i + (rrList (M := M) F).length * t + 1, ?_, ?_⟩
    · have := Nat.le_mul_of_pos_left t hlen; omega
    · simp only [sched]
      rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hlen)]
      congr 1
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  refine ⟨⟨schedState F f p₀ m₀, sched F p₀ m₀, rfl, fun t => (hstep t).2⟩,
    ⟨fun p hp q t => hfairL _ (rrList_mem hp _ (Or.inr ⟨q, rfl⟩)) t,
    fun p hp t => hfairL _ (rrList_mem hp _ (Or.inl rfl)) t⟩, ?_⟩
  have h0 := (hstep 0).2
  simp only [sched] at h0
  show (schedState F f p₀ m₀ (0 + 1)).bc p₀ 1 = some m₀
  generalize schedState F f p₀ m₀ (0 + 1) = s1 at h0 ⊢
  cases h0 with
  | bcast _ _ => simp [schedState, St.tick, St.doBcast, St.init]

end Podc.RDMAAgreement.RB
