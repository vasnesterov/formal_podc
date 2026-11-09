import Papers.PODC2026.RandomizedWaitFreeLocks.Alg2Inv

/-!
# Algorithm 2: safety (S1), (S2)

Section 4.2.1 of Aeini, Bencivenga, Giakkoupis, Woelfel, *Simple and Efficient Randomized
Wait-Free Locks* (PODC 2026): Observation 4.10, Lemmas 4.11–4.15, for the model of
`Alg2Model.lean`. The executions are all runs `run init step xs` of the transition system
(every adversary, every outcome of the random choices).
-/

namespace Podc.RandomizedWaitFreeLocks.Alg2

variable {P D : Type*} [DecidableEq P] [DecidableEq D]

open Function

/-! ## How the steps change the ghost state -/

section StepFacts

variable (c : Cfg P D) (a : Act P D) (b : Bool)

lemma step_clock : (step c a b).1.clock = c.clock + 1 := by
  cases a with
  | invoke p x => simp only [step]; split_ifs <;> simp [tick]
  | abort p => simp only [step]; split_ifs <;> simp [tick]
  | sched p j =>
    simp only [step]
    generalize c.pc p = pc
    rcases pc with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] <;> (try split) <;> simp

lemma step_started (x : D) :
    (step c a b).1.started x = true ↔ c.started x = true ∨ (step c a b).2 = .exS x := by
  cases a with
  | invoke p x => simp only [step]; split_ifs <;> simp [tick]
  | abort p => simp only [step]; split_ifs <;> simp [tick]
  | sched p j =>
    simp only [step]
    generalize c.pc p = pc
    rcases pc with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] <;> (try split) <;> simp [update_apply]
    aesop

lemma step_done (x : D) :
    (step c a b).1.done x = true ↔ c.done x = true ∨ (step c a b).2 = .exE x := by
  cases a with
  | invoke p x => simp only [step]; split_ifs <;> simp [tick]
  | abort p => simp only [step]; split_ifs <;> simp [tick]
  | sched p j =>
    simp only [step]
    generalize c.pc p = pc
    rcases pc with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] <;> (try split) <;> simp [update_apply]
    aesop

lemma step_inv {p : P} {x : D} (h : (step c a b).2 = .inv p x) :
    c.pc p = .idle ∧ c.used x = false ∧ (step c a b).1.call p = some x ∧
      (step c a b).1.callIdx p = c.clock := by
  cases a with
  | invoke q y =>
    simp only [step] at h ⊢
    split_ifs at h ⊢ with hv
    · cases h; simp [hv]
  | abort q => simp only [step] at h; split_ifs at h
  | sched q j =>
    simp only [step] at h
    generalize c.pc q = pc at h
    rcases pc with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] at h <;> (try split at h) <;> simp at h

lemma step_resp {p : P} {x : D} {r : Bool} (h : (step c a b).2 = .resp p x r) :
    c.pc p = .l34 ∧ c.call p = some x ∧ r = c.done x ∧ (step c a b).1.call p = none := by
  cases a with
  | invoke q y => simp only [step] at h; split_ifs at h
  | abort q => simp only [step] at h; split_ifs at h
  | sched q j =>
    simp only [step] at h ⊢
    revert h
    rcases hpc : c.pc q with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      intro h <;> simp only [stepAt, tick] at h ⊢ <;> (try split at h) <;> (try simp at h)
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp_all

lemma step_call_other {p : P} (h1 : ∀ x, (step c a b).2 ≠ .inv p x)
    (h2 : ∀ x r, (step c a b).2 ≠ .resp p x r) :
    (step c a b).1.call p = c.call p ∧ (step c a b).1.callIdx p = c.callIdx p := by
  cases a with
  | invoke q y =>
    simp only [step] at h1 ⊢
    split_ifs at h1 ⊢ with hv
    · have hqp : p ≠ q := by rintro rfl; exact h1 y rfl
      simp [update_of_ne hqp]
    · simp [tick]
  | abort q => simp only [step]; split_ifs <;> simp [tick]
  | sched q j =>
    simp only [step] at h2 ⊢
    revert h2
    rcases hpc : c.pc q with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      intro h2 <;> simp only [stepAt, tick] at h2 ⊢ <;> (try split) <;> simp
    rename_i y hy
    have hqp : p ≠ q := by rintro rfl; exact h2 y (c.done y) (by simp [hy])
    simp [update_of_ne hqp]

lemma casStat_of_ne (st : D → Stat) (o : Option D) (old new : Stat) (x : D) (h : st x ≠ old) :
    casStat st o old new x = st x := by
  cases o with
  | none => rfl
  | some y =>
    simp only [casStat]
    split_ifs with hy
    · rw [update_of_ne (by rintro rfl; exact h hy)]
    · rfl

/-- Observation 4.10: a `stat` field that is not `wait` never changes. -/
theorem obs_4_10 (x : D) (h : c.stat x ≠ .wait) : (step c a b).1.stat x = c.stat x := by
  cases a with
  | invoke p x => simp only [step]; split_ifs <;> simp [tick]
  | abort p => simp only [step]; split_ifs <;> simp [tick]
  | sched p j =>
    simp only [step]
    generalize c.pc p = pc
    rcases pc with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] <;> (try split) <;> simp [casStat_of_ne _ _ _ _ _ h]

/-- `L` changes only by a successful CAS of line 21. -/
lemma step_L : (step c a b).1.L = c.L ∨
    ∃ p r, c.pc p = .hap r .l21 ∧ c.L = c.w p := by
  cases a with
  | invoke p x => simp only [step]; split_ifs <;> simp [tick]
  | abort p => simp only [step]; split_ifs <;> simp [tick]
  | sched p j =>
    simp only [step]
    rcases hpc : c.pc p with _ | ⟨r, (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [stepAt, tick] <;> (try split) <;> simp
    exact Or.inr ⟨p, ⟨r, hpc⟩, by assumption⟩

end StepFacts

/-! ## State-level lemmas of Section 4.2.1 -/

section Lemmas

variable {c : Cfg P D}

/-- `Post` (the conclusion of Lemma 4.11) is stable. -/
lemma post_step {x : D} (h : Post c x) (a : Act P D) (b : Bool) : Post (step c a b).1 x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [obs_4_10 c a b x h1]; exact h1, fun h' => ?_⟩
  rw [obs_4_10 c a b x h1] at h'
  exact (step_done c a b x).2 (Or.inl (h2 h'))

/-- Lemma 4.11 (one step): if `L = ω` and a step changes `L`, then after that step
`ω.stat = susp`, or `ω.stat = exec` and `ω` is done (and this persists by `post_step`). -/
theorem lemma_4_11 (hc : Reachable init step c) {x : D} (hL : c.L = some x) (a : Act P D)
    (b : Bool) (hne : (step c a b).1.L ≠ some x) : Post (step c a b).1 x := by
  refine post_step ?_ a b
  rcases step_L c a b with h | ⟨p, r, hpc, hw⟩
  · exact absurd (h.trans hL) hne
  · exact ((inv_reachable hc).2 p).hap r .l21 x hpc (hw ▸ hL)

/-- Lemma 4.12 (state form): a suspended descriptor has never been executed (and, by
Observation 4.10, never will be: see `lemma_4_15`). -/
theorem lemma_4_12 (hc : Reachable init step c) {x : D} (h : c.stat x = .susp) :
    c.started x = false := by
  by_contra h'
  rw [(inv_reachable hc).1.start_exec x (by simpa using h')] at h
  cases h

/-- Lemma 4.13 (state form): during the execution interval of `ω.T` (`ω` started, not
done), `L = ω`. -/
theorem lemma_4_13 (hc : Reachable init step c) {x : D} (h1 : c.started x = true)
    (h2 : c.done x = false) : c.L = some x :=
  (inv_reachable hc).1.active_L x h1 h2

end Lemmas

/-! ## (S1), (S2) -/

/-- The ghost observations of Algorithm 2 are coherent with its events. -/
theorem coherent : Coherent (init : Cfg P D) step (fun c d => c.started d = true)
    (fun c d => c.done d = true) Cfg.call Cfg.callIdx Cfg.clock where
  clock_init := rfl
  clock_step c a b _ := step_clock c a b
  started_init d := by simp [init]
  started_step c a b d _ := step_started c a b d
  done_init d := by simp [init]
  done_step c a b d _ := step_done c a b d
  call_init p := rfl
  call_inv c a b p d hc h := by
    obtain ⟨h1, -, h3, h4⟩ := step_inv c a b h
    exact ⟨((inv_reachable hc).2 p).idle_iff.1 h1, h3, h4⟩
  call_resp c a b p d r hc h := by
    obtain ⟨-, h2, h3, h4⟩ := step_resp c a b h
    exact ⟨h2, h4, by rw [h3]⟩
  call_other c a b p _ h1 h2 := step_call_other c a b h1 h2

/-- (S1) and (S2) for Algorithm 2 (Lemmas 4.14 and 4.15): in every execution, the execution
intervals of distinct thunks are disjoint, the execution interval of `ω.T` lies within the
`Lock(ω)` call, and a `Lock(ω)` call returns `True` iff it responds after `ω.T` has been
executed. -/
theorem alg2_safety (xs : List (Act P D × Bool)) :
    S1 (run init step xs).2 ∧ S2 (run init step xs).2 := by
  refine s1_s2_of_invariants coherent ?_ ?_ ?_ xs
  · -- Lemma 4.14 via Lemma 4.13
    intro c hc d₁ d₂ hne h1 h1' h2 h2'
    have e1 := lemma_4_13 hc h1 (by simpa using h1')
    have e2 := lemma_4_13 hc h2 (by simpa using h2')
    rw [e1] at e2
    exact hne (Option.some_injective _ e2)
  · intro c hc d h1 h1'
    have I := inv_reachable hc
    have hx := I.1.start_exec d h1
    have hu : c.used d = true := by
      by_contra hu
      rw [(I.1.unused d (by simpa using hu)).1] at hx
      cases hx
    exact I.1.pending d hu (by simpa using h1') (by rw [hx]; decide)
  · intro c a b p d r hc h h1
    obtain ⟨hpc, hx, -, -⟩ := step_resp c a b h
    obtain ⟨y, hy, hfin⟩ := ((inv_reachable hc).2 p).fin (Or.inr hpc)
    rw [hx] at hy; cases hy
    rcases hfin with hf | hf
    · exact hf
    · exact absurd (lemma_4_12 hc hf) (by simpa using h1)

/-- Lemma 4.15, second case: if a `Lock(ω)` call by `p` responds with `False` (event `j`),
then `p` has received the abort signal before (`abort_sig = True` in the configuration
before the response), and no `ω.execute()` is ever invoked in the execution. -/
theorem lemma_4_15 (xs : List (Act P D × Bool)) (j : ℕ) (p : P) (d : D)
    (h : (run init step xs).2[j]? = some (.resp p d false)) :
    (run init step (xs.take j)).1.abort p = true ∧
      ∀ k : ℕ, (run init step xs).2[k]? ≠ some (.exS d) := by
  have hlen := run_length init step xs
  have hj : j < xs.length := by
    rw [← hlen]; by_contra h'; push Not at h'; rw [List.getElem?_eq_none h'] at h; cases h
  obtain ⟨-, hev⟩ := run_take_succ init step xs j hj
  rw [hev] at h
  have hR : ∀ t, Reachable init step (run init step (xs.take t)).1 := fun t => ⟨_, rfl⟩
  obtain ⟨hpc, hx, hr, -⟩ := step_resp _ _ _ (Option.some_injective _ h)
  have I := inv_reachable (hR j)
  obtain ⟨y, hy, hfin⟩ := (I.2 p).fin (Or.inr hpc)
  rw [hx] at hy; cases hy
  have hsusp : (run init step (xs.take j)).1.stat d = .susp := by
    rcases hfin with hf | hf
    · rw [← hr] at hf; cases hf
    · exact hf
  refine ⟨I.1.abort_susp p d hx hsusp, ?_⟩
  -- `stat d = susp` from point `j` on (Observation 4.10)
  have hstay : ∀ t, j ≤ t → t ≤ xs.length → (run init step (xs.take t)).1.stat d = .susp := by
    intro t ht htl
    induction t, ht using Nat.le_induction with
    | base => exact hsusp
    | succ t ht ih =>
      rw [(run_take_succ init step xs t (by omega)).1, obs_4_10 _ _ _ d (by rw [ih (by omega)]; decide),
        ih (by omega)]
  have hend := lemma_4_12 (hR xs.length) (hstay xs.length hj.le le_rfl)
  intro k hk
  have hklen : k < xs.length := by
    rw [← hlen]; by_contra h'; push Not at h'; rw [List.getElem?_eq_none h'] at hk; cases hk
  have := (coherent.started_run xs xs.length le_rfl d).2 ⟨k, hklen, hk⟩
  rw [hend] at this
  cases this

/-! ## Non-vacuity: a solo `Lock()` call executes its thunk and returns `True` -/

/-- A single process `()` calls `Lock(())` and is scheduled 33 times: its thunk is executed
(events 13, 14) and the call returns `True` (event 33). -/
example :
    let es := (run (init : Cfg Unit Unit) step
      ((.invoke () (), false) :: List.replicate 33 (.sched () 0, false))).2
    es[13]? = some (.exS ()) ∧ es[14]? = some (.exE ()) ∧ es[33]? = some (.resp () () true) := by
  decide

end Podc.RandomizedWaitFreeLocks.Alg2
