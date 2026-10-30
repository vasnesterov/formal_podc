import Papers.PODC2022.AnonymousMACConsensus.Model

/-!
# MAC-SC is not wait-free under the literal handler-priority assumption

The abstract claims that all algorithms of the paper are wait-free. Assumption (iii) ("the handler
has a priority over the execution of the main thread") is needed for regularity
(`theorem_1_needs_priority`), but taken literally it lets the adversary starve a node's main
thread: if a new message is always delivered to node `0` before its handler has emptied its
queue, the first line of node `0`'s pending operation is never executed.

`mac_sc_not_wait_free` gives such an infinite execution on two nodes: node `1` stores forever,
completing one operation every 8 steps; every message delivered to node `0` is processed by its
handler (its queue never holds more than two messages, and the handler takes a step in every
round); nobody crashes; but node `0`'s `Collect`, invoked at the start, never executes line 4.
-/

namespace Podc.AnonymousMACConsensus

namespace Starvation

/-- Configurations on two nodes with natural-number values. -/
abbrev C := Config (Fin 2) ℕ

/-- The round-robin schedule: step `r` of a round of node `1`'s `Store₁(0)`. Step 4 is a handler
step of node `0`. -/
def nxt (r : ℕ) (c : C) : C :=
  match r with
  | 0 => { c with phase := Function.update c.phase 1 (.invoked (.store 0)) }
  | 1 => match c.phase 1 with
    | .invoked o => { c with phase := Function.update c.phase 1 (.bcast o (lineView c 1 o) ∅) }
    | _ => c
  | 2 => match c.phase 1 with
    | .bcast o cv got => { c with phase := Function.update c.phase 1 (.bcast o cv (insert 1 got)),
                                  queue := Function.update c.queue 1 (c.queue 1 ++ [cv]) }
    | _ => c
  | 3 => match c.phase 1 with
    | .bcast o cv got => { c with phase := Function.update c.phase 1 (.bcast o cv (insert 0 got)),
                                  queue := Function.update c.queue 0 (c.queue 0 ++ [cv]) }
    | _ => c
  | 4 => match c.queue 0 with
    | W :: q => { c with view := Function.update c.view 0 ((c.view 0).merge W),
                         queue := Function.update c.queue 0 q }
    | [] => c
  | 5 => match c.queue 1 with
    | W :: q => { c with view := Function.update c.view 1 ((c.view 1).merge W),
                         queue := Function.update c.queue 1 q }
    | [] => c
  | 6 => match c.phase 1 with
    | .bcast o cv _ => { c with phase := Function.update c.phase 1 (.acked o cv) }
    | _ => c
  | 7 => match c.phase 1 with
    | .acked _ _ => { c with phase := Function.update c.phase 1 .idle,
                              cnt := Function.update c.cnt 1 (c.cnt 1 + 1) }
    | _ => c
  | _ => c

/-- Shape of node `1` (and of the crash set) before step `r` of a round. -/
def Shape1 (r : ℕ) (c : C) : Prop :=
  c.crashed = ∅ ∧
  match r with
  | 0 => c.phase 1 = .idle ∧ c.queue 1 = []
  | 1 => ∃ o, c.phase 1 = .invoked o ∧ c.queue 1 = []
  | 2 => ∃ o cv, c.phase 1 = .bcast o cv ∅ ∧ c.queue 1 = []
  | 3 => ∃ o cv, c.phase 1 = .bcast o cv {1} ∧ c.queue 1 = [cv]
  | 4 => ∃ o cv, c.phase 1 = .bcast o cv {0, 1} ∧ c.queue 1 = [cv]
  | 5 => ∃ o cv, c.phase 1 = .bcast o cv {0, 1} ∧ c.queue 1 = [cv]
  | 6 => ∃ o cv, c.phase 1 = .bcast o cv {0, 1} ∧ c.queue 1 = []
  | 7 => ∃ o cv, c.phase 1 = .acked o cv ∧ c.queue 1 = []
  | _ => False

lemma Shape1.lt {r : ℕ} {c : C} (h : Shape1 r c) : r < 8 := by
  obtain ⟨-, h⟩ := h
  match r, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => omega

/-- Each step of the schedule is a step of MAC-SC (with handler priority) and preserves the shape
of node `1`. The handler step of node `0` needs a nonempty queue. -/
lemma Shape1.step {r : ℕ} {c : C} (h : Shape1 r c) (h4 : r = 4 → c.queue 0 ≠ []) :
    (∃ l, Step true c l (nxt r c)) ∧ Shape1 ((r + 1) % 8) (nxt r c) := by
  obtain ⟨hcr, h⟩ := h
  match r, h with
  | 0, ⟨hp, hq⟩ =>
    refine ⟨⟨_, Step.invoke c 1 (.store 0) (by simp [hcr]) hp⟩, ?_⟩
    simp [Shape1, nxt, hcr, hq]
  | 1, ⟨o, hp, hq⟩ =>
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hp]; exact Step.exec c 1 o (by simp [hcr]) hp (fun _ => hq)
    · simp [Shape1, nxt, hp, hcr, hq]
  | 2, ⟨o, cv, hp, hq⟩ =>
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hp]; exact Step.deliver c 1 1 o cv ∅ hp (by simp)
    · simp [Shape1, nxt, hp, hcr, hq]
  | 3, ⟨o, cv, hp, hq⟩ =>
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hp]; exact Step.deliver c 1 0 o cv {1} hp (by simp)
    · simp only [Shape1, nxt, hp]
      refine ⟨hcr, o, cv, ?_, ?_⟩
      · simp
      · simp [hq]
  | 4, ⟨o, cv, hp, hq⟩ =>
    obtain ⟨W, q, hq0⟩ := List.exists_cons_of_ne_nil (h4 rfl)
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hq0]; exact Step.handle c 0 W q (by simp [hcr]) hq0
    · simp [Shape1, nxt, hq0, hcr, hp, hq]
  | 5, ⟨o, cv, hp, hq⟩ =>
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hq]; exact Step.handle c 1 cv [] (by simp [hcr]) hq
    · simp [Shape1, nxt, hq, hcr, hp]
  | 6, ⟨o, cv, hp, hq⟩ =>
    refine ⟨⟨none, ?_⟩, ?_⟩
    · simp only [nxt, hp]
      exact Step.ack c 1 o cv {0, 1} (by simp [hcr]) hp (by intro k _; fin_cases k <;> simp)
    · simp [Shape1, nxt, hp, hcr, hq]
  | 7, ⟨o, cv, hp, hq⟩ =>
    refine ⟨⟨some (.ret 1 (c.cnt 1) (resp o cv)), ?_⟩, ?_⟩
    · simp only [nxt, hp]; exact Step.ret c 1 o cv (by simp [hcr]) hp
    · simp [Shape1, nxt, hp, hcr, hq]

lemma nxt_phase0 (r : ℕ) (c : C) : (nxt r c).phase 0 = c.phase 0 := by
  match r with
  | 0 => simp [nxt]
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp only [nxt]; split <;> simp
  | _ + 8 => rfl

lemma nxt_queue0 (r : ℕ) (c : C) (hr : r ≠ 3) (hr' : r ≠ 4) : (nxt r c).queue 0 = c.queue 0 := by
  match r, hr, hr' with
  | 0, _, _ => simp [nxt]
  | 1, _, _ | 2, _, _ | 5, _, _ | 6, _, _ | 7, _, _ => simp only [nxt]; split <;> simp
  | _ + 8, _, _ => rfl

lemma nxt_queue0_three {c : C} (h : Shape1 3 c) : ∃ cv, (nxt 3 c).queue 0 = c.queue 0 ++ [cv] := by
  obtain ⟨-, o, cv, hp, -⟩ := h
  exact ⟨cv, by simp [nxt, hp]⟩

lemma nxt_queue0_four {c : C} {W : View (Fin 2) ℕ} {q : List (View (Fin 2) ℕ)}
    (h : c.queue 0 = W :: q) :
    (nxt 4 c).queue 0 = q ∧
      nxt 4 c = { c with view := Function.update c.view 0 ((c.view 0).merge W),
                         queue := Function.update c.queue 0 q } := by
  simp [nxt, h]

lemma nxt_cnt1 (r : ℕ) (c : C) (hr : r ≠ 7) : (nxt r c).cnt 1 = c.cnt 1 := by
  match r, hr with
  | 0, _ => simp [nxt]
  | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => simp only [nxt]; split <;> simp
  | _ + 8, _ => rfl

lemma nxt_cnt1_seven {c : C} (h : Shape1 7 c) : (nxt 7 c).cnt 1 = c.cnt 1 + 1 := by
  obtain ⟨-, o, cv, hp, -⟩ := h
  simp [nxt, hp]

/-! ## The preamble -/

lemma phase_update_self' (v : Fin 2 → View (Fin 2) ℕ) (q : Fin 2 → List (View (Fin 2) ℕ))
    (n : Fin 2 → ℕ) (f : Fin 2 → Phase (Fin 2) ℕ) (cr : Set (Fin 2)) (i : Fin 2)
    (x : Phase (Fin 2) ℕ) : (Config.mk v q n (Function.update f i x) cr).phase i = x := by simp

/-- A run of the schedule from `c` started at step `r₀` of a round. -/
def run (r₀ : ℕ) (c : C) : ℕ → C
  | 0 => c
  | t + 1 => nxt ((r₀ + t) % 8) (run r₀ c t)

/-- The starting configuration: node `1` has completed `Store₁(0)` without node `0` processing its
message; then node `0` invoked `Collect₀`. -/
lemma exists_start : ∃ (c : C) (h : History (Fin 2) ℕ), Reach true c h ∧
    Label.inv 0 0 .collect ∈ h ∧ Shape1 0 c ∧ c.phase 0 = .invoked .collect ∧
    (c.queue 0).length = 1 ∧ c.cnt 1 = 1 := by
  have s0 : Shape1 0 (Config.init : C) := by simp [Shape1, Config.init]
  have r0 : Reach true (Config.init : C) [] := Reach.init
  obtain ⟨⟨l1, st1⟩, s1⟩ := s0.step (by simp)
  obtain ⟨⟨l2, st2⟩, s2⟩ := s1.step (by simp)
  obtain ⟨⟨l3, st3⟩, s3⟩ := s2.step (by simp)
  obtain ⟨⟨l4, st4⟩, s4⟩ := s3.step (by simp)
  -- skip the handler step of node `0` (step 4): use steps 5, 6, 7 directly
  have s4' : Shape1 5 (nxt 3 (nxt 2 (nxt 1 (nxt 0 Config.init)))) := by
    obtain ⟨hcr, o, cv, hp, hq⟩ := s4
    exact ⟨hcr, o, cv, hp, hq⟩
  obtain ⟨⟨l5, st5⟩, s5⟩ := s4'.step (by simp)
  obtain ⟨⟨l6, st6⟩, s6⟩ := s5.step (by simp)
  obtain ⟨⟨l7, st7⟩, s7⟩ := s6.step (by simp)
  set c7 := nxt 7 (nxt 6 (nxt 5 (nxt 3 (nxt 2 (nxt 1 (nxt 0 Config.init)))))) with hc7
  have hph0 : c7.phase 0 = .idle := by simp [c7, nxt_phase0, Config.init]
  have hq0 : c7.queue 0 = (nxt 3 (nxt 2 (nxt 1 (nxt 0 Config.init)))).queue 0 := by
    simp [c7, nxt_queue0]
  obtain ⟨cv, hcv⟩ := nxt_queue0_three s3
  have hcnt : c7.cnt 1 = 1 := by
    simp only [c7]
    rw [nxt_cnt1_seven s6]
    simp [nxt_cnt1, Config.init]
  obtain ⟨hcr7, s7⟩ := s7
  have st8 := Step.invoke (prio := true) c7 0 .collect (by simp [hcr7]) hph0
  have hr := (((((((r0.step st1).step st2).step st3).step st4).step st5).step st6).step st7).step st8
  refine ⟨_, _, hr, ?_, ⟨hcr7, ?_⟩, by simp, ?_, by simpa using hcnt⟩
  · have : c7.cnt 0 = 0 := by simp [c7, Config.init, nxt]
    simp [this]
  · simpa using s7
  · simp only [Nat.reduceAdd, Nat.reduceMod] at hcv
    rw [hq0, hcv, nxt_queue0 2 _ (by decide) (by decide), nxt_queue0 1 _ (by decide) (by decide),
      nxt_queue0 0 _ (by decide) (by decide)]
    simp [Config.init]

/-- **MAC-SC is not wait-free** when the handler has absolute priority (assumption (iii) taken
literally). There is an infinite execution of MAC-SC on two nodes, starting in a reachable
configuration in which node `0` has invoked `Collect₀`, such that nobody crashes, node `1`
completes an operation in every round of 8 steps, node `0`'s handler takes a step in every round
and its queue never holds more than two messages (so every message delivered to `0` is processed),
yet node `0`'s queue is never empty, so its `Collect₀` never executes line 4 and never returns. -/
theorem mac_sc_not_wait_free :
    ∃ (ex : ℕ → Config (Fin 2) ℕ) (h₀ : History (Fin 2) ℕ),
      Reach true (ex 0) h₀ ∧ Label.inv 0 0 .collect ∈ h₀ ∧
      (∀ t, ∃ l, Step true (ex t) l (ex (t + 1))) ∧
      (∀ t, (ex t).crashed = ∅) ∧
      (∀ t, (ex t).phase 0 = .invoked .collect) ∧
      (∀ t, (ex t).queue 0 ≠ [] ∧ ((ex t).queue 0).length ≤ 2) ∧
      (∀ k, (ex (8 * k)).cnt 1 = k + 1) ∧
      (∀ k, ∃ W q, (ex (8 * k + 4)).queue 0 = W :: q ∧
        ex (8 * k + 5) = { ex (8 * k + 4) with
          view := Function.update (ex (8 * k + 4)).view 0 (((ex (8 * k + 4)).view 0).merge W),
          queue := Function.update (ex (8 * k + 4)).queue 0 q }) := by
  obtain ⟨c, h, hr, hinv, hs, hph, hlen, hcnt⟩ := exists_start
  set ex := run 0 c with hex
  have hsucc : ∀ t, ex (t + 1) = nxt (t % 8) (ex t) := by
    intro t; simp [ex, run]
  -- the invariant
  have key : ∀ t, Shape1 (t % 8) (ex t) ∧ (ex t).phase 0 = .invoked .collect ∧
      ((ex t).queue 0).length = (if t % 8 = 4 then 2 else 1) ∧
      (ex t).cnt 1 = t / 8 + 1 := by
    intro t
    induction t with
    | zero => exact ⟨hs, hph, by simpa [ex, run] using hlen, by simpa [ex, run] using hcnt⟩
    | succ t ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hne : t % 8 = 4 → (ex t).queue 0 ≠ [] := by
        intro h4'; rw [h4'] at h3; simp at h3
        intro he; rw [he] at h3; simp at h3
      obtain ⟨-, h1'⟩ := h1.step hne
      rw [hsucc]
      refine ⟨by rw [Nat.add_mod]; simpa using h1', by rw [nxt_phase0, h2], ?_, ?_⟩
      · have hlt := Nat.mod_lt t (show 8 > 0 by norm_num)
        rcases (show t % 8 = 3 ∨ t % 8 = 4 ∨ (t % 8 ≠ 3 ∧ t % 8 ≠ 4) by omega) with h | h | ⟨h, h'⟩
        · obtain ⟨cv, hcv⟩ := nxt_queue0_three (h ▸ h1)
          rw [h, hcv]
          rw [h] at h3
          simp at h3
          have : (t + 1) % 8 = 4 := by omega
          simp [this, h3]
        · obtain ⟨W, q, hq⟩ := List.exists_cons_of_ne_nil (hne h)
          rw [h, (nxt_queue0_four hq).1]
          rw [h, hq] at h3
          simp at h3
          have : (t + 1) % 8 ≠ 4 := by omega
          simp [this]; omega
        · rw [nxt_queue0 _ _ h h', h3]
          have : (t + 1) % 8 ≠ 4 := by omega
          have : t % 8 ≠ 4 := h'
          simp [*]
      · rcases (show t % 8 = 7 ∨ t % 8 ≠ 7 by omega) with h | h
        · rw [h, nxt_cnt1_seven (h ▸ h1), h4]; omega
        · rw [nxt_cnt1 _ _ h, h4]; omega
  refine ⟨ex, h, by simpa [ex, run] using hr, hinv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    have := ((key t).1.step (fun h4 => by
      have h3 := (key t).2.2.1; rw [h4] at h3; intro he; rw [he] at h3; simp at h3)).1
    rwa [hsucc]
  · intro t; exact (key t).1.1
  · intro t; exact (key t).2.1
  · intro t
    have h3 := (key t).2.2.1
    constructor
    · intro he; rw [he] at h3; split_ifs at h3
    · rw [h3]; split_ifs <;> omega
  · intro k
    have := (key (8 * k)).2.2.2
    rw [this]; omega
  · intro k
    have h3 := (key (8 * k + 4)).2.2.1
    have hm : (8 * k + 4) % 8 = 4 := by omega
    rw [hm] at h3
    simp only [ite_true] at h3
    obtain ⟨W, q, hq⟩ := List.exists_cons_of_ne_nil (show (ex (8 * k + 4)).queue 0 ≠ [] by
      intro he; rw [he] at h3; simp at h3)
    refine ⟨W, q, hq, ?_⟩
    rw [hsucc, hm]
    exact (nxt_queue0_four hq).2

end Starvation

end Podc.AnonymousMACConsensus
