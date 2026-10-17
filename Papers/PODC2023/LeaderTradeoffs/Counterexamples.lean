import Papers.PODC2023.LeaderTradeoffs.Tradeoff

/-!
# Counterexamples: the one-round broadcast algorithm

`broadcast m`: in round 1 every node sends its ID on all ports; after round 1 a node outputs
"leader" iff its own ID is larger than every received ID; this decision is irrevocable and the node
stays silent afterwards (`broadcast_terminatesBy`). It elects
the maximum ID in one round with `n (n - 1)` messages.

* `theorem_3_8_as_stated_false`: Theorem 3.8 as stated (`T > (log₂ n - 1)/(log₂ f + 1) + 1`)
  fails for **every** power of two `n ≥ 2`, with the increasing function `f(n) = n` and an ID
  universe of the required size: `broadcast` has `T = 1`, while the claimed bound is `> 1`.
  (The corrected bound `T > (log₂ n - 1)/(⌈log₂ f⌉ + 1)` of `theorem_3_8_corrected` holds.)
* `terminatingLiteral_broadcast`, `lemma_3_6_literal_false`: Definition 3.5 read literally
  ("for every restricted execution prefix in `Exec_r(X)`, all nodes of `X` have terminated") is
  vacuous whenever `Exec_r(X)` is empty. For `broadcast` every set of fewer than `n` IDs is then
  "terminating", so Lemma 3.6 (at most `n / 2^ℓ` disjoint terminating `2^ℓ`-sets) and
  Corollary 3.7 fail for the literal definition; they hold for the existential reading
  (`Isolable`, `not_disjoint_isolable`, `exists_universe_no_isolable`).
-/

open Classical Finset

namespace LeaderTradeoffs

/-- Sending rule of `broadcast`: undecided nodes send their ID on every port. -/
def bcSend {m : ℕ} (s : ℕ × Option Bool) (_ : Fin m) : Option ℕ :=
  if s.2.isNone then some s.1 else none

/-- Step rule of `broadcast`: an undecided node decides "leader" iff all received IDs are smaller;
decided nodes never change their state. -/
def bcStep {m : ℕ} (s : ℕ × Option Bool) (inbox : Fin m → Option ℕ) : ℕ × Option Bool :=
  if s.2.isSome then s else
    (s.1, some (decide (∀ j, (inbox j).all (fun x => decide (x < s.1)) = true)))

/-- The one-round broadcast algorithm. -/
def broadcast (m : ℕ) : Algorithm m where
  State := ℕ × Option Bool
  Msg := ℕ
  init x := (x, none)
  send := bcSend
  step := bcStep
  output s := s.2

variable {m : ℕ}

theorem bcStep_fst (s : ℕ × Option Bool) (inb : Fin m → Option ℕ) : (bcStep s inb).1 = s.1 := by
  unfold bcStep; split <;> rfl

theorem bcStep_of_isSome {s : ℕ × Option Bool} (h : s.2.isSome) (inb : Fin m → Option ℕ) :
    bcStep s inb = s := by
  unfold bcStep; rw [if_pos h]

theorem broadcast_run_zero (p : PortMap m) (u : ℕ) : run (broadcast m) p 0 u = (u, none) := rfl

theorem broadcast_run_succ_fst (p : PortMap m) (r u : ℕ) :
    (run (broadcast m) p r u).1 = u := by
  induction r with
  | zero => rfl
  | succ r ih => exact (bcStep_fst _ _).trans ih

theorem broadcast_run_succ_snd (p : PortMap m) (r u : ℕ) :
    ((run (broadcast m) p (r + 1) u).2).isSome := by
  induction r with
  | zero => simp [run, broadcast, bcStep]
  | succ r ih =>
    exact (congrArg (fun s : ℕ × Option Bool => s.2.isSome)
      (bcStep_of_isSome ih _)).trans ih

/-- Decisions are irrevocable: the state after round 1 never changes. -/
theorem broadcast_run_stable (p : PortMap m) (r u : ℕ) :
    run (broadcast m) p (r + 1) u = run (broadcast m) p 1 u := by
  induction r with
  | zero => rfl
  | succ r ih =>
    show (broadcast m).step (run (broadcast m) p (r + 1) u) _ = _
    exact (bcStep_of_isSome (broadcast_run_succ_snd p r u) _).trans ih

theorem broadcast_inbox_zero {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) {u : ℕ}
    (hu : u ∈ I) (j : Fin m) {v : ℕ} (hj : p u j = some v) :
    inbox (broadcast m) p (run (broadcast m) p 0) u j = some v := by
  have hv : v ∈ I := hp.1.mem u hu j v hj
  obtain ⟨i, hi⟩ := hp.1.symm u hu j v hj
  simp only [inbox, hj, Option.bind_some, backPort_eq hp.1 hv hi]
  rfl

theorem broadcast_output_one {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I)
    (hI : I.card = m + 1) {u : ℕ} (hu : u ∈ I) :
    (broadcast m).output (run (broadcast m) p 1 u) = some (decide (∀ v ∈ I, v ≠ u → v < u)) := by
  show (run (broadcast m) p 1 u).2 = _
  simp only [run, broadcast_run_zero]
  show some (decide (∀ j, (inbox (broadcast m) p (run (broadcast m) p 0) u j).all
    (fun x => decide (x < u)) = true)) = _
  congr 1
  apply decide_eq_decide.2
  constructor
  · intro h v hv hne
    obtain ⟨j, hj⟩ := hp.surj hI hu hv hne
    have := h j
    rw [broadcast_inbox_zero hp hu j hj] at this
    simpa using this
  · intro h j
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hp.2 u hu j)
    rw [broadcast_inbox_zero hp hu j hv]
    have hvI : v ∈ I := hp.1.mem u hu j v hv
    have hne : v ≠ u := fun h' => hp.1.ne u hu j (h' ▸ hv)
    simpa using h v hvI hne

/-- `broadcast` elects (the maximum ID) in one round, for every ID universe. -/
theorem broadcast_electsBy (U : Finset ℕ) : ElectsBy (broadcast m) U 1 := by
  intro I _ hI p hp
  have hne : I.Nonempty := by rw [← Finset.card_pos, hI]; omega
  rw [Finset.card_eq_one]
  refine ⟨I.max' hne, ?_⟩
  ext u
  simp only [leaders, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hu, h⟩
    rw [broadcast_output_one hp hI hu] at h
    simp only [Option.some.injEq, decide_eq_true_eq] at h
    apply le_antisymm (Finset.le_max' _ _ hu)
    apply Finset.max'_le
    intro v hv
    by_cases hvu : v = u
    · rw [hvu]
    · exact (h v hv hvu).le
  · rintro rfl
    refine ⟨Finset.max'_mem _ _, ?_⟩
    rw [broadcast_output_one hp hI (Finset.max'_mem _ _)]
    simp only [Option.some.injEq, decide_eq_true_eq]
    intro v hv hne
    exact lt_of_le_of_ne (Finset.le_max' _ _ hv) hne

theorem broadcast_msgs (p : PortMap m) (I : Finset ℕ) :
    msgs (broadcast m) p 1 I = I.card * m := by
  simp only [msgs, Finset.sum_range_one, roundMsgs, broadcast_run_zero, sendCount]
  simp [broadcast, bcSend]

/-- `broadcast` terminates in one round: every node decides after round 1, never changes its
output and never sends again. -/
theorem broadcast_terminatesBy (U : Finset ℕ) : TerminatesBy (broadcast m) U 1 := by
  intro I _ _ p _ u _
  refine ⟨broadcast_run_succ_snd p 0 u, fun r hr => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [broadcast_run_stable]
  refine ⟨rfl, ?_⟩
  have h := broadcast_run_succ_snd p 0 u
  unfold sendCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  show ¬ (bcSend (run (broadcast m) p 1 u) j).isSome = true
  unfold bcSend
  rw [if_neg (by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using h)]
  simp

/-- `broadcast` sends `n (n - 1) ≤ n · n` messages. -/
theorem broadcast_msgBound (U : Finset ℕ) :
    MsgBound (broadcast m) U 1 ((m + 1) * ((m : ℝ) + 1)) := by
  intro I _ hI p _
  rw [broadcast_msgs, hI]
  push_cast
  nlinarith

/-- **Theorem 3.8 as stated is false.** For every `n = 2^k ≥ 2`, the increasing function
`f(n) = n > 1` and an ID universe of size `2 n log₂ n + n`, the broadcast algorithm elects a
leader in `T = 1` round with at most `n · f(n)` messages, but the claimed bound
`T > (log₂ n - 1)/(log₂ f(n) + 1) + 1` is larger than `1`. -/
theorem theorem_3_8_as_stated_false {k : ℕ} (hk : 1 ≤ k) (hm : m + 1 = 2 ^ k) :
    ∃ (A : Algorithm m) (U : Finset ℕ) (T : ℕ), 2 * (m + 1) * k + (m + 1) ≤ U.card ∧
      ElectsBy A U T ∧ TerminatesBy A U T ∧ MsgBound A U T ((m + 1) * ((m : ℝ) + 1)) ∧
      ¬ ((Real.logb 2 (m + 1) - 1) / (Real.logb 2 ((m : ℝ) + 1) + 1) + 1 < T) := by
  refine ⟨broadcast m, range (2 * (m + 1) * k + (m + 1)), 1, by simp, broadcast_electsBy _,
    broadcast_terminatesBy _, broadcast_msgBound _, ?_⟩
  have hlog : Real.logb 2 ((m : ℝ) + 1) = k := by
    rw [show ((m : ℝ) + 1) = (2 : ℝ) ^ k by exact_mod_cast hm,
      Real.logb_self_pow two_pos (by norm_num)]
  rw [hlog]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 0 ≤ ((k : ℝ) - 1) / (k + 1) := div_nonneg (by linarith) (by linarith)
  push_cast
  linarith

/-- Definition 3.5 read literally: `X` "forms terminating components" if for some round `r`,
in **every** restricted execution prefix of `X` (partial port mapping on `X`, all messages of
`X`-nodes received inside `X` through round `r`) all nodes of `X` have terminated. -/
def TerminatingLiteral (A : Algorithm m) (X : Finset ℕ) : Prop :=
  ∃ r, ∀ p : PortMap m, WF p X → Valid A p r X → ∀ u ∈ X, (A.output (run A p r u)).isSome

/-- For `broadcast`, every set of fewer than `n` IDs is literally "terminating": `Exec_1(X)` is
empty because each node sends on all `n - 1` ports in round 1. -/
theorem terminatingLiteral_broadcast {X : Finset ℕ} (hX : X.card ≤ m) :
    TerminatingLiteral (broadcast m) X := by
  refine ⟨1, fun p hp hv u hu => ?_⟩
  exfalso
  have hfree : freePorts p u = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    simp only [freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have := hv 0 (by norm_num) u hu j hj
    exact absurd this (by rw [broadcast_run_zero]; simp [broadcast, bcSend])
  have h1 := card_nbrs hp hu
  rw [hfree, Finset.card_empty, add_zero] at h1
  have h2 := Finset.card_le_card (nbrs_subset hp hu)
  rw [Finset.card_erase_of_mem hu] at h2
  have : 0 < X.card := Finset.card_pos.2 ⟨u, hu⟩
  omega

/-- **Lemma 3.6 with the literal Definition 3.5 is false**: with `n = 2` nodes and `ℓ = 0`,
the lemma allows at most `2^(log₂ n - ℓ) = 2` disjoint terminating singletons, but for the
(correct) broadcast algorithm all singletons are literally terminating. -/
theorem lemma_3_6_literal_false :
    ElectsBy (broadcast 1) (range 3) 1 ∧ TerminatesBy (broadcast 1) (range 3) 1 ∧
      (∀ i ∈ range 3, TerminatingLiteral (broadcast 1) {i}) ∧ 2 ^ (1 - 0) < 3 := by
  refine ⟨broadcast_electsBy _, broadcast_terminatesBy _, fun i _ => terminatingLiteral_broadcast (by simp), by norm_num⟩

end LeaderTradeoffs
