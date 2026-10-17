import Papers.PODC2023.LeaderTradeoffs.Model

-- CSLib candidate

/-!
# From multicast to single-send algorithms (Lemma 3.12)

Lemma 3.12 of Kutten, Robinson, Tan, Zhu, *Improved Tradeoffs for Leader Election* (PODC 2023):
a multicast algorithm `A` sending `M(n)` messages in `T(n)` rounds can be turned into a
*single-send* algorithm (at most one message per node per round) sending at most `M(n)`
messages in at most `n · T(n)` rounds.

**Construction** (`simulate`). Each round of `A` is simulated by `n = m + 1` sub-rounds. The
simulating node keeps the `A`-state of the start of the simulated round, a sub-round counter
`k ∈ {0, …, m}` and a buffer of the messages received so far, indexed by the receiving port.
In sub-round `k < m` it sends `A`'s message for port `k` (and only that one) on port `k`; every
received message is stored in the buffer. Sub-round `m` is idle; at its end the node applies
`A.step` to its `A`-state and the buffer, and clears the buffer.

Since `inbox` delivers `v`'s message for `u` along the single port `backPort p v u`, this message
arrives exactly in the sub-round equal to that port. The simulation is therefore exact for
*every* (even partial, non-well-formed) port map `p` (`run_simulate`), and every `A`-message is
sent exactly once, so the message counts coincide exactly (`msgs_simulate`), not just up to `≤`.
-/

open Classical Finset

namespace LeaderTradeoffs

variable {m : ℕ}

/-- A *single-send* algorithm sends at most one message per round at every node
(Lemma 3.12 of [Kutten, Robinson, Tan, Zhu, PODC 2023]). -/
def SingleSend (A : Algorithm m) : Prop := ∀ s, sendCount A s ≤ 1

/-- The single-send simulation of a multicast algorithm `A` (proof of Lemma 3.12). A state is
`(A-state, sub-round counter, buffer of received messages indexed by the receiving port)`. -/
def simulate (A : Algorithm m) : Algorithm m where
  State := A.State × ℕ × (Fin m → Option A.Msg)
  Msg := A.Msg
  init x := (A.init x, 0, fun _ => none)
  send st j := if j.val = st.2.1 then A.send st.1 j else none
  step st inb :=
    if st.2.1 < m then (st.1, st.2.1 + 1, fun j => (inb j).or (st.2.2 j))
    else (A.step st.1 st.2.2, 0, fun _ => none)
  output st := A.output st.1

variable {A : Algorithm m} {p : PortMap m}

/-- Lemma 3.12: the simulation is single-send. -/
theorem simulate_singleSend (A : Algorithm m) : SingleSend (simulate A) := by
  intro st
  unfold sendCount
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 : a.val = st.2.1 := by
    by_contra h; simp [simulate, h] at ha
  have h2 : b.val = st.2.1 := by
    by_contra h; simp [simulate, h] at hb
  exact Fin.ext (by omega)

/-- The buffer after `k` sub-rounds of the simulated round whose start states are `st`: the
messages that were sent on ports `< k`. -/
noncomputable def subBuf (A : Algorithm m) (p : PortMap m) (st : ℕ → A.State) (k u : ℕ) :
    Fin m → Option A.Msg := fun j =>
  (p u j).bind fun v => (backPort p v u).bind fun i =>
    if i.val < k then A.send (st v) i else none

theorem subBuf_zero (st : ℕ → A.State) (u : ℕ) : subBuf A p st 0 u = fun _ => none := by
  funext j
  simp only [subBuf, Nat.not_lt_zero, ite_false]
  rcases p u j with _ | v
  · rfl
  · simp only [Option.bind_some]
    rcases backPort p v u with _ | i <;> rfl

theorem subBuf_m (st : ℕ → A.State) (u : ℕ) : subBuf A p st m u = inbox A p st u := by
  funext j
  simp [subBuf, inbox, Fin.is_lt]

/-- One sub-round `k < m` of the simulation. -/
theorem run_simulate_sub {r k : ℕ} (hk : k < m)
    (h : ∀ u, run (simulate A) p ((m + 1) * r + k) u =
      (run A p r u, k, subBuf A p (run A p r) k u)) :
    ∀ u, run (simulate A) p ((m + 1) * r + (k + 1)) u =
      (run A p r u, k + 1, subBuf A p (run A p r) (k + 1) u) := by
  intro u
  have h' : run (simulate A) p ((m + 1) * r + k) =
      fun u => (run A p r u, k, subBuf A p (run A p r) k u) := funext h
  rw [← Nat.add_assoc, run, h']
  simp only [simulate, hk, ite_true, Prod.mk.injEq, true_and]
  funext j
  simp only [inbox, subBuf]
  rcases p u j with _ | v
  · rfl
  · simp only [Option.bind_some]
    rcases backPort p v u with _ | i
    · rfl
    · simp only [Option.bind_some]
      by_cases hik : i.val = k
      · simp [hik]
      · by_cases hlt : i.val < k
        · simp [hik, hlt, show i.val < k + 1 by omega]
        · simp [hik, hlt, show ¬ i.val < k + 1 by omega]

/-- The last (idle) sub-round `m` of the simulation applies `A.step`. -/
theorem run_simulate_round {r : ℕ}
    (h : ∀ u, run (simulate A) p ((m + 1) * r + m) u =
      (run A p r u, m, subBuf A p (run A p r) m u)) :
    ∀ u, run (simulate A) p ((m + 1) * (r + 1) + 0) u =
      (run A p (r + 1) u, 0, subBuf A p (run A p (r + 1)) 0 u) := by
  intro u
  have h' : run (simulate A) p ((m + 1) * r + m) =
      fun u => (run A p r u, m, subBuf A p (run A p r) m u) := funext h
  have heq : (m + 1) * (r + 1) + 0 = (m + 1) * r + m + 1 := by ring
  rw [heq, run, h', subBuf_zero]
  simp [simulate, run, subBuf_m]

/-- The simulation invariant (proof of Lemma 3.12), for an arbitrary port map: after `k ≤ m`
sub-rounds of simulated round `r`, a node holds `A`'s state after `r` rounds, counter `k` and
the messages sent to it on ports `< k`. -/
theorem run_simulate (r : ℕ) : ∀ k ≤ m, ∀ u,
    run (simulate A) p ((m + 1) * r + k) u = (run A p r u, k, subBuf A p (run A p r) k u) := by
  have base : ∀ r, (∀ u, run (simulate A) p ((m + 1) * r + 0) u =
      (run A p r u, 0, subBuf A p (run A p r) 0 u)) → ∀ k ≤ m, ∀ u,
      run (simulate A) p ((m + 1) * r + k) u = (run A p r u, k, subBuf A p (run A p r) k u) := by
    intro r h0 k hk
    induction k with
    | zero => exact h0
    | succ k ih => exact run_simulate_sub (by omega) (ih (by omega))
  induction r with
  | zero =>
    apply base
    intro u
    rw [subBuf_zero]
    rfl
  | succ r ih => exact base _ (run_simulate_round (ih m le_rfl))

/-- At the start of each simulated round the simulation holds exactly `A`'s state, counter `0`
and an empty buffer. -/
theorem run_simulate_mul (r u : ℕ) :
    run (simulate A) p ((m + 1) * r) u = (run A p r u, 0, fun _ => none) := by
  have := run_simulate (A := A) (p := p) r 0 (Nat.zero_le _) u
  rwa [Nat.add_zero, subBuf_zero] at this

/-- The simulation has the output of `A` after `(m + 1) · T` rounds. -/
theorem simulate_output (T u : ℕ) :
    (simulate A).output (run (simulate A) p ((m + 1) * T) u) = A.output (run A p T u) := by
  rw [run_simulate_mul]
  rfl

theorem sendCount_simulate (s : A.State) (k : ℕ) (b : Fin m → Option A.Msg) :
    sendCount (simulate A) (s, k, b) =
      #{j ∈ {j | (A.send s j).isSome} | j.val = k} := by
  unfold sendCount
  congr 1
  ext j
  by_cases hj : j.val = k <;> simp [simulate, hj]

/-- Over the `m + 1` sub-rounds of a simulated round, each `A`-message is sent exactly once. -/
theorem sum_sendCount_simulate (s : A.State) (b : ℕ → Fin m → Option A.Msg) :
    ∑ k ∈ range (m + 1), sendCount (simulate A) (s, k, b k) = sendCount A s := by
  simp only [sendCount_simulate]
  rw [sendCount, card_eq_sum_card_fiberwise (f := Fin.val) (t := range (m + 1))]
  intro j _
  simp only [coe_range, Set.mem_Iio]
  omega

theorem roundMsgs_simulate (T : ℕ) (S : Finset ℕ) :
    ∑ k ∈ range (m + 1), roundMsgs (simulate A) p ((m + 1) * T + k) S = roundMsgs A p T S := by
  unfold roundMsgs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl fun k hk => by
    rw [run_simulate T k (by simp only [mem_range] at hk; omega) u]]
  exact sum_sendCount_simulate _ _

/-- Lemma 3.12: the simulation sends exactly as many messages in `(m + 1) · T` rounds as `A`
sends in `T` rounds, for every port map. -/
theorem msgs_simulate (p : PortMap m) (T : ℕ) (S : Finset ℕ) :
    msgs (simulate A) p ((m + 1) * T) S = msgs A p T S := by
  induction T with
  | zero => simp [msgs]
  | succ T ih =>
    rw [show (m + 1) * (T + 1) = (m + 1) * T + (m + 1) by ring, msgs_succ, ← ih]
    unfold msgs
    rw [Finset.sum_range_add, roundMsgs_simulate]

theorem leaders_simulate (p : PortMap m) (T : ℕ) (I : Finset ℕ) :
    leaders (simulate A) p ((m + 1) * T) I = leaders A p T I := by
  unfold leaders
  exact Finset.filter_congr fun u _ => by rw [simulate_output]

/-- Lemma 3.12 (correctness): the simulation elects a leader by round `(m + 1) · T`. -/
theorem electsBy_simulate {U : Finset ℕ} {T : ℕ} (h : ElectsBy A U T) :
    ElectsBy (simulate A) U ((m + 1) * T) := by
  intro I hI hc p hp
  rw [leaders_simulate]
  exact h I hI hc p hp

/-- Lemma 3.12 (message complexity): the simulation obeys the message bound of `A`. -/
theorem msgBound_simulate {U : Finset ℕ} {T : ℕ} {M : ℝ} (h : MsgBound A U T M) :
    MsgBound (simulate A) U ((m + 1) * T) M := by
  intro I hI hc p hp
  rw [msgs_simulate]
  exact h I hI hc p hp

/-- Lemma 3.12 (termination): the simulation terminates by round `(m + 1) · T`. -/
theorem terminatesBy_simulate {U : Finset ℕ} {T : ℕ} (h : TerminatesBy A U T) :
    TerminatesBy (simulate A) U ((m + 1) * T) := by
  intro I hI hc p hp u hu
  obtain ⟨h1, h2⟩ := h I hI hc p hp u hu
  refine ⟨by rw [simulate_output]; exact h1, fun r hr => ?_⟩
  have hdecomp : r = (m + 1) * (r / (m + 1)) + r % (m + 1) := (Nat.div_add_mod r (m + 1)).symm
  have hk : r % (m + 1) ≤ m := Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos m))
  have hT : T ≤ r / (m + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos m)).2 (by
    rw [mul_comm]; exact hr)
  obtain ⟨ho, hs⟩ := h2 _ hT
  rw [hdecomp, run_simulate _ _ hk, simulate_output]
  refine ⟨ho, ?_⟩
  rw [sendCount_simulate]
  apply Nat.eq_zero_of_le_zero
  calc #{j ∈ {j | (A.send (run A p (r / (m + 1)) u) j).isSome} | j.val = r % (m + 1)}
      ≤ sendCount A (run A p (r / (m + 1)) u) := Finset.card_filter_le _ _
    _ = 0 := hs

/-- **Lemma 3.12** of [Kutten, Robinson, Tan, Zhu, PODC 2023]. For every (multicast) algorithm
`A` there is a single-send algorithm `S` that elects a leader in `n · T` rounds whenever `A`
elects a leader in `T` rounds (`n = m + 1`), and in every execution sends exactly as many
messages in its first `n · T` rounds as `A` sends in its first `T` rounds. -/
theorem lemma_3_12 (A : Algorithm m) : ∃ S : Algorithm m, SingleSend S ∧
    (∀ U T, ElectsBy A U T → ElectsBy S U ((m + 1) * T)) ∧
    (∀ U T, TerminatesBy A U T → TerminatesBy S U ((m + 1) * T)) ∧
    (∀ U T (M : ℝ), MsgBound A U T M → MsgBound S U ((m + 1) * T) M) ∧
    ∀ (p : PortMap m) T I, msgs S p ((m + 1) * T) I = msgs A p T I :=
  ⟨simulate A, simulate_singleSend A, fun _ _ => electsBy_simulate,
    fun _ _ => terminatesBy_simulate, fun _ _ _ => msgBound_simulate, msgs_simulate⟩

end LeaderTradeoffs
