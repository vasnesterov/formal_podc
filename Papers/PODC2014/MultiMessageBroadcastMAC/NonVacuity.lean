import Papers.PODC2014.MultiMessageBroadcastMAC.Restricted
import Papers.PODC2014.MultiMessageBroadcastMAC.Correctness

/-!
# Non-vacuity: executions satisfying all hypotheses

* `ackBound_of_quiescent`, `progBound_of_quiescent`: an execution whose first `N` events happen at
  time `0` and after which no node broadcasts satisfies the acknowledgment and progress bounds.
* `example3`: a concrete execution on the path `0 — 1 — 2` with an unreliable link `0 ⋯ 2`
  (2-restricted): `m` arrives at `0`, node `2` first receives it over the unreliable link, every
  node broadcasts and acknowledges it. It satisfies every hypothesis of Theorems 3.1, 3.2 and 3.4.
-/

namespace Podc.MultiMessageBroadcastMAC

open Filter

variable {V M : Type*}

namespace Exec

variable [DecidableEq V] [DecidableEq M] {G G' : SimpleGraph V} {α : Exec G G' M}

open Config

omit [DecidableEq V] [DecidableEq M] in
variable (α) in
lemma T_nonneg (n : ℕ) : 0 ≤ α.T n := α.T_zero ▸ α.T_mono (Nat.zero_le n)

omit [DecidableEq M] in
theorem ackBound_of_quiescent {N : ℕ} (hN : ∀ n ≥ N, ∀ i, ¬ (α.cfg n).Busy i) (hT : α.T N = 0)
    {Fack : ℝ} (hF : 0 ≤ Fack) : α.AckBound Fack := by
  intro i n hf
  have hnN : n < N := by
    by_contra h
    exact hN n (not_lt.1 h) i hf.1
  refine ⟨N, by rw [hT]; linarith [α.T_nonneg n], ?_⟩
  have h1 := hf.1
  have h2 := hN N le_rfl i
  have h3 := ((α.mono hnN.le).log_prefix i).length_le
  unfold Busy at h1 h2
  omega

omit [DecidableEq M] in
theorem progBound_of_quiescent {N : ℕ} (hN : ∀ n ≥ N, ∀ i, ¬ (α.cfg n).Busy i) (hT : α.T N = 0)
    {Fprog : ℝ} (hFp : 0 ≤ Fprog) : α.ProgBound Fprog := by
  rintro t t' j ht htt' ⟨⟨i, m⟩, -, hs, hna⟩
  have hNa : N ≤ α.last t := α.le_last (by rw [hT]; exact ht)
  have hab : α.last t ≤ α.last t' := α.last_monotone (by linarith)
  refine absurd (α.acked_mono hab ?_) hna
  have h1 := hN _ hNa i
  have h2 := (α.inv (α.last t)).acks_le i
  unfold Busy at h1
  unfold Started at hs
  unfold Acked
  dsimp only at hs ⊢
  rw [List.take_of_length_le (by omega)] at hs ⊢
  exact hs

end Exec

namespace Example

/-- The events of `example3`. -/
def evs : List (Event (Fin 3) Unit) :=
  [.arrive 0 (), .rcv 0 2, .rcv 0 1, .ack 0, .rcv 1 0, .rcv 1 2, .ack 1, .rcv 2 1, .ack 2]

/-- Times of `example3`: the first nine events at time `0`, then one skip per time unit. -/
noncomputable def times (n : ℕ) : ℝ := max 0 ((n : ℝ) - 9)

/-- The concrete execution: `G` is the path `0 — 1 — 2`, `G' = ⊤` adds the unreliable link
`0 ⋯ 2`; `m = ()` arrives at `0`; node `2` gets it first over the unreliable link. -/
noncomputable def example3 : Exec (SimpleGraph.pathGraph 3) (⊤ : SimpleGraph (Fin 3)) Unit where
  ev n := evs.getD n .skip
  T := times
  T_zero := by simp [times]
  T_mono := fun a b h => max_le_max le_rfl (by simp only [sub_le_sub_iff_right]; exact_mod_cast h)
  T_tendsto := by
    refine tendsto_atTop_mono (fun n => le_max_right _ _) ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- The configurations of `example3` (computed by hand). -/
def cfgs : ℕ → Config (Fin 3) Unit
  | 0 => ⟨![[], [], []], ![0, 0, 0], ![∅, ∅, ∅]⟩
  | 1 => ⟨![[()], [], []], ![0, 0, 0], ![∅, ∅, ∅]⟩
  | 2 => ⟨![[()], [], [()]], ![0, 0, 0], ![∅, ∅, {(0, ())}]⟩
  | 3 => ⟨![[()], [()], [()]], ![0, 0, 0], ![∅, {(0, ())}, {(0, ())}]⟩
  | 4 => ⟨![[()], [()], [()]], ![1, 0, 0], ![∅, {(0, ())}, {(0, ())}]⟩
  | 5 => ⟨![[()], [()], [()]], ![1, 0, 0], ![{(1, ())}, {(0, ())}, {(0, ())}]⟩
  | 6 => ⟨![[()], [()], [()]], ![1, 0, 0], ![{(1, ())}, {(0, ())}, {(1, ()), (0, ())}]⟩
  | 7 => ⟨![[()], [()], [()]], ![1, 1, 0], ![{(1, ())}, {(0, ())}, {(1, ()), (0, ())}]⟩
  | 8 => ⟨![[()], [()], [()]], ![1, 1, 0], ![{(1, ())}, {(2, ()), (0, ())}, {(1, ()), (0, ())}]⟩
  | _ => ⟨![[()], [()], [()]], ![1, 1, 1], ![{(1, ())}, {(2, ()), (0, ())}, {(1, ()), (0, ())}]⟩

lemma steps (k : ℕ) (hk : k < 9) :
    step (SimpleGraph.pathGraph 3) ⊤ (cfgs k) (evs.getD k .skip) = cfgs (k + 1) := by
  interval_cases k
  all_goals ext i
  all_goals fin_cases i
  all_goals simp [step, cfgs, evs, Config.head, SimpleGraph.pathGraph_adj, Fin.forall_fin_succ]

lemma cfg_eq (n : ℕ) (hn : n ≤ 9) : example3.cfg n = cfgs n := by
  induction n with
  | zero =>
    ext i
    all_goals fin_cases i
    all_goals simp [cfgs]
  | succ n ih =>
    rw [Exec.cfg_succ, ih (by omega)]
    exact steps n (by omega)

lemma cfg_eq_nine (n : ℕ) (hn : 9 ≤ n) : example3.cfg n = cfgs 9 := by
  induction n, hn using Nat.le_induction with
  | base => exact cfg_eq 9 le_rfl
  | succ n hn ih =>
    rw [Exec.cfg_succ, ih]
    have : evs.getD n .skip = .skip := List.getD_eq_default _ _ (by simp [evs]; omega)
    simp only [example3, this, step]

lemma quiescent : ∀ n ≥ 9, ∀ i, ¬ (example3.cfg n).Busy i := by
  intro n hn i
  rw [cfg_eq_nine n hn]
  fin_cases i <;> simp [Config.Busy, cfgs]

lemma T_nine : example3.T 9 = 0 := by simp [example3, times]

lemma ackBound {Fack : ℝ} (hF : 0 ≤ Fack) : example3.AckBound Fack :=
  Exec.ackBound_of_quiescent quiescent T_nine hF

lemma progBound {Fprog : ℝ} (hF : 0 ≤ Fprog) : example3.ProgBound Fprog :=
  Exec.progBound_of_quiescent quiescent T_nine hF

lemma arrivalsAtZero : example3.ArrivalsAtZero := by
  intro n i m h
  have hn : n < 9 := by
    by_contra hn
    have : evs.getD n .skip = .skip := List.getD_eq_default _ _ (by simp [evs]; omega)
    simp only [example3, this] at h
    cases h
  show times (n + 1) = 0
  unfold times
  have : ((n + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast hn
  exact max_eq_left (by linarith)

lemma arrives : example3.Arrives 0 () := ⟨0, rfl⟩

lemma rRestricted : RRestricted (SimpleGraph.pathGraph 3) ⊤ 2 := by
  have h01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]
  have h12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by simp [SimpleGraph.pathGraph_adj]
  have e01 := SimpleGraph.edist_eq_one_iff_adj.2 h01
  have e12 := SimpleGraph.edist_eq_one_iff_adj.2 h12
  have e10 := SimpleGraph.edist_eq_one_iff_adj.2 h01.symm
  have e21 := SimpleGraph.edist_eq_one_iff_adj.2 h12.symm
  have e02 : (SimpleGraph.pathGraph 3).edist 0 2 ≤ (2 : ℕ) :=
    SimpleGraph.edist_le_natCast_add (m := 1) (n := 1) (by rw [e01]; rfl) (by rw [e12]; rfl)
  have e20 : (SimpleGraph.pathGraph 3).edist 2 0 ≤ (2 : ℕ) := by
    rw [SimpleGraph.edist_comm]; exact e02
  have hadj : ∀ u v, (SimpleGraph.pathGraph 3).Adj u v →
      (SimpleGraph.pathGraph 3).edist u v ≤ (2 : ℕ) := fun u v h => by
    rw [SimpleGraph.edist_eq_one_iff_adj.2 h]; norm_num
  intro u v huv
  have : u ≠ v := huv.ne
  fin_cases u <;> fin_cases v
  all_goals first | exact absurd rfl this | exact e02 | exact e20 |
    exact hadj _ _ (by simp [SimpleGraph.pathGraph_adj])

/-- All hypotheses of Theorems 3.1, 3.2 (with `r = 2`), 3.4 and 3.16 hold in `example3`, for all
`F_ack, F_prog ≥ 0`, and its conclusion is the delivery of `m` everywhere. -/
theorem example3_nonvacuous {Fack Fprog : ℝ} (hFa : 0 ≤ Fack) (hFp : 0 ≤ Fprog) :
    SimpleGraph.pathGraph 3 ≤ ⊤ ∧ RRestricted (SimpleGraph.pathGraph 3) ⊤ 2 ∧
      example3.AckBound Fack ∧ example3.ProgBound Fprog ∧ example3.ArrivalsAtZero ∧
      example3.Arrives 0 () ∧ example3.SolvesMMB ∧
      () ∈ example3.R 2 (2 * Fprog + 3 * 2 * 1 * Fack) := by
  refine ⟨le_top, rRestricted, ackBound hFa, progBound hFp, arrivalsAtZero, arrives,
    Exec.theorem_3_4 (ackBound hFa), ?_⟩
  have h01 : (SimpleGraph.pathGraph 3).Adj 0 1 := by simp [SimpleGraph.pathGraph_adj]
  have h12 : (SimpleGraph.pathGraph 3).Adj 1 2 := by simp [SimpleGraph.pathGraph_adj]
  have := Exec.theorem_3_2 (D := 2) (k := 1) (K := {()}) (i₀ := 0) (j := 2) (α := example3)
    le_top (by norm_num) rRestricted (ackBound hFa) (progBound hFp) hFp hFa arrivalsAtZero
    (fun _ _ _ => Finset.mem_singleton_self _) (by simp) arrives
    (h01.reachable.trans h12.reachable) ?_
  · exact_mod_cast this
  · refine SimpleGraph.dist_le_of_edist_le_natCast (n := 2) ?_
    exact SimpleGraph.edist_le_natCast_add (m := 1) (n := 1)
      (by rw [SimpleGraph.edist_eq_one_iff_adj.2 h01]; rfl)
      (by rw [SimpleGraph.edist_eq_one_iff_adj.2 h12]; rfl)

end Example

end Podc.MultiMessageBroadcastMAC
