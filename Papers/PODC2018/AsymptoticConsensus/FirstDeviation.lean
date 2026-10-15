import Papers.PODC2018.AsymptoticConsensus.LowerBounds

/-!
# The "first deviation parity" algorithm (counterexample to Theorem 4 (⇐) of FNS'18)

For two agents in the network model `{H0, H1, H2}` we define an asymptotic consensus algorithm
`fd` whose limits are always initial values (`fd_limit`), although exact consensus is not
solvable in this model.

**Algorithm.** Each agent stores its own initial value, the initial values it knows, a round
counter and a decision variable `dec` (initially `none`). In round `t` (1-indexed), agent `i`
* keeps `dec` if it is already set;
* otherwise, if `i` does not hear the other agent `o` in round `t`, sets
  `dec := if t odd then x_i else x_o`;
* otherwise copies the decision variable of `o` (possibly `none`).

The output is `dec` if set, and agent `0`'s initial value (once known) otherwise.

**Why it works.** If every round is `H0`, no decision is ever taken and both outputs equal
`x 0` from time `1` on. Otherwise let `T + 1` be the first round in which some agent `k` is deaf
and `D := if T + 1 odd then x_k else x_o`. In round `T + 1`, `k` decides `D` and `o` copies
`none`; in round `T + 2`, `o` either is deaf and decides by parity of `T + 2` (which gives `D`
again) or copies `D` from `k`. Decisions never change afterwards.

## Main results

* `fd`: the algorithm.
* `fd_eventually_const`: in every execution, both outputs are eventually equal to `x 0` or `x 1`.
* `fd_solves`: `fd` solves asymptotic consensus in `{H0, H1, H2}`.
* `fd_limit`: every limit of `fd` is an initial value.
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Filter Topology Set

variable {V : Type*}

/-- The other agent among two agents. -/
def oth (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem oth_zero : oth 0 = 1 := rfl
@[simp] theorem oth_one : oth 1 = 0 := rfl
@[simp] theorem oth_oth (i : Fin 2) : oth (oth i) = i := by fin_cases i <;> rfl

theorem eq_oth_of_ne {i j : Fin 2} (h : j ≠ i) : j = oth i := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- Local state of the first-deviation-parity algorithm. -/
structure FDState (V : Type*) where
  /-- The agent's own initial value. -/
  own : V
  /-- The initial values known to the agent (`none` = unknown). -/
  known : Fin 2 → Option V
  /-- Number of completed rounds. -/
  round : ℕ
  /-- The decision variable. -/
  dec : Option V

/-- One round of agent `i` in state `s`, receiving `mo` from the other agent (`none` if it did
not hear it). -/
def FDState.upd (i : Fin 2) (s : FDState V) (mo : Option (FDState V)) : FDState V where
  own := s.own
  known := fun j => if j = i then some s.own else
    match mo with
    | some so => some so.own
    | none => s.known j
  round := s.round + 1
  dec := match s.dec with
    | some v => some v
    | none => match mo with
      | none => some (if (s.round + 1) % 2 = 1 then s.own else (s.known (oth i)).getD s.own)
      | some so => so.dec

/-- The transition function of the first-deviation-parity algorithm. -/
def fdStep [Zero V] : StepFn (Fin 2) (FDState V) := fun i m =>
  match m i with
  | some s => s.upd i (m (oth i))
  | none => ⟨0, fun _ => none, 0, none⟩

/-- The **first-deviation-parity** algorithm for two agents. -/
def fd [Zero V] : Alg (Fin 2) (FDState V) V where
  init i v := ⟨v, fun j => if j = i then some v else none, 0, none⟩
  step := fdStep
  out s := s.dec.getD ((s.known 0).getD s.own)

namespace FD

/-! ### Basic lemmas -/

@[simp] theorem upd_own (i : Fin 2) (s : FDState V) (mo) : (s.upd i mo).own = s.own := rfl
@[simp] theorem upd_round (i : Fin 2) (s : FDState V) (mo) :
    (s.upd i mo).round = s.round + 1 := rfl

theorem upd_known_self (i : Fin 2) (s : FDState V) (mo) : (s.upd i mo).known i = some s.own := by
  simp [FDState.upd]

theorem upd_known_heard (i : Fin 2) (s so : FDState V) :
    (s.upd i (some so)).known (oth i) = some so.own := by
  fin_cases i <;> simp [FDState.upd]

theorem upd_dec_some (i : Fin 2) (s : FDState V) (mo) {v : V} (h : s.dec = some v) :
    (s.upd i mo).dec = some v := by
  simp [FDState.upd, h]

theorem upd_dec_heard (i : Fin 2) (s so : FDState V) (h : s.dec = none) :
    (s.upd i (some so)).dec = so.dec := by
  simp [FDState.upd, h]

theorem upd_dec_deaf (i : Fin 2) (s : FDState V) (h : s.dec = none) :
    (s.upd i none).dec =
      some (if (s.round + 1) % 2 = 1 then s.own else (s.known (oth i)).getD s.own) := by
  simp [FDState.upd, h]

theorem msgs_of_hears {σ : Type*} {G : Graph (Fin 2)} {C : Fin 2 → σ} {i j : Fin 2}
    (h : Hears G i j) : msgs G C i j = some (C j) := by
  simp [msgs, h]

theorem msgs_of_not_hears {σ : Type*} {G : Graph (Fin 2)} {C : Fin 2 → σ} {i j : Fin 2}
    (h : ¬ Hears G i j) : msgs G C i j = none := by
  simp [msgs, h]

theorem hears_H0 (i : Fin 2) : Hears H0 i (oth i) := by
  fin_cases i <;> simp [Hears, H0]

/-- In a deviating round of `{H0, H1, H2}` some agent `k` is deaf while the other hears `k`. -/
theorem exists_deaf {G : Graph (Fin 2)} (hG : G ∈ ({H0, H1, H2} : Set (Graph (Fin 2))))
    (h : G ≠ H0) : ∃ k, ¬ Hears G k (oth k) ∧ Hears G (oth k) k := by
  rcases hG with rfl | rfl | rfl
  · exact absurd rfl h
  · exact ⟨0, by simp [Hears, H1]⟩
  · exact ⟨1, by simp [Hears, H2]⟩

section run

variable [Zero V]

/-- The run of `fd` with initial values `x` and pattern `p`. -/
noncomputable def run (x : Fin 2 → V) (p : ℕ → Graph (Fin 2)) : ℕ → Fin 2 → FDState V :=
  conf fd.step (fd.initC x) p

theorem run_succ (x : Fin 2 → V) (p : ℕ → Graph (Fin 2)) (t : ℕ) (i : Fin 2) :
    run x p (t + 1) i = (run x p t i).upd i (msgs (p t) (run x p t) i (oth i)) := by
  change fdStep i (msgs (p t) (run x p t) i) = _
  simp [fdStep, msgs_of_hears (hears_self (p t) i)]

theorem run_own_round (x : Fin 2 → V) (p : ℕ → Graph (Fin 2)) :
    ∀ t i, (run x p t i).own = x i ∧ (run x p t i).round = t := by
  intro t
  induction t with
  | zero => intro i; exact ⟨rfl, rfl⟩
  | succ t ih => intro i; rw [run_succ]; exact ⟨(ih i).1, by simp [(ih i).2]⟩

theorem run_dec_none (x : Fin 2 → V) {p : ℕ → Graph (Fin 2)} {T : ℕ}
    (hlt : ∀ t < T, p t = H0) : ∀ t ≤ T, ∀ i, (run x p t i).dec = none := by
  intro t
  induction t with
  | zero => intro _ i; rfl
  | succ t ih =>
    intro ht i
    rw [run_succ, hlt t (by omega), msgs_of_hears (hears_H0 i),
      upd_dec_heard _ _ _ (ih (by omega) i)]
    exact ih (by omega) _

theorem run_known_H0 (x : Fin 2 → V) {p : ℕ → Graph (Fin 2)} {t : ℕ} (h : p t = H0)
    (i j : Fin 2) : (run x p (t + 1) i).known j = some (x j) := by
  rw [run_succ, h, msgs_of_hears (hears_H0 i)]
  by_cases hj : j = i
  · subst hj; rw [upd_known_self, (run_own_round x p t j).1]
  · rw [eq_oth_of_ne hj, upd_known_heard, (run_own_round x p t _).1]

/-! ### Main results -/

/-- In every execution of `fd` in `{H0, H1, H2}`, the outputs of both agents are eventually
constant, equal to one of the initial values. -/
theorem fd_eventually_const (x : Fin 2 → V) {p : ℕ → Graph (Fin 2)}
    (hp : p ∈ Pat ({H0, H1, H2} : Set (Graph (Fin 2)))) :
    ∃ z, (z = x 0 ∨ z = x 1) ∧ ∃ t₀, ∀ t ≥ t₀, ∀ i, fd.out (run x p t i) = z := by
  by_cases hdev : ∃ t, p t ≠ H0
  · classical
    obtain ⟨T, hT, hlt⟩ : ∃ T, p T ≠ H0 ∧ ∀ t < T, p t = H0 :=
      ⟨Nat.find hdev, Nat.find_spec hdev, fun t ht => not_not.1 (Nat.find_min hdev ht)⟩
    obtain ⟨k, hk1, hk2⟩ := exists_deaf (hp T) hT
    have hnone := run_dec_none x hlt
    set D := if (T + 1) % 2 = 1 then x k else x (oth k) with hD
    -- round `T + 1`: agent `k` is deaf and decides `D`
    have hk : (run x p (T + 1) k).dec = some D := by
      rw [run_succ, msgs_of_not_hears hk1, upd_dec_deaf _ _ (hnone T le_rfl k),
        (run_own_round x p T k).1, (run_own_round x p T k).2, hD]
      rcases Nat.eq_zero_or_pos T with h0 | hpos
      · simp [h0]
      · obtain ⟨s, hs⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
        have hkn : (run x p T k).known (oth k) = some (x (oth k)) := by
          rw [hs]; exact run_known_H0 x (hlt s (by omega)) k (oth k)
        rw [hkn]; rfl
    -- round `T + 1`: agent `oth k` hears `k`, copies `none` and learns `x k`
    have ho : (run x p (T + 1) (oth k)).dec = none ∧
        (run x p (T + 1) (oth k)).known k = some (x k) := by
      rw [run_succ, oth_oth, msgs_of_hears hk2]
      refine ⟨?_, ?_⟩
      · rw [upd_dec_heard _ _ _ (hnone T le_rfl _)]; exact hnone T le_rfl _
      · have := upd_known_heard (oth k) (run x p T (oth k)) (run x p T (oth (oth k)))
        simp only [oth_oth] at this
        rw [this, (run_own_round x p T k).1]
    -- round `T + 2`: both agents have decided `D`
    have h2 : ∀ i, (run x p (T + 2) i).dec = some D := by
      intro i
      by_cases hi : i = k
      · subst hi; rw [run_succ]; exact upd_dec_some _ _ _ hk
      · obtain rfl := eq_oth_of_ne hi
        rw [run_succ]
        by_cases hh : Hears (p (T + 1)) (oth k) (oth (oth k))
        · rw [msgs_of_hears hh, upd_dec_heard _ _ _ ho.1]; simpa using hk
        · rw [msgs_of_not_hears hh, upd_dec_deaf _ _ ho.1, oth_oth, ho.2,
            (run_own_round x p _ _).1, (run_own_round x p _ _).2, hD]
          simp only [Option.getD_some, Option.some.injEq]
          split_ifs <;> first | rfl | omega
    -- decisions never change
    have hstay : ∀ s i, (run x p (T + 2 + s) i).dec = some D := by
      intro s
      induction s with
      | zero => exact h2
      | succ s ih => intro i; rw [← add_assoc, run_succ]; exact upd_dec_some _ _ _ (ih i)
    refine ⟨D, ?_, T + 2, fun t ht i => ?_⟩
    · rw [hD]; split_ifs <;> fin_cases k <;> simp
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      simp [fd, hstay s i]
  · push Not at hdev
    refine ⟨x 0, Or.inl rfl, 1, fun t ht i => ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hn := run_dec_none x (T := s + 1) (fun t _ => hdev t) (s + 1) le_rfl i
    simp [fd, hn, run_known_H0 x (hdev s)]

end run

variable [NormedAddCommGroup V]

/-- Every execution of `fd` in `{H0, H1, H2}` has a limit, which is `x 0` or `x 1`. -/
theorem fd_exists_limit (x : Fin 2 → V) {p : ℕ → Graph (Fin 2)}
    (hp : p ∈ Pat ({H0, H1, H2} : Set (Graph (Fin 2)))) :
    ∃ z, (z = x 0 ∨ z = x 1) ∧ fd.HasLimit (fd.initC x) p z := by
  obtain ⟨z, hz, t₀, h⟩ := fd_eventually_const x hp
  exact ⟨z, hz, fun i => tendsto_atTop_of_eventually_const fun t ht => h t ht i⟩

end FD

open FD

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The first-deviation-parity algorithm solves asymptotic consensus in `{H0, H1, H2}`. -/
theorem fd_solves : (fd (V := V)).Solves ({H0, H1, H2} : Set (Graph (Fin 2))) := by
  intro x p hp
  obtain ⟨z, hz, hlim⟩ := fd_exists_limit x hp
  refine ⟨z, subset_convexHull ℝ _ ?_, hlim⟩
  rcases hz with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Every limit of the first-deviation-parity algorithm in `{H0, H1, H2}` is an initial
value: the limit is `x 0` or `x 1`. -/
theorem fd_limit (x : Fin 2 → V) (p : ℕ → Graph (Fin 2))
    (hp : p ∈ Pat ({H0, H1, H2} : Set (Graph (Fin 2)))) (z : V)
    (h : fd.HasLimit (fd.initC x) p z) : z = x 0 ∨ z = x 1 := by
  obtain ⟨z', hz', hlim⟩ := fd_exists_limit x hp
  rw [h.unique hlim]
  exact hz'

end AsymptoticConsensus
