import Papers.PODC2015.WeakestFDEventualConsistency.ECtoEIC

/-!
# Algorithm 6 does not satisfy the literal (uniform) EIC-Agreement

A run of Algorithm 6 (`Alg6.driver`) with two processes, `true` (faulty: crashes at time `3`) and
`false` (correct); each proposes its own name to every EIC instance.

* `0`: `true` starts and invokes `proposeEC_0([true])`;
* `1`: `false` starts and invokes `proposeEC_0([false])`;
* `2`: EC returns `[true]` to `true`, which decides `true` for EIC instance `0` (and invokes
  `proposeEC_1([true, true])`); then `true` crashes;
* `3 + 2j`: EC returns `false`'s own proposal `[false, …, false]` (length `j + 1`) to its
  instance `j`; `3 + 2j + 1`: `false` takes a time-out step.

The EC black box satisfies EC (agreement from instance `1` on: only `false` gets responses to
instances `≥ 1`) and the run is admissible, yet the faulty process's (last) decision for EIC
instance `0` is `true` while the correct one's is `false` forever: the processes "return
infinitely different values" to instance `0`, violating EIC-Agreement read literally ("no two
processes"). Hence Lemma 4 of [DGKPS15] holds only with agreement among correct processes
(`Alg6.lemma4`).
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace Alg6Counterexample

open Driver

/-- Each process proposes its own name. -/
def inp : Bool → ℕ → Bool := fun x _ => x

/-- The schedule. -/
def sched : ℕ → Option (Bool × Choice Bool (ℕ × List Bool))
  | 0 => some (true, .tick)
  | 1 => some (false, .tick)
  | 2 => some (true, .input (0, [true]))
  | t + 3 => if t % 2 = 0 then some (false, .input (t / 2, List.replicate (t / 2 + 1) false))
      else some (false, .tick)

/-- `true` crashes at time `3`. -/
def F : FailurePattern Bool where
  crashed t := if 3 ≤ t then {true} else ∅
  mono a b h := by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Set.empty_subset _
    · exact le_rfl

/-- The run. -/
def run : Run Bool Unit (ℕ × List Bool) := ⟨F, fun _ _ => (), sched⟩

/-- Algorithm 6 for this application. -/
abbrev D := Alg6.driver inp

lemma sched_input {t : ℕ} {x : Bool} {j : ℕ} {v : List Bool} :
    sched t = some (x, .input (j, v)) ↔
      (t = 2 ∧ x = true ∧ j = 0 ∧ v = [true]) ∨
      (t = 3 + 2 * j ∧ x = false ∧ v = List.replicate (j + 1) false) := by
  match t with
  | 0 => simp [sched]; intro h; omega
  | 1 => simp [sched]; intro h; omega
  | 2 =>
    simp only [sched, Option.some.injEq, Prod.mk.injEq, Choice.input.injEq, true_and]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; simp
    · rintro (⟨rfl, rfl, rfl⟩ | ⟨h, -⟩)
      · simp
      · omega
  | t + 3 =>
    simp only [sched]
    split_ifs with h
    · simp only [Option.some.injEq, Prod.mk.injEq, Choice.input.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; right; exact ⟨by omega, rfl, rfl⟩
      · rintro (⟨h1, -⟩ | ⟨h1, rfl, rfl⟩)
        · omega
        · have : t / 2 = j := by omega
          subst this; exact ⟨rfl, rfl, rfl⟩
    · simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, false_iff]
      omega

lemma sched_true {t : ℕ} {c : Choice Bool (ℕ × List Bool)} (h : sched t = some (true, c)) :
    t ≤ 2 := by
  match t with
  | 0 | 1 | 2 => omega
  | t + 3 => simp only [sched] at h; split_ifs at h <;> simp at h

/-- The states of the correct process `false`. -/
lemma st_false (t : ℕ) :
    (D.alg Unit).st run false t = (t / 2, List.replicate (t / 2 - 1) false) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    match t with
    | 0 => rw [(D.alg Unit).loc_succ_of_ne run 0 false (by simp [run, sched])]; exact ih
    | 1 =>
      rw [st_succ_start (Dr := D) (r := run) (show run.σ 1 = some (false, .tick) from rfl)
        (by simp only [n]; rw [ih])]
      simp only [dat]; rw [ih]
    | 2 => rw [(D.alg Unit).loc_succ_of_ne run 2 false (by simp [run, sched])]; exact ih
    | t + 3 =>
      rcases Nat.even_or_odd t with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have hσ : run.σ (j + j + 3) = some (false, .input (j, List.replicate (j + 1) false)) := by
          simp only [run, sched, show (j + j) % 2 = 0 by omega, show (j + j) / 2 = j by omega,
            ↓reduceIte]
        have hn : D.n run false (j + j + 3) = j + 1 := by
          simp only [n]; rw [ih]; omega
        rw [st_succ_input hσ hn]
        simp only [Prod.mk.injEq]; constructor
        · omega
        · show List.replicate (j + 1) false = _; congr 1; omega
      · have hσ : run.σ (2 * j + 1 + 3) = some (false, .tick) := by
          simp only [run, sched, show ¬ ((2 * j + 1) % 2 = 0) by omega, ↓reduceIte]
        have hn : D.n run false (2 * j + 1 + 3) = (j + 1) + 1 := by
          simp only [n]; rw [ih]; omega
        rw [st_succ_tick hσ hn, ih]
        simp only [Prod.mk.injEq]; constructor
        · omega
        · congr 1; omega

/-- The states of the faulty process `true`. -/
lemma st_true_ge (t : ℕ) : (D.alg Unit).st run true (t + 3) = (2, [true]) := by
  induction t with
  | zero =>
    have h0 : (D.alg Unit).st run true 0 = (0, []) := rfl
    have h1 : (D.alg Unit).st run true 1 = (1, []) := by
      rw [st_succ_start (Dr := D) (r := run) (show run.σ 0 = some (true, .tick) from rfl)
        (by simp only [n]; rw [h0])]
      simp only [dat]; rw [h0]
    have h2 : (D.alg Unit).st run true 2 = (1, []) := by
      rw [(D.alg Unit).loc_succ_of_ne run 1 true (by simp [run, sched])]; exact h1
    rw [st_succ_input (Dr := D) (r := run) (c := 0) (show run.σ 2 = some (true, .input (0, [true]))
      from rfl) (by simp only [n]; rw [h2])]
    rfl
  | succ t ih =>
    rw [(D.alg Unit).loc_succ_of_ne run (t + 3) true (fun c h => by
      have := sched_true (t := t + 3) (c := c) h; omega)]
    exact ih

lemma st_true_two : (D.alg Unit).st run true 2 = (1, []) := by
  have h0 : (D.alg Unit).st run true 0 = (0, []) := rfl
  have h1 : (D.alg Unit).st run true 1 = (1, []) := by
    rw [st_succ_start (Dr := D) (r := run) (show run.σ 0 = some (true, .tick) from rfl)
      (by simp only [n]; rw [h0])]
    simp only [dat]; rw [h0]
  rw [(D.alg Unit).loc_succ_of_ne run 1 true (by simp [run, sched])]; exact h1

lemma bb_inv_true : (D.bbHist run).inv true 0 [true] 0 := by
  refine out_bb_iff.2 ⟨rfl, ?_, ?_⟩
  · have := st_true_two
    have h : (D.alg Unit).st run true 1 = (1, []) := by
      rw [st_succ_start (Dr := D) (r := run) (show run.σ 0 = some (true, .tick) from rfl) rfl]; rfl
    simp only [n]; rw [h]
  · have h : (D.alg Unit).st run true 1 = (1, []) := by
      rw [st_succ_start (Dr := D) (r := run) (show run.σ 0 = some (true, .tick) from rfl) rfl]; rfl
    simp only [dat]; rw [h]; rfl

lemma bb_inv_false (j : ℕ) :
    (D.bbHist run).inv false j (List.replicate (j + 1) false) (2 * j + 1) := by
  refine out_bb_iff.2 ⟨?_, ?_, ?_⟩
  · simp only [n]; rw [st_false]; omega
  · simp only [n]; rw [st_false]; omega
  · simp only [dat]; rw [st_false]
    show _ = List.replicate _ false ++ [false]
    rw [show (2 * j + 1 + 1) / 2 - 1 = j by omega, List.replicate_succ']

lemma resp_iff {x : Bool} {j : ℕ} {v : List Bool} {t : ℕ} :
    (D.bbHist run).resp x j v t ↔
      (t = 2 ∧ x = true ∧ j = 0 ∧ v = [true]) ∨
      (t = 3 + 2 * j ∧ x = false ∧ v = List.replicate (j + 1) false) := sched_input

/-- The EC black box of the run satisfies EC (agreement from instance `1` on). -/
theorem ec : EC run.F (D.bbHist run) := by
  refine ⟨?_, ?_, ?_, 1, ?_⟩
  · intro x hx j
    have : x = false := by
      by_contra h; simp only [Bool.not_eq_false] at h; subst h
      exact hx 3 (by simp [run, F])
    subst this
    exact ⟨_, _, resp_iff.2 (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  · intro x j v v' t t' h h'
    rcases resp_iff.1 h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      rcases resp_iff.1 h' with ⟨h1, h2, h3, rfl⟩ | ⟨rfl, h2, rfl⟩ <;> simp_all
  · intro x j v t h
    rcases resp_iff.1 h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨true, 0, by omega, bb_inv_true⟩
    · exact ⟨false, _, by omega, bb_inv_false j⟩
  · intro j hj x y v v' t t' h h'
    rcases resp_iff.1 h with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩
    · omega
    rcases resp_iff.1 h' with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl⟩
    · omega
    rfl

lemma respAfterInv : (D.bbHist run).RespAfterInv := by
  intro x j v t h
  rcases resp_iff.1 h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨_, 0, by omega, bb_inv_true⟩
  · exact ⟨_, _, by omega, bb_inv_false j⟩

lemma admissible : (D.alg Unit).Admissible run where
  alive t x c h := by
    cases x
    · simp [run, F]
    · have := sched_true (t := t) (c := c) h; simp [run, F]; omega
  recv_valid t x q s h := by
    exfalso
    match t with
    | 0 | 1 | 2 => simp [run, sched] at h
    | t + 3 => simp only [run, sched] at h; split_ifs at h <;> simp at h
  recv_once t t' x q s h := by
    exfalso
    match t with
    | 0 | 1 | 2 => simp [run, sched] at h
    | t + 3 => simp only [run, sched] at h; split_ifs at h <;> simp at h
  ticks x hx T := by
    have : x = false := by
      by_contra h; simp only [Bool.not_eq_false] at h; subst h
      exact hx 3 (by simp [run, F])
    subst this
    refine ⟨2 * T + 1 + 3, by omega, ?_⟩
    simp only [run, sched, show ¬ ((2 * T + 1) % 2 = 0) by omega, ↓reduceIte]
  delivery x _ t s q m _ := m.elim

/-- The faulty process `true` decided `true` for EIC instance `0` (at time `2`) and never again. -/
lemma current_true (t : ℕ) (ht : 3 ≤ t) : (D.appHist run).Current true 0 true t := by
  refine ⟨2, by omega, ?_, fun t₁ v₁ h₁ _ hr => ?_⟩
  · refine Alg6.app_resp_iff.2 ⟨0, [true], ?_, rfl, le_rfl, rfl, ?_⟩
    · simp only [n]; rw [st_true_two]
    · simp only [dat]; rw [st_true_two]; simp
  · obtain ⟨c, x, -, hσ, -⟩ := Alg6.app_resp_iff.1 hr
    have := sched_true (t := t₁) hσ; omega

/-- The correct process `false` decided `false` for EIC instance `0` (at time `3`) and never
again. -/
lemma current_false (t : ℕ) (ht : 4 ≤ t) : (D.appHist run).Current false 0 false t := by
  refine ⟨3, by omega, ?_, fun t₁ v₁ h₁ _ hr => ?_⟩
  · refine Alg6.app_resp_iff.2 ⟨0, [false], ?_, rfl, le_rfl, rfl, ?_⟩
    · simp only [n]; rw [st_false]
    · simp only [dat]; rw [st_false]; simp
  · obtain ⟨c, x, -, hσ, -, hx, hd⟩ := Alg6.app_resp_iff.1 hr
    rcases sched_input.1 hσ with ⟨h, -⟩ | ⟨rfl, -, rfl⟩
    · omega
    · have hc : 1 ≤ c := by omega
      apply hd
      simp only [dat]; rw [st_false]
      simp only [List.getElem?_replicate, show 0 < c + 1 by omega, show 0 < (3 + 2 * c) / 2 - 1 by omega,
        ↓reduceIte] at hx ⊢
      exact hx

/-- **The literal reading of Lemma 4 of [DGKPS15] fails for Algorithm 6**: there is an
admissible run of Algorithm 6 whose EC black box responds only to invoked instances and satisfies
EC, but in which a faulty and a correct process return infinitely different values to EIC
instance `0`, violating EIC-Agreement read as "no two processes". (Agreement among correct
processes holds, `Alg6.lemma4`.) -/
theorem not_EICAgreement :
    ∃ r : Run Bool Unit (ℕ × List Bool), (D.alg Unit).Admissible r ∧
      (D.bbHist r).RespAfterInv ∧ EC r.F (D.bbHist r) ∧ ¬ EICAgreement (D.appHist r) :=
  ⟨run, admissible, respAfterInv, ec, fun h => h true false 0 fun T =>
    ⟨max T 4, le_max_left _ _, true, false, by decide,
      current_true _ (by omega), current_false _ (by omega)⟩⟩

end Alg6Counterexample

end Podc.WeakestFDEventualConsistency
