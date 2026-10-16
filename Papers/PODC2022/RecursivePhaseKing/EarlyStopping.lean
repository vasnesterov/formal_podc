import Papers.PODC2022.RecursivePhaseKing.Subroutines
import Cslib.Computability.Distributed.Byzantine.PartialSync.Rounds

/-!
# Algorithm 1: the early-stopping Phase King protocol (Theorem 2.9)

Algorithm 1 of [LS22] with the weak validator and the termination check implemented by
Algorithm 2 and electors' broadcast by the king's broadcast (Algorithm 3), as one round algorithm
of CSLib's synchronous round model (`RoundAlgorithm`, executions `RoundRun` with `SyncFrom 0`:
messages between correct nodes are delivered, messages from faulty nodes are arbitrary).

One loop iteration `k` (0-based; the king is `king k`) takes the six rounds `6k, …, 6k + 5`:

| round `6k + i` | `i = 0` | `1` | `2` | `3` | `4` | `5` |
|---|---|---|---|---|---|---|
| subroutine | validator, bcast 1 | validator, bcast 2 | king's bcast | termcheck, bcast 1 | termcheck, bcast 2 | termination bcast |

Convention (3) of [LS22] ("if `i ∈ V_g` terminates with output `b` and communicates this to other
nodes, they will assume that `i` sends `b` in all future rounds") is implemented explicitly: every
node records the senders of termination broadcasts (`done`) and substitutes the recorded value for
their messages from then on (`eff`). A terminated node *halts*: it sends nothing afterwards.

Main results (`n = |P|`, `3t < n`, at most `t` faulty nodes, `f = |F|` the actual number of faulty
nodes; the kings of the first `t + 1` iterations are distinct):
* `theorem_2_9_validity`, `theorem_2_9_agreement` (binary consensus, Definition 2.1);
* `theorem_2_9_termination`: every correct node has decided and halted after `6 (f + 1)` rounds;
* `theorem_2_9_messages`: correct nodes send at most `6 n² (f + 1)` single-bit messages in total.
-/

set_option linter.unusedSectionVars false

namespace RecursivePhaseKing

open Finset Cslib.Byzantine.PartialSync

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Local state of a node running Algorithm 1. -/
structure St (P : Type*) where
  /-- The opinion `op_i`. -/
  op : Bool
  /-- The bit `strong_i` returned by the last validator call. -/
  strong : Bool
  /-- The second-round message of the current instance of Algorithm 2 (line 4), if any. -/
  snd : Option Bool
  /-- The output (set when `term_i = 1`). -/
  out : Option Bool
  /-- Whether the node has returned (after its termination broadcast). -/
  halted : Bool
  /-- `done q = some b`: `q` made a termination broadcast with value `b`. -/
  done : P → Option Bool

/-- Effective receptions (convention (3)): a sender recorded as terminated with value `b` is
assumed to send `b`. -/
def eff (s : St P) (rcv : P → Option Bool) : P → Option Bool := fun q => (s.done q).or (rcv q)

variable (t : ℕ) (king : ℕ → P) (tb : ℕ → P → St P → (P → Option Bool) → Bool)

/-- Algorithm 1 of [LS22] with Algorithms 2 and 3 as subroutines, as a round algorithm. Round `r`
is round `r % 6` of iteration `r / 6`, whose king is `king (r / 6)`. `tb` resolves the arbitrary
choices of convention (4) (line 6 of Algorithm 2 when both values qualify). -/
def alg1 : RoundAlgorithm P Bool (St P) Bool Bool where
  init _ b := ⟨b, false, none, none, false, fun _ => none⟩
  send r p s _ :=
    if s.halted then none
    else if r % 6 = 0 then some s.op
    else if r % 6 = 1 then s.snd
    else if r % 6 = 2 then (if p = king (r / 6) then some s.op else none)
    else if r % 6 = 3 then some s.op
    else if r % 6 = 4 then s.snd
    else s.out
  trans r p s rcv :=
    if s.halted then s
    else if r % 6 = 0 then { s with snd := vote (Fintype.card P - t) (eff s rcv) }
    else if r % 6 = 1 then
      { s with op := adopt t (tb r p s rcv) s.op (eff s rcv), strong := strongOf t (eff s rcv) }
    else if r % 6 = 2 then { s with op := kingOut s.op s.strong (eff s rcv (king (r / 6))) }
    else if r % 6 = 3 then { s with snd := vote (Fintype.card P - t) (eff s rcv) }
    else if r % 6 = 4 then
      { s with op := adopt t (tb r p s rcv) s.op (eff s rcv),
               out := if strongOf t (eff s rcv) then
                 some (adopt t (tb r p s rcv) s.op (eff s rcv)) else none }
    else { s with halted := s.out.isSome, done := fun q => (s.done q).or (rcv q) }
  decide _ s := s.out

variable {t king tb}

/-! ### One-step equations -/

section Steps

variable {r : ℕ} {p q : P} {s : St P} {rcv : P → Option Bool}

theorem trans_halted (h : s.halted = true) : (alg1 t king tb).trans r p s rcv = s := by
  simp [alg1, h]

theorem send_halted (h : s.halted = true) : (alg1 t king tb).send r p s q = none := by
  simp [alg1, h]

theorem trans_0 (h : s.halted = false) (hr : r % 6 = 0) : (alg1 t king tb).trans r p s rcv =
    { s with snd := vote (Fintype.card P - t) (eff s rcv) } := by
  simp [alg1, h, hr]

theorem trans_1 (h : s.halted = false) (hr : r % 6 = 1) : (alg1 t king tb).trans r p s rcv =
    { s with op := adopt t (tb r p s rcv) s.op (eff s rcv), strong := strongOf t (eff s rcv) } := by
  simp [alg1, h, hr]

theorem trans_2 (h : s.halted = false) (hr : r % 6 = 2) : (alg1 t king tb).trans r p s rcv =
    { s with op := kingOut s.op s.strong (eff s rcv (king (r / 6))) } := by
  simp [alg1, h, hr]

theorem trans_3 (h : s.halted = false) (hr : r % 6 = 3) : (alg1 t king tb).trans r p s rcv =
    { s with snd := vote (Fintype.card P - t) (eff s rcv) } := by
  simp [alg1, h, hr]

theorem trans_4 (h : s.halted = false) (hr : r % 6 = 4) : (alg1 t king tb).trans r p s rcv =
    { s with op := adopt t (tb r p s rcv) s.op (eff s rcv),
             out := if strongOf t (eff s rcv) then
               some (adopt t (tb r p s rcv) s.op (eff s rcv)) else none } := by
  simp [alg1, h, hr]

theorem trans_5 (h : s.halted = false) (hr : r % 6 = 5) : (alg1 t king tb).trans r p s rcv =
    { s with halted := s.out.isSome, done := fun q => (s.done q).or (rcv q) } := by
  simp [alg1, h, hr]

theorem trans_halted_of_ne5 (hr : r % 6 ≠ 5) :
    ((alg1 t king tb).trans r p s rcv).halted = s.halted := by
  unfold alg1; dsimp only; split_ifs <;> first | rfl | omega

theorem trans_done_of_ne5 (hr : r % 6 ≠ 5) :
    ((alg1 t king tb).trans r p s rcv).done = s.done := by
  unfold alg1; dsimp only; split_ifs <;> first | rfl | omega

theorem trans_out_of_ne4 (hr : r % 6 ≠ 4) :
    ((alg1 t king tb).trans r p s rcv).out = s.out := by
  unfold alg1; dsimp only; split_ifs <;> rfl

theorem send_03 (h : s.halted = false) (hr : r % 6 = 0 ∨ r % 6 = 3) :
    (alg1 t king tb).send r p s q = some s.op := by
  rcases hr with hr | hr <;> simp [alg1, h, hr]

theorem send_14 (h : s.halted = false) (hr : r % 6 = 1 ∨ r % 6 = 4) :
    (alg1 t king tb).send r p s q = s.snd := by
  rcases hr with hr | hr <;> simp [alg1, h, hr]

theorem send_2 (h : s.halted = false) (hr : r % 6 = 2) :
    (alg1 t king tb).send r (king (r / 6)) s q = some s.op := by
  simp [alg1, h, hr]

theorem send_5 (h : s.halted = false) (hr : r % 6 = 5) :
    (alg1 t king tb).send r p s q = s.out := by
  simp [alg1, h, hr]

end Steps

/-! ### Executions -/

variable {F : Finset P} {inp : P → Bool} (E : RoundRun (alg1 t king tb) F inp)

namespace Alg1

/-- The effective receptions of `p` in round `r`. -/
def effR (r : ℕ) (p : P) : P → Option Bool := eff (E.s r p) (E.rcv r p)

theorem s_succ (r : ℕ) (p : P) :
    E.s (r + 1) p = (alg1 t king tb).trans r p (E.s r p) (E.rcv r p) := E.s_succ r p

theorem s_zero (p : P) : E.s 0 p = ⟨inp p, false, none, none, false, fun _ => none⟩ := E.s_zero p

/-- A halted node never changes its state. -/
theorem frozen {r : ℕ} {p : P} (h : (E.s r p).halted = true) : ∀ r' ≥ r, E.s r' p = E.s r p := by
  intro r' hr'
  induction r', hr' using Nat.le_induction with
  | base => rfl
  | succ r' _ ih => rw [s_succ, ih, trans_halted h]

theorem halted_mono {r r' : ℕ} {p : P} (h : (E.s r p).halted = true) (hr : r ≤ r') :
    (E.s r' p).halted = true := by rw [frozen E h r' hr]; exact h

/-- Basic invariant (for every node): halted nodes have an output, and a node with an output is
halted, except right after round `6k + 4` (before its termination broadcast). -/
theorem inv (r : ℕ) (p : P) :
    ((E.s r p).halted = true → (E.s r p).out.isSome) ∧
      ((E.s r p).out.isSome → (E.s r p).halted = true ∨ r % 6 = 5) := by
  induction r with
  | zero => simp [s_zero]
  | succ r ih =>
    rw [s_succ]
    by_cases hh : (E.s r p).halted = true
    · rw [trans_halted hh]; exact ⟨fun _ => ih.1 hh, fun _ => Or.inl hh⟩
    · rw [Bool.not_eq_true] at hh
      have h6 : r % 6 < 6 := Nat.mod_lt _ (by norm_num)
      by_cases h5 : r % 6 = 5
      · rw [trans_5 hh h5]
        simp only
        exact ⟨id, fun h => Or.inl h⟩
      · rw [trans_halted_of_ne5 h5, hh]
        refine ⟨fun h => absurd h (by simp), fun ho => Or.inr ?_⟩
        by_cases h4 : r % 6 = 4
        · omega
        · rw [trans_out_of_ne4 h4] at ho
          rcases ih.2 ho with h | h
          · rw [hh] at h; exact absurd h (by simp)
          · omega

/-- Outputs are never revoked. -/
theorem out_persist {r : ℕ} {p : P} {v : Bool} (h : (E.s r p).out = some v) :
    ∀ r' ≥ r, (E.s r' p).out = some v := by
  have hs : (E.s r p).out.isSome := by rw [h]; rfl
  rcases (inv E r p).2 hs with hh | h5
  · intro r' hr'; rw [frozen E hh r' hr']; exact h
  · have hh1 : (E.s (r + 1) p).halted = true := by
      rw [s_succ]
      by_cases hh : (E.s r p).halted = true
      · rw [trans_halted hh]; exact hh
      · rw [Bool.not_eq_true] at hh; rw [trans_5 hh h5]; simpa using hs
    have ho1 : (E.s (r + 1) p).out = some v := by
      rw [s_succ]
      by_cases hh : (E.s r p).halted = true
      · rw [trans_halted hh]; exact h
      · rw [Bool.not_eq_true] at hh; rw [trans_5 hh h5]; exact h
    intro r' hr'
    rcases Nat.eq_or_lt_of_le hr' with e | lt
    · rw [← e]; exact h
    · rw [frozen E hh1 r' lt]; exact ho1

/-! ### The "all correct nodes hold `b`" regime -/

/-- At the beginning of an iteration, all correct nodes hold `b`: running nodes have opinion `b`,
halted nodes have output `b`. -/
def Good (b : Bool) (r : ℕ) : Prop :=
  ∀ q ∉ F, ((E.s r q).halted = true → (E.s r q).out = some b) ∧
    ((E.s r q).halted = false → (E.s r q).op = b)

theorem good_step_ne5 {b : Bool} {r : ℕ} (hr : r % 6 ≠ 5) (hG : Good E b r)
    (hop : ∀ q ∉ F, (E.s r q).halted = false → (E.s (r + 1) q).op = b) : Good E b (r + 1) := by
  intro q hq
  by_cases hh : (E.s r q).halted = true
  · rw [frozen E hh (r + 1) (Nat.le_succ r)]
    exact ⟨fun _ => (hG q hq).1 hh, fun h => absurd hh (by simp [h])⟩
  · rw [Bool.not_eq_true] at hh
    have : (E.s (r + 1) q).halted = false := by rw [s_succ, trans_halted_of_ne5 hr, hh]
    exact ⟨fun h => absurd h (by simp [this]), fun _ => hop q hq hh⟩

variable {E} (hE : E.SyncFrom 0)
include hE

theorem rcv_eq {r : ℕ} {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    E.rcv r p q = (alg1 t king tb).send r q (E.s r q) p := hE r (Nat.zero_le _) p q hp hq

/-- Recorded terminations are exactly the terminations of correct nodes (for correct, running
receivers). -/
theorem done_eq (r : ℕ) {p q : P} (hp : p ∉ F) (hq : q ∉ F) (hph : (E.s r p).halted = false) :
    (E.s r p).done q = if (E.s r q).halted then (E.s r q).out else none := by
  induction r with
  | zero => simp [s_zero]
  | succ r ih =>
    have hph' : (E.s r p).halted = false := by
      by_contra h; rw [Bool.not_eq_false] at h
      rw [halted_mono E h (Nat.le_succ r)] at hph; exact absurd hph (by simp)
    have ih := ih hph'
    by_cases hqh : (E.s r q).halted = true
    · -- `q` is frozen
      have hq1 : E.s (r + 1) q = E.s r q := frozen E hqh (r + 1) (Nat.le_succ r)
      rw [hq1]; simp only [hqh, ↓reduceIte]
      simp only [hqh, ↓reduceIte] at ih
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((inv E r q).1 hqh)
      rw [s_succ]
      by_cases h5 : r % 6 = 5
      · rw [trans_5 hph' h5]; simp only; rw [ih, hv]; rfl
      · rw [trans_done_of_ne5 h5, ih]
    · rw [Bool.not_eq_true] at hqh
      simp only [hqh, Bool.false_eq_true, ↓reduceIte] at ih
      rw [s_succ E r p, s_succ E r q]
      by_cases h5 : r % 6 = 5
      · rw [trans_5 hph' h5, trans_5 hqh h5]
        simp only
        rw [ih, rcv_eq hE hp hq, send_5 hqh h5]
        cases (E.s r q).out <;> simp
      · rw [trans_done_of_ne5 h5, trans_halted_of_ne5 h5, hqh, ih]; simp

/-- Effective reception from a correct sender by a correct running receiver. -/
theorem effR_eq (r : ℕ) {p q : P} (hp : p ∉ F) (hq : q ∉ F) (hph : (E.s r p).halted = false) :
    effR E r p q = if (E.s r q).halted then (E.s r q).out
      else (alg1 t king tb).send r q (E.s r q) p := by
  unfold effR eff
  rw [done_eq hE r hp hq hph, rcv_eq hE hp hq]
  split_ifs with h
  · rw [send_halted h]; cases (E.s r q).out <;> rfl
  · rfl

/-- In the `Good b` regime, every correct running node receives `b` (effectively) from every
correct node in the broadcast rounds `6k` and `6k + 3`. -/
theorem effR_good_03 {b : Bool} {r : ℕ} (hr : r % 6 = 0 ∨ r % 6 = 3) (hG : Good E b r)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) (hph : (E.s r p).halted = false) :
    effR E r p q = some b := by
  rw [effR_eq hE r hp hq hph]
  split_ifs with h
  · exact (hG q hq).1 h
  · rw [Bool.not_eq_true] at h; rw [send_03 h hr, (hG q hq).2 h]

/-- Lemma (`Good` regime): if all correct nodes hold `b` at the beginning of iteration `k`, all of
them have halted with output `b` at its end. This is the validity argument of Theorem 2.9
(Lemma 2.3, validity of Definition 2.5 and Corollary 2.8), including nodes that terminated
earlier (convention (3)). -/
theorem good_iter (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {b : Bool} {k : ℕ}
    (hG : Good E b (6 * k)) : ∀ q ∉ F, (E.s (6 * k + 6) q).halted = true ∧
      (E.s (6 * k + 6) q).out = some b := by
  have m0 : (6 * k) % 6 = 0 := by omega
  have m1 : (6 * k + 1) % 6 = 1 := by omega
  have m2 : (6 * k + 2) % 6 = 2 := by omega
  have m3 : (6 * k + 3) % 6 = 3 := by omega
  have m4 : (6 * k + 4) % 6 = 4 := by omega
  have m5 : (6 * k + 5) % 6 = 5 := by omega
  -- running nodes are running in all rounds `6k, …, 6k + 5`
  have run : ∀ q, (E.s (6 * k) q).halted = false → ∀ i ≤ 5, (E.s (6 * k + i) q).halted = false := by
    intro q hq i hi
    induction i with
    | zero => exact hq
    | succ i ih =>
      rw [← Nat.add_assoc, s_succ, trans_halted_of_ne5 (by omega), ih (by omega)]
  -- round 6k: everybody sends `b`
  have r0 : ∀ q ∉ F, (E.s (6 * k) q).halted = false → (E.s (6 * k + 1) q).snd = some b ∧
      (E.s (6 * k + 1) q).op = b := by
    intro q hq hh
    rw [s_succ, trans_0 hh m0]
    exact ⟨vote_of_all h3 hF fun q' hq' => effR_good_03 hE (Or.inl m0) hG hq hq' hh,
      (hG q hq).2 hh⟩
  have G1 : Good E b (6 * k + 1) := good_step_ne5 E (by omega) hG fun q hq hh => (r0 q hq hh).2
  -- round 6k+1: second broadcast of the validator
  have r1 : ∀ q ∉ F, (E.s (6 * k) q).halted = false → (E.s (6 * k + 2) q).op = b ∧
      (E.s (6 * k + 2) q).strong = true := by
    intro q hq hh
    have hh1 := run q hh 1 (by omega)
    rw [s_succ, trans_1 hh1 m1]
    have hall : ∀ q' ∉ F, effR E (6 * k + 1) q q' = some b := by
      intro q' hq'
      rw [effR_eq hE _ hq hq' hh1]
      split_ifs with h
      · exact (G1 q' hq').1 h
      · rw [Bool.not_eq_true] at h
        rw [send_14 h (Or.inl m1)]
        have h0 : (E.s (6 * k) q').halted = false := by
          by_contra h'; rw [Bool.not_eq_false] at h'
          rw [halted_mono E h' (Nat.le_succ _)] at h; exact absurd h (by simp)
        exact (r0 q' hq' h0).1
    exact alg2_out_of_all h3 hF _ _ hall
  have G2 : Good E b (6 * k + 2) := good_step_ne5 E (by omega) G1 fun q hq hh => by
    have h0 : (E.s (6 * k) q).halted = false := by
      by_contra h'; rw [Bool.not_eq_false] at h'
      rw [halted_mono E h' (Nat.le_succ _)] at hh; exact absurd hh (by simp)
    exact (r1 q hq h0).1
  -- round 6k+2: strong nodes keep their opinion
  have r2 : ∀ q ∉ F, (E.s (6 * k) q).halted = false → (E.s (6 * k + 3) q).op = b := by
    intro q hq hh
    rw [s_succ, trans_2 (run q hh 2 (by omega)) m2]
    simp [kingOut, (r1 q hq hh).2, (r1 q hq hh).1]
  have G3 : Good E b (6 * k + 3) := good_step_ne5 E (by omega) G2 fun q hq hh => by
    have h0 : (E.s (6 * k) q).halted = false := by
      by_contra h'; rw [Bool.not_eq_false] at h'
      rw [halted_mono E h' (by omega)] at hh; exact absurd hh (by simp)
    exact r2 q hq h0
  -- round 6k+3: first broadcast of the termination check
  have r3 : ∀ q ∉ F, (E.s (6 * k) q).halted = false → (E.s (6 * k + 4) q).snd = some b ∧
      (E.s (6 * k + 4) q).op = b := by
    intro q hq hh
    have hh3 := run q hh 3 (by omega)
    rw [s_succ, trans_3 hh3 m3]
    exact ⟨vote_of_all h3 hF fun q' hq' => effR_good_03 hE (Or.inr m3) G3 hq hq' hh3,
      (G3 q hq).2 hh3⟩
  -- round 6k+4: second broadcast of the termination check
  have r4 : ∀ q ∉ F, (E.s (6 * k) q).halted = false → (E.s (6 * k + 5) q).out = some b := by
    intro q hq hh
    have hh4 := run q hh 4 (by omega)
    rw [s_succ, trans_4 hh4 m4]
    have hall : ∀ q' ∉ F, effR E (6 * k + 4) q q' = some b := by
      intro q' hq'
      rw [effR_eq hE _ hq hq' hh4]
      split_ifs with h
      · have h0 : (E.s (6 * k) q').halted = true := by
          by_contra h'; rw [Bool.not_eq_true] at h'
          rw [run q' h' 4 (by omega)] at h; exact absurd h (by simp)
        rw [frozen E h0 _ (by omega)]; exact (hG q' hq').1 h0
      · rw [Bool.not_eq_true] at h
        rw [send_14 h (Or.inr m4)]
        have h0 : (E.s (6 * k) q').halted = false := by
          by_contra h'; rw [Bool.not_eq_false] at h'
          rw [halted_mono E h' (by omega)] at h; exact absurd h (by simp)
        exact (r3 q' hq' h0).1
    obtain ⟨ha, hs⟩ := alg2_out_of_all h3 hF (tb (6 * k + 4) q (E.s (6 * k + 4) q)
      (E.rcv (6 * k + 4) q)) (E.s (6 * k + 4) q).op hall
    simp only [effR] at ha hs
    simp [hs, ha]
  -- round 6k+5: termination broadcast
  intro q hq
  by_cases hh : (E.s (6 * k) q).halted = true
  · rw [frozen E hh _ (by omega)]; exact ⟨hh, (hG q hq).1 hh⟩
  · rw [Bool.not_eq_true] at hh
    have ho := r4 q hq hh
    rw [show 6 * k + 6 = 6 * k + 5 + 1 by rfl, s_succ, trans_5 (run q hh 5 (by omega)) m5]
    simp [ho]

/-! ### Iterations in which no correct node has terminated yet -/

/-- If no correct node has halted at the beginning of iteration `k`, the first five rounds of the
iteration are an instance of Algorithm 2 (validator), Algorithm 3 (king) and Algorithm 2
(termination check) among the correct nodes. -/
theorem fresh_iter {k : ℕ}
    (hfresh : ∀ q ∉ F, (E.s (6 * k) q).halted = false) :
    ∃ (Iv It : Alg2Inst F t),
      (∀ q ∉ F, Iv.x q = (E.s (6 * k) q).op) ∧
      (∀ q ∉ F, (E.s (6 * k + 2) q).op = Iv.o q ∧ (E.s (6 * k + 2) q).strong = Iv.s q) ∧
      (∀ q ∉ F, (E.s (6 * k + 3) q).op = kingOut (Iv.o q) (Iv.s q)
        (effR E (6 * k + 2) q (king k))) ∧
      (king k ∉ F → ∀ q ∉ F, effR E (6 * k + 2) q (king k) = some (Iv.o (king k))) ∧
      (∀ q ∉ F, It.x q = (E.s (6 * k + 3) q).op) ∧
      (∀ q ∉ F, (E.s (6 * k + 5) q).op = It.o q ∧
        (E.s (6 * k + 5) q).out = if It.s q then some (It.o q) else none) ∧
      (∀ q ∉ F, (E.s (6 * k + 5) q).halted = false) := by
  have m0 : (6 * k) % 6 = 0 := by omega
  have m1 : (6 * k + 1) % 6 = 1 := by omega
  have m2 : (6 * k + 2) % 6 = 2 := by omega
  have m3 : (6 * k + 3) % 6 = 3 := by omega
  have m4 : (6 * k + 4) % 6 = 4 := by omega
  have d2 : (6 * k + 2) / 6 = k := by omega
  have run : ∀ q ∉ F, ∀ i ≤ 5, (E.s (6 * k + i) q).halted = false := by
    intro q hq i hi
    induction i with
    | zero => exact hfresh q hq
    | succ i ih =>
      rw [← Nat.add_assoc, s_succ, trans_halted_of_ne5 (by omega), ih (by omega)]
  have eff_run : ∀ i ≤ 5, ∀ p ∉ F, ∀ q ∉ F, effR E (6 * k + i) p q =
      (alg1 t king tb).send (6 * k + i) q (E.s (6 * k + i) q) p := by
    intro i hi p hp q hq
    rw [effR_eq hE _ hp hq (run p hp i hi)]; simp only [run q hq i hi, Bool.false_eq_true, ↓reduceIte]
  -- the validator instance
  let Iv : Alg2Inst F t :=
    { x := fun q => (E.s (6 * k) q).op
      pick := fun q => tb (6 * k + 1) q (E.s (6 * k + 1) q) (E.rcv (6 * k + 1) q)
      r1 := effR E (6 * k)
      r2 := effR E (6 * k + 1)
      h1 := fun i hi q hq => by
        have e0 := eff_run 0 (by omega) i hi q hq
        rw [Nat.add_zero] at e0
        rw [e0, send_03 (hfresh q hq) (Or.inl m0)]
      h2 := fun i hi q hq => by
        rw [eff_run 1 (by omega) i hi q hq, send_14 (run q hq 1 (by omega)) (Or.inl m1), s_succ,
          trans_0 (hfresh q hq) m0]
        rfl }
  have hv2 : ∀ q ∉ F, (E.s (6 * k + 2) q).op = Iv.o q ∧ (E.s (6 * k + 2) q).strong = Iv.s q := by
    intro q hq
    rw [s_succ, trans_1 (run q hq 1 (by omega)) m1]
    have : (E.s (6 * k + 1) q).op = (E.s (6 * k) q).op := by
      rw [s_succ, trans_0 (hfresh q hq) m0]
    exact ⟨by simp only [Alg2Inst.o]; rw [this]; rfl, rfl⟩
  have hk3 : ∀ q ∉ F, (E.s (6 * k + 3) q).op = kingOut (Iv.o q) (Iv.s q)
      (effR E (6 * k + 2) q (king k)) := by
    intro q hq
    rw [s_succ, trans_2 (run q hq 2 (by omega)) m2, d2]
    simp only
    rw [(hv2 q hq).1, (hv2 q hq).2]; rfl
  have hkk : king k ∉ F → ∀ q ∉ F, effR E (6 * k + 2) q (king k) = some (Iv.o (king k)) := by
    intro hk q hq
    rw [eff_run 2 (by omega) q hq _ hk]
    have := send_2 (t := t) (king := king) (tb := tb) (q := q) (run _ hk 2 (by omega)) m2
    rw [d2] at this
    rw [this, (hv2 _ hk).1]
  -- the termination-check instance
  let It : Alg2Inst F t :=
    { x := fun q => (E.s (6 * k + 3) q).op
      pick := fun q => tb (6 * k + 4) q (E.s (6 * k + 4) q) (E.rcv (6 * k + 4) q)
      r1 := effR E (6 * k + 3)
      r2 := effR E (6 * k + 4)
      h1 := fun i hi q hq => by
        rw [eff_run 3 (by omega) i hi q hq, send_03 (run q hq 3 (by omega)) (Or.inr m3)]
      h2 := fun i hi q hq => by
        rw [eff_run 4 (by omega) i hi q hq, send_14 (run q hq 4 (by omega)) (Or.inr m4), s_succ,
          trans_3 (run q hq 3 (by omega)) m3]
        rfl }
  refine ⟨Iv, It, fun q _ => rfl, hv2, hk3, hkk, fun q _ => rfl, fun q hq => ?_,
    fun q hq => run q hq 5 (by omega)⟩
  rw [s_succ, trans_4 (run q hq 4 (by omega)) m4]
  have : (E.s (6 * k + 4) q).op = (E.s (6 * k + 3) q).op := by
    rw [s_succ, trans_3 (run q hq 3 (by omega)) m3]
  simp only [Alg2Inst.o, Alg2Inst.s]
  rw [this]
  exact ⟨rfl, rfl⟩

/-- Halting happens only in round `6k + 5`: the state at `6k + 6` from the state at `6k + 5`. -/
theorem halted_6 {k : ℕ} {q : P} (hq : (E.s (6 * k + 5) q).halted = false) :
    (E.s (6 * k + 6) q).halted = (E.s (6 * k + 5) q).out.isSome ∧
      (E.s (6 * k + 6) q).out = (E.s (6 * k + 5) q).out ∧
      (E.s (6 * k + 6) q).op = (E.s (6 * k + 5) q).op := by
  rw [show 6 * k + 6 = 6 * k + 5 + 1 by rfl, s_succ, trans_5 hq (by omega)]
  exact ⟨rfl, rfl, rfl⟩

/-- The invariant of Theorem 2.9: at the beginning of every iteration, either no correct node has
terminated, or all correct nodes hold a common value (termination agreement, Corollary 2.8). -/
theorem fresh_or_good (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) (k : ℕ) :
    (∀ q ∉ F, (E.s (6 * k) q).halted = false) ∨ ∃ b, Good E b (6 * k) := by
  induction k with
  | zero => left; intro q _; simp [s_zero]
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 * k + 6 by ring]
    rcases ih with hfresh | ⟨b, hG⟩
    · obtain ⟨Iv, It, -, -, -, -, -, hout, hrun⟩ := fresh_iter hE hfresh
      by_cases hex : ∃ p ∉ F, (E.s (6 * k + 6) p).halted = true
      · right
        obtain ⟨p, hp, hph⟩ := hex
        rw [(halted_6 hE (hrun p hp)).1, (hout p hp).2] at hph
        have hsp : It.s p = true := by by_contra h; simp [h] at hph
        refine ⟨It.o p, fun q hq => ⟨fun hqh => ?_, fun hqh => ?_⟩⟩
        · obtain ⟨-, ho, -⟩ := halted_6 hE (hrun q hq)
          rw [(halted_6 hE (hrun q hq)).1, (hout q hq).2] at hqh
          have hsq : It.s q = true := by by_contra h; simp [h] at hqh
          rw [ho, (hout q hq).2]; simp only [hsq, ↓reduceIte]; rw [It.lemma_2_4 h3 hF p hp hsp q hq]
        · rw [(halted_6 hE (hrun q hq)).2.2, (hout q hq).1, It.lemma_2_4 h3 hF p hp hsp q hq]
      · left
        intro q hq
        by_contra h
        exact hex ⟨q, hq, by simpa using h⟩
    · right
      refine ⟨b, fun q hq => ?_⟩
      have := good_iter hE h3 hF hG q hq
      exact ⟨fun _ => this.2, fun h => absurd this.1 (by simp [h])⟩

/-- An iteration with a correct king (in which no correct node terminated before) ends with all
correct nodes halted: Lemma 2.6 + Lemma 2.4 + Corollary 2.8. -/
theorem king_iter (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t) {k : ℕ} (hk : king k ∉ F)
    (hfresh : ∀ q ∉ F, (E.s (6 * k) q).halted = false) :
    ∀ q ∉ F, (E.s (6 * k + 6) q).halted = true := by
  obtain ⟨Iv, It, -, -, hk3, hkk, hItx, hout, hrun⟩ := fresh_iter hE hfresh
  -- Lemma 2.6: after the king's broadcast all correct nodes agree
  have hEB := lemma_2_6 (F := F) (k := king k) (b := Iv.o) (s := Iv.s)
    (rk := fun q => effR E (6 * k + 2) q (king k)) (fun hk' q hq => hkk hk' q hq)
  have hagree := hEB.2 (by
    rw [card_singleton]
    exact lt_of_lt_of_le (by norm_num) (card_pos.2 ⟨king k, mem_sdiff.2 ⟨mem_singleton_self _, hk⟩⟩))
    (Iv.spec h3 hF).weakAgreement
  -- termination check validity
  have hval := It.lemma_2_3 h3 hF
    (v := kingOut (Iv.o (king k)) (Iv.s (king k)) (effR E (6 * k + 2) (king k) (king k)))
    (fun q hq => by rw [hItx q hq, hk3 q hq]; exact hagree q hq (king k) hk)
  intro q hq
  rw [(halted_6 hE (hrun q hq)).1, (hout q hq).2]
  simp [(hval q hq).2]

/-! ### Theorem 2.9 -/

omit hE in
/-- Some king among the first `f + 1` iterations is correct. -/
theorem exists_correct_king (hF : F.card ≤ t)
    (hking : ∀ i ≤ t, ∀ j ≤ t, king i = king j → i = j) :
    ∃ k ≤ F.card, king k ∉ F := by
  have hcard : ((range (F.card + 1)).image king).card = F.card + 1 := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hking i (by omega) j (by omega) h
  obtain ⟨e, he, heF⟩ := exists_mem_notMem_of_card_lt_card (s := F)
    (t := (range (F.card + 1)).image king) (by omega)
  obtain ⟨k, hk, rfl⟩ := mem_image.1 he
  exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, heF⟩

theorem all_halted (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hking : ∀ i ≤ t, ∀ j ≤ t, king i = king j → i = j) :
    ∀ q ∉ F, (E.s (6 * (F.card + 1)) q).halted = true := by
  obtain ⟨k, hkf, hk⟩ := exists_correct_king hF hking
  intro q hq
  refine halted_mono E ?_ (show 6 * k + 6 ≤ 6 * (F.card + 1) by omega)
  rcases fresh_or_good hE h3 hF k with hfresh | ⟨b, hG⟩
  · exact king_iter hE h3 hF hk hfresh q hq
  · exact (good_iter hE h3 hF hG q hq).1

end Alg1

open Alg1

variable {E}

/-- Theorem 2.9 of [LS22] (termination within `6(f+1)` rounds): after `6(f + 1)` rounds every
correct node has decided and halted, where `f = |F|` is the actual number of faulty nodes. -/
theorem theorem_2_9_termination (hE : E.SyncFrom 0) (h3 : 3 * t < Fintype.card P)
    (hF : F.card ≤ t) (hking : ∀ i ≤ t, ∀ j ≤ t, king i = king j → i = j) :
    ∀ q ∉ F, ((alg1 t king tb).decide q (E.s (6 * (F.card + 1)) q)).isSome ∧
      (E.s (6 * (F.card + 1)) q).halted = true := by
  intro q hq
  have hh := all_halted hE h3 hF hking q hq
  exact ⟨(inv E _ q).1 hh, hh⟩

/-- Theorem 2.9 of [LS22] (agreement): all decisions of correct nodes are equal. -/
theorem theorem_2_9_agreement (hE : E.SyncFrom 0) (h3 : 3 * t < Fintype.card P)
    (hF : F.card ≤ t) (hking : ∀ i ≤ t, ∀ j ≤ t, king i = king j → i = j)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) {r r' : ℕ} {v w : Bool}
    (hv : (alg1 t king tb).decide p (E.s r p) = some v)
    (hw : (alg1 t king tb).decide q (E.s r' q) = some w) : v = w := by
  set T := 6 * (F.card + 1)
  have hv' := out_persist E hv (max r T) (le_max_left _ _)
  have hw' := out_persist E hw (max r' T) (le_max_left _ _)
  rcases fresh_or_good hE h3 hF (F.card + 1) with hfresh | ⟨b, hG⟩
  · have := all_halted hE h3 hF hking p hp
    rw [hfresh p hp] at this; exact absurd this (by simp)
  · have hpT := all_halted hE h3 hF hking p hp
    have hqT := all_halted hE h3 hF hking q hq
    rw [frozen E hpT _ (le_max_right _ _), (hG p hp).1 hpT] at hv'
    rw [frozen E hqT _ (le_max_right _ _), (hG q hq).1 hqT] at hw'
    rw [← Option.some_inj, ← hv', ← hw']

/-- Theorem 2.9 of [LS22] (validity): if all correct nodes have input `b`, every decision of a
correct node is `b`. -/
theorem theorem_2_9_validity (hE : E.SyncFrom 0) (h3 : 3 * t < Fintype.card P)
    (hF : F.card ≤ t) {b : Bool} (hinp : ∀ q ∉ F, inp q = b) {p : P} (hp : p ∉ F) {r : ℕ}
    {v : Bool} (hv : (alg1 t king tb).decide p (E.s r p) = some v) : v = b := by
  have hG : Good E b (6 * 0) := fun q hq => by simp [s_zero, hinp q hq]
  have h1 := good_iter hE h3 hF hG p hp
  have hv' := out_persist E hv (max r 6) (le_max_left _ _)
  rw [frozen E h1.1 _ (le_max_right _ _), h1.2] at hv'
  exact (Option.some_inj.1 hv').symm

/-- The number of messages sent by correct nodes in round `r`. -/
def msgs (E : RoundRun (alg1 t king tb) F inp) (r : ℕ) : ℕ :=
  ((Fᶜ ×ˢ univ).filter fun pq : P × P =>
    ((alg1 t king tb).send r pq.1 (E.s r pq.1) pq.2).isSome).card

/-- Theorem 2.9 of [LS22] (communication): correct nodes send at most `6 n² (f + 1)` messages in
total, each a single bit (`Bool`). -/
theorem theorem_2_9_messages (hE : E.SyncFrom 0) (h3 : 3 * t < Fintype.card P)
    (hF : F.card ≤ t) (hking : ∀ i ≤ t, ∀ j ≤ t, king i = king j → i = j) (R : ℕ) :
    ∑ r ∈ range R, msgs E r ≤ 6 * Fintype.card P ^ 2 * (F.card + 1) := by
  set T := 6 * (F.card + 1)
  have hzero : ∀ r ≥ T, msgs E r = 0 := by
    intro r hr
    unfold msgs
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨p, q⟩ hpq
    have hp : p ∉ F := by simpa using (mem_product.1 hpq).1
    have hh := halted_mono E (all_halted hE h3 hF hking p hp) hr
    simp [send_halted hh]
  have hle : ∀ r, msgs E r ≤ Fintype.card P ^ 2 := by
    intro r
    refine le_trans (card_filter_le _ _) ?_
    rw [card_product, card_univ, sq]
    exact Nat.mul_le_mul_right _ (card_le_univ _)
  calc ∑ r ∈ range R, msgs E r ≤ ∑ r ∈ range T, msgs E r := by
        rcases le_total R T with h | h
        · exact sum_le_sum_of_subset (range_subset_range.2 h)
        · rw [← sum_range_add_sum_Ico _ h, sum_eq_zero (fun r hr => hzero r (mem_Ico.1 hr).1)]
          simp
    _ ≤ ∑ _r ∈ range T, Fintype.card P ^ 2 := sum_le_sum fun r _ => hle r
    _ = 6 * Fintype.card P ^ 2 * (F.card + 1) := by simp [T]; ring

end RecursivePhaseKing
