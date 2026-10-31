import Papers.PODC2015.WeakestFDEventualConsistency.RunTools
import Papers.PODC2015.WeakestFDEventualConsistency.Specs

/-!
# Literal (uniform) EIC cannot be implemented with `Ω`

Under the literal reading of EIC-Agreement ("no two processes return infinitely different
values", faulty processes included), EIC is not implementable with `Ω` in the environment of (at
least) three processes where at least one process is correct, whereas EC is (Lemma 2 of
[DGKPS15], Algorithm 4). So under the literal reading, EC and EIC are *not* equivalent, and
Lemma 4 (a transformation from EC to EIC) is false; Theorem 3 holds only with EIC-Agreement
among correct processes (`Alg6.lemma4`, `Alg7.lemma5`).

**Argument.** Fix distinct processes `a`, `b`, `c`; `a` proposes `false`, `b` proposes `true`.
* In the *solo run* of `a` (all others crashed from the start, `Ω` outputs `a` at `a`), `a` must
  respond to instance `0` (EIC-Termination), at some first time `T_a`, with its own proposal
  `false` (EIC-Validity: nobody else ever invokes anything). Likewise `b` responds `true` at
  `T_b` in its solo run.
* In the *merged run*, `a` and `b` take exactly the steps of their solo runs until `T_a`, resp.
  `T_b`, and then crash; `c` is correct, `Ω` outputs `c` at `c`; the messages between the three
  are delayed until `a` and `b` have crashed (they are faulty, so they need not receive
  anything). `a` and `b` cannot distinguish the merged run from their solo runs
  (`sim`), so they return `false` and `true` to instance `0` and these remain their last
  responses forever: they return infinitely different values.

**Model.** The application is folded into the algorithm: the initial state of `p` depends only on
`p`'s own proposals `inp p : ℕ → V` (`EICAlg.init`), so a process does not know the others'
proposals. Process `p` is deemed to invoke instance `0` at its first step and instance `j + 1` at
the step of its first response to `j` (the paper's usage assumption), with value `inp p j`
(`hist`). Knowing one's own future proposals in advance only makes algorithms stronger. The
failure-detector range is `P` and the history must belong to `Omega P`.
-/

namespace Podc.WeakestFDEventualConsistency

open Cslib.FailureDetectors

namespace EICImpossible

variable {P M S O V : Type*} [DecidableEq P]

/-- An algorithm for EIC using `Ω`, with the application folded in: `init p w` is the initial
state of `p` when its proposals are `w : ℕ → V`; outputs `(j, v)` mean "return `v` to
`proposeEIC_j`". There are no input events. -/
structure EICAlg (P M S V : Type*) where
  /-- Initial state of `p` given its own proposals. -/
  init : P → (ℕ → V) → S
  /-- The step function (the failure-detector value is a process id, the output of `Ω`). -/
  step : P → P → S → Event P M Empty → S × Option M × List (ℕ × V)

/-- The algorithm for the proposals `inp`. -/
def EICAlg.alg (A : EICAlg P M S V) (inp : P → ℕ → V) : Algorithm P P M Empty (ℕ × V) S :=
  ⟨fun p => A.init p (inp p), A.step⟩

/-- The EIC history of a run: responses are outputs; `p` invokes instance `0` at its first step
and instance `j + 1` at the step of its first response to `j`, with value `inp p j`. -/
def hist (B : Algorithm P P M Empty (ℕ × V) S) (inp : P → ℕ → V) (r : Run P P Empty) :
    ECHist P V where
  resp p j v t := B.Out r p (j, v) t
  inv p j v t := v = inp p j ∧
    ((j = 0 ∧ (∃ c, r.σ t = some (p, c)) ∧ ∀ t' < t, ∀ c, r.σ t' ≠ some (p, c)) ∨
      (∃ j', j = j' + 1 ∧ (∃ v', B.Out r p (j', v') t) ∧
        ∀ t' < t, ∀ v', ¬ B.Out r p (j', v') t'))

/-- `A` implements (literal) EIC with `Ω` in the environment `E`. -/
def SolvesEIC (A : EICAlg P M S V) (E : Set (FailurePattern P)) : Prop :=
  ∀ (inp : P → ℕ → V) (r : Run P P Empty), r.F ∈ E → r.H ∈ Omega P r.F →
    (A.alg inp).Admissible r → EIC r.F (hist (A.alg inp) inp r)

/-- The environment in which at least one process is correct. -/
def AtLeastOneCorrect : Set (FailurePattern P) := {F | ∃ c, F.Correct c}

/-- Every process's module outputs its own id. -/
def Hid : P → ℕ → P := fun p _ => p

/-! ### Solo runs -/

/-- All processes but `x` crash at time `0`. -/
def soloF (x : P) : FailurePattern P := ⟨fun _ => {y | y ≠ x}, fun _ _ _ => le_rfl⟩

/-- The schedule of the solo run of `x`, which steps at the times `≡ k (mod 3)`: at times
`3 (2u) + k` a time-out, at times `3 (2u + 1) + k` the reception of its own message sent at time
`3u + k` (if any). -/
def soloπ (x : P) (k : ℕ) : ℕ → Config P M S → Option (P × Choice P Empty) := fun t C =>
  if t % 3 = k then
    if t / 3 % 2 = 0 then some (x, .tick)
    else (C.msg (3 * (t / 3 / 2) + k)).elim (some (x, .tick))
      (fun ym => if ym.1 = x then some (x, .recv x (3 * (t / 3 / 2) + k)) else some (x, .tick))
  else none

/-- The solo run of `x`. -/
def soloRun (B : Algorithm P P M Empty O S) (x : P) (k : ℕ) : Run P P Empty :=
  policyRun B (soloF x) Hid (soloπ x k)

lemma soloπ_spec {x y : P} {k t : ℕ} {C : Config P M S} {c : Choice P Empty}
    (h : soloπ x k t C = some (y, c)) :
    y = x ∧ t % 3 = k ∧ ∀ z s, c = .recv z s →
      z = x ∧ t / 3 % 2 = 1 ∧ s = 3 * (t / 3 / 2) + k ∧ ∃ m, C.msg s = some (x, m) := by
  simp only [soloπ] at h
  split_ifs at h with h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, h1, fun z s hc => by cases hc⟩
  · rcases hm : C.msg (3 * (t / 3 / 2) + k) with _ | ⟨y', m⟩
    · rw [hm] at h; simp only [Option.elim, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h1, fun z s hc => by cases hc⟩
    · rw [hm] at h; simp only [Option.elim] at h
      split_ifs at h with h3
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, h1, fun z s hc => ?_⟩
        simp only [Choice.recv.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨rfl, by omega, rfl, m, by rw [hm, h3]⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, h1, fun z s hc => by cases hc⟩

variable (B : Algorithm P P M Empty O S)

lemma soloRun_σ {x y : P} {k t : ℕ} {c : Choice P Empty}
    (h : (soloRun B x k).σ t = some (y, c)) :
    y = x ∧ t % 3 = k ∧ ∀ z s, c = .recv z s →
      z = x ∧ t / 3 % 2 = 1 ∧ s = 3 * (t / 3 / 2) + k ∧
        ∃ m, (B.cfg (soloRun B x k) t).msg s = some (x, m) := by
  rw [soloRun, σ_policyRun] at h
  exact soloπ_spec h

/-- Messages of a run are broadcast by processes stepping at their sending times. -/
lemma msg_sender {r : Run P P Empty} {t s : ℕ} {z : P} {m : M}
    (h : (B.cfg r t).msg s = some (z, m)) : s < t ∧ ∃ c, r.σ s = some (z, c) := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    rw [Algorithm.msg_eq_none_of_le r t s (by omega)] at h
    exact absurd h (by simp)
  · obtain ⟨c, -, hσ, -⟩ := Algorithm.msg_spec r h
    exact ⟨c, hσ⟩

/-- Solo runs are admissible. -/
lemma soloRun_admissible (x : P) {k : ℕ} (hk : k < 3) : B.Admissible (soloRun B x k) where
  alive t y c h := by
    obtain ⟨rfl, -⟩ := soloRun_σ B h
    simp [soloRun, policyRun, soloF]
  recv_valid t y z s h := by
    obtain ⟨rfl, h1, h2⟩ := soloRun_σ B h
    obtain ⟨rfl, h3, rfl, m, hm⟩ := h2 z s rfl
    exact ⟨by omega, m, hm⟩
  recv_once t t' y z s h h' := by
    obtain ⟨rfl, h1, h2⟩ := soloRun_σ B h
    obtain ⟨-, h1', h2'⟩ := soloRun_σ B h'
    obtain ⟨-, h3, hs, -⟩ := h2 z s rfl
    obtain ⟨-, h3', hs', -⟩ := h2' z s rfl
    omega
  ticks y hy T := by
    have : y = x := by
      by_contra hne; exact hy 0 (by simp [soloRun, policyRun, soloF, hne])
    subst this
    refine ⟨3 * (2 * T) + k, by omega, ?_⟩
    rw [soloRun, σ_policyRun]
    simp only [soloπ, show (3 * (2 * T) + k) % 3 = k by omega,
      show (3 * (2 * T) + k) / 3 % 2 = 0 by omega, ↓reduceIte]
  delivery y hy t s z m hm := by
    have : y = x := by
      by_contra hne; exact hy 0 (by simp [soloRun, policyRun, soloF, hne])
    subst this
    obtain ⟨hst, c, hσ⟩ := msg_sender B hm
    obtain ⟨rfl, hsk, -⟩ := soloRun_σ B hσ
    refine ⟨3 * (2 * (s / 3) + 1) + k, ?_⟩
    have hm' : (B.cfg (soloRun B z k) (3 * (2 * (s / 3) + 1) + k)).msg s = some (z, m) := by
      rw [Algorithm.msg_eq_succ _ (by omega), ← Algorithm.msg_eq_succ _ hst]; exact hm
    rw [soloRun, σ_policyRun]
    simp only [soloπ, show (3 * (2 * (s / 3) + 1) + k) % 3 = k by omega,
      show (3 * (2 * (s / 3) + 1) + k) / 3 % 2 = 1 by omega, ↓reduceIte,
      show 3 * ((3 * (2 * (s / 3) + 1) + k) / 3 / 2) + k = s by omega, one_ne_zero]
    rw [show (B.cfg (policyRun B (soloF z) Hid (soloπ z k)) (3 * (2 * (s / 3) + 1) + k)) =
      (B.cfg (soloRun B z k) (3 * (2 * (s / 3) + 1) + k)) from rfl, hm']
    simp

lemma soloRun_omega (x : P) (k : ℕ) : (soloRun B x k).H ∈ Omega P (soloRun B x k).F := by
  intro _
  refine ⟨x, fun t h => h rfl, 0, fun t _ y hy => ?_⟩
  have : y = x := by
    by_contra hne; exact hy 0 (by simp [soloRun, policyRun, soloF, hne])
  subst this; rfl

lemma soloRun_correct (x : P) (k : ℕ) : (soloRun B x k).F.Correct x := fun _ h => h rfl

/-! ### The merged run -/

/-- The schedule of the merged run: `a` repeats the steps of its solo run (schedule `σa`, slot `0`)
up to time `Ta`, `b` those of its solo run (`σb`, slot `1`) up to time `Tb`; `c` takes the
slot `2`: at times `3 (2u) + 2` a time-out, at times `3 (2u + 1) + 2` the reception of the message
sent at time `u` (if any). -/
def mergedπ (σa σb : ℕ → Option (P × Choice P Empty)) (Ta Tb : ℕ) (c : P) :
    ℕ → Config P M S → Option (P × Choice P Empty) := fun t C =>
  if t % 3 = 0 then (if t ≤ Ta then σa t else none)
  else if t % 3 = 1 then (if t ≤ Tb then σb t else none)
  else if t / 3 % 2 = 0 then some (c, .tick)
  else (C.msg (t / 3 / 2)).elim (some (c, .tick)) (fun ym => some (c, .recv ym.1 (t / 3 / 2)))

/-- `a` crashes after `Ta`, `b` after `Tb`, `c` is correct, everybody else crashes at `0`. -/
def mergedF (a b c : P) (Ta Tb : ℕ) : FailurePattern P where
  crashed t := {y | (y ≠ a ∧ y ≠ b ∧ y ≠ c) ∨ (y = a ∧ Ta < t) ∨ (y = b ∧ Tb < t)}
  mono t t' h y hy := by
    rcases hy with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, by omega⟩)

/-- The merged run. -/
def mergedRun (a b c : P) (Ta Tb : ℕ) : Run P P Empty :=
  policyRun B (mergedF a b c Ta Tb) Hid
    (mergedπ (soloRun B a 0).σ (soloRun B b 1).σ Ta Tb c)

omit [DecidableEq P] in
lemma mergedπ_spec {σa σb : ℕ → Option (P × Choice P Empty)} {Ta Tb : ℕ} {c y : P} {t : ℕ}
    {C : Config P M S} {ch : Choice P Empty} (h : mergedπ σa σb Ta Tb c t C = some (y, ch)) :
    (t % 3 = 0 ∧ t ≤ Ta ∧ σa t = some (y, ch)) ∨ (t % 3 = 1 ∧ t ≤ Tb ∧ σb t = some (y, ch)) ∨
      (t % 3 = 2 ∧ y = c ∧ ∀ z s, ch = .recv z s →
        t / 3 % 2 = 1 ∧ s = t / 3 / 2 ∧ ∃ m, C.msg s = some (z, m)) := by
  simp only [mergedπ] at h
  split_ifs at h with h1 h2 h3 h4 h5
  · exact Or.inl ⟨h1, h2, h⟩
  · exact Or.inr (Or.inl ⟨h3, h4, h⟩)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨by omega, rfl, fun z s hc => by cases hc⟩)
  · rcases hm : C.msg (t / 3 / 2) with _ | ⟨y', m⟩
    · rw [hm] at h; simp only [Option.elim, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr ⟨by omega, rfl, fun z s hc => by cases hc⟩)
    · rw [hm] at h; simp only [Option.elim, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Or.inr (Or.inr ⟨by omega, rfl, fun z s hc => ?_⟩)
      simp only [Choice.recv.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨by omega, rfl, m, hm⟩

variable {a b c : P} {Ta Tb : ℕ}

lemma mergedRun_σ {y : P} {t : ℕ} {ch : Choice P Empty}
    (h : (mergedRun B a b c Ta Tb).σ t = some (y, ch)) :
    (y = a ∧ t % 3 = 0 ∧ t ≤ Ta ∧ (soloRun B a 0).σ t = some (y, ch)) ∨
    (y = b ∧ t % 3 = 1 ∧ t ≤ Tb ∧ (soloRun B b 1).σ t = some (y, ch)) ∨
    (y = c ∧ t % 3 = 2 ∧ ∀ z s, ch = .recv z s → t / 3 % 2 = 1 ∧ s = t / 3 / 2 ∧
      ∃ m, (B.cfg (mergedRun B a b c Ta Tb) t).msg s = some (z, m)) := by
  rw [mergedRun, σ_policyRun] at h
  rcases mergedπ_spec h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨(soloRun_σ B h3).1, h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨(soloRun_σ B h3).1, h1, h2, h3⟩)
  · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)

lemma mergedRun_σ_a (hab : a ≠ b) (hac : a ≠ c) {t : ℕ} (ht : t ≤ Ta) (ch : Choice P Empty) :
    (soloRun B a 0).σ t = some (a, ch) ↔ (mergedRun B a b c Ta Tb).σ t = some (a, ch) := by
  constructor
  · intro h
    obtain ⟨-, h0, -⟩ := soloRun_σ B h
    rw [mergedRun, σ_policyRun]
    simp only [mergedπ, h0, ht, ↓reduceIte]; exact h
  · intro h
    rcases mergedRun_σ B h with ⟨-, -, -, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · exact h'
    · exact absurd h' hab
    · exact absurd h' hac

lemma mergedRun_σ_b (hab : a ≠ b) (hbc : b ≠ c) {t : ℕ} (ht : t ≤ Tb) (ch : Choice P Empty) :
    (soloRun B b 1).σ t = some (b, ch) ↔ (mergedRun B a b c Ta Tb).σ t = some (b, ch) := by
  constructor
  · intro h
    obtain ⟨-, h0, -⟩ := soloRun_σ B h
    rw [mergedRun, σ_policyRun]
    simp only [mergedπ, h0, ht, ↓reduceIte, one_ne_zero]; exact h
  · intro h
    rcases mergedRun_σ B h with ⟨h', -⟩ | ⟨-, -, -, h'⟩ | ⟨h', -⟩
    · exact absurd h'.symm hab
    · exact h'
    · exact absurd h' hbc

/-- `a` cannot distinguish the merged run from its solo run up to `Ta`. -/
lemma sim_a (hab : a ≠ b) (hac : a ≠ c) :
    ∀ t ≤ Ta + 1, B.st (soloRun B a 0) a t = B.st (mergedRun B a b c Ta Tb) a t ∧
      ∀ s m, (B.cfg (soloRun B a 0) t).msg s = some (a, m) ↔
        (B.cfg (mergedRun B a b c Ta Tb) t).msg s = some (a, m) :=
  sim _ _ a (Ta + 1) (fun t ht ch => mergedRun_σ_a B hab hac (by omega) ch) (fun _ _ => rfl)
    (fun t _ q s h => ((soloRun_σ B h).2.2 q s rfl).1)

lemma sim_out_a (hab : a ≠ b) (hac : a ≠ c) :
    ∀ t < Ta + 1, ∀ o, B.Out (soloRun B a 0) a o t ↔ B.Out (mergedRun B a b c Ta Tb) a o t :=
  sim_out _ _ a (Ta + 1) (fun t ht ch => mergedRun_σ_a B hab hac (by omega) ch) (fun _ _ => rfl)
    (fun t _ q s h => ((soloRun_σ B h).2.2 q s rfl).1)

lemma sim_b (hab : a ≠ b) (hbc : b ≠ c) :
    ∀ t ≤ Tb + 1, B.st (soloRun B b 1) b t = B.st (mergedRun B a b c Ta Tb) b t ∧
      ∀ s m, (B.cfg (soloRun B b 1) t).msg s = some (b, m) ↔
        (B.cfg (mergedRun B a b c Ta Tb) t).msg s = some (b, m) :=
  sim _ _ b (Tb + 1) (fun t ht ch => mergedRun_σ_b B hab hbc (by omega) ch) (fun _ _ => rfl)
    (fun t _ q s h => ((soloRun_σ B h).2.2 q s rfl).1)

lemma sim_out_b (hab : a ≠ b) (hbc : b ≠ c) :
    ∀ t < Tb + 1, ∀ o, B.Out (soloRun B b 1) b o t ↔ B.Out (mergedRun B a b c Ta Tb) b o t :=
  sim_out _ _ b (Tb + 1) (fun t ht ch => mergedRun_σ_b B hab hbc (by omega) ch) (fun _ _ => rfl)
    (fun t _ q s h => ((soloRun_σ B h).2.2 q s rfl).1)

lemma mergedRun_correct (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {y : P}
    (hy : (mergedRun B a b c Ta Tb).F.Correct y) : y = c := by
  by_contra hne
  by_cases hya : y = a
  · subst hya; exact hy (Ta + 1) (Or.inr (Or.inl ⟨rfl, by omega⟩))
  by_cases hyb : y = b
  · subst hyb; exact hy (Tb + 1) (Or.inr (Or.inr ⟨rfl, by omega⟩))
  exact hy 0 (Or.inl ⟨hya, hyb, hne⟩)

lemma mergedRun_correct_c (hac : a ≠ c) (hbc : b ≠ c) :
    (mergedRun B a b c Ta Tb).F.Correct c := by
  intro t h
  rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h rfl
  · exact hac h.symm
  · exact hbc h.symm

lemma mergedRun_omega (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (mergedRun B a b c Ta Tb).H ∈ Omega P (mergedRun B a b c Ta Tb).F := by
  intro _
  refine ⟨c, mergedRun_correct_c B hac hbc, 0, fun t _ y hy => ?_⟩
  obtain rfl := mergedRun_correct B hab hac hbc hy
  rfl

/-- The merged run is admissible. -/
lemma mergedRun_admissible (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    B.Admissible (mergedRun B a b c Ta Tb) where
  alive t y ch h := by
    rintro (⟨h1, h2, h3⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩) <;>
      rcases mergedRun_σ B h with ⟨h4, -, h5, -⟩ | ⟨h4, -, h5, -⟩ | ⟨h4, -⟩
    all_goals first
      | omega
      | exact h1 h4
      | exact h2 h4
      | exact h3 h4
      | exact hab h4
      | exact hab h4.symm
      | exact hac h4
      | exact hac h4.symm
      | exact hbc h4
  recv_valid t y z s h := by
    rcases mergedRun_σ B h with ⟨rfl, -, h5, h6⟩ | ⟨rfl, -, h5, h6⟩ | ⟨rfl, h1, h2⟩
    · obtain ⟨hst, m, hm⟩ := (soloRun_admissible B y (by norm_num)).recv_valid t y z s h6
      obtain rfl := ((soloRun_σ B h6).2.2 z s rfl).1
      exact ⟨hst, m, ((sim_a B hab hac t (by omega)).2 s m).1 hm⟩
    · obtain ⟨hst, m, hm⟩ := (soloRun_admissible B y (by norm_num)).recv_valid t y z s h6
      obtain rfl := ((soloRun_σ B h6).2.2 z s rfl).1
      exact ⟨hst, m, ((sim_b B hab hbc t (by omega)).2 s m).1 hm⟩
    · obtain ⟨h3, rfl, m, hm⟩ := h2 z s rfl
      exact ⟨by omega, m, hm⟩
  recv_once t t' y z s h h' := by
    rcases mergedRun_σ B h with ⟨rfl, -, -, h6⟩ | ⟨rfl, -, -, h6⟩ | ⟨rfl, h1, h2⟩ <;>
      rcases mergedRun_σ B h' with ⟨h4, -, -, h6'⟩ | ⟨h4, -, -, h6'⟩ | ⟨h4, h1', h2'⟩
    all_goals first
      | exact absurd h4 hab | exact absurd h4.symm hab | exact absurd h4 hac
      | exact absurd h4.symm hac | exact absurd h4 hbc | exact absurd h4.symm hbc | skip
    · exact (soloRun_admissible B y (by norm_num)).recv_once t t' y z s h6 h6'
    · exact (soloRun_admissible B y (by norm_num)).recv_once t t' y z s h6 h6'
    · obtain ⟨h3, h5, -⟩ := h2 z s rfl
      obtain ⟨h3', h5', -⟩ := h2' z s rfl
      omega
  ticks y hy T := by
    obtain rfl := mergedRun_correct B hab hac hbc hy
    refine ⟨3 * (2 * T) + 2, by omega, ?_⟩
    rw [mergedRun, σ_policyRun]
    simp only [mergedπ, show (3 * (2 * T) + 2) % 3 = 2 by omega,
      show (3 * (2 * T) + 2) / 3 % 2 = 0 by omega, ↓reduceIte, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one]
  delivery y hy t s z m hm := by
    obtain rfl := mergedRun_correct B hab hac hbc hy
    obtain ⟨hst, -⟩ := msg_sender B hm
    refine ⟨3 * (2 * s + 1) + 2, ?_⟩
    have hm' : (B.cfg (mergedRun B a b y Ta Tb) (3 * (2 * s + 1) + 2)).msg s = some (z, m) := by
      rw [Algorithm.msg_eq_succ _ (by omega), ← Algorithm.msg_eq_succ _ hst]; exact hm
    rw [mergedRun, σ_policyRun]
    simp only [mergedπ, show (3 * (2 * s + 1) + 2) % 3 = 2 by omega,
      show (3 * (2 * s + 1) + 2) / 3 % 2 = 1 by omega, ↓reduceIte, OfNat.ofNat_ne_zero,
      OfNat.ofNat_ne_one, one_ne_zero, show (3 * (2 * s + 1) + 2) / 3 / 2 = s by omega]
    rw [show B.cfg (policyRun B (mergedF a b y Ta Tb) Hid
      (mergedπ (soloRun B a 0).σ (soloRun B b 1).σ Ta Tb y)) (3 * (2 * s + 1) + 2) =
      B.cfg (mergedRun B a b y Ta Tb) (3 * (2 * s + 1) + 2) from rfl, hm']
    rfl

/-! ### The impossibility -/

/-- **Literal EIC is not implementable with `Ω`.** In the environment where at least one process
is correct, with at least three processes, no algorithm using `Ω` implements EIC with the
literal (uniform) EIC-Agreement. In contrast, EC is implementable with `Ω` in every environment
(Lemma 2 of [DGKPS15]); hence, under the literal reading of EIC-Agreement, Lemma 4 and Theorem 3
of [DGKPS15] fail. -/
theorem not_solvesEIC (a b c : P) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (A : EICAlg P M S Bool) : ¬ SolvesEIC A AtLeastOneCorrect := by
  intro hA
  set inp : P → ℕ → Bool := fun y _ => decide (y = b) with hinp
  set B := A.alg inp with hB
  -- in its solo run, a process responds to instance `0`, and only with its own proposal
  have solo : ∀ x k, k < 3 → (∃ T v, B.Out (soloRun B x k) x (0, v) T) ∧
      ∀ T v, B.Out (soloRun B x k) x (0, v) T → v = inp x 0 := by
    intro x k hk
    obtain ⟨hterm, -, -, hval⟩ := hA inp (soloRun B x k) ⟨x, soloRun_correct B x k⟩
      (soloRun_omega B x k) (soloRun_admissible B x hk)
    refine ⟨?_, ?_⟩
    · obtain ⟨v, T, h⟩ := hterm x (soloRun_correct B x k) 0
      exact ⟨T, v, h⟩
    · intro T v h
      obtain ⟨y, t', -, hinv, hj⟩ := hval x 0 v T h
      rcases hj with ⟨-, ⟨c', hσ⟩, -⟩ | ⟨j', hj', -⟩
      · obtain ⟨rfl, -⟩ := soloRun_σ B hσ
        exact hinv
      · omega
  classical
  obtain ⟨hexA, hvalA⟩ := solo a 0 (by norm_num)
  obtain ⟨hexB, hvalB⟩ := solo b 1 (by norm_num)
  obtain ⟨va, hva⟩ := Nat.find_spec hexA
  obtain ⟨vb, hvb⟩ := Nat.find_spec hexB
  have hva' : va = false := by rw [hvalA _ _ hva]; simp [hinp, hab]
  have hvb' : vb = true := by rw [hvalB _ _ hvb]; simp [hinp]
  set Ta := Nat.find hexA
  set Tb := Nat.find hexB
  set rm := mergedRun B a b c Ta Tb
  obtain ⟨-, -, hagr, -⟩ := hA inp rm ⟨c, mergedRun_correct_c B hac hbc⟩
    (mergedRun_omega B hab hac hbc) (mergedRun_admissible B hab hac hbc)
  refine hagr a b 0 fun T => ⟨max T (max Ta Tb + 1), le_max_left _ _, va, vb,
    by rw [hva', hvb']; decide, ⟨Ta, by omega, ?_, fun t₁ v₁ h₁ _ hr => ?_⟩,
    ⟨Tb, by omega, ?_, fun t₁ v₁ h₁ _ hr => ?_⟩⟩
  · exact (sim_out_a B hab hac Ta (by omega) _).1 hva
  · obtain ⟨⟨ch, hσ⟩, -⟩ := hr
    rcases mergedRun_σ B hσ with ⟨-, -, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · exact hab h
    · exact hac h
  · exact (sim_out_b B hab hbc Tb (by omega) _).1 hvb
  · obtain ⟨⟨ch, hσ⟩, -⟩ := hr
    rcases mergedRun_σ B hσ with ⟨h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩
    · exact hab h.symm
    · omega
    · exact hbc h

end EICImpossible

end Podc.WeakestFDEventualConsistency
