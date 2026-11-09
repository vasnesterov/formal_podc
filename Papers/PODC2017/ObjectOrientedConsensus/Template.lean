import Mathlib

/-!
# Objects and consensus templates (Sections 2–3 of Afek–Aspnes–Cohen–Vainstein)

Y. Afek, J. Aspnes, E. Cohen, D. Vainstein, *Object Oriented Consensus*, PODC 2017 (brief
announcement); full version (16 pp.) [AACV].

The objects of Section 2 are specified by the input/output behaviour of one invocation round:

* `I` — the processes that invoke the object (with inputs `val`),
* `O ⊆ I` — the processes that return from it (with outputs `out`; crashed processes do not return).

`IsVAC I O val out` is the vacillate-adopt-commit object, `IsAC I O val out` the adopt-commit object.

The templates of Section 3 are modelled at the level of these specifications: an execution of
Algorithm 1 (`Exec1`) is a sequence of VAC rounds, the outputs of each round only constrained by
`IsVAC`, and the reconciliator outputs `recon` arbitrary (validity and weak agreement are hypotheses of the
theorems that need them). The processes invoking round `m + 1` are a subset of those that returned from
round `m`; this covers both the paper's reading of Algorithm 1 (a process that commits halts) and the
variant where deciding processes keep participating (`Exec1.Halting` distinguishes them).

* Lemma 1 (Algorithm 1 is a correct consensus algorithm): `Exec1.lemma1_agreement`,
  `Exec1.lemma1_validity`, `Exec1.lemma1_termination`.
* The Algorithm 2 template (adopt-commit + conciliator, "proved similarly"): `Exec2.agreement`,
  `Exec2.validity`, `Exec2.termination`. Its agreement needs the *validity of the conciliator*
  (`Exec2.ConciliatorValid`); Algorithm 4 (Phase-King's conciliator) does not have it, see
  `PhaseKing.lean`.
-/

namespace Podc.ObjectOrientedConsensus

/-- Confidence levels returned by VAC and AC objects. -/
inductive Conf where
  | vacillate
  | adopt
  | commit
  deriving DecidableEq, Repr

variable {P V : Type*}

/-- **Vacillate-adopt-commit** (Section 2 of [AACV]) on one invocation round: invokers `I` with
inputs `val`, returners `O` with outputs `out`. -/
structure IsVAC (I O : Set P) (val : P → V) (out : P → Conf × V) : Prop where
  /-- Only invokers return. -/
  sub : O ⊆ I
  /-- Validity: a returned value is the input of an invoker. -/
  validity : ∀ p ∈ O, ∃ q ∈ I, (out p).2 = val q
  /-- Convergence: unanimous inputs `v` make every returner get `(commit, v)`. -/
  convergence : ∀ v, (∀ q ∈ I, val q = v) → ∀ p ∈ O, out p = (.commit, v)
  /-- Coherence over adopt & commit. -/
  coh_ac : ∀ p ∈ O, (out p).1 = .commit → ∀ q ∈ O, (out q).1 ≠ .vacillate ∧ (out q).2 = (out p).2
  /-- Coherence over vacillate & adopt. -/
  coh_va : (∀ r ∈ O, (out r).1 ≠ .commit) → ∀ p ∈ O, (out p).1 = .adopt →
    ∀ q ∈ O, (out q).1 = .vacillate ∨ (out q).2 = (out p).2

/-- **Adopt-commit** (Section 2 of [AACV], after Gafni) on one invocation round. -/
structure IsAC (I O : Set P) (val : P → V) (out : P → Conf × V) : Prop where
  /-- Only invokers return. -/
  sub : O ⊆ I
  /-- The confidence is `adopt` or `commit`. -/
  noVac : ∀ p ∈ O, (out p).1 ≠ .vacillate
  /-- Validity: a returned value is the input of an invoker. -/
  validity : ∀ p ∈ O, ∃ q ∈ I, (out p).2 = val q
  /-- Convergence: unanimous inputs `v` make every returner get `(commit, v)`. -/
  convergence : ∀ v, (∀ q ∈ I, val q = v) → ∀ p ∈ O, out p = (.commit, v)
  /-- Coherence: a commit value is returned to everybody. -/
  coherence : ∀ p ∈ O, (out p).1 = .commit → ∀ q ∈ O, (out q).2 = (out p).2

/-- Forgetting vacillation: `vacillate` is reported as `adopt`. -/
def Conf.toAC : Conf → Conf
  | .vacillate => .adopt
  | c => c

/-- Section 1/5 remark ("adopt-commit is slightly weaker"): relabelling `vacillate` as `adopt` turns a
VAC round into an AC round. -/
theorem IsVAC.toAC {I O : Set P} {val : P → V} {out : P → Conf × V} (h : IsVAC I O val out) :
    IsAC I O val (fun p => ((out p).1.toAC, (out p).2)) where
  sub := h.sub
  noVac p _ := by cases (out p).1 <;> simp [Conf.toAC]
  validity := h.validity
  convergence v hv p hp := by simp [h.convergence v hv p hp, Conf.toAC]
  coherence p hp hc q hq := by
    have hc' : (out p).1 = .commit := by
      revert hc; cases (out p).1 <;> simp [Conf.toAC]
    exact (h.coh_ac p hp hc' q hq).2

/-! ### Algorithm 1: VAC + reconciliator -/

/-- The value a process carries into the next round of Algorithm 1: the reconciliator's output after
`vacillate`, the returned value after `adopt`/`commit`. -/
def next1 (o : Conf × V) (r : V) : V := if o.1 = .vacillate then r else o.2

/-- An execution of Algorithm 1 (consensus template, VAC + reconciliator), described by its rounds
`m = 0, 1, …` (the paper's `m = 1, 2, …`). Round `m` is a VAC round with invokers `I m`, returners `O m`,
inputs `val m` and outputs `out m`; `recon m p` is the reconciliator's output to `p` (used only if `p`
vacillated). The invokers of round `m + 1` returned from round `m` (crashes and halting only remove
processes). -/
structure Exec1 (P V : Type*) where
  /-- Inputs of consensus. -/
  inp : P → V
  /-- Invokers of the VAC of round `m`. -/
  I : ℕ → Set P
  /-- Processes returning from the VAC of round `m`. -/
  O : ℕ → Set P
  /-- Inputs of the VAC of round `m`. -/
  val : ℕ → P → V
  /-- Outputs of the VAC of round `m`. -/
  out : ℕ → P → Conf × V
  /-- Outputs of the reconciliator of round `m`. -/
  recon : ℕ → P → V
  val_zero : ∀ p ∈ I 0, val 0 p = inp p
  I_succ : ∀ m, I (m + 1) ⊆ O m
  val_succ : ∀ m, ∀ p ∈ I (m + 1), val (m + 1) p = next1 (out m p) (recon m p)
  vac : ∀ m, IsVAC (I m) (O m) (val m) (out m)

namespace Exec1

variable (E : Exec1 P V)

/-- `p` decides `v` (in some round it returns `(commit, v)`). -/
def Decides (p : P) (v : V) : Prop := ∃ m, p ∈ E.O m ∧ E.out m p = (.commit, v)

/-- Algorithm 1 as printed: `decide σ` is followed by `halt`, so a committing process does not invoke
the next round. -/
def Halting : Prop := ∀ m, ∀ p ∈ E.I (m + 1), (E.out m p).1 ≠ .commit

/-- After a commit of `v` in round `m`, every process entering any later round carries `v`, and
every process returning from a later round returns `(commit, v)`. -/
theorem after_commit {m : ℕ} {p : P} {v : V} (hp : p ∈ E.O m) (hc : E.out m p = (.commit, v)) :
    ∀ k, (∀ q ∈ E.I (m + k + 1), E.val (m + k + 1) q = v) ∧
      ∀ q ∈ E.O (m + k + 1), E.out (m + k + 1) q = (.commit, v) := by
  intro k
  induction k with
  | zero =>
    have hval : ∀ q ∈ E.I (m + 1), E.val (m + 1) q = v := by
      intro q hq
      have hqO := E.I_succ m hq
      obtain ⟨hnv, hqv⟩ := (E.vac m).coh_ac p hp (by simp [hc]) q hqO
      rw [E.val_succ m q hq, next1, if_neg hnv, hqv, hc]
    exact ⟨hval, (E.vac (m + 1)).convergence v hval⟩
  | succ k ih =>
    have hval : ∀ q ∈ E.I (m + (k + 1) + 1), E.val (m + (k + 1) + 1) q = v := by
      intro q hq
      have hqO : q ∈ E.O (m + k + 1) := by
        have := E.I_succ _ hq; rwa [show m + (k + 1) = m + k + 1 by omega] at this
      rw [E.val_succ _ q hq, show m + (k + 1) = m + k + 1 by omega, next1, ih.2 q hqO]
      simp
    exact ⟨hval, (E.vac _).convergence v hval⟩

/-- **Lemma 1 of [AACV], agreement.** Two decisions in an execution of Algorithm 1 are equal. Holds
whether or not deciding processes halt. -/
theorem lemma1_agreement {p q : P} {v w : V} (hp : E.Decides p v) (hq : E.Decides q w) : v = w := by
  obtain ⟨m, hpm, hpc⟩ := hp
  obtain ⟨m', hqm, hqc⟩ := hq
  rcases lt_trichotomy m m' with h | rfl | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := (E.after_commit hpm hpc k).2 q hqm
    rw [hqc] at this
    exact (Prod.ext_iff.1 this).2.symm
  · have := ((E.vac m).coh_ac p hpm (by simp [hpc]) q hqm).2
    rw [hpc, hqc] at this
    exact this.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := (E.after_commit hqm hqc k).2 p hpm
    rw [hpc] at this
    exact (Prod.ext_iff.1 this).2

/-- The reconciliator only returns valid values (an input of consensus). The paper's proof of Lemma 1
assumes this ("all inputs to the VAC and reconciliator objects are clearly valid"); its definition of
the reconciliator states it only at the agreement point (footnote 1). -/
def RecValid : Prop := ∀ m, ∀ p ∈ E.O m, (E.out m p).1 = .vacillate → ∃ q ∈ E.I 0, E.recon m p = E.inp q

/-- Every value carried into round `m` is an input of consensus (given a valid reconciliator). -/
theorem val_valid (hrec : E.RecValid) : ∀ m, ∀ p ∈ E.I m, ∃ q ∈ E.I 0, E.val m p = E.inp q := by
  intro m
  induction m with
  | zero => intro p hp; exact ⟨p, hp, E.val_zero p hp⟩
  | succ m ih =>
    intro p hp
    have hpO := E.I_succ m hp
    rw [E.val_succ m p hp, next1]
    split_ifs with hv
    · exact hrec m p hpO hv
    · obtain ⟨q, hq, hqv⟩ := (E.vac m).validity p hpO
      rw [hqv]
      exact ih q hq

/-- **Lemma 1 of [AACV], validity.** With a valid reconciliator every decision is an input. -/
theorem lemma1_validity (hrec : E.RecValid) {p : P} {v : V} (hp : E.Decides p v) :
    ∃ q ∈ E.I 0, E.inp q = v := by
  obtain ⟨m, hpm, hpc⟩ := hp
  obtain ⟨q, hq, hqv⟩ := (E.vac m).validity p hpm
  obtain ⟨r, hr, hrv⟩ := E.val_valid hrec m q hq
  exact ⟨r, hr, by rw [← hrv, ← hqv, hpc]⟩

/-- The reconciliator's *weak agreement* in round `m` (Section 2): every vacillating process receives
`u`, and `u` is the value of the processes that did not vacillate. -/
def WeakAgreementAt (m : ℕ) (u : V) : Prop :=
  ∀ p ∈ E.O m, ((E.out m p).1 = .vacillate → E.recon m p = u) ∧ ((E.out m p).1 ≠ .vacillate → (E.out m p).2 = u)

/-- If the reconciliator gives all vacillating processes the value adopted by some process (or
committed), weak agreement holds: VAC coherence makes the non-vacillating processes agree. -/
theorem weakAgreementAt_of_adopt {m : ℕ} {p : P} (hp : p ∈ E.O m) (hpv : (E.out m p).1 ≠ .vacillate)
    (hrec : ∀ q ∈ E.O m, (E.out m q).1 = .vacillate → E.recon m q = (E.out m p).2) :
    E.WeakAgreementAt m (E.out m p).2 := by
  intro q hq
  refine ⟨hrec q hq, fun hqv => ?_⟩
  by_cases hc : ∃ r ∈ E.O m, (E.out m r).1 = .commit
  · obtain ⟨r, hr, hrc⟩ := hc
    rw [((E.vac m).coh_ac r hr hrc q hq).2, ((E.vac m).coh_ac r hr hrc p hp).2]
  · push Not at hc
    have hpa : (E.out m p).1 = .adopt := by
      have := hc p hp; revert hpv this; cases (E.out m p).1 <;> simp
    have hqa : (E.out m q).1 = .adopt := by
      have := hc q hq; revert hqv this; cases (E.out m q).1 <;> simp
    rcases (E.vac m).coh_va hc p hp hpa q hq with h | h
    · rw [hqa] at h; cases h
    · exact h

/-- **Lemma 1 of [AACV], termination (deterministic part).** If weak agreement holds in round `m`,
every process returning from round `m + 1` commits there. (Termination of the VAC itself, i.e. that
every non-crashed invoker returns, is a property of the implementation; see `BenOr.lean` for where it
fails.) -/
theorem lemma1_termination {m : ℕ} {u : V} (h : E.WeakAgreementAt m u) :
    ∀ p ∈ E.O (m + 1), E.out (m + 1) p = (.commit, u) := by
  refine (E.vac (m + 1)).convergence u fun q hq => ?_
  have hqO := E.I_succ m hq
  rw [E.val_succ m q hq, next1]
  split_ifs with hv
  · exact (h q hqO).1 hv
  · exact (h q hqO).2 hv

end Exec1

/-! ### Algorithm 2: AC + conciliator -/

/-- An execution of Algorithm 2 (adopt-commit + conciliator). `con m p` is the conciliator's output to
`p` in round `m` (used only if `p` adopted). -/
structure Exec2 (P V : Type*) where
  /-- Inputs of consensus. -/
  inp : P → V
  /-- Invokers of the AC of round `m`. -/
  I : ℕ → Set P
  /-- Processes returning from the AC of round `m`. -/
  O : ℕ → Set P
  /-- Inputs of the AC of round `m`. -/
  val : ℕ → P → V
  /-- Outputs of the AC of round `m`. -/
  out : ℕ → P → Conf × V
  /-- Outputs of the conciliator of round `m`. -/
  con : ℕ → P → V
  val_zero : ∀ p ∈ I 0, val 0 p = inp p
  I_succ : ∀ m, I (m + 1) ⊆ O m
  val_succ : ∀ m, ∀ p ∈ I (m + 1),
    val (m + 1) p = if (out m p).1 = .commit then (out m p).2 else con m p
  ac : ∀ m, IsAC (I m) (O m) (val m) (out m)

namespace Exec2

variable (E : Exec2 P V)

/-- `p` decides `v` (in some round it returns `(commit, v)`). -/
def Decides (p : P) (v : V) : Prop := ∃ m, p ∈ E.O m ∧ E.out m p = (.commit, v)

/-- Validity of the conciliator (Aspnes' framework): its output is the input of one of its invokers,
i.e. a value adopted in the same round. -/
def ConciliatorValid : Prop :=
  ∀ m, ∀ p ∈ E.O m, (E.out m p).1 = .adopt → ∃ q ∈ E.O m, (E.out m q).1 = .adopt ∧ E.con m p = (E.out m q).2

/-- After a commit of `v` in round `m`, every later round is unanimous on `v` (needs a valid
conciliator). -/
theorem after_commit (hcon : E.ConciliatorValid) {m : ℕ} {p : P} {v : V} (hp : p ∈ E.O m)
    (hc : E.out m p = (.commit, v)) :
    ∀ k, (∀ q ∈ E.I (m + k + 1), E.val (m + k + 1) q = v) ∧
      ∀ q ∈ E.O (m + k + 1), E.out (m + k + 1) q = (.commit, v) := by
  have hall : ∀ q ∈ E.O m, (E.out m q).2 = v := fun q hq => by
    rw [(E.ac m).coherence p hp (by simp [hc]) q hq, hc]
  intro k
  induction k with
  | zero =>
    have hval : ∀ q ∈ E.I (m + 1), E.val (m + 1) q = v := by
      intro q hq
      have hqO := E.I_succ m hq
      rw [E.val_succ m q hq]
      split_ifs with hqc
      · exact hall q hqO
      · have hqa : (E.out m q).1 = .adopt := by
          have := (E.ac m).noVac q hqO; revert hqc this; cases (E.out m q).1 <;> simp
        obtain ⟨r, hr, -, hrv⟩ := hcon m q hqO hqa
        rw [hrv, hall r hr]
    exact ⟨hval, (E.ac (m + 1)).convergence v hval⟩
  | succ k ih =>
    have hval : ∀ q ∈ E.I (m + (k + 1) + 1), E.val (m + (k + 1) + 1) q = v := by
      intro q hq
      have hqO : q ∈ E.O (m + k + 1) := by
        have := E.I_succ _ hq; rwa [show m + (k + 1) = m + k + 1 by omega] at this
      rw [E.val_succ _ q hq, show m + (k + 1) = m + k + 1 by omega, ih.2 q hqO]
      simp
    exact ⟨hval, (E.ac _).convergence v hval⟩

/-- **Algorithm 2 of [AACV], agreement** ("proved similarly" to Lemma 1), under the validity of the
conciliator. -/
theorem agreement (hcon : E.ConciliatorValid) {p q : P} {v w : V} (hp : E.Decides p v)
    (hq : E.Decides q w) : v = w := by
  obtain ⟨m, hpm, hpc⟩ := hp
  obtain ⟨m', hqm, hqc⟩ := hq
  rcases lt_trichotomy m m' with h | rfl | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := (E.after_commit hcon hpm hpc k).2 q hqm
    rw [hqc] at this
    exact (Prod.ext_iff.1 this).2.symm
  · have := (E.ac m).coherence p hpm (by simp [hpc]) q hqm
    rw [hpc, hqc] at this
    exact this.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := (E.after_commit hcon hqm hqc k).2 p hpm
    rw [hpc] at this
    exact (Prod.ext_iff.1 this).2

/-- **Algorithm 2 of [AACV], validity**, under the validity of the conciliator. -/
theorem validity (hcon : E.ConciliatorValid) {p : P} {v : V} (hp : E.Decides p v) :
    ∃ q ∈ E.I 0, E.inp q = v := by
  have key : ∀ m, ∀ p ∈ E.I m, ∃ q ∈ E.I 0, E.val m p = E.inp q := by
    intro m
    induction m with
    | zero => intro p hp; exact ⟨p, hp, E.val_zero p hp⟩
    | succ m ih =>
      have hout : ∀ q ∈ E.O m, ∃ r ∈ E.I 0, (E.out m q).2 = E.inp r := fun q hq => by
        obtain ⟨r, hr, hrv⟩ := (E.ac m).validity q hq
        obtain ⟨s, hs, hsv⟩ := ih r hr
        exact ⟨s, hs, hrv.trans hsv⟩
      intro p hp
      have hpO := E.I_succ m hp
      rw [E.val_succ m p hp]
      split_ifs with hc
      · exact hout p hpO
      · have hpa : (E.out m p).1 = .adopt := by
          have := (E.ac m).noVac p hpO; revert hc this; cases (E.out m p).1 <;> simp
        obtain ⟨r, hr, -, hrv⟩ := hcon m p hpO hpa
        rw [hrv]; exact hout r hr
  obtain ⟨m, hpm, hpc⟩ := hp
  obtain ⟨q, hq, hqv⟩ := (E.ac m).validity p hpm
  obtain ⟨r, hr, hrv⟩ := key m q hq
  exact ⟨r, hr, by rw [← hrv, ← hqv, hpc]⟩

/-- **Algorithm 2 of [AACV], termination (deterministic part).** If in round `m` every process
leaves with the same value `u` (the conciliator agreed), every process returning from round `m + 1`
commits `u`. -/
theorem termination {m : ℕ} {u : V}
    (h : ∀ p ∈ E.O m, (if (E.out m p).1 = .commit then (E.out m p).2 else E.con m p) = u) :
    ∀ p ∈ E.O (m + 1), E.out (m + 1) p = (.commit, u) :=
  (E.ac (m + 1)).convergence u fun q hq => by rw [E.val_succ m q hq]; exact h q (E.I_succ m hq)

end Exec2

end Podc.ObjectOrientedConsensus
