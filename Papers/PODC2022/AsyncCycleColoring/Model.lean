import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# The asynchronous cycle with local immediate snapshots

Fraigniaud, Lambein-Monette, Rabie, *Fault Tolerant Coloring of the Asynchronous Cycle*
(PODC 2022 brief announcement; full version arXiv:2207.11198), Section 2.

The `n` processes sit on the nodes `ZMod n` of the cycle `C_n`; the neighbours of `p` are `p - 1`
and `p + 1`. Every process `p` owns a single-writer register `R_p`, initially `⊥` (`none`).
A *round* of `p` (an activation) is a local immediate snapshot: `p` writes its current local state
into `R_p`, reads the registers of its two neighbours and performs a local computation, which
either yields a new local state or makes `p` return an output (and stop).

A *schedule* `σ : ℕ → Finset (ZMod n)` gives the set `σ t` of processes activated at time
`t ≥ 1`. Processes activated at the same time behave as in an immediate snapshot: first all of
them write, then all of them read (Section 2.1). Activating a process that has already returned
has no effect. Crashes are modelled by schedules that stop activating a process; nothing forces a
schedule to be fair.

Since the model has no consistent orientation, an algorithm should treat its two neighbours
symmetrically; the algorithms of the paper do, but the model does not need this.

We store the full local state in the register (the paper's algorithms write all their variables).
The input of `p` (its identifier `X_p`) is part of its initial local state.
-/

namespace AsyncCycle

/-- An algorithm for the asynchronous cycle: from the local state and the contents of the two
neighbours' registers (`none` = `⊥`), compute a new local state (`Sum.inl`) or return an output
(`Sum.inr`). -/
structure Alg (S O : Type*) where
  step : S → Option S → Option S → S ⊕ O

variable {n : ℕ} {S O : Type*}

/-- A global configuration: local states, register contents, outputs (`none` = still working). -/
structure Config (n : ℕ) (S O : Type*) where
  loc : ZMod n → S
  reg : ZMod n → Option S
  out : ZMod n → Option O

namespace Config

/-- `p` performs a *working* activation in the transition to the next configuration. -/
def Acts (c : Config n S O) (σ : Finset (ZMod n)) (p : ZMod n) : Prop :=
  p ∈ σ ∧ c.out p = none

instance (c : Config n S O) (σ : Finset (ZMod n)) (p : ZMod n) : Decidable (c.Acts σ p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Registers after the write phase of the processes activated in `σ`. -/
def regAfter (c : Config n S O) (σ : Finset (ZMod n)) (p : ZMod n) : Option S :=
  if c.Acts σ p then some (c.loc p) else c.reg p

/-- The local computation of `p` (meaningful when `p` acts). -/
def res (A : Alg S O) (c : Config n S O) (σ : Finset (ZMod n)) (p : ZMod n) : S ⊕ O :=
  A.step (c.loc p) (c.regAfter σ (p - 1)) (c.regAfter σ (p + 1))

/-- One time step: all activated working processes write, then read, then compute. -/
def next (A : Alg S O) (σ : Finset (ZMod n)) (c : Config n S O) : Config n S O where
  loc p := if c.Acts σ p then Sum.elim id (fun _ => c.loc p) (c.res A σ p) else c.loc p
  reg := c.regAfter σ
  out p := if c.Acts σ p then Sum.elim (fun _ => none) some (c.res A σ p) else c.out p

end Config

/-- The execution of `A` from the initial local states `init` under the schedule `σ`;
`run A init σ t` is the configuration at the end of time `t` (`σ (t + 1)` is activated next). -/
def run (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) : ℕ → Config n S O
  | 0 => ⟨init, fun _ => none, fun _ => none⟩
  | t + 1 => (run A init σ t).next A (σ (t + 1))

/-- `p` performs a working activation at time `t + 1`. -/
def ActsAt (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) :
    Prop :=
  (run A init σ t).Acts (σ (t + 1)) p

instance (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (t : ℕ) (p : ZMod n) :
    Decidable (ActsAt A init σ t p) :=
  inferInstanceAs (Decidable ((run A init σ t).Acts _ _))

/-- Number of working activations of `p` among the times `1, …, T`. -/
def workActs (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n)) (p : ZMod n)
    (T : ℕ) : ℕ :=
  ((Finset.range T).filter (fun t => ActsAt A init σ t p)).card

/-- Wait-freedom with running time `K` (Section 2.2): in every execution, every process is
activated at most `K` times before it returns (it returns at the latest at its `K`-th
activation). -/
def WaitFreeWithin (A : Alg S O) (init : ZMod n → S) (K : ℕ) : Prop :=
  ∀ σ : ℕ → Finset (ZMod n), ∀ p T, workActs A init σ p T ≤ K

/-- The outputs of the terminated processes properly colour the subgraph of `C_n` they induce. -/
def ProperOutputs (A : Alg S O) (init : ZMod n → S) : Prop :=
  ∀ σ : ℕ → Finset (ZMod n), ∀ t p o o', (run A init σ t).out p = some o →
    (run A init σ t).out (p + 1) = some o' → o ≠ o'

/-- All outputs lie in `pal`. -/
def OutputsIn (A : Alg S O) (init : ZMod n → S) (pal : Set O) : Prop :=
  ∀ σ : ℕ → Finset (ZMod n), ∀ t p o, (run A init σ t).out p = some o → o ∈ pal

/-! ### Basic facts about executions -/

section Basic

variable (A : Alg S O) (init : ZMod n → S) (σ : ℕ → Finset (ZMod n))

@[simp] lemma run_zero_loc : (run A init σ 0).loc = init := rfl
@[simp] lemma run_zero_reg (p : ZMod n) : (run A init σ 0).reg p = none := rfl
@[simp] lemma run_zero_out (p : ZMod n) : (run A init σ 0).out p = none := rfl

lemma run_succ (t : ℕ) : run A init σ (t + 1) = (run A init σ t).next A (σ (t + 1)) := rfl

lemma reg_succ (t : ℕ) (p : ZMod n) :
    (run A init σ (t + 1)).reg p =
      if ActsAt A init σ t p then some ((run A init σ t).loc p) else (run A init σ t).reg p := rfl

lemma reg_succ_of_acts {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) :
    (run A init σ (t + 1)).reg p = some ((run A init σ t).loc p) := by
  rw [reg_succ, ite_eq_left h]

lemma reg_succ_of_not_acts {t : ℕ} {p : ZMod n} (h : ¬ ActsAt A init σ t p) :
    (run A init σ (t + 1)).reg p = (run A init σ t).reg p := by
  rw [reg_succ, ite_eq_right h]

/-- The local computation performed by `p` at time `t + 1`. -/
def resAt (t : ℕ) (p : ZMod n) : S ⊕ O :=
  A.step ((run A init σ t).loc p) ((run A init σ (t + 1)).reg (p - 1))
    ((run A init σ (t + 1)).reg (p + 1))

lemma loc_succ (t : ℕ) (p : ZMod n) :
    (run A init σ (t + 1)).loc p =
      if ActsAt A init σ t p then Sum.elim id (fun _ => (run A init σ t).loc p) (resAt A init σ t p)
      else (run A init σ t).loc p := rfl

lemma out_succ (t : ℕ) (p : ZMod n) :
    (run A init σ (t + 1)).out p =
      if ActsAt A init σ t p then Sum.elim (fun _ => none) some (resAt A init σ t p)
      else (run A init σ t).out p := rfl

lemma loc_succ_of_not_acts {t : ℕ} {p : ZMod n} (h : ¬ ActsAt A init σ t p) :
    (run A init σ (t + 1)).loc p = (run A init σ t).loc p := by
  rw [loc_succ, ite_eq_right h]

lemma out_succ_of_not_acts {t : ℕ} {p : ZMod n} (h : ¬ ActsAt A init σ t p) :
    (run A init σ (t + 1)).out p = (run A init σ t).out p := by
  rw [out_succ, ite_eq_right h]

/-- A failing activation: `p` computes a new local state. -/
lemma loc_succ_of_inl {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) {s : S}
    (hs : resAt A init σ t p = Sum.inl s) : (run A init σ (t + 1)).loc p = s := by
  rw [loc_succ, ite_eq_left h, hs]; rfl

lemma out_succ_of_inl {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) {s : S}
    (hs : resAt A init σ t p = Sum.inl s) : (run A init σ (t + 1)).out p = none := by
  rw [out_succ, ite_eq_left h, hs]; rfl

/-- A returning activation. -/
lemma loc_succ_of_inr {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) {o : O}
    (ho : resAt A init σ t p = Sum.inr o) :
    (run A init σ (t + 1)).loc p = (run A init σ t).loc p := by
  rw [loc_succ, ite_eq_left h, ho]; rfl

lemma out_succ_of_inr {t : ℕ} {p : ZMod n} (h : ActsAt A init σ t p) {o : O}
    (ho : resAt A init σ t p = Sum.inr o) : (run A init σ (t + 1)).out p = some o := by
  rw [out_succ, ite_eq_left h, ho]; rfl

lemma actsAt_iff (t : ℕ) (p : ZMod n) :
    ActsAt A init σ t p ↔ p ∈ σ (t + 1) ∧ (run A init σ t).out p = none := Iff.rfl

/-- Once a process has returned, its output never changes. -/
lemma out_succ_of_some {t : ℕ} {p : ZMod n} {o : O} (h : (run A init σ t).out p = some o) :
    (run A init σ (t + 1)).out p = some o := by
  have : ¬ ActsAt A init σ t p := fun h' => by simp [h'.2] at h
  rw [out_succ_of_not_acts A init σ this, h]

lemma out_mono {t t' : ℕ} (htt' : t ≤ t') {p : ZMod n} {o : O}
    (h : (run A init σ t).out p = some o) : (run A init σ t').out p = some o := by
  induction t', htt' using Nat.le_induction with
  | base => exact h
  | succ t' _ ih => exact out_succ_of_some A init σ ih

/-- After returning, a process is never active again, so its register and its local state are
frozen. -/
lemma not_acts_of_out {t : ℕ} {p : ZMod n} {o : O} (h : (run A init σ t).out p = some o) :
    ¬ ActsAt A init σ t p := fun h' => by simp [h'.2] at h

end Basic

/-! ### Correctness from a "claims" discipline

The three algorithms of the paper return a colour only if it is not *claimed* by the register of
any neighbour, and the returned colour is claimed by the returning process's own last written
state. Since a process that has returned never writes again, outputs are proper. -/

section Claims

variable {A : Alg S O} {init : ZMod n → S}

/-- The return discipline: `claims s` is the set of outputs claimed by a register holding `s`.
A process returns `o` only if its own state claims `o` and no neighbour's register does. -/
def ClaimSafe (A : Alg S O) (claims : S → Set O) : Prop :=
  ∀ s l r o, A.step s l r = Sum.inr o →
    o ∈ claims s ∧ (∀ x, l = some x → o ∉ claims x) ∧ (∀ x, r = some x → o ∉ claims x)

variable (σ : ℕ → Finset (ZMod n))

/-- When `p` has returned `o`, its register holds a state claiming `o` (forever). -/
lemma reg_claims_of_out {claims : S → Set O} (hA : ClaimSafe A claims) :
    ∀ t (p : ZMod n) (o : O), (run A init σ t).out p = some o →
      ∃ x, (run A init σ t).reg p = some x ∧ o ∈ claims x := by
  intro t
  induction t with
  | zero => intro p o h; simp at h
  | succ t ih =>
    intro p o h
    by_cases hp : ActsAt A init σ t p
    · rw [out_succ, ite_eq_left hp] at h
      rcases hr : resAt A init σ t p with s | o'
      · rw [hr] at h; simp at h
      · rw [hr] at h
        simp only [Sum.elim_inr, Option.some.injEq] at h
        subst h
        exact ⟨_, reg_succ_of_acts A init σ hp, (hA _ _ _ _ hr).1⟩
    · rw [out_succ_of_not_acts A init σ hp] at h
      rw [reg_succ_of_not_acts A init σ hp]
      exact ih p o h

/-- If `p` has returned `o` by time `t`, then its register at every later time claims `o`. -/
lemma reg_claims_of_out_le {claims : S → Set O} (hA : ClaimSafe A claims) {t t' : ℕ}
    (htt' : t ≤ t') {p : ZMod n} {o : O} (h : (run A init σ t).out p = some o) :
    ∃ x, (run A init σ t').reg p = some x ∧ o ∈ claims x :=
  reg_claims_of_out σ hA t' p o (out_mono A init σ htt' h)

/-- Generic correctness: under the claims discipline, neighbouring outputs differ, on every cycle
`C_n`. -/
theorem properOutputs_of_claimSafe {claims : S → Set O}
    (hA : ClaimSafe A claims) : ProperOutputs A init := by
  intro σ T
  -- First: whenever a process returns at time `t + 1`, every neighbour that has already returned
  -- (at time `≤ t + 1`) has a different output.
  have key : ∀ t (p q : ZMod n) (o o' : O), (q = p - 1 ∨ q = p + 1) →
      ActsAt A init σ t p → resAt A init σ t p = Sum.inr o →
      (run A init σ (t + 1)).out q = some o' → o ≠ o' := by
    intro t p q o o' hq hp hr hq'
    have hsafe := hA _ _ _ _ hr
    obtain ⟨x, hx, hox⟩ := reg_claims_of_out σ hA (t + 1) q o' hq'
    rintro rfl
    rcases hq with rfl | rfl
    · exact hsafe.2.1 x hx hox
    · exact hsafe.2.2 x hx hox
  -- Main induction.
  intro p o o'
  induction T with
  | zero => intro h; simp at h
  | succ t ih =>
    intro hp hq
    by_cases hpo : (run A init σ t).out p = some o
    · by_cases hqo : (run A init σ t).out (p + 1) = some o'
      · exact ih hpo hqo
      · -- `p + 1` returned at time `t + 1`.
        have hqa : ActsAt A init σ t (p + 1) := by
          by_contra hna; rw [out_succ_of_not_acts A init σ hna] at hq; exact hqo hq
        have hr : resAt A init σ t (p + 1) = Sum.inr o' := by
          rw [out_succ, ite_eq_left hqa] at hq
          rcases hr : resAt A init σ t (p + 1) with s | o''
          · rw [hr] at hq; simp at hq
          · rw [hr] at hq; simp only [Sum.elim_inr, Option.some.injEq] at hq; rw [hq]
        exact (key t (p + 1) p o' o (Or.inl (by simp)) hqa hr hp).symm
    · -- `p` returned at time `t + 1`.
      have hpa : ActsAt A init σ t p := by
        by_contra hna; rw [out_succ_of_not_acts A init σ hna] at hp; exact hpo hp
      have hr : resAt A init σ t p = Sum.inr o := by
        rw [out_succ, ite_eq_left hpa] at hp
        rcases hr : resAt A init σ t p with s | o''
        · rw [hr] at hp; simp at hp
        · rw [hr] at hp; simp only [Sum.elim_inr, Option.some.injEq] at hp; rw [hp]
      exact key t p (p + 1) o o' (Or.inr rfl) hpa hr hq

/-- Generic palette lemma: if an invariant of local states holds initially, is preserved by
failing steps, and every output returned from a state satisfying it lies in `pal`. -/
theorem outputsIn_of_inv {Inv : S → Prop} {pal : Set O} (h0 : ∀ p, Inv (init p))
    (hstep : ∀ s l r s', Inv s → A.step s l r = Sum.inl s' → Inv s')
    (hout : ∀ s l r o, Inv s → A.step s l r = Sum.inr o → o ∈ pal) : OutputsIn A init pal := by
  intro σ
  have hinv : ∀ t p, Inv ((run A init σ t).loc p) := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      intro p
      by_cases hp : ActsAt A init σ t p
      · rcases hr : resAt A init σ t p with s | o
        · rw [loc_succ_of_inl A init σ hp hr]; exact hstep _ _ _ _ (ih p) hr
        · rw [loc_succ_of_inr A init σ hp hr]; exact ih p
      · rw [loc_succ_of_not_acts A init σ hp]; exact ih p
  intro t
  induction t with
  | zero => intro p o h; simp at h
  | succ t ih =>
    intro p o h
    by_cases hp : ActsAt A init σ t p
    · rw [out_succ, ite_eq_left hp] at h
      rcases hr : resAt A init σ t p with s | o'
      · rw [hr] at h; simp at h
      · rw [hr] at h; simp only [Sum.elim_inr, Option.some.injEq] at h; subst h
        exact hout _ _ _ _ (hinv t p) hr
    · rw [out_succ_of_not_acts A init σ hp] at h; exact ih p o h

end Claims

end AsyncCycle
