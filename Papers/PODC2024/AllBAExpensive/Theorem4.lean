import Papers.PODC2024.AllBAExpensive.Reduction
import Papers.PODC2024.AllBAExpensive.Solvability
import Cslib.Computability.Distributed.Byzantine.PartialSync.FLM
import Cslib.Computability.Distributed.Byzantine.PartialSync.DolevStrong
import Cslib.Computability.Distributed.Byzantine.PartialSync.ICSync

/-!
# All Byzantine Agreement Problems Are Expensive — §5: the general solvability theorem

* `trivial_of_solvableSync`: **Lemma 10**, corrected: it needs `n ≥ 3` (it is false for `n = 2`,
  `t = 1`: `lemma10_counterexample` in `Solvability.lean`). Proof as in the paper: Lemma 6 +
  the Fischer–Lynch–Merritt impossibility (`Cslib.Byzantine.PartialSync.weakValidity_not_solvableSync`).
* `theorem4_auth`: **Theorem 4**, authenticated part (CC ⇔ solvable), given that interactive
  consistency is authenticated-solvable (Dolev–Strong, cited by the paper).
* `theorem4_unauth`: **Theorem 4**, unauthenticated part, **corrected**: a non-trivial problem is
  unauthenticated-solvable iff it satisfies CC and (`n > 3t` or `n ≤ 2`), given that interactive
  consistency is unauthenticated-solvable for `n > 3t` (cited by the paper).
* `theorem4_auth'`, `theorem4_unauth'`: the same, **unconditional** (interactive consistency is
  discharged by the verified protocols `Cslib.Byzantine.PartialSync.icSolvableAuthSync_dolevStrong`
  (Dolev–Strong, any `t`) and `Cslib.Byzantine.PartialSync.icSolvableSync_of_three_t_lt` (`n > 3t`)).
* `theorem4_unauth_as_stated_false`: the paper's version ("iff CC and `n > 3t`") is false.
* `message_lower_bound_psync(_auth)`: the lower bound of this paper applies to every
  partially synchronous solution, i.e. it implies Theorem 4 of *On the Validity of Consensus*
  (PODC 2023) up to the constant.
-/

namespace AllBAExpensive

open Finset Cslib.Byzantine.PartialSync

variable {P VI VO : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}
  {val : ValidityProperty P VI VO}

/-- **Lemma 10** of [AllBAExpensive], corrected (`3 ≤ n` added): if `val` is
unauthenticated-solvable in synchrony with `3 ≤ n ≤ 3t`, then `val` is trivial. -/
theorem trivial_of_solvableSync [Nonempty VI] (h3 : 3 ≤ Fintype.card P)
    (hn : Fintype.card P ≤ 3 * t) (htn : t < Fintype.card P) (h : val.SolvableSync t δ) :
    val.Trivial t := by
  by_contra hnt
  exact weakValidity_not_solvableSync (δ := 0) h3 hn
    (weakConsensus_solvableSync_of (h.mono_delta (Nat.zero_le δ)) hnt htn)

/-- **Theorem 4** of [AllBAExpensive], authenticated part: a problem is authenticated-solvable in
synchrony iff it satisfies the containment condition (given that interactive consistency is
authenticated-solvable, [Dolev–Strong]). -/
theorem theorem4_auth [Nonempty VI] (htn : t < Fintype.card P)
    (hIC : ICSolvableAuthSync P VI t δ) :
    val.SolvableAuthSync t δ ↔ ContainmentCondition t val :=
  solvableAuthSync_iff_containmentCondition htn hIC

/-- **Theorem 4** of [AllBAExpensive], unauthenticated part, **corrected**: a non-trivial problem
is unauthenticated-solvable in synchrony iff it satisfies CC and (`n > 3t` or `n ≤ 2`), given that
interactive consistency is unauthenticated-solvable for `n > 3t` [Pease–Shostak–Lamport]. The
paper omits the case `n ≤ 2`. -/
theorem theorem4_unauth {P VI : Type} [Fintype P] [DecidableEq P] [Nonempty VI]
    {val : ValidityProperty P VI VO} (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P)
    (hIC : 3 * t < Fintype.card P → ICSolvableSync P VI t δ) :
    val.SolvableSync t δ ↔
      ContainmentCondition t val ∧ (3 * t < Fintype.card P ∨ Fintype.card P ≤ 2) := by
  constructor
  · intro h
    refine ⟨containmentCondition_of_solvableSync h htn, ?_⟩
    by_contra hc
    push Not at hc
    exact hnt (trivial_of_solvableSync (by omega) hc.1 htn h)
  · rintro ⟨hC, h3 | h2⟩
    · exact solvableSync_of_containmentCondition hC (hIC h3)
    · exact solvableSync_of_containmentCondition hC (icSolvableSync_of_card_le_two VI (Or.inr h2))

/-- The unauthenticated part of **Theorem 4** as stated in the paper ("a non-trivial problem is
unauthenticated-solvable iff it satisfies CC and `n > 3t`") is false: for `n = 2`, `t = 1`, weak
consensus is non-trivial and unauthenticated-solvable. -/
theorem theorem4_unauth_as_stated_false (δ : ℕ) :
    ¬ ∀ val : ValidityProperty (Fin 2) Bool Bool, ¬ val.Trivial 1 →
      (val.SolvableSync 1 δ ↔ ContainmentCondition 1 val ∧ 3 * 1 < Fintype.card (Fin 2)) := by
  intro h
  have := (h _ (lemma10_counterexample δ).2).mp (lemma10_counterexample δ).1
  simp at this

/-- **Theorem 4** of [AllBAExpensive], authenticated part, unconditional: for `t < n`, a problem
is authenticated-solvable in synchrony iff it satisfies the containment condition. -/
theorem theorem4_auth' {P VI : Type} [Fintype P] [DecidableEq P] [Nonempty VI]
    {val : ValidityProperty P VI VO} (htn : t < Fintype.card P) :
    val.SolvableAuthSync t δ ↔ ContainmentCondition t val :=
  theorem4_auth htn (icSolvableAuthSync_dolevStrong htn)

/-- **Theorem 4** of [AllBAExpensive], unauthenticated part, corrected and unconditional: for
`t < n`, a non-trivial problem is unauthenticated-solvable in synchrony iff it satisfies the
containment condition and (`n > 3t` or `n ≤ 2`). -/
theorem theorem4_unauth' {P VI : Type} [Fintype P] [DecidableEq P] [Nonempty VI]
    {val : ValidityProperty P VI VO} (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P) :
    val.SolvableSync t δ ↔
      ContainmentCondition t val ∧ (3 * t < Fintype.card P ∨ Fintype.card P ≤ 2) :=
  theorem4_unauth hnt htn icSolvableSync_of_three_t_lt

/-! ### Relation to *On the Validity of Consensus* (PODC 2023), Theorem 4 -/

variable {M S K : Type*} {A : Algorithm P M S VI VO} {Au : Auth P M K}

/-- The lower bound of this paper applies to every algorithm solving a non-trivial problem in
**partial synchrony** (a partially synchronous solution is a synchronous one): this recovers
Theorem 4 of *On the Validity of Consensus* (`ValidityConsensus.message_lower_bound_auth`,
`⌈t/2⌉(⌈t/2⌉+1)` messages) up to the constant, without using asynchrony. -/
theorem message_lower_bound_psync_auth [Nonempty VI] (hU : A.Unforging Au)
    (hA : SolvesConsensusAuth Au t δ A val) (hnt : ¬ val.Trivial t)
    (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.AuthValid Au A ∧ R.gst = 0 ∧
      ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N :=
  message_lower_bound_auth hU hA.sync hnt htn

/-- Unauthenticated version of `message_lower_bound_psync_auth`. -/
theorem message_lower_bound_psync [Nonempty VI] (hA : SolvesConsensus t δ A val)
    (hnt : ¬ val.Trivial t) (htn : t < Fintype.card P) :
    ∃ R : Run P M VI, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N, t ^ 2 ≤ 32 * R.msgsUpTo A N :=
  message_lower_bound hA.sync hnt htn

end AllBAExpensive
