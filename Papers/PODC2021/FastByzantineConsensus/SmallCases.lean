import Papers.PODC2021.FastByzantineConsensus.TwoStep
import Podc.PartialSync.Triviality

/-!
# The case `n ≤ 3f` and the degenerate case `n = 1`

* `not_solves_of_le_three_mul`: the classic bound — no protocol solves consensus with weak
  validity tolerating `f` Byzantine processes if `2 ≤ n ≤ 3f` (also with signatures). Derived from
  Theorem 1 of *On the Validity of Consensus* (`SolvesConsensusAuth.trivial`),
  since weak validity is a non-trivial validity property. This covers the case `t ≤ 1` of
  Theorem 4.5 of Kuznetsov–Tonkikh–Zhang.
* `single_fastConsensus`: for `n = 1` the protocol "decide your own input immediately" is an
  `f`-resilient `t`-two-step consensus protocol for all `f`, `t`. In particular Theorem 4.5 fails
  for `f = 1`, `t = 0` (`3f + 2t − 2 = 1`), and the classic `3f + 1` bound needs `n ≥ 2`.
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [Fintype P] [DecidableEq P]

/-- Weakening the resilience: a protocol tolerating `f` faults tolerates `f' ≤ f` faults. -/
theorem SolvesConsensusAuth.mono {Au : Auth P M K} {A : Algorithm P M S V V} {f f' δ : ℕ}
    {val : ValidityProperty P V V} (h : SolvesConsensusAuth Au f δ A val) (hf : f' ≤ f) :
    SolvesConsensusAuth Au f' δ A val := by
  have hV : ∀ R : Run P M V, R.Valid f' δ → R.Valid f δ := fun R hR =>
    ⟨hR.card_faulty.trans hf, hR.dl_ge, hR.dl_le⟩
  exact ⟨fun R hR => h.termination R (hV R hR), fun R hR => h.agreement R (hV R hR),
    fun R hR => h.validity R (hV R hR)⟩

/-- **Classic bound** (Pease–Shostak–Lamport / Dwork–Lynch–Stockmeyer, used for `t ≤ 1` in
Theorem 4.5): no consensus with weak validity for `2 ≤ n ≤ 3f`, even with signatures. -/
theorem not_solves_of_le_three_mul {Au : Auth P M K} {A : Algorithm P M S V V} {f δ : ℕ}
    (hU : A.Unforging Au) (h2 : 2 ≤ Fintype.card P) (hn : Fintype.card P ≤ 3 * f) {a b : V}
    (hab : a ≠ b) : ¬ SolvesConsensusAuth Au f δ A (weakValidity P V) := by
  intro h
  have : Nonempty V := ⟨a⟩
  have hf' : min f (Fintype.card P - 1) ≤ f := min_le_left _ _
  have h3 : Fintype.card P ≤ 3 * min f (Fintype.card P - 1) := by
    rcases le_total f (Fintype.card P - 1) with hle | hle
    · rw [min_eq_left hle]; exact hn
    · rw [min_eq_right hle]; omega
  have h0 : 0 < min f (Fintype.card P - 1) := by
    rcases le_total f (Fintype.card P - 1) with hle | hle
    · rw [min_eq_left hle]; omega
    · rw [min_eq_right hle]; omega
  have h1 : min f (Fintype.card P - 1) < Fintype.card P :=
    (min_le_right _ _).trans_lt (by omega)
  obtain ⟨v, hv⟩ := (SolvesConsensusAuth.mono h hf').trivial hU h0 h1 h3
  have hc : ∀ x : V, IsInputConfig (min f (Fintype.card P - 1)) (fun _ : P => some x) := by
    intro x
    unfold IsInputConfig
    have : (Config.procs (fun _ : P => some x)) = univ := by ext p; simp
    rw [this, card_univ]; omega
  have ha := hv _ (hc a) a (fun _ => rfl)
  have hb := hv _ (hc b) b (fun _ => rfl)
  exact hab (ha.symm.trans hb)

/-- The one-process protocol: decide the own input at once, send nothing. -/
def selfDecide (P V : Type*) : Algorithm P Unit V V V where
  init _ v := v
  step _ s _ := s
  send _ _ _ := []
  decide _ s := some s

/-- **Counterexample for `n = 1`.** With a single process, deciding the own input immediately is an
`f`-resilient `t`-two-step consensus protocol (for every `f`, `t`, `δ`). -/
theorem single_fastConsensus (hP : Fintype.card P = 1) (f t δ : ℕ) :
    FastConsensus (selfDecide P V) (Auth.none P Unit) f t δ := by
  have hsub : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp hP.le
  have hst : ∀ (R : Run P Unit V) τ p, R.st (selfDecide P V) τ p = R.inp p := by
    intro R τ p
    induction τ with
    | zero => rfl
    | succ τ ih => rw [Run.st_succ]; exact ih
  have hdec : ∀ (R : Run P Unit V) p v, R.Decides (selfDecide P V) p v → v = R.inp p := by
    rintro R p v ⟨τ, hτ⟩
    rw [hst] at hτ
    exact (Option.some.inj hτ).symm
  refine ⟨⟨fun R _ _ p _ => ⟨R.inp p, 0, rfl⟩, ?_, ?_⟩, ?_⟩
  · intro R _ _ p _ q _ v w hv hw
    rw [hdec R p v hv, hdec R q w hw, Subsingleton.elim p q]
  · intro R _ _ p hp v hv x hx
    have := hx p
    simp only [Run.inputConf, hp, ite_false, Option.some.injEq] at this
    rw [hdec R p v hv, this]
  · intro I T _ x _
    exact ⟨I x, 0, Nat.zero_le _, rfl⟩

/-- Theorem 4.5 as literally stated ("no `f`-resilient `t`-two-step consensus protocol for
`3f + 2t − 2` processes", with `t ≤ f`) is false for `f = 1`, `t = 0`. -/
theorem theorem_4_5_fails_f1_t0 (hP : Fintype.card P = 3 * 1 + 2 * 0 - 2) (δ : ℕ) :
    FastConsensus (selfDecide P V) (Auth.none P Unit) 1 0 δ :=
  single_fastConsensus hP 1 0 δ

end FastByzantineConsensus
