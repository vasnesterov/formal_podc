import Papers.PODC2021.GoodCaseLatencyBB.Basic

/-!
# Replaying messages of another run without forging signatures

A Byzantine process `b` of a run `R'` often *replays* what it sent, as a correct process, in a
reference run `Ri`. Such a replay is legal (`Run.AuthValid`) if every token in the replayed
messages was signed by an `R'`-Byzantine process or already emitted by an `R'`-correct process.

`tokens_replay_dl` is a refinement of CSLib's `Run.tokens_replay`: the hypothesis is only required
for batches that are **delivered in `Ri` before the replay horizon `T`**, and the emission time of
the tokens of such a batch may be as late as its **delivery time** in `Ri` (not its sending time).
This is needed when correct processes behave differently in `Ri` and `R'` from some time on, or
start later in `R'` (unsynchronized start): their later messages never reach the replaying process
in `Ri` before the horizon, so they need not be reproducible. -/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

-- CSLib candidate
/-- **Replay lemma (delivery-time version).** -/
theorem tokens_replay_dl {Au : Auth P M K} {A : Algorithm P M S V V} (hU : A.Unforging Au)
    {Ri R' : Run P M V} {T : ℕ}
    (h : ∀ q σ r, Ri.dl q σ r < T → σ ≤ Ri.dl q σ r → (q ∈ R'.faulty ∧ q ∉ Ri.faulty) ∨
      ∀ m ∈ Ri.out A q σ r, ∀ x ∈ Au.tokens m,
        Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A (Ri.dl q σ r)) :
    ∀ σ ≤ T, ∀ q, q ∉ Ri.faulty → q ∈ R'.faulty → ∀ r, ∀ m ∈ Ri.out A q σ r,
      ∀ x ∈ Au.tokens m, Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A σ := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro hσ q hq hq' r m hm x hx
    rw [Run.out_of_correct A Ri hq] at hm
    rcases hU Ri q σ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
    · exact Or.inl (hs ▸ hq')
    · obtain ⟨σ', hσ', hdl, hm''⟩ := Run.mem_inbox.mp hm'
      rcases h q' σ' q (by omega) (by omega) with ⟨h1, h2⟩ | h3
      · rcases ih σ' (by omega) (by omega) q' h2 h1 q m' hm'' x hx' with e | e
        · exact Or.inl e
        · exact Or.inr (Run.honestTokens_mono (by omega) e)
      · rcases h3 m' hm'' x hx' with e | e
        · exact Or.inl e
        · exact Or.inr (Run.honestTokens_mono (by omega) e)

/-- A token emitted by an `R'`-correct process `q` at time `σ'` (as part of a message to `r'`) is
in `R'.honestTokens` from time `σ'` on. -/
theorem mem_honestTokens_of_out {VI : Type*} {Au : Auth P M K} {A : Algorithm P M S VI V}
    {R' : Run P M VI}
    {q r' : P} {σ' τ : ℕ} (hq : q ∉ R'.faulty) (hσ : σ' ≤ τ) {m : M} (hm : m ∈ R'.out A q σ' r')
    {x : K} (hx : x ∈ Au.tokens m) : x ∈ R'.honestTokens Au A τ :=
  ⟨σ', hσ, q, hq, r', m, hm, hx⟩

end GoodCaseLatencyBB
