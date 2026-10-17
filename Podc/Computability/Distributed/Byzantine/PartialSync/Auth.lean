import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/PartialSync/Auth.lean (append to the
-- existing file)

/-!
# Replay lemmas restricted to the messages that matter

Additions to `Cslib/Computability/Distributed/Byzantine/PartialSync/Auth.lean`. A Byzantine process
of a run `R'` often *replays* what it sent, as a correct process, in a reference run `Ri`. CSLib's
`Run.tokens_replay` justifies this (`Run.AuthValid`) when all messages of `Ri` up to some time are
reproducible. The versions here only require it for the messages that can actually influence the
replayed ones, and allow tokens to be emitted in `R'` as late as their **delivery** time in `Ri`:

* `Run.tokens_replay_rel` (master lemma): the replayed events form a set `Rel` of (sender, time)
  pairs that is causally closed, up to batches whose tokens are already available in `R'`;
* `Run.tokens_replay_dl`: the special case `Rel q σ ↔ σ ≤ T` (every batch delivered in `Ri` before
  the replay horizon `T`).

This is needed when correct processes behave differently in `Ri` and `R'` from some time on, or
start at different times (unsynchronized start).
-/

namespace Cslib.Byzantine.PartialSync

namespace Run

variable {P M S VI VO K : Type*} [DecidableEq P] {Au : Auth P M K} {A : Algorithm P M S VI VO}

/-- A token emitted by an `R'`-correct process `q` at time `σ'` (as part of a message to `r'`) is
in `R'.honestTokens` from time `σ'` on. -/
theorem mem_honestTokens_of_out {R' : Run P M VI} {q r' : P} {σ' τ : ℕ} (hq : q ∉ R'.faulty)
    (hσ : σ' ≤ τ) {m : M} (hm : m ∈ R'.out A q σ' r') {x : K} (hx : x ∈ Au.tokens m) :
    x ∈ R'.honestTokens Au A τ :=
  ⟨σ', hσ, q, hq, r', m, hm, hx⟩

/-- **Replay lemma restricted to a causally closed set of events.** `Rel q σ` marks the (send)
events whose messages may be replayed. If, for every such event of an `Ri`-correct process, every
batch it has received is either sent by an `Ri`-correct, `R'`-Byzantine process at a marked event,
or carries only tokens that are `R'`-Byzantine-signed or emitted by `R'`-correct processes by its
delivery time, then replayed messages respect unforgeability in `R'`. -/
theorem tokens_replay_rel (hU : A.Unforging Au) {Ri R' : Run P M VI} (Rel : P → ℕ → Prop)
    (h : ∀ q σ, Rel q σ → q ∉ Ri.faulty → ∀ q' σ', σ' ≤ Ri.dl q' σ' q → Ri.dl q' σ' q < σ →
      (q' ∈ R'.faulty ∧ q' ∉ Ri.faulty ∧ Rel q' σ') ∨
      ∀ m ∈ Ri.out A q' σ' q, ∀ x ∈ Au.tokens m,
        Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A (Ri.dl q' σ' q)) :
    ∀ σ q, Rel q σ → q ∉ Ri.faulty → q ∈ R'.faulty → ∀ r, ∀ m ∈ Ri.out A q σ r,
      ∀ x ∈ Au.tokens m, Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A σ := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro q hR hq hq' r m hm x hx
    rw [out_of_correct A Ri hq] at hm
    rcases hU Ri q σ r m hm x hx with hs | ⟨τ', hτ', q', m', hm', hx'⟩
    · exact Or.inl (hs ▸ hq')
    · obtain ⟨σ', hσ', hdl, hm''⟩ := mem_inbox.mp hm'
      rcases h q σ hR hq q' σ' (by omega) (by omega) with ⟨h1, h2, h3⟩ | h4
      · rcases ih σ' (by omega) q' h3 h2 h1 q m' hm'' x hx' with e | e
        · exact Or.inl e
        · exact Or.inr (honestTokens_mono (by omega) e)
      · rcases h4 m' hm'' x hx' with e | e
        · exact Or.inl e
        · exact Or.inr (honestTokens_mono (by omega) e)

/-- **Replay lemma (delivery-time version).** The hypothesis of `Run.tokens_replay` is only
required for batches that are delivered in `Ri` before the replay horizon `T`, and the tokens of
such a batch may be emitted in `R'` as late as its delivery time in `Ri`. -/
theorem tokens_replay_dl (hU : A.Unforging Au) {Ri R' : Run P M VI} {T : ℕ}
    (h : ∀ q σ r, Ri.dl q σ r < T → σ ≤ Ri.dl q σ r → (q ∈ R'.faulty ∧ q ∉ Ri.faulty) ∨
      ∀ m ∈ Ri.out A q σ r, ∀ x ∈ Au.tokens m,
        Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A (Ri.dl q σ r)) :
    ∀ σ ≤ T, ∀ q, q ∉ Ri.faulty → q ∈ R'.faulty → ∀ r, ∀ m ∈ Ri.out A q σ r,
      ∀ x ∈ Au.tokens m, Au.signer x ∈ R'.faulty ∨ x ∈ R'.honestTokens Au A σ :=
  fun σ hσ q hq hq' => tokens_replay_rel hU (fun _ σ => σ ≤ T)
    (fun q σ hσ _ q' σ' h1 h2 => (h q' σ' q (by omega) h1).imp_left fun h => ⟨h.1, h.2, by omega⟩)
    σ q hσ hq hq'

end Run

end Cslib.Byzantine.PartialSync
