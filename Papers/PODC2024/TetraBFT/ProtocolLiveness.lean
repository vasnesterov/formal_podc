import Papers.PODC2024.TetraBFT.Validity
import Papers.PODC2024.TetraBFT.Liveness

/-!
# Lemmas 2 and 4 for the message-level protocol

The combinatorial liveness lemmas, transferred to runs of `tetra prm` (any run, no timing
assumption):

* `leader_determines_safe` (**Lemma 2**): a node that has received suggest messages for its current
  view from all correct nodes determines some value safe by Rule 1; so a correct leader in that
  situation proposes (`proposeVal_isSome`).
* `follower_determines_safe` (**Lemma 4**): a node in view `v ≥ 1` that has received a proposal for
  `v` from a *correct* leader of `v` and proof messages for `v` from all correct nodes determines
  the proposed value safe by Rule 3, so it casts its vote-1 for it.

What is *not* formalized is the timing part of the liveness argument (that after GST all correct
nodes eventually spend long enough together in a view with a correct leader); in fact this part
fails for the view-change rule of the paper (`Counterexample.lean`).
-/

set_option linter.unusedSectionVars false

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

variable {n : ℕ} {V : Type} [DecidableEq V] {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

/-- **Lemma 2** (protocol level). -/
theorem leader_determines_safe (hn : 3 * prm.f < n) (hR : R.faulty.card ≤ prm.f) (x₀ : V)
    {τ : ℕ} {p : Fin n}
    (hall : ∀ q ∉ R.faulty, q ∈ repSenders (R.st A τ p).rcv (getSuggest (R.st A τ p).view)) :
    ∃ x, leaderSafe prm (R.st A τ p) x := by
  have hE := toExec_safetyHyp (prm := prm) R hR
  obtain ⟨x, hx⟩ := Execution.lemma2 (E := toExec (prm := prm) R) (by simpa using hn) hE x₀ hall
    (fun q hq hqF => by
      obtain ⟨τ', -, hm⟩ := rcv_authentic R hqF (mem_of_repSenders_suggest hq)
      exact suggest_honest R hm)
  exact ⟨x, by simpa [leaderSafe] using hx⟩

/-- A leader that determines some value safe proposes. -/
theorem proposeVal_isSome {s : St n V} (h : ∃ x, leaderSafe prm s x) :
    (proposeVal prm s).isSome := by
  unfold proposeVal
  split_ifs <;> simp

/-- **Lemma 4** (protocol level). -/
theorem follower_determines_safe (hn : 3 * prm.f < n) (hR : R.faulty.card ≤ prm.f) {τ : ℕ}
    {j : Fin n} {x : V} (hv : (R.st A τ j).view ≠ 0)
    (hℓ : prm.leader (R.st A τ j).view ∉ R.faulty)
    (hprop : (prm.leader (R.st A τ j).view, Msg.proposal (R.st A τ j).view x) ∈ (R.st A τ j).rcv)
    (hall : ∀ q ∉ R.faulty, q ∈ repSenders (R.st A τ j).rcv (getProof (R.st A τ j).view)) :
    nodeSafe prm (R.st A τ j) x := by
  have hE := toExec_safetyHyp (prm := prm) R hR
  obtain ⟨τ', -, hm⟩ := rcv_authentic R hℓ hprop
  obtain ⟨h0 | hL, -⟩ := (st_inv (prm := prm) R τ' _).out _ hm
  · exact absurd h0 hv
  have := Execution.lemma4 (E := toExec (prm := prm) R) (by simpa using hn) hE
    (by simpa using hL)
    (fun q hq hqF => by
      obtain ⟨τ'', -, hm'⟩ := rcv_authentic R hqF (mem_of_repSenders_suggest hq)
      exact suggest_honest R hm')
    hall
    (fun q hq hqF => by
      obtain ⟨τ'', -, hm'⟩ := rcv_authentic R hqF (mem_of_repSenders hq)
      exact proof_honest R hm')
  simpa [nodeSafe] using this

end TetraBFT
