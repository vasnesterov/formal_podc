import Mathlib

/-!
# Appendix A: reliable broadcast implements unidirectionality when `f = 1` and `n ≥ 3`

The two-phase protocol of Appendix A: phase 1 — send the signed input to all and wait for valid
phase-1 messages from `n - 1` distinct processes; phase 2 — forward everything received and wait
for phase-2 messages from `n - 1` distinct processes, each containing `m ≥ 2` validly signed values
from distinct processes. A process receives `q`'s message if it got `q`'s phase-1 message or a
phase-2 message containing it.

We formalize the end-of-round argument (`Round`): `P1 x` = senders of the phase-1 messages `x` got
in phase 1, `P2 x` = senders of the phase-2 messages it got in phase 2, `content z` = signers of
the values in `z`'s phase-2 message. Reliable broadcast makes `content z` the same for all
receivers even for Byzantine `z`; for correct `z` it contains `P1 z` (forward all); for Byzantine
`z` it has at least two signers (the validity check). Signatures make the contents genuine; they
play no role in the timing argument and are not modelled.

`appendix_claim`: for `f ≤ 1`, `n ≥ 3`, any two correct processes satisfy unidirectionality.
The paper's proof says "all processes in `Q` must receive at least one of `p` or `p'`'s messages
in phase 1, w.l.o.g. `p`'s" — this is false for a Byzantine member of `Q` and the w.l.o.g. is not
justified (different members of `Q` may see different values); the proof below picks a correct
member of `Q` when `n ≥ 4` and uses the `m ≥ 2` check plus reliable broadcast when `n = 3`.
-/

namespace Podc.TrustedHW

namespace AppendixRB

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The end-of-round data of one execution of the Appendix A protocol. -/
structure Round (P : Type) where
  /-- Byzantine processes. -/
  F : Finset P
  /-- Phase-1 senders received by `x` in phase 1. -/
  P1 : P → Finset P
  /-- Signers contained in `z`'s phase-2 message (the same for every receiver, by RB). -/
  content : P → Finset P
  /-- Phase-2 senders received by `x` in phase 2. -/
  P2 : P → Finset P

/-- The constraints of the protocol. -/
structure Valid (R : Round P) : Prop where
  card_P1 : ∀ x, x ∉ R.F → Fintype.card P - 1 ≤ (R.P1 x).card
  forward : ∀ x, x ∉ R.F → R.P1 x ⊆ R.content x
  two_signers : ∀ z, 2 ≤ (R.content z).card
  card_P2 : ∀ x, x ∉ R.F → Fintype.card P - 1 ≤ (R.P2 x).card

/-- `x` received `y`'s round message (directly in phase 1 or inside a phase-2 message). -/
def Recv (R : Round P) (x y : P) : Prop := y ∈ R.P1 x ∨ ∃ z ∈ R.P2 x, y ∈ R.content z

lemma eq_erase_of_card {s : Finset P} {a : P} (hs : Fintype.card P - 1 ≤ s.card) (ha : a ∉ s) :
    s = Finset.univ.erase a := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; rintro rfl; exact ha hx
  · rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]; exact hs

/-- **Claim of Appendix A**: with at most one Byzantine process and `n ≥ 3`, for any two correct
processes `p ≠ p'`, `p` receives `p'`'s message or `p'` receives `p`'s before ending the round. -/
theorem appendix_claim {R : Round P} (hR : Valid R) (hF : R.F.card ≤ 1)
    (hn : 3 ≤ Fintype.card P) {p p' : P} (hp : p ∉ R.F) (hp' : p' ∉ R.F) (hpp : p ≠ p') :
    Recv R p p' ∨ Recv R p' p := by
  by_contra hcon
  simp only [Recv, not_or, not_exists, not_and] at hcon
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
  -- `P1 p' = univ \ {p}`, so `p' ∈ content p'`
  have hP1p' := eq_erase_of_card (hR.card_P1 p' hp') h3
  have hP1p := eq_erase_of_card (hR.card_P1 p hp) h1
  have hp'c : p' ∈ R.content p' := hR.forward p' hp' (by rw [hP1p']; simp [Ne.symm hpp])
  have hpc : p ∈ R.content p := hR.forward p hp (by rw [hP1p]; simp [hpp])
  have hP2p : p' ∉ R.P2 p := fun h => h2 p' h hp'c
  have hP2p' : p ∉ R.P2 p' := fun h => h4 p h hpc
  have eP2p := eq_erase_of_card (hR.card_P2 p hp) hP2p
  have eP2p' := eq_erase_of_card (hR.card_P2 p' hp') hP2p'
  -- the other processes `Q`
  set Q := (Finset.univ.erase p).erase p' with hQ
  have hQcard : Q.card = Fintype.card P - 2 := by
    rw [hQ, Finset.card_erase_of_mem (by simp [Ne.symm hpp]),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  have hmemQ : ∀ z, z ∈ Q ↔ z ≠ p ∧ z ≠ p' := by intro z; simp [hQ, and_comm]
  -- some `z ∈ Q` has `p` or `p'` in its phase-2 content
  obtain ⟨z, hzQ, hz⟩ : ∃ z ∈ Q, p ∈ R.content z ∨ p' ∈ R.content z := by
    by_cases hc : ∃ z ∈ Q, z ∉ R.F
    · obtain ⟨z, hzQ, hzF⟩ := hc
      refine ⟨z, hzQ, ?_⟩
      by_contra hn'
      push Not at hn'
      have hsub : R.P1 z ⊆ Q := by
        intro x hx; rw [hmemQ]
        exact ⟨fun h => hn'.1 (h ▸ hR.forward z hzF hx), fun h => hn'.2 (h ▸ hR.forward z hzF hx)⟩
      have := Finset.card_le_card hsub
      have := hR.card_P1 z hzF
      omega
    · push Not at hc
      have hQF : Q ⊆ R.F := hc
      have hQ1 : Q.card ≤ 1 := (Finset.card_le_card hQF).trans hF
      obtain ⟨z, hzQ⟩ : Q.Nonempty := by rw [← Finset.card_pos]; omega
      refine ⟨z, hzQ, ?_⟩
      by_contra hn'
      push Not at hn'
      have hsub : R.content z ⊆ Q := by
        intro x hx; rw [hmemQ]
        exact ⟨fun h => hn'.1 (h ▸ hx), fun h => hn'.2 (h ▸ hx)⟩
      have := Finset.card_le_card hsub
      have := hR.two_signers z
      omega
  rw [hmemQ] at hzQ
  rcases hz with hz | hz
  · exact h4 z (by rw [eP2p']; simpa using hzQ.1) hz
  · exact h2 z (by rw [eP2p]; simpa using hzQ.2) hz

/-- Liveness core: with `f ≤ 1` there are `n - 1` correct processes, whose phase-1 and phase-2
messages suffice to end both phases, and a correct process forwards at least `n - 1 ≥ 2` values. -/
theorem appendix_live_core {F : Finset P} (hF : F.card ≤ 1) (hn : 3 ≤ Fintype.card P) :
    Fintype.card P - 1 ≤ (Finset.univ \ F).card ∧ 2 ≤ Fintype.card P - 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]; omega

/-- Non-vacuity: a round satisfying the hypotheses (`n = 3`, process `2` Byzantine with phase-2
content `{0, 2}`). -/
theorem valid_nonvacuous :
    ∃ R : Round (Fin 3), Valid R ∧ R.F.card ≤ 1 :=
  ⟨⟨{2}, fun _ => Finset.univ, fun z => if z = 2 then {0, 2} else Finset.univ,
      fun _ => Finset.univ⟩,
    ⟨fun _ _ => by simp, fun x hx => by simp at hx; simp [hx], fun z => by
      by_cases h : z = 2 <;> simp [h], fun _ _ => by simp⟩, by decide⟩

end AppendixRB

end Podc.TrustedHW
