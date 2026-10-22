import Papers.PODC2014.AbstractMACConsensus.UnknownSize
import Papers.PODC2014.AbstractMACConsensus.Networks

/-!
# Theorem 3.3: anonymous consensus is impossible (even knowing `n` and `D`)

Newport, *Consensus with an abstract MAC layer*, PODC 2014, Section 3.2.

Given the networks of `Nets D n` (`Networks.lean`): `B` and `A` have the same size and diameter;
`A` contains two copies of a gadget joined through a bridge node `q`, and `B` covers each copy.
In `A`, hold `q`'s broadcast for `t` rounds, where `t` is such that in the synchronous executions
of `B` with constant inputs everyone has decided (Lemma 3.5). During these rounds, each node of
copy `b` behaves like its preimages in `B` with all inputs `b` (Lemma 3.6, an instance of
`syncLoc_comp`), so copy `0` decides `0` and copy `1` decides `1`.

Anonymous algorithms are those with trivial identities (`I = Unit`); knowledge of `n` and `D` is
implicit (the algorithm only has to work on networks of size `n` and diameter `D`).
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC Filter SimpleGraph

variable {M S : Type*}

/-- **Lemma 3.6 + proof of Theorem 3.3**, for given networks: no anonymous algorithm solves
consensus in all networks of diameter `D` and size `n`. -/
theorem not_solves_of_nets {D n : ℕ} (N : Nets D n) (A : Algorithm Unit M S) :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected → G.diam = D → SolvesConsensus A G (fun _ => ()) 0 := by
  intro H
  let _ := N.fA; let _ := N.dA; let _ := N.fB; let _ := N.dB; let _ := N.rA; let _ := N.rB
  have hA := H N.VA N.GA N.cardA N.connA N.diamA
  have hB := H N.VB N.GB N.cardB N.connB N.diamB
  -- Lemma 3.5 in `B`
  obtain ⟨t0, ht0⟩ := sync_decided A (fun _ => ()) hB false
  obtain ⟨t1, ht1⟩ := sync_decided A (fun _ => ()) hB true
  set t := max t0 t1
  -- the execution `α_A`
  let Hq : ℕ → N.VA → Bool := fun j x => decide (j < t ∧ x = N.q)
  let inp : N.VA → Bool := fun x => decide (∃ v, N.p true v = x)
  let Hn : ℕ → N.VB → Bool := fun _ _ => false
  have hinp : ∀ b v, inp (N.p b v) = b := by
    intro b v
    cases b
    · simp only [inp, decide_eq_false_iff_not, not_exists]
      exact fun w h => N.p_disj v w h.symm
    · simp only [inp, decide_eq_true_eq]; exact ⟨v, rfl⟩
  -- Lemma 3.6: copy `b` of `A` behaves like `B` with all inputs `b`
  have sim : ∀ b v, syncLoc A N.GA Hq (fun v => A.initNode () (inp v)) t (N.p b v) =
      syncLoc A N.GB Hn (fun _ => A.initNode () b) t v := by
    intro b
    refine syncLoc_comp A (N.p b) Hq Hn _ _ t (fun j hj v' => ?_) (fun j _ v' => ?_)
      (fun v' => by simp [hinp]) t le_rfl
    · have := N.cover b v'
      convert this using 3
      · simp [Hq, hj]
      · simp [Hn]
    · simp [Hq, Hn, N.p_ne_q]
  obtain ⟨w⟩ := N.connB.nonempty
  have d0 : (syncLoc A N.GA Hq (fun v => A.initNode () (inp v)) t (N.p false w)).dec =
      some false := by
    rw [sim]; exact syncLoc_dec_mono (ht0 w) (le_max_left _ _)
  have d1 : (syncLoc A N.GA Hq (fun v => A.initNode () (inp v)) t (N.p true w)).dec =
      some true := by
    rw [sim]; exact syncLoc_dec_mono (ht1 w) (le_max_right _ _)
  -- `α_A` is admissible, so agreement must hold in it
  let c₀ := Config.init A (fun _ : N.VA => ()) inp
  have hfair := syncSched_fair Hq c₀ rfl (fun _ => rfl) t
    (fun j hj x => by simp [Hq]; omega) (A := A) (G := N.GA)
  obtain ⟨T, hT, hT'⟩ := hfair.exists_timely
  obtain ⟨hAg, -, -⟩ := hA inp _ T 2 hT hT' (fun i => by rw [syncSched_down]; simp)
  have := hAg t t (N.p false w) (N.p true w) false true (by rw [syncSched_loc]; exact d0)
    (by rw [syncSched_loc]; exact d1)
  simp at this

/-- **Theorem 3.3.** For every even diameter `D ≥ 4` and size `n ≥ D` there is `n'` with
`n ≤ n' ≤ 8 n` such that no anonymous algorithm solves consensus in all networks of diameter `D`
and size `n'` (the paper: "for some constant `c`"; here `c = 8`). -/
theorem theorem_3_3 (D n : ℕ) (hD : Even D) (hD4 : 4 ≤ D) (hn : D ≤ n) :
    ∃ n', n ≤ n' ∧ n' ≤ 8 * n ∧ ∀ A : Algorithm Unit M S,
      ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n' → G.Connected → G.diam = D → SolvesConsensus A G (fun _ => ()) 0 := by
  obtain ⟨k, rfl⟩ := hD
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 1 := ⟨k - 1, by omega⟩
  obtain ⟨N⟩ := exists_nets d n (by omega)
  refine ⟨3 * (n + d + 5), by omega, by omega, fun A => ?_⟩
  have hD' : d + 1 + (d + 1) = 2 * d + 2 := by ring
  rw [hD']
  exact not_solves_of_nets N A

end Podc.AbstractMACConsensus
