import Podc.Computability.Distributed.AbstractMAC.Sync
import Cslib.Foundations.Combinatorics.SimpleGraph.PathGraph

/-!
# Theorem 3.10: consensus needs `⌊D/2⌋ F_ack` time

Newport, *Consensus with an abstract MAC layer*, PODC 2014, Section 3.4.

On the line `u₀, …, u_D` (`pathGraph (D + 1)`, diameter `D`), run the synchronous scheduler that
waits the maximal time `F` between rounds (round `j` at time `j F`). Before time `⌊D/2⌋ F` the
endpoints only depend on the inputs of their own half of the line; with input `0` on the first half
and `1` on the second, validity (in the all-`0` / all-`1` executions) and indistinguishability force
the endpoints to decide differently.

The result holds for every algorithm that is only required to work on this one network (so even
with unique ids and knowledge of `n` and `D`).
-/

namespace Podc.AbstractMACConsensus

open Cslib.AbstractMAC Filter SimpleGraph

variable {I M S : Type*}

/-- A walk on the line moves by at most one position per step. -/
lemma pathGraph_walk_dist {n : ℕ} {v w : Fin n} (q : (pathGraph n).Walk v w) :
    (v : ℕ) ≤ w + q.length ∧ (w : ℕ) ≤ v + q.length := by
  induction q with
  | nil => simp
  | cons h q ih =>
    rw [pathGraph_adj] at h
    simp only [Walk.length_cons]
    omega

/-- **Theorem 3.10.** For every algorithm solving consensus on the line of diameter `D` and every
bound `F > 0` on the acknowledgment delay, there is a timely, crash-free execution (with diverging
time) in which some node has not decided before time `⌊D/2⌋ F`. -/
theorem theorem_3_10 (D : ℕ) (A : Algorithm I M S) (id : Fin (D + 1) → I)
    (H : SolvesConsensus A (pathGraph (D + 1)) id 0) {F : ℝ} (hF : 0 < F) :
    ∃ (inp : Fin (D + 1) → Bool) (σ : ℕ → List (Event (Fin (D + 1)))) (T : ℕ → ℝ),
      Timely A (pathGraph (D + 1)) (Config.init A id inp) σ T F ∧ Tendsto T atTop atTop ∧
      (∀ i, (run A (pathGraph (D + 1)) (Config.init A id inp) σ i).down = ∅) ∧
      ∃ u, ∀ i, ((run A (pathGraph (D + 1)) (Config.init A id inp) σ i).loc u).dec.isSome →
        ((D / 2 : ℕ) : ℝ) * F ≤ T i := by
  set h := D / 2
  let Hn : ℕ → Fin (D + 1) → Bool := fun _ _ => false
  -- the synchronous execution with maximal delays, for any input vector
  have hT : ∀ inp : Fin (D + 1) → Bool,
      Timely A (pathGraph (D + 1)) (Config.init A id inp) (syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp))
        (fun i => i * F) F :=
    fun inp => syncSched_timely Hn _ rfl (fun _ => rfl) (fun _ _ => rfl) hF.le
  have hcons : ∀ inp : Fin (D + 1) → Bool,
      Agreement A (pathGraph (D + 1)) (Config.init A id inp) (syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp)) ∧
      Validity A (pathGraph (D + 1)) inp (Config.init A id inp) (syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp)) :=
    fun inp => by
      obtain ⟨h1, h2, -⟩ := H inp _ _ F (hT inp) (tendsto_mul_const hF)
        (fun i => by rw [syncSched_down]; simp)
      exact ⟨h1, h2⟩
  let inp : Fin (D + 1) → Bool := fun j => decide (h ≤ (j : ℕ))
  refine ⟨inp, syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp), fun i => i * F, hT inp,
    tendsto_mul_const hF, syncSched_down Hn id inp, ?_⟩
  by_contra hcon
  push Not at hcon
  -- an endpoint deciding early decides like in a constant-input execution
  have early : ∀ (u : Fin (D + 1)) (b : Bool) (i : ℕ), i < h →
      (∀ w : Fin (D + 1), (∀ q : (pathGraph (D + 1)).Walk u w, q.length ≤ i → inp w = b)) →
      ((run A (pathGraph (D + 1)) (Config.init A id inp) (syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp)) i).loc u).dec.isSome →
      ((run A (pathGraph (D + 1)) (Config.init A id inp) (syncSched A (pathGraph (D + 1)) Hn (Config.init A id inp)) i).loc u).dec =
        some b := by
    intro u b i _ hloc hdec
    rw [syncSched_loc] at hdec ⊢
    rw [syncLoc_congr_of_walk A Hn _ (fun v => A.initNode (id v) b) i u
      (fun w q hq => by simp [hloc w q hq])] at hdec ⊢
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hdec
    rw [hb']
    obtain ⟨w, hw⟩ := (hcons fun _ => b).2 i u b' (by rw [syncSched_loc]; exact hb')
    exact congrArg some hw.symm
  obtain ⟨i0, hi0, hlt0⟩ := hcon ⟨0, by omega⟩
  obtain ⟨i1, hi1, hlt1⟩ := hcon ⟨D, by omega⟩
  have hi0' : i0 < h := by
    have : (i0 : ℝ) < h := lt_of_mul_lt_mul_right hlt0 hF.le
    exact_mod_cast this
  have hi1' : i1 < h := by
    have : (i1 : ℝ) < h := lt_of_mul_lt_mul_right hlt1 hF.le
    exact_mod_cast this
  have d0 := early ⟨0, by omega⟩ false i0 hi0' (fun w q hq => by
    have := (pathGraph_walk_dist q).2
    change (w : ℕ) ≤ 0 + q.length at this
    simp only [inp, decide_eq_false_iff_not, not_le]
    omega) hi0
  have d1 := early ⟨D, by omega⟩ true i1 hi1' (fun w q hq => by
    have := (pathGraph_walk_dist q).1
    change D ≤ (w : ℕ) + q.length at this
    simp only [inp, decide_eq_true_eq]
    omega) hi1
  have := (hcons inp).1 i0 i1 _ _ _ _ d0 d1
  simp at this

end Podc.AbstractMACConsensus
