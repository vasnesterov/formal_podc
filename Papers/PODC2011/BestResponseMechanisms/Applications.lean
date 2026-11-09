import Papers.PODC2011.BestResponseMechanisms.Mechanism
import Papers.PODC2011.BestResponseMechanisms.CostSharing
import Papers.PODC2011.BestResponseMechanisms.BGP
import Papers.PODC2011.BestResponseMechanisms.StableRoommates

/-!
# The mechanisms of Section 3 via the corrected Theorem 2.7

The round-robin mechanisms of Theorems 3.2 and 3.4 run for `n²` time steps, i.e. `n` rounds of
round robin. The corrected Theorem 2.7 (`theorem_2_7_incentive_compatible`) needs
`max(e_G, kᵢ)` rounds, `kᵢ` the clear-outcome witness indices; in all applications these are
`≤ n`, so the mechanisms of Section 3 are incentive compatible as claimed.
-/

open Set Function Cslib.GameTheory TieBreakGame
open scoped NNReal

namespace Podc.BestResponseMechanisms

/-- From `e_G ≤ m`, an elimination sequence of length `≤ m` exists. -/
lemma exists_solves_le_of_elimParam_le {ι : Type*} {S : ι → Type*} {R : Type*} [DecidableEq ι]
    [LinearOrder R] {G : TieBreakGame ι S R} (hS : G.NBRSolvable) {m : ℕ}
    (hm : G.elimParam ≤ m) : ∃ (E : ℕ → Subgame S) (r : ℕ) (s : ∀ i, S i), G.Solves E r s ∧ r ≤ m := by
  have hne : {r | ∃ (E : ℕ → Subgame S) (s : ∀ i, S i), G.Solves E r s}.Nonempty := by
    obtain ⟨E, r, s, h⟩ := hS; exact ⟨r, E, s, h⟩
  obtain ⟨E, s, h⟩ := Nat.sInf_mem hne
  exact ⟨E, _, s, h, hm⟩

namespace CostSharing.CostSharingRule

/-- **Theorem 3.4 of [NSVZ].** The round-robin cost-sharing mechanism with `n` users (`Fin n`),
any starting bids, in which every user bids `mechBid` ("the minimal bid `≤ vᵢ` with which `i` is
serviced, else `vᵢ`"), stops after `n²` steps at the outcome `s*` of Theorem 3.3 (serviced set =
Moulin's set, each serviced user pays its Moulin cost share `≤ vⱼ`), and is incentive compatible
(ex post: for every realization `v` of the values). -/
theorem theorem_3_4 {n : ℕ} (C : CostSharingRule (Fin (n + 1))) (v : Fin (n + 1) → ℝ≥0)
    (init : Fin (n + 1) → ℝ≥0) :
    IsIncentiveCompatible (C.game v) (roundRobin init) (C.mechBid v) ((n + 1) * (n + 1)) ∧
      (roundRobin init).prof (brStrategy (roundRobin init) (C.mechBid v)) ((n + 1) * (n + 1)) =
        C.outcome v ∧
      C.serviced (C.outcome v) = C.moulinSet v ∧
      ∀ j ∈ C.moulinSet v, C.outcome v j = C.c j (C.moulinSet v) ∧ C.c j (C.moulinSet v) ≤ v j := by
  obtain ⟨h1, huniq, -, hserv, hpay, -, -, hcard, -⟩ := C.theorem_3_3 v
  obtain ⟨E, r, s, hE, hr⟩ := exists_solves_le_of_elimParam_le ⟨_, _, _, h1⟩ hcard
  have hs : s = C.outcome v := huniq E r s hE
  subst hs
  have := theorem_2_7_incentive_compatible (roundRobin init) hE (m := n + 1)
    (by simpa using hr) (fun i => ⟨_, 4, 1, by omega, C.clearWitness v i⟩)
    (fun i b => C.isBR_mechBid v i b) (fun σ => roundRobin_hasRounds init σ (n + 1))
  exact ⟨this.1, this.2, hserv, hpay⟩

end CostSharing.CostSharingRule

namespace StableRoommates

/-- **Theorem 3.2 of [NSVZ].** For a cycle-free stable-roommates game with `n` students (`Fin n`;
this covers correlated markets and the bipartite intern–hospital markets, see
`theorem_3_1_correlated`, `theorem_3_1_internHospital`), the round-robin mechanism with `n²`
steps in which every student plays a tie-broken best response (`br`; the paper's "announce your
favourite student to whom you can make a better offer" is one when such a student exists,
`mechanism_isBR`) ends at a profile whose matching is stable, and it is incentive compatible in
ex-post Nash, from any starting profile. -/
theorem theorem_3_2 {n : ℕ} {acc : Fin (n + 1) → Fin (n + 1) → Prop}
    {α : Fin (n + 1) → Fin (n + 1) → ℕ}
    (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i))
    (br : ∀ i, (∀ j, Strat acc j) → Strat acc i) (hbr : IsBRRule (game acc α prec) br)
    (init : ∀ i, Strat acc i) :
    IsIncentiveCompatible (game acc α prec) (roundRobin init) br ((n + 1) * (n + 1)) ∧
      IsStable acc α (matchingOf ((roundRobin init).prof (brStrategy (roundRobin init) br)
        ((n + 1) * (n + 1)))) := by
  obtain ⟨E, r, s, hE, hr, hW, -, -, hstab⟩ :=
    theorem_3_1 hsymm hirr hpos hinj hcf prec hne
  have hr' : r ≤ n + 1 := by simpa using hr
  have := theorem_2_7_incentive_compatible (roundRobin init) hE hr'
    (fun i => by obtain ⟨k, hk, hWi⟩ := hW i; exact ⟨E, r, k, hk.trans hr', hWi⟩) hbr
    (fun σ => roundRobin_hasRounds init σ (n + 1))
  exact ⟨this.1, by rw [this.2]; exact hstab⟩

end StableRoommates

namespace BGP

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {d : V}

/-- **Theorem 3.5 of [NSVZ] ([Levin–Schapira–Zohar]), via Theorems 3.6 and 2.7 (corrected).**
In a connected network with No Dispute Wheel, for every tie-breaking rule there is a stable
routing tree `s` such that every best-response mechanism (BGP: every node repeatedly picks its
best available route given the neighbours' current routes) in which every run has at least
`n` rounds by the horizon `N` (`n` = number of source nodes; any starting point, any adaptive
activation order, simultaneous activations allowed) ends at `s` and is incentive compatible in
ex-post Nash. -/
theorem theorem_3_5 (ρ : Rankings G d) (hconn : G.Connected) (hndw : NoDisputeWheel G d ρ.rank)
    (prec : ∀ i : Player d, Strategy G d i → Strategy G d i → Prop) :
    ∃ s : Profile G d, IsRoutingTree s ∧
      ∀ (M : Mechanism (Strategy G d)) (br : ∀ i, Profile G d → Strategy G d i) (N : ℕ),
        IsBRRule (bgpGame G d ρ prec) br →
        (∀ σ, HasRounds (M.acts σ) N (Fintype.card (Player d))) →
        IsIncentiveCompatible (bgpGame G d ρ prec) M br N ∧ M.prof (brStrategy M br) N = s := by
  obtain ⟨E, r, s, hE, hr, htree, -, -, hW⟩ := theorem_3_6 ρ hconn hndw prec
  refine ⟨s, htree, fun M br N hbr hR => theorem_2_7_incentive_compatible M hE hr
    (fun i => ?_) hbr hR⟩
  obtain ⟨k, hk, hWi⟩ := hW i
  exact ⟨E, r, k, hk.trans hr, hWi⟩

end BGP

end Podc.BestResponseMechanisms
