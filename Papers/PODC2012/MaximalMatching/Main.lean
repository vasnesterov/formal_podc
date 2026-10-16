import Papers.PODC2012.MaximalMatching.Greedy
import Cslib.Computability.Distributed.ColourSystem.MessagePassing

/-!
# Main results of Hirvonen–Suomela, *Distributed Maximal Matching: Greedy is Optimal* (PODC'12)

Two equivalent formulations of the model are covered.

1. **View-based model on colour systems** (the paper's formal model, §2.3): `theorem2`,
   `theorem6`, `lemma1`, `lemma5`, `corollary3` (files `Greedy.lean`, `LowerBound.lean`).
2. **Synchronous message passing on arbitrary `k`-edge-coloured networks** (the operational
   model of §1.2), here with the lower bound for **finite simple** networks
   (`theorem2_messagePassing`, `theorem6_messagePassing`, `corollary3_messagePassing`).
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox MPAlgorithm

variable {k : ℕ}

/-- **Lemma 1** in the message-passing model: the greedy algorithm, run as a full-information
message-passing algorithm for `k - 1` rounds, finds a maximal matching in **every**
`k`-edge-coloured network (finite or infinite, with or without cycles). -/
theorem lemma1_messagePassing :
    ∃ M : MPAlgorithm k, ∀ (α : Type) (G : ColouredGraph k α),
      G.IsMaximalMatching (M.out G (k - 1)) := by
  refine ⟨ofView greedy, fun α G => ?_⟩
  have h := isMaximalMatching_view lemma1.1 (fun V hV => lemma1.2 V hV) G
  have e : (ofView greedy).out G (k - 1) = fun a => greedy (G.view a) 1 :=
    funext fun a => out_ofView lemma1.1 G a
  rw [e]; exact h

/-- **Theorem 2** in the message-passing model, lower bound for finite networks: an `r`-round
deterministic algorithm that finds a maximal matching in every finite simple anonymous
`k`-edge-coloured network has `r ≥ k - 1`. -/
theorem theorem2_lower_messagePassing (M : MPAlgorithm k) (r : ℕ)
    (hM : ∀ (α : Type) [Finite α] (G : ColouredGraph k α), G.IsSimple →
      G.IsMaximalMatching (M.out G r)) : k - 1 ≤ r :=
  theorem2_lower (M.toAlgorithm r) r (M.hasRunningTime_toAlgorithm r)
    (fun _ hV => M.findsMaximalMatching_of_finite r (fun _ => False)
      (fun α _ G hs _ => hM α G hs) hV (fun _ h => h.elim))

/-- **Theorem 2** (message-passing model): `k - 1` rounds are necessary and sufficient. -/
theorem theorem2_messagePassing :
    (∃ M : MPAlgorithm k, ∀ (α : Type) (G : ColouredGraph k α),
      G.IsMaximalMatching (M.out G (k - 1))) ∧
    ∀ (M : MPAlgorithm k) (r : ℕ), (∀ (α : Type) [Finite α] (G : ColouredGraph k α),
      G.IsSimple → G.IsMaximalMatching (M.out G r)) → k - 1 ≤ r :=
  ⟨lemma1_messagePassing, theorem2_lower_messagePassing⟩

/-- **Theorem 6** in the message-passing model: for `k ≥ 3`, even on finite simple
`(k-1)`-regular `k`-edge-coloured networks, maximal matching needs `k - 1` rounds. -/
theorem theorem6_messagePassing (hk : 3 ≤ k) (M : MPAlgorithm k) (r : ℕ)
    (hM : ∀ (α : Type) [Finite α] (G : ColouredGraph k α), G.IsSimple → G.IsRegular (k - 1) →
      G.IsMaximalMatching (M.out G r)) : k - 1 ≤ r :=
  le_runningTime hk (M.toAlgorithm r) r (M.hasRunningTime_toAlgorithm r)
    (fun _ hV hreg => M.findsMaximalMatching_of_finite r (fun d => d = k - 1)
      (fun α _ G hs hd => hM α G hs (hd _ rfl)) hV (fun _ hd => hd ▸ hreg))

/-- **Corollary 3** in the message-passing model: for `Δ ≥ 2`, maximal matching in finite simple
`Δ`-regular (so maximum degree `Δ`) `(Δ+1)`-edge-coloured networks needs `Δ` rounds. -/
theorem corollary3_messagePassing (Δ : ℕ) (hΔ : 2 ≤ Δ) (M : MPAlgorithm (Δ + 1)) (r : ℕ)
    (hM : ∀ (α : Type) [Finite α] (G : ColouredGraph (Δ + 1) α), G.IsSimple → G.IsRegular Δ →
      G.IsMaximalMatching (M.out G r)) : Δ ≤ r := by
  have := theorem6_messagePassing (k := Δ + 1) (by omega) M r (by simpa using hM)
  simpa using this

end Papers.PODC2012.MaximalMatching
