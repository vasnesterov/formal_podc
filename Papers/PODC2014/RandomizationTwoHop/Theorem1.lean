import Papers.PODC2014.RandomizationTwoHop.AStarTerm
import Papers.PODC2014.RandomizationTwoHop.Flood

/-!
# Theorem 1: `Π ∈ GRAN ⇒ Πᶜ` is solvable by a deterministic anonymous algorithm

`astar`: algorithm `A*` (with the one-level-deeper views, see `AStar.lean`) as a deterministic
port-numbering algorithm: nodes flood their truncated walk languages and in round `r` evaluate
phase `⌊√r⌋` of `A*` (`outPhase`), which by then only depends on what they know
(`outPhase_trunc`).

Correctness: on an instance `I` of `Πᶜ`, `terminates` (Lemma 8) gives a phase `z + 1` in which
all nodes output and the run `η` of `A_R` on `I` with the bits `b^{z+1}` decides everywhere;
`outPhase_eq` (Lemma 9) shows that every output of `A*` up to phase `z + 1` is `η`'s output, and
the first output of every node is produced by phase `z + 1`. Since `A_R` solves `Π`, `η`'s output
labelling is valid.
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph AStar

variable {In Out C : Type} [LinearOrder C]

/-- Algorithm `A*` as a deterministic message-passing algorithm. -/
noncomputable def astar (Pb : Problem In Out) (AR : RAlg In Out) : RAlg (In × C) Out :=
  floodAlg fun r W => outPhase Pb AR (Nat.sqrt r) W

/-- In round `r ≥ p²` the depth-`r` view suffices to evaluate phase `p`. -/
theorem outPhase_trunc (Pb : Problem In Out) (AR : RAlg In Out) {p r : ℕ} (h : p * p ≤ r)
    (W : Set (List (In × C))) : outPhase Pb AR p (trunc r W) = outPhase Pb AR p W :=
  outPhase_depthLocal Pb AR p _ _ (trunc_trunc ((Db_succ_le p).trans h) W)

/-- **Theorem 1.** If `Π ∈ GRAN`, then `Πᶜ` (the 2-hop coloured variant of `Π`) is solvable by
a deterministic anonymous algorithm. -/
theorem theorem_1 (Pb : Problem In Out) (hP : GRAN Pb) :
    ∃ A : RAlg (In × C) Out, A.IsDeterministic ∧ Solves A (colored C Pb) := by
  obtain ⟨⟨AR, hA⟩, ⟨B, hB⟩⟩ := hP
  refine ⟨astar Pb AR, floodAlg_isDeterministic _, ?_⟩
  rintro X ⟨hXi, hXc⟩ P hPs hPG
  obtain ⟨z, hout, hη⟩ := terminates Pb AR hXc hB hXi hA
  have hdec : ∀ β t v, (astar Pb AR).decided P X.lab β t v =
      firstOut (fun r W => outPhase Pb AR (Nat.sqrt r) W) (⟪X⟫ v) t :=
    fun β t v => floodAlg_decided _ X P hPs hPG β t v
  set r₀ := (z + 1) * (z + 1)
  have hsq : Nat.sqrt r₀ = z + 1 := Nat.sqrt_eq' (z + 1) |>.symm ▸ by simp [r₀, Nat.sqrt_eq]
  have hF₀ : ∀ v, (outPhase Pb AR (Nat.sqrt r₀) (trunc r₀ (⟪X⟫ v))).isSome := by
    intro v; rw [hsq, outPhase_trunc Pb AR le_rfl]; exact hout v
  refine ⟨fun β₀ t₀ => ⟨β₀, fun _ _ _ => rfl, r₀, fun v => ?_⟩, fun β t h => ?_⟩
  · rw [hdec]; exact firstOut_isSome le_rfl (hF₀ v)
  · have hfun : (fun v => ((astar Pb AR).decided P X.lab β t v).get (h v)) =
        fun v => (runX AR X (fun u => bitsOf (bits Pb AR X (z + 1) u)) z v).get (hη v) := by
      funext v
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (h v)
      rw [Option.get_eq_of_eq_some ho]
      rw [hdec] at ho
      obtain ⟨k, -, hk, hmin⟩ := firstOut_eq_some ho
      rw [outPhase_trunc Pb AR (Nat.sqrt_le k)] at hk
      have hkz : Nat.sqrt k ≤ z + 1 := by
        by_contra hgt
        have hk0 : r₀ < k := by
          have := Nat.le_sqrt.1 (show z + 2 ≤ Nat.sqrt k by omega)
          simp only [r₀]; nlinarith
        have := hF₀ v
        rw [hmin r₀ hk0] at this
        simp at this
      have h9 := outPhase_eq Pb AR hXc hkz hk
      exact (Option.get_eq_of_eq_some
        (RAlg.decided_eq_some_mono (show Nat.sqrt k - 1 ≤ z by omega) h9) _).symm
    show Pb.valid (X.map Prod.fst) _
    rw [hfun]
    exact (hA.colored hXi hXc).2 _ z hη

end Podc.RandomizationTwoHop
