import Papers.PODC2012.WeakModelsModalLogic.MultisetSim
import Papers.PODC2012.WeakModelsModalLogic.Separations
import Papers.PODC2012.WeakModelsModalLogic.Theorem17

/-!
# The linear order of the weak models (equations (1) and (2) of Hella et al.)

`SB ⊊ MB = VB ⊊ SV = MV = VV ⊊ VVc` and the same for the constant-time classes. The equalities
hold for every output set `Y`; the strict inclusions are witnessed by problems with outputs in
`Bool` (`Y = {0, 1}`), as in the paper.
-/

namespace Podc.WeakModelsModalLogic

/-- The equalities and inclusions of (1), for every output set `Y`. -/
theorem collapse (Y : Type) :
    SB Y ⊆ MB Y ∧ MB Y = VB Y ∧ VB Y ⊆ SV Y ∧ SV Y = MV Y ∧ MV Y = VV Y ∧ VV Y ⊆ VVc Y := by
  obtain ⟨h1, -, h3, -⟩ := cor10 Y
  have h7 := (cor7 Y).1
  refine ⟨SB_subset_MB, h1.symm, ?_, h7.symm, h3.symm, VV_subset_VVc⟩
  rw [h1, ← h7]; exact MB_subset_MV

/-- The equalities and inclusions of (2), for every output set `Y`. -/
theorem collapse1 (Y : Type) :
    SB1 Y ⊆ MB1 Y ∧ MB1 Y = VB1 Y ∧ VB1 Y ⊆ SV1 Y ∧ SV1 Y = MV1 Y ∧ MV1 Y = VV1 Y ∧
      VV1 Y ⊆ VVc1 Y := by
  obtain ⟨-, h2, -, h4⟩ := cor10 Y
  have h7 := (cor7 Y).2
  refine ⟨SB1_subset_MB1, h2.symm, ?_, h7.symm, h4.symm, VV1_subset_VVc1⟩
  rw [h2, ← h7]; exact MB1_subset_MV1

/-- Equation (1) of [Hella et al.]: `SB ⊊ MB = VB ⊊ SV = MV = VV ⊊ VVc`. -/
theorem linearOrder :
    SB Bool ⊂ MB Bool ∧ MB Bool = VB Bool ∧ VB Bool ⊂ SV Bool ∧ SV Bool = MV Bool ∧
      MV Bool = VV Bool ∧ VV Bool ⊂ VVc Bool := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := collapse Bool
  refine ⟨h1.ssubset_of_ne cor14.1, h2, h3.ssubset_of_ne cor12.1, h4, h5,
    h6.ssubset_of_ne corollary18.1.symm⟩

/-- Equation (2) of [Hella et al.]:
`SB(1) ⊊ MB(1) = VB(1) ⊊ SV(1) = MV(1) = VV(1) ⊊ VVc(1)`. -/
theorem linearOrder1 :
    SB1 Bool ⊂ MB1 Bool ∧ MB1 Bool = VB1 Bool ∧ VB1 Bool ⊂ SV1 Bool ∧ SV1 Bool = MV1 Bool ∧
      MV1 Bool = VV1 Bool ∧ VV1 Bool ⊂ VVc1 Bool := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := collapse1 Bool
  refine ⟨h1.ssubset_of_ne cor14.2, h2, h3.ssubset_of_ne cor12.2, h4, h5,
    h6.ssubset_of_ne corollary18.2.symm⟩

end Podc.WeakModelsModalLogic
