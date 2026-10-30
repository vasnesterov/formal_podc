import Papers.PODC2023.BilateralNetworkCreation.LayerTree
import Papers.PODC2023.BilateralNetworkCreation.Stretched

/-!
# Proposition 3.8: stretched binary trees are in BGE

The `k`-stretched complete binary tree of depth `d` (`stretchedTree d k`, `Stretched.lean`) has
subtree sizes depending only on the layer (`sF d k`), halving every `k` layers; by
`bge_of_layerSized` it is in BGE for `α ≥ 7kn`.
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

lemma stretched_layerSized (d k : ℕ) (hk : 1 ≤ k) :
    LayerSized (stretchedTree d k) sRoot k (sF d k) where
  card_sub x := by rw [card_sub_stretchedTree, stretchedTree_dist_root]
  anti := sF_antitone
  decay := two_mul_sF_add_le hk
  half := two_mul_sF_one_le hk

/-- Proposition 3.8: a `k`-stretched binary tree with `n` nodes is in BGE for `α ≥ 7kn`
(`M > α n³` is the disconnection penalty). -/
theorem prop_3_8 (d k : ℕ) (hk : 1 ≤ k) {α : ℝ} {M : ℕ}
    (hα : 7 * k * Fintype.card (SVert d k) ≤ α) (hM : α * (Fintype.card (SVert d k)) ^ 3 < M) :
    BGE α M (stretchedTree d k) :=
  bge_of_layerSized stretchedTree_isTree (stretched_layerSized d k hk) hk hα hM

end Podc.BilateralNetworkCreation
