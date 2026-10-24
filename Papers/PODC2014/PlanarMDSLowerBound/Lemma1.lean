import Papers.PODC2014.PlanarMDSLowerBound.Blocks
import Podc.Foundations.Combinatorics.HypergraphRamsey
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

/-!
# Lemma 1 of Hilke–Lenzen–Suomela: repeated Ramsey

Let `A` be a `T`-round LOCAL algorithm (`Cslib.Local.IsLocal T`) that outputs a dominating set on
every identifier assignment of the grid `grid (r * m) m` (`r` blocks of `m × m` nodes) with
identifiers `Fin (r m²)`.

* `outF A`: the output of `A` as a function of the local view (well defined by
  `out_eq_of_view_eq`); `colour A X = outF A (placement k X)` is the paper's colouring `c(X)` of the
  `K`-subsets of identifiers (`k = 2T + 1`, `K = k²`).
* `rest`, `blockIds`: the repeated choice `V₁ = V`, `Yᵢ ⊆ Vᵢ` monochromatic of size `M = m²`,
  `Vᵢ₊₁ = Vᵢ \ Yᵢ`.
* `lemma_1`: with `ℓ ≥ N(K, M)` (the Ramsey number), the assignment `asgEquiv` built from the `Yᵢ`
  puts every internal node of blocks `0, …, r - ℓ - 1` into the output of `A`, provided the
  internal area of a block is at least `3 × 3` (`2T + 3 ≤ m`), which the paper's last step ("the
  common output cannot be 0") needs.
-/

namespace Podc.PlanarMDSLowerBound

open Finset Cslib

section Colour

variable {W H n T : ℕ} (A : SimpleGraph (Fin n) → Fin n → Bool)

open Classical in
/-- The output of `A` as a function of the view `f` of a node (`false` for impossible views). -/
noncomputable def outF (W H T : ℕ) (f : Fin (2 * T + 1) → Fin (2 * T + 1) → Option (Fin n)) : Bool :=
  if h : ∃ (σ : GV W H ≃ Fin n) (v : GV W H), view T σ v = f then
    A (lab h.choose) (h.choose h.choose_spec.choose)
  else false

variable {A} in
lemma out_eq_outF (hA : Local.IsLocal T (fun G (_ : Fin n → Unit) v => A G v))
    (σ : GV W H ≃ Fin n) (v : GV W H) : A (lab σ) (σ v) = outF A W H T (view T σ v) := by
  have h : ∃ (σ' : GV W H ≃ Fin n) (v' : GV W H), view T σ' v' = view T σ v := ⟨σ, v, rfl⟩
  rw [outF, dite_eq_left_of_eq_true (eq_true h)]
  exact (out_eq_of_view_eq hA h.choose_spec.choose_spec).symm

/-- The paper's colouring `c(X)` of `K`-sets of identifiers: the output of a node whose `k × k`
region carries the identifiers of `X` in increasing order by rows. -/
noncomputable def colour (W H T : ℕ) (X : Finset (Fin n)) : Bool :=
  outF A W H T (placement (2 * T + 1) X)

end Colour

section Lemma1

variable {T m r : ℕ} {A : SimpleGraph (Fin (r * m * m)) → Fin (r * m * m) → Bool}

/-- Internal nodes of a block whose identifier set is homogeneous all produce the same output. -/
lemma out_internal (hA : Local.IsLocal T (fun G (_ : Fin (r * m * m) → Unit) v => A G v))
    (Y : ℕ → Finset (Fin (r * m * m))) (hY : ∀ i < r, (Y i).card = m * m)
    (hdisj : ∀ i j, i < r → j < r → i ≠ j → Disjoint (Y i) (Y j))
    {i : ℕ} (hi : i < r) {col : Bool}
    (hhom : IsHomogeneous (colour A (r * m) m T) ((2 * T + 1) * (2 * T + 1)) (Y i) col)
    {a b : ℕ} (ha : T ≤ a) (ha' : a + T < m) (hb : T ≤ b) (hb' : b + T < m) :
    A (lab (asgEquiv Y hY hdisj)) (asgEquiv Y hY hdisj (node i a b hi (by omega) (by omega))) =
      col := by
  obtain ⟨X, hXY, hXc, hv⟩ := view_asg_internal Y hY hdisj hi ha ha' hb hb'
  rw [out_eq_outF hA, hv]
  exact hhom X hXY hXc

/-- The last step of the proof of Lemma 1: if all internal nodes of a block give the same output
and `2T + 3 ≤ m`, this output is `1` (otherwise the node at internal position `(T+1, T+1)` would not
be dominated). -/
lemma common_output_true (σ : GV (r * m) m ≃ Fin (r * m * m))
    (hdom : (lab σ).IsDominatingSet {u | A (lab σ) u = true})
    {i : ℕ} (hi : i < r) (hm : 2 * T + 3 ≤ m) {col : Bool}
    (hout : ∀ a b, T ≤ a → ∀ (ha' : a + T < m), T ≤ b → ∀ (hb' : b + T < m),
      A (lab σ) (σ (node i a b hi (by omega) (by omega))) = col) : col = true := by
  by_contra hcol
  simp only [Bool.not_eq_true] at hcol
  subst hcol
  rcases hdom (σ (node i (T + 1) (T + 1) hi (by omega) (by omega))) with h | ⟨u, hu, hadj⟩
  · simp only [Set.mem_ofPred_eq] at h
    rw [hout (T + 1) (T + 1) (by omega) (by omega) (by omega) (by omega)] at h
    exact Bool.false_ne_true h
  · simp only [Set.mem_ofPred_eq] at hu
    rw [lab_adj, Equiv.symm_apply_apply, pt_node, Cslib.SimpleGraph.TriAdj] at hadj
    set p := σ.symm u with hp
    have hx := p.1.2
    have hy := p.2.2
    simp only [pt] at hadj
    have hm0 : 0 < m := by omega
    -- `p` is the node `(i m + a', b')` with `T ≤ a' ≤ T + 2`, `T ≤ b' ≤ T + 2`
    have hpx : (p.1 : ℕ) = i * m + ((p.1 : ℕ) - i * m) := by omega
    have hp' : p = node i ((p.1 : ℕ) - i * m) (p.2 : ℕ) hi (by omega) (by omega) := by
      ext <;> (simp only [node]; try omega)
    have := hout ((p.1 : ℕ) - i * m) (p.2 : ℕ) (by omega) (by omega) (by omega) (by omega)
    rw [← hp', hp, Equiv.apply_symm_apply] at this
    rw [this] at hu
    exact Bool.false_ne_true hu

/-! ### The repeated Ramsey construction -/

variable {n : ℕ}

lemma exists_pick (c : Finset (Fin n) → Bool) {K M N : ℕ}
    (hN : ∀ S : Finset (Fin n), N ≤ S.card → ∃ Y ⊆ S, Y.card = M ∧ ∃ col, IsHomogeneous c K Y col)
    (S : Finset (Fin n)) (hS : M ≤ S.card) :
    ∃ Y ⊆ S, Y.card = M ∧ (N ≤ S.card → ∃ col, IsHomogeneous c K Y col) := by
  by_cases h : N ≤ S.card
  · obtain ⟨Y, h1, h2, h3⟩ := hN S h
    exact ⟨Y, h1, h2, fun _ => h3⟩
  · obtain ⟨Y, h1, h2⟩ := Finset.exists_subset_card_eq hS
    exact ⟨Y, h1, h2, fun h' => absurd h' h⟩

variable (c : Finset (Fin n) → Bool) (K M N : ℕ)
  (hN : ∀ S : Finset (Fin n), N ≤ S.card → ∃ Y ⊆ S, Y.card = M ∧ ∃ col, IsHomogeneous c K Y col)

open Classical in
/-- Step 1 of the paper's construction: a subset `Y ⊆ S` of size `M`, monochromatic if `|S| ≥ N`. -/
noncomputable def pick (S : Finset (Fin n)) : Finset (Fin n) :=
  if h : M ≤ S.card then (exists_pick c hN S h).choose else ∅

/-- The remaining identifiers `Vᵢ` (`V₀ = V`, `Vᵢ₊₁ = Vᵢ \ Yᵢ`). -/
noncomputable def rest : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | i + 1 => rest i \ pick c K M N hN (rest i)

/-- The identifiers `Yᵢ` of block `i`. -/
noncomputable def blockIds (i : ℕ) : Finset (Fin n) := pick c K M N hN (rest c K M N hN i)

lemma pick_spec {S : Finset (Fin n)} (hS : M ≤ S.card) :
    pick c K M N hN S ⊆ S ∧ (pick c K M N hN S).card = M ∧
      (N ≤ S.card → ∃ col, IsHomogeneous c K (pick c K M N hN S) col) := by
  rw [pick, dite_eq_left_of_eq_true (eq_true hS)]
  exact (exists_pick c hN S hS).choose_spec

lemma rest_card {i : ℕ} (hi : i * M ≤ n) : (rest c K M N hN i).card = n - i * M := by
  induction i with
  | zero => simp [rest]
  | succ i ih =>
    have hi' : i * M ≤ n := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ i)) hi
    have hM : M ≤ (rest c K M N hN i).card := by
      rw [ih hi', Nat.succ_mul] at *; omega
    obtain ⟨h1, h2, -⟩ := pick_spec c K M N hN hM
    rw [rest, Finset.card_sdiff_of_subset h1, h2, ih hi', Nat.succ_mul]
    omega

lemma rest_antitone {i j : ℕ} (hij : i ≤ j) : rest c K M N hN j ⊆ rest c K M N hN i := by
  induction hij with
  | refl => exact subset_rfl
  | step _ ih => exact (Finset.sdiff_subset).trans ih

lemma blockIds_card {i : ℕ} (hi : (i + 1) * M ≤ n) : (blockIds c K M N hN i).card = M := by
  have hi' : i * M ≤ n := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ i)) hi
  have hM : M ≤ (rest c K M N hN i).card := by
    rw [rest_card c K M N hN hi', Nat.succ_mul] at *; omega
  exact (pick_spec c K M N hN hM).2.1

lemma blockIds_disjoint {i j : ℕ} (hij : i < j) :
    Disjoint (blockIds c K M N hN i) (blockIds c K M N hN j) := by
  by_cases hM : M ≤ (rest c K M N hN j).card
  · have h1 : blockIds c K M N hN j ⊆ rest c K M N hN (i + 1) :=
      (pick_spec c K M N hN hM).1.trans (rest_antitone c K M N hN hij)
    rw [rest] at h1
    exact Finset.disjoint_of_subset_right h1 Finset.disjoint_sdiff
  · have he : blockIds c K M N hN j = ∅ := by
      rw [blockIds, pick, dite_eq_right_of_eq_false (eq_false hM)]
    rw [he]
    exact Finset.disjoint_empty_right _

lemma blockIds_homogeneous {i : ℕ} (hi : (i + 1) * M ≤ n) (hN' : N ≤ n - i * M) :
    ∃ col, IsHomogeneous c K (blockIds c K M N hN i) col := by
  have hi' : i * M ≤ n := le_trans (Nat.mul_le_mul_right _ (Nat.le_succ i)) hi
  have hc := rest_card c K M N hN hi'
  have hM : M ≤ (rest c K M N hN i).card := by
    rw [hc, Nat.succ_mul] at *; omega
  exact (pick_spec c K M N hN hM).2.2 (by rw [hc]; exact hN')

end Lemma1

/-- **Lemma 1** of the paper (for `2T + 3 ≤ m`). Let `N` be a Ramsey number for colourings of the
`K`-subsets (`K = (2T+1)²`) with monochromatic `M`-subsets (`M = m²`), and `ℓ ≥ N`, `ℓ ≤ r`. For every
`T`-round LOCAL algorithm `A` that outputs a dominating set for every identifier assignment of the
grid of `r` blocks of `m × m` nodes, there is an identifier assignment `σ` under which all internal
nodes (`T ≤ a < m - T`, `T ≤ b < m - T`) of the blocks `i < r - ℓ` are in the output. -/
theorem lemma_1 {T m r ℓ N : ℕ} (hm : 2 * T + 3 ≤ m)
    (hN : ∀ {α : Type} [DecidableEq α] (c : Finset α → Bool) (S : Finset α), N ≤ S.card →
      ∃ Y ⊆ S, Y.card = m * m ∧ ∃ col, IsHomogeneous c ((2 * T + 1) * (2 * T + 1)) Y col)
    (hℓ : N ≤ ℓ) (A : SimpleGraph (Fin (r * m * m)) → Fin (r * m * m) → Bool)
    (hA : Local.IsLocal T (fun G (_ : Fin (r * m * m) → Unit) v => A G v))
    (hdom : ∀ σ : GV (r * m) m ≃ Fin (r * m * m), (lab σ).IsDominatingSet {u | A (lab σ) u = true}) :
    ∃ σ : GV (r * m) m ≃ Fin (r * m * m), ∀ i (hi : i + ℓ < r) a b, T ≤ a → ∀ (ha' : a + T < m),
      T ≤ b → ∀ (hb' : b + T < m),
      A (lab σ) (σ (node i a b (by omega) (by omega) (by omega))) = true := by
  set c := colour A (r * m) m T
  have hN' : ∀ S : Finset (Fin (r * m * m)), N ≤ S.card →
      ∃ Y ⊆ S, Y.card = m * m ∧ ∃ col, IsHomogeneous c ((2 * T + 1) * (2 * T + 1)) Y col :=
    fun S hS => hN c S hS
  set K := (2 * T + 1) * (2 * T + 1)
  set M := m * m
  let Y := blockIds c K M N hN'
  have hY : ∀ i < r, (Y i).card = M := fun i hi =>
    blockIds_card c K M N hN' (by
      have : (i + 1) * M ≤ r * M := Nat.mul_le_mul_right _ hi
      simpa [M, Nat.mul_assoc] using this)
  have hdisj : ∀ i j, i < r → j < r → i ≠ j → Disjoint (Y i) (Y j) := by
    intro i j _ _ hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact blockIds_disjoint c K M N hN' h
    · exact (blockIds_disjoint c K M N hN' h).symm
  refine ⟨asgEquiv Y hY hdisj, ?_⟩
  intro i hi
  have hi' : i < r := by omega
  obtain ⟨col, hcol⟩ := blockIds_homogeneous c K M N hN' (i := i)
    (by
      have : (i + 1) * M ≤ r * M := Nat.mul_le_mul_right _ hi'
      simpa [M, Nat.mul_assoc] using this)
    (by
      have h1 : r * m * m = r * M := by simp [M, Nat.mul_assoc]
      have hM : 0 < M := Nat.mul_pos (by omega) (by omega)
      rw [h1, ← Nat.sub_mul]
      calc N ≤ ℓ := hℓ
        _ ≤ r - i := by omega
        _ ≤ (r - i) * M := Nat.le_mul_of_pos_right _ hM)
  have hall := fun a b ha ha' hb hb' =>
    out_internal hA Y hY hdisj hi' hcol (a := a) (b := b) ha ha' hb hb'
  have := common_output_true (asgEquiv Y hY hdisj) (hdom _) hi' hm hall
  subst this
  intro a b ha ha' hb hb'
  exact hall a b ha ha' hb hb'

end Podc.PlanarMDSLowerBound
