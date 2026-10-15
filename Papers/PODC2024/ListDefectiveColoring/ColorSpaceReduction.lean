import Papers.PODC2024.ListDefectiveColoring.Basic

/-!
# Lemma 4.5 of [FK24]: colour space reduction

The colour space `C` is partitioned into subspaces `C_i` (`part : α → ι`, colour `x` lies in the
subspace `part x`). Every node first picks a subspace `i`, by solving a list *defective* colouring
instance `J` with colour space `ι` (cost `T_D(σ, p)`), and then solves the list *arbdefective*
colouring instance `K` with list `L_{v,i} = L_v ∩ C_i` on the subgraph of edges whose endpoints
picked the same subspace (cost `T_A(S/σ, ⌈C/p⌉)`).

We formalize the combinatorial ("spec-level") content, for *any* solutions of the sub-instances:

* `FK24.ColorSpace.choice_hasSlack`: `J` has slack `σ` (first display of the proof);
* `FK24.ColorSpace.sub_hasSlack`: for every list defective colouring `ψ` of `J`, the instance `K`
  has slack `S/σ` on `sameClass G ψ` (second display of the proof);
* `FK24.ColorSpace.isListArbdefective_of_sub`: every list arbdefective colouring of `K` on
  `sameClass G ψ` is a list arbdefective colouring of the original instance on `G`;
* `FK24.lemma45`: the combination (Lemma 4.5, eq. (17)).

**Gap in the proof's construction (trivial fix).** In the paper the subspace-choice instance has *all* `p` subspaces in every
list. Then a node may pick a subspace `i` with `L_v ∩ C_i = ∅` (its defect `d_{v,i} = 0` is not
violated if it has no neighbour picking `i`), after which it has an empty list. The step
`(S/σ) · d_{v,i} ≥ ...`, `∑_{L_{v,i}} (d_v(x)+1) > (S/σ) d_{v,i}` fails for `d_{v,i} = 0`.
We use the lists `{i | L_v ∩ C_i ≠ ∅}` (`(I.L v).image part`) instead; the slack computation of
the paper goes through unchanged. `FK24.ColorSpace.paper_counterexample` shows that the construction
with all subspaces can fail. The round-time statement (17) of Lemma 4.5 itself is not refuted.

Round complexities (`T_D(σ, p) + T_A(S/σ, ⌈C/p⌉)`) are not formalized.
-/

open Finset

namespace FK24

variable {V α ι β : Type*}

/-- `G` restricted to the edges whose endpoints have the same `f`-value (the paper's `G_i`'s,
put side by side). -/
def sameClass (G : SimpleGraph V) (f : V → β) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u = f v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq β] (f : V → β) :
    DecidableRel (sameClass G f).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ f u = f v))

theorem sameClass_adj {G : SimpleGraph V} {f : V → β} {u v : V} :
    (sameClass G f).Adj u v ↔ G.Adj u v ∧ f u = f v := Iff.rfl

theorem neighborFinset_sameClass [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq β] (f : V → β) (v : V) :
    (sameClass G f).neighborFinset v = {u ∈ G.neighborFinset v | f u = f v} := by
  ext u
  simp [sameClass_adj, eq_comm]

theorem degree_sameClass [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq β] (f : V → β) (v : V) :
    (sameClass G f).degree v = #{u ∈ G.neighborFinset v | f u = f v} := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_sameClass]

namespace ColorSpace

variable [DecidableEq ι]

/-- `L_{v,i} = L_v ∩ C_i` (eq. (18)). -/
def subList (I : ListInstance V α) (part : α → ι) (v : V) (i : ι) : Finset α :=
  {x ∈ I.L v | part x = i}

/-- `W_{v,i} = ∑_{x ∈ L_{v,i}} (d_v(x) + 1)`. -/
def subWeight (I : ListInstance V α) (part : α → ι) (v : V) (i : ι) : ℕ :=
  ∑ x ∈ subList I part v i, (I.d v x + 1)

theorem sum_subWeight (I : ListInstance V α) (part : α → ι) (v : V) :
    ∑ i ∈ (I.L v).image part, subWeight I part v i = I.weight v := by
  unfold subWeight subList ListInstance.weight
  exact sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem part hx) _

section Graph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `d_{v,i} = ⌊σ · deg(v) · W_{v,i} / W_v⌋` (eq. (19)). -/
noncomputable def subDefect (I : ListInstance V α) (part : α → ι) (σ : ℝ) (v : V) (i : ι) : ℕ :=
  ⌊σ * G.degree v * subWeight I part v i / I.weight v⌋₊

/-- The subspace-choice instance (colour space `ι`, defects `d_{v,i}`), with the **fixed** lists
`{i | L_{v,i} ≠ ∅}`. -/
noncomputable def choice (I : ListInstance V α) (part : α → ι) (σ : ℝ) : ListInstance V ι where
  L v := (I.L v).image part
  d := subDefect G I part σ

/-- The subspace-choice instance of the paper, with *all* subspaces in every list. -/
noncomputable def choicePaper [Fintype ι] (I : ListInstance V α) (part : α → ι) (σ : ℝ) :
    ListInstance V ι where
  L _ := univ
  d := subDefect G I part σ

end Graph

/-- The instance on the nodes that picked subspace `ψ v`: lists `L_{v,ψ(v)}`, the original
defects. -/
def sub (I : ListInstance V α) (part : α → ι) (ψ : V → ι) : ListInstance V α where
  L v := subList I part v (ψ v)
  d := I.d

theorem mem_image_iff_subWeight_pos (I : ListInstance V α) (part : α → ι) (v : V) (i : ι) :
    i ∈ (I.L v).image part ↔ 0 < subWeight I part v i := by
  unfold subWeight subList
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := mem_image.1 h
    exact sum_pos (fun _ _ => Nat.succ_pos _) ⟨x, mem_filter.2 ⟨hx, rfl⟩⟩
  · intro h
    obtain ⟨x, hx, -⟩ := exists_ne_zero_of_sum_ne_zero h.ne'
    exact mem_image.2 ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem weight_pos_of_hasSlack {I : ListInstance V α} {S : ℝ} (hS : 0 ≤ S)
    (h : HasSlack G I S) (v : V) : 0 < I.weight v := by
  have := h v
  have : (0 : ℝ) < I.weight v := lt_of_le_of_lt (by positivity) this
  exact_mod_cast this

/-- Lemma 4.5 of [FK24], first display of the proof: the subspace-choice instance has slack `σ`,
`∑_{i} (d_{v,i} + 1) > σ · deg(v)`. -/
theorem choice_hasSlack {I : ListInstance V α} (part : α → ι) {S σ : ℝ} (hS : 0 ≤ S)
    (h : HasSlack G I S) : HasSlack G (choice G I part σ) σ := by
  intro v
  have hW : (0 : ℝ) < I.weight v := by exact_mod_cast weight_pos_of_hasSlack G hS h v
  have hne : ((I.L v).image part).Nonempty := by
    have : (I.L v).Nonempty := by
      by_contra hc
      rw [not_nonempty_iff_eq_empty] at hc
      have := weight_pos_of_hasSlack G hS h v
      simp [ListInstance.weight, hc] at this
    exact this.image part
  have hsum : ∑ i ∈ (I.L v).image part, (σ * G.degree v * subWeight I part v i / I.weight v) =
      σ * G.degree v := by
    rw [← sum_div, ← mul_sum]
    have : ∑ i ∈ (I.L v).image part, (subWeight I part v i : ℝ) = I.weight v := by
      exact_mod_cast sum_subWeight I part v
    rw [this, mul_div_assoc, div_self hW.ne', mul_one]
  show σ * (G.degree v : ℝ) <
    ((∑ i ∈ (I.L v).image part, (subDefect G I part σ v i + 1) : ℕ) : ℝ)
  push_cast
  exact lt_of_eq_of_lt hsum.symm (sum_lt_sum_of_nonempty hne (fun i _ => Nat.lt_floor_add_one _))

/-- Lemma 4.5 of [FK24], second display of the proof: if `ψ` is a list defective colouring of the
subspace-choice instance, then the instance with lists `L_{v,ψ(v)}` has slack `S/σ` on the graph of
edges whose endpoints picked the same subspace. -/
theorem sub_hasSlack {I : ListInstance V α} (part : α → ι) {S σ : ℝ} (hS : 0 ≤ S) (hσ : 0 < σ)
    (h : HasSlack G I S) {ψ : V → ι} (hψ : IsListDefective G (choice G I part σ) ψ) :
    HasSlack (sameClass G ψ) (sub I part ψ) (S / σ) := by
  intro v
  obtain ⟨hmem, hdef⟩ := hψ v
  have hW : (0 : ℝ) < I.weight v := by exact_mod_cast weight_pos_of_hasSlack G hS h v
  have hWi : (0 : ℝ) < subWeight I part v (ψ v) := by
    exact_mod_cast (mem_image_iff_subWeight_pos I part v (ψ v)).1 hmem
  have hdeg : ((sameClass G ψ).degree v : ℝ) ≤ subDefect G I part σ v (ψ v) := by
    rw [degree_sameClass]; exact_mod_cast hdef
  have hfl : (subDefect G I part σ v (ψ v) : ℝ) ≤
      σ * G.degree v * subWeight I part v (ψ v) / I.weight v :=
    Nat.floor_le (by positivity)
  have hSv := h v
  change S / σ * ((sameClass G ψ).degree v : ℝ) < (subWeight I part v (ψ v) : ℝ)
  calc S / σ * ((sameClass G ψ).degree v : ℝ)
      ≤ S / σ * (σ * G.degree v * subWeight I part v (ψ v) / I.weight v) := by
        gcongr; exact hdeg.trans hfl
    _ = (S * G.degree v) * subWeight I part v (ψ v) / I.weight v := by
        field_simp
    _ < I.weight v * subWeight I part v (ψ v) / I.weight v := by gcongr
    _ = subWeight I part v (ψ v) := by field_simp

/-- Lemma 4.5 of [FK24], correctness of the combination: a list arbdefective colouring of the
sub-instance on `sameClass G ψ` is a list arbdefective colouring of the original instance on `G`. -/
theorem isListArbdefective_of_sub {I : ListInstance V α} (part : α → ι) (ψ : V → ι)
    {col : V → α} {O : V → V → Prop}
    (hc : IsListArbdefective (sameClass G ψ) (sub I part ψ) col O) :
    IsListArbdefective G I col O := by
  classical
  obtain ⟨hL, hO, hd⟩ := hc
  have hpart : ∀ v, part (col v) = ψ v := fun v => (mem_filter.1 (hL v)).2
  refine ⟨fun v => (mem_filter.1 (hL v)).1, fun u v huv he => hO ⟨huv, ?_⟩ he, fun v => ?_⟩
  · rw [← hpart, he, hpart]
  · refine le_trans (le_of_eq ?_) (hd v)
    congr 1
    ext u
    simp only [mem_filter, SimpleGraph.mem_neighborFinset, sameClass_adj]
    constructor
    · rintro ⟨hvu, hO', he⟩
      exact ⟨⟨hvu, by rw [← hpart, ← he, hpart]⟩, hO', he⟩
    · rintro ⟨⟨hvu, -⟩, hO', he⟩
      exact ⟨hvu, hO', he⟩

end ColorSpace

open ColorSpace in
/-- Lemma 4.5 of [FK24] (colour space reduction, eq. (17)), spec level, with the fix that the
subspace-choice lists only contain subspaces `i` with `L_v ∩ C_i ≠ ∅`.
Let `I` have slack `S` on `G` and `0 < σ ≤ S` (the paper: `1 ≤ σ ≤ S`; only `σ > 0` and `S ≥ 0`
are used). Then

1. the subspace-choice instance `choice G I part σ` (colour space `ι`, of size `p`) has slack `σ`;
2. for every list defective colouring `ψ` of it, the instance `sub I part ψ` (lists
   `L_v ∩ C_{ψ(v)}`, contained in one subspace) has slack `S/σ` on `sameClass G ψ`;
3. every list arbdefective colouring of `sub I part ψ` on `sameClass G ψ` solves `I` on `G`.

Hence `T_A(S, C) ≤ T_D(σ, p) + T_A(S/σ, ⌈C/p⌉)` (round complexities are not formalized). -/
theorem lemma45 [Fintype V] [DecidableEq ι] (G : SimpleGraph V)
    [DecidableRel G.Adj] (I : ListInstance V α) (part : α → ι) {S σ : ℝ} (hσ : 0 < σ)
    (hσS : σ ≤ S) (h : HasSlack G I S) :
    HasSlack G (choice G I part σ) σ ∧
      ∀ ψ : V → ι, IsListDefective G (choice G I part σ) ψ →
        HasSlack (sameClass G ψ) (sub I part ψ) (S / σ) ∧
          ∀ (col : V → α) (O : V → V → Prop),
            IsListArbdefective (sameClass G ψ) (sub I part ψ) col O →
              IsListArbdefective G I col O := by
  have hS : 0 ≤ S := hσ.le.trans hσS
  exact ⟨choice_hasSlack G part hS h, fun ψ hψ =>
    ⟨sub_hasSlack G part hS hσ h hψ, fun _ _ hc => isListArbdefective_of_sub G part ψ hc⟩⟩

namespace ColorSpace

/-- A gap in the construction of the proof of Lemma 4.5 of [FK24] (the statement (17) is not
refuted; the fix is to restrict the subspace-choice lists to subspaces meeting `L_v`). With the
paper's subspace-choice lists (all subspaces) the reduction can fail: a single isolated node with list `{0}`, defect `0`, and two subspaces (`part ≡ 0`). The instance has
every slack `S`, `ψ ≡ 1` is a list defective colouring of the paper's subspace-choice instance
(for every `σ`), but then the sub-instance has an empty list: it does not have slack `S/σ`, and it
has no list arbdefective colouring at all. -/
theorem paper_counterexample (S σ : ℝ) :
    let G : SimpleGraph Unit := ⊥
    let I : ListInstance Unit ℕ := ⟨fun _ => {0}, fun _ _ => 0⟩
    let part : ℕ → Fin 2 := fun _ => 0
    let ψ : Unit → Fin 2 := fun _ => 1
    HasSlack G I S ∧ IsListDefective G (choicePaper G I part σ) ψ ∧
      ¬ HasSlack (sameClass G ψ) (sub I part ψ) (S / σ) ∧
      ∀ col O, ¬ IsListArbdefective (sameClass G ψ) (sub I part ψ) col O := by
  intro G I part ψ
  have hsub : ∀ v, (sub I part ψ).L v = ∅ := fun v => by
    ext x; simp [sub, subList, I, part, ψ]
  refine ⟨fun v => ?_, fun v => ⟨mem_univ _, by simp [G]⟩, fun hs => ?_, fun col O hc => ?_⟩
  · simp [ListInstance.weight, I]
  · have := hs ()
    simp [ListInstance.weight, hsub] at this
  · have := hc.1 ()
    simp [hsub] at this

end ColorSpace

end FK24
