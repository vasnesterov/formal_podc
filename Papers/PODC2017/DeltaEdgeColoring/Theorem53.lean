import Papers.PODC2017.DeltaEdgeColoring.Theorem52Arboricity
import Papers.PODC2017.DeltaEdgeColoring.CliqueDecomposition

/-!
# Theorem 5.3: the orientation connector, `(Δ + o(Δ))`-edge-colouring

Let `G` carry an acyclic orientation with out-degree `≤ d`, given by a rank `r` (`u → v` iff
`r u < r v`; the paper orients along the H-partition and then by identifiers). Every vertex `v`
splits its incoming edges into groups of `sIn` consecutive edges (by identifier) and its outgoing
edges into groups of `sOut`; the `i`-th incoming group and the `i`-th outgoing group are attached to
the virtual vertex `(v, i)`. The **orientation connector** has the virtual vertices and one edge
`(u, outSlot u v) — (v, inSlot v u)` per edge `u → v` of `G`.

* `oconn_degree_le`, `oconn_hasOutDegLE`: the connector has max degree `≤ sIn + sOut` and an
  orientation with out-degree `≤ sOut` (so arboricity `≤ sOut`, as it is acyclic).
* `classGraph_degree_le`, `classGraph_hasOutDegLE`: for a proper edge colouring `φ'` of the
  connector, every colour class of the induced edge colouring `φ` of `G` has max degree
  `≤ max nIn nOut` and out-degree `≤ nOut`, where `nIn = ⌈Δ/sIn⌉`, `nOut = ⌈d/sOut⌉` are the numbers
  of groups.
* `theorem_5_3_combine`: `⟨φ, ψ⟩` is a proper edge colouring with `K₁ · K₂` colours for any proper
  colourings `φ'` of the connector (`K₁` colours) and `ψ_i` of the classes (`K₂` colours).
* `theorem_5_3_count`: with Theorem 5.2 for both steps, `(sIn + 7 sOut) · (max nIn nOut + 6 nOut)`
  colours; `theorem_5_3`: for `sIn = ⌊√Δ⌋+1`, `sOut = ⌊√d⌋+1` this is `≤ (⌊√Δ⌋ + 7⌊√d⌋ + 8)²`.
* `theorem_5_3_arboricity` and `theorem_5_3_asymptotic`: for arboricity `a` (`d = 3a`),
  `≤ (√Δ + 7√(3a) + 8)²` colours, which is `≤ (1 + ε) Δ` once `a ≤ δ Δ` and `Δ ≥ N`
  (i.e. `Δ + o(Δ)` colours when `a = o(Δ)`).
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

section Connector

variable (G : SimpleGraph V) (r : V → ℕ)

open Classical in
/-- The in-neighbours of `v`. -/
noncomputable def inN (v : V) : Finset V := {u | G.Adj u v ∧ r u < r v}

open Classical in
/-- The out-neighbours of `u`. -/
noncomputable def outN (u : V) : Finset V := {v | G.Adj u v ∧ r u < r v}

/-- The group (virtual vertex) of `v` to which the incoming edge `u → v` is attached. -/
noncomputable def inSlot (sIn : ℕ) (v u : V) : ℕ := block sIn (inN G r v) u

/-- The group (virtual vertex) of `u` to which the outgoing edge `u → v` is attached. -/
noncomputable def outSlot (sOut : ℕ) (u v : V) : ℕ := block sOut (outN G r u) v

/-- The orientation connector on the virtual vertices `V × Fin (m + 1)`. -/
noncomputable def oconn (m sIn sOut : ℕ) : SimpleGraph (V × Fin (m + 1)) where
  Adj x y :=
    (G.Adj x.1 y.1 ∧ r x.1 < r y.1 ∧ (x.2 : ℕ) = outSlot G r sOut x.1 y.1 ∧
      (y.2 : ℕ) = inSlot G r sIn y.1 x.1) ∨
    (G.Adj y.1 x.1 ∧ r y.1 < r x.1 ∧ (y.2 : ℕ) = outSlot G r sOut y.1 x.1 ∧
      (x.2 : ℕ) = inSlot G r sIn x.1 y.1)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> exact lt_irrefl _ h.2.1⟩

/-- The virtual vertex `(v, i)`. -/
def vv (m : ℕ) (v : V) (i : ℕ) : V × Fin (m + 1) := (v, Fin.ofNat (m + 1) i)

/-- The virtual vertex of `v` used by the edge `vw`. -/
noncomputable def slotAt (sIn sOut : ℕ) (v w : V) : ℕ :=
  if r w < r v then inSlot G r sIn v w else outSlot G r sOut v w

/-- The connector edge of the edge `vw` of `G`. -/
noncomputable def liftE (m sIn sOut : ℕ) (v w : V) : Sym2 (V × Fin (m + 1)) :=
  s(vv m v (slotAt G r sIn sOut v w), vv m w (slotAt G r sIn sOut w v))

lemma liftE_comm (m sIn sOut : ℕ) (v w : V) : liftE G r m sIn sOut v w = liftE G r m sIn sOut w v :=
  Sym2.eq_swap

/-- The edge colouring of `G` induced by an edge colouring `φ'` of the connector. -/
noncomputable def inducedColoring (m sIn sOut : ℕ) (φ' : Sym2 (V × Fin (m + 1)) → ℕ) :
    Sym2 V → ℕ :=
  Sym2.lift ⟨fun v w => φ' (liftE G r m sIn sOut v w), fun v w => congrArg φ' (liftE_comm G r m sIn sOut v w)⟩

/-- The colour class `i` of an edge colouring `φ` of `G`. -/
def classGraph (φ : Sym2 V → ℕ) (i : ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ φ s(u, v) = i
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

end Connector

variable {G : SimpleGraph V} {r : V → ℕ} {Δ d sIn sOut m : ℕ}

/-- The hypotheses: `r` orients every edge (adjacent vertices have distinct ranks), out-degrees are
`≤ d`, degrees are `≤ Δ`, the group sizes are positive, and `m + 1` virtual vertices per vertex
suffice (`⌈Δ/sIn⌉ ≤ m + 1`, `⌈d/sOut⌉ ≤ m + 1`). -/
structure ConnHyp (G : SimpleGraph V) (r : V → ℕ) (Δ d sIn sOut m : ℕ) : Prop where
  ne : ∀ ⦃u v⦄, G.Adj u v → r u ≠ r v
  outDeg : ∀ u, #(outN G r u) ≤ d
  deg : ∀ v, (G.neighborSet v).ncard ≤ Δ
  sIn_pos : 0 < sIn
  sOut_pos : 0 < sOut
  nIn_le : Δ ⌈/⌉ sIn ≤ m + 1
  nOut_le : d ⌈/⌉ sOut ≤ m + 1

lemma mem_inN {v u : V} : u ∈ inN G r v ↔ G.Adj u v ∧ r u < r v := by
  classical simp [inN]

lemma mem_outN {u v : V} : v ∈ outN G r u ↔ G.Adj u v ∧ r u < r v := by
  classical simp [outN]

lemma card_inN_le (hH : ConnHyp G r Δ d sIn sOut m) (v : V) : #(inN G r v) ≤ Δ := by
  refine le_trans ?_ (hH.deg v)
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun u hu => (mem_inN.1 hu).1.symm) (Set.toFinite _)

lemma ceilDiv_mono_left {a b c : ℕ} (h : a ≤ b) : a ⌈/⌉ c ≤ b ⌈/⌉ c := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_le_div_right (by omega)

lemma inSlot_lt (hH : ConnHyp G r Δ d sIn sOut m) {v u : V} (hu : G.Adj u v) (hr : r u < r v) :
    inSlot G r sIn v u < Δ ⌈/⌉ sIn :=
  lt_of_lt_of_le (block_lt hH.sIn_pos (mem_inN.2 ⟨hu, hr⟩)) (ceilDiv_mono_left (card_inN_le hH v))

lemma outSlot_lt (hH : ConnHyp G r Δ d sIn sOut m) {u v : V} (hu : G.Adj u v) (hr : r u < r v) :
    outSlot G r sOut u v < d ⌈/⌉ sOut :=
  lt_of_lt_of_le (block_lt hH.sOut_pos (mem_outN.2 ⟨hu, hr⟩)) (ceilDiv_mono_left (hH.outDeg u))

lemma val_vv {i : ℕ} (hi : i < m + 1) (v : V) : ((vv m v i).2 : ℕ) = i := by
  simp [vv, Nat.mod_eq_of_lt hi]

lemma slotAt_lt (hH : ConnHyp G r Δ d sIn sOut m) {v w : V} (hvw : G.Adj v w) :
    slotAt G r sIn sOut v w < max (Δ ⌈/⌉ sIn) (d ⌈/⌉ sOut) := by
  unfold slotAt
  split_ifs with h
  · exact lt_max_of_lt_left (inSlot_lt hH hvw.symm h)
  · exact lt_max_of_lt_right (outSlot_lt hH hvw (lt_of_le_of_ne (not_lt.1 h) (hH.ne hvw)))

lemma slotAt_lt_succ (hH : ConnHyp G r Δ d sIn sOut m) {v w : V} (hvw : G.Adj v w) :
    slotAt G r sIn sOut v w < m + 1 :=
  lt_of_lt_of_le (slotAt_lt hH hvw) (max_le hH.nIn_le hH.nOut_le)

/-- The lift of an edge of `G` is an edge of the connector. -/
lemma oconn_adj_lift (hH : ConnHyp G r Δ d sIn sOut m) {v w : V} (hvw : G.Adj v w) :
    (oconn G r m sIn sOut).Adj (vv m v (slotAt G r sIn sOut v w))
      (vv m w (slotAt G r sIn sOut w v)) := by
  rcases lt_or_gt_of_ne (hH.ne hvw) with h | h
  · left
    refine ⟨hvw, h, ?_, ?_⟩
    · rw [val_vv (slotAt_lt_succ hH hvw)]; simp [slotAt, vv, not_lt.2 h.le]
    · rw [val_vv (slotAt_lt_succ hH hvw.symm)]; simp [slotAt, vv, h]
  · right
    refine ⟨hvw.symm, h, ?_, ?_⟩
    · rw [val_vv (slotAt_lt_succ hH hvw.symm)]; simp [slotAt, vv, not_lt.2 h.le]
    · rw [val_vv (slotAt_lt_succ hH hvw)]; simp [slotAt, vv, h]

/-- **Two edges at `v` with the same induced colour use different virtual vertices of `v`.** -/
lemma slotAt_injOn (hH : ConnHyp G r Δ d sIn sOut m) {φ' : Sym2 (V × Fin (m + 1)) → ℕ}
    (hφ' : (oconn G r m sIn sOut).IsEdgeColoring φ') {v w w' : V} (hw : G.Adj v w)
    (hw' : G.Adj v w')
    (hcol : inducedColoring G r m sIn sOut φ' s(v, w) = inducedColoring G r m sIn sOut φ' s(v, w'))
    (hslot : slotAt G r sIn sOut v w = slotAt G r sIn sOut v w') : w = w' := by
  have h1 := oconn_adj_lift hH hw
  have h2 := oconn_adj_lift hH hw'
  rw [hslot] at h1
  have := hφ' h1 h2 (by simpa [inducedColoring, liftE, hslot] using hcol)
  exact congrArg Prod.fst this

/-! ### The connector: degree and out-degree -/

/-- The connector has max degree `≤ sIn + sOut`. -/
theorem oconn_degree_le (hH : ConnHyp G r Δ d sIn sOut m) (x : V × Fin (m + 1)) :
    ((oconn G r m sIn sOut).neighborSet x).ncard ≤ sIn + sOut := by
  classical
  obtain ⟨v, j⟩ := x
  set A : Finset V := {w ∈ outN G r v | outSlot G r sOut v w = j}
  set B : Finset V := {u ∈ inN G r v | inSlot G r sIn v u = j}
  have hsub : (oconn G r m sIn sOut).neighborSet (v, j) ⊆
      ↑(A.image (fun w => vv m w (inSlot G r sIn w v)) ∪
        B.image (fun u => vv m u (outSlot G r sOut u v))) := by
    rintro ⟨y, k⟩ hy
    simp only [SimpleGraph.mem_neighborSet, oconn] at hy
    simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe, A, B, mem_filter]
    rcases hy with ⟨hadj, hr, hj, hk⟩ | ⟨hadj, hr, hk, hj⟩
    · left
      refine ⟨y, ⟨mem_outN.2 ⟨hadj, hr⟩, hj.symm⟩, ?_⟩
      ext
      · rfl
      · simp only [vv, Fin.val_ofNat]
        rw [hk, Nat.mod_eq_of_lt (hk ▸ k.2)]
    · right
      refine ⟨y, ⟨mem_inN.2 ⟨hadj, hr⟩, hj.symm⟩, ?_⟩
      ext
      · rfl
      · simp only [vv, Fin.val_ofNat]
        rw [hk, Nat.mod_eq_of_lt (hk ▸ k.2)]
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  refine (card_union_le _ _).trans ?_
  have h1 : #(A.image (fun w => vv m w (inSlot G r sIn w v))) ≤ sOut :=
    card_image_le.trans (card_block_le hH.sOut_pos _ _)
  have h2 : #(B.image (fun u => vv m u (outSlot G r sOut u v))) ≤ sIn :=
    card_image_le.trans (card_block_le hH.sIn_pos _ _)
  omega

/-- The connector has an orientation with out-degree `≤ sOut` (the orientation of `G`), hence
arboricity `≤ sOut` (it is acyclic). -/
theorem oconn_hasOutDegLE (hH : ConnHyp G r Δ d sIn sOut m) :
    (oconn G r m sIn sOut).HasOutDegLE sOut := by
  classical
  refine ⟨{ out := fun x => ({w ∈ outN G r x.1 | outSlot G r sOut x.1 w = x.2} : Finset V).image
              (fun w => vv m w (inSlot G r sIn w x.1))
            adj_of_mem := ?_, mem_or_mem := ?_, card_out_le := ?_ }⟩
  · rintro ⟨v, j⟩ y hy
    simp only [mem_image, mem_filter] at hy
    obtain ⟨w, ⟨hw, hj⟩, rfl⟩ := hy
    obtain ⟨hvw, hr⟩ := mem_outN.1 hw
    left
    refine ⟨hvw, hr, hj.symm, ?_⟩
    exact val_vv (lt_of_lt_of_le (inSlot_lt hH hvw hr) hH.nIn_le) w
  · rintro ⟨v, j⟩ ⟨w, k⟩ h
    rcases h with ⟨hadj, hr, hj, hk⟩ | ⟨hadj, hr, hk, hj⟩
    · left
      simp only [mem_image, mem_filter]
      refine ⟨w, ⟨mem_outN.2 ⟨hadj, hr⟩, hj.symm⟩, ?_⟩
      ext
      · rfl
      · simp only [vv, Fin.val_ofNat]; rw [← hk, Nat.mod_eq_of_lt k.2]
    · right
      simp only [mem_image, mem_filter]
      refine ⟨v, ⟨mem_outN.2 ⟨hadj, hr⟩, hk.symm⟩, ?_⟩
      ext
      · rfl
      · simp only [vv, Fin.val_ofNat]; rw [← hj, Nat.mod_eq_of_lt j.2]
  · rintro ⟨v, j⟩
    exact card_image_le.trans (card_block_le hH.sOut_pos _ _)

/-! ### The colour classes -/

/-- Every colour class of the induced colouring has max degree `≤ max ⌈Δ/sIn⌉ ⌈d/sOut⌉`
(the number of virtual vertices). -/
theorem classGraph_degree_le (hH : ConnHyp G r Δ d sIn sOut m)
    {φ' : Sym2 (V × Fin (m + 1)) → ℕ} (hφ' : (oconn G r m sIn sOut).IsEdgeColoring φ') (i : ℕ)
    (v : V) :
    ((classGraph G (inducedColoring G r m sIn sOut φ') i).neighborSet v).ncard ≤
      max (Δ ⌈/⌉ sIn) (d ⌈/⌉ sOut) := by
  classical
  have hfin : ((classGraph G (inducedColoring G r m sIn sOut φ') i).neighborSet v) =
      ↑({w | (classGraph G (inducedColoring G r m sIn sOut φ') i).Adj v w} : Finset V) := by
    ext; simp
  rw [hfin, Set.ncard_coe_finset]
  have hmaps : Set.MapsTo (slotAt G r sIn sOut v)
      (({w | (classGraph G (inducedColoring G r m sIn sOut φ') i).Adj v w} : Finset V) : Set V)
      (range (max (Δ ⌈/⌉ sIn) (d ⌈/⌉ sOut))) := by
    intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    simpa using slotAt_lt hH hw.1
  have hinj : Set.InjOn (slotAt G r sIn sOut v)
      (({w | (classGraph G (inducedColoring G r m sIn sOut φ') i).Adj v w} : Finset V) : Set V) := by
    intro w hw w' hw' hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw hw'
    exact slotAt_injOn hH hφ' hw.1 hw'.1 (hw.2.trans hw'.2.symm) hs
  simpa using card_le_card_of_injOn _ hmaps hinj

/-- Every colour class has an orientation with out-degree `≤ ⌈d/sOut⌉` (the number of outgoing
groups), hence arboricity `≤ ⌈d/sOut⌉`. -/
theorem classGraph_hasOutDegLE (hH : ConnHyp G r Δ d sIn sOut m)
    {φ' : Sym2 (V × Fin (m + 1)) → ℕ} (hφ' : (oconn G r m sIn sOut).IsEdgeColoring φ') (i : ℕ) :
    (classGraph G (inducedColoring G r m sIn sOut φ') i).HasOutDegLE (d ⌈/⌉ sOut) := by
  classical
  refine ⟨{ out := fun v => {w ∈ outN G r v | inducedColoring G r m sIn sOut φ' s(v, w) = i}
            adj_of_mem := ?_, mem_or_mem := ?_, card_out_le := ?_ }⟩
  · intro v w hw
    simp only [mem_filter] at hw
    exact ⟨(mem_outN.1 hw.1).1, hw.2⟩
  · intro v w h
    rcases lt_or_gt_of_ne (hH.ne h.1) with hr | hr
    · left; simp only [mem_filter]; exact ⟨mem_outN.2 ⟨h.1, hr⟩, h.2⟩
    · right; simp only [mem_filter]
      refine ⟨mem_outN.2 ⟨h.1.symm, hr⟩, ?_⟩
      rw [Sym2.eq_swap]; exact h.2
  · intro v
    have hmaps : Set.MapsTo (slotAt G r sIn sOut v)
        (({w ∈ outN G r v | inducedColoring G r m sIn sOut φ' s(v, w) = i} : Finset V) : Set V)
        (range (d ⌈/⌉ sOut)) := by
      intro w hw
      simp only [coe_filter, Set.mem_ofPred_eq] at hw
      obtain ⟨hvw, hr⟩ := mem_outN.1 hw.1
      simp only [coe_range, Set.mem_Iio, slotAt, not_lt.2 hr.le, ite_false]
      exact outSlot_lt hH hvw hr
    have hinj : Set.InjOn (slotAt G r sIn sOut v)
        (({w ∈ outN G r v | inducedColoring G r m sIn sOut φ' s(v, w) = i} : Finset V) :
          Set V) := by
      intro w hw w' hw' hs
      simp only [coe_filter, Set.mem_ofPred_eq] at hw hw'
      exact slotAt_injOn hH hφ' (mem_outN.1 hw.1).1 (mem_outN.1 hw'.1).1 (hw.2.trans hw'.2.symm) hs
    simpa using card_le_card_of_injOn _ hmaps hinj

/-! ### Combining the two colourings -/

/-- **Theorem 5.3, correctness of the combination.** If `φ'` properly edge-colours the connector with
`K₁` colours and, for every colour `i`, `ψ i` properly edge-colours the class `i` with `K₂` colours,
then `⟨φ, ψ⟩` (encoded as `φ e · K₂ + ψ_{φ e} e`) properly edge-colours `G` with `K₁ · K₂` colours. -/
theorem theorem_5_3_combine (hH : ConnHyp G r Δ d sIn sOut m) {K₁ K₂ : ℕ}
    {φ' : Sym2 (V × Fin (m + 1)) → ℕ} (hφ' : (oconn G r m sIn sOut).IsProperEdgeColoring φ' K₁)
    {ψ : ℕ → Sym2 V → ℕ}
    (hψ : ∀ i, (classGraph G (inducedColoring G r m sIn sOut φ') i).IsProperEdgeColoring (ψ i) K₂) :
    G.IsProperEdgeColoring (fun e => inducedColoring G r m sIn sOut φ' e * K₂ +
      ψ (inducedColoring G r m sIn sOut φ' e) e) (K₁ * K₂) := by
  set φ := inducedColoring G r m sIn sOut φ'
  have hφlt : ∀ ⦃u v⦄, G.Adj u v → φ s(u, v) < K₁ := fun u v huv => hφ'.1 (oconn_adj_lift hH huv)
  have hψlt : ∀ ⦃u v⦄, G.Adj u v → ψ (φ s(u, v)) s(u, v) < K₂ :=
    fun u v huv => (hψ (φ s(u, v))).1 ⟨huv, rfl⟩
  refine ⟨fun u v huv => mixed_lt (hφlt huv) (hψlt huv), fun u v w huv huw he => ?_⟩
  obtain ⟨h1, h2⟩ := (mixed_eq_iff (hψlt huv) (hψlt huw)).1 he
  rw [h1] at h2
  exact (hψ (φ s(u, w))).2 ⟨huv, h1⟩ ⟨huw, rfl⟩ h2

/-- **Theorem 5.3, colour count.** Colouring the connector and then every colour class with the
procedure of Theorem 5.2 (`theorem_5_2_arboricity`: `Δ' + 6a'` colours for max degree `Δ'` and
out-degree `a'`) gives a proper edge colouring of `G` with
`(sIn + 7 sOut) · (max ⌈Δ/sIn⌉ ⌈d/sOut⌉ + 6 ⌈d/sOut⌉)` colours. -/
theorem theorem_5_3_count (hH : ConnHyp G r Δ d sIn sOut m) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c
      ((sIn + 7 * sOut) * (max (Δ ⌈/⌉ sIn) (d ⌈/⌉ sOut) + 6 * (d ⌈/⌉ sOut))) := by
  classical
  -- colour the connector by Theorem 5.2
  obtain ⟨_, _, _, _, _, hrun1, ⟨φ', hφ'⟩, _⟩ :=
    theorem_5_2_arboricity (oconn_hasOutDegLE hH) (oconn_degree_le hH)
  have hφ'p := hrun1 φ' hφ'
  -- colour every class by Theorem 5.2
  have hcls : ∀ i, ∃ ψ : Sym2 V → ℕ,
      (classGraph G (inducedColoring G r m sIn sOut φ') i).IsProperEdgeColoring ψ
        (max (Δ ⌈/⌉ sIn) (d ⌈/⌉ sOut) + 6 * (d ⌈/⌉ sOut)) := by
    intro i
    obtain ⟨_, _, _, _, _, hrun2, ⟨ψ, hψ⟩, _⟩ :=
      theorem_5_2_arboricity (classGraph_hasOutDegLE hH hφ'p.2 i)
        (classGraph_degree_le hH hφ'p.2 i)
    exact ⟨ψ, hrun2 ψ hψ⟩
  choose ψ hψ using hcls
  exact ⟨_, (theorem_5_3_combine hH (K₁ := sIn + sOut + 6 * sOut) hφ'p hψ).mono le_rfl
    (Nat.mul_le_mul_right _ (by omega))⟩

/-! ### The parameters of the paper and the final bound -/

lemma ceilDiv_sqrt_succ_le (n : ℕ) : n ⌈/⌉ (Nat.sqrt n + 1) ≤ Nat.sqrt n + 1 := by
  rw [ceilDiv_le_iff_le_mul (Nat.succ_pos _)]
  exact (Nat.lt_succ_sqrt n).le

lemma nat_sqrt_succ_le_real (n : ℕ) : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ Real.sqrt n + 1 := by
  push_cast
  linarith [Real.nat_sqrt_le_real_sqrt (a := n)]

/-- **Theorem 5.3** (number of colours). Let `G` have max degree `≤ Δ` and an acyclic orientation
(rank `r`) with out-degree `≤ d`. With groups of `sIn = ⌊√Δ⌋ + 1` incoming and `sOut = ⌊√d⌋ + 1`
outgoing edges, the algorithm (connector coloured by Theorem 5.2, classes coloured by Theorem 5.2)
produces a proper edge colouring with at most `(sIn + 7 sOut)² ≤ (√Δ + 7√d + 8)²` colours, i.e.
`Δ + O(√(Δ d) + d + √Δ)`. -/
theorem theorem_5_3 (hne : ∀ ⦃u v⦄, G.Adj u v → r u ≠ r v) (hout : ∀ u, #(outN G r u) ≤ d)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ Δ) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c
      ((Nat.sqrt Δ + 1 + 7 * (Nat.sqrt d + 1)) ^ 2) ∧
      (((Nat.sqrt Δ + 1 + 7 * (Nat.sqrt d + 1)) ^ 2 : ℕ) : ℝ) ≤
        (Real.sqrt Δ + 7 * Real.sqrt d + 8) ^ 2 := by
  set s := Nat.sqrt Δ + 1
  set q := Nat.sqrt d + 1
  have hs : Δ ⌈/⌉ s ≤ s := ceilDiv_sqrt_succ_le Δ
  have hq : d ⌈/⌉ q ≤ q := ceilDiv_sqrt_succ_le d
  have hH : ConnHyp G r Δ d s q (s + q) :=
    ⟨hne, hout, hdeg, Nat.succ_pos _, Nat.succ_pos _, by omega, by omega⟩
  obtain ⟨c, hc⟩ := theorem_5_3_count hH
  refine ⟨c, hc.mono le_rfl ?_, ?_⟩
  · rw [sq]
    refine Nat.mul_le_mul_left _ ?_
    have : max (Δ ⌈/⌉ s) (d ⌈/⌉ q) ≤ s + q := max_le (by omega) (by omega)
    omega
  · have h1 := nat_sqrt_succ_le_real Δ
    have h2 := nat_sqrt_succ_le_real d
    have h0 : (0 : ℝ) ≤ ((s + 7 * q : ℕ) : ℝ) := by positivity
    push_cast at h1 h2 ⊢
    have : (s : ℝ) + 7 * q ≤ Real.sqrt Δ + 7 * Real.sqrt d + 8 := by
      simp only [s, q]; push_cast; linarith
    exact pow_le_pow_left₀ (by positivity) this 2

/-- **Theorem 5.3** for graphs of arboricity `≤ a` (orientation of out-degree `≤ a`): orienting
along the H-partition of degree `3a` (then by identifiers), the algorithm uses at most
`(√Δ + 7√(3a) + 8)²` colours. -/
theorem theorem_5_3_arboricity {a : ℕ} (hG : G.HasOutDegLE a)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ Δ) :
    ∃ c : Sym2 V → ℕ, G.IsProperEdgeColoring c
      ((Nat.sqrt Δ + 1 + 7 * (Nat.sqrt (3 * a) + 1)) ^ 2) ∧
      (((Nat.sqrt Δ + 1 + 7 * (Nat.sqrt (3 * a) + 1)) ^ 2 : ℕ) : ℝ) ≤
        (Real.sqrt Δ + 7 * Real.sqrt (3 * a) + 8) ^ 2 := by
  classical
  obtain ⟨h, hH⟩ := exists_hPartition hG
  set n := Fintype.card V
  let e : V → ℕ := fun v => Fintype.equivFin V v
  have he : ∀ v, e v < n := fun v => (Fintype.equivFin V v).2
  let r : V → ℕ := fun v => h v * n + e v
  have hr : ∀ u v, r u ≤ r v → h u ≤ h v := by
    intro u v huv
    by_contra hlt
    push Not at hlt
    have : (h v + 1) * n ≤ h u * n := Nat.mul_le_mul_right _ hlt
    have := he v
    simp only [r] at huv
    nlinarith
  have hne : ∀ ⦃u v⦄, G.Adj u v → r u ≠ r v := by
    intro u v huv heq
    have h1 := hr u v heq.le
    have h2 := hr v u heq.ge
    have hh : h u = h v := le_antisymm h1 h2
    simp only [r, hh, Nat.add_left_cancel_iff] at heq
    exact G.ne_of_adj huv ((Fintype.equivFin V).injective (Fin.ext heq))
  have hout : ∀ u, #(outN G r u) ≤ 3 * a := by
    intro u
    refine le_trans (card_le_card fun v hv => ?_) (hH.card_le u)
    obtain ⟨huv, hlt⟩ := mem_outN.1 hv
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨huv, hr u v hlt.le⟩
  have := theorem_5_3 hne hout hdeg
  push_cast at this ⊢
  exact this

/-- **Theorem 5.3** (`Δ + o(Δ)` colours for `a = o(Δ)`): for every `ε > 0` there are `δ > 0` and
`N` such that the bound `(√Δ + 7√(3a) + 8)²` of `theorem_5_3_arboricity` is at most `(1 + ε) Δ`
whenever `Δ ≥ N` and `a ≤ δ Δ`. -/
theorem theorem_5_3_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ Δ a : ℕ, N ≤ Δ → (a : ℝ) ≤ δ * Δ →
      (Real.sqrt Δ + 7 * Real.sqrt (3 * a) + 8) ^ 2 ≤ (1 + ε) * Δ := by
  set η := min 1 ε / 8 with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 8 := by rw [hη]; linarith [min_le_left 1 ε]
  have hηε : 8 * η ≤ ε := by rw [hη]; linarith [min_le_right 1 ε]
  refine ⟨(η / 7) ^ 2 / 3, by positivity, ⌈(8 / η) ^ 2⌉₊, fun Δ a hN ha => ?_⟩
  set x := Real.sqrt Δ
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxx : x ^ 2 = Δ := Real.sq_sqrt (Nat.cast_nonneg _)
  -- `8 ≤ η √Δ`
  have h8 : 8 ≤ η * x := by
    have : (8 / η) ^ 2 ≤ (Δ : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
    have h' : 8 / η ≤ x := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 / η)]
      exact Real.sqrt_le_sqrt this
    rw [div_le_iff₀ hη0] at h'
    linarith
  -- `7 √(3a) ≤ η √Δ`
  have h7 : 7 * Real.sqrt (3 * a) ≤ η * x := by
    have h3 : (3 * a : ℝ) ≤ (η / 7 * x) ^ 2 := by
      rw [mul_pow, hxx]; nlinarith
    have := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq (by positivity)] at this
    linarith
  calc (x + 7 * Real.sqrt (3 * a) + 8) ^ 2 ≤ (x + η * x + η * x) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity); linarith
    _ = (1 + 2 * η) ^ 2 * x ^ 2 := by ring
    _ ≤ (1 + ε) * x ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
    _ = (1 + ε) * Δ := by rw [hxx]

end Podc.DeltaEdgeColoring
