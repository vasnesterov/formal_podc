import Papers.PODC2026.PLSTradeoff.Tradeoff

/-!
# Certifying and outputting a TS partition with `O(log n)` bits (Lemma 4.5)

The honest prover gives every node the identifier of its cluster (`⌈log₂ n⌉` bits, fixed width)
and one bit telling whether it lies in `X`. A node `v` sees radius `3t+2`; it reconstructs
`C̃_u = {w : d(u, w) ≤ 2t, CompID(w) = CompID(u)}` for the nodes `u` near it, outputs these sets
and the marked nodes, and checks for its own cluster `C̃_v` the weak diameter `≤ t`, the cost
ratio `≤ ε`, and two separation at `v` (no unmarked node of another cluster within distance 2 of
an unmarked `v`).

Compared with the paper (Appendix A): the paper searches clusters within radius `r = 3t + 2`
and claims an `r`-PLS, but a node then needs to see `B_r(u)` for `u` at distance up to `r + 2`,
i.e. radius about `2r + 2`. Searching within radius `2t` suffices (`Ĉ_u = Ĉ_v` for `u ∈ Ĉ_v` only
needs the two diameter checks), and then radius `3t + 2` is indeed enough.
-/

namespace PLSTradeoff

open Cslib.BitEncoding

open SimpleGraph
open Cslib.Local (GAgree loc mask loc_le gAgree_loc edist_le_edist_loc mask_of_le
  loc_edist_le_iff loc_adj_iff)

variable {V : Type*} [Fintype V]

/-! ### Fixed-width binary encoding -/

/-- The `w` lowest bits of `k`. -/
def bitsW (w k : ℕ) : List Bool := List.ofFn (fun i : Fin w => k.testBit i)

@[simp] lemma length_bitsW (w k : ℕ) : (bitsW w k).length = w := by simp [bitsW]

lemma bitsW_inj {w k k' : ℕ} (hk : k < 2 ^ w) (hk' : k' < 2 ^ w) (h : bitsW w k = bitsW w k') :
    k = k' := by
  have h' := List.ofFn_injective h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · exact congrFun h' ⟨i, hi⟩
  · push Not at hi
    rw [Nat.testBit_lt_two_pow (hk.trans_le (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (hk'.trans_le (Nat.pow_le_pow_right (by norm_num) hi))]

/-! ### Cluster identifiers -/

section ClusterId

variable {G : SimpleGraph V} {t : ℕ} {ε : ℝ}

open Classical in
/-- The identifier of the cluster of `v`: the least index (in `Fin n`) of a node of it. -/
noncomputable def TSPartition.cid (ts : TSPartition G t ε) (v : V) : ℕ :=
  (((Finset.univ.filter (· ∈ ts.cl v)).image (Fintype.equivFin V)).min'
    ⟨Fintype.equivFin V v, Finset.mem_image_of_mem _ (by simpa using ts.mem_cl v)⟩ :
      Fin (Fintype.card V))

lemma TSPartition.cid_lt (ts : TSPartition G t ε) (v : V) : ts.cid v < Fintype.card V := by
  unfold TSPartition.cid; exact Fin.isLt _

lemma TSPartition.cid_eq_iff (ts : TSPartition G t ε) {u v : V} :
    ts.cid u = ts.cid v ↔ ts.cl u = ts.cl v := by
  classical
  constructor
  · intro h
    unfold TSPartition.cid at h
    set su := (Finset.univ.filter (· ∈ ts.cl u)).image (Fintype.equivFin V) with hsu
    set sv := (Finset.univ.filter (· ∈ ts.cl v)).image (Fintype.equivFin V) with hsv
    have hu := Finset.min'_mem su
      ⟨Fintype.equivFin V u, Finset.mem_image_of_mem _ (by simpa using ts.mem_cl u)⟩
    have hv := Finset.min'_mem sv
      ⟨Fintype.equivFin V v, Finset.mem_image_of_mem _ (by simpa using ts.mem_cl v)⟩
    rw [Fin.val_inj.1 h] at hu
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.1 hu
    obtain ⟨y', hy', hyeq'⟩ := Finset.mem_image.1 hv
    have : y = y' := (Fintype.equivFin V).injective (hyeq.trans hyeq'.symm)
    subst this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    rw [← ts.cl_eq y u hy, ts.cl_eq y v hy']
  · intro h
    unfold TSPartition.cid
    simp only [h]

end ClusterId

/-! ### The scheme -/

/-- The radius of the scheme. -/
def certR (t : ℕ) : ℕ := 3 * t + 2

/-- The clusters reconstructed by `v` (in its localized view `H` with labels `ℓ`). -/
def recCl (H : SimpleGraph V) (t : ℕ) (ℓ : V → Label) (u : V) : Set V :=
  {w | H.edist u w ≤ (2 * t : ℕ) ∧ (parse (ℓ w)).1 = (parse (ℓ u)).1}

/-- The marked nodes. -/
def marked (ℓ : V → Label) : Set V := {w | (parse (ℓ w)).2 = [true]}

/-- The checks of node `v` on its view `(H, ℓ)`. -/
def CertCheck (H : SimpleGraph V) (t : ℕ) (ε : ℝ) (ℓ : V → Label) (v : V) : Prop :=
  (∀ a ∈ recCl H t ℓ v, ∀ b ∈ recCl H t ℓ v, H.edist a b ≤ t) ∧
  (((recCl H t ℓ v ∩ marked ℓ).ncard : ℝ) ≤ ε * (recCl H t ℓ v).ncard) ∧
  (∀ w, w ∉ recCl H t ℓ v → v ∉ marked ℓ → w ∉ marked ℓ → (2 : ℕ∞) < H.edist v w)

/-- The verifier: run `CertCheck` on the radius-`(3t+2)` view, output the reconstructed clusters
and the marked nodes. -/
noncomputable def certVer (t : ℕ) (ε : ℝ) (G : SimpleGraph V) (ℓ : V → Label) (v : V) :
    Option (TSOut V) :=
  open Classical in
  if CertCheck (loc G v (certR t)) t ε (mask G v (certR t) ℓ) v then
    some (recCl (loc G v (certR t)) t (mask G v (certR t) ℓ), marked (mask G v (certR t) ℓ))
  else none

/-- The honest labels: the cluster identifier (`⌈log₂ n⌉` bits) and the `X` bit. -/
noncomputable def certLabel {G : SimpleGraph V} {t : ℕ} {ε : ℝ} (ts : TSPartition G t ε)
    (v : V) : Label :=
  open Classical in
  encList [bitsW (Nat.clog 2 (Fintype.card V)) (ts.cid v), [decide (v ∈ ts.X)]]

/-- The honest prover (an arbitrary TS partition, if one exists). -/
noncomputable def certProv (t : ℕ) (ε : ℝ) (G : SimpleGraph V) (v : V) : Label :=
  open Classical in
  if h : Nonempty (TSPartition G t ε) then certLabel (Classical.choice h) v else []

section Proofs

variable {G : SimpleGraph V} {t : ℕ} {ε : ℝ}

omit [Fintype V] in
lemma recCl_loc_eq {ℓ : V → Label} {v u : V} {a : ℕ} (hu : G.edist v u ≤ a)
    (ha : a + 2 * t ≤ certR t) :
    recCl (loc G v (certR t)) t (mask G v (certR t) ℓ) u = recCl G t ℓ u := by
  ext w
  simp only [recCl, Set.mem_ofPred_eq]
  rw [loc_edist_le_iff hu ha le_rfl]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, ?_⟩
    have hvw : G.edist v w ≤ certR t := (edist_le_natCast_add hu hw).trans (by exact_mod_cast ha)
    rwa [mask_of_le hvw, mask_of_le (hu.trans (by exact_mod_cast (by omega : a ≤ certR t)))] at h
  · rintro ⟨hw, h⟩
    refine ⟨hw, ?_⟩
    have hvw : G.edist v w ≤ certR t := (edist_le_natCast_add hu hw).trans (by exact_mod_cast ha)
    rwa [mask_of_le hvw, mask_of_le (hu.trans (by exact_mod_cast (by omega : a ≤ certR t)))]

omit [Fintype V] in
lemma marked_mask_iff {ℓ : V → Label} {v w : V} (hw : G.edist v w ≤ certR t) :
    w ∈ marked (mask G v (certR t) ℓ) ↔ w ∈ marked ℓ := by
  simp only [marked, Set.mem_ofPred_eq, mask_of_le hw]

omit [Fintype V] in
lemma certVer_isLocal (t : ℕ) (ε : ℝ) :
    IsLocal (ι := Unit) (certR t) (fun G _ ℓ v => certVer (V := V) t ε G ℓ v) := by
  refine isLocal_iff.2 fun G I ℓ G' I' ℓ' v h => ?_
  simp only [certVer]
  rw [viewEq_loc_eq h, (viewEq_mask_eq h).2]

/-- Completeness: if `G` admits a TS partition, all nodes accept the honest labels. -/
lemma certVer_complete (ts : TSPartition G t ε) (v : V) :
    CertCheck (loc G v (certR t)) t ε (mask G v (certR t) (certLabel ts)) v := by
  classical
  have hv0 : G.edist v v ≤ (0 : ℕ) := by simp
  have hpar : ∀ w, parse (certLabel ts w) =
      (bitsW (Nat.clog 2 (Fintype.card V)) (ts.cid w), [decide (w ∈ ts.X)]) := by
    intro w; simp [certLabel]
  have hpow : ∀ w, ts.cid w < 2 ^ Nat.clog 2 (Fintype.card V) := fun w =>
    (ts.cid_lt w).trans_le (Nat.le_pow_clog (by norm_num) _)
  -- the reconstructed cluster of `v` is its true cluster
  have hrec : recCl G t (certLabel ts) v = ts.cl v := by
    ext w
    simp only [recCl, Set.mem_ofPred_eq, hpar]
    constructor
    · rintro ⟨-, h⟩
      have := bitsW_inj (hpow w) (hpow v) h
      rw [← ts.cl_eq_iff, ← ts.cid_eq_iff]; exact this
    · intro hw
      refine ⟨(ts.diam v v (ts.mem_cl v) w hw).trans (by exact_mod_cast (by omega : t ≤ 2 * t)),
        ?_⟩
      rw [(ts.cid_eq_iff).2 (ts.cl_eq w v hw)]
  have hmark : ∀ w, w ∈ marked (certLabel ts) ↔ w ∈ ts.X := by
    intro w; simp [marked, hpar]
  rw [CertCheck, recCl_loc_eq hv0 (by unfold certR; omega), hrec]
  have hvC : ∀ {w}, w ∈ ts.cl v → G.edist v w ≤ t := fun hw => ts.diam v v (ts.mem_cl v) _ hw
  refine ⟨fun a ha b hb => ?_, ?_, fun w hw hv hw' => ?_⟩
  · exact (loc_edist_le_iff (hvC ha) (by unfold certR; omega : t + t ≤ certR t) le_rfl).2
      (ts.diam v a ha b hb)
  · have : ts.cl v ∩ marked (mask G v (certR t) (certLabel ts)) = ts.cl v ∩ ts.X := by
      ext w
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨hw, hw'⟩
        exact ⟨hw, (hmark w).1 ((marked_mask_iff ((hvC hw).trans
          (by unfold certR; exact_mod_cast (by omega)))).1 hw')⟩
      · rintro ⟨hw, hw'⟩
        exact ⟨hw, (marked_mask_iff ((hvC hw).trans
          (by unfold certR; exact_mod_cast (by omega)))).2 ((hmark w).2 hw')⟩
    rw [this]; exact ts.ratio v
  · have hv' : v ∉ ts.X := fun h => hv ((marked_mask_iff (by simp)).2
      ((hmark v).2 h))
    by_cases hvw : G.edist v w ≤ certR t
    · have hw'' : w ∉ ts.X := fun h => hw' ((marked_mask_iff hvw).2 ((hmark w).2 h))
      have hne : ts.cl v ≠ ts.cl w := fun h => hw (h ▸ ts.mem_cl w)
      exact (ts.sep v w hv' hw'' hne).trans_le edist_le_edist_loc
    · push Not at hvw
      refine lt_of_lt_of_le ?_ edist_le_edist_loc
      exact lt_of_le_of_lt (by exact_mod_cast (by unfold certR; omega : 2 ≤ certR t)) hvw

omit [Fintype V] in
/-- Soundness: if all nodes accept, the reconstructed clusters form a TS partition for which all
outputs are correct. -/
lemma certVer_sound (ℓ : V → Label)
    (hall : ∀ v, CertCheck (loc G v (certR t)) t ε (mask G v (certR t) ℓ) v) :
    ∃ ts : TSPartition G t ε, ∀ v, TSOut.Correct ts v
      (recCl (loc G v (certR t)) t (mask G v (certR t) ℓ), marked (mask G v (certR t) ℓ)) := by
  have hv0 : ∀ v : V, G.edist v v ≤ (0 : ℕ) := by simp
  have hloc : ∀ v, recCl (loc G v (certR t)) t (mask G v (certR t) ℓ) v = recCl G t ℓ v :=
    fun v => recCl_loc_eq (hv0 v) (by unfold certR; omega)
  -- the checks, transferred to `G`
  have hdiam : ∀ v, ∀ a ∈ recCl G t ℓ v, ∀ b ∈ recCl G t ℓ v, G.edist a b ≤ t := by
    intro v a ha b hb
    have := (hall v).1 a (by rwa [hloc]) b (by rwa [hloc])
    exact edist_le_edist_loc.trans this
  have hself : ∀ v, v ∈ recCl G t ℓ v := fun v => ⟨by simp, rfl⟩
  have hcl : ∀ u v, u ∈ recCl G t ℓ v → recCl G t ℓ u = recCl G t ℓ v := by
    intro u v hu
    have hvu : G.edist v u ≤ t := hdiam v v (hself v) u hu
    ext y
    constructor
    · intro hy
      have huy : G.edist u y ≤ t := hdiam u u (hself u) y hy
      exact ⟨(edist_le_natCast_add hvu huy).trans (by exact_mod_cast (by omega)), hy.2.trans hu.2⟩
    · intro hy
      have hvy : G.edist v y ≤ t := hdiam v v (hself v) y hy
      refine ⟨?_, hy.2.trans hu.2.symm⟩
      rw [SimpleGraph.edist_comm] at hvu
      exact (edist_le_natCast_add hvu hvy).trans (by exact_mod_cast (by omega))
  have hmarkv : ∀ v w, G.edist v w ≤ certR t →
      (w ∈ marked (mask G v (certR t) ℓ) ↔ w ∈ marked ℓ) := fun v w hw => marked_mask_iff hw
  refine ⟨{ cl := recCl G t ℓ
            mem_cl := hself
            cl_eq := hcl
            X := marked ℓ
            twoSep := twoSep_of_distSep ?_
            diam := hdiam
            ratio := ?_ }, fun v u hu => ?_⟩
  · intro u w hu hw hne
    by_contra hle
    push Not at hle
    have hw' : w ∉ recCl (loc G u (certR t)) t (mask G u (certR t) ℓ) u := by
      rw [hloc]; intro h; exact hne (hcl w u h).symm
    have := (hall u).2.2 w hw' (fun h => hu ((hmarkv u u (by simp)).1 h))
      (fun h => hw ((hmarkv u w (hle.trans (by unfold certR; exact_mod_cast (by omega)))).1 h))
    rw [← not_le] at this
    exact this ((loc_edist_le_iff (hv0 u) (by unfold certR; omega : 0 + 2 ≤ certR t) le_rfl).2
      hle)
  · intro v
    have h := (hall v).2.1
    rw [hloc] at h
    have : recCl G t ℓ v ∩ marked (mask G v (certR t) ℓ) = recCl G t ℓ v ∩ marked ℓ := by
      ext w
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨hw, hw'⟩
        exact ⟨hw, (hmarkv v w ((hdiam v v (hself v) w hw).trans
          (by unfold certR; exact_mod_cast (by omega)))).1 hw'⟩
      · rintro ⟨hw, hw'⟩
        exact ⟨hw, (hmarkv v w ((hdiam v v (hself v) w hw).trans
          (by unfold certR; exact_mod_cast (by omega)))).2 hw'⟩
    rwa [this] at h
  · -- correctness of the outputs
    obtain ⟨w, hw, hwu⟩ := hu
    have hvw : G.edist v w ≤ t := hdiam v v (hself v) w hw
    have hvu : G.edist v u ≤ (t + 2 : ℕ) := edist_le_natCast_add hvw hwu
    refine ⟨recCl_loc_eq hvu (by unfold certR; omega), fun y hy => ?_⟩
    have huy : G.edist u y ≤ t := hdiam u u (hself u) y hy
    exact hmarkv v y ((edist_le_natCast_add hvu huy).trans
      (by unfold certR; exact_mod_cast (by omega)))

end Proofs

omit [Fintype V] in
lemma certVer_eq_some {t : ℕ} {ε : ℝ} {G : SimpleGraph V} {ℓ : V → Label} {v : V}
    (h : CertCheck (loc G v (certR t)) t ε (mask G v (certR t) ℓ) v) :
    certVer t ε G ℓ v =
      some (recCl (loc G v (certR t)) t (mask G v (certR t) ℓ), marked (mask G v (certR t) ℓ)) := by
  classical
  unfold certVer
  exact ite_eq_left h

omit [Fintype V] in
lemma certCheck_of_isSome {t : ℕ} {ε : ℝ} {G : SimpleGraph V} {ℓ : V → Label} {v : V}
    (h : (certVer t ε G ℓ v).isSome) :
    CertCheck (loc G v (certR t)) t ε (mask G v (certR t) ℓ) v := by
  classical
  by_contra hc
  unfold certVer at h
  rw [ite_eq_right hc] at h
  exact absurd h (by simp)

lemma certProv_eq {t : ℕ} {ε : ℝ} {G : SimpleGraph V} (hne : Nonempty (TSPartition G t ε)) :
    certProv t ε G = certLabel (Classical.choice hne) := by
  classical
  funext v
  unfold certProv
  exact dite_eq_left hne

/-- **Lemma 4.5** of [Filtser–Fischer, PODC 2026]: in any graph family and for any `t`, `ε`,
there is a `(3t+2)`-PLS that certifies and outputs a `(t, ε)`-TS partition with cost
`2⌈log₂ n⌉ + 4 = O(log n)`. -/
theorem exists_tsCert (𝒢 : Set (SimpleGraph V)) (t : ℕ) (ε : ℝ) :
    ∃ S : TSCert 𝒢 t ε (3 * t + 2), S.CostLE (2 * Nat.clog 2 (Fintype.card V) + 4) := by
  classical
  refine ⟨{ prov := certProv t ε
            ver := certVer t ε
            isLocal := certVer_isLocal t ε
            complete := fun G _ hne v => ?_
            sound := fun G _ ℓ hall => ?_ }, fun G _ v => ?_⟩
  · rw [certProv_eq hne, certVer_eq_some (certVer_complete _ v)]
    rfl
  · have hall' := fun v => certCheck_of_isSome (hall v)
    obtain ⟨ts, hts⟩ := certVer_sound ℓ hall'
    refine ⟨ts, fun v o ho => ?_⟩
    rw [certVer_eq_some (hall' v), Option.some.injEq] at ho
    exact ho ▸ hts v
  · by_cases hne : Nonempty (TSPartition G t ε)
    · show (certProv t ε G v).length ≤ _
      rw [certProv_eq hne]
      simp only [certLabel, length_encList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, length_bitsW, List.length_cons, List.length_nil]
      omega
    · show (certProv t ε G v).length ≤ _
      unfold certProv
      rw [dite_eq_right hne]
      simp

end PLSTradeoff
