import Papers.PODC2026.PLSTradeoff.TSPartition
import Papers.PODC2026.PLSTradeoff.Encoding

/-!
# TS partitions imply a tradeoff (Lemma 3.2)

Given an `R`-PLS that certifies and outputs a `(t, ε)`-TS partition with cost `c`, every 1-PLS of
cost `p` can be turned into a `max R (2t+2)`-PLS of cost `2c + 2⌈ε(2p+1)⌉ + 2`
(`tradeoff_of_tsCert`), i.e. an `O(t)`-PLS with cost `O(⌈εp⌉ + c)`.

The construction follows the paper:
* the label of `v` is the pair (TS label, `ProofPart`), where the `ProofPart`s of the nodes of a
  cluster `C` (sorted by identifier) are consecutive blocks of the encoding of the 1-PLS labels of
  `C ∩ X` (`ppLabel`);
* every node runs the TS verifier and decodes the 1-PLS labels `ℓ_X` of the nodes of `X` near its
  cluster (`decodeX`); a node with `B₁(v) ⊆ X` runs the 1-PLS verifier on `ℓ_X`; the leader of a
  cluster (the largest identifier in `C \ X`) checks that `ℓ_X` extends to `C \ X` so that all
  nodes of `H_C` accept (`CoreCheck`).

Lemma 3.5 (`sound_of_good`) is the combinatorial core of soundness.
-/

namespace PLSTradeoff

open SimpleGraph SinklessOrientation

variable {V : Type*} {ι : Type*}

section Helpers

variable {G : SimpleGraph V}

lemma eq_or_adj_of_edist_le_one {u z : V} (h : G.edist u z ≤ 1) : z = u ∨ G.Adj u z := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, G.edist u z = k :=
    (ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by decide) h)).imp fun _ h => h.symm
  have hk1 : k ≤ 1 := by exact_mod_cast hk ▸ h
  interval_cases k
  · exact Or.inl (edist_eq_zero_iff.1 hk).symm
  · exact Or.inr (edist_eq_one_iff_adj.1 hk)

lemma edist_le_one_of_eq_or_adj {u z : V} (h : z = u ∨ G.Adj u z) : G.edist u z ≤ 1 := by
  rcases h with rfl | h
  · simp
  · rw [edist_eq_one_iff_adj.2 h]

lemma viewEq_self {α : Type*} {R : ℕ} {I : V → ι} {ℓ ℓ' : V → α} {u : V}
    (h : ∀ z, G.edist u z ≤ R → ℓ z = ℓ' z) : ViewEq R G I ℓ G I ℓ' u :=
  ⟨fun _ _ _ => Iff.rfl, fun z hz => ⟨rfl, h z hz⟩⟩

lemma edist_le_add {a b c : V} {m n : ℕ} (h1 : G.edist a b ≤ m) (h2 : G.edist b c ≤ n) :
    G.edist a c ≤ (m + n : ℕ) := by
  calc G.edist a c ≤ G.edist a b + G.edist b c := SimpleGraph.edist_triangle
    _ ≤ m + n := add_le_add h1 h2
    _ = ((m + n : ℕ) : ℕ∞) := by push_cast; rfl

end Helpers

/-! ### Sorted clusters and the encoding of `ℓ_X` on a cluster -/

section Sorted

variable [Fintype V] [LinearOrder V]

open Classical in
/-- The nodes of `C`, sorted by identifier. -/
noncomputable def sortedL (C : Set V) : List V := (Finset.univ.filter (· ∈ C)).sort (· ≤ ·)

lemma mem_sortedL {C : Set V} {u : V} : u ∈ sortedL C ↔ u ∈ C := by
  classical
  simp [sortedL]

lemma nodup_sortedL (C : Set V) : (sortedL C).Nodup := by
  classical
  exact Finset.sort_nodup _ _

lemma length_sortedL (C : Set V) : (sortedL C).length = C.ncard := by
  classical
  rw [sortedL, Finset.length_sort]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext; simp

/-- Splitting a label `(TSLabel, ProofPart)`. Malformed labels are read as `([], [])`. -/
def parse (w : Label) : Label × Label :=
  match decList w with
  | [a, b] => (a, b)
  | _ => ([], [])

@[simp] lemma parse_encList (a b : Label) : parse (encList [a, b]) = (a, b) := by
  simp [parse]

/-- The TS-label part of a labeling. -/
def tsPart (ℓ : V → Label) : V → Label := fun u => (parse (ℓ u)).1

/-- The `ProofPart` part of a labeling. -/
def ppPart (ℓ : V → Label) : V → Label := fun u => (parse (ℓ u)).2

/-- `DecodeLex`: the label `ℓ_X(u)` decoded from the `ProofPart`s of the cluster `clu u`, where
`xs` marks the separating set. -/
noncomputable def decodeX (clu : V → Set V) (xs : Set V) (PP : V → Label) (u : V) : Label :=
  (decList ((sortedL (clu u)).map PP).flatten).getD ((sortedL (clu u ∩ xs)).idxOf u) []

/-- `XLabel(C, X)`: the encoding of the labels `Pv` of the nodes of `C ∩ X` (sorted). -/
noncomputable def xEnc (Pv : V → Label) (C X : Set V) : Label :=
  encList ((sortedL (C ∩ X)).map Pv)

/-- `Lex(C, XLabel(C, X), v)`: the block of `XLabel(C, X)` stored at `v ∈ C`. -/
noncomputable def ppLabel (Pv : V → Label) (C X : Set V) (v : V) : Label :=
  chunk (xEnc Pv C X) (cdiv (xEnc Pv C X).length C.ncard) ((sortedL C).idxOf v)

/-- Decoding the blocks stored on a cluster gives back the encoded labels. -/
lemma decodeX_eq {clu : V → Set V} {xs : Set V} {PP : V → Label} {C X : Set V}
    {Pv : V → Label} {u : V} (hclu : clu u = C) (hxs : C ∩ xs = C ∩ X)
    (hPP : ∀ y ∈ C, PP y = ppLabel Pv C X y) (hu : u ∈ C) (huX : u ∈ X) :
    decodeX clu xs PP u = Pv u := by
  unfold decodeX
  rw [hclu, hxs]
  have hmap : (sortedL C).map PP =
      (sortedL C).map (fun y => chunk (xEnc Pv C X) (cdiv (xEnc Pv C X).length C.ncard)
        ((sortedL C).idxOf y)) :=
    List.map_congr_left (fun y hy => hPP y (mem_sortedL.1 hy))
  have hpos : 0 < C.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨u, hu⟩
  rw [hmap, map_idxOf_eq _ (nodup_sortedL C), length_sortedL,
    flatten_chunks _ hpos, xEnc, decList_encList]
  have hlt : (sortedL (C ∩ X)).idxOf u < (sortedL (C ∩ X)).length :=
    List.idxOf_lt_length_iff.2 (mem_sortedL.2 ⟨hu, huX⟩)
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf]

lemma decodeX_congr {clu clu' : V → Set V} {xs xs' : Set V} {PP PP' : V → Label} {u : V}
    (hclu : clu u = clu' u) (hxs : clu u ∩ xs = clu' u ∩ xs')
    (hPP : ∀ y ∈ clu u, PP y = PP' y) : decodeX clu xs PP u = decodeX clu' xs' PP' u := by
  unfold decodeX
  rw [← hxs, ← hclu, List.map_congr_left (fun y hy => hPP y (mem_sortedL.1 hy))]

lemma length_ppLabel_le {Pv : V → Label} {C X : Set V} {v : V} {p m : ℕ} (hC : C.Nonempty)
    (hp : ∀ x ∈ C ∩ X, (Pv x).length ≤ p) (hm : (C ∩ X).ncard * (2 * p + 1) ≤ C.ncard * m) :
    (ppLabel Pv C X v).length ≤ m := by
  refine (length_chunk_le _ _ _).trans (cdiv_le_of_le_mul ((Set.ncard_pos (Set.toFinite _)).2 hC) ?_)
  refine le_trans ?_ hm
  rw [xEnc]
  refine (length_encList_le _ p ?_).trans ?_
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    exact hp x (mem_sortedL.1 hx)
  · rw [List.length_map, length_sortedL]

end Sorted

/-! ### Lemma 3.5 -/

section Lemma35

variable {G : SimpleGraph V} {t : ℕ} {ε : ℝ}

/-- Lemma 3.5: if a labeling `ℓ_X` of the separating set is *good* (nodes whose closed
neighbourhood lies in `X` accept it) and for every cluster `C` it has a *good extension* (making
all nodes of `H_C` accept), then the configuration satisfies `P` (by soundness of the 1-PLS). -/
theorem sound_of_good {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop}
    (S1 : PLS 𝒢 P 1) (hG : G ∈ 𝒢) (I : V → ι) (ts : TSPartition G t ε) (ℓX : V → Label)
    (hgood : ∀ v, (∀ u, (u = v ∨ G.Adj v u) → u ∈ ts.X) → S1.ver G I ℓX v = true)
    (hext : ∀ w, ∃ ℓC : V → Label, (∀ x ∈ ts.X, ℓC x = ℓX x) ∧
      ∀ u ∈ ts.H w, S1.ver G I ℓC u = true) :
    P G I := by
  classical
  -- one extension per cluster (indexed by the cluster as a set)
  let ext : Set V → V → Label := fun C =>
    if h : ∃ w, ts.cl w = C then Classical.choose (hext (Classical.choose h)) else ℓX
  have ext_spec : ∀ w, (∀ x ∈ ts.X, ext (ts.cl w) x = ℓX x) ∧
      ∀ u ∈ ts.H w, S1.ver G I (ext (ts.cl w)) u = true := by
    intro w
    have h : ∃ w', ts.cl w' = ts.cl w := ⟨w, rfl⟩
    have hw' : ts.cl (Classical.choose h) = ts.cl w := Classical.choose_spec h
    have hH : ts.H (Classical.choose h) = ts.H w := by
      simp only [TSPartition.H, hw']
    simp only [ext, dite_eq_left h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hext (Classical.choose h))
    exact ⟨h1, hH ▸ h2⟩
  let ℓV : V → Label := fun u => if u ∈ ts.X then ℓX u else ext (ts.cl u) u
  refine S1.sound G hG I ℓV (fun u => ?_)
  by_cases hB : ∀ y, (y = u ∨ G.Adj u y) → y ∈ ts.X
  · rw [S1.isLocal G I ℓV G I ℓX u (viewEq_self fun z hz => ?_)]
    · exact hgood u hB
    · simp [ℓV, hB z (eq_or_adj_of_edist_le_one hz)]
  · obtain ⟨w, hw⟩ := ts.mem_H_of_not_subset hB
    rw [S1.isLocal G I ℓV G I (ext (ts.cl w)) u (viewEq_self fun z hz => ?_)]
    · exact (ext_spec w).2 u hw
    · rcases ts.ball_subset_of_mem_H hw z (eq_or_adj_of_edist_le_one hz) with hz' | hz'
      · by_cases hzX : z ∈ ts.X
        · simp [ℓV, hzX, (ext_spec w).1 z hzX]
        · simp [ℓV, hzX, ts.cl_eq z w hz']
      · simp [ℓV, hz', (ext_spec w).1 z hz']

end Lemma35

/-! ### The verifier and the prover of Lemma 3.2 -/

section Construction

variable [Fintype V] [LinearOrder V]

/-- The checks of node `v` (assertions (3) and (4) of the paper), given its TS output `o`, in a
(localized) configuration `(H, J, ℓ)`. -/
def CoreCheck (ver1 : SimpleGraph V → (V → ι) → (V → Label) → V → Bool) (o : TSOut V)
    (H : SimpleGraph V) (J : V → ι) (ℓ : V → Label) (v : V) : Prop :=
  ((∀ u, (u = v ∨ H.Adj v u) → u ∈ o.2) → ver1 H J (decodeX o.1 o.2 (ppPart ℓ)) v = true) ∧
  ((v ∉ o.2 ∧ ∀ w ∈ o.1 v, w ∉ o.2 → w ≤ v) →
    ∃ ℓ' : V → Label,
      (∀ x ∈ o.2, (∃ w ∈ o.1 v, H.edist w x ≤ 2) → ℓ' x = decodeX o.1 o.2 (ppPart ℓ) x) ∧
      ∀ u, (∃ y, (y = u ∨ H.Adj u y) ∧ y ∈ o.1 v ∧ y ∉ o.2) → ver1 H J ℓ' u = true)

variable {𝒢 : Set (SimpleGraph V)} {t R : ℕ} {ε : ℝ}

/-- The verifier of the constructed `O(t)`-PLS: run the TS verifier on the TS labels, then the
checks `CoreCheck` on the configuration seen within radius `Rt`. -/
noncomputable def verT (S : TSCert 𝒢 t ε R)
    (ver1 : SimpleGraph V → (V → ι) → (V → Label) → V → Bool) (Rt : ℕ)
    (G : SimpleGraph V) (I : V → ι) (ℓ : V → Label) (v : V) : Bool :=
  open Classical in
  match S.ver G (tsPart ℓ) v with
  | none => false
  | some o => decide (CoreCheck ver1 o (loc G v Rt) (mask G v Rt I) (mask G v Rt ℓ) v)

lemma verT_isLocal (S : TSCert 𝒢 t ε R)
    (ver1 : SimpleGraph V → (V → ι) → (V → Label) → V → Bool) {Rt : ℕ} (hR : R ≤ Rt) :
    IsLocal Rt (verT S ver1 Rt) := by
  intro G I ℓ G' I' ℓ' v h
  have hts : S.ver G (tsPart ℓ) v = S.ver G' (tsPart ℓ') v :=
    S.isLocal G (fun _ => ()) (tsPart ℓ) G' (fun _ => ()) (tsPart ℓ') v
      ⟨h.1.mono_radius hR, fun u hu => ⟨rfl, by
        simp only [tsPart, (h.2 u (hu.trans (by exact_mod_cast hR))).2]⟩⟩
  have hloc := viewEq_loc_eq h
  obtain ⟨hI, hℓ⟩ := viewEq_mask_eq h
  unfold verT
  rw [hts, hloc, hI, hℓ]

/-- The honest prover of the constructed PLS. It uses the TS partition output by the honest TS
labels (which exists by soundness of the TS scheme). -/
noncomputable def provT (S : TSCert 𝒢 t ε R) (prov1 : SimpleGraph V → (V → ι) → V → Label)
    (G : SimpleGraph V) (I : V → ι) (v : V) : Label :=
  open Classical in
  if h : G ∈ 𝒢 ∧ ∀ v, (S.ver G (S.prov G) v).isSome then
    encList [S.prov G v,
      ppLabel (prov1 G I) ((Classical.choose (S.sound G h.1 _ h.2)).cl v)
        (Classical.choose (S.sound G h.1 _ h.2)).X v]
  else []

omit [Fintype V] [LinearOrder V] in
/-- Distances around the cluster of `v`. -/
lemma edist_near {G : SimpleGraph V} (ts : TSPartition G t ε) {v w u y : V}
    (hw : w ∈ ts.cl v) (hu : G.edist w u ≤ 2) (hy : y ∈ ts.cl u) :
    G.edist v y ≤ (2 * t + 2 : ℕ) := by
  have h1 : G.edist v w ≤ t := ts.diam v v (ts.mem_cl v) w hw
  have h2 : G.edist u y ≤ t := ts.diam u u (ts.mem_cl u) y hy
  have := edist_le_add (edist_le_add h1 hu) h2
  exact this.trans (by exact_mod_cast (by omega : t + 2 + t ≤ 2 * t + 2))

/-- The local decoding at `v` agrees with the global decoding near `v`'s cluster. -/
lemma decodeX_local {G : SimpleGraph V} (ts : TSPartition G t ε) {v : V} {o : TSOut V}
    (ho : o.Correct ts v) {Rt : ℕ} (hRt : 2 * t + 2 ≤ Rt) (ℓ : V → Label) {u : V}
    (hu : ∃ w ∈ ts.cl v, G.edist w u ≤ 2) :
    decodeX o.1 o.2 (ppPart (mask G v Rt ℓ)) u = decodeX ts.cl ts.X (ppPart ℓ) u := by
  obtain ⟨h1, h2⟩ := ho u hu
  obtain ⟨w, hw, hwu⟩ := hu
  apply decodeX_congr h1
  · rw [h1]; ext y
    simp only [Set.mem_inter_iff]
    exact ⟨fun ⟨hy, hy'⟩ => ⟨hy, (h2 y hy).1 hy'⟩, fun ⟨hy, hy'⟩ => ⟨hy, (h2 y hy).2 hy'⟩⟩
  · intro y hy
    rw [h1] at hy
    simp only [ppPart]
    rw [mask_of_le ((edist_near ts hw hwu hy).trans (by exact_mod_cast hRt))]

omit [Fintype V] [LinearOrder V] in
/-- Membership in `o.2` near the cluster of `v` is membership in `X`. -/
lemma mem_out_iff {G : SimpleGraph V} (ts : TSPartition G t ε) {v : V} {o : TSOut V}
    (ho : o.Correct ts v) {u : V} (hu : ∃ w ∈ ts.cl v, G.edist w u ≤ 2) :
    u ∈ o.2 ↔ u ∈ ts.X :=
  (ho u hu).2 u (ts.mem_cl u)

end Construction

/-! ### Lemma 3.2 -/

section Main

variable [Fintype V] [LinearOrder V]

/-- **Lemma 3.2** of [Filtser–Fischer, PODC 2026] (TS partition implies tradeoff). Suppose every
graph of `𝒢` admits a `(t, ε)`-TS partition and such a partition can be certified and outputted
by an `R`-PLS of cost `c`. Then every 1-PLS for a predicate `P` on `𝒢` with cost `p` yields a
`max R (2t+2)`-PLS for `P` with cost `2c + 2⌈ε(2p+1)⌉ + 2 = O(⌈εp⌉ + c)`. -/
theorem tradeoff_of_tsCert {𝒢 : Set (SimpleGraph V)} {P : SimpleGraph V → (V → ι) → Prop}
    {t R c p : ℕ} {ε : ℝ} (S : TSCert 𝒢 t ε R) (hc : S.CostLE c)
    (hex : ∀ G ∈ 𝒢, Nonempty (TSPartition G t ε)) (S1 : PLS 𝒢 P 1) (hp : S1.CostLE p) :
    ∃ St : PLS 𝒢 P (max R (2 * t + 2)), St.CostLE (2 * c + 2 * ⌈ε * (2 * p + 1)⌉₊ + 2) := by
  classical
  set Rt := max R (2 * t + 2) with hRt_def
  have hR : R ≤ Rt := le_max_left _ _
  have hRt : 2 * t + 2 ≤ Rt := le_max_right _ _
  -- the honest TS labels are accepted everywhere on graphs of `𝒢`
  have hacc : ∀ G ∈ 𝒢, ∀ v, (S.ver G (S.prov G) v).isSome :=
    fun G hG => S.complete G hG (hex G hG)
  refine ⟨{ prov := provT S S1.prov
            ver := verT S S1.ver Rt
            isLocal := verT_isLocal S S1.ver hR
            complete := ?_
            sound := ?_ }, ?_⟩
  · ---------------- completeness ----------------
    intro G hG I hP v
    have h : G ∈ 𝒢 ∧ ∀ v, (S.ver G (S.prov G) v).isSome := ⟨hG, hacc G hG⟩
    set ts := Classical.choose (S.sound G h.1 _ h.2) with hts_def
    have hts : ∀ v o, S.ver G (S.prov G) v = some o → o.Correct ts v :=
      Classical.choose_spec (S.sound G h.1 _ h.2)
    have hprov : provT S S1.prov G I = fun v =>
        encList [S.prov G v, ppLabel (S1.prov G I) (ts.cl v) ts.X v] := by
      funext v; simp only [provT, dite_eq_left h, hts_def]
    have htsPart : tsPart (provT S S1.prov G I) = S.prov G := by
      funext v; simp [hprov, tsPart]
    -- global decoding of the honest labels gives the 1-PLS labels on `X`
    have hdec : ∀ u ∈ ts.X,
        decodeX ts.cl ts.X (ppPart (provT S S1.prov G I)) u = S1.prov G I u := by
      intro u hu
      refine decodeX_eq rfl rfl (fun y hy => ?_) (ts.mem_cl u) hu
      simp only [ppPart, hprov, parse_encList]
      rw [ts.cl_eq y u hy]
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (h.2 v)
    have hoC : o.Correct ts v := hts v o ho
    simp only [verT, htsPart, ho, decide_eq_true_eq]
    set ℓt := provT S S1.prov G I
    have hvC : ∀ {w}, w ∈ ts.cl v → G.edist v w ≤ t := fun hw => ts.diam v v (ts.mem_cl v) _ hw
    refine ⟨fun hB => ?_, fun _ => ⟨S1.prov G I, fun x hx hxw => ?_, fun u hu => ?_⟩⟩
    · -- assertion (3)
      have hv0 : G.edist v v ≤ (0 : ℕ) := by simp
      rw [ver_loc_mask S1.isLocal I _ _ hv0 (by omega) (fun _ _ => rfl)]
      rw [S1.isLocal G I _ G I (S1.prov G I) v (viewEq_self fun z hz => ?_)]
      · exact S1.complete G hG I hP v
      · have hz := eq_or_adj_of_edist_le_one hz
        have hnear : ∃ w ∈ ts.cl v, G.edist w z ≤ 2 :=
          ⟨v, ts.mem_cl v, hz.elim (fun h => by simp [h]) (fun h => by
            rw [edist_eq_one_iff_adj.2 h]; norm_num)⟩
        have hzo : z ∈ o.2 := hB z (hz.imp id (fun h => (loc_adj_iff hv0 (by omega)).2 h))
        rw [decodeX_local ts hoC hRt _ hnear]
        exact hdec z ((mem_out_iff ts hoC hnear).1 hzo)
    · -- assertion (4): the labels agree with the honest ones on `X` near the cluster
      obtain ⟨w, hw, hwx⟩ := hxw
      rw [(hoC v ⟨v, ts.mem_cl v, by simp⟩).1] at hw
      have hwx' : G.edist w x ≤ 2 :=
        (loc_edist_le_iff (hvC hw) (by omega : t + 2 ≤ Rt) le_rfl).1 hwx
      have hnear : ∃ w ∈ ts.cl v, G.edist w x ≤ 2 := ⟨w, hw, hwx'⟩
      rw [decodeX_local ts hoC hRt _ hnear]
      exact (hdec x ((mem_out_iff ts hoC hnear).1 hx)).symm
    · obtain ⟨y, hy, hyC, -⟩ := hu
      rw [(hoC v ⟨v, ts.mem_cl v, by simp⟩).1] at hyC
      have hvy := hvC hyC
      have hvu : G.edist v u ≤ (t + 1 : ℕ) := by
        rcases hy with rfl | hy
        · exact hvy.trans (by exact_mod_cast (by omega : t ≤ t + 1))
        · exact edist_le_add hvy (edist_le_one_of_eq_or_adj (Or.inr (loc_le G v Rt hy).symm))
      rw [ver_loc_mask S1.isLocal I _ _ hvu (by omega) (fun _ _ => rfl)]
      exact S1.complete G hG I hP u
  · ---------------- soundness ----------------
    intro G hG I ℓ hall
    have hsome : ∀ v, (S.ver G (tsPart ℓ) v).isSome := by
      intro v
      have := hall v
      simp only [verT] at this
      cases h : S.ver G (tsPart ℓ) v with
      | none => rw [h] at this; exact absurd this (by simp)
      | some o => simp
    obtain ⟨ts, hts⟩ := S.sound G hG _ hsome
    have hcheck : ∀ v, ∃ o, S.ver G (tsPart ℓ) v = some o ∧ o.Correct ts v ∧
        CoreCheck S1.ver o (loc G v Rt) (mask G v Rt I) (mask G v Rt ℓ) v := by
      intro v
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (hsome v)
      have := hall v
      simp only [verT, ho, decide_eq_true_eq] at this
      exact ⟨o, ho, hts v o ho, this⟩
    let ℓX : V → Label := decodeX ts.cl ts.X (ppPart ℓ)
    refine sound_of_good S1 hG I ts ℓX (fun v hB => ?_) (fun w => ?_)
    · -- good `X`-labeling
      obtain ⟨o, -, hoC, hc3, -⟩ := hcheck v
      have hv0 : G.edist v v ≤ (0 : ℕ) := by simp
      have hnear : ∀ {z}, G.edist v z ≤ 1 → ∃ w ∈ ts.cl v, G.edist w z ≤ 2 :=
        fun hz => ⟨v, ts.mem_cl v, hz.trans (by norm_num)⟩
      have := hc3 (fun u hu => (mem_out_iff ts hoC (hnear (edist_le_one_of_eq_or_adj
        (hu.imp id (fun h => (loc_adj_iff hv0 (by omega)).1 h))))).2
        (hB u (hu.imp id (fun h => (loc_adj_iff hv0 (by omega)).1 h))))
      rw [ver_loc_mask S1.isLocal I _ _ hv0 (by omega) (fun _ _ => rfl)] at this
      rwa [S1.isLocal G I _ G I ℓX v (viewEq_self fun z hz => decodeX_local ts hoC hRt ℓ
        (hnear hz))] at this
    · -- good extension for the cluster of `w`
      by_cases hne : ∃ y ∈ ts.cl w, y ∉ ts.X
      · -- the leader: the largest identifier in `C \ X`
        let F : Finset V := Finset.univ.filter (fun y => y ∈ ts.cl w ∧ y ∉ ts.X)
        have hF : F.Nonempty := by
          obtain ⟨y, hy, hyX⟩ := hne; exact ⟨y, by simp [F, hy, hyX]⟩
        set v := F.max' hF with hv_def
        have hvF : v ∈ F := F.max'_mem hF
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hvF
        have hclv : ts.cl v = ts.cl w := ts.cl_eq v w hvF.1
        obtain ⟨o, -, hoC, -, hc4⟩ := hcheck v
        have hcl_o : o.1 v = ts.cl v := (hoC v ⟨v, ts.mem_cl v, by simp⟩).1
        have hvC : ∀ {y}, y ∈ ts.cl v → G.edist v y ≤ t :=
          fun hy => ts.diam v v (ts.mem_cl v) _ hy
        obtain ⟨ℓ', hℓ'X, hℓ'acc⟩ := hc4 ⟨fun h => hvF.2 ((mem_out_iff ts hoC
          ⟨v, ts.mem_cl v, by simp⟩).1 h), fun y hy hyo => by
            rw [hcl_o] at hy
            have hyX : y ∉ ts.X := fun h => hyo ((mem_out_iff ts hoC
              ⟨y, hy, by simp⟩).2 h)
            exact F.le_max' y (by simp [F, hclv ▸ hy, hyX])⟩
        refine ⟨fun u => if u ∈ ts.X then ℓX u else ℓ' u, fun x hx => by simp [hx],
          fun u hu => ?_⟩
        obtain ⟨y, hy, hyC, hyX⟩ := hu
        rw [← hclv] at hyC
        have hvy := hvC hyC
        have hvu : G.edist v u ≤ (t + 1 : ℕ) := by
          rcases hy with rfl | hy
          · exact hvy.trans (by exact_mod_cast (by omega : t ≤ t + 1))
          · exact edist_le_add hvy (edist_le_one_of_eq_or_adj (Or.inr hy.symm))
        have hacc' := hℓ'acc u ⟨y, hy.imp id (fun h =>
          ((loc_adj_iff hvy (by omega : t + 1 ≤ Rt)).2 h.symm).symm),
          hcl_o ▸ hyC, fun h => hyX ((mem_out_iff ts hoC ⟨y, hyC, by simp⟩).1 h)⟩
        rw [ver_loc_mask S1.isLocal I _ _ hvu (by omega) (fun _ _ => rfl)] at hacc'
        rw [S1.isLocal G I _ G I ℓ' u (viewEq_self fun z hz => ?_)]
        · exact hacc'
        · have hz' := eq_or_adj_of_edist_le_one hz
          -- `z` is within distance 2 of `y ∈ C_v`
          have hyz : G.edist y z ≤ 2 := by
            rcases hy with rfl | hy
            · exact hz.trans (by norm_num)
            · have := edist_le_add (edist_le_one_of_eq_or_adj (Or.inr hy.symm)) hz
              exact this.trans (by norm_num)
          have hnear : ∃ w ∈ ts.cl v, G.edist w z ≤ 2 := ⟨y, hyC, hyz⟩
          by_cases hzX : z ∈ ts.X
          · simp only [hzX, ite_true]
            have hzo : z ∈ o.2 := (mem_out_iff ts hoC hnear).2 hzX
            rw [hℓ'X z hzo ⟨y, hcl_o ▸ hyC,
              (loc_edist_le_iff hvy (by omega : t + 2 ≤ Rt) le_rfl).2 hyz⟩]
            exact (decodeX_local ts hoC hRt ℓ hnear).symm
          · simp [hzX]
      · -- no node of `C \ X`: `H_C` is empty
        push Not at hne
        refine ⟨ℓX, fun _ _ => rfl, fun u hu => ?_⟩
        obtain ⟨y, -, hyC, hyX⟩ := hu
        exact absurd (hne y hyC) hyX
  · ---------------- cost ----------------
    intro G hG I hP v
    have h : G ∈ 𝒢 ∧ ∀ v, (S.ver G (S.prov G) v).isSome := ⟨hG, hacc G hG⟩
    have key : ∀ ts : TSPartition G t ε,
        (ppLabel (S1.prov G I) (ts.cl v) ts.X v).length ≤ ⌈ε * (2 * p + 1)⌉₊ := by
      intro ts
      refine length_ppLabel_le ⟨v, ts.mem_cl v⟩ (fun x _ => hp G hG I hP x) ?_
      have hr := ts.ratio v
      have hceil := Nat.le_ceil (ε * (2 * p + 1))
      have hpos : (0 : ℝ) ≤ (ts.cl v).ncard := by positivity
      have : (((ts.cl v ∩ ts.X).ncard * (2 * p + 1) : ℕ) : ℝ) ≤
          (((ts.cl v).ncard * ⌈ε * (2 * p + 1)⌉₊ : ℕ) : ℝ) := by
        push_cast
        calc ((ts.cl v ∩ ts.X).ncard : ℝ) * (2 * p + 1)
            ≤ ε * (ts.cl v).ncard * (2 * p + 1) := by gcongr
          _ = (ts.cl v).ncard * (ε * (2 * p + 1)) := by ring
          _ ≤ (ts.cl v).ncard * ⌈ε * (2 * p + 1)⌉₊ := by gcongr
      exact_mod_cast this
    have h1 := hc G hG v
    have h2 := key (Classical.choose (S.sound G h.1 _ h.2))
    simp only [provT, dite_eq_left h]
    rw [length_encList]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

end Main

end PLSTradeoff
