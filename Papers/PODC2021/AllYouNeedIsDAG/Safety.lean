import Papers.PODC2021.AllYouNeedIsDAG.Ordering
import Cslib.Foundations.Data.Finset.Quorum

/-!
# DAG-Rider: safety (Lemma 1, Claims 4–5, Propositions 1–2)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, Section 6.1.

All statements are about arbitrary *snapshot sequences* (the local DAGs at the `wave_ready`
events) that are closed (Claim 1) and valid (line 25) with respect to one global `Content`
(non-equivocation). No assumption relates the snapshots of different processes or of different
waves of the same process, so the theorems hold for every asynchronous schedule.

* `DCommit v d`: some correct process *directly* commits `v` in wave `d` (the commit rule of line 36
  holds in a closed valid local DAG).
* `lemma1_direct` (Lemma 1, for direct commits): every vertex of round `> round(d, 4)` in any closed
  valid local DAG has a strong path to `v`. The quorum intersection only needs
  `2(2f + 1) > n`, i.e. `n ≤ 4f + 1`.
* `orun_inv`: after any number of waves, the output of a process is the delivery sequence of the
  *full chain* of its last directly committed leader (`fullChain`), which is a function of the
  global DAG only.
* `delivered_prefix` (total order, strong form): the outputs of any two processes (after any
  numbers of waves) are prefix-comparable; `total_order` (Proposition 2) and `integrity`
  (Proposition 1) are the BAB properties of Definition 3.1.
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*} [DecidableEq P]

/-- The (potential) leader vertex of wave `w`. -/
def lv (coin : ℕ → P) (w : ℕ) : Vtx P := (wround w 1, coin w)

/-- The leader `v` of wave `d ≥ 1` is directly committed by some process, i.e. the commit rule
holds in some closed valid local DAG. -/
def DCommit (f : ℕ) (C : Content P B) (coin : ℕ → P) (v : Vtx P) (d : ℕ) : Prop :=
  1 ≤ d ∧ v = lv coin d ∧
    ∃ D, Closed C D ∧ Valid f C D ∧ v ∈ D ∧ 2 * f + 1 ≤ commitCount C D v d

variable {f : ℕ} {C : Content P B} {coin : ℕ → P}

lemma wround_one (w : ℕ) (hw : 1 ≤ w) : wround w 1 = 4 * w - 3 := by
  unfold wround; omega

lemma wround_four (w : ℕ) (hw : 1 ≤ w) : wround w 4 = 4 * w := by
  unfold wround; omega

omit [DecidableEq P] in
/-- In a closed valid DAG, every vertex has a strong path to some vertex of every lower round
`≥ 1`. -/
lemma exists_sPath_down {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D) :
    ∀ n, ∀ u ∈ D, ∀ k, 1 ≤ k → k + n = u.1 → ∃ x ∈ D, x.1 = k ∧ SPath C u x := by
  intro n
  induction n with
  | zero => intro u hu k _ hk; exact ⟨u, hu, by omega, SPath.refl u⟩
  | succ n ih =>
    intro u hu k hk1 hk
    obtain ⟨s, hs⟩ : (C.strong u).Nonempty := by
      rw [← Finset.card_pos]; have := hV u hu; omega
    have e : SEdge C u (u.1 - 1, s) := ⟨by simp; omega, hs, by simp; omega⟩
    have hmem : (u.1 - 1, s) ∈ D := hD u hu _ e.edge
    obtain ⟨x, hx, hx1, hxp⟩ := ih _ hmem k hk1 (by simp; omega)
    exact ⟨x, hx, hx1, Relation.ReflTransGen.head e hxp⟩

/-- **Lemma 1** (for direct commits). If the leader `v` of wave `d` is directly committed, then
every vertex `u` of a round `> round(d, 4)` in any closed valid local DAG (in particular the
leader of any later wave, in the DAG of any process) has a strong path to `v`. -/
theorem lemma1_direct [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) {v : Vtx P} {d : ℕ}
    (hc : DCommit f C coin v d) {D' : Finset (Vtx P)} (hD' : Closed C D') (hV' : Valid f C D')
    {u : Vtx P} (hu : u ∈ D') (hr : wround d 4 < u.1) : SPath C u v := by
  classical
  obtain ⟨hd, -, D, -, -, -, hcnt⟩ := hc
  have h4 := wround_four d hd
  -- descend to round `4d + 1`
  obtain ⟨x, hx, hx1, hux⟩ := exists_sPath_down hD' hV' (u.1 - (4 * d + 1)) u hu (4 * d + 1)
    (by omega) (by omega)
  set F := D.filter (fun u => u.1 = wround d 4 ∧ SPath C u v) with hF
  have hinj : Set.InjOn Prod.snd (F : Set (Vtx P)) := by
    intro a ha b hb hab
    simp only [hF, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    exact Prod.ext (by rw [ha.2.1, hb.2.1]) hab
  have hQ : 2 * f + 1 ≤ (F.image Prod.snd).card := by
    rw [Finset.card_image_of_injOn hinj]; exact hcnt
  obtain ⟨s, hs⟩ := Cslib.Quorum.inter_nonempty_of_card_le_four_mul_add_one hP hQ (hV' x hx)
  rw [Finset.mem_inter, Finset.mem_image] at hs
  obtain ⟨⟨y, hy, rfl⟩, hsx⟩ := hs
  simp only [hF, Finset.mem_filter] at hy
  have e : SEdge C x y := ⟨by omega, hsx, by omega⟩
  exact hux.trans (Relation.ReflTransGen.head e hy.2.2)

/-! ### The greedy chain of leaders (lines 39–43), computed in the global DAG -/

/-- The loop of lines 39–43 evaluated on the global DAG. -/
def gchain (C : Content P B) (coin : ℕ → P) : Vtx P → List ℕ → List (Vtx P)
  | _, [] => []
  | cur, w :: ws =>
    if SPath C cur (lv coin w) then lv coin w :: gchain C coin (lv coin w) ws
    else gchain C coin cur ws

/-- In a closed local DAG, the loop of lines 39–43 does not depend on the DAG. -/
lemma chain_eq_gchain {D : Finset (Vtx P)} (hD : Closed C D) :
    ∀ ws cur, cur ∈ D → chain C coin D cur ws = gchain C coin cur ws := by
  intro ws
  induction ws with
  | nil => intro cur _; rfl
  | cons w ws ih =>
    intro cur hcur
    simp only [chain, gchain, leader]
    by_cases hm : (wround w 1, coin w) ∈ D
    · simp only [hm, ite_true]
      by_cases hp : SPath C cur (lv coin w)
      · simp only [lv] at hp ⊢
        simp only [hp, ite_true, ih _ hm]
      · simp only [lv] at hp ⊢
        simp only [hp, ite_false, ih _ hcur]
    · have hp : ¬ SPath C cur (lv coin w) := fun h => hm (hD.mem_of_sPath hcur h)
      simp only [lv] at hp ⊢
      simp only [hm, hp, ite_false, ih _ hcur]

lemma mem_gchain {ws : List ℕ} {cur x : Vtx P} (hx : x ∈ cur :: gchain C coin cur ws) :
    SPath C cur x ∧ (x = cur ∨ ∃ w ∈ ws, x = lv coin w) := by
  induction ws generalizing cur with
  | nil =>
    simp only [gchain, List.mem_singleton] at hx
    exact ⟨hx ▸ SPath.refl _, Or.inl hx⟩
  | cons w ws ih =>
    simp only [gchain] at hx
    split_ifs at hx with hp
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨SPath.refl _, Or.inl rfl⟩
      · obtain ⟨h1, h2⟩ := ih hx
        refine ⟨hp.trans h1, Or.inr ?_⟩
        rcases h2 with rfl | ⟨w', hw', rfl⟩
        · exact ⟨w, List.mem_cons_self, rfl⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨SPath.refl _, Or.inl rfl⟩
      · obtain ⟨h1, h2⟩ := ih (List.mem_cons_of_mem _ hx)
        refine ⟨h1, ?_⟩
        rcases h2 with h | ⟨w', hw', rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨w', List.mem_cons_of_mem _ hw', rfl⟩

lemma gchain_append (cur : Vtx P) (l₁ l₂ : List ℕ) :
    gchain C coin cur (l₁ ++ l₂) =
      gchain C coin cur l₁ ++ gchain C coin ((gchain C coin cur l₁).getLast?.getD cur) l₂ := by
  induction l₁ generalizing cur with
  | nil => simp [gchain]
  | cons w l₁ ih =>
    simp only [List.cons_append, gchain]
    split_ifs with hp
    · rw [ih, List.getLast?_cons]; simp
    · rw [ih]

omit [DecidableEq P] in
lemma getLast_mem_cons (cur : Vtx P) (l : List (Vtx P)) : l.getLast?.getD cur ∈ cur :: l := by
  cases h : l.getLast? with
  | none => simp
  | some a => simpa using List.mem_cons_of_mem cur (List.mem_of_getLast? h)

/-- The waves `w - 1, …, d + 1`. -/
lemma mem_wavesDown {w d x : ℕ} : x ∈ wavesDown w d ↔ d < x ∧ x < w := by
  simp only [wavesDown, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨w - 1 - x, by omega, by omega⟩

lemma wavesDown_split {w d : ℕ} (hd : 1 ≤ d) (hdw : d < w) :
    wavesDown w 0 = wavesDown w d ++ d :: wavesDown d 0 := by
  unfold wavesDown
  have : w - 1 - 0 = (w - 1 - d) + d := by omega
  rw [this, List.range_add, List.map_append, List.map_map]
  congr 1
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.sub_zero, Function.comp_def]
  congr 1
  · omega
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    omega

/-- The full sequence of leaders committed together with (and before) `v`, the leader of wave `d`,
in increasing wave order. -/
def fullChain (C : Content P B) (coin : ℕ → P) (v : Vtx P) (d : ℕ) : List (Vtx P) :=
  (gchain C coin v (wavesDown d 0)).reverse ++ [v]

/-- Key step of total order: once `v₀` (wave `d`) is directly committed, the chain of every later
leader `v` passes through `v₀`. -/
theorem gchain_through [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) {v₀ v : Vtx P} {d w : ℕ}
    (hc : DCommit f C coin v₀ d) (hdw : d < w) (hv : v = lv coin w) {D : Finset (Vtx P)}
    (hD : Closed C D) (hV : Valid f C D) (hvD : v ∈ D) :
    gchain C coin v (wavesDown w 0) =
      gchain C coin v (wavesDown w d) ++ v₀ :: gchain C coin v₀ (wavesDown d 0) := by
  have hd := hc.1
  rw [wavesDown_split hd hdw, gchain_append]
  congr 1
  obtain ⟨hpc, hc'⟩ := mem_gchain (getLast_mem_cons v (gchain C coin v (wavesDown w d)))
  generalize (gchain C coin v (wavesDown w d)).getLast?.getD v = c at hpc hc' ⊢
  have hcD : c ∈ D := hD.mem_of_sPath hvD hpc
  have hround : wround d 4 < c.1 := by
    rw [wround_four d hd]
    rcases hc' with h | ⟨w', hw', h⟩
    · rw [h, hv]; simp only [lv, wround]; omega
    · rw [h]; rw [mem_wavesDown] at hw'; simp only [lv, wround]; omega
  have hp := lemma1_direct hP hc hD hV hcD hround
  obtain ⟨-, hv0, -⟩ := hc
  subst hv0
  simp only [gchain, hp, ↓reduceIte]

/-! ### Delivery -/

variable {sortV : Finset (Vtx P) → List (Vtx P)}

omit [DecidableEq P] in
lemma deliverAll_append (D : Finset (Vtx P)) (L : List (Vtx P)) (l₁ l₂ : List (Vtx P)) :
    deliverAll C sortV D L (l₁ ++ l₂) = deliverAll C sortV D (deliverAll C sortV D L l₁) l₂ := by
  simp [deliverAll, List.foldl_append]

omit [DecidableEq P] in
lemma prefix_deliverAll (D : Finset (Vtx P)) (L : List (Vtx P)) (l : List (Vtx P)) :
    L <+: deliverAll C sortV D L l := by
  induction l generalizing L with
  | nil => exact List.prefix_refl L
  | cons x l ih =>
    simp only [deliverAll, List.foldl_cons]
    exact (List.prefix_append L _).trans (ih _)

omit [DecidableEq P] in
lemma deliverAll_congr {D D' : Finset (Vtx P)} (L : List (Vtx P)) (l : List (Vtx P))
    (h : ∀ x ∈ l, hist C D x = hist C D' x) :
    deliverAll C sortV D L l = deliverAll C sortV D' L l := by
  induction l generalizing L with
  | nil => rfl
  | cons x l ih =>
    simp only [deliverAll, List.foldl_cons]
    have : deliverOne C sortV D L x = deliverOne C sortV D' L x := by
      simp only [deliverOne, h x List.mem_cons_self]
    rw [this]
    exact ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))

lemma mem_fullChain {v x : Vtx P} {d : ℕ} (hx : x ∈ fullChain C coin v d) : SPath C v x := by
  simp only [fullChain, List.mem_append, List.mem_reverse, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact (mem_gchain (List.mem_cons_of_mem v hx)).1
  · exact SPath.refl _

/-- Delivering a full chain does not depend on the (closed) local DAG. -/
lemma deliverAll_fullChain_congr {D D' : Finset (Vtx P)} (hD : Closed C D) (hD' : Closed C D')
    {v : Vtx P} (hv : v ∈ D) (hv' : v ∈ D') (d : ℕ) (L : List (Vtx P)) :
    deliverAll C sortV D L (fullChain C coin v d) = deliverAll C sortV D' L (fullChain C coin v d) :=
  deliverAll_congr L _ fun _ hx =>
    hist_eq_of_closed hD hD' (hD.mem_of_sPath hv (mem_fullChain hx))
      (hD'.mem_of_sPath hv' (mem_fullChain hx))

/-! ### The invariant of the ordering layer -/

/-- The state of a process is either initial, or determined by its last directly committed
leader `lv coin s.decided`: the output is the delivery of its full chain. -/
def OInv (f : ℕ) (C : Content P B) (coin : ℕ → P) (sortV : Finset (Vtx P) → List (Vtx P))
    (s : OState P) : Prop :=
  (s.decided = 0 ∧ s.delivered = []) ∨
    (DCommit f C coin (lv coin s.decided) s.decided ∧
      ∃ D, Closed C D ∧ Valid f C D ∧ lv coin s.decided ∈ D ∧
        s.delivered = deliverAll C sortV D [] (fullChain C coin (lv coin s.decided) s.decided))

lemma waveReady_inv [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) {D : Finset (Vtx P)}
    (hD : Closed C D) (hV : Valid f C D) {w : ℕ} (hw : 1 ≤ w) {s : OState P}
    (hs : OInv f C coin sortV s) (hsw : s.decided < w) :
    OInv f C coin sortV (waveReady f C coin sortV D w s) ∧
      (waveReady f C coin sortV D w s).decided ≤ w := by
  unfold waveReady
  cases hl : leader coin D w with
  | none => exact ⟨hs, show s.decided ≤ w by omega⟩
  | some v =>
    simp only
    have hvD : v ∈ D ∧ v = lv coin w := by
      unfold leader at hl; split_ifs at hl with h
      · cases hl; exact ⟨h, rfl⟩
    split_ifs with hcnt
    swap
    · exact ⟨hs, by omega⟩
    refine ⟨Or.inr ?_, le_rfl⟩
    simp only
    have hcw : DCommit f C coin (lv coin w) w :=
      ⟨hw, rfl, D, hD, hV, hvD.2 ▸ hvD.1, hvD.2 ▸ hcnt⟩
    refine ⟨hcw, D, hD, hV, hvD.2 ▸ hvD.1, ?_⟩
    rw [chain_eq_gchain hD _ _ hvD.1, List.reverse_cons]
    rw [← hvD.2]
    rcases hs with ⟨h0, h1⟩ | ⟨hc0, D₀, hD₀, -, hv₀, hdel⟩
    · rw [h0, h1]; rfl
    · have hd := hc0.1
      have hv₀D : lv coin s.decided ∈ D :=
        hD.mem_of_sPath hvD.1 (lemma1_direct hP hc0 hD hV hvD.1 (by
          rw [hvD.2, wround_four _ hd]; simp only [lv, wround]; omega))
      rw [hdel, deliverAll_fullChain_congr hD₀ hD hv₀ hv₀D, ← deliverAll_append]
      congr 1
      simp only [fullChain]
      rw [gchain_through hP hc0 hsw hvD.2 hD hV hvD.1]
      simp

/-- The invariant of the ordering layer after `W` waves. -/
theorem orun_inv [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) {D : ℕ → Finset (Vtx P)}
    (hD : ∀ w, Closed C (D w) ∧ Valid f C (D w)) (W : ℕ) :
    OInv f C coin sortV (orun f C coin sortV D W) ∧ (orun f C coin sortV D W).decided ≤ W := by
  induction W with
  | zero => exact ⟨Or.inl ⟨rfl, rfl⟩, le_rfl⟩
  | succ W ih =>
    exact waveReady_inv hP (hD (W + 1)).1 (hD (W + 1)).2 (by omega) ih.1 (by omega)

/-- Two states satisfying the invariant have prefix-comparable outputs. -/
lemma prefix_of_inv [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) {s₁ s₂ : OState P}
    (h₁ : OInv f C coin sortV s₁) (h₂ : OInv f C coin sortV s₂) (hle : s₁.decided ≤ s₂.decided) :
    s₁.delivered <+: s₂.delivered := by
  rcases h₁ with ⟨-, h⟩ | ⟨hc₁, D₁, hD₁, -, hv₁, hdel₁⟩
  · rw [h]; exact List.nil_prefix
  rcases h₂ with ⟨h, -⟩ | ⟨hc₂, D₂, hD₂, hV₂, hv₂, hdel₂⟩
  · have := hc₁.1; omega
  rw [hdel₁, hdel₂]
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · rw [heq] at hv₁ ⊢
    rw [deliverAll_fullChain_congr hD₁ hD₂ hv₁ hv₂]
  · have hd₁ := hc₁.1
    have hv₁D₂ : lv coin s₁.decided ∈ D₂ :=
      hD₂.mem_of_sPath hv₂ (lemma1_direct hP hc₁ hD₂ hV₂ hv₂ (by
        rw [wround_four _ hd₁]; simp only [lv, wround]; omega))
    rw [deliverAll_fullChain_congr hD₁ hD₂ hv₁ hv₁D₂]
    have : fullChain C coin (lv coin s₂.decided) s₂.decided =
        fullChain C coin (lv coin s₁.decided) s₁.decided ++
          ((gchain C coin (lv coin s₂.decided) (wavesDown s₂.decided s₁.decided)).reverse ++
            [lv coin s₂.decided]) := by
      simp only [fullChain]
      rw [gchain_through hP hc₁ hlt rfl hD₂ hV₂ hv₂]
      simp
    rw [this, deliverAll_append]
    exact prefix_deliverAll _ _ _

/-- **Total order, strong form.** For any two processes (closed valid snapshot sequences w.r.t. the
same global contents and coin) and any numbers of completed waves, the two output sequences are
prefix-comparable. Only `n ≤ 4f + 1` is used (the paper has `n = 3f + 1`). -/
theorem delivered_prefix [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1)
    {D₁ D₂ : ℕ → Finset (Vtx P)} (hD₁ : ∀ w, Closed C (D₁ w) ∧ Valid f C (D₁ w))
    (hD₂ : ∀ w, Closed C (D₂ w) ∧ Valid f C (D₂ w)) (W₁ W₂ : ℕ) :
    (orun f C coin sortV D₁ W₁).delivered <+: (orun f C coin sortV D₂ W₂).delivered ∨
      (orun f C coin sortV D₂ W₂).delivered <+: (orun f C coin sortV D₁ W₁).delivered := by
  have h₁ := (orun_inv (coin := coin) (sortV := sortV) hP hD₁ W₁).1
  have h₂ := (orun_inv (coin := coin) (sortV := sortV) hP hD₂ W₂).1
  rcases le_total (orun f C coin sortV D₁ W₁).decided (orun f C coin sortV D₂ W₂).decided with
    h | h
  · exact Or.inl (prefix_of_inv hP h₁ h₂ h)
  · exact Or.inr (prefix_of_inv hP h₂ h₁ h)

/-- Outputs only grow. -/
lemma orun_prefix_succ (D : ℕ → Finset (Vtx P)) (W : ℕ) :
    (orun f C coin sortV D W).delivered <+: (orun f C coin sortV D (W + 1)).delivered := by
  simp only [orun, waveReady]
  split
  · exact List.prefix_refl _
  · split_ifs
    · exact prefix_deliverAll _ _ _
    · exact List.prefix_refl _

lemma orun_mono (D : ℕ → Finset (Vtx P)) {W W' : ℕ} (h : W ≤ W') :
    (orun f C coin sortV D W).delivered <+: (orun f C coin sortV D W').delivered := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (orun_prefix_succ D _)

/-! ### Integrity -/

omit [DecidableEq P] in
lemma nodup_deliverAll (hsort : SortSpec sortV) (D : Finset (Vtx P)) {L : List (Vtx P)}
    (hL : L.Nodup) (l : List (Vtx P)) : (deliverAll C sortV D L l).Nodup := by
  classical
  induction l generalizing L with
  | nil => exact hL
  | cons x l ih =>
    simp only [deliverAll, List.foldl_cons]
    apply ih
    simp only [deliverOne]
    refine List.nodup_append.2 ⟨hL, (hsort _).1, ?_⟩
    intro a ha b hb hab
    subst hab
    rw [(hsort _).2, Finset.mem_filter] at hb
    exact hb.2 ha

/-- **Proposition 1 (Integrity).** A process outputs every vertex `(r, k)` (i.e. a block with
round `r` and source `k`) at most once. -/
theorem integrity (hsort : SortSpec sortV) (D : ℕ → Finset (Vtx P)) (W : ℕ) :
    (orun f C coin sortV D W).delivered.Nodup := by
  induction W with
  | zero => exact List.nodup_nil
  | succ W ih =>
    simp only [orun, waveReady]
    split
    · exact ih
    · split_ifs
      · exact nodup_deliverAll hsort _ ih _
      · exact ih

/-- **Proposition 2 (Total order, Definition 3.1).** If a process outputs `m` before `m'`, then
any process that outputs `m'` has output `m` before. -/
theorem total_order [Fintype P] (hP : Fintype.card P ≤ 4 * f + 1) (hsort : SortSpec sortV)
    {D₁ D₂ : ℕ → Finset (Vtx P)} (hD₁ : ∀ w, Closed C (D₁ w) ∧ Valid f C (D₁ w))
    (hD₂ : ∀ w, Closed C (D₂ w) ∧ Valid f C (D₂ w)) (W₁ W₂ : ℕ) {m m' : Vtx P}
    (hbefore : List.Sublist [m, m'] (orun f C coin sortV D₁ W₁).delivered)
    (hm' : m' ∈ (orun f C coin sortV D₂ W₂).delivered) :
    List.Sublist [m, m'] (orun f C coin sortV D₂ W₂).delivered := by
  rcases delivered_prefix (coin := coin) (sortV := sortV) hP hD₁ hD₂ W₁ W₂ with h | h
  · exact hbefore.trans h.sublist
  · obtain ⟨X, hX⟩ := h
    have hnd := integrity (f := f) (C := C) (coin := coin) hsort D₁ W₁
    rw [← hX] at hbefore hnd
    rw [List.nodup_append] at hnd
    rw [List.sublist_append_iff] at hbefore
    obtain ⟨l₁, l₂, heq, h₁, h₂⟩ := hbefore
    match l₁, l₂, heq with
    | [], _, rfl => exact absurd rfl (hnd.2.2 _ hm' _ (h₂.subset (by simp)))
    | [_], _, heq =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact absurd rfl (hnd.2.2 _ hm' _ (h₂.subset (by simp)))
    | [_, _], _, heq =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact h₁
    | _ :: _ :: _ :: _, _, heq => simp at heq

end DagRider
