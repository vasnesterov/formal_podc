import Papers.PODC2021.AllYouNeedIsDAG.Safety

/-!
# Chain quality (Section 3): true for round-major delivery orders

Section 3 of the paper: "our BAB protocol satisfies chain quality. That is, for every prefix of
ordered messages of size `(2f + 1) r`, at least `(f + 1) r` were broadcast by correct processes."
No proof is given, and `order_vertices` delivers each causal history "in some deterministic order".

* `chain_quality`: the claim holds whenever the deterministic order is **round-major** (lists
  vertices by non-decreasing round; the order inside a round is arbitrary, so the adversary may
  even have all Byzantine vertices of a round delivered first). Key fact (`fullBelow_orun`): in
  every prefix of the output, every round below the highest round of the prefix already has
  `2f + 1` vertices; there are at most `f` Byzantine vertices per round (non-equivocation).
* For other deterministic orders the claim is false (e.g. ordering by source first: see
  `ChainQualityCounterexample.lean`).
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*} [DecidableEq P]
variable {f : ℕ} {C : Content P B} {coin : ℕ → P} {sortV : Finset (Vtx P) → List (Vtx P)}

/-- A round-major order: each listed set is sorted by non-decreasing round. -/
def RoundMajor (sortV : Finset (Vtx P) → List (Vtx P)) : Prop :=
  ∀ s, (sortV s).Pairwise (fun a b => a.1 ≤ b.1)

/-- In every prefix of `L`, every round `ρ ≥ 1` below a round present in the prefix has at least
`2f + 1` vertices in the prefix. -/
def FullBelow (f : ℕ) (L : List (Vtx P)) : Prop :=
  ∀ i, ∀ x ∈ L.take i, ∀ ρ, 1 ≤ ρ → ρ < x.1 → 2 * f + 1 ≤ ((L.take i).toFinset.filter (·.1 = ρ)).card

omit [DecidableEq P] in
/-- In a causal history, every round below a vertex of the history has `2f + 1` vertices. -/
lemma hist_layer_full [DecidableEq P] {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D)
    {v x : Vtx P} (hv : v ∈ D) (hx : x ∈ hist C D v) {ρ : ℕ} (hρ : 1 ≤ ρ) (hρx : ρ < x.1) :
    2 * f + 1 ≤ ((hist C D v).filter (·.1 = ρ)).card := by
  rw [mem_hist] at hx
  obtain ⟨y, hy, hy1, hxy⟩ := exists_sPath_down hD hV (x.1 - (ρ + 1)) x hx.1 (ρ + 1) (by omega)
    (by omega)
  have hvy : Path C v y := hx.2.trans hxy.path
  have hyD : y ∈ D := hD.mem_of_path hv hvy
  calc 2 * f + 1 ≤ (C.strong y).card := hV y hyD
    _ = ((C.strong y).image (fun s => (ρ, s))).card :=
        (Finset.card_image_of_injective _ (fun a b h => by simpa using h)).symm
    _ ≤ _ := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_image] at hz
        obtain ⟨s, hs, rfl⟩ := hz
        have e : SEdge C y (ρ, s) := ⟨by simp; omega, hs, hρ⟩
        rw [Finset.mem_filter, mem_hist]
        exact ⟨⟨hD _ hyD _ e.edge, hvy.trans (Relation.ReflTransGen.single e.edge)⟩, rfl⟩

omit [DecidableEq P] in
lemma deliverOne_spec (hsort : SortSpec sortV) (hmaj : RoundMajor sortV) (D : Finset (Vtx P))
    (L : List (Vtx P)) (v : Vtx P) :
    ∃ S, deliverOne C sortV D L v = L ++ S ∧ (∀ x, x ∈ S ↔ x ∈ hist C D v ∧ x ∉ L) ∧
      S.Pairwise (fun a b => a.1 ≤ b.1) := by
  classical
  refine ⟨_, rfl, fun x => ?_, hmaj _⟩
  rw [(hsort _).2, Finset.mem_filter]

lemma fullBelow_deliverOne (hsort : SortSpec sortV) (hmaj : RoundMajor sortV)
    {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D) {v : Vtx P} (hv : v ∈ D)
    {L : List (Vtx P)} (hL : FullBelow f L) : FullBelow f (deliverOne C sortV D L v) := by
  obtain ⟨S, hdel, hSmem, hSpw⟩ := deliverOne_spec hsort hmaj D L v
  rw [hdel]
  intro i x hx ρ hρ hρx
  rcases le_or_gt i L.length with hi | hi
  · rw [List.take_append_of_le_length hi] at hx ⊢
    exact hL i x hx ρ hρ hρx
  · rw [List.take_append, List.take_of_length_le hi.le] at hx ⊢
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have h := hL L.length x (by rwa [List.take_length]) ρ hρ hρx
      rw [List.take_length] at h
      refine le_trans h (Finset.card_le_card ?_)
      intro z hz
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append] at hz ⊢
      exact ⟨Or.inl hz.1, hz.2⟩
    · have hxS : x ∈ S := List.mem_of_mem_take hx
      have hxh : x ∈ hist C D v := ((hSmem x).1 hxS).1
      refine le_trans (hist_layer_full hD hV hv hxh hρ hρx) (Finset.card_le_card ?_)
      intro y hy
      rw [Finset.mem_filter] at hy
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append]
      refine ⟨?_, hy.2⟩
      by_cases hyL : y ∈ L
      · exact Or.inl hyL
      · right
        have hyS : y ∈ S := (hSmem y).2 ⟨hy.1, hyL⟩
        rw [← List.take_append_drop (i - L.length) S, List.mem_append] at hyS
        rcases hyS with h | h
        · exact h
        · exfalso
          rw [← List.take_append_drop (i - L.length) S, List.pairwise_append] at hSpw
          have := hSpw.2.2 x hx y h
          omega

lemma fullBelow_deliverAll (hsort : SortSpec sortV) (hmaj : RoundMajor sortV)
    {D : Finset (Vtx P)} (hD : Closed C D) (hV : Valid f C D) :
    ∀ (ls L : List (Vtx P)), (∀ v ∈ ls, v ∈ D) → FullBelow f L →
      FullBelow f (deliverAll C sortV D L ls) := by
  intro ls
  induction ls with
  | nil => intro L _ h; exact h
  | cons v ls ih =>
    intro L hls hL
    simp only [deliverAll, List.foldl_cons]
    exact ih _ (fun w hw => hls w (List.mem_cons_of_mem _ hw))
      (fullBelow_deliverOne hsort hmaj hD hV (hls v List.mem_cons_self) hL)

omit [DecidableEq P] in
lemma mem_deliverOne {D : Finset (Vtx P)} {L : List (Vtx P)} {v x : Vtx P} (hsort : SortSpec sortV)
    (hx : x ∈ deliverOne C sortV D L v) : x ∈ L ∨ x ∈ D := by
  classical
  unfold deliverOne at hx
  rw [List.mem_append, (hsort _).2, Finset.mem_filter, mem_hist] at hx
  tauto

omit [DecidableEq P] in
lemma mem_deliverAll {D : Finset (Vtx P)} (hsort : SortSpec sortV) :
    ∀ (ls L : List (Vtx P)) x, x ∈ deliverAll C sortV D L ls → x ∈ L ∨ x ∈ D := by
  intro ls
  induction ls with
  | nil => intro L x hx; exact Or.inl hx
  | cons v ls ih =>
    intro L x hx
    simp only [deliverAll, List.foldl_cons] at hx
    rcases ih _ x hx with h | h
    · exact mem_deliverOne hsort h
    · exact Or.inr h

/-- Every output of the ordering layer has full lower rounds in all its prefixes. -/
lemma fullBelow_orun (hsort : SortSpec sortV) (hmaj : RoundMajor sortV) {D : ℕ → Finset (Vtx P)}
    (hD : ∀ w, Closed C (D w) ∧ Valid f C (D w)) (W : ℕ) :
    FullBelow f (orun f C coin sortV D W).delivered ∧
      ∀ x ∈ (orun f C coin sortV D W).delivered, ∃ w, x ∈ D w := by
  induction W with
  | zero =>
    refine ⟨?_, by simp [orun]⟩
    intro i x hx; simp [orun] at hx
  | succ W ih =>
    simp only [orun, waveReady]
    split
    · exact ih
    · rename_i v hl
      have hvD : v ∈ D (W + 1) := by
        unfold leader at hl; split_ifs at hl with h; cases hl; exact h
      split_ifs
      · have hmem : ∀ u ∈ (v :: chain C coin (D (W + 1)) v
            (wavesDown (W + 1) (orun f C coin sortV D W).decided)).reverse, u ∈ D (W + 1) := by
          intro u hu
          rw [List.mem_reverse, chain_eq_gchain (hD _).1 _ _ hvD] at hu
          exact (hD _).1.mem_of_sPath hvD (mem_gchain hu).1
        refine ⟨fullBelow_deliverAll hsort hmaj (hD _).1 (hD _).2 _ _ hmem ih.1, ?_⟩
        intro x hx
        rcases mem_deliverAll hsort _ _ x hx with h | h
        · exact ih.2 x h
        · exact ⟨_, h⟩
      · exact ih

/-- **Chain quality** (Section 3), for round-major delivery orders: if at most `f` processes are
Byzantine, then every prefix of the output of size `(2f + 1) r` contains at most `f r` vertices
(blocks) of Byzantine processes, i.e. at least `(f + 1) r` blocks of correct processes. -/
theorem chain_quality (hsort : SortSpec sortV) (hmaj : RoundMajor sortV) {D : ℕ → Finset (Vtx P)}
    (hD : ∀ w, Closed C (D w) ∧ Valid f C (D w)) (hround : ∀ w, ∀ x ∈ D w, 1 ≤ x.1)
    (byz : Finset P) (hbyz : byz.card ≤ f) (W r : ℕ)
    (hlen : (2 * f + 1) * r ≤ (orun f C coin sortV D W).delivered.length) :
    (((orun f C coin sortV D W).delivered.take ((2 * f + 1) * r)).filter
        (fun x => decide (x.2 ∈ byz))).length ≤ f * r := by
  classical
  set L := (orun f C coin sortV D W).delivered with hLdef
  obtain ⟨hfull, hmemD⟩ := fullBelow_orun (coin := coin) hsort hmaj hD W
  have hnd : L.Nodup := integrity hsort D W
  set m := (2 * f + 1) * r with hm
  set T := (L.take m).toFinset with hT
  have hndT : (L.take m).Nodup := (List.take_sublist _ _).nodup hnd
  have hcardT : T.card = m := by
    rw [hT, List.toFinset_card_of_nodup hndT, List.length_take]; omega
  have hr1 : ∀ x ∈ T, 1 ≤ x.1 := by
    intro x hx
    rw [hT, List.mem_toFinset] at hx
    obtain ⟨w, hw⟩ := hmemD x (List.mem_of_mem_take hx)
    exact hround w x hw
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp only [Nat.mul_zero]; exact Nat.zero_le _
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hcardT]; positivity
  set M := T.sup Prod.fst with hM
  obtain ⟨xm, hxm, hxmM⟩ := Finset.exists_mem_eq_sup T hTne Prod.fst
  have hle : ∀ x ∈ T, x.1 ≤ M := fun x hx => Finset.le_sup (f := Prod.fst) hx
  have hM1 : 1 ≤ M := by rw [hM, hxmM]; exact hr1 xm hxm
  -- `T` is the disjoint union of its rounds `1..M`
  have hsum : T.card = ∑ ρ ∈ Finset.Icc 1 M, (T.filter (·.1 = ρ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => by
      simp only [Finset.coe_Icc, Set.mem_Icc]; exact ⟨hr1 x hx, hle x hx⟩)
  have hlow : ∀ ρ ∈ Finset.Icc 1 (M - 1), 2 * f + 1 ≤ (T.filter (·.1 = ρ)).card := by
    intro ρ hρ
    rw [Finset.mem_Icc] at hρ
    exact hfull m xm (by rw [hT, List.mem_toFinset] at hxm; exact hxm) ρ hρ.1 (by rw [← hxmM]; omega)
  have htop : 1 ≤ (T.filter (·.1 = M)).card :=
    Finset.card_pos.2 ⟨xm, Finset.mem_filter.2 ⟨hxm, hxmM.symm⟩⟩
  have hsplit : Finset.Icc 1 M = insert M (Finset.Icc 1 (M - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)] at hsum
  have hlowsum : (2 * f + 1) * (M - 1) ≤ ∑ ρ ∈ Finset.Icc 1 (M - 1), (T.filter (·.1 = ρ)).card := by
    have := Finset.card_nsmul_le_sum _ _ _ hlow
    simpa [Nat.card_Icc, mul_comm] using this
  have hMr : M ≤ r := by
    by_contra h
    have : (2 * f + 1) * r + 1 ≤ (2 * f + 1) * (M - 1) + 1 := by
      have : r ≤ M - 1 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1
    omega
  -- Byzantine vertices lie in `[1, M] × byz`
  calc (((L.take m).filter (fun x => decide (x.2 ∈ byz)))).length
      = (T.filter (fun x => x.2 ∈ byz)).card := by
        rw [hT, ← List.toFinset_card_of_nodup (hndT.filter _), List.toFinset_filter]
        simp
    _ ≤ (Finset.Icc 1 M ×ˢ byz).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hr1 x hx.1, hle x hx.1⟩, hx.2⟩
    _ = M * byz.card := by rw [Finset.card_product, Nat.card_Icc]; congr 1
    _ ≤ r * f := Nat.mul_le_mul hMr hbyz
    _ = f * r := mul_comm _ _

end DagRider
