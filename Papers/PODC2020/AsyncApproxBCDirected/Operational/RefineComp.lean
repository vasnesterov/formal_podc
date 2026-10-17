import Papers.PODC2020.AsyncApproxBCDirected.Operational.RefineVal

/-!
# Refinement, `COMPLETE` layer: FIFO-Flood satisfies the hypotheses `CR_*` of `RoundExec`

* `sent_iff`, `mcTime_hst`, `mcMsg_eq`: the abstract Maximal-Consistency notions (`Sent`,
  `mcTime`, `mcMsg`) evaluated on `Mr` coincide with the operational ones (`mcK`, `mcContent`).
* `genuine`: a `COMPLETE` message received along a path of correct nodes is genuine.
* `CR_honest'`, `CR_fifo'`, `CR_live'`, `idx_inj'`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

namespace BWOp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (f N : ℕ)
  (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V (BMsg V))

/-- The own-value function of node `v` in round `r`. -/
noncomputable abbrev ownF (v : V) (r : ℕ) : Hist V → Option ℝ := xv G f N v (inp v) r

/-- The abstract `CR` (FIFO-received `COMPLETE` messages). -/
noncomputable def CRr (r : ℕ) (v : V) (t : ℕ) : Finset (V × List V × Finset (Msg V) × Finset V) :=
  CRop G f v r (ownF G f N inp v r) (hst G f N B inp ev t v)

theorem mcAt_iff {r : ℕ} {c : V} {F' : Finset V} {t : ℕ} :
    MCAt G (Mr G f N B inp ev r) c F' t ↔
      MCop G c r (ownF G f N inp c r (hst G f N B inp ev t c)) (hst G f N B inp ev t c) F' :=
  Iff.rfl

theorem take_hst_exists {c : V} {t k : ℕ} :
    ∃ t' ≤ t, hst G f N B inp ev t' c = (hst G f N B inp ev t c).take k :=
  (spec G f N).exists_time_hist G B inp ev c t (List.take_prefix _ _)

theorem threadL_iff {c : V} {F' : Finset V} : F' ∈ threadL f c ↔ c ∉ F' ∧ F'.card ≤ f := by
  classical simp [threadL]

/-- Abstract `Sent` = operational Maximal-Consistency reached at some time. -/
theorem sent_iff {r : ℕ} {c : V} {F' : Finset V} :
    Sent G f (Mr G f N B inp ev r) c F' ↔
      F' ∈ threadL f c ∧ ∃ t, (mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F').isSome := by
  rw [threadL_iff]
  constructor
  · rintro ⟨h1, h2, t, ht⟩
    refine ⟨⟨h1, h2⟩, t, ?_⟩
    rcases hk : mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' with _ | k
    · exfalso
      have := (firstIdx_eq_none.mp hk) (hst G f N B inp ev t c).length le_rfl
      rw [List.take_length] at this
      exact this ht
    · rfl
  · rintro ⟨⟨h1, h2⟩, t, ht⟩
    refine ⟨h1, h2, ?_⟩
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp ht
    obtain ⟨-, hP, -⟩ := firstIdx_eq_some.mp hk
    obtain ⟨t', -, ht'⟩ := take_hst_exists G f N B inp ev (c := c) (t := t) (k := k)
    exact ⟨t', by rw [mcAt_iff, ht']; exact hP⟩

/-- The first time of Maximal-Consistency is the first prefix. -/
theorem mcTime_hst {r : ℕ} {c : V} {F' : Finset V} {t k : ℕ}
    (hk : mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' = some k) :
    mcTime G (Mr G f N B inp ev r) c F' ≤ t ∧
      hst G f N B inp ev (mcTime G (Mr G f N B inp ev r) c F') c =
        (hst G f N B inp ev t c).take k := by
  classical
  obtain ⟨hkl, hP, hmin⟩ := firstIdx_eq_some.mp hk
  obtain ⟨t', ht't, ht'⟩ := take_hst_exists G f N B inp ev (c := c) (t := t) (k := k)
  have hex : ∃ s, MCAt G (Mr G f N B inp ev r) c F' s := ⟨t', by rw [mcAt_iff, ht']; exact hP⟩
  have hmt : mcTime G (Mr G f N B inp ev r) c F' = Nat.find hex := by simp [mcTime, hex]
  rw [hmt]
  have hle : Nat.find hex ≤ t' := Nat.find_min' hex (by rw [mcAt_iff, ht']; exact hP)
  refine ⟨hle.trans ht't, ?_⟩
  have hpre : hst G f N B inp ev (Nat.find hex) c <+: hst G f N B inp ev t c :=
    hst_prefix G f N B inp ev (hle.trans ht't) c
  have hpre' : hst G f N B inp ev (Nat.find hex) c <+: (hst G f N B inp ev t c).take k := by
    rw [← ht']; exact hst_prefix G f N B inp ev hle c
  have hlen : (hst G f N B inp ev (Nat.find hex) c).length = k := by
    apply le_antisymm
    · have := hpre'.length_le; simp at this; omega
    · by_contra hlt
      push Not at hlt
      apply hmin _ hlt
      have h1 := Nat.find_spec hex
      rw [mcAt_iff] at h1
      rwa [← List.prefix_iff_eq_take.mp hpre]
  rw [List.prefix_iff_eq_take.mp hpre, hlen]

theorem mcMsg_eq {r : ℕ} {c : V} {F' : Finset V} {t : ℕ}
    (hs : (mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F').isSome) :
    mcMsg G (Mr G f N B inp ev r) c F' =
      mcContent G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨-, h2⟩ := mcTime_hst G f N B inp ev hk
  simp only [mcMsg, mcContent, hk, Mr]
  rw [h2]

/-- The FIFO counter (ghost `idx`). -/
noncomputable def idxR (r : ℕ) (c : V) (F' : Finset V) : ℕ := by
  classical
  exact if h : ∃ t, F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) then
    counter G f c r (ownF G f N inp c r) (hst G f N B inp ev (Nat.find h) c) F' else 0

theorem idxR_eq {r : ℕ} {c : V} {F' : Finset V} {t : ℕ}
    (h : F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c)) :
    idxR G f N B inp ev r c F' = counter G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' := by
  classical
  have hex : ∃ t, F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) := ⟨t, h⟩
  simp only [idxR, hex, dite_true]
  rcases le_total t (Nat.find hex) with h1 | h1
  · exact counter_prefix G f c r _ (hst_prefix G f N B inp ev h1 c) h
  · exact (counter_prefix G f c r _ (hst_prefix G f N B inp ev h1 c) (Nat.find_spec hex)).symm

theorem compOf_eq_some {v : V} {r : ℕ} {e : V × BMsg V}
    {o : V × List V × Finset (Msg V) × Finset V × ℕ} (h : compOf v r e = some o) :
    ∃ p, e = (e.1, .comp r o.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2 p) ∧ p.getLast? = some e.1 ∧
      o.2.1 = p ++ [v] := by
  rcases e with ⟨u, _ | ⟨r', c, Mc, F', k, p⟩⟩
  · simp [compOf] at h
  · simp only [compOf] at h
    split_ifs at h with hc
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨p, by rw [hc.1], hc.2, rfl⟩

/-- **Genuineness**: a `COMPLETE` message received along a path of correct nodes was sent by its
initiator, with its actual content and counter. -/
theorem genuine (r : ℕ) : ∀ n, ∀ P : List V, P.length = n → ∀ v ∉ B, ∀ t e c Mc F' k,
    e ∈ hst G f N B inp ev t v → compOf v r e = some (c, P, Mc, F', k) → Avoids P B →
    P.head? = some c ∧ F' ∈ threadL f c ∧
      (mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F').isSome ∧
      Mc = mcContent G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' ∧
      k = counter G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) F' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hPn v hv t e c Mc F' k he hce hPB
  obtain ⟨p, he', hp, hP⟩ := compOf_eq_some hce
  simp only at he' hP
  have hu : e.1 ∉ B := hPB e.1 (by rw [hP]; exact List.mem_append_left _ (List.mem_of_getLast? hp))
  have hsent := (spec G f N).mem_sent_of_mem_hist G B inp ev hu (t := t) (v := v)
    (m := .comp r c Mc F' k p) (by rw [he'] at he; exact he)
  obtain ⟨k', hk', hk''⟩ := mem_allSends.mp hsent
  obtain ⟨-, -, hcase⟩ := comp_sent G f N hk''
  rcases hcase with ⟨h₀, u', p₀, hsplit, hp₀, rfl, -⟩ | ⟨rfl, rfl, hF, hmc, rfl, rfl⟩
  · -- relayed: induction along the path
    have hsplit' : (hst G f N B inp ev t e.1).take k' = h₀ ++ [(u', BMsg.comp r c Mc F' k p₀)] :=
      hsplit
    have hin : (u', BMsg.comp r c Mc F' k p₀) ∈ hst G f N B inp ev t e.1 :=
      List.mem_of_mem_take (i := k') (by rw [hsplit']; simp)
    have hlt : (p₀ ++ [e.1]).length < n := by rw [← hPn, hP]; simp
    have hPB' : Avoids (p₀ ++ [e.1]) B := fun y hy => hPB y (by rw [hP]; exact List.mem_append_left _ hy)
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih _ hlt (p₀ ++ [e.1]) rfl e.1 hu t _ c Mc F' k hin
      (by simp [compOf, hp₀]) hPB'
    refine ⟨?_, h2, h3, h4, h5⟩
    rw [hP]; simpa using h1
  · -- originated by `e.1 = c`
    have hpre : (hst G f N B inp ev t e.1).take k' <+: hst G f N B inp ev t e.1 :=
      List.take_prefix _ _
    have hs : (mcK G e.1 r (ownF G f N inp e.1 r) ((hst G f N B inp ev t e.1).take k') F').isSome := by
      simp only [ownF] at hmc ⊢; rw [hmc]; rfl
    refine ⟨by rw [hP]; rfl, hF, ?_, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
      rw [mcK_prefix G e.1 r _ hpre hj]; rfl
    · exact (mcContent_prefix G e.1 r _ hpre hs).symm
    · exact (counter_prefix G f e.1 r _ hpre (mem_compSeq G f |>.mpr ⟨hF, hs⟩)).symm

theorem mem_CRop {v : V} {r : ℕ} {own : Hist V → Option ℝ} {h : Hist V}
    {o : V × List V × Finset (Msg V) × Finset V} :
    o ∈ CRop G f v r own h ↔
      (∃ e ∈ h, ∃ k, compOf v r e = some (o.1, o.2.1, o.2.2.1, o.2.2.2, k) ∧
        ∀ j < k, ∃ e' ∈ h, ∃ Mc'' F'', compOf v r e' = some (o.1, o.2.1, Mc'', F'', j)) ∨
      (o.1 = v ∧ o.2.1 = [v] ∧ o.2.2.2 ∈ threadL f v ∧ (mcK G v r own h o.2.2.2).isSome ∧
        o.2.2.1 = mcContent G v r own h o.2.2.2) := by
  classical
  rcases o with ⟨c, P, Mc, F'⟩
  simp only [CRop, fifoCR, ownCR, mem_union, mem_image, List.mem_toFinset, List.mem_filter,
    List.mem_filterMap, decide_eq_true_eq, Prod.mk.injEq]
  apply or_congr
  · constructor
    · rintro ⟨⟨c', P', Mc', F'', k⟩, ⟨⟨e, he, hce⟩, hall⟩, rfl, rfl, rfl, rfl⟩
      refine ⟨e, he, k, hce, fun j hj => ?_⟩
      obtain ⟨⟨c₁, P₁, M₁, F₁, k₁⟩, ⟨e', he', hce'⟩, h1, h2, h3⟩ := hall j hj
      simp only at h1 h2 h3
      subst h1 h2 h3
      exact ⟨e', he', M₁, F₁, hce'⟩
    · rintro ⟨e, he, k, hce, hall⟩
      refine ⟨⟨c, P, Mc, F', k⟩, ⟨⟨e, he, hce⟩, fun j hj => ?_⟩, rfl, rfl, rfl, rfl⟩
      obtain ⟨e', he', M₁, F₁, hce'⟩ := hall j hj
      exact ⟨⟨c, P, M₁, F₁, j⟩, ⟨e', he', hce'⟩, rfl, rfl, rfl⟩
  · constructor
    · rintro ⟨F₁, ⟨h1, h2⟩, rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, h1, h2, rfl⟩
    · rintro ⟨rfl, rfl, h1, h2, rfl⟩; exact ⟨F', ⟨h1, h2⟩, rfl, rfl, rfl, rfl⟩

/-- `CR_honest` of `RoundExec`. -/
theorem CR_honest' (r : ℕ) {v : V} (hv : v ∉ B) (t : ℕ) (c : V) (P : List V)
    (Mc : Finset (Msg V)) (F' : Finset V) (hm : (c, P, Mc, F') ∈ CRr G f N B inp ev r v t)
    (hP : Avoids P B) :
    P.head? = some c ∧ Sent G f (Mr G f N B inp ev r) c F' ∧
      Mc = mcMsg G (Mr G f N B inp ev r) c F' ∧ mcTime G (Mr G f N B inp ev r) c F' ≤ t := by
  rcases (mem_CRop G f).mp hm with ⟨e, he, k, hce, -⟩ | ⟨h1, h2, hF, hs, h5⟩
  · obtain ⟨h1, h2, h3, h4, -⟩ := genuine G f N B inp ev r _ P rfl v hv t e c Mc F' k he hce hP
    obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp h3
    exact ⟨h1, (sent_iff G f N B inp ev).mpr ⟨h2, t, h3⟩, by rw [h4, mcMsg_eq G f N B inp ev h3],
      (mcTime_hst G f N B inp ev hk₀).1⟩
  · simp only at h1 h2 hF hs h5
    subst h1 h2 h5
    obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨rfl, (sent_iff G f N B inp ev).mpr ⟨hF, t, hs⟩, (mcMsg_eq G f N B inp ev hs).symm,
      (mcTime_hst G f N B inp ev hk₀).1⟩

/-! ## FIFO counters -/

theorem compSeq_nodup (v : V) (r : ℕ) (own : Hist V → Option ℝ) (h : Hist V) :
    (compSeq G f v r own h).Nodup := by
  classical
  unfold compSeq
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => (List.Nodup.filter _ (by simp [threadL, Finset.nodup_toList])), ?_⟩
  refine List.Pairwise.imp_of_mem (R := fun a b => a ≠ b) ?_ (List.nodup_range)
  intro a b _ _ hab
  rw [Function.onFun, List.disjoint_left]
  intro F' ha hb
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  exact hab (Option.some.inj (ha.2.symm.trans hb.2))

theorem counter_inj {v : V} {r : ℕ} {own : Hist V → Option ℝ} {h : Hist V} {F₁ F₂ : Finset V}
    (h₁ : F₁ ∈ compSeq G f v r own h) (h₂ : F₂ ∈ compSeq G f v r own h)
    (he : counter G f v r own h F₁ = counter G f v r own h F₂) : F₁ = F₂ := by
  classical
  simp only [counter] at he
  have l1 := List.idxOf_lt_length_iff.mpr h₁
  have l2 := List.idxOf_lt_length_iff.mpr h₂
  rw [← List.getElem_idxOf l1, ← List.getElem_idxOf l2]
  simp only [he]

theorem counter_getElem {v : V} {r : ℕ} {own : Hist V → Option ℝ} {h : Hist V} {j : ℕ}
    (hj : j < (compSeq G f v r own h).length) :
    counter G f v r own h (compSeq G f v r own h)[j] = j := by
  classical
  simp only [counter]
  exact (compSeq_nodup G f v r own h).idxOf_getElem j hj

theorem sent_mem_compSeq {r : ℕ} {c : V} {F' : Finset V}
    (hs : Sent G f (Mr G f N B inp ev r) c F') :
    ∃ t, F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) := by
  obtain ⟨hF, t, ht⟩ := (sent_iff G f N B inp ev).mp hs
  exact ⟨t, (mem_compSeq G f).mpr ⟨hF, ht⟩⟩

theorem mem_compSeq_later {r : ℕ} {c : V} {F' : Finset V} {t t' : ℕ} (htt : t ≤ t')
    (h : F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c)) :
    F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t' c) :=
  (compSeq_prefix G f c r _ (hst_prefix G f N B inp ev htt c)).subset h

/-- `idx_inj` of `RoundExec`. -/
theorem idx_inj' (r : ℕ) (c : V) (F₁ F₂ : Finset V) (h₁ : Sent G f (Mr G f N B inp ev r) c F₁)
    (h₂ : Sent G f (Mr G f N B inp ev r) c F₂)
    (he : idxR G f N B inp ev r c F₁ = idxR G f N B inp ev r c F₂) : F₁ = F₂ := by
  obtain ⟨t₁, ht₁⟩ := sent_mem_compSeq G f N B inp ev h₁
  obtain ⟨t₂, ht₂⟩ := sent_mem_compSeq G f N B inp ev h₂
  have a₁ := mem_compSeq_later G f N B inp ev (le_max_left t₁ t₂) ht₁
  have a₂ := mem_compSeq_later G f N B inp ev (le_max_right t₁ t₂) ht₂
  rw [idxR_eq G f N B inp ev a₁, idxR_eq G f N B inp ev a₂] at he
  exact counter_inj G f a₁ a₂ he

/-- `CR_fifo` of `RoundExec`. -/
theorem CR_fifo' (r : ℕ) {v : V} (hv : v ∉ B) (t : ℕ) (c : V) (P : List V)
    (Mc : Finset (Msg V)) (F' F'' : Finset V) (hm : (c, P, Mc, F') ∈ CRr G f N B inp ev r v t)
    (hP : Avoids P B) (hs'' : Sent G f (Mr G f N B inp ev r) c F'')
    (hlt : idxR G f N B inp ev r c F'' < idxR G f N B inp ev r c F') :
    (c, P, mcMsg G (Mr G f N B inp ev r) c F'', F'') ∈ CRr G f N B inp ev r v t := by
  rcases (mem_CRop G f).mp hm with ⟨e, he, k, hce, hall⟩ | ⟨h1, h2, hF, hs, h5⟩
  · obtain ⟨-, hF', hs', -, hk⟩ := genuine G f N B inp ev r _ P rfl v hv t e c Mc F' k he hce hP
    have hF'mem : F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) :=
      (mem_compSeq G f).mpr ⟨hF', hs'⟩
    rw [idxR_eq G f N B inp ev hF'mem, ← hk] at hlt
    obtain ⟨e', he', Mc₁, F₁, hce'⟩ := hall _ hlt
    obtain ⟨-, hF₁, hs₁, hMc₁, hk₁⟩ :=
      genuine G f N B inp ev r _ P rfl v hv t e' c Mc₁ F₁ _ he' hce' hP
    have hF₁mem : F₁ ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) :=
      (mem_compSeq G f).mpr ⟨hF₁, hs₁⟩
    have hF₁eq : F₁ = F'' := by
      apply idx_inj' G f N B inp ev r c F₁ F'' ((sent_iff G f N B inp ev).mpr ⟨hF₁, t, hs₁⟩) hs''
      rw [idxR_eq G f N B inp ev hF₁mem]; exact hk₁.symm
    subst hF₁eq
    refine (mem_CRop G f).mpr (Or.inl ⟨e', he', idxR G f N B inp ev r c F₁, ?_,
      fun i hi => hall i (by omega)⟩)
    rw [hce', hMc₁, ← mcMsg_eq G f N B inp ev hs₁]
  · simp only at h1 h2 hF hs h5
    subst h1 h2 h5
    have hF'mem : F' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) :=
      (mem_compSeq G f).mpr ⟨hF, hs⟩
    obtain ⟨t'', ht''⟩ := sent_mem_compSeq G f N B inp ev hs''
    have hF''mem : F'' ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c) := by
      rcases le_total t'' t with h | h
      · exact mem_compSeq_later G f N B inp ev h ht''
      · have hpre := compSeq_prefix G f c r (ownF G f N inp c r) (hst_prefix G f N B inp ev h c)
        rw [idxR_eq G f N B inp ev hF'mem, idxR_eq G f N B inp ev ht''] at hlt
        have l1 := List.idxOf_lt_length_iff.mpr hF'mem
        have hlt' : (compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t'' c)).idxOf F'' <
            (compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t c)).length := by
          simp only [counter] at hlt l1 ⊢; omega
        have l2 := List.idxOf_lt_length_iff.mpr ht''
        have := List.getElem_idxOf l2
        rw [← this, ← hpre.getElem hlt']
        exact List.getElem_mem _
    have hs'' : (mcK G c r (ownF G f N inp c r) (hst G f N B inp ev t c) F'').isSome :=
      ((mem_compSeq G f).mp hF''mem).2
    exact (mem_CRop G f).mpr (Or.inr ⟨rfl, rfl, ((mem_compSeq G f).mp hF''mem).1, hs'',
      mcMsg_eq G f N B inp ev hs''⟩)

/-! ## Liveness of FIFO-Flood -/

variable {G f N B inp ev} in
/-- A `COMPLETE` message originated by a correct node travels along every simple path of correct
nodes. -/
theorem travel (r : ℕ) (hr : r < N) (hfair : Fair (alg G f N) G B inp ev) {c : V} (hc : c ∉ B)
    {Mc : Finset (Msg V)} {F'' : Finset V} {j t₁ : ℕ}
    (horig : ∀ w ∈ outL G c, (w, BMsg.comp r c Mc F'' j [c]) ∈
      (spec G f N).allSends c (inp c) (hst G f N B inp ev t₁ c)) :
    ∀ (b : List V) (v : V), IsSimplePath G (c :: b) c v → b ≠ [] → Avoids (c :: b) B →
      ∃ t, ∃ e ∈ hst G f N B inp ev t v, compOf v r e = some (c, c :: b, Mc, F'', j) := by
  intro b
  induction b using List.reverseRecOn with
  | nil => intro _ _ h; exact absurd rfl h
  | append_singleton b₀ v ih =>
    intro v' hP _ hPB
    have hvv : v' = v := by
      have := hP.1.2.1
      rw [← List.cons_append, List.getLast?_append] at this; simpa using this.symm
    subst hvv
    obtain ⟨q, hq, hadj, hqv, hql⟩ := IsSimplePath.of_snoc hP
    have hvB : v' ∉ B := hPB v' (by simp)
    have hqB : q ∉ B := hPB q (List.mem_cons.mpr (by
      rcases List.mem_cons.mp (List.mem_of_getLast? hql) with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)))
    have hnd : (c :: (b₀ ++ [v'])).Nodup := hP.2
    by_cases hb₀ : b₀ = []
    · subst hb₀
      have hqc : q = c := by simpa using hql.symm
      subst hqc
      obtain ⟨t, ht⟩ := (spec G f N).mem_hist_of_mem_sent G B inp ev hfair hc hvB hqv hadj
        (horig v' ((mem_outL G).mpr ⟨hadj, hqv⟩))
      exact ⟨t, _, ht, by simp [compOf]⟩
    · obtain ⟨t, e, he, hce⟩ := ih q hq hb₀ (fun y hy => hPB y (by
        rcases List.mem_cons.mp hy with h | h
        · exact h ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)))
      obtain ⟨p₀, he', hp₀, hpp⟩ := compOf_eq_some hce
      simp only at he' hpp
      obtain ⟨A, C, hAC⟩ := List.append_of_mem he
      have hnd1 : (p₀ ++ [q]).Nodup := by rw [← hpp]; exact hq.2
      have hnd2 : (p₀ ++ [q, v']).Nodup := by
        have : p₀ ++ [q, v'] = c :: (b₀ ++ [v']) := by rw [← List.cons_append, hpp]; simp
        rw [this]; exact hnd
      have hrel := react_relay_comp G f N (x := inp q) (A := A) (c := c) (Mc := Mc) (F' := F'')
        (k := j) hr hp₀ hnd1 ((mem_outL G).mpr ⟨hadj, hqv⟩) hnd2
      rw [← he'] at hrel
      have hsent : (v', BMsg.comp r c Mc F'' j (p₀ ++ [q])) ∈
          (spec G f N).allSends q (inp q) (hst G f N B inp ev t q) := by
        refine mem_allSends.mpr ⟨A.length + 1, ?_, ?_⟩
        · have := congrArg List.length hAC
          simp only [List.length_append, List.length_cons] at this
          show A.length + 1 ≤ (hst G f N B inp ev t q).length
          omega
        · have : (hst G f N B inp ev t q).take (A.length + 1) = A ++ [e] := by
            rw [hAC, List.take_append]; simp
          show _ ∈ (spec G f N).react q (inp q) ((hst G f N B inp ev t q).take (A.length + 1))
          rw [this]; exact hrel
      obtain ⟨t', ht'⟩ := (spec G f N).mem_hist_of_mem_sent G B inp ev hfair hqB hvB hqv hadj hsent
      refine ⟨t', _, ht', ?_⟩
      have h1 : c :: (b₀ ++ [v']) = p₀ ++ [q] ++ [v'] := by rw [← List.cons_append, hpp]
      simp [compOf, h1]

variable {G f N B inp ev} in
/-- Every `COMPLETE` of a correct node is eventually originated towards all out-neighbours, with
its final content and counter. -/
theorem originated (r : ℕ) (hr : r < N) {c : V} {t₁ : ℕ} {F : Finset V}
    (hF : F ∈ compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c)) :
    ∀ w ∈ outL G c, (w, BMsg.comp r c
      (mcContent G c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c) F) F
      (counter G f c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c) F) [c]) ∈
        (spec G f N).allSends c (inp c) (hst G f N B inp ev t₁ c) := by
  intro w hw
  obtain ⟨hFt, hs⟩ := (mem_compSeq G f).mp hF
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  have hkl : k ≤ (hst G f N B inp ev t₁ c).length := (firstIdx_eq_some.mp hk).1
  set h₀ := (hst G f N B inp ev t₁ c).take k
  have hpre : h₀ <+: hst G f N B inp ev t₁ c := List.take_prefix _ _
  have hlen : h₀.length = k := by simp [h₀, hkl]
  have hk₀ : mcK G c r (ownF G f N inp c r) h₀ F = some h₀.length := by
    rw [hlen]; exact mcK_prefix_le G c r _ hpre hk (by omega)
  have hs₀ : (mcK G c r (ownF G f N inp c r) h₀ F).isSome := by rw [hk₀]; rfl
  refine mem_allSends.mpr ⟨k, hkl, ?_⟩
  have := react_newComp G f N (x := inp c) (h := h₀) hr hFt hk₀ hw
  rw [mcContent_prefix G c r _ hpre hs₀ |>.symm,
    counter_prefix G f c r _ hpre ((mem_compSeq G f).mpr ⟨hFt, hs₀⟩) |>.symm] at *
  exact this

variable {G f N B inp ev} in
/-- `CR_live` of `RoundExec`. -/
theorem CR_live' (r : ℕ) (hr : r < N) (hfair : Fair (alg G f N) G B inp ev) {v : V} (hv : v ∉ B)
    (c : V) (P : List V) (F' : Finset V) (hs : Sent G f (Mr G f N B inp ev r) c F')
    (hP : IsSimplePath G P c v) (hPB : Avoids P B) :
    ∃ t, (c, P, mcMsg G (Mr G f N B inp ev r) c F', F') ∈ CRr G f N B inp ev r v t := by
  classical
  have hc : c ∉ B := hPB c (List.mem_of_head? hP.1.1)
  obtain ⟨t₁, ht₁⟩ := sent_mem_compSeq G f N B inp ev hs
  set L := compSeq G f c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c)
  have hsF := ((mem_compSeq G f).mp ht₁).2
  have hmc : mcMsg G (Mr G f N B inp ev r) c F' =
      mcContent G c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c) F' :=
    mcMsg_eq G f N B inp ev hsF
  have hPc : P = c :: P.tail := hP.eq_cons
  by_cases htail : P.tail = []
  · -- `P = [c]`, `c = v`: the own entry
    have hPc' : P = [c] := by rw [hPc, htail]
    have hcv : c = v := by
      have := hP.1.2.1; rw [hPc'] at this; simpa using this
    subst hcv
    refine ⟨t₁, (mem_CRop G f).mpr (Or.inr ⟨rfl, hPc', ((mem_compSeq G f).mp ht₁).1, hsF, hmc⟩)⟩
  -- every `COMPLETE` with counter `≤` that of `F'` travels along `P`
  have hidx : (L.idxOf F') < L.length := List.idxOf_lt_length_iff.mpr ht₁
  have hctr : ∀ j < L.length, ∃ t, ∃ e ∈ hst G f N B inp ev t v, ∃ Mc'' F'',
      compOf v r e = some (c, P, Mc'', F'', j) := by
    intro j hj
    have hmem : L[j] ∈ L := List.getElem_mem hj
    have horig := originated (G := G) (B := B) (ev := ev) r hr hmem
    rw [counter_getElem G f hj] at horig
    obtain ⟨t, e, he, hce⟩ := travel r hr hfair hc horig P.tail v (by rw [← hPc]; exact hP)
      htail (by rw [← hPc]; exact hPB)
    rw [← hPc] at hce
    exact ⟨t, e, he, _, _, hce⟩
  have hfin : {j | j < L.idxOf F'}.Finite := Set.finite_lt_nat _
  obtain ⟨T₁, hT₁⟩ := hfin.exists_forall_of_monotone
    (p := fun j t => ∃ e ∈ hst G f N B inp ev t v, ∃ Mc'' F'',
      compOf v r e = some (c, P, Mc'', F'', j))
    (fun j _ t t' htt ⟨e, he, h⟩ => ⟨e, (hst_prefix G f N B inp ev htt v).subset he, h⟩)
    (fun j hj => hctr j (by simp at hj; omega))
  have horigF := originated (G := G) (B := B) (ev := ev) r hr ht₁
  obtain ⟨T₂, eF, heF, hceF⟩ := travel r hr hfair hc horigF P.tail v (by rw [← hPc]; exact hP)
    htail (by rw [← hPc]; exact hPB)
  rw [← hPc] at hceF
  refine ⟨max T₁ T₂, (mem_CRop G f).mpr (Or.inl ⟨eF,
    (hst_prefix G f N B inp ev (le_max_right _ _) v).subset heF,
    counter G f c r (ownF G f N inp c r) (hst G f N B inp ev t₁ c) F', ?_, fun j hj => ?_⟩)⟩
  · rw [hceF, hmc]
  · have hj' : j < L.idxOf F' := by simpa [counter] using hj
    obtain ⟨e, he, Mc'', F'', hce⟩ := hT₁ j hj'
    exact ⟨e, (hst_prefix G f N B inp ev (le_max_left _ _) v).subset he, Mc'', F'', hce⟩

end BWOp

end AsyncApproxBCDirected
