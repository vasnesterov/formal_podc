import Papers.PODC2017.RegisterEmulationSpace.Lemma4

/-!
# One round of Lemma 1: the adversary `Ad_i` and its invariants (Section 3.2)

Round `i` of the construction of Lemma 1: after a sequential run (configuration `X₀`, all clients
idle, covered registers `K = Cov(t_{i-1})`), a fresh writer `a` invokes `write(v)` and only `a` acts.
The adversary freezes (never lets respond) all operations of `a` on the servers of
`zSet Q Wd = Q ∪ G`, where
* `Q` (the paper's `Q_i`): the set `covF` of servers outside `F` holding a register outside `K`
  covered by `a`, as long as this set has at most `f` elements, and frozen afterwards;
* `fr = frSet Wd` (the paper's `F_i`, restricted to `F`): servers holding a register outside `K`
  written in this round;
* `G = F \ fr` as long as `|Q| < |fr ∩ F|`, else `∅` (a simplification of the paper's
  `G_i = M_i`: we freeze all of `F \ F_i`, not only the servers with a covered register).

Invariants (the paper's Lemma 2): `Q ⊆ covF`, `|Q| ≤ f`, `|fr ∩ F| ≤ |Q| + 1`,
`|Q| < f → Q = covF ∧ fr ⊆ F`, `Q ∩ fr = ∅`. Hence at most `f` servers are frozen (Claim 1), the
frozen set is eventually constant, so the strategy run is fair with these servers crashed and `a`
returns (Lemma 3). By `fresh_resp` (Lemma 4) `|fr| > f` at the return, hence `|Q| = f`
(Corollary 2): `f` servers outside `F` keep a fresh register covered by `a`.

Unlike the paper's `Ad_i`, our adversary also freezes the *reads* of `a` on frozen servers, so that
the strategy run itself is fair (in the paper, reads on `Q_i ∪ M_i` keep responding, and the crash
run of Lemma 3 must crash these servers only at the stabilization time, not "immediately after `r`").
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace

variable {C B V W L S : Type*} [DecidableEq C] [DecidableEq B] [DecidableEq S] [Fintype B]

open Function

section Defs

variable (δ : B → S) (F : Finset S) (a : C) (K : Finset B)

open Classical in
/-- Registers outside `K` covered by a pending write of `a`. -/
noncomputable def fcov (X : Cfg C B V W L) : Finset B :=
  Finset.univ.filter fun b => b ∉ K ∧ ∃ p ∈ X.pend a, p.reg = b ∧ p.op.IsWrite

/-- Servers outside `F` holding a register of `fcov`. -/
noncomputable def covF (X : Cfg C B V W L) : Finset S := (fcov a K X).image δ \ F

open Classical in
/-- Servers holding a register outside `K` written in the round (`F_i` of the paper, on all
servers). -/
noncomputable def frSet (Wd : Finset B) : Finset S := (Wd.filter (· ∉ K)).image δ

/-- The frozen servers. -/
noncomputable def zSet (Q : Finset S) (Wd : Finset B) : Finset S :=
  Q ∪ (if Q.card < (frSet δ K Wd ∩ F).card then F \ frSet δ K Wd else ∅)

/-- The register written by an event (if it is the response of a write). -/
def written (X : Cfg C B V W L) : Ev C V → Finset B
  | .resp c n =>
    match (X.pend c).find? (fun q => q.n = n) with
    | some ⟨_, b, .write _⟩ => {b}
    | _ => ∅
  | _ => ∅

/-- State of the round: configuration, `Q`, registers written so far in the round. -/
structure RS (C B V W L S : Type*) where
  X : Cfg C B V W L
  Q : Finset S
  Wd : Finset B

variable (A : Alg C B V W L) (f : ℕ)

/-- One step of the adversary `Ad_i`. -/
noncomputable def rstep (st : RS C B V W L S) : RS C B V W L S :=
  let e := soloEv δ a (zSet δ F K st.Q st.Wd) st.X
  let X' := A.step st.X e
  ⟨X', if (covF δ F a K X').card ≤ f then covF δ F a K X' else st.Q, st.Wd ∪ written st.X e⟩

/-- The run of the round. -/
noncomputable def rseq (X₁ : Cfg C B V W L) : ℕ → RS C B V W L S
  | 0 => ⟨X₁, ∅, ∅⟩
  | t + 1 => rstep δ F a K A f (rseq X₁ t)

end Defs

lemma mem_fcov {a : C} {K : Finset B} {X : Cfg C B V W L} {b : B} :
    b ∈ fcov a K X ↔ b ∉ K ∧ ∃ p ∈ X.pend a, p.reg = b ∧ p.op.IsWrite := by
  simp [fcov]

lemma mem_covF {δ : B → S} {F : Finset S} {a : C} {K : Finset B} {X : Cfg C B V W L} {s : S} :
    s ∈ covF δ F a K X ↔ s ∉ F ∧ ∃ p ∈ X.pend a, p.op.IsWrite ∧ p.reg ∉ K ∧ δ p.reg = s := by
  simp only [covF, Finset.mem_sdiff, Finset.mem_image, mem_fcov]
  constructor
  · rintro ⟨⟨b, ⟨hbK, p, hp, rfl, hw⟩, rfl⟩, hF⟩; exact ⟨hF, p, hp, hw, hbK, rfl⟩
  · rintro ⟨hF, p, hp, hw, hK, rfl⟩; exact ⟨⟨p.reg, ⟨hK, p, hp, rfl, hw⟩, rfl⟩, hF⟩

lemma mem_frSet {δ : B → S} {K : Finset B} {Wd : Finset B} {s : S} :
    s ∈ frSet δ K Wd ↔ ∃ b ∈ Wd, b ∉ K ∧ δ b = s := by
  simp [frSet, and_assoc]

lemma frSet_mono {δ : B → S} {K : Finset B} {Wd Wd' : Finset B} (h : Wd ⊆ Wd') :
    frSet δ K Wd ⊆ frSet δ K Wd' := by
  intro s hs
  obtain ⟨b, hb, hbK, rfl⟩ := mem_frSet.1 hs
  exact mem_frSet.2 ⟨b, h hb, hbK, rfl⟩

/-- At most `f` servers are frozen (Claim 1). -/
lemma zSet_card_le {δ : B → S} {F : Finset S} {K : Finset B} {f : ℕ} (hF : F.card ≤ f + 1)
    {Q : Finset S} {Wd : Finset B} (hq : Q.card ≤ f)
    (hfr : (frSet δ K Wd ∩ F).card ≤ Q.card + 1) : (zSet δ F K Q Wd).card ≤ f := by
  unfold zSet
  split_ifs with h
  · have h1 : (F \ frSet δ K Wd).card + (frSet δ K Wd ∩ F).card = F.card := by
      rw [Finset.inter_comm, Finset.card_sdiff_add_card_inter]
    calc (Q ∪ (F \ frSet δ K Wd)).card ≤ Q.card + (F \ frSet δ K Wd).card :=
          Finset.card_union_le _ _
      _ ≤ f := by omega
  · simpa using hq

/-- The `Q`-update keeps `Q` when the new `covF` is between `Q` and the old `covF`. -/
lemma qupd_eq {f : ℕ} {Q K K' : Finset S} (hQK' : Q ⊆ K') (hK'K : K' ⊆ K) (hq : Q.card ≤ f)
    (hsmall : Q.card < f → Q = K) : (if K'.card ≤ f then K' else Q) = Q := by
  split_ifs with h
  · rcases Nat.lt_or_ge Q.card f with hl | hl
    · exact (Finset.Subset.antisymm hQK' ((hsmall hl) ▸ hK'K)).symm
    · exact (Finset.eq_of_subset_of_card_le hQK' (by omega)).symm
  · rfl

namespace Alg

variable (A : Alg C B V W L)

lemma doStep_pend_self (X : Cfg C B V W L) (c : C) :
    ∃ l : List (POp B W), l.length ≤ 1 ∧ (A.doStep X c).pend c = X.pend c ++ l := by
  unfold doStep
  split
  · rename_i b o _
    exact ⟨[⟨X.cnt c, b, o⟩], by simp, by simp⟩
  · split <;> exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩

lemma covF_doStep {δ : B → S} {F : Finset S} {a : C} {K : Finset B} (X : Cfg C B V W L) :
    covF δ F a K X ⊆ covF δ F a K (A.doStep X a) ∧
    (covF δ F a K (A.doStep X a)).card ≤ (covF δ F a K X).card + 1 := by
  obtain ⟨l, hl, he⟩ := A.doStep_pend_self X a
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨hF, p, hp, hw, hK, rfl⟩ := mem_covF.1 hs
    exact mem_covF.2 ⟨hF, p, by rw [he]; exact List.mem_append_left _ hp, hw, hK, rfl⟩
  · match l, hl with
    | [], _ =>
      rw [List.append_nil] at he
      have : covF δ F a K (A.doStep X a) = covF δ F a K X := by
        ext s; simp only [mem_covF, he]
      rw [this]; omega
    | [q], _ =>
      have : covF δ F a K (A.doStep X a) ⊆ insert (δ q.reg) (covF δ F a K X) := by
        intro s hs
        obtain ⟨hF, p, hp, hw, hK, rfl⟩ := mem_covF.1 hs
        rw [he] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exact Finset.mem_insert_of_mem (mem_covF.2 ⟨hF, p, hp, hw, hK, rfl⟩)
        · simp at hp; subst hp; exact Finset.mem_insert_self _ _
      exact (Finset.card_le_card this).trans (Finset.card_insert_le _ _)

lemma covF_apply {δ : B → S} {F : Finset S} {a : C} {K : Finset B} {X : Cfg C B V W L}
    (hwf : WF X) {p : POp B W} (hp : p ∈ X.pend a) :
    covF δ F a K (A.apply X a p) ⊆ covF δ F a K X ∧
    ∀ s ∈ covF δ F a K X, s ≠ δ p.reg → s ∈ covF δ F a K (A.apply X a p) := by
  have hpend : (A.apply X a p).pend a = (X.pend a).filter (fun q => q.n ≠ p.n) :=
    A.apply_pend_self X a p
  refine ⟨fun s hs => ?_, fun s hs hne => ?_⟩
  · obtain ⟨hF, q, hq, hw, hK, rfl⟩ := mem_covF.1 hs
    rw [hpend] at hq
    exact mem_covF.2 ⟨hF, q, List.mem_of_mem_filter hq, hw, hK, rfl⟩
  · obtain ⟨hF, q, hq, hw, hK, rfl⟩ := mem_covF.1 hs
    refine mem_covF.2 ⟨hF, q, ?_, hw, hK, rfl⟩
    rw [hpend]
    exact (mem_filter_ne hwf hp).2 ⟨hq, fun h => hne (by rw [h])⟩

lemma written_apply {X : Cfg C B V W L} (hwf : WF X) {c : C} {p : POp B W} (hp : p ∈ X.pend c) :
    written X (.resp c p.n : Ev C V) ⊆ {p.reg} ∧
    (∀ b ∈ written X (.resp c p.n : Ev C V), p.op.IsWrite) := by
  simp only [written, find_n hwf hp]
  obtain ⟨n, b, o⟩ := p
  cases o <;> simp

lemma written_step (X : Cfg C B V W L) (c : C) : written X (.step c : Ev C V) = ∅ := rfl

/-- The round invariant (Lemma 2 of the paper, adapted). -/
structure RInv (δ : B → S) (F : Finset S) (a : C) (K : Finset B) (f : ℕ)
    (X₀ : Cfg C B V W L) (v : V) (st : RS C B V W L S) : Prop where
  other : ∀ c ≠ a, st.X.pend c = X₀.pend c ∧ st.X.loc c = X₀.loc c ∧ st.X.cur c = X₀.cur c ∧
    st.X.cnt c = X₀.cnt c
  val : ∀ b ∉ st.Wd, st.X.val b = X₀.val b
  qsub : st.Q ⊆ covF δ F a K st.X
  qcard : st.Q.card ≤ f
  fcard : (frSet δ K st.Wd ∩ F).card ≤ st.Q.card + 1
  small : st.Q.card < f → st.Q = covF δ F a K st.X ∧ frSet δ K st.Wd ⊆ F
  disj : Disjoint st.Q (frSet δ K st.Wd)
  ret : RetInv a (.write v) (X₀.hist ++ [.inv a (.write v)]) st.X
  wf : WF st.X

theorem rInv_step {δ : B → S} {F : Finset S} {a : C} {K : Finset B} {f : ℕ}
    {X₀ : Cfg C B V W L} {v : V} {st : RS C B V W L S} (h : RInv δ F a K f X₀ v st) :
    RInv δ F a K f X₀ v (rstep δ F a K A f st) ∧ st.Q ⊆ (rstep δ F a K A f st).Q ∧
      st.Wd ⊆ (rstep δ F a K A f st).Wd := by
  set Z := zSet δ F K st.Q st.Wd with hZ
  have hQZ : st.Q ⊆ Z := Finset.subset_union_left
  have hother : ∀ c ≠ a, (A.step st.X (soloEv δ a Z st.X)).pend c = X₀.pend c ∧
      (A.step st.X (soloEv δ a Z st.X)).loc c = X₀.loc c ∧
      (A.step st.X (soloEv δ a Z st.X)).cur c = X₀.cur c ∧
      (A.step st.X (soloEv δ a Z st.X)).cnt c = X₀.cnt c := by
    intro c hc
    obtain ⟨h1, h2, h3, h4⟩ := A.step_other st.X (soloEv_isOf δ a Z st.X) hc
    obtain ⟨g1, g2, g3, g4⟩ := h.other c hc
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
  have hret := A.retInv_step h.ret (soloEv_isOf δ a Z st.X)
  have hwf := A.wf_step h.wf (soloEv δ a Z st.X)
  rcases soloEv_cases δ a Z st.X with ⟨hs, -⟩ | ⟨p, hp, hpZ, hr⟩
  · -- a step of `a`: `covF` grows by at most one server, nothing is written
    obtain ⟨hsub, hcard⟩ := A.covF_doStep (δ := δ) (F := F) (K := K) st.X
    have hX' : A.step st.X (soloEv δ a Z st.X) = A.doStep st.X a := by rw [hs]; rfl
    set K' := covF δ F a K (A.doStep st.X a)
    have hQK' : st.Q ⊆ K' := h.qsub.trans hsub
    have hrs : rstep δ F a K A f st = ⟨A.doStep st.X a, if K'.card ≤ f then K' else st.Q, st.Wd⟩ := by
      simp only [rstep, ← hZ, hs, written_step, Finset.union_empty]; rfl
    rw [hrs]
    have hQ'sub : st.Q ⊆ if K'.card ≤ f then K' else st.Q := by split_ifs <;> simp [hQK']
    refine ⟨⟨fun c hc => hX' ▸ hother c hc, fun b hb => by simpa using h.val b hb, ?_, ?_, ?_, ?_,
      ?_, hX' ▸ hret, hX' ▸ hwf⟩, hQ'sub, subset_rfl⟩
    · show (if K'.card ≤ f then K' else st.Q) ⊆ K'
      split_ifs <;> first | exact subset_rfl | exact hQK'
    · dsimp only; split_ifs with h' <;> [exact h'; exact h.qcard]
    · exact h.fcard.trans (by have := Finset.card_le_card hQ'sub; dsimp only at this ⊢; omega)
    · dsimp only
      intro hlt
      split_ifs at hlt ⊢ with h'
      · exact ⟨rfl, (h.small (lt_of_le_of_lt (Finset.card_le_card hQK') hlt)).2⟩
      · exfalso
        have := (h.small hlt).1
        rw [← this] at hcard
        omega
    · dsimp only
      split_ifs with h'
      · rcases Nat.lt_or_ge st.Q.card f with hl | hl
        · rw [Finset.disjoint_left]
          intro s hs hs'
          exact (mem_covF.1 hs).1 ((h.small hl).2 hs')
        · rw [← Finset.eq_of_subset_of_card_le hQK' (by omega)]; exact h.disj
      · exact h.disj
  · -- a response to `a`'s operation `p` on an unfrozen server
    have hX' : A.step st.X (soloEv δ a Z st.X) = A.apply st.X a p := by
      rw [hr, step_resp, A.doResp_of_mem h.wf hp]
    obtain ⟨hsub, hkeep⟩ := A.covF_apply (δ := δ) (F := F) (K := K) h.wf hp
    obtain ⟨hwr, hwrw⟩ := written_apply h.wf hp
    set K' := covF δ F a K (A.apply st.X a p)
    have hQK' : st.Q ⊆ K' := fun s hs =>
      hkeep s (h.qsub hs) (fun he => hpZ (he ▸ hQZ hs))
    have hQ' : (if K'.card ≤ f then K' else st.Q) = st.Q :=
      qupd_eq hQK' hsub h.qcard (fun hl => (h.small hl).1)
    set Wd' := st.Wd ∪ written st.X (.resp a p.n)
    have hrs : rstep δ F a K A f st = ⟨A.apply st.X a p, st.Q, Wd'⟩ := by
      have hX'' : A.step st.X (Ev.resp a p.n) = A.apply st.X a p := hr ▸ hX'
      simp only [rstep, ← hZ, hr, hX'']
      rw [hQ']
    rw [hrs]
    -- new fresh responders
    have hfr : ∀ s ∈ frSet δ K Wd', s ∈ frSet δ K st.Wd ∨
        (s = δ p.reg ∧ p.op.IsWrite ∧ p.reg ∉ K) := by
      intro s hs
      obtain ⟨b, hb, hbK, rfl⟩ := mem_frSet.1 hs
      rcases Finset.mem_union.1 hb with hb | hb
      · exact Or.inl (mem_frSet.2 ⟨b, hb, hbK, rfl⟩)
      · have := Finset.mem_singleton.1 (hwr hb)
        subst this
        exact Or.inr ⟨rfl, hwrw _ hb, hbK⟩
    refine ⟨⟨fun c hc => hX' ▸ hother c hc, ?_, hQK', h.qcard, ?_, ?_, ?_, hX' ▸ hret, hX' ▸ hwf⟩,
      subset_rfl, Finset.subset_union_left⟩
    · intro b hb
      have hb' : b ∉ written st.X (.resp a p.n) := fun h' => hb (Finset.mem_union_right _ h')
      rw [← h.val b (fun h' => hb (Finset.mem_union_left _ h'))]
      by_cases hbp : b = p.reg
      · subst hbp
        have : ¬ p.op.IsWrite := by
          intro hw
          apply hb'
          simp only [written, find_n h.wf hp]
          obtain ⟨n, r, o⟩ := p
          cases o with
          | read => exact hw.elim
          | write w => simp
        rw [A.apply_val]
        split
        · rfl
        · rename_i w hw; exact (this (by rw [hw]; trivial)).elim
      · exact A.apply_val_of_ne _ _ _ hbp
    · -- `|fr ∩ F| ≤ |Q| + 1`
      dsimp only
      by_cases hnew : δ p.reg ∈ F ∧ δ p.reg ∉ frSet δ K st.Wd
      · have hnz : ¬ st.Q.card < (frSet δ K st.Wd ∩ F).card := by
          intro hlt
          apply hpZ
          rw [hZ, zSet, if_pos hlt]
          exact Finset.mem_union_right _ (Finset.mem_sdiff.2 hnew)
        have : frSet δ K Wd' ∩ F ⊆ insert (δ p.reg) (frSet δ K st.Wd ∩ F) := by
          intro s hs
          rcases hfr s (Finset.mem_inter.1 hs).1 with h1 | ⟨rfl, -⟩
          · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨h1, (Finset.mem_inter.1 hs).2⟩)
          · exact Finset.mem_insert_self _ _
        have := (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
        omega
      · have : frSet δ K Wd' ∩ F ⊆ frSet δ K st.Wd ∩ F := by
          intro s hs
          obtain ⟨hs1, hs2⟩ := Finset.mem_inter.1 hs
          rcases hfr s hs1 with h1 | ⟨rfl, -⟩
          · exact Finset.mem_inter.2 ⟨h1, hs2⟩
          · push Not at hnew
            exact Finset.mem_inter.2 ⟨hnew hs2, hs2⟩
        exact (Finset.card_le_card this).trans h.fcard
    · intro hl
      refine ⟨?_, ?_⟩
      · exact Finset.Subset.antisymm hQK' ((h.small hl).1 ▸ hsub)
      · intro s hs
        rcases hfr s hs with h1 | ⟨rfl, hw, hK⟩
        · exact (h.small hl).2 h1
        · by_contra hF
          apply hpZ
          apply hQZ
          rw [(h.small hl).1]
          exact mem_covF.2 ⟨hF, p, hp, hw, hK, rfl⟩
    · rw [Finset.disjoint_left]
      intro s hs hs'
      rcases hfr s hs' with h1 | ⟨rfl, -⟩
      · exact Finset.disjoint_left.1 h.disj hs h1
      · exact hpZ (hQZ hs)

end Alg

end Podc.RegisterEmulationSpace
