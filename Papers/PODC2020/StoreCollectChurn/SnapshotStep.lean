import Papers.PODC2020.StoreCollectChurn.SnapshotFrame

/-!
# The step lemma: a node's own step preserves its invariant

This is where the paper's Lemma 12 is proved: when a scan borrows the view `V₁(q).sview` because
`⟨p, ssqno⟩ ∈ V₁(q).scounts`, regularity shows that the double collect certifying this view
started after `p`'s Line 71 store (`borrow_cert`).
-/

namespace Podc.StoreCollectChurn.Snap

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)}

lemma AfterStore.succ_of_notStore {i : ℕ} {p : P} {s s' : LState P V} {st : ℕ}
    (h : AfterStore E i p s st) (hns : ∀ y, ¬ StE E i p y) (hsto : s'.stored = s.stored)
    (hss : s'.ssqno = s.ssqno) : AfterStore E (i + 1) p s' st := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, hsto ▸ h2, hsto ▸ hss ▸ h3, fun a ha y hy hs => ?_⟩
  rcases Nat.lt_or_ge a i with hai | hai
  · exact h4 a hai y hy (hss ▸ hs)
  · obtain rfl : a = i := by omega
    exact absurd hy (hns y)

lemma NInv.mk_same {i : ℕ} {p : P} {s s' : LState P V} (hI : NInv E i p s)
    (hsto : s'.stored = s.stored) (hss : s.ssqno ≤ s'.ssqno) (hus : s.usqno ≤ s'.usqno)
    (hns : ∀ x, ¬ StE E i p x) (hpc : PCInv E (i + 1) p s') : NInv E (i + 1) p s' := by
  obtain ⟨hst, h2, h3, hok, -⟩ := hI
  refine ⟨fun a ha x hx => ?_, by rw [hsto]; omega, by rw [hsto]; omega,
    hsto ▸ hok.mono (by omega), hpc⟩
  rcases Nat.lt_or_ge a i with hai | hai
  · obtain ⟨h1, h2⟩ := hst a hai x hx
    exact ⟨hsto ▸ h1, by omega⟩
  · obtain rfl : a = i := by omega
    exact absurd hx (hns x)

lemma NInv.mk_store {i : ℕ} {p : P} {s s' : LState P V} {x : SCVal P V} (hI : NInv E i p s)
    (hx : StE E i p x) (hsto : s'.stored = x) (hfact : StoredOK E i p x)
    (hss : x.ssqno ≤ s'.ssqno) (hss' : s.ssqno ≤ s'.ssqno) (hus : x.usqno ≤ s'.usqno)
    (hge : s.stored.usqno ≤ x.usqno) (hpc : PCInv E (i + 1) p s') : NInv E (i + 1) p s' := by
  obtain ⟨hst, -, -, -, -⟩ := hI
  refine ⟨fun a ha y hy => ?_, by rw [hsto]; exact hss, by rw [hsto]; exact hus,
    hsto ▸ hfact.mono (by omega), hpc⟩
  rcases Nat.lt_or_ge a i with hai | hai
  · obtain ⟨h1, h2⟩ := hst a hai y hy
    exact ⟨by rw [hsto]; omega, by omega⟩
  · obtain rfl : a = i := by omega
    unfold StE at hx hy; rw [hx] at hy; cases hy
    exact ⟨by rw [hsto], hss⟩

/-- **Lemma 12 of the paper** (the core): if the collect `(ic, i)` of node `p`, whose current scan
stored `ssqno` at `st` (Line 71), returns `W` with `⟨p, ssqno⟩ ∈ W(q).scounts`, then the borrowed
view `W(q).sview` is certified by a double collect inside `(st, i]`. -/
lemma borrow_cert (hreg : Regular (scSched E)) (hpast : Past E i) {p q : P} {ic : ℕ}
    {W : SCView P V} {x : SCVal P V} {s : LState P V} {st : ℕ}
    (hc : ColE E ic i p W) (hWq : W q = some x) (hsc : x.scounts p = some s.ssqno)
    (has : AfterStore E i p s st) : Cert E x.sview st (i + 1) := by
  obtain ⟨a, hai, hax, -⟩ := reg1_some hreg hc hWq
  have hf := hpast.1 a hai q x hax
  obtain ⟨-, h0, h1⟩ := hf.ok
  have hu : 1 ≤ x.usqno := by
    by_contra hlt
    have := congrFun (h0 (by omega)) p
    rw [hsc] at this; cases this
  obtain ⟨l', l, W', hcl, hla, hsc', hcert, -⟩ := h1 hu
  rw [hsc'] at hsc
  simp only [ssqVec, Option.map_eq_some_iff] at hsc
  obtain ⟨y, hy, hys⟩ := hsc
  obtain ⟨a₂, ha₂l, ha₂, -⟩ := reg1_some hreg hcl hy
  have hl : l < a := hla
  have := has.2.2.2 a₂ (by omega) y ha₂ hys
  exact hcert.mono (by omega) (by omega)

end Podc.StoreCollectChurn.Snap

namespace Podc.StoreCollectChurn.Snap

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)}

lemma ScanCtx.transfer {i i' : ℕ} {p : P} {s s' : LState P V} {emb : Option V} {h lo lo' : ℕ}
    (hc : ScanCtx E i p s emb h lo) (hi : i ≤ i') (hlo : lo ≤ lo') (hH : NoHIn E p h i')
    (hU : updCnt E i' p = updCnt E i p) (h1 : s'.stored.usqno = s.stored.usqno)
    (h2 : s'.usqno = s.usqno) (h3 : s'.scounts = s.scounts) : ScanCtx E i' p s' emb h lo' := by
  obtain ⟨c1, -, c3, c4, c5⟩ := hc
  refine ⟨by omega, hH, by rw [h1, h2, c3], by omega, ?_⟩
  rcases emb with _ | v
  · exact ⟨c5.1, by rw [h2, hU, c5.2]⟩
  · obtain ⟨⟨u1, u2, u3⟩, l', l, W, hl1, hl2, hl3, hl4⟩ := c5
    exact ⟨⟨u1, by rw [hU, u2, h2], by rw [h2]; exact u3⟩, l', l, W, hl1, hl2, by omega,
      by rw [h3, hl4]⟩

/-- End of a scan whose result `W` is certified inside `(st, i]`. -/
lemma NInv.finish {i : ℕ} {p : P} {s : LState P V} {emb : Option V} {h st : ℕ}
    {W' : SCView P V} {W : P → Option V} (hI : NInv E i p s)
    (hctx : ScanCtx E i p s emb h st) (hhst : h < st) (has : AfterStore E i p s st)
    (hcert : Cert E W st (i + 1)) (he : E[i]? = some (.sc (.ret p W'))) :
    NInv E (i + 1) p (finishScan { s with V1 := W' } emb W) := by
  have hnst : ∀ x, ¬ StE E i p x := fun x hx => by rw [StE, he] at hx; simp at hx
  have hU : updCnt E (i + 1) p = updCnt E i p := updCnt_succ_of_none he rfl
  have hH : NoHIn E p h (i + 1) := hctx.2.1.succ he (fun _ => ⟨_, rfl⟩)
  have := has.1
  obtain ⟨c1, -, c3, c4, c5⟩ := hctx
  rcases emb with _ | v
  · refine hI.mk_same rfl le_rfl le_rfl hnst ?_
    simp only [finishScan, PCInv]
    exact ⟨h, by omega, c5.1, hH, hcert.mono (by omega) le_rfl, by rw [hU]; exact c5.2, c3⟩
  · refine hI.mk_same rfl le_rfl (by simp [finishScan]) hnst ?_
    obtain ⟨⟨u1, u2, u3⟩, l', l, W79, hl1, hl2, hl3, hl4⟩ := c5
    simp only [finishScan, PCInv]
    refine ⟨h, v, by omega, u1, hH, by rw [hU, u2], by rw [c3], ?_, l', l, W79, hl1, hl2,
      by omega, hl4, hcert.mono (by omega) le_rfl⟩
    simp [valOf, u3]

theorem NInv.step (pk : Pick P V) (hreg : Regular (scSched E)) {i : ℕ} {p : P}
    {s s' : LState P V} {e : Ev P V} (hpast : Past E i) (hI : NInv E i p s)
    (he : E[i]? = some e) (hp : e.proc = p) (hs : lstep pk p s e = some s') :
    NInv E (i + 1) p s' ∧ (∀ x, StE E i p x → StoreFact E i p x) ∧
      (∀ r, E[i]? = some (.hret p r) → RetFact E i p r) := by
  have hpc := hI.2.2.2.2
  unfold PCInv at hpc
  rcases hpc' : s.pc with _ | emb | emb | emb | ⟨emb, _ | _⟩ | emb | W | v | v | _ | _ | _ <;>
    rw [hpc'] at hpc <;>
    rcases e with ⟨q, _ | v'⟩ | ⟨q, r⟩ | ⟨⟨q, x⟩ | q | q | ⟨q, W'⟩⟩ <;>
    simp [lstep, hpc'] at hs <;>
    simp only [Ev.proc, SCEv.proc] at hp <;> subst hp <;> dsimp only at hpc
  case idle.hinv.scan =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨hu, hsu⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl (by simp) le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    refine ⟨i, ⟨by omega, NoHIn.self, hsu, by omega, he, ?_⟩, fun a ha y hy => ?_⟩
    · rw [updCnt_succ_of_none he rfl]; exact hu
    · rcases Nat.lt_or_ge a i with hai | hai
      · exact Nat.lt_succ_of_le (hI.1 a hai y hy).2
      · obtain rfl : a = i := by omega
        exact absurd hy (hnst y)
  case idle.hinv.update =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨hu, hsu⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    refine ⟨i, by omega, NoHIn.self, ⟨he, ?_, ?_⟩, hsu⟩
    · rw [updCnt_succ_of_some he (v := v') (by simp [updOf]), hu]
    · rw [hu]; exact updArgs_getElem he
  case scStore.sc.stInv =>
    obtain ⟨h, hc, hlt⟩ := hpc
    obtain ⟨rfl, rfl⟩ := hs
    have hfact : StoreFact E i q { s.stored with ssqno := s.ssqno } := by
      refine ⟨hI.2.2.2.1, ?_, fun a' ha' x' hx' => (hI.1 a' ha' x' hx').1⟩
      have c3 := hc.2.2.1
      have c5 := hc.2.2.2.2
      show s.stored.usqno ≤ _
      rcases emb with _ | v
      · rw [c3, c5.2]
      · rw [c3, c5.1.2.1]; omega
    refine ⟨hI.mk_store he rfl hfact.ok le_rfl le_rfl hI.2.2.1 le_rfl ?_,
      fun x hx => by rw [StE, he] at hx; cases hx; exact hfact,
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    refine ⟨h, i, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
      (updCnt_succ_of_none he rfl) rfl rfl rfl, hc.1, by omega, he, rfl, fun a ha y hy hys => ?_⟩
    rcases Nat.lt_or_ge a i with hai | hai
    · have := hlt a hai y hy; simp only at hys; omega
    · omega
  case scStoreW.sc.ack =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, st, hc, hhst, has⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, st, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
      (updCnt_succ_of_none he rfl) rfl rfl rfl, hhst, has.succ_of_notStore hnst rfl rfl⟩
  case scCol1.sc.colInv =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, st, hc, hhst, has⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, st, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
      (updCnt_succ_of_none he rfl) rfl rfl rfl, hhst, has.succ_of_notStore hnst rfl rfl,
      i, has.1, by omega, he, NoEvIn.self⟩
  case scColN.sc.colInv =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, st, hc, hhst, has, i₁, j₁, h1, h2, h3⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, st, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
      (updCnt_succ_of_none he rfl) rfl rfl rfl, hhst, has.succ_of_notStore hnst rfl rfl,
      i₁, j₁, i, h1, h2, h3, by omega, he, NoEvIn.self⟩
  case scColW.true.sc.ret =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, st, hc, hhst, has, ic, h1, h2, h3, h4⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, st, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
      (updCnt_succ_of_none he rfl) rfl rfl rfl, hhst, has.succ_of_notStore hnst rfl rfl,
      ic, i, h1, ⟨h3, he, nextE_of_noEvIn h2 h3 he rfl rfl h4⟩, by omega⟩
  case scColW.false.sc.ret =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    have hnr : ∀ r, E[i]? = some (.hret q r) → RetFact E i q r := fun r hr => by
      rw [he] at hr; simp at hr
    obtain ⟨h, st, hc, hhst, has, i₁, j₁, ic, h1, h2, h3, h4, h5, h6⟩ := hpc
    have hcol : ColE E ic i q W' := ⟨h5, he, nextE_of_noEvIn h4 h5 he rfl rfl h6⟩
    by_cases hd : ∀ r, rU W' r = rU s.V1 r
    · rw [if_pos hd] at hs
      cases hs
      refine ⟨hI.finish hc hhst has ?_ he, fun x hx => absurd hx (hnst x), hnr⟩
      exact ⟨i₁, j₁, q, s.V1, ic, i, q, W', h2, hcol, h1, h3, by omega,
        fun r => (hd r).symm, rfl⟩
    · rw [if_neg hd] at hs
      rcases hpk : pk.f W' q s.ssqno with _ | q'
      · rw [hpk] at hs
        cases hs
        refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x), hnr⟩
        simp only [PCInv]
        exact ⟨h, st, hc.transfer (by omega) le_rfl (hc.2.1.succ he fun _ => ⟨_, rfl⟩)
          (updCnt_succ_of_none he rfl) rfl rfl rfl, hhst, has.succ_of_notStore hnst rfl rfl,
          ic, i, (by have := h2.2.2.1; omega), hcol, by omega⟩
      · rw [hpk] at hs
        cases hs
        obtain ⟨x, hWx, hsc⟩ := pk.spec _ _ _ _ hpk
        have hcert := borrow_cert hreg hpast hcol hWx hsc has
        have hsv : sviewOf W' q' = x.sview := by simp [sviewOf, hWx]
        refine ⟨?_, fun x hx => absurd hx (hnst x), hnr⟩
        rw [hsv]
        exact hI.finish hc hhst has hcert he
  case scRet.hret =>
    obtain ⟨h, hlt, hh, hH, hcert, hu, hsu⟩ := hpc
    obtain ⟨rfl, rfl⟩ := hs
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => ?_⟩
    · simp only [PCInv]
      exact ⟨by rw [updCnt_succ_of_none he rfl]; exact hu, hsu⟩
    · rw [he] at hr; cases hr
      exact ⟨h, hlt, hH, Or.inl ⟨hh, hcert⟩⟩
  case upCol.sc.colInv =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, hlt, hH, hctx, hsu⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    obtain ⟨u1, u2, u3⟩ := hctx
    exact ⟨h, by omega, hH.succ he fun _ => ⟨_, rfl⟩,
      ⟨u1, by rw [updCnt_succ_of_none he rfl]; exact u2, u3⟩, hsu, i, hlt, by omega, he,
      NoEvIn.self⟩
  case upColW.sc.ret =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, hlt, hH, ⟨u1, u2, u3⟩, hsu, ic, h1, h2, h3, h4⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl (by simp) le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    refine ⟨h, ⟨by omega, hH.succ he fun _ => ⟨_, rfl⟩, hsu, by omega,
      ⟨u1, by rw [updCnt_succ_of_none he rfl]; exact u2, u3⟩, ic, i, W', ⟨h3, he,
      nextE_of_noEvIn h2 h3 he rfl rfl h4⟩, h1, by omega, rfl⟩, fun a ha y hy => ?_⟩
    rcases Nat.lt_or_ge a i with hai | hai
    · exact Nat.lt_succ_of_le (hI.1 a hai y hy).2
    · obtain rfl : a = i := by omega
      exact absurd hy (hnst y)
  case upStore.sc.stInv =>
    obtain ⟨h, v, hlt, hh, hH, hu, hsu, hval, l', l, W79, hl1, hl2, hl3, hl4, hcert⟩ := hpc
    obtain ⟨rfl, rfl⟩ := hs
    have hok : StoredOK E i q ⟨s.val, s.usqno, s.ssqno, s.sview, s.scounts⟩ :=
      ⟨hval, fun h0 => by simp only at h0; omega, fun _ => ⟨l', l, W79, hl1, hl3, hl4, hcert,
        h, v, hl2, hh, by simp only; rw [hu, updCnt_eq_of_noHIn hlt hH]⟩⟩
    have hfact : StoreFact E i q ⟨s.val, s.usqno, s.ssqno, s.sview, s.scounts⟩ :=
      ⟨hok, hu.le, fun a' ha' x' hx' => by have := (hI.1 a' ha' x' hx').1; simp only; omega⟩
    refine ⟨hI.mk_store he rfl hok le_rfl le_rfl le_rfl (by simp only; omega) ?_,
      fun x hx => by rw [StE, he] at hx; cases hx; exact hfact,
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, v, i, hlt, by omega, hh, hH.succ he fun _ => ⟨_, rfl⟩, he,
      by rw [updCnt_succ_of_none he rfl]; exact hu, trivial, NoEvIn.self⟩
  case upStoreW.sc.ack =>
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    obtain ⟨h, v, a, h1, h2, hh, hH, hst, hu, hsu, hn⟩ := hpc; subst hs
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => by rw [he] at hr; simp at hr⟩
    simp only [PCInv]
    exact ⟨h, v, a, i, h1, by omega, hh, hH.succ he fun _ => ⟨_, rfl⟩, hst,
      nextE_of_noEvIn h2 hst he rfl rfl hn, by rw [updCnt_succ_of_none he rfl]; exact hu, hsu⟩
  case upRet.hret =>
    obtain ⟨h, v, a, b, h1, h2, hh, hH, hst, hn, hu, hsu⟩ := hpc
    obtain ⟨rfl, rfl⟩ := hs
    have hnst : ∀ x, ¬ StE E i q x := fun x hx => by rw [StE, he] at hx; simp at hx
    refine ⟨hI.mk_same rfl le_rfl le_rfl hnst ?_, fun x hx => absurd hx (hnst x),
      fun r hr => ?_⟩
    · simp only [PCInv]
      exact ⟨by rw [updCnt_succ_of_none he rfl, hsu, hu], hsu.symm⟩
    · rw [he] at hr; cases hr
      have := hn.1
      exact ⟨h, by omega, hH, Or.inr ⟨v, hh, rfl, a, b, s.stored, h1, h2, hst, hn, hu⟩⟩

end Podc.StoreCollectChurn.Snap
