import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Reg
import Papers.PODC2017.RegisterEmulationSpace.Algorithm2SafetySteps

/-!
# Algorithm 2: preservation of the write-sequential invariant `RInv`, one event at a time
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

/-- Protection is preserved when values, `tsVal`s and queues are unchanged and pending writes only
disappear. -/
lemma Prot.congr {X X' : Cf} {T : ℕ} {b : B} (h : Prot X T b) (hval : X'.val = X.val)
    (hts : ∀ e, (X'.loc e).ts = (X.loc e).ts) (hq : ∀ e, (X'.loc e).q = (X.loc e).q)
    (hpw : ∀ e p, p ∈ X'.pend e → p.op.IsWrite → p ∈ X.pend e) : Prot X' T b :=
  ⟨hval ▸ h.1, fun e => ⟨fun p hp hpb w hw => (h.2 e).1 p (hpw e p hp (by simp [hw])) hpb w hw,
    fun hb => by rw [hts]; rw [hq] at hb; exact (h.2 e).2 hb⟩⟩

/-- Transfer of the invariant along events that change neither the history, nor values, nor
`tsVal`s, nor the bookkeeping sets, and only remove pending writes. -/
lemma rinv_congr {X X' : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) (hval : X'.val = X.val)
    (hcur : X'.cur = X.cur) (hhist : X'.hist = X.hist)
    (hloc : ∀ e, (X'.loc e).ts = (X.loc e).ts ∧ (X'.loc e).val = (X.loc e).val ∧
      (X'.loc e).pw = (X.loc e).pw ∧ (X'.loc e).cov = (X.loc e).cov ∧
      (X'.loc e).wr = (X.loc e).wr ∧ (X'.loc e).q = (X.loc e).q ∧ (X'.loc e).mode = (X.loc e).mode)
    (hpw : ∀ e p, p ∈ X'.pend e → p.op.IsWrite → p ∈ X.pend e)
    (hbest : ∀ e, (X'.loc e).mode.isColl → OKr v₀ X σ (X'.loc e).best)
    (hcoll : ∀ e lv (Q : Finset B), (∀ b ∈ Q, Prot X lv b) → (X.loc e).mode.isColl →
      ((∃ b ∈ Q, b ∈ (X.loc e).got) → lv ≤ (X.loc e).best.1) →
      ((∃ b ∈ Q, b ∈ (X'.loc e).got) → lv ≤ (X'.loc e).best.1)) :
    RInv δ f R v₀ Wr X' σ := by
  have hmode : ∀ e, (X'.loc e).mode = (X.loc e).mode := fun e => (hloc e).2.2.2.2.2.2
  have hWP : WP X → WP X' := fun ⟨d, v, h1, h2⟩ => ⟨d, v, hcur ▸ h1, (hmode d).trans h2⟩
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ x := fun x h => h.congr v₀ hWP
  have hU : ∀ e, U (X'.loc e) = U (X.loc e) := fun e => by
    simp only [U, (hloc e).2.2.1, (hloc e).2.2.2.2.2.1]
  have hw : ∀ e p w, p ∈ X'.pend e → p.op = .write w → p ∈ X.pend e :=
    fun e p w hp hpw' => hpw e p hp (by simp [hpw'])
  have hP : ∀ T b, Prot X T b → Prot X' T b := fun T b h =>
    h.congr hval (fun e => (hloc e).1) (fun e => (hloc e).2.2.2.2.2.1) hpw
  refine ⟨hS.reg, hcur ▸ hS.cur, fun d o h => hhist ▸ hS.inHist d o (hcur ▸ h), hS.lvl,
    fun d v h => hS.wlen d v (hcur ▸ h), fun h => hS.wnone (hcur ▸ h), hcur ▸ hS.wpend,
    fun d d' v v' h h' => hS.wuniq d d' v v' (hcur ▸ h) (hcur ▸ h'), ?_, ?_, ?_, ?_, ?_,
    fun e he => hOK _ (hbest e he), ?_, ?_, ?_⟩
  · intro c v ha hm; rw [(hloc c).1, (hloc c).2.1]
    exact hS.wpTs c v (hcur ▸ ha) (by rwa [hmode] at hm)
  · intro c v ha hm p hp w hpw' hcv
    rw [hmode] at hm; rw [(hloc c).2.2.2.1] at hcv
    exact hS.fresh c v (hcur ▸ ha) hm p (hw c p w hp hpw') w hpw' hcv
  · intro b; rw [hval]; exact hOK _ (hS.vals b)
  · intro e p hp w hpw'
    rw [(hloc e).1]
    exact ⟨hOK _ (hS.pends e p (hw e p w hp hpw') w hpw').1, (hS.pends e p (hw e p w hp hpw') w hpw').2⟩
  · intro e; rw [(hloc e).1, (hloc e).2.1]; exact hOK _ (hS.tsv e)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb)⟩
  · intro d o lv hop hc
    rw [hmode] at hc
    rcases hS.coll d o lv hop hc with h0 | ⟨Q, hQ, hQP, hQC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb), hcoll d lv Q hQP hc hQC⟩
  · intro c v ha hm
    rw [hmode] at hm
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (hloc c).2.2.2.2.1 hval hU]
    simp only [hU]
    exact hS.count c v (hcur ▸ ha) hm

/-- A step triggering a low-level write (line 10 or line 32). -/
lemma rinv_trigW {X : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) (d : C) (b : B)
    (hb : b ∈ (X.loc d).q) :
    RInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with q := (X.loc d).q.erase b,
                                                    pw := insert b (X.loc d).pw },
               pend := update X.pend d (X.pend d ++ [⟨X.cnt d, b, .write ((X.loc d).ts, (X.loc d).val)⟩]),
               cnt := update X.cnt d (X.cnt d + 1) } σ := by
  set l := X.loc d with hl
  set l' : Loc B V := { l with q := l.q.erase b, pw := insert b l.pw }
  set X' : Cf := { X with
      loc := update X.loc d l'
      pend := update X.pend d (X.pend d ++ [POp.mk (X.cnt d) b (.write (l.ts, l.val))])
      cnt := update X.cnt d (X.cnt d + 1) }
  have hmode := upd_field Loc.mode X.loc d l' rfl
  have hts := upd_field Loc.ts X.loc d l' rfl
  have hval := upd_field Loc.val X.loc d l' rfl
  have hwr := upd_field Loc.wr X.loc d l' rfl
  have hcov := upd_field Loc.cov X.loc d l' rfl
  have hgot := upd_field Loc.got X.loc d l' rfl
  have hbest := upd_field Loc.best X.loc d l' rfl
  have hU := upd_field U X.loc d l' (by
    simp only [U, l']; ext x; simp only [mem_union, mem_insert, mem_erase]
    by_cases hx : x = b
    · subst hx; simp only [true_or, true_iff]; exact Or.inr hb
    · simp only [hx, false_or, ne_eq, not_false_eq_true, true_and]; exact Iff.rfl)
  have hWP : WP X → WP X' := fun ⟨e, v, h1, h2⟩ => ⟨e, v, h1, (hmode e).trans h2⟩
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ x := fun x h => h.congr v₀ hWP
  have hP : ∀ T b', Prot X T b' → Prot X' T b' := by
    intro T b' h
    refine ⟨h.1, fun e => ⟨?_, ?_⟩⟩
    · intro p hp hpb w hw
      rcases (mem_upd_pend _ _ _ _ _).1 hp with hp | ⟨rfl, rfl⟩
      · exact (h.2 e).1 p hp hpb w hw
      · simp only [LOp.write.injEq] at hw
        rw [← hw]
        exact (h.2 e).2 (hpb ▸ hb)
    · intro hq
      rw [hts]
      by_cases he : e = d
      · subst he
        have hq2 : b' ∈ l.q.erase b := by simpa [X', l'] using hq
        exact (h.2 _).2 (mem_erase.1 hq2).2
      · have hq2 : b' ∈ (X.loc e).q := by simpa [X', update_of_ne he] using hq
        exact (h.2 e).2 hq2
  refine { hS with
    wpTs := ?_
    fresh := ?_
    vals := fun b' => hOK _ (hS.vals b')
    pends := ?_
    tsv := ?_
    best := ?_
    quorum := ?_
    coll := ?_
    count := ?_ }
  · intro c v ha hm; rw [hts, hval]; exact hS.wpTs c v ha (by rwa [hmode] at hm)
  · intro c v ha hm p hp w hw hcv
    rw [hmode] at hm; rw [hcov] at hcv
    rcases (mem_upd_pend _ _ _ _ _).1 hp with hp | ⟨rfl, rfl⟩
    · exact hS.fresh c v ha hm p hp w hw hcv
    · simp only [LOp.write.injEq] at hw
      obtain ⟨h1, h2⟩ := hS.wpTs _ v ha hm
      rw [← hw, h1, h2]
  · intro e p hp w hw
    rw [hts]
    rcases (mem_upd_pend _ _ _ _ _).1 hp with hp | ⟨rfl, rfl⟩
    · exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
    · simp only [LOp.write.injEq] at hw
      exact ⟨hOK _ (hw ▸ hS.tsv e), by rw [← hw]⟩
  · intro e; rw [hts, hval]; exact hOK _ (hS.tsv e)
  · intro e he; rw [hbest]; rw [hmode] at he; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b' hb' => hP _ b' (hQP b' hb')⟩
  · intro e o lv hop hc
    rw [hmode] at hc
    rcases hS.coll e o lv hop hc with h0 | ⟨Q, hQ, hQP, hQC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b' hb' => hP _ b' (hQP b' hb'), by rw [hgot, hbest]; exact hQC⟩
  · intro c v ha hm
    rw [hmode] at hm
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (hwr c) rfl hU]
    have hU' : ∀ e, U (X'.loc e) = U (X.loc e) := hU
    simp only [hU']
    exact hS.count c v ha hm

/-- A step triggering a low-level read. -/
lemma rinv_trigR {X : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) (d : C) (b : B) :
    RInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with rq := (X.loc d).rq.erase b },
               pend := update X.pend d (X.pend d ++ [POp.mk (X.cnt d) b .read]),
               cnt := update X.cnt d (X.cnt d + 1) } σ := by
  set l' : Loc B V := { X.loc d with rq := (X.loc d).rq.erase b }
  refine rinv_congr δ f R v₀ Wr hS rfl rfl rfl (fun e => ⟨upd_field Loc.ts X.loc d l' rfl e,
    upd_field Loc.val X.loc d l' rfl e, upd_field Loc.pw X.loc d l' rfl e,
    upd_field Loc.cov X.loc d l' rfl e, upd_field Loc.wr X.loc d l' rfl e,
    upd_field Loc.q X.loc d l' rfl e, upd_field Loc.mode X.loc d l' rfl e⟩) ?_ ?_ ?_
  · intro e p hp hw
    rcases (mem_upd_pend _ _ _ _ _).1 hp with hp | ⟨rfl, rfl⟩
    · exact hp
    · exact absurd hw (by simp)
  · intro e he
    simp only [upd_field Loc.best X.loc d l' rfl e]
    simp only [upd_field Loc.mode X.loc d l' rfl e] at he
    exact hS.best e he
  · intro e lv Q _ _ hC hge
    simp only [upd_field Loc.best X.loc d l' rfl e]
    simp only [upd_field Loc.got X.loc d l' rfl e] at hge
    exact hC hge

/-- Response to a low-level read on `b` (line 28). -/
lemma rinv_respRead {X : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) (d : C) (b : B)
    (P' : List (POp B (ℕ × V))) (hP' : ∀ p ∈ P', p ∈ X.pend d) :
    RInv δ f R v₀ Wr
      { X with pend := update X.pend d P',
               loc := update X.loc d (recvRead (X.loc d) b (X.val b)) } σ := by
  set l' := recvRead (X.loc d) b (X.val b)
  have hr : l'.ts = (X.loc d).ts ∧ l'.val = (X.loc d).val ∧ l'.pw = (X.loc d).pw ∧
      l'.cov = (X.loc d).cov ∧ l'.wr = (X.loc d).wr ∧ l'.q = (X.loc d).q ∧
      l'.mode = (X.loc d).mode := by
    simp only [l', recvRead]; split_ifs <;> simp
  refine rinv_congr δ f R v₀ Wr hS rfl rfl rfl (fun e => ⟨upd_field Loc.ts X.loc d l' hr.1 e,
    upd_field Loc.val X.loc d l' hr.2.1 e, upd_field Loc.pw X.loc d l' hr.2.2.1 e,
    upd_field Loc.cov X.loc d l' hr.2.2.2.1 e, upd_field Loc.wr X.loc d l' hr.2.2.2.2.1 e,
    upd_field Loc.q X.loc d l' hr.2.2.2.2.2.1 e,
    upd_field Loc.mode X.loc d l' hr.2.2.2.2.2.2 e⟩) ?_ ?_ ?_
  · intro e p hp _
    by_cases he : e = d
    · subst he; simp only [update_self] at hp; exact hP' p hp
    · simpa [update_of_ne he] using hp
  · intro e he
    by_cases hed : e = d
    · subst hed
      simp only [update_self] at he ⊢
      have hm : (X.loc e).mode.isColl := by rw [← hr.2.2.2.2.2.2]; exact he
      simp only [l', recvRead, hm, ite_true]
      split_ifs
      · exact hS.vals b
      · exact hS.best e hm
    · simp only [update_of_ne hed] at he ⊢; exact hS.best e he
  · intro e lv Q hP hm hC hge
    by_cases hed : e = d
    · subst hed
      simp only [update_self] at hge ⊢
      simp only [l', recvRead, hm, ite_true, mem_insert] at hge ⊢
      obtain ⟨b', hb'Q, hb' | hb'⟩ := hge
      · subst hb'
        have := (hP b' hb'Q).1
        split_ifs with h <;> omega
      · have := hC ⟨b', hb'Q, hb'⟩
        split_ifs with h <;> omega
    · simp only [update_of_ne hed] at hge ⊢; exact hC hge

/-- Response to a low-level write `p` on `b` with value `w` (lines 29–34). -/
lemma rinv_respWrite (hL : Layout δ f Wr R) {X : Cf} {σ : HSt C V}
    (hgi : GI f R X) (hS : RInv δ f R v₀ Wr X σ) (d : C)
    (p : POp B (ℕ × V)) (hp : p ∈ X.pend d) (w : ℕ × V) (hw : p.op = .write w)
    (P' : List (POp B (ℕ × V))) (hP' : ∀ x, x ∈ P' ↔ x ∈ X.pend d ∧ x ≠ p) :
    RInv δ f R v₀ Wr
      { X with pend := update X.pend d P',
               loc := update X.loc d (recvWrite (X.loc d) p.reg),
               val := update X.val p.reg w } σ := by
  set b := p.reg with hbdef
  set l := X.loc d with hl
  set l' := recvWrite l b with hl'
  set X' : Cf := { X with
      pend := update X.pend d P'
      loc := update X.loc d l'
      val := update X.val b w } with hX'
  have hci := hgi.2 d
  have hbpw : b ∈ l.pw := hci.mem_pw_of hp (by simp [hw])
  have hr : l'.ts = l.ts ∧ l'.val = l.val ∧ l'.mode = l.mode ∧ l'.got = l.got ∧ l'.best = l.best := by
    simp only [l', recvWrite]; split_ifs <;> simp
  have hmode : ∀ e, (X'.loc e).mode = (X.loc e).mode := upd_field Loc.mode X.loc d l' hr.2.2.1
  have hts : ∀ e, (X'.loc e).ts = (X.loc e).ts := upd_field Loc.ts X.loc d l' hr.1
  have hvl : ∀ e, (X'.loc e).val = (X.loc e).val := upd_field Loc.val X.loc d l' hr.2.1
  have hgot : ∀ e, (X'.loc e).got = (X.loc e).got := upd_field Loc.got X.loc d l' hr.2.2.2.1
  have hbest : ∀ e, (X'.loc e).best = (X.loc e).best := upd_field Loc.best X.loc d l' hr.2.2.2.2
  have hWP : WP X → WP X' := fun ⟨e, v, h1, h2⟩ => ⟨e, v, h1, (hmode e).trans h2⟩
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ x := fun x h => h.congr v₀ hWP
  have hpend : ∀ e x, x ∈ X'.pend e → x ∈ X.pend e := by
    intro e x hx
    by_cases he : e = d
    · subst he; simp only [X', update_self] at hx; exact ((hP' x).1 hx).1
    · simpa [X', update_of_ne he] using hx
  have hwOK := hS.pends d p hp w hw
  have hqd : ∀ e b', b' ∈ (X'.loc e).q → b' ∈ (X.loc e).q ∨ (e = d ∧ b' = b) := by
    intro e b' hb'
    by_cases he : e = d
    · subst he
      simp only [X', update_self, l', recvWrite] at hb'
      split_ifs at hb'
      · rcases mem_insert.1 hb' with h | h
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl h
      · exact Or.inl hb'
    · left; simpa [X', update_of_ne he] using hb'
  have hcov : ∀ e, (X'.loc e).cov ⊆ (X.loc e).cov := by
    intro e
    by_cases he : e = d
    · subst he
      simp only [X', update_self, l', recvWrite]
      split_ifs
      · exact erase_subset _ _
      · exact subset_rfl
    · simp [X', update_of_ne he]
  have hP : ∀ T b', Prot X T b' → Prot X' T b' := by
    intro T b' hPb
    refine ⟨?_, fun e => ⟨?_, ?_⟩⟩
    · by_cases hbb : b' = b
      · subst hbb; simp only [X', update_self]
        exact (hPb.2 d).1 p hp rfl w hw
      · simp only [X', update_of_ne hbb]; exact hPb.1
    · intro x hx hxb w' hxw
      exact (hPb.2 e).1 x (hpend e x hx) hxb w' hxw
    · intro hq
      rw [hts]
      rcases hqd e b' hq with hq | ⟨rfl, rfl⟩
      · exact (hPb.2 e).2 hq
      · exact ((hPb.2 e).1 p hp rfl w hw).trans hwOK.2
  refine { hS with
    wpTs := ?_
    fresh := ?_
    vals := ?_
    pends := ?_
    tsv := ?_
    best := ?_
    quorum := ?_
    coll := ?_
    count := ?_ }
  · intro c v ha hm; rw [hts, hvl]; exact hS.wpTs c v ha (by rwa [hmode] at hm)
  · -- fresh
    intro c v ha hm x hx w' hxw hcv
    rw [hmode] at hm
    have hx0 := hpend c x hx
    by_cases hxc : x.reg ∈ (X.loc c).cov
    · -- then `c = d`, `x.reg = b` and the erased `b` was `x.reg`: impossible
      exfalso
      by_cases he : c = d
      · subst he
        simp only [X', update_self, l', recvWrite] at hcv
        split_ifs at hcv with hbc
        · have hxb : x.reg = b := by
            by_contra hne; exact hcv (mem_erase.2 ⟨hne, hxc⟩)
          have := hci.uniq x hx0 p hp (by simp [hxw]) (by simp [hw]) hxb
          exact ((hP' x).1 (by simpa [X'] using hx)).2 this
        · exact hcv hxc
      · exact hcv (by simpa [X', update_of_ne he] using hxc)
    · exact hS.fresh c v ha hm x hx0 w' hxw hxc
  · intro b'
    by_cases hb' : b' = b
    · subst hb'; simp only [X', update_self]; exact hOK _ hwOK.1
    · simp only [X', update_of_ne hb']; exact hOK _ (hS.vals b')
  · intro e x hx w' hxw
    rw [hts]
    exact ⟨hOK _ (hS.pends e x (hpend e x hx) w' hxw).1, (hS.pends e x (hpend e x hx) w' hxw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he; rw [hbest]; rw [hmode] at he; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b' hb' => hP _ b' (hQP b' hb')⟩
  · intro e o lv hop hc
    rw [hmode] at hc
    rcases hS.coll e o lv hop hc with h0 | ⟨Q, hQ, hQP, hQC⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b' hb' => hP _ b' (hQP b' hb'), by rw [hgot, hbest]; exact hQC⟩
  · -- count
    intro c v ha hm
    rw [hmode] at hm
    have hcount := hS.count c v ha hm
    set N := Nb Wr R c with hN
    set x : ℕ × V := (σ.done + 1, v) with hx
    have hUd := U_recvWrite f hci hbpw
    have hUe : ∀ e, e ≠ d → U (X'.loc e) = U (X.loc e) := by
      intro e he; simp [X', update_of_ne he]
    have hUsub : ∀ e, U (X'.loc e) ⊆ U (X.loc e) := by
      intro e
      by_cases he : e = d
      · subst he
        simp only [X', update_self]
        by_cases hc : b ∈ l.cov
        · rw [hUd.1 hc]
        · rw [hUd.2 hc]; exact erase_subset _ _
      · rw [hUe e he]
    have hwr : (X'.loc c).wr ⊆ insert b (X.loc c).wr := by
      by_cases he : c = d
      · subst he
        simp only [X', update_self, l', recvWrite]
        split_ifs
        · exact subset_insert _ _
        · exact subset_rfl
      · simp [X', update_of_ne he, subset_insert]
    -- membership in `Sp` of registers other than `b` is unchanged
    have hSp : Sp R Wr X' c x ⊆ insert b (Sp R Wr X c x) := by
      intro b' hb'
      by_cases hbb : b' = b
      · exact hbb ▸ mem_insert_self _ _
      apply mem_insert_of_mem
      simp only [Sp, mem_filter] at hb' ⊢
      obtain ⟨h1, h2, h3⟩ := hb'
      refine ⟨(mem_insert.1 (hwr h1)).resolve_left hbb, ?_, fun e he => ?_⟩
      · simpa [X', update_of_ne hbb] using h2
      · intro hU
        apply h3 e he
        by_cases hed : e = d
        · subst hed
          simp only [X', update_self]
          by_cases hc : b ∈ l.cov
          · rw [hUd.1 hc]; exact hU
          · rw [hUd.2 hc]; exact mem_erase.2 ⟨hbb, hU⟩
        · rw [hUe e hed]; exact hU
    have hsum : ∑ e ∈ N, #(U (X'.loc e)) ≤ ∑ e ∈ N, #(U (X.loc e)) :=
      sum_le_sum fun e _ => card_le_card (hUsub e)
    by_cases hbS : b ∈ Sp R Wr X' c x
    · -- the register `b` became spoiled: `d ∈ N` released it
      simp only [Sp, mem_filter] at hbS
      obtain ⟨hbw, hbv, hbU⟩ := hbS
      have hdc : d ≠ c := by
        rintro rfl
        simp only [X', update_self, l', recvWrite] at hbw hbv
        split_ifs at hbw with hc
        · exact disjoint_left.1 hci.dpw hbpw hbw
        · exact hbv (hS.fresh _ v ha hm p hp w hw hc)
      have hbwc : b ∈ (X.loc c).wr := by simpa [X', update_of_ne hdc.symm] using hbw
      have hdN : d ∈ N := by
        have hbd : b ∈ R d := (hgi.2 d).pw_sub hbpw
        have hbc : b ∈ R c := (hgi.2 c).wr_sub hbwc
        have hdW : d ∈ Wr := by
          by_contra hdW; rw [hL.out d hdW] at hbd; simp at hbd
        simp only [N, Nb, mem_filter]
        exact ⟨hdW, hdc, fun hdis => disjoint_left.1 hdis hbd hbc⟩
      have hnc : b ∉ l.cov := by
        intro hc
        apply hbU d hdN
        simp only [X', update_self]; rw [hUd.1 hc]; exact mem_union_left _ hbpw
      have hdU : #(U (X'.loc d)) + 1 = #(U (X.loc d)) := by
        simp only [X', update_self]
        have hbU : b ∈ U (X.loc d) := mem_union_left _ hbpw
        rw [hUd.2 hnc, card_erase_of_mem hbU]
        have := card_pos.2 ⟨b, hbU⟩
        omega
      have hsum' : ∑ e ∈ N, #(U (X'.loc e)) + 1 = ∑ e ∈ N, #(U (X.loc e)) := by
        rw [← add_sum_erase _ _ hdN, ← add_sum_erase _ _ hdN, add_right_comm, hdU]
        congr 1
        exact sum_congr rfl fun e he => by rw [hUe e (ne_of_mem_erase he)]
      have := card_le_card hSp
      have := card_insert_le b (Sp R Wr X c x)
      omega
    · have hsub : Sp R Wr X' c x ⊆ Sp R Wr X c x := by
        intro b' hb'
        rcases mem_insert.1 (hSp hb') with h | h
        · exact absurd (h ▸ hb') hbS
        · exact h
      have := card_le_card hsub
      omega


/-- Lemma 7 for a collect: a complete collect has a maximum timestamp at least the number of
writes completed when its operation was invoked. -/
lemma rcollect_ge {X : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) (d : C) (o : HOp V) (lv : ℕ)
    (hop : σ.op d = some (o, lv)) (hc : (X.loc d).mode.isColl) (hdone : Done δ f (X.loc d).got) :
    lv ≤ (X.loc d).best.1 := by
  rcases hS.coll d o lv hop hc with h0 | ⟨Q, hQ, -, hC⟩
  · omega
  apply hC
  unfold Done at hdone
  have hle : #(Q.image δ) ≤ Fintype.card S := card_le_univ _
  obtain ⟨s, hs⟩ := inter_nonempty_of_card_lt_card_add_card (subset_univ (Q.image δ))
    (subset_univ (univ.filter fun s => ∀ b, δ b = s → b ∈ (X.loc d).got))
    (by rw [card_univ]; omega)
  obtain ⟨hs1, hs2⟩ := mem_inter.1 hs
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hs1
  exact ⟨b, hb, (mem_filter.1 hs2).2 b rfl⟩

lemma valOf_append (wv : List V) (v : V) {t : ℕ} (ht : t ≤ wv.length) :
    valOf v₀ (wv ++ [v]) t = valOf v₀ wv t := by
  rcases t with _ | t
  · rfl
  · simp only [valOf, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]

lemma valOf_last (wv : List V) (v : V) : valOf v₀ (wv ++ [v]) (wv.length + 1) = v := by
  simp [valOf]

/-- The write values after an invocation. -/
def wvNext (wv : List V) : HOp V → List V
  | .write v => wv ++ [v]
  | .read => wv

lemma op_of_cur {X : Cf} {σ : HSt C V} (hS : RInv δ f R v₀ Wr X σ) {d : C} {o : HOp V}
    (h : X.cur d = some o) : ∃ lv, σ.op d = some (o, lv) := by
  rw [hS.cur d] at h
  rcases hop : σ.op d with _ | ⟨o', lv⟩
  · simp [hop] at h
  · simp only [hop, Option.map_some, Option.some.injEq] at h
    exact ⟨lv, by rw [h]⟩

/-- An accepted invocation. -/
lemma rinv_inv {X : Cf} {σ : HSt C V} (hgi : GI f R X) (hS : RInv δ f R v₀ Wr X σ) (d : C)
    (o : HOp V) (hcur : X.cur d = none) (hws : isW o = true → σ.wpend = false) :
    RInv δ f R v₀ Wr
      { X with loc := update X.loc d ((alg δ f R v₀).invoke d o (X.loc d)),
               cur := update X.cur d (some o),
               hist := X.hist ++ [.inv d o] } (hstep v₀ σ (.inv d o)) := by
  have hidle : (X.loc d).mode = .idle := ((hgi.2 d).mode.none_iff).1 hcur
  set l' := (alg δ f R v₀).invoke d o (X.loc d)
  have hl' : l' = startCollect v₀ (match o with | .read => .rd | .write v => .wc v) (X.loc d) := by
    simp only [l', alg, hidle]; rcases o <;> rfl
  have hf : l'.ts = (X.loc d).ts ∧ l'.val = (X.loc d).val ∧ l'.pw = (X.loc d).pw ∧
      l'.cov = (X.loc d).cov ∧ l'.wr = (X.loc d).wr ∧ l'.q = (X.loc d).q ∧ l'.got = ∅ ∧
      l'.best = (0, v₀) ∧ l'.mode ≠ .wp ∧ l'.mode.isColl := by
    rw [hl']; rcases o <;> simp [startCollect]
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d (some o)
      hist := X.hist ++ [.inv d o] }
  set σ' := hstep v₀ σ (.inv d o)
  have hσ'wv : σ'.wv = wvNext σ.wv o := by rcases o <;> rfl
  have hσ'done : σ'.done = σ.done := rfl
  have hσ'op : σ'.op = update σ.op d (some (o, σ.done)) := rfl
  have hts := upd_field Loc.ts X.loc d l' hf.1
  have hvl := upd_field Loc.val X.loc d l' hf.2.1
  have hq := upd_field Loc.q X.loc d l' hf.2.2.2.2.2.1
  have hcov := upd_field Loc.cov X.loc d l' hf.2.2.2.1
  have hwr := upd_field Loc.wr X.loc d l' hf.2.2.2.2.1
  have hU := upd_field U X.loc d l' (by simp only [U, hf.2.2.1, hf.2.2.2.2.2.1])
  have hothers : ∀ e, e ≠ d → X'.loc e = X.loc e := fun e he => by simp [X', update_of_ne he]
  have hcur' : ∀ e, e ≠ d → X'.cur e = X.cur e := fun e he => by simp [X', update_of_ne he]
  -- writes pending in `X'` other than `d`'s are pending in `X`
  have hwX : ∀ e v, e ≠ d → X'.cur e = some (.write v) → X.cur e = some (.write v) :=
    fun e v he h => by rwa [hcur' e he] at h
  have hnoW : (∃ e v, X.cur e = some (.write v)) → isW o = false := by
    intro h
    by_contra hw
    simp only [Bool.not_eq_false] at hw
    have := hws hw
    rw [← Bool.not_eq_true, hS.wpend] at this
    exact this h
  have hWP : WP X → WP X' := by
    rintro ⟨e, v, h1, h2⟩
    have hed : e ≠ d := by rintro rfl; rw [hcur] at h1; cases h1
    exact ⟨e, v, by rw [hcur' e hed]; exact h1, by rw [hothers e hed]; exact h2⟩
  have hWP' : WP X' → WP X := by
    rintro ⟨e, v, h1, h2⟩
    have hed : e ≠ d := by rintro rfl; simp only [X', update_self] at h2; exact hf.2.2.2.2.2.2.2.2.1 h2
    exact ⟨e, v, hwX e v hed h1, by rw [← hothers e hed]; exact h2⟩
  have hwvle : ∀ t, t ≤ σ.wv.length → valOf v₀ σ'.wv t = valOf v₀ σ.wv t := by
    intro t ht; rw [hσ'wv]; rcases o with _ | v
    · rfl
    · exact valOf_append v₀ _ _ ht
  have hlen : σ.done ≤ σ.wv.length := by
    by_cases h : ∃ e v, X.cur e = some (.write v)
    · obtain ⟨e, v, h⟩ := h; have := (hS.wlen e v h).1; omega
    · push Not at h; rw [hS.wnone h]
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ' x := by
    rintro x ⟨h1, h2 | ⟨h2, h3⟩⟩
    · exact ⟨by rw [hwvle _ (h2.trans hlen)]; exact h1, Or.inl h2⟩
    · obtain ⟨e, v, he, -⟩ := id h3
      have hwo := hnoW ⟨e, v, he⟩
      have hlen' := (hS.wlen e v he).1
      exact ⟨by rw [hwvle _ (by omega)]; exact h1, Or.inr ⟨h2, hWP h3⟩⟩
  refine ⟨hS.reg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X', hσ'op]
    · rw [hcur' e hed, hS.cur e, hσ'op, update_of_ne hed]
  · intro e o' h
    by_cases hed : e = d
    · subst hed; simp only [X', update_self, Option.some.injEq] at h; subst h; simp [X']
    · rw [hcur' e hed] at h; exact List.mem_append_left _ (hS.inHist e o' h)
  · intro e o' lv h
    by_cases hed : e = d
    · subst hed; simp only [hσ'op, update_self, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨le_rfl, fun _ => rfl⟩
    · rw [hσ'op, update_of_ne hed] at h; exact hS.lvl e o' lv h
  · intro e v h
    by_cases hed : e = d
    · subst hed; simp only [X', update_self, Option.some.injEq] at h; subst h
      have hn : ∀ e v, X.cur e ≠ some (.write v) := by
        intro e' v' h'
        have := hnoW ⟨e', v', h'⟩; simp [isW] at this
      have hl := hS.wnone hn
      rw [hσ'wv, hσ'done]
      exact ⟨by simp [wvNext, hl], by rw [← hl]; exact valOf_last v₀ _ _⟩
    · have h0 := hwX e v hed h
      have hwo := hnoW ⟨e, v, h0⟩
      have := hS.wlen e v h0
      rcases o with _ | v'
      · exact this
      · simp [isW] at hwo
  · intro hn
    have hd : isW o = false := by
      rcases o with _ | v
      · rfl
      · exact absurd (by simp [X']) (hn d v)
    have : ∀ e v, X.cur e ≠ some (.write v) := by
      intro e v h
      by_cases hed : e = d
      · subst hed; rw [hcur] at h; cases h
      · exact hn e v (by rw [hcur' e hed]; exact h)
    rw [hσ'wv, hσ'done]
    rcases o with _ | v
    · exact hS.wnone this
    · simp [isW] at hd
  · rcases o with _ | v
    · show σ.wpend = true ↔ _
      rw [hS.wpend]
      constructor
      · rintro ⟨e, v, h⟩
        have hed : e ≠ d := by rintro rfl; rw [hcur] at h; cases h
        exact ⟨e, v, by rw [hcur' e hed]; exact h⟩
      · rintro ⟨e, v, h⟩
        have hed : e ≠ d := by rintro rfl; simp [X'] at h
        exact ⟨e, v, hwX e v hed h⟩
    · show true = true ↔ _
      simp only [true_iff]
      exact ⟨d, v, by simp [X']⟩
  · intro e e' v v' h h'
    by_cases hed : e = d
    · by_cases he'd : e' = d
      · rw [hed, he'd]
      · subst hed
        have := hnoW ⟨e', v', hwX e' v' he'd h'⟩
        simp only [X', update_self, Option.some.injEq] at h; subst h; simp [isW] at this
    · by_cases he'd : e' = d
      · subst he'd
        have := hnoW ⟨e, v, hwX e v hed h⟩
        simp only [X', update_self, Option.some.injEq] at h'; subst h'; simp [isW] at this
      · exact hS.wuniq e e' v v' (hwX e v hed h) (hwX e' v' he'd h')
  · intro c v h hm
    have hcd : c ≠ d := by
      rintro rfl; simp only [X', update_self] at hm; exact hf.2.2.2.2.2.2.2.2.1 hm
    rw [hothers c hcd] at hm ⊢
    exact hS.wpTs c v (hwX c v hcd h) hm
  · intro c v h hm p hp w hw hcv
    have hcd : c ≠ d := by
      rintro rfl; simp only [X', update_self] at hm; exact hf.2.2.2.2.2.2.2.2.1 hm
    rw [hothers c hcd] at hm hcv
    exact hS.fresh c v (hwX c v hcd h) hm p hp w hw hcv
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed
      simp only [X', update_self, hf.2.2.2.2.2.2.2.1]
      exact ⟨rfl, Or.inl (Nat.zero_le _)⟩
    · rw [hothers e hed] at he ⊢; exact hOK _ (hS.best e he)
  · have hP : ∀ T b, Prot X T b → Prot X' T b := fun T b h =>
      h.congr rfl hts hq (fun e p hp _ => hp)
    rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb)⟩
  · have hP : ∀ T b, Prot X T b → Prot X' T b := fun T b h =>
      h.congr rfl hts hq (fun e p hp _ => hp)
    intro e o' lv hop hc
    by_cases hed : e = d
    · subst hed
      simp only [hσ'op, update_self, Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨-, rfl⟩ := hop
      rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
      · exact Or.inl h0
      · refine Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb), ?_⟩
        rintro ⟨b, -, hb⟩
        simp only [X', update_self, hf.2.2.2.2.2.2.1] at hb
        simp at hb
    · rw [hσ'op, update_of_ne hed] at hop
      rw [hothers e hed] at hc ⊢
      rcases hS.coll e o' lv hop hc with h0 | ⟨Q, hQ, hQP, hQC⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb), hQC⟩
  · intro c v h hm
    have hcd : c ≠ d := by
      rintro rfl; simp only [X', update_self] at hm; exact hf.2.2.2.2.2.2.2.2.1 hm
    rw [hothers c hcd] at hm
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (by rw [hothers c hcd]) rfl hU]
    have hU' : ∀ e, U (X'.loc e) = U (X.loc e) := hU
    simp only [hU']
    exact hS.count c v (hwX c v hcd h) hm

/-- Return of a read (line 19): the read is regular (Lemma 7, Lemma 8). -/
lemma rinv_retR {X : Cf} {σ : HSt C V} (hgi : GI f R X) (hS : RInv δ f R v₀ Wr X σ) (d : C)
    (hm : (X.loc d).mode = .rd) (hdone : Done δ f (X.loc d).got) :
    RInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with mode := .idle },
               cur := update X.cur d none,
               hist := X.hist ++ [.ret d (X.loc d).best.2] } (hstep v₀ σ (.ret d (X.loc d).best.2)) := by
  have hcur : X.cur d = some .read := by
    have := (hgi.2 d).mode; rw [hm] at this
    rcases h : X.cur d with _ | _ | _ <;> simp_all [ModeOK]
  obtain ⟨lv, hop⟩ := op_of_cur δ f R v₀ Wr hS hcur
  have hge := rcollect_ge δ f R v₀ Wr hS d .read lv hop (by simp [hm]) hdone
  set l' : Loc B V := { X.loc d with mode := .idle }
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d none
      hist := X.hist ++ [.ret d (X.loc d).best.2] }
  set σ' := hstep v₀ σ (.ret d (X.loc d).best.2)
  have hσ' : σ' = { σ with
      op := update σ.op d none
      reg := σ.reg ∧ ∃ t, lv ≤ t ∧ t ≤ σ.wv.length ∧ (X.loc d).best.2 = valOf v₀ σ.wv t } := by
    simp only [σ', hstep, hop]
  have hts := upd_field Loc.ts X.loc d l' rfl
  have hvl := upd_field Loc.val X.loc d l' rfl
  have hq := upd_field Loc.q X.loc d l' rfl
  have hothers : ∀ e, e ≠ d → X'.loc e = X.loc e := fun e he => by simp [X', update_of_ne he]
  have hcur' : ∀ e, e ≠ d → X'.cur e = X.cur e := fun e he => by simp [X', update_of_ne he]
  have hwX : ∀ e v, X'.cur e = some (.write v) → e ≠ d ∧ X.cur e = some (.write v) := by
    intro e v h
    have hed : e ≠ d := by rintro rfl; simp [X'] at h
    exact ⟨hed, by rwa [hcur' e hed] at h⟩
  have hWX : ∀ e v, X.cur e = some (.write v) → e ≠ d ∧ X'.cur e = some (.write v) := by
    intro e v h
    have hed : e ≠ d := by rintro rfl; rw [hcur] at h; cases h
    exact ⟨hed, by rw [hcur' e hed]; exact h⟩
  have hWP : WP X → WP X' := by
    rintro ⟨e, v, h1, h2⟩
    obtain ⟨hed, h1'⟩ := hWX e v h1
    exact ⟨e, v, h1', by rw [hothers e hed]; exact h2⟩
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ x := fun x h => h.congr v₀ hWP
  have hP : ∀ T b, Prot X T b → Prot X' T b := fun T b h =>
    h.congr rfl hts hq (fun e p hp _ => hp)
  rw [hσ']
  refine ⟨⟨hS.reg, (X.loc d).best.1, hge, ?_, (hS.best d (by simp [hm])).1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases (hS.best d (by simp [hm])).2 with h | ⟨h, e, v, he, -⟩
    · by_cases hw : ∃ e v, X.cur e = some (.write v)
      · obtain ⟨e, v, he⟩ := hw; have := (hS.wlen e v he).1; omega
      · push Not at hw; rw [hS.wnone hw]; exact h
    · have := (hS.wlen e v he).1; omega
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X']
    · rw [hcur' e hed, hS.cur e]; dsimp only; rw [update_of_ne hed]
  · intro e o h
    by_cases hed : e = d
    · subst hed; simp [X'] at h
    · rw [hcur' e hed] at h; exact List.mem_append_left _ (hS.inHist e o h)
  · intro e o lv' h
    by_cases hed : e = d
    · subst hed; simp at h
    · dsimp only at h; rw [update_of_ne hed] at h; exact hS.lvl e o lv' h
  · intro e v h; exact hS.wlen e v (hwX e v h).2
  · intro hn; exact hS.wnone fun e v h => hn e v (hWX e v h).2
  · show σ.wpend = true ↔ _
    rw [hS.wpend]
    constructor
    · rintro ⟨e, v, h⟩; exact ⟨e, v, (hWX e v h).2⟩
    · rintro ⟨e, v, h⟩; exact ⟨e, v, (hwX e v h).2⟩
  · intro e e' v v' h h'; exact hS.wuniq e e' v v' (hwX e v h).2 (hwX e' v' h').2
  · intro c v h hm'
    obtain ⟨hcd, h0⟩ := hwX c v h
    rw [hothers c hcd] at hm' ⊢
    exact hS.wpTs c v h0 hm'
  · intro c v h hm' p hp w hw hcv
    obtain ⟨hcd, h0⟩ := hwX c v h
    rw [hothers c hcd] at hm' hcv
    exact hS.fresh c v h0 hm' p hp w hw hcv
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed; simp [X', l'] at he
    · rw [hothers e hed] at he ⊢; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb)⟩
  · intro e o lv' hop' hc
    by_cases hed : e = d
    · subst hed; simp [X', l'] at hc
    · dsimp only at hop'; rw [update_of_ne hed] at hop'
      rw [hothers e hed] at hc ⊢
      rcases hS.coll e o lv' hop' hc with h0 | ⟨Q, hQ, hQP, hQC⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb), hQC⟩
  · intro c v h hm'
    obtain ⟨hcd, h0⟩ := hwX c v h
    rw [hothers c hcd] at hm'
    have hU : ∀ e, U (X'.loc e) = U (X.loc e) := upd_field U X.loc d l' rfl
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (by rw [hothers c hcd]) rfl hU]
    simp only [hU]
    exact hS.count c v h0 hm'

lemma cur_of_wp {X : Cf} (hgi : GI f R X) {e : C} (h : (X.loc e).mode = .wp) :
    ∃ v, X.cur e = some (.write v) := by
  have := (hgi.2 e).mode; rw [h] at this
  rcases hc : X.cur e with _ | _ | v <;> simp_all [ModeOK]

/-- The transition to the writing phase (lines 3–10): the new timestamp is `T + 1` (Lemma 6). -/
lemma rinv_toWp {X : Cf} {σ : HSt C V} (hgi : GI f R X) (hS : RInv δ f R v₀ Wr X σ) (d : C)
    (v : V) (hm : (X.loc d).mode = .wc v) (hdone : Done δ f (X.loc d).got) :
    RInv δ f R v₀ Wr
      { X with
          loc := update X.loc d { X.loc d with
            ts := (X.loc d).best.1 + 1
            val := v
            cov := (X.loc d).pw
            wr := ∅
            q := R d \ (X.loc d).pw
            mode := .wp } } σ := by
  have hcur : X.cur d = some (.write v) := by
    have := (hgi.2 d).mode; rw [hm] at this
    rcases h : X.cur d with _ | _ | v' <;> simp_all [ModeOK]
  obtain ⟨lv, hop⟩ := op_of_cur δ f R v₀ Wr hS hcur
  have hlv : lv = σ.done := (hS.lvl d _ lv hop).2 rfl
  have hge := rcollect_ge δ f R v₀ Wr hS d _ lv hop (by simp [hm]) hdone
  have hnWP : ¬ WP X := by
    rintro ⟨e, v', h1, h2⟩
    have := hS.wuniq e d v' v h1 hcur
    subst this; rw [hm] at h2; cases h2
  have hbest : (X.loc d).best.1 = σ.done := by
    rcases (hS.best d (by simp [hm])).2 with h | ⟨-, h⟩
    · omega
    · exact absurd h hnWP
  have hvv := (hS.wlen d v hcur).2
  set l := X.loc d
  set l' : Loc B V := { l with
      ts := l.best.1 + 1
      val := v
      cov := l.pw
      wr := ∅
      q := R d \ l.pw
      mode := .wp }
  set X' : Cf := { X with loc := update X.loc d l' }
  have hle : ∀ x, OKr v₀ X σ x → x.1 ≤ σ.done := fun x h => by
    rcases h.2 with h | ⟨-, h⟩
    · exact h
    · exact absurd h hnWP
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ x := fun x h => h.congr v₀ fun h' => absurd h' hnWP
  have hl'ts : l'.ts = σ.done + 1 := by simp [l', hbest]
  have hothers : ∀ e, e ≠ d → X'.loc e = X.loc e := fun e he => by simp [X', update_of_ne he]
  have hself : X'.loc d = l' := by simp [X']
  have hpw : ∀ p ∈ X.pend d, ∀ w, p.op = .write w → p.reg ∈ l.pw :=
    fun p hp w hw => (hgi.2 d).mem_pw_of hp (by simp [hw])
  have hP : ∀ T b, T ≤ σ.done → Prot X T b → Prot X' T b := by
    intro T b hT h
    refine ⟨h.1, fun e => ⟨(h.2 e).1, fun hb' => ?_⟩⟩
    by_cases hed : e = d
    · subst hed; rw [hself, hl'ts]; omega
    · rw [hothers e hed] at hb' ⊢; exact (h.2 e).2 hb'
  refine { hS with
    wpTs := ?_
    fresh := ?_
    vals := fun b => hOK _ (hS.vals b)
    pends := ?_
    tsv := ?_
    best := ?_
    quorum := ?_
    coll := ?_
    count := ?_ }
  · intro c v' hc hm'
    have := hS.wuniq c d v' v hc hcur; subst this
    rw [hcur] at hc; simp only [Option.some.injEq, HOp.write.injEq] at hc; subst hc
    rw [hself]; exact ⟨hl'ts, rfl⟩
  · intro c v' hc _ p hp w hw hcv
    have := hS.wuniq c d v' v hc hcur; subst this
    rw [hself] at hcv
    exact absurd (hpw p hp w hw) hcv
  · intro e p hp w hw
    refine ⟨hOK _ (hS.pends e p hp w hw).1, ?_⟩
    by_cases hed : e = d
    · subst hed; rw [hself, hl'ts]
      have := hle _ (hS.pends e p hp w hw).1; omega
    · rw [hothers e hed]; exact (hS.pends e p hp w hw).2
  · intro e
    by_cases hed : e = d
    · subst hed; rw [hself, hl'ts]
      exact ⟨hvv.symm, Or.inr ⟨rfl, e, v, hcur, by rw [hself]⟩⟩
    · rw [hothers e hed]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed; rw [hself] at he; simp [l'] at he
    · rw [hothers e hed] at he ⊢; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hQP⟩
    · exact Or.inl h0
    · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b le_rfl (hQP b hb)⟩
  · intro e o lv' hop' hc
    by_cases hed : e = d
    · subst hed; rw [hself] at hc; simp [l'] at hc
    · rw [hothers e hed] at hc ⊢
      rcases hS.coll e o lv' hop' hc with h0 | ⟨Q, hQ, hQP, hQC⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hS.lvl e o lv' hop').1 (hQP b hb), hQC⟩
  · intro c v' hc hm'
    have := hS.wuniq c d v' v hc hcur; subst this
    rw [hcur] at hc; simp only [Option.some.injEq, HOp.write.injEq] at hc; subst hc
    have hSp : Sp R Wr X' c (σ.done + 1, v) = ∅ := by
      ext b; simp [Sp, hself, l']
    rw [hSp, card_empty, zero_add]
    calc ∑ e ∈ Nb Wr R c, #(U (X'.loc e)) ≤ ∑ e ∈ Nb Wr R c, f := by
          refine sum_le_sum fun e he => ?_
          have hec : e ≠ c := (mem_filter.1 he).2.1
          rw [hothers e hec]
          refine (hgi.2 e).card_U_le fun hwp => hec ?_
          obtain ⟨v'', hv''⟩ := cur_of_wp f R hgi hwp
          exact hS.wuniq e c v'' v hv'' hcur
      _ = #(Nb Wr R c) * f := by rw [sum_const, smul_eq_mul]

/-- Return of a write (line 12): the registers of `wrSet` still holding `(T + 1, v)` and not
covered by other writers form the new protected quorum (Lemma 6, Observation 3). -/
lemma rinv_retW (hL : Layout δ f Wr R) {X : Cf} {σ : HSt C V} (hgi : GI f R X)
    (hS : RInv δ f R v₀ Wr X σ) (d : C) (v : V)
    (hcur : X.cur d = some (.write v)) (hm : (X.loc d).mode = .wp) (hq : (X.loc d).q = ∅)
    (hc : #(R d) ≤ #(X.loc d).wr + f) (hdW : d ∈ Wr) :
    RInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with mode := .idle },
               cur := update X.cur d none,
               hist := X.hist ++ [.ret d (X.loc d).val] } (hstep v₀ σ (.ret d (X.loc d).val)) := by
  classical
  obtain ⟨lv, hop⟩ := op_of_cur δ f R v₀ Wr hS hcur
  have hσ' : hstep v₀ σ (.ret d (X.loc d).val) = { σ with
      op := update σ.op d none
      done := σ.done + 1
      wpend := false } := by
    simp only [hstep, hop]
  rw [hσ']
  have hwl := hS.wlen d v hcur
  set l' : Loc B V := { X.loc d with mode := .idle }
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d none
      hist := X.hist ++ [.ret d (X.loc d).val] }
  have hts := upd_field Loc.ts X.loc d l' rfl
  have hvl := upd_field Loc.val X.loc d l' rfl
  have hqf := upd_field Loc.q X.loc d l' rfl
  have hothers : ∀ e, e ≠ d → X'.loc e = X.loc e := fun e he => by simp [X', update_of_ne he]
  have hcur' : ∀ e, e ≠ d → X'.cur e = X.cur e := fun e he => by simp [X', update_of_ne he]
  have hnoW : ∀ e v', X'.cur e ≠ some (.write v') := by
    intro e v' h
    by_cases hed : e = d
    · subst hed; simp [X'] at h
    · rw [hcur' e hed] at h; exact hed (hS.wuniq e d v' v h hcur)
  set σ' : HSt C V := { σ with op := update σ.op d none, done := σ.done + 1, wpend := false }
  have hOK : ∀ x, OKr v₀ X σ x → OKr v₀ X' σ' x := by
    rintro x ⟨h1, h2 | ⟨h2, -⟩⟩
    · exact ⟨h1, Or.inl (by simp only [σ']; omega)⟩
    · exact ⟨h1, Or.inl (by simp only [σ']; omega)⟩
  have hP : ∀ T b, Prot X T b → Prot X' T b := fun T b h =>
    h.congr rfl hts hqf (fun e p hp _ => hp)
  refine ⟨hS.reg, ?_, ?_, ?_, fun e v' h => absurd h (hnoW e v'), fun _ => by simp only [σ']; omega,
    by simp only [σ', Bool.false_eq_true, false_iff, not_exists]; exact hnoW,
    fun e _ v' _ h => absurd h (hnoW e v'), fun c v' h => absurd h (hnoW c v'),
    fun c v' h => absurd h (hnoW c v'), fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_,
    fun c v' h => absurd h (hnoW c v')⟩
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X', σ']
    · rw [hcur' e hed, hS.cur e]; simp only [σ']; rw [update_of_ne hed]
  · intro e o h
    by_cases hed : e = d
    · subst hed; simp [X'] at h
    · rw [hcur' e hed] at h; exact List.mem_append_left _ (hS.inHist e o h)
  · intro e o lv' h
    by_cases hed : e = d
    · subst hed; simp [σ'] at h
    · simp only [σ'] at h ⊢; rw [update_of_ne hed] at h
      refine ⟨(hS.lvl e o lv' h).1.trans (Nat.le_succ _), fun hw => ?_⟩
      exfalso
      rcases o with _ | v'
      · simp [isW] at hw
      · have hce : X.cur e = some (.write v') := by rw [hS.cur e, h]; rfl
        exact hed (hS.wuniq e d v' v hce hcur)
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed; simp [X', l'] at he
    · rw [hothers e hed] at he ⊢; exact hOK _ (hS.best e he)
  · -- the new quorum
    right
    have hcount := hS.count d v hcur hm
    have hcap := hL.cap d hdW
    obtain ⟨hts_d, hval_d⟩ := hS.wpTs d v hcur hm
    set N := Nb Wr R d
    set W := (X.loc d).wr
    set x : ℕ × V := (σ.done + 1, v)
    set G := W.filter fun b => X.val b = x ∧ ∀ e ∈ N, b ∉ U (X.loc e)
    set I := W.filter fun b => ∃ e ∈ N, b ∈ U (X.loc e)
    have hWsub : W ⊆ G ∪ Sp R Wr X d x ∪ I := by
      intro b hb
      by_cases h1 : ∀ e ∈ N, b ∉ U (X.loc e)
      · by_cases h2 : X.val b = x
        · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hb, h2, h1⟩))
        · simp only [mem_union]; left; right
          simp only [Sp, mem_filter]; exact ⟨hb, h2, h1⟩
      · push Not at h1
        simp only [mem_union]; right
        exact mem_filter.2 ⟨hb, h1⟩
    have hI : #I ≤ ∑ e ∈ N, #(U (X.loc e)) := by
      refine (card_le_card ?_).trans card_biUnion_le
      intro b hb
      obtain ⟨e, he, hbe⟩ := (mem_filter.1 hb).2
      exact mem_biUnion.2 ⟨e, he, hbe⟩
    have hW : #W ≤ #G + #(Sp R Wr X d x) + #I :=
      (card_le_card hWsub).trans ((card_union_le _ _).trans (by
        have := card_union_le G (Sp R Wr X d x); omega))
    have hGsub : G ⊆ R d := (filter_subset _ _).trans (hgi.2 d).wr_sub
    have hGcard : #(G.image δ) = #G :=
      card_image_of_injOn ((hL.inj d).mono (by exact_mod_cast hGsub))
    have hnot : ∀ b ∈ G, ∀ e, b ∉ U (X.loc e) := by
      intro b hb e
      obtain ⟨hbW, -, hbN⟩ := mem_filter.1 hb
      by_cases hed : e = d
      · subst hed
        simp only [U, mem_union, not_or]
        exact ⟨fun h => disjoint_left.1 (hgi.2 e).dpw h hbW,
          fun h => disjoint_left.1 (hgi.2 e).dqw h hbW⟩
      by_cases heN : e ∈ N
      · exact hbN e heN
      have hbR : b ∈ R d := hGsub hb
      intro hbU
      have hbRe : b ∈ R e := by
        simp only [U, mem_union] at hbU
        rcases hbU with h | h
        · exact (hgi.2 e).pw_sub h
        · exact (hgi.2 e).q_sub h
      by_cases heW : e ∈ Wr
      · apply heN
        simp only [N, Nb, mem_filter]
        exact ⟨heW, hed, fun hdis => disjoint_left.1 hdis hbRe hbR⟩
      · rw [hL.out e heW] at hbRe; simp at hbRe
    refine ⟨G, by rw [hGcard]; omega, fun b hb => ⟨?_, fun e => ⟨?_, ?_⟩⟩⟩
    · have := (mem_filter.1 hb).2.1; simp only [X']; rw [this]
    · intro p hp hpb w hw
      exfalso
      have := (hgi.2 e).mem_pw_of hp (by simp [hw])
      rw [hpb] at this
      exact hnot b hb e (mem_union_left _ this)
    · intro hbq
      rw [hqf] at hbq
      exact absurd (mem_union_right _ hbq) (hnot b hb e)
  · intro e o lv' hop' hc'
    by_cases hed : e = d
    · subst hed; simp [X', l'] at hc'
    · simp only [σ'] at hop'; rw [update_of_ne hed] at hop'
      rw [hothers e hed] at hc' ⊢
      rcases hS.coll e o lv' hop' hc' with h0 | ⟨Q, hQ, hQP, hQC⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Q, hQ, fun b hb => hP _ b (hQP b hb), hQC⟩

end Podc.RegisterEmulationSpace.Alg2
