import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Safety

/-!
# Algorithm 2: preservation of the sequential-run invariant, one event at a time
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

lemma upd_field {α : Type*} (F : Loc B V → α) (loc : C → Loc B V) (d : C) (l' : Loc B V)
    (hF : F l' = F (loc d)) (e : C) : F (update loc d l' e) = F (loc e) := by
  by_cases h : e = d
  · rw [h, update_self]; exact hF
  · rw [update_of_ne h]

lemma mem_upd_pend (P : C → List (POp B (ℕ × V))) (d : C) (p₀ : POp B (ℕ × V)) (e : C)
    (p : POp B (ℕ × V)) : p ∈ update P d (P d ++ [p₀]) e ↔ p ∈ P e ∨ (e = d ∧ p = p₀) := by
  by_cases h : e = d
  · subst h; simp
  · simp [h]

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

/-- `Sp` only depends on `wrSet` of `c`, the values and the sets `U`. -/
lemma Sp_congr {X X' : Cf} (c : C) (x : ℕ × V) (hwr : (X'.loc c).wr = (X.loc c).wr)
    (hval : X'.val = X.val) (hU : ∀ e, U (X'.loc e) = U (X.loc e)) :
    Sp R Wr X' c x = Sp R Wr X c x := by
  ext b; simp only [Sp, mem_filter, hwr, hval, hU]

/-- A step triggering a low-level write (line 10 or line 32). -/
lemma sinv_trigW {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)}
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (b : B) (hb : b ∈ (X.loc d).q) :
    SInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with q := (X.loc d).q.erase b,
                                                    pw := insert b (X.loc d).pw },
               pend := update X.pend d (X.pend d ++ [⟨X.cnt d, b, .write ((X.loc d).ts, (X.loc d).val)⟩]),
               cnt := update X.cnt d (X.cnt d + 1) } L a := by
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
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' L a x := fun x h => h.congr v₀ hmode
  refine ⟨hS.hist, hS.corr, hS.cur, ?_, ?_, fun b' => hOK _ (hS.vals b'), ?_, ?_, ?_, ?_, ?_⟩
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
  · rcases hS.quorum with h0 | ⟨Q, hQ, hP, hC⟩
    · exact Or.inl h0
    refine Or.inr ⟨Q, hQ, fun b' hb' => ⟨(hP b' hb').1, fun e => ⟨?_, ?_⟩⟩, ?_⟩
    · intro p hp hpb w hw
      rcases (mem_upd_pend _ _ _ _ _).1 hp with hp | ⟨rfl, rfl⟩
      · exact ((hP b' hb').2 e).1 p hp hpb w hw
      · simp only [LOp.write.injEq] at hw
        rw [← hw]
        exact ((hP b' hb').2 e).2 (hpb ▸ hb)
    · intro hq
      rw [hts]
      by_cases he : e = d
      · subst he
        have hq2 : b' ∈ l.q.erase b := by simpa [X', l'] using hq
        exact ((hP b' hb').2 _).2 (mem_erase.1 hq2).2
      · have hq2 : b' ∈ (X.loc e).q := by simpa [X', update_of_ne he] using hq
        exact ((hP b' hb').2 e).2 hq2
    · intro e he hge
      rw [hmode] at he; rw [hgot] at hge; rw [hbest]
      exact hC e he hge
  · intro c v ha hm
    rw [hmode] at hm
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (hwr c) rfl hU]
    have hU' : ∀ e, U (X'.loc e) = U (X.loc e) := hU
    simp only [hU']
    exact hS.count c v ha hm

/-- Transfer of the invariant along events that change neither values, nor `tsVal`s, nor the
bookkeeping sets, and only remove pending writes. -/
lemma sinv_congr {X X' : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)}
    (hS : SInv δ f R v₀ Wr X L a) (hval : X'.val = X.val) (hcur : X'.cur = X.cur)
    (hhist : X'.hist = X.hist)
    (hloc : ∀ e, (X'.loc e).ts = (X.loc e).ts ∧ (X'.loc e).val = (X.loc e).val ∧
      (X'.loc e).pw = (X.loc e).pw ∧ (X'.loc e).cov = (X.loc e).cov ∧
      (X'.loc e).wr = (X.loc e).wr ∧ (X'.loc e).q = (X.loc e).q ∧ (X'.loc e).mode = (X.loc e).mode)
    (hpw : ∀ e p, p ∈ X'.pend e → p.op.IsWrite → p ∈ X.pend e)
    (hbest : ∀ e, (X'.loc e).mode.isColl → OK v₀ X L a (X'.loc e).best)
    (hcoll : ∀ Q : Finset B, (∀ b ∈ Q, Prot X (wcount L) b) →
      (∀ e, (X.loc e).mode.isColl → (∃ b ∈ Q, b ∈ (X.loc e).got) → wcount L ≤ (X.loc e).best.1) →
      ∀ e, (X'.loc e).mode.isColl → (∃ b ∈ Q, b ∈ (X'.loc e).got) → wcount L ≤ (X'.loc e).best.1) :
    SInv δ f R v₀ Wr X' L a := by
  have hmode : ∀ e, (X'.loc e).mode = (X.loc e).mode := fun e => (hloc e).2.2.2.2.2.2
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' L a x := fun x h => h.congr v₀ hmode
  have hU : ∀ e, U (X'.loc e) = U (X.loc e) := fun e => by
    simp only [U, (hloc e).2.2.1, (hloc e).2.2.2.2.2.1]
  have hw : ∀ e p w, p ∈ X'.pend e → p.op = .write w → p ∈ X.pend e :=
    fun e p w hp hpw' => hpw e p hp (by simp [hpw'])
  refine ⟨hhist ▸ hS.hist, hS.corr, fun e => hcur ▸ hS.cur e, ?_, ?_, ?_, ?_, ?_,
    fun e he => hOK _ (hbest e he), ?_, ?_⟩
  · intro c v ha hm; rw [(hloc c).1, (hloc c).2.1]; exact hS.wpTs c v ha (by rwa [hmode] at hm)
  · intro c v ha hm p hp w hpw' hcv
    rw [hmode] at hm; rw [(hloc c).2.2.2.1] at hcv
    exact hS.fresh c v ha hm p (hw c p w hp hpw') w hpw' hcv
  · intro b; rw [hval]; exact hOK _ (hS.vals b)
  · intro e p hp w hpw'
    rw [(hloc e).1]
    exact ⟨hOK _ (hS.pends e p (hw e p w hp hpw') w hpw').1, (hS.pends e p (hw e p w hp hpw') w hpw').2⟩
  · intro e; rw [(hloc e).1, (hloc e).2.1]; exact hOK _ (hS.tsv e)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hP, hC⟩
    · exact Or.inl h0
    have hP' : ∀ b ∈ Q, Prot X' (wcount L) b := by
      intro b hb
      refine ⟨hval ▸ (hP b hb).1, fun e => ⟨fun p hp hpb w hpw' =>
        ((hP b hb).2 e).1 p (hw e p w hp hpw') hpb w hpw', fun hq => ?_⟩⟩
      rw [(hloc e).1]; rw [(hloc e).2.2.2.2.2.1] at hq
      exact ((hP b hb).2 e).2 hq
    exact Or.inr ⟨Q, hQ, hP', hcoll Q hP hC⟩
  · intro c v ha hm
    rw [hmode] at hm
    rw [Sp_congr R Wr (X := X) (X' := X') c _ (hloc c).2.2.2.2.1 hval hU]
    simp only [hU]
    exact hS.count c v ha hm

/-- A step triggering a low-level read. -/
lemma sinv_trigR {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)}
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (b : B) :
    SInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with rq := (X.loc d).rq.erase b },
               pend := update X.pend d (X.pend d ++ [POp.mk (X.cnt d) b .read]),
               cnt := update X.cnt d (X.cnt d + 1) } L a := by
  set l' : Loc B V := { X.loc d with rq := (X.loc d).rq.erase b }
  refine sinv_congr δ f R v₀ Wr hS rfl rfl rfl (fun e => ⟨upd_field Loc.ts X.loc d l' rfl e,
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
  · intro Q _ hC e he hge
    simp only [upd_field Loc.best X.loc d l' rfl e]
    simp only [upd_field Loc.mode X.loc d l' rfl e] at he
    simp only [upd_field Loc.got X.loc d l' rfl e] at hge
    exact hC e he hge

/-- Response to a low-level read on `b` (line 28). -/
lemma sinv_respRead {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)}
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (b : B) (P' : List (POp B (ℕ × V)))
    (hP' : ∀ p ∈ P', p ∈ X.pend d) :
    SInv δ f R v₀ Wr
      { X with pend := update X.pend d P',
               loc := update X.loc d (recvRead (X.loc d) b (X.val b)) } L a := by
  set l' := recvRead (X.loc d) b (X.val b)
  have hr : l'.ts = (X.loc d).ts ∧ l'.val = (X.loc d).val ∧ l'.pw = (X.loc d).pw ∧
      l'.cov = (X.loc d).cov ∧ l'.wr = (X.loc d).wr ∧ l'.q = (X.loc d).q ∧
      l'.mode = (X.loc d).mode := by
    simp only [l', recvRead]; split_ifs <;> simp
  refine sinv_congr δ f R v₀ Wr hS rfl rfl rfl (fun e => ⟨upd_field Loc.ts X.loc d l' hr.1 e,
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
  · intro Q hP hC e he hge
    by_cases hed : e = d
    · subst hed
      simp only [update_self] at he hge ⊢
      have hm : (X.loc e).mode.isColl := by rw [← hr.2.2.2.2.2.2]; exact he
      simp only [l', recvRead, hm, ite_true, mem_insert] at hge ⊢
      obtain ⟨b', hb'Q, hb' | hb'⟩ := hge
      · subst hb'
        have := (hP b' hb'Q).1
        split_ifs with h <;> omega
      · have := hC e hm ⟨b', hb'Q, hb'⟩
        split_ifs with h <;> omega
    · simp only [update_of_ne hed] at he hge ⊢; exact hC e he hge

lemma U_recvWrite {Rc : Finset B} {l : Loc B V} {P o} (hci : CI Rc f l P o) {b : B} (hb : b ∈ l.pw) :
    (b ∈ l.cov → U (recvWrite l b) = U l) ∧ (b ∉ l.cov → U (recvWrite l b) = (U l).erase b) := by
  have hbq : b ∉ l.q := fun h => disjoint_left.1 hci.dpq hb h
  constructor
  · intro hc
    simp only [U, recvWrite, hc, ite_true]
    ext x; simp only [mem_union, mem_erase, mem_insert]
    by_cases hx : x = b
    · subst hx; simp [hb]
    · simp [hx]
  · intro hc
    simp only [U, recvWrite, hc, ite_false]
    ext x; simp only [mem_union, mem_erase]
    by_cases hx : x = b
    · subst hx; simp [hbq]
    · simp [hx]

/-- Response to a low-level write `p` on `b` with value `w` (lines 29–34). -/
lemma sinv_respWrite (hL : Layout δ f Wr R) {X : Cf} {L : List (C × HOp V × V)}
    {a : Option (C × HOp V)} (hgi : GI f R X) (hS : SInv δ f R v₀ Wr X L a) (d : C)
    (p : POp B (ℕ × V)) (hp : p ∈ X.pend d) (w : ℕ × V) (hw : p.op = .write w)
    (P' : List (POp B (ℕ × V))) (hP' : ∀ x, x ∈ P' ↔ x ∈ X.pend d ∧ x ≠ p) :
    SInv δ f R v₀ Wr
      { X with pend := update X.pend d P',
               loc := update X.loc d (recvWrite (X.loc d) p.reg),
               val := update X.val p.reg w } L a := by
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
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' L a x := fun x h => h.congr v₀ hmode
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
  refine ⟨hS.hist, hS.corr, hS.cur, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- quorum
    rcases hS.quorum with h0 | ⟨Q, hQ, hP, hC⟩
    · exact Or.inl h0
    refine Or.inr ⟨Q, hQ, fun b' hb' => ⟨?_, fun e => ⟨?_, ?_⟩⟩, ?_⟩
    · by_cases hbb : b' = b
      · subst hbb; simp only [X', update_self]
        exact ((hP _ hb').2 d).1 p hp rfl w hw
      · simp only [X', update_of_ne hbb]; exact (hP b' hb').1
    · intro x hx hxb w' hxw
      exact ((hP b' hb').2 e).1 x (hpend e x hx) hxb w' hxw
    · intro hq
      rw [hts]
      rcases hqd e b' hq with hq | ⟨rfl, rfl⟩
      · exact ((hP b' hb').2 e).2 hq
      · exact (((hP _ hb').2 e).1 p hp rfl w hw).trans hwOK.2
    · intro e he hge
      rw [hmode] at he; rw [hgot] at hge; rw [hbest]
      exact hC e he hge
  · -- count
    intro c v ha hm
    rw [hmode] at hm
    have hcount := hS.count c v ha hm
    set N := Nb Wr R c with hN
    set x : ℕ × V := (wcount L + 1, v) with hx
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

/-- Lemma 7 for a collect: a completed collect (in a sequential run, no write in its writing
phase) returns the last written value with its timestamp. -/
lemma collect_result {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)}
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (hc : (X.loc d).mode.isColl)
    (hdone : Done δ f (X.loc d).got) (hHI : ∀ x, ¬ HI X (wcount L) a x) :
    (X.loc d).best = (wcount L, lastVal v₀ L) := by
  have hge : wcount L ≤ (X.loc d).best.1 := by
    rcases hS.quorum with h0 | ⟨Q, hQ, -, hC⟩
    · omega
    apply hC d hc
    unfold Done at hdone
    have hle : #(Q.image δ) ≤ Fintype.card S := card_le_univ _
    obtain ⟨s, hs⟩ := inter_nonempty_of_card_lt_card_add_card (subset_univ (Q.image δ))
      (subset_univ (univ.filter fun s => ∀ b, δ b = s → b ∈ (X.loc d).got))
      (by rw [card_univ]; omega)
    obtain ⟨hs1, hs2⟩ := mem_inter.1 hs
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hs1
    exact ⟨b, hb, (mem_filter.1 hs2).2 b rfl⟩
  rcases hS.best d hc with h | h | h
  · omega
  · exact h
  · exact absurd h (hHI _)

/-- An accepted invocation (only when no operation is pending). -/
lemma sinv_inv {X : Cf} {L : List (C × HOp V × V)} (hgi : GI f R X)
    (hS : SInv δ f R v₀ Wr X L none) (d : C) (o : HOp V) :
    SInv δ f R v₀ Wr
      { X with loc := update X.loc d ((alg δ f R v₀).invoke d o (X.loc d)),
               cur := update X.cur d (some o),
               hist := X.hist ++ [.inv d o] } L (some (d, o)) := by
  have hidle : (X.loc d).mode = .idle := ((hgi.2 d).mode.none_iff).1 (by rw [hS.cur d]; rfl)
  set l' := (alg δ f R v₀).invoke d o (X.loc d)
  have hl' : l' = startCollect v₀ (match o with | .read => .rd | .write v => .wc v) (X.loc d) := by
    simp only [l', alg, hidle]; rcases o <;> rfl
  have hf : l'.ts = (X.loc d).ts ∧ l'.val = (X.loc d).val ∧ l'.pw = (X.loc d).pw ∧
      l'.cov = (X.loc d).cov ∧ l'.wr = (X.loc d).wr ∧ l'.q = (X.loc d).q ∧ l'.got = ∅ ∧
      l'.best = (0, v₀) ∧ l'.mode ≠ .wp := by
    rw [hl']; rcases o <;> simp [startCollect]
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d (some o)
      hist := X.hist ++ [.inv d o] }
  have hts := upd_field Loc.ts X.loc d l' hf.1
  have hvl := upd_field Loc.val X.loc d l' hf.2.1
  have hq := upd_field Loc.q X.loc d l' hf.2.2.2.2.2.1
  have hU := upd_field U X.loc d l' (by simp only [U, hf.2.2.1, hf.2.2.2.2.2.1])
  have hnw : ∀ e, (X'.loc e).mode = .wp → (X.loc e).mode = .wp := by
    intro e he
    by_cases hed : e = d
    · subst hed; simp only [X', update_self] at he; exact absurd he hf.2.2.2.2.2.2.2.2
    · simpa [X', update_of_ne hed] using he
  have hHI : ∀ x, ¬ HI X' (wcount L) (some (d, o)) x := by
    rintro x ⟨c, v, hc, hm, -⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    simp only [X', update_self] at hm
    exact hf.2.2.2.2.2.2.2.2 hm
  have hOK : ∀ x, OK v₀ X L none x → OK v₀ X' L (some (d, o)) x := by
    rintro x (h | h | ⟨c, v, hc, -⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · cases hc
  refine ⟨by simp [X', hS.hist, aPart], hS.corr, ?_, ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X', curOf]
    · simp [X', hS.cur e, curOf, hed]
  · intro c v hc hm; exact absurd ⟨c, v, hc, hm, rfl⟩ (hHI _)
  · intro c v hc hm; exact absurd ⟨c, v, hc, hm, rfl⟩ (hHI _)
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed
      simp only [X', update_self, hf.2.2.2.2.2.2.2.1]
      rcases Nat.eq_zero_or_pos (wcount L) with h0 | h0
      · exact Or.inr (Or.inl (by rw [h0, lastVal_of_wcount_zero v₀ L h0]))
      · exact Or.inl h0
    · simp only [X', update_of_ne hed] at he ⊢; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hP, hC⟩
    · exact Or.inl h0
    refine Or.inr ⟨Q, hQ, fun b hb => ⟨(hP b hb).1, fun e => ⟨((hP b hb).2 e).1, fun hb' => ?_⟩⟩, ?_⟩
    · rw [hts]; rw [hq] at hb'; exact ((hP b hb).2 e).2 hb'
    · intro e he hge
      by_cases hed : e = d
      · subst hed
        simp only [X', update_self, hf.2.2.2.2.2.2.1] at hge
        simp at hge
      · simp only [X', update_of_ne hed] at he hge ⊢; exact hC e he hge
  · intro c v hc hm; exact absurd ⟨c, v, hc, hm, rfl⟩ (hHI _)

lemma curOf_eq_some {a : Option (C × HOp V)} {d : C} {o : HOp V} (h : curOf a d = some o) :
    a = some (d, o) := by
  rcases a with _ | ⟨c, o'⟩
  · simp [curOf] at h
  · simp only [curOf] at h
    split_ifs at h with hdc
    · subst hdc; cases h; rfl

/-- Return of a read (line 19): it returns the value of the last write (Lemma 7, Lemma 8). -/
lemma sinv_retR {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} (hgi : GI f R X)
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (hm : (X.loc d).mode = .rd)
    (hdone : Done δ f (X.loc d).got) :
    SInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with mode := .idle },
               cur := update X.cur d none,
               hist := X.hist ++ [.ret d (X.loc d).best.2] } (L ++ [(d, .read, (X.loc d).best.2)])
      none := by
  have hcur : X.cur d = some .read := by
    have := (hgi.2 d).mode; rw [hm] at this
    rcases h : X.cur d with _ | _ | _ <;> simp_all [ModeOK]
  have ha : a = some (d, .read) := curOf_eq_some (hS.cur d ▸ hcur)
  have hHI : ∀ x, ¬ HI X (wcount L) a x := by
    rintro x ⟨c, v, hc, -⟩; rw [ha] at hc; simp at hc
  have hbest := collect_result δ f R v₀ Wr hS d (by simp [hm]) hdone hHI
  set l' : Loc B V := { X.loc d with mode := .idle }
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d none
      hist := X.hist ++ [.ret d (X.loc d).best.2] }
  have hT : wcount (L ++ [(d, .read, (X.loc d).best.2)]) = wcount L := by simp [wcount_snoc, isW]
  have hu : lastVal v₀ (L ++ [(d, .read, (X.loc d).best.2)]) = lastVal v₀ L := by
    simp [lastVal_snoc]
  have hts := upd_field Loc.ts X.loc d l' rfl
  have hvl := upd_field Loc.val X.loc d l' rfl
  have hq := upd_field Loc.q X.loc d l' rfl
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' (L ++ [(d, .read, (X.loc d).best.2)]) none x := by
    rintro x (h | h | h)
    · exact Or.inl (hT ▸ h)
    · exact Or.inr (Or.inl (by rw [hT, hu]; exact h))
    · exact absurd h (hHI _)
  have hidle : ∀ e, e ≠ d → (X.loc e).mode = .idle := by
    intro e he
    exact ((hgi.2 e).mode.none_iff).1 (by rw [hS.cur e, ha]; simp [curOf, he])
  refine ⟨?_, ?_, ?_, ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_⟩
  · simp [X', hS.hist, ha, aPart, seqHist_snoc]
  · exact seqCorrect_snoc_read v₀ hS.corr d _ (by rw [hbest])
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X', curOf]
    · simp [X', hS.cur e, ha, curOf, hed]
  · intro c v hc; cases hc
  · intro c v hc; cases hc
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed; simp [X', l'] at he
    · simp only [X', update_of_ne hed] at he; rw [hidle e hed] at he; simp at he
  · rw [hT]
    rcases hS.quorum with h0 | ⟨Q, hQ, hP, -⟩
    · exact Or.inl h0
    refine Or.inr ⟨Q, hQ, fun b hb => ⟨(hP b hb).1, fun e => ⟨((hP b hb).2 e).1, fun hb' => ?_⟩⟩, ?_⟩
    · rw [hts]; rw [hq] at hb'; exact ((hP b hb).2 e).2 hb'
    · intro e he
      by_cases hed : e = d
      · subst hed; simp [X', l'] at he
      · simp only [X', update_of_ne hed] at he; rw [hidle e hed] at he; simp at he
  · intro c v hc; cases hc

lemma idle_of_cur {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} (hgi : GI f R X)
    (hS : SInv δ f R v₀ Wr X L a) {d : C} {o : HOp V} (ha : a = some (d, o)) (e : C) (he : e ≠ d) :
    (X.loc e).mode = .idle :=
  ((hgi.2 e).mode.none_iff).1 (by rw [hS.cur e, ha]; simp [curOf, he])

/-- The transition to the writing phase (lines 3–10): the new timestamp is `T + 1`. -/
lemma sinv_toWp {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} (hgi : GI f R X)
    (hS : SInv δ f R v₀ Wr X L a) (d : C) (v : V) (hm : (X.loc d).mode = .wc v)
    (hdone : Done δ f (X.loc d).got) :
    SInv δ f R v₀ Wr
      { X with
          loc := update X.loc d { X.loc d with
            ts := (X.loc d).best.1 + 1
            val := v
            cov := (X.loc d).pw
            wr := ∅
            q := R d \ (X.loc d).pw
            mode := .wp } } L a := by
  have hcur : X.cur d = some (.write v) := by
    have := (hgi.2 d).mode; rw [hm] at this
    rcases h : X.cur d with _ | _ | v' <;> simp_all [ModeOK]
  have ha : a = some (d, .write v) := curOf_eq_some (hS.cur d ▸ hcur)
  have hHI : ∀ x, ¬ HI X (wcount L) a x := by
    rintro x ⟨c, v', hc, hm', -⟩
    rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc
    rw [← hc.1, hm] at hm'; cases hm'
  have hbest := collect_result δ f R v₀ Wr hS d (by simp [hm]) hdone hHI
  have hidle := idle_of_cur δ f R v₀ Wr hgi hS ha
  set l := X.loc d
  set l' : Loc B V := { l with
      ts := l.best.1 + 1
      val := v
      cov := l.pw
      wr := ∅
      q := R d \ l.pw
      mode := .wp }
  set X' : Cf := { X with loc := update X.loc d l' }
  have hle : ∀ x, OK v₀ X L a x → x.1 ≤ wcount L := fun x h =>
    h.le_of_not_wp v₀ (fun c v' hc hm' => by
      rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact absurd (hm'.symm.trans hm) (by simp))
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' L a x := by
    rintro x (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd h (hHI _)
  have hl'ts : l'.ts = wcount L + 1 := by simp [l', hbest]
  have hothers : ∀ e, e ≠ d → X'.loc e = X.loc e := fun e he => by simp [X', update_of_ne he]
  have hself : X'.loc d = l' := by simp [X']
  have hpw : ∀ p ∈ X.pend d, ∀ w, p.op = .write w → p.reg ∈ l.pw :=
    fun p hp w hw => (hgi.2 d).mem_pw_of hp (by simp [hw])
  refine ⟨hS.hist, hS.corr, hS.cur, ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, ?_, ?_, ?_⟩
  · intro c v' hc hm'
    rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq, HOp.write.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [hself]; exact ⟨hl'ts, rfl⟩
  · intro c v' hc _ p hp w hw hcv
    rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
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
      exact Or.inr (Or.inr ⟨e, v, ha, by rw [hself], rfl⟩)
    · rw [hothers e hed]; exact hOK _ (hS.tsv e)
  · intro e he
    by_cases hed : e = d
    · subst hed; rw [hself] at he; simp [l'] at he
    · rw [hothers e hed] at he ⊢; exact hOK _ (hS.best e he)
  · rcases hS.quorum with h0 | ⟨Q, hQ, hP, hC⟩
    · exact Or.inl h0
    refine Or.inr ⟨Q, hQ, fun b hb => ⟨(hP b hb).1, fun e => ⟨((hP b hb).2 e).1, fun hb' => ?_⟩⟩, ?_⟩
    · by_cases hed : e = d
      · subst hed; rw [hself, hl'ts]; omega
      · rw [hothers e hed] at hb' ⊢; exact ((hP b hb).2 e).2 hb'
    · intro e he
      by_cases hed : e = d
      · subst hed; rw [hself] at he; simp [l'] at he
      · rw [hothers e hed] at he ⊢; exact hC e he
  · intro c v' hc hm'
    rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq, HOp.write.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hSp : Sp R Wr X' d (wcount L + 1, v) = ∅ := by
      ext b; simp [Sp, hself, l']
    rw [hSp, card_empty, zero_add]
    calc ∑ e ∈ Nb Wr R d, #(U (X'.loc e)) ≤ ∑ e ∈ Nb Wr R d, f := by
          refine sum_le_sum fun e he => ?_
          have hec : e ≠ d := (mem_filter.1 he).2.1
          rw [hothers e hec]
          exact (hgi.2 e).card_U_le (by rw [hidle e hec]; simp)
      _ = #(Nb Wr R d) * f := by rw [sum_const, smul_eq_mul]

/-- Return of a write (line 12): the registers of `wrSet` still holding `(T + 1, v)` and not
covered by other writers form the new protected quorum (Lemma 6, Observation 3). -/
lemma sinv_retW (hL : Layout δ f Wr R) {X : Cf} {L : List (C × HOp V × V)}
    {a : Option (C × HOp V)} (hgi : GI f R X) (hS : SInv δ f R v₀ Wr X L a) (d : C) (v : V)
    (hcur : X.cur d = some (.write v)) (hm : (X.loc d).mode = .wp) (hq : (X.loc d).q = ∅)
    (hc : #(R d) ≤ #(X.loc d).wr + f) (hdW : d ∈ Wr) :
    SInv δ f R v₀ Wr
      { X with loc := update X.loc d { X.loc d with mode := .idle },
               cur := update X.cur d none,
               hist := X.hist ++ [.ret d (X.loc d).val] } (L ++ [(d, .write v, (X.loc d).val)])
      none := by
  classical
  have ha : a = some (d, .write v) := curOf_eq_some (hS.cur d ▸ hcur)
  obtain ⟨hts_d, hval_d⟩ := hS.wpTs d v ha hm
  have hidle := idle_of_cur δ f R v₀ Wr hgi hS ha
  set l' : Loc B V := { X.loc d with mode := .idle }
  set L' := L ++ [(d, .write v, (X.loc d).val)]
  set X' : Cf := { X with
      loc := update X.loc d l'
      cur := update X.cur d none
      hist := X.hist ++ [.ret d (X.loc d).val] }
  have hT : wcount L' = wcount L + 1 := by simp [L', wcount_snoc, isW]
  have hu : lastVal v₀ L' = v := by simp [L', lastVal_snoc]
  have hts := upd_field Loc.ts X.loc d l' rfl
  have hvl := upd_field Loc.val X.loc d l' rfl
  have hqf := upd_field Loc.q X.loc d l' rfl
  have hpwf := upd_field Loc.pw X.loc d l' rfl
  have hOK : ∀ x, OK v₀ X L a x → OK v₀ X' L' none x := by
    rintro x (h | h | ⟨c, v', hc', -, h⟩)
    · exact Or.inl (by rw [hT]; omega)
    · exact Or.inl (by rw [hT, h]; simp)
    · rw [ha] at hc'; simp only [Option.some.injEq, Prod.mk.injEq, HOp.write.injEq] at hc'
      obtain ⟨-, rfl⟩ := hc'
      exact Or.inr (Or.inl (by rw [hT, hu, h]))
  have hall_idle : ∀ e, ¬ (X'.loc e).mode.isColl := by
    intro e he
    by_cases hed : e = d
    · subst hed; simp [X', l'] at he
    · simp only [X', update_of_ne hed] at he; rw [hidle e hed] at he; simp at he
  refine ⟨?_, ?_, ?_, ?_, ?_, fun b => hOK _ (hS.vals b), ?_, ?_, fun e he => absurd he (hall_idle e),
    ?_, ?_⟩
  · simp [X', L', hS.hist, ha, aPart, seqHist_snoc]
  · exact seqCorrect_snoc_write v₀ hS.corr d v _
  · intro e
    by_cases hed : e = d
    · subst hed; simp [X', curOf]
    · simp [X', hS.cur e, ha, curOf, hed]
  · intro c v hc; cases hc
  · intro c v hc; cases hc
  · intro e p hp w hw
    rw [hts]; exact ⟨hOK _ (hS.pends e p hp w hw).1, (hS.pends e p hp w hw).2⟩
  · intro e; rw [hts, hvl]; exact hOK _ (hS.tsv e)
  · -- the new quorum
    right
    have hcount := hS.count d v ha hm
    have hcap := hL.cap d hdW
    set N := Nb Wr R d
    set W := (X.loc d).wr
    set x : ℕ × V := (wcount L + 1, v)
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
    -- registers of `G` are covered by nobody
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
    refine ⟨G, by rw [hGcard]; omega, fun b hb => ⟨?_, fun e => ⟨?_, ?_⟩⟩, fun e he => absurd he (hall_idle e)⟩
    · rw [hT]; have := (mem_filter.1 hb).2.1; simp only [X'] ; rw [this]
    · intro p hp hpb w hw
      exfalso
      have := (hgi.2 e).mem_pw_of hp (by simp [hw])
      rw [hpb] at this
      exact hnot b hb e (mem_union_left _ this)
    · intro hbq
      rw [hqf] at hbq
      exact absurd (mem_union_right _ hbq) (hnot b hb e)
  · intro c v hc; cases hc

end Podc.RegisterEmulationSpace.Alg2
