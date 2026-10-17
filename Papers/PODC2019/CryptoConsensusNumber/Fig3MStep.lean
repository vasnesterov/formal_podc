import Papers.PODC2019.CryptoConsensusNumber.Fig3MInv

/-!
# Figure 3: the memory invariant is preserved by every step
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ} {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {q : Fin n}

lemma invCnt_congr (C : Cfg μ q₀ k) (q : Fin n) (l' : Loc n Acct) (a : Acct) (r : ℕ)
    (h : Invd l' a r ↔ Invd (C.loc q) a r) :
    (Finset.univ.filter (fun q'' => Invd (Function.update C.loc q l' q'') a r)).card =
      invCnt C a r := by
  unfold invCnt; congr 1; ext q''
  by_cases hq : q'' = q
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

lemma cfg_eq_tau (C : Cfg μ q₀ k) (q : Fin n) (l' : Loc n Acct) (m' : Mem n Acct k) :
    ({ C with loc := Function.update C.loc q l', mem := m' } : Cfg μ q₀ k) =
      ⟨Function.update C.loc q l', Function.update C.pend q (C.pend q), m'⟩ := by
  simp

lemma MInv.of_local (hI : MInv μ C K) (q : Fin n) (l' : Loc n Acct)
    (pd' : Option (ATOp (Fin n) Acct)) (hq : PInv μ K C.mem q l' pd')
    (hinv : ∀ a r, Invd l' a r ↔ Invd (C.loc q) a r) :
    MInv μ (⟨Function.update C.loc q l', Function.update C.pend q pd', C.mem⟩ : Cfg μ q₀ k) K :=
  hI.of_step q l' pd' C.mem hq (fun _ _ => rfl) (fun _ _ _ => rfl) (DecExt.refl _)
    le_rfl (fun t ht _ => ht) hI.kInj hI.kOwn hI.regK
    (fun a r => (hI.cnt a r).trans (invCnt_congr C q l' a r (hinv a r)).symm)
    hI.kcNone hI.decK hI.decUniq

/-! ## Invocations and responses -/

lemma MInv.step_inv_read (hI : MInv μ C K) (h0 : C.pend q = none) (a : Acct) :
    MInv μ { C with
      pend := Function.update C.pend q (some (ATOp.read a))
      loc := Function.update C.loc q { C.loc q with pc := .rscan a } } K := by
  have hp := hI.proc q
  have hidle : (C.loc q).pc = .idle := hp.idle.1 h0
  refine hI.of_local q _ _ ?_ (by simp [Invd, hidle, PC.updFor])
  exact {
    idle := by simp
    pendTx := by simp [PC.tx?]
    pendR := by intro a' h; cases h; rfl
    hist := by rw [hp.hist, hidle]; rfl
    com := hp.com
    asDec := hp.asDec
    asAll := hp.asAll
    upd := by simp
    txP := by simp [PC.tx?]
    reg := by simp [PC.posted]
    notCom := by simp [PC.pre]
    coll := by simp
    loop := by simp [PC.loopC]
    prop := by simp
    kCur := fun t ht htp => Or.inr ((hp.kCur t ht htp).resolve_left (by simp [hidle, PC.tx?]))
    kRnd := fun t ht htp => Or.inr ((hp.kRnd t ht htp).resolve_left (by simp [hidle, PC.tx?]))
    invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hidle, PC.updFor] using h) }

lemma MInv.step_inv_nonowner (hI : MInv μ C K) (h0 : C.pend q = none)
    (o : ATOp (Fin n) Acct) :
    MInv μ { C with
      pend := Function.update C.pend q (some o)
      loc := Function.update C.loc q { C.loc q with pc := .ret (.inl false) } } K := by
  have hp := hI.proc q
  have hidle : (C.loc q).pc = .idle := hp.idle.1 h0
  refine hI.of_local q _ _ ?_ (by simp [Invd, hidle, PC.updFor])
  exact {
    idle := by simp
    pendTx := by simp [PC.tx?]
    pendR := by simp
    hist := by rw [hp.hist, hidle]; rfl
    com := hp.com
    asDec := hp.asDec
    asAll := hp.asAll
    upd := by simp
    txP := by simp [PC.tx?]
    reg := by simp [PC.posted]
    notCom := by simp [PC.pre]
    coll := by simp
    loop := by simp [PC.loopC]
    prop := by simp
    kCur := fun t ht htp => Or.inr ((hp.kCur t ht htp).resolve_left (by simp [hidle, PC.tx?]))
    kRnd := fun t ht htp => Or.inr ((hp.kRnd t ht htp).resolve_left (by simp [hidle, PC.tx?]))
    invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hidle, PC.updFor] using h) }

/-- The tuple created by an owner's transfer invocation. -/
def newTx (l : Loc n Acct) (q : Fin n) (a b : Acct) (x : ℕ) : Tx n Acct := ⟨a, b, x, q, l.rnd a⟩

lemma MInv.newTx_not_mem (hI : MInv μ C K) (h0 : C.pend q = none) (a b : Acct) (x : ℕ) :
    newTx (C.loc q) q a b x ∉ K := by
  intro hm
  have hp := hI.proc q
  have hidle : (C.loc q).pc = .idle := hp.idle.1 h0
  rcases hp.kRnd _ hm rfl with h | h
  · simp [hidle, PC.tx?] at h
  · simp [newTx] at h

lemma MInv.step_inv_owner (hI : MInv μ C K) (h0 : C.pend q = none) (a b : Acct) (x : ℕ)
    (hq : q ∈ μ a) :
    MInv μ { C with
      pend := Function.update C.pend q (some (ATOp.transfer q a b x))
      loc := Function.update C.loc q { C.loc q with pc := .write (newTx (C.loc q) q a b x) } }
      (insert (newTx (C.loc q) q a b x) K) := by
  have hp := hI.proc q
  have hidle : (C.loc q).pc = .idle := hp.idle.1 h0
  set tx := newTx (C.loc q) q a b x with htx
  have hnew : tx ∉ K := hI.newTx_not_mem h0 a b x
  refine hI.of_step q _ _ C.mem ?_ (fun _ _ => rfl) (fun _ _ _ => rfl) (DecExt.refl _)
    (Set.subset_insert _ _) ?_ ?_ ?_ (fun a i t h => ?_)
    (fun a r => (hI.cnt a r).trans (invCnt_congr C q _ a r (by simp [Invd, hidle, PC.updFor])).symm)
    hI.kcNone (fun a r t b h => ?_) hI.decUniq
  · exact {
      idle := by simp
      pendTx := by intro tx' h; simp [PC.tx?] at h; subst h; rfl
      pendR := by simp
      hist := by rw [hp.hist, hidle]; rfl
      com := hp.com
      asDec := hp.asDec
      asAll := hp.asAll
      upd := by simp
      txP := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact ⟨rfl, Set.mem_insert _ _, le_rfl⟩
      reg := by simp [PC.posted]
      notCom := by
        intro tx' h; simp [PC.pre] at h; subst h
        intro hc
        obtain ⟨r, -, b', hd⟩ := (hp.com _ _).1 hc
        exact hnew (hI.decK _ _ _ _ hd).1
      coll := by simp
      loop := by simp [PC.loopC]
      prop := by simp
      kCur := by
        intro t ht htp
        rcases Set.mem_insert_iff.1 ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr ((hp.kCur t ht htp).resolve_left (by simp [hidle, PC.tx?]))
      kRnd := by
        intro t ht htp
        rcases Set.mem_insert_iff.1 ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr ((hp.kRnd t ht htp).resolve_left (by simp [hidle, PC.tx?]))
      invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hidle, PC.updFor] using h) }
  · intro t ht htp
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · exact absurd rfl htp
    · exact ht
  · intro t ht t' ht' h1 h2 h3
    rcases Set.mem_insert_iff.1 ht with rfl | ht <;> rcases Set.mem_insert_iff.1 ht' with rfl | ht'
    · rfl
    · exfalso
      rcases hp.kRnd t' ht' h2.symm with h | h
      · simp [hidle, PC.tx?] at h
      · rw [← h1, ← h3] at h; exact lt_irrefl _ h
    · exfalso
      rcases hp.kRnd t ht h2 with h | h
      · simp [hidle, PC.tx?] at h
      · rw [h1, h3] at h; exact lt_irrefl _ h
    · exact hI.kInj t ht t' ht' h1 h2 h3
  · intro t ht
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · exact hq
    · exact hI.kOwn t ht
  · obtain ⟨h1, h2, h3⟩ := hI.regK a i t h
    exact ⟨Set.mem_insert_of_mem _ h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := hI.decK a r t b h
    exact ⟨Set.mem_insert_of_mem _ h1, h2⟩

lemma MInv.step_ret (hI : MInv μ C K) {r : Bool ⊕ ℕ} (hpc : (C.loc q).pc = .ret r) :
    MInv μ { C with
      pend := Function.update C.pend q none
      loc := Function.update C.loc q { C.loc q with pc := .idle } } K := by
  have hp := hI.proc q
  refine hI.of_local q _ _ ?_ (by simp [Invd, hpc, PC.updFor])
  exact {
    idle := by simp
    pendTx := by simp [PC.tx?]
    pendR := by simp
    hist := by rw [hp.hist, hpc]; rfl
    com := hp.com
    asDec := hp.asDec
    asAll := hp.asAll
    upd := by simp
    txP := by simp [PC.tx?]
    reg := by simp [PC.posted]
    notCom := by simp [PC.pre]
    coll := by simp
    loop := by simp [PC.loopC]
    prop := by simp
    kCur := fun t ht htp => Or.inr ((hp.kCur t ht htp).resolve_left (by simp [hpc, PC.tx?]))
    kRnd := fun t ht htp => Or.inr ((hp.kRnd t ht htp).resolve_left (by simp [hpc, PC.tx?]))
    invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }

/-! ## Internal steps -/

lemma MInv.step_rscan (hI : MInv μ C K) {a : Acct} (hpc : (C.loc q).pc = .rscan a) (v : Bool ⊕ ℕ) :
    MInv μ { C with loc := Function.update C.loc q { C.loc q with pc := .ret v } } K := by
  have hp := hI.proc q
  have e := cfg_eq_tau C q { C.loc q with pc := .ret v } C.mem
  simp only at e; rw [e]
  refine hI.of_local q _ _ ?_ (by simp [Invd, hpc, PC.updFor])
  exact {
    idle := by simp only [Function.update_self]; rw [hp.idle, hpc]; simp
    pendTx := by simp [PC.tx?]
    pendR := by simp
    hist := by rw [hp.hist, hpc]; rfl
    com := hp.com
    asDec := hp.asDec
    asAll := hp.asAll
    upd := by simp
    txP := by simp [PC.tx?]
    reg := by simp [PC.posted]
    notCom := by simp [PC.pre]
    coll := by simp
    loop := by simp [PC.loopC]
    prop := by simp
    kCur := fun t ht htp => Or.inr ((hp.kCur t ht htp).resolve_left (by simp [hpc, PC.tx?]))
    kRnd := fun t ht htp => Or.inr ((hp.kRnd t ht htp).resolve_left (by simp [hpc, PC.tx?]))
    invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }

lemma MInv.step_write (hI : MInv μ C K) {tx : Tx n Acct} (hpc : (C.loc q).pc = .write tx) :
    MInv μ { C with
      mem := Function.update C.mem (.inr (.inl (tx.a, q))) (some tx : Option (Tx n Acct)),
      loc := Function.update C.loc q { C.loc q with pc := .coll tx ⟨0, q.pos⟩ ∅ } } K := by
  have hp := hI.proc q
  obtain ⟨htxp, htxK, -⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  set m' : Mem n Acct k := Function.update C.mem (.inr (.inl (tx.a, q))) (some tx : Option (Tx n Acct))
  have e := cfg_eq_tau C q { C.loc q with pc := .coll tx ⟨0, q.pos⟩ ∅ } m'
  simp only at e; rw [e]
  have hDec : ∀ a r, Dec m' a r = Dec C.mem a r := fun a r => Dec_update_Reg _ _ a r
  have hASq : AS m' = AS C.mem := AS_update_inr _ _
  refine hI.of_step q { C.loc q with pc := .coll tx ⟨0, q.pos⟩ ∅ } _ m' ?_
    (fun _ _ => congrFun (AS_update_inr _ _) _) (fun q' hq' a => ?_)
    (fun a r d h => by rw [hDec]; exact h)
    le_rfl (fun t ht _ => ht) hI.kInj hI.kOwn (fun a i t h => ?_)
    (fun a r => by
      rw [KC_update_Reg]
      exact (hI.cnt a r).trans (invCnt_congr C q _ a r (by simp [Invd, hpc, PC.updFor])).symm)
    (fun a r => by rw [hDec, KC_update_Reg]; exact hI.kcNone a r)
    (fun a r t b h => by rw [hDec] at h; exact hI.decK a r t b h)
    (fun a r r' t b b' h h' => by rw [hDec] at h h'; exact hI.decUniq a r r' t b b' h h')
  · exact {
      idle := by simp only [Function.update_self]; rw [hp.idle, hpc]; simp
      pendTx := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.pendTx _ (by simp [hpc, PC.tx?])
      pendR := by simp
      hist := by rw [hASq, hp.hist, hpc]; rfl
      com := by intro a t; simp only [hDec]; exact hp.com a t
      asDec := by intro t b; rw [hASq]; simp only [hDec]; exact hp.asDec t b
      asAll := by intro a r; rw [hASq]; simp only [hDec]; exact hp.asAll a r
      upd := by simp
      txP := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.txP _ (by simp [hpc, PC.tx?])
      reg := by
        intro tx' h; simp [PC.posted] at h; subst h
        rw [Reg_update_Reg]; simp [htxp]
      notCom := by
        intro tx' h; simp [PC.pre] at h; subst h
        exact hp.notCom _ (by simp [hpc, PC.pre])
      coll := by
        intro tx' i acc h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨by simp, fun h => by simp at h⟩
      loop := by simp [PC.loopC]
      prop := by simp
      kCur := fun t ht htp => by
        rcases hp.kCur t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      kRnd := fun t ht htp => by
        rcases hp.kRnd t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }
  · rw [Reg_update_Reg, ite_eq_right]; intro h; simp at h; exact hq' h.2
  · rw [Reg_update_Reg] at h
    split_ifs at h with hai
    · cases h; simp at hai; obtain ⟨rfl, rfl⟩ := hai; exact ⟨htxK, rfl, htxp⟩
    · exact hI.regK a i t h

lemma MInv.coll_last (hI : MInv μ C K) {tx : Tx n Acct} {i : Fin n} {acc : Finset (Tx n Acct)}
    (hpc : (C.loc q).pc = .coll tx i acc) (hi : ¬ i.val + 1 < n) :
    tx ∈ (acc ∪ Option.toFinset (Reg C.mem tx.a i)) \ (C.loc q).com tx.a := by
  have hp := hI.proc q
  obtain ⟨htxp, -, -⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  rw [Finset.mem_sdiff]
  refine ⟨?_, hp.notCom tx (by simp [hpc, PC.pre])⟩
  rcases lt_or_eq_of_le (show q.val ≤ i.val by have := q.isLt; omega) with h | h
  · exact Finset.mem_union_left _ ((hp.coll tx i acc hpc).2 h)
  · have hiq : i = q := Fin.ext h.symm
    subst hiq
    rw [hp.reg tx (by simp [hpc, PC.posted])]
    simp

lemma MInv.step_coll (hI : MInv μ C K) {tx : Tx n Acct} {i : Fin n} {acc : Finset (Tx n Acct)}
    (hpc : (C.loc q).pc = .coll tx i acc) :
    MInv μ { C with
      loc := Function.update C.loc q
        (if h : i.val + 1 < n then
          { C.loc q with pc := .coll tx ⟨i.val + 1, h⟩ (acc ∪ Option.toFinset (Reg C.mem tx.a i)) }
        else { C.loc q with pc := loopCheck tx ((acc ∪ Option.toFinset (Reg C.mem tx.a i)) \
          (C.loc q).com tx.a) (C.loc q).hist }) } K := by
  have hp := hI.proc q
  obtain ⟨htxp, htxK, htxr⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  obtain ⟨hacc, hown⟩ := hp.coll tx i acc hpc
  have hreg : ∀ t ∈ Option.toFinset (Reg C.mem tx.a i), t ∈ K ∧ t.a = tx.a := by
    intro t ht
    rw [Option.mem_toFinset] at ht
    obtain ⟨h1, h2, -⟩ := hI.regK _ _ _ ht
    exact ⟨h1, h2⟩
  have e := cfg_eq_tau C q (if h : i.val + 1 < n then
          { C.loc q with pc := .coll tx ⟨i.val + 1, h⟩ (acc ∪ Option.toFinset (Reg C.mem tx.a i)) }
        else { C.loc q with pc := loopCheck tx ((acc ∪ Option.toFinset (Reg C.mem tx.a i)) \
          (C.loc q).com tx.a) (C.loc q).hist }) C.mem
  simp only at e; rw [e]
  by_cases hi : i.val + 1 < n
  · simp only [hi, dite_true]
    refine hI.of_local q _ _ ?_ (by simp [Invd, hpc, PC.updFor])
    exact {
      idle := by rw [hp.idle, hpc]; simp
      pendTx := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.pendTx _ (by simp [hpc, PC.tx?])
      pendR := by simp
      hist := by rw [hp.hist, hpc]; rfl
      com := hp.com
      asDec := hp.asDec
      asAll := hp.asAll
      upd := by simp
      txP := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.txP _ (by simp [hpc, PC.tx?])
      reg := by
        intro tx' h; simp [PC.posted] at h; subst h
        exact hp.reg _ (by simp [hpc, PC.posted])
      notCom := by
        intro tx' h; simp [PC.pre] at h; subst h
        exact hp.notCom _ (by simp [hpc, PC.pre])
      coll := by
        intro tx' i' acc' h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨fun t ht => ?_, fun hlt => ?_⟩
        · rcases Finset.mem_union.1 ht with ht | ht
          · exact hacc t ht
          · exact hreg t ht
        · simp only at hlt
          rcases lt_or_eq_of_le (show q.val ≤ i.val by omega) with h | h
          · exact Finset.mem_union_left _ (hown h)
          · have hiq : i = q := Fin.ext h.symm
            subst hiq
            rw [hp.reg tx (by simp [hpc, PC.posted])]
            simp
      loop := by simp [PC.loopC]
      prop := by simp
      kCur := fun t ht htp => by
        rcases hp.kCur t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      kRnd := fun t ht htp => by
        rcases hp.kRnd t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }
  · simp only [hi, dite_false]
    have hmem := hI.coll_last hpc hi
    set c := (acc ∪ Option.toFinset (Reg C.mem tx.a i)) \ (C.loc q).com tx.a with hc
    have hlc : loopCheck tx c (C.loc q).hist = .snap tx c := by simp [loopCheck, hmem]
    rw [hlc]
    refine hI.of_local q _ _ ?_ (by simp [Invd, hpc, PC.updFor])
    exact {
      idle := by rw [hp.idle, hpc]; simp
      pendTx := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.pendTx _ (by simp [hpc, PC.tx?])
      pendR := by simp
      hist := by rw [hp.hist, hpc]; rfl
      com := hp.com
      asDec := hp.asDec
      asAll := hp.asAll
      upd := by simp
      txP := by
        intro tx' h; simp [PC.tx?] at h; subst h
        exact hp.txP _ (by simp [hpc, PC.tx?])
      reg := by
        intro tx' h; simp [PC.posted] at h; subst h
        exact hp.reg _ (by simp [hpc, PC.posted])
      notCom := by simp [PC.pre]
      coll := by simp
      loop := by
        intro tx' c' h; simp [PC.loopC] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨hmem, fun t ht => ?_⟩
        rw [hc, Finset.mem_sdiff] at ht
        rcases Finset.mem_union.1 ht.1 with h | h
        · exact ⟨(hacc t h).1, (hacc t h).2, ht.2⟩
        · exact ⟨(hreg t h).1, (hreg t h).2, ht.2⟩
      prop := by simp
      kCur := fun t ht htp => by
        rcases hp.kCur t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      kRnd := fun t ht htp => by
        rcases hp.kRnd t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h ⊢; exact h
        · exact Or.inr h
      invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }

lemma MInv.step_snap (hI : MInv μ C K) {tx : Tx n Acct} {c : Finset (Tx n Acct)}
    (hpc : (C.loc q).pc = .snap tx c) :
    MInv μ { C with
      loc := Function.update C.loc q
        { C.loc q with pc := .prop tx c (proposal q₀ (oldest c tx) (AS C.mem)) } } K := by
  have hp := hI.proc q
  obtain ⟨hin, hcK⟩ := hp.loop tx c (by simp [hpc, PC.loopC])
  have e := cfg_eq_tau C q { C.loc q with pc := .prop tx c (proposal q₀ (oldest c tx) (AS C.mem)) } C.mem
  simp only at e; rw [e]
  refine hI.of_local q _ _ ?_ (by simp [Invd, hpc, PC.updFor])
  exact {
    idle := by rw [hp.idle, hpc]; simp
    pendTx := by
      intro tx' h; simp [PC.tx?] at h; subst h
      exact hp.pendTx _ (by simp [hpc, PC.tx?])
    pendR := by simp
    hist := by rw [hp.hist, hpc]; rfl
    com := hp.com
    asDec := hp.asDec
    asAll := hp.asAll
    upd := by simp
    txP := by
      intro tx' h; simp [PC.tx?] at h; subst h
      exact hp.txP _ (by simp [hpc, PC.tx?])
    reg := by
      intro tx' h; simp [PC.posted] at h; subst h
      exact hp.reg _ (by simp [hpc, PC.posted])
    notCom := by simp [PC.pre]
    coll := by simp
    loop := by
      intro tx' c' h; simp [PC.loopC] at h; obtain ⟨rfl, rfl⟩ := h
      exact hp.loop _ _ (by simp [hpc, PC.loopC])
    prop := by
      intro tx' c' pr h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact oldest_spec ⟨_, hin⟩ _
    kCur := fun t ht htp => by
      rcases hp.kCur t ht htp with h | h
      · left; simp [hpc, PC.tx?] at h ⊢; exact h
      · exact Or.inr h
    kRnd := fun t ht htp => by
      rcases hp.kRnd t ht htp with h | h
      · left; simp [hpc, PC.tx?] at h ⊢; exact h
      · exact Or.inr h
    invdMem := fun a' r h => hp.invdMem a' r (by simpa [Invd, hpc, PC.updFor] using h) }

/-! ## Proposal and update -/

lemma invCnt_insert (C : Cfg μ q₀ k) (q : Fin n) (l' : Loc n Acct) (a : Acct) (r : ℕ)
    (h1 : Invd l' a r) (h2 : ¬ Invd (C.loc q) a r) :
    (Finset.univ.filter (fun q'' => Invd (Function.update C.loc q l' q'') a r)).card =
      invCnt C a r + 1 := by
  unfold invCnt
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter (fun q'' => Invd (C.loc q'') a r))
    (a := q) (by simp [h2])]
  congr 1; ext q''
  by_cases hq : q'' = q
  · subst hq; simp [h1]
  · simp [Function.update_of_ne hq, hq]

/-- No more than `k` processes invoke a `k`-consensus object, so `propose` never returns `⊥`. -/
lemma MInv.cnt_lt (hI : MInv μ C K) (hk : KShared μ k) {tx : Tx n Acct} {c : Finset (Tx n Acct)}
    {pr : Tx n Acct × Bool} (hpc : (C.loc q).pc = .prop tx c pr) :
    (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 < k := by
  rw [hI.cnt]
  have hp := hI.proc q
  obtain ⟨htxp, htxK, -⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  have hq : q ∈ μ tx.a := htxp ▸ hI.kOwn tx htxK
  have hsub : Finset.univ.filter (fun q' => Invd (C.loc q') tx.a ((C.loc q).rnd tx.a)) ⊆
      (μ tx.a).erase q := by
    intro q' hq'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    rw [Finset.mem_erase]
    refine ⟨?_, (hI.proc q').invdMem _ _ hq'⟩
    rintro rfl
    simp [Invd, hpc, PC.updFor] at hq'
  calc invCnt C tx.a ((C.loc q).rnd tx.a) ≤ ((μ tx.a).erase q).card := Finset.card_le_card hsub
    _ < (μ tx.a).card := Finset.card_erase_lt_of_mem hq
    _ ≤ k := hk tx.a

lemma step_prop' {tx : Tx n Acct} {c : Finset (Tx n Acct)} {pr : Tx n Acct × Bool}
    (h0 : C.pend q ≠ none) (hpc : (C.loc q).pc = .prop tx c pr)
    (hk : (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 < k) :
    (impl μ q₀ k).step C (.tau q) = some { C with
      mem := Function.update C.mem (.inr (.inr (tx.a, (C.loc q).rnd tx.a)))
        (((some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr),
          (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 + 1)) : Option (Tx n Acct × Bool) × ℕ)
      loc := Function.update C.loc q
        { C.loc q with
          pc := .upd tx c (some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr))
          hist := (C.loc q).hist ∪ {(Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr} } } := by
  rw [step_prop tx c pr h0 hpc]
  simp only [hk, ite_true, Option.toFinset_some]

lemma MInv.step_prop (hI : MInv μ C K) {tx : Tx n Acct} {c : Finset (Tx n Acct)}
    {pr : Tx n Acct × Bool} (hpc : (C.loc q).pc = .prop tx c pr) :
    MInv μ { C with
      mem := Function.update C.mem (.inr (.inr (tx.a, (C.loc q).rnd tx.a)))
        (((some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr),
          (KC C.mem tx.a ((C.loc q).rnd tx.a)).2 + 1)) : Option (Tx n Acct × Bool) × ℕ)
      loc := Function.update C.loc q
        { C.loc q with
          pc := .upd tx c (some ((Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr))
          hist := (C.loc q).hist ∪ {(Dec C.mem tx.a ((C.loc q).rnd tx.a)).getD pr} } } K := by
  have hp := hI.proc q
  obtain ⟨htxp, htxK, htxr⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  obtain ⟨hin, hcK⟩ := hp.loop tx c (by simp [hpc, PC.loopC])
  have hprc := (hp.prop tx c pr hpc).1
  set a := tx.a with ha
  set ρ := (C.loc q).rnd a with hρ
  set dn := (Dec C.mem a ρ).getD pr with hdn
  set m' : Mem n Acct k := Function.update C.mem (.inr (.inr (a, ρ)))
    ((some dn, (KC C.mem a ρ).2 + 1) : Option (Tx n Acct × Bool) × ℕ) with hm'
  have hKC : ∀ a' r, KC m' a' r =
      if (a', r) = (a, ρ) then (some dn, (KC C.mem a ρ).2 + 1) else KC C.mem a' r :=
    fun a' r => KC_update_KC _ _ _ _
  have hDec : ∀ a' r, Dec m' a' r = if (a', r) = (a, ρ) then some dn else Dec C.mem a' r := by
    intro a' r; simp only [Dec, hKC]; split_ifs <;> rfl
  have hExt : DecExt C.mem m' := by
    intro a' r d h; rw [hDec]; split_ifs with he
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp [hdn, h]
    · exact h
  have hASm : AS m' = AS C.mem := AS_update_inr _ _
  have hRegm : ∀ a' i, Reg m' a' i = Reg C.mem a' i := fun a' i => Reg_update_KC _ _ _ _
  have hp' := hp.frame (m' := m') (by rw [hASm]) (fun a' => hRegm a' q) hExt le_rfl
    (fun t ht _ => ht)
  have hq : q ∈ μ a := htxp ▸ hI.kOwn tx htxK
  set l' : Loc n Acct := { C.loc q with pc := .upd tx c (some dn), hist := (C.loc q).hist ∪ {dn} }
    with hl'
  have hinvd : ∀ a' r, Invd l' a' r ↔ Invd (C.loc q) a' r ∨ (a' = a ∧ r = ρ) := by
    intro a' r
    simp only [Invd, hl', hpc, PC.updFor, decide_eq_true_eq, Bool.false_eq_true, and_false,
      or_false, hρ]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · subst h2; exact Or.inr ⟨rfl, h1⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · subst h1; exact Or.inr ⟨h2, rfl⟩
  have hnotinv : ¬ Invd (C.loc q) a ρ := by simp [Invd, hpc, PC.updFor, hρ]
  have hdnK : dn.1 ∈ K ∧ dn.1.a = a := by
    cases hd0 : Dec C.mem a ρ with
    | none =>
      have : dn = pr := by simp [hdn, hd0]
      rw [this]; exact ⟨(hcK pr.1 hprc).1, (hcK pr.1 hprc).2.1⟩
    | some d0 =>
      have : dn = d0 := by simp [hdn, hd0]
      rw [this]; exact hI.decK a ρ d0.1 d0.2 hd0
  have e := cfg_eq_tau C q l' m'
  simp only at e; rw [e]
  refine hI.of_step q l' _ m' ?_ (fun _ _ => by rw [hASm]) (fun q' _ a' => hRegm a' q') hExt
    le_rfl (fun t ht _ => ht) hI.kInj hI.kOwn
    (fun a' i t h => hI.regK a' i t (by rwa [hRegm] at h)) ?_ ?_ ?_ ?_
  · exact {
      idle := by
        have := hp'.idle; rw [hpc] at this; simp only [reduceCtorEq, iff_false] at this
        simp [hl', this]
      pendTx := by
        intro tx' h; simp [hl', PC.tx?] at h; subst h
        exact hp'.pendTx _ (by simp [hpc, PC.tx?])
      pendR := by simp [hl']
      hist := by
        have := hp'.hist; rw [hpc] at this
        simp only [hl', this, PC.updDec, Option.toFinset_none, Finset.union_empty,
          Option.toFinset_some]
      com := hp'.com
      asDec := hp'.asDec
      asAll := hp'.asAll
      upd := by
        intro tx' c' d' h; simp only [hl', PC.upd.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨?_, rfl⟩
        rw [hDec]; simp [hl', ← ha, ← hρ]
      txP := by
        intro tx' h; simp [hl', PC.tx?] at h; subst h
        exact hp'.txP _ (by simp [hpc, PC.tx?])
      reg := by
        intro tx' h; simp [hl', PC.posted] at h; subst h
        exact hp'.reg _ (by simp [hpc, PC.posted])
      notCom := by simp [hl', PC.pre]
      coll := by simp [hl']
      loop := by
        intro tx' c' h; simp [hl', PC.loopC] at h; obtain ⟨rfl, rfl⟩ := h
        exact hp'.loop _ _ (by simp [hpc, PC.loopC])
      prop := by simp [hl']
      kCur := fun t ht htp => by
        rcases hp'.kCur t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h; simp [hl', PC.tx?, h]
        · exact Or.inr h
      kRnd := fun t ht htp => by
        rcases hp'.kRnd t ht htp with h | h
        · left; simp [hpc, PC.tx?] at h; simp [hl', PC.tx?, h]
        · exact Or.inr h
      invdMem := fun a' r h => by
        rcases (hinvd a' r).1 h with h | ⟨rfl, -⟩
        · exact hp.invdMem a' r h
        · exact hq }
  · intro a' r
    rw [hKC]
    split_ifs with he
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      rw [invCnt_insert C q l' _ _ ((hinvd _ _).2 (Or.inr ⟨rfl, rfl⟩)) hnotinv, hI.cnt]
    · rw [invCnt_congr C q l' a' r ?_, hI.cnt]
      rw [hinvd]
      constructor
      · rintro (h | ⟨rfl, rfl⟩)
        · exact h
        · exact absurd rfl he
      · exact Or.inl
  · intro a' r
    rw [hDec, hKC]
    split_ifs with he
    · simp
    · exact hI.kcNone a' r
  · intro a' r t b h
    rw [hDec] at h
    split_ifs at h with he
    · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [Option.some.injEq] at h; rw [h] at hdnK; exact hdnK
    · exact hI.decK a' r t b h
  · have key : ∀ r' t b b', dn = (t, b) → Dec C.mem a r' = some (t, b') → r' = ρ := by
      intro r' t b b' h h'
      cases hd0 : Dec C.mem a ρ with
      | none =>
        exfalso
        have hdp : dn = pr := by simp [hdn, hd0]
        rw [hdp] at h
        have ht : t ∈ c := by rw [show t = pr.1 by rw [h]]; exact hprc
        have hta : t.a = a := (hcK t ht).2.1
        exact hI.undec_of_loop (q := q) (tx := tx) (c := c) (by simp [hpc, PC.loopC]) ht hd0 r' b'
          (by rw [hta]; exact h')
      | some d0 =>
        have hdd : dn = d0 := by simp [hdn, hd0]
        rw [hdd] at h; rw [h] at hd0
        exact (hI.decUniq a ρ r' t b b' hd0 h').symm
    intro a' r r' t b b' h h'
    rw [hDec] at h h'
    by_cases he : (a', r) = (a, ρ) <;> by_cases he' : (a', r') = (a, ρ)
    · simp only [Prod.mk.injEq] at he he'; rw [he.2, he'.2]
    · simp only [he, he', ↓reduceIte] at h h'
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [Option.some.injEq] at h
      exact (key r' t b b' h h').symm
    · simp only [he, he', ↓reduceIte] at h h'
      simp only [Prod.mk.injEq] at he'; obtain ⟨rfl, rfl⟩ := he'
      simp only [Option.some.injEq] at h'
      exact key r t b' b h' h
    · simp only [he, he', ↓reduceIte] at h h'
      exact hI.decUniq a' r r' t b b' h h'

/-- The local state after the update step (line 11 and lines 12–14). -/
def updLoc (l : Loc n Acct) (tx : Tx n Acct) (c : Finset (Tx n Acct))
    (d : Option (Tx n Acct × Bool)) : Loc n Acct :=
  { l with
    pc := loopCheck tx (c \ (l.com tx.a ∪ Option.toFinset (Option.map Prod.fst d))) l.hist
    com := Function.update l.com tx.a (l.com tx.a ∪ Option.toFinset (Option.map Prod.fst d))
    rnd := Function.update l.rnd tx.a (l.rnd tx.a + 1) }

lemma MInv.step_upd (hI : MInv μ C K) {tx : Tx n Acct} {c : Finset (Tx n Acct)}
    {d : Option (Tx n Acct × Bool)} (hpc : (C.loc q).pc = .upd tx c d) :
    MInv μ { C with
      mem := Function.update C.mem (.inl ()) (Function.update (AS C.mem) q (C.loc q).hist)
      loc := Function.update C.loc q (updLoc (C.loc q) tx c d) } K := by
  have hp := hI.proc q
  obtain ⟨htxp, htxK, htxr⟩ := hp.txP tx (by simp [hpc, PC.tx?])
  obtain ⟨hin, hcK⟩ := hp.loop tx c (by simp [hpc, PC.loopC])
  obtain ⟨hd, hds⟩ := hp.upd tx c d hpc
  obtain ⟨d', rfl⟩ := Option.isSome_iff_exists.1 hds
  set a := tx.a with ha
  set ρ := (C.loc q).rnd a with hρ
  have hd'K := hI.decK a ρ d'.1 d'.2 hd.symm
  set m' : Mem n Acct k := Function.update C.mem (.inl ())
    (Function.update (AS C.mem) q (C.loc q).hist) with hm'
  have hASm : AS m' = Function.update (AS C.mem) q (C.loc q).hist := AS_update_AS _
  have hDecm : ∀ a' r, Dec m' a' r = Dec C.mem a' r := fun a' r => Dec_update_AS _ _ _
  have hRegm : ∀ a' i, Reg m' a' i = Reg C.mem a' i := fun a' i => Reg_update_AS _ _ _
  have hKCm : ∀ a' r, KC m' a' r = KC C.mem a' r := fun a' r => KC_update_AS _ _ _
  have hhist : (C.loc q).hist = AS C.mem q ∪ {d'} := by
    rw [hp.hist, hpc]; simp [PC.updDec]
  have hASq : AS m' q = AS C.mem q ∪ {d'} := by rw [hASm, Function.update_self, hhist]
  set com' := Function.update (C.loc q).com a ((C.loc q).com a ∪ {d'.1}) with hcom'
  set c' := c \ ((C.loc q).com a ∪ {d'.1}) with hc'
  set l' := updLoc (C.loc q) tx c (some d') with hl'
  have hl'com : l'.com = com' := by simp [hl', updLoc, hcom', ha]
  have hl'rnd : l'.rnd = Function.update (C.loc q).rnd a (ρ + 1) := by simp [hl', updLoc, ha, hρ]
  have hl'hist : l'.hist = (C.loc q).hist := rfl
  have hl'pc : l'.pc = loopCheck tx c' (C.loc q).hist := by simp [hl', updLoc, hc', ha]
  have hcom'a : com' a = (C.loc q).com a ∪ {d'.1} := by simp [hcom']
  have hcomsub : ∀ a', (C.loc q).com a' ⊆ com' a' := by
    intro a'; by_cases h : a' = a
    · subst h; rw [hcom'a]; exact Finset.subset_union_left
    · simp [hcom', h]
  have hrnd'a : ∀ a', l'.rnd a' = if a' = a then ρ + 1 else (C.loc q).rnd a' := by
    intro a'; rw [hl'rnd, Function.update_apply]
  have hinvd : ∀ a' r, Invd l' a' r ↔ Invd (C.loc q) a' r := by
    intro a' r
    have hupd : ∀ a', (C.loc q).pc.updFor a' = decide (a = a') := by
      intro a'; simp [hpc, PC.updFor, ha]
    have hupd' : ∀ a', l'.pc.updFor a' = false := by
      intro a'; rw [hl'pc]; unfold loopCheck; split_ifs <;> rfl
    simp only [Invd, hupd, hupd', hrnd'a, Bool.false_eq_true, and_false, or_false,
      decide_eq_true_eq]
    by_cases h : a' = a
    · rw [ite_eq_left h, h, ← hρ]; simp only [and_true]; omega
    · simp only [h, ite_false]; constructor
      · exact Or.inl
      · rintro (h' | ⟨-, h'⟩)
        · exact h'
        · exact absurd h'.symm h
  have e := cfg_eq_tau C q l' m'
  simp only at e; rw [e]
  refine hI.of_step q l' _ m' ?_ (fun q' hq' => by rw [hASm, Function.update_of_ne hq'])
    (fun q' _ a' => hRegm a' q') (fun a' r d h => by rw [hDecm]; exact h)
    le_rfl (fun t ht _ => ht) hI.kInj hI.kOwn
    (fun a' i t h => hI.regK a' i t (by rwa [hRegm] at h))
    (fun a' r => by rw [hKCm, invCnt_congr C q l' a' r (hinvd a' r), hI.cnt])
    (fun a' r => by rw [hDecm, hKCm]; exact hI.kcNone a' r)
    (fun a' r t b h => hI.decK a' r t b (by rwa [hDecm] at h))
    (fun a' r r' t b b' h h' => hI.decUniq a' r r' t b b' (by rwa [hDecm] at h)
      (by rwa [hDecm] at h'))
  -- the process itself
  have hcomiff : ∀ a' t, t ∈ com' a' ↔ ∃ r < l'.rnd a', ∃ b, Dec C.mem a' r = some (t, b) := by
    intro a' t
    by_cases h : a' = a
    · subst h
      rw [hcom'a, hrnd'a, ite_eq_left rfl, Finset.mem_union, hp.com, Finset.mem_singleton]
      constructor
      · rintro (⟨r, hr, b, hb⟩ | rfl)
        · exact ⟨r, by omega, b, hb⟩
        · exact ⟨ρ, by omega, d'.2, by rw [← hd]⟩
      · rintro ⟨r, hr, b, hb⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
        · exact Or.inl ⟨r, hr, b, hb⟩
        · right; rw [← hd] at hb; cases hb; rfl
    · rw [show com' a' = (C.loc q).com a' by simp [hcom', h], hrnd'a, ite_eq_right h, hp.com]
  by_cases hmem : tx ∈ c'
  · have hpc' : l'.pc = .snap tx c' := by rw [hl'pc]; simp [loopCheck, hmem]
    exact {
      idle := by rw [hpc']; have := hp.idle; rw [hpc] at this; simp only [reduceCtorEq, iff_false] at this; simp [this]
      pendTx := by
        intro tx' h; rw [hpc'] at h; simp [PC.tx?] at h; subst h
        exact hp.pendTx _ (by simp [hpc, PC.tx?])
      pendR := by rw [hpc']; simp
      hist := by rw [hl'hist, hpc', hASq, hhist]; simp [PC.updDec]
      com := by intro a' t; rw [hl'com, hcomiff]; simp only [hDecm]
      asDec := by
        intro t b hm
        rw [hASq, Finset.mem_union, Finset.mem_singleton] at hm
        rcases hm with hm | rfl
        · obtain ⟨r, hr, hb⟩ := hp.asDec t b hm
          refine ⟨r, ?_, by rw [hDecm]; exact hb⟩
          rw [hrnd'a]; split_ifs with h
          · rw [h] at hr; omega
          · exact hr
        · refine ⟨ρ, ?_, by rw [hDecm, hd'K.2, ← hd]⟩
          rw [hrnd'a, ite_eq_left hd'K.2]; omega
      asAll := by
        intro a' r hr
        rw [hrnd'a] at hr
        by_cases h : a' = a ∧ r = ρ
        · obtain ⟨rfl, rfl⟩ := h
          exact ⟨d', by rw [hDecm, ← hd], by rw [hASq]; simp⟩
        · have hr' : r < (C.loc q).rnd a' := by
            split_ifs at hr with h'
            · subst h'; rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
              · exact hr
              · exact absurd ⟨rfl, hr⟩ h
            · exact hr
          obtain ⟨d'', h1, h2⟩ := hp.asAll a' r hr'
          exact ⟨d'', by rw [hDecm]; exact h1, by rw [hASq]; exact Finset.mem_union_left _ h2⟩
      upd := by rw [hpc']; simp
      txP := by
        intro tx' h; rw [hpc'] at h; simp [PC.tx?] at h; subst h
        refine ⟨htxp, htxK, ?_⟩
        rw [hrnd'a, ite_eq_left ha.symm]; omega
      reg := by
        intro tx' h; rw [hpc'] at h; simp [PC.posted] at h; subst h
        rw [hRegm]; exact hp.reg _ (by simp [hpc, PC.posted])
      notCom := by rw [hpc']; simp [PC.pre]
      coll := by rw [hpc']; simp
      loop := by
        intro tx' c'' h; rw [hpc'] at h; simp [PC.loopC] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨hmem, fun t ht => ?_⟩
        rw [hc', Finset.mem_sdiff] at ht
        obtain ⟨h1, h2, -⟩ := hcK t ht.1
        refine ⟨h1, h2, ?_⟩
        rw [hl'com, hcom'a]; exact ht.2
      prop := by rw [hpc']; simp
      kCur := fun t ht htp => by
        rcases hp.kCur t ht htp with h | h
        · left; rw [hpc']; simp [hpc, PC.tx?] at h ⊢; exact h
        · right; rw [hl'com]; exact hcomsub _ h
      kRnd := fun t ht htp => by
        rcases hp.kRnd t ht htp with h | h
        · left; rw [hpc']; simp [hpc, PC.tx?] at h ⊢; exact h
        · right; rw [hrnd'a]; split_ifs with h' <;> [(rw [h'] at h; omega); exact h]
      invdMem := fun a' r h => hp.invdMem a' r ((hinvd a' r).1 h) }
  · have hpc' : l'.pc = .ret (.inl (decide ((tx, true) ∈ (C.loc q).hist))) := by
      rw [hl'pc]; simp [loopCheck, hmem]
    have htxcom : tx ∈ com' a := by
      rw [hc', Finset.mem_sdiff] at hmem; push Not at hmem
      rw [hcom'a]; exact hmem hin
    exact {
      idle := by rw [hpc']; have := hp.idle; rw [hpc] at this; simp only [reduceCtorEq, iff_false] at this; simp [this]
      pendTx := by rw [hpc']; simp [PC.tx?]
      pendR := by rw [hpc']; simp
      hist := by rw [hl'hist, hpc', hASq, hhist]; simp [PC.updDec]
      com := by intro a' t; rw [hl'com, hcomiff]; simp only [hDecm]
      asDec := by
        intro t b hm
        rw [hASq, Finset.mem_union, Finset.mem_singleton] at hm
        rcases hm with hm | rfl
        · obtain ⟨r, hr, hb⟩ := hp.asDec t b hm
          refine ⟨r, ?_, by rw [hDecm]; exact hb⟩
          rw [hrnd'a]; split_ifs with h
          · rw [h] at hr; omega
          · exact hr
        · refine ⟨ρ, ?_, by rw [hDecm, hd'K.2, ← hd]⟩
          rw [hrnd'a, ite_eq_left hd'K.2]; omega
      asAll := by
        intro a' r hr
        rw [hrnd'a] at hr
        by_cases h : a' = a ∧ r = ρ
        · obtain ⟨rfl, rfl⟩ := h
          exact ⟨d', by rw [hDecm, ← hd], by rw [hASq]; simp⟩
        · have hr' : r < (C.loc q).rnd a' := by
            split_ifs at hr with h'
            · subst h'; rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | hr
              · exact hr
              · exact absurd ⟨rfl, hr⟩ h
            · exact hr
          obtain ⟨d'', h1, h2⟩ := hp.asAll a' r hr'
          exact ⟨d'', by rw [hDecm]; exact h1, by rw [hASq]; exact Finset.mem_union_left _ h2⟩
      upd := by rw [hpc']; simp
      txP := by rw [hpc']; simp [PC.tx?]
      reg := by rw [hpc']; simp [PC.posted]
      notCom := by rw [hpc']; simp [PC.pre]
      coll := by rw [hpc']; simp
      loop := by rw [hpc']; simp [PC.loopC]
      prop := by rw [hpc']; simp
      kCur := fun t ht htp => by
        rcases hp.kCur t ht htp with h | h
        · right; simp [hpc, PC.tx?] at h; subst h; rw [hl'com]; exact htxcom
        · right; rw [hl'com]; exact hcomsub _ h
      kRnd := fun t ht htp => by
        rcases hp.kRnd t ht htp with h | h
        · right; simp [hpc, PC.tx?] at h; subst h; rw [hrnd'a, ite_eq_left rfl]; omega
        · right; rw [hrnd'a]; split_ifs with h' <;> [(rw [h'] at h; omega); exact h]
      invdMem := fun a' r h => hp.invdMem a' r ((hinvd a' r).1 h) }

end CryptoCons.Fig3
