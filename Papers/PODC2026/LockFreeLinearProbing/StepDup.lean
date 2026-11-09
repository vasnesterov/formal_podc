import Papers.PODC2026.LockFreeLinearProbing.StepOwn

/-!
# The invariant `Inv` is preserved: the duplicate scan (lines 48–67, `del_other_copy`)
-/

set_option linter.unusedSectionVars false

namespace Podc.LockFreeLinearProbing

open Cslib.SharedMemory Function

variable {K : Type} [DecidableEq K] [Inhabited K] {m : ℕ} [NeZero m] {h : K → Fin m}
variable {P : Type} [DecidableEq P] {N : ℕ} {ts : P → ℕ} {C C' : Cfg K m P} {p : P}

lemma dsNext_cases (l : Loc K m) :
    (l.i + 1 = h l.op.key ∧ dsNext h l = { l with i := l.i + 1, pc := .l66LL }) ∨
    (l.i + 1 ≠ h l.op.key ∧ dsNext h l = { l with i := l.i + 1, pc := .dsLL }) := by
  unfold dsNext; split_ifs with h1
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨h1, rfl⟩

lemma dsBody_cases (l : Loc K m) :
    (l.val = .empty ∧ dsBody h l = { l with pc := .l66LL }) ∨
    (l.val ≠ .empty ∧ l.i ≠ l.j ∧ l.val.key? = some l.op.key ∧
      (dist h l.op.key l.i < dist h l.op.key l.j ∨ l.val = .key l.op.key .fin) ∧
      dsBody h l = { l with pc := .dcLL76 }) ∨
    (l.val = .key l.op.key .tent ∧ l.i ≠ l.j ∧ ¬ dist h l.op.key l.i < dist h l.op.key l.j ∧
      dsBody h l = { l with pc := .docRD }) ∨
    (l.val ≠ .empty ∧ (l.i ≠ l.j → l.val.key? = some l.op.key → l.val = .key l.op.key .reval) ∧
      dsBody h l = dsNext h l) := by
  unfold dsBody
  split_ifs with h1 h2 h3 h4
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2.1, h2.2, h3, rfl⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, h2.1, fun h5 => h3 (Or.inl h5), rfl⟩))
    obtain ⟨-, hk⟩ := h2
    rcases hv : l.val with _ | _ | _ | _ | ⟨w, t⟩ <;> rw [hv] at hk h4 h3 <;> simp [Cell.key?] at hk
    subst hk; cases t <;> simp_all
  · exact Or.inr (Or.inr (Or.inr ⟨h1, fun a b => by simpa using h4, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, fun a b => absurd ⟨a, b⟩ h2, rfl⟩))

/-- The coverage of a duplicate scan at position `i` together with the cell `i`. -/
lemma covers_dsNext {l : Loc K m} {c : Fin m} (hc : covers h (dsNext h l) c) :
    dist h l.op.key c < dist h l.op.key l.i ∨ c = l.i := by
  rcases dsNext_cases (h := h) l with ⟨h1, he⟩ | ⟨h1, he⟩ <;> rw [he] at hc
  · rcases Nat.lt_or_ge (dist h l.op.key c) (dist h l.op.key l.i) with h2 | h2
    · exact Or.inl h2
    · right
      have h3 := dist_of_succ_eq h _ _ h1
      have h4 := dist_lt h l.op.key c
      exact dist_inj h l.op.key (by omega)
  · simp only [covers] at hc
    rw [dist_succ h _ _ h1] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (dist_inj h _ h2)

lemma dsNext_val (l : Loc K m) : (dsNext h l).pc.isVal ∧ (dsNext h l).j = l.j ∧
    (dsNext h l).op = l.op ∧ LocInv (dsNext h l) ∧ recorded (dsNext h l) = none ∧
    (dsNext h l).pc ≠ .docRD ∧ (dsNext h l).pc ≠ .docSC ∧ (dsNext h l).pc ≠ .docRD2 ∧
    (dsNext h l).pc ≠ .iSC := by
  rcases dsNext_cases (h := h) l with ⟨-, he⟩ | ⟨-, he⟩ <;> rw [he] <;>
    simp [PC.isVal, LocInv, recorded]

/-- If owner `J`'s cell is not covered by `p` scanning at `i`, but `p` read `EMPTY` at `i`,
then `J`'s cell lies before `i` (`J`'s free-cell search passed `i`): impossible. -/
lemma lt_of_empty (hI : Inv h N ts C) {J : P} (hJ : (C.loc J).pc.isVal) {v : K}
    (hk : (C.loc J).op.key = v) {i : Fin m} (hi : C.val i = .empty) (hne : (C.loc J).j ≠ i) :
    dist h v (C.loc J).j < dist h v i := by
  rcases Nat.lt_or_ge (dist h v (C.loc J).j) (dist h v i) with h1 | h1
  · exact h1
  · exfalso
    rcases Nat.lt_or_eq_of_le h1 with h2 | h2
    · exact hI.p3' J (Or.inr hJ) i (by rw [hk]; exact h2) hi
    · exact hne (dist_inj h v h2).symm

lemma tau_dsLL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .dsLL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  set l := C.loc p with hl
  have hact : act h p l = .access l.i (.ll p) (fun r => dsBody h { l with val := r.1 }) := by
    simp only [act, hpc, l]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  have hv : l.pc.isVal := by simp [hpc, PC.isVal]
  set w := C.val l.i with hw
  show Inv h (N + 1) ts (upd C p (dsBody h { l with val := w }) l.i
    (w, if p ∈ C.lks l.i then C.lks l.i else p :: C.lks l.i))
  have hpj := hI.own p hv
  -- the generic obligations
  have key : ∀ l' : Loc K m, l'.op = l.op → l'.j = l.j → l'.pc.isVal → LocInv l' →
      (recorded l' = none ∨ recorded l' = some (l.i, w)) → l'.pc ≠ .docRD2 →
      (l'.pc = .docRD ∨ l'.pc = .docSC → l'.i = l.i) → l'.pc ≠ .iSC →
      (∀ J, J ≠ p → (C.loc J).pc.isVal → (C.loc J).op.key = l.op.key →
        C.val (C.loc J).j = .key l.op.key .tent → covers h l' (C.loc J).j → ts p < ts J) →
      (C.val l.j = .key l.op.key .tent → ∀ c, covers h l' c → C.val c ≠ .key l.op.key .fin) →
      Inv h (N + 1) ts (upd C p l' l.i (w, if p ∈ C.lks l.i then C.lks l.i else p :: C.lks l.i)) := by
    intro l' hop hj hv' hloc hrec hd2 hdi hnisc ha1 ha4
    refine inv_of_unchanged hI hp ⟨rfl, fun q hq => mem_addLink_iff hq, hop, by rw [hv, hv'],
      fun _ => hj⟩ hloc (Or.inr (Or.inl rfl)) ?_ ?_ ?_ ?_ ?_ ?_ (fun h1 => absurd h1 hnisc)
    · intro y w' hr _
      rcases hrec with h1 | h1 <;> rw [h1] at hr
      · cases hr
      · simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; simp
    · intro _ c hc; rw [hop, hj] at hc; exact hI.p3' p (Or.inr hv) c hc
    · intro J hJp hJv _ hk ht hc; rw [hop] at hk ht; exact ha1 J hJp hJv hk ht hc
    · rintro J (⟨h1, h2⟩ | h1)
      · exact absurd (by rw [hdi h1]; simpa using mem_addLink_self _) h2
      · exact absurd h1 hd2
    · rintro (⟨h1, h2⟩ | h1)
      · exact absurd (by rw [hdi h1]; simpa using mem_addLink_self _) h2
      · exact absurd h1 hd2
    · intro _ ht c hc; rw [hop] at ht ⊢; rw [hj] at ht; exact ha4 ht c hc
  have hcov : ∀ c, covers h l c ↔ dist h l.op.key c < dist h l.op.key l.i := by
    intro c; simp [covers, hpc]
  rcases dsBody_cases (h := h) { l with val := w } with
    ⟨h1, he⟩ | ⟨h1, h2, h3, h4, he⟩ | ⟨h1, h2, h3, he⟩ | ⟨h1, h2, he⟩ <;> rw [he]
  · -- `EMPTY`: the scan is complete
    simp only at h1
    refine key _ rfl rfl (by simp [PC.isVal]) (by simp [LocInv]) (by simp [recorded])
      (by simp) (by simp) (by simp) ?_ ?_
    · intro J hJp hJv hk ht _
      have hne : (C.loc J).j ≠ l.i := by intro h5; rw [h5, ← hw, h1] at ht; cases ht
      exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht ((hcov _).2 (lt_of_empty hI hJv hk h1 hne))
    · intro ht c _ hc
      have : dist h l.op.key c < dist h l.op.key l.i := by
        rcases Nat.lt_or_ge (dist h l.op.key c) (dist h l.op.key l.i) with h5 | h5
        · exact h5
        · exact absurd h1 (hI.p3 c _ _ hc l.i h5)
      exact hI.a4 p c hv ht ((hcov c).2 this) hc
  · -- an earlier or final copy: `del_copy`
    refine key _ rfl rfl (by simp [PC.isVal]) (by simp [LocInv]) (by simp [recorded])
      (by simp) (by simp) (by simp) ?_ ?_
    · intro J _ _ _ _ hc; simp [covers] at hc
    · intro _ c hc; simp [covers] at hc
  · -- a later tentative copy: `del_other_copy`
    simp only at h1 h2
    refine key _ rfl rfl (by simp [PC.isVal]) (by simp [LocInv, h1, h2]) (by simp [recorded])
      (by simp) (by simp) (by simp) ?_ ?_
    · intro J hJp hJv hk ht hc
      exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht ((hcov _).2 (by simpa [covers] using hc))
    · intro ht c hc; exact hI.a4 p c hv ht ((hcov c).2 (by simpa [covers] using hc))
  · -- continue the scan
    simp only at h1 h2
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := dsNext_val (h := h) { l with val := w }
    refine key _ d3 d2 d1 d4 (Or.inl d5) d8 (fun h5 => by rcases h5 with h5 | h5 <;> simp_all)
      d9 ?_ ?_
    · intro J hJp hJv hk ht hc
      rcases covers_dsNext hc with h5 | h5
      · exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht ((hcov _).2 h5)
      · exfalso
        simp only at h5
        have hij : l.i ≠ l.j := by
          intro h6; apply hJp; apply hI.own_inj J p hJv hv; rw [h5, h6]
        have := h2 hij (by rw [hw, ← h5, ht]; simp)
        rw [hw, ← h5, ht] at this; cases this
    · intro ht c hc hF
      rcases covers_dsNext hc with h5 | h5
      · exact hI.a4 p c hv ht ((hcov c).2 h5) hF
      · simp only at h5; rw [h5] at hF
        have hij : l.i ≠ l.j := by intro h6; rw [h6, ht] at hF; cases hF
        have := h2 hij (by rw [hw, hF]; simp)
        rw [hw, hF] at this; cases this

/-- An owner step in the duplicate scan that changes no cell value and keeps the scan position
and the coverage. -/
lemma inv_dup_same (hI : Inv h N ts C) (hp : C.pend p ≠ none) {x : Fin m} {c' : Cell K × List P}
    {l' : Loc K m} (hv : (C.loc p).pc.isVal) (hu : c'.1 = C.val x)
    (hlk : ∀ q, q ≠ p → (q ∈ c'.2 ↔ q ∈ C.lks x)) (hshape : LinkShape C p x c')
    (hop : l'.op = (C.loc p).op) (hj : l'.j = (C.loc p).j) (hv' : l'.pc.isVal) (hloc : LocInv l')
    (hlink : ∀ y w, recorded l' = some (y, w) → p ∈ (upd C p l' x c').lks y →
      (upd C p l' x c').val y = w)
    (hcov : ∀ c, covers h l' c → covers h (C.loc p) c)
    (hdoc : ∀ J, ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → J ≠ p → (C.loc J).pc.isVal → (C.loc J).j = l'.i →
      (C.loc J).op.key = l'.op.key → C.val l'.i = .key l'.op.key .tent → ts p < ts J)
    (hdoc_self : ((((l'.pc = .docRD ∨ l'.pc = .docSC) ∧ p ∉ (upd C p l' x c').lks l'.i) ∨
      l'.pc = .docRD2)) → l'.j ≠ l'.i)
    (hisc : l'.pc ≠ .iSC) :
    Inv h (N + 1) ts (upd C p l' x c') := by
  refine inv_of_unchanged hI hp ⟨hu, hlk, hop, by rw [hv, hv'], fun _ => hj⟩ hloc hshape hlink
    ?_ ?_ hdoc (fun hd _ hji => hdoc_self hd hji) ?_ (fun h1 => absurd h1 hisc)
  · intro _ c hc; rw [hop, hj] at hc; exact hI.p3' p (Or.inr hv) c hc
  · intro J hJp hJv _ hk ht hc; rw [hop] at hk ht
    exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht (hcov _ hc)
  · intro _ ht c hc; rw [hop] at ht ⊢; rw [hj] at ht; exact hI.a4 p c hv ht (hcov c hc)

lemma tau_docRD (hI : Inv h N ts C) (hpc : (C.loc p).pc = .docRD)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  set l := C.loc p with hl
  have hl0 := hI.loc p; simp only [LocInv, ← hl, hpc] at hl0
  have hact : act h p l = .access l.j (.vl p) (fun r =>
      if r.1 = .key l.op.key .tent then { l with cur := r.1, pc := .docSC }
      else docRet h { l with cur := r.1 } false) := by
    simp only [act, hpc, l]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  have hv : l.pc.isVal := by simp [hpc, PC.isVal]
  show Inv h (N + 1) ts (upd C p (if C.val l.j = .key l.op.key .tent then
    { l with cur := C.val l.j, pc := .docSC } else docRet h { l with cur := C.val l.j } false)
    l.j (C.val l.j, C.lks l.j))
  split_ifs with h1
  · refine inv_dup_same hI hp hv rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl rfl
      (by simp [PC.isVal]) (by simpa [LocInv] using hl0) ?_ ?_ ?_ ?_ (by simp)
    · intro y w hr hy
      simp only [recorded] at hr
      have : recorded l = some (y, w) := by simp only [recorded, hpc]; exact hr
      rw [upd_same] at hy ⊢
      exact hI.link p y w this hy
    · intro c hc; show covers h l c; simpa [covers, hpc] using hc
    · intro J hd hJp hJv hj hk ht
      rcases hd with ⟨-, h2⟩ | h2
      · rw [upd_same] at h2
        exact hI.doc p J (Or.inl ⟨Or.inl hpc, h2⟩) hJv hj hk ht
      · simp at h2
    · intro _; exact Ne.symm hl0.2
  · simp only [docRet, Bool.false_eq_true, ite_false]
    exact inv_val_noCov hI hp hv rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl rfl (by simp [PC.noCov])
      (by simp [LocInv]) (by simp [recorded])

lemma tau_docSC (hI : Inv h N ts C) (hpc : (C.loc p).pc = .docSC)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  set l := C.loc p with hl
  have hl0 := hI.loc p; simp only [LocInv, ← hl, hpc] at hl0
  have hact : act h p l = .access l.i (.sc p .collided) (fun r =>
      if r.2 then docRet h l true else { l with pc := .docRD2 }) := by
    simp only [act, hpc, l]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  have hv : l.pc.isVal := by simp [hpc, PC.isVal]
  have hcov0 : ∀ c, covers h l c ↔ dist h l.op.key c < dist h l.op.key l.i := by
    intro c; simp [covers, hpc]
  simp only [llscObj.δ_sc]
  by_cases hsc : p ∈ C.lks l.i
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_true, docRet]
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := dsNext_val (h := h) l
    refine inv_of_write hI hp hsc (by simp) (by simp) (by simp)
      (fun _ _ _ _ => by simp [OwnCell]) (by simp) d3 (by rw [d1, hv])
      (fun _ => ⟨d2, by rw [d2]; exact hl0.2⟩) d4 d5 ?_ ?_ ?_ ?_ d9
    · intro _ c hc; rw [d3, d2] at hc; exact hI.p3' p (Or.inr hv) c hc
    · intro J hJp hJv _ hk ht hc
      rw [d3] at hk ht
      have hne : (C.loc J).j ≠ l.i := by
        intro h5; rw [h5, upd_val_self] at ht; cases ht
      rw [upd_val_ne _ _ _ _ hne] at ht
      rcases covers_dsNext hc with h5 | h5
      · exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht ((hcov0 _).2 h5)
      · exact absurd h5 hne
    · rintro (h5 | h5 | h5) <;> simp_all
    · intro _ ht c hc
      simp only [d3, d2] at ht ⊢
      have hjne : l.j ≠ l.i := Ne.symm hl0.2
      rw [upd_val_ne _ _ _ _ hjne] at ht
      rcases covers_dsNext hc with h5 | h5
      · by_cases hci : c = l.i
        · rw [hci, upd_val_self]; simp
        · rw [upd_val_ne _ _ _ _ hci]; exact hI.a4 p c hv ht ((hcov0 c).2 h5)
      · rw [h5, upd_val_self]; simp
  · simp only [Cfg.lks] at hsc
    simp only [hsc, ite_false]
    refine inv_dup_same hI hp hv rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl rfl
      (by simp [PC.isVal]) (by simpa [LocInv] using hl0.2) (by simp [recorded]) ?_ ?_ ?_ (by simp)
    · intro c hc; show covers h l c; simpa [covers, hpc] using hc
    · intro J _ hJp hJv hj hk ht
      exact hI.doc p J (Or.inl ⟨Or.inr hpc, hsc⟩) hJv hj hk ht
    · intro _; exact Ne.symm hl0.2

lemma tau_docRD2 (hI : Inv h N ts C) (hpc : (C.loc p).pc = .docRD2)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  set l := C.loc p with hl
  have hl0 := hI.loc p; simp only [LocInv, ← hl, hpc] at hl0
  have hact : act h p l = .access l.i (.vl p) (fun r =>
      docRet h l (decide (r.1 ≠ .key l.op.key .fin))) := by
    simp only [act, hpc, l]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  have hv : l.pc.isVal := by simp [hpc, PC.isVal]
  have hcov0 : ∀ c, covers h l c ↔ dist h l.op.key c < dist h l.op.key l.i := by
    intro c; simp [covers, hpc]
  show Inv h (N + 1) ts (upd C p (docRet h l (decide (C.val l.i ≠ .key l.op.key .fin)))
    l.i (C.val l.i, C.lks l.i))
  by_cases hF : C.val l.i = .key l.op.key .fin
  · have e : decide (C.val l.i ≠ .key l.op.key .fin) = false := by simp [hF]
    rw [e]; simp only [docRet, Bool.false_eq_true, ite_false]
    exact inv_val_noCov hI hp hv rfl (fun _ _ => Iff.rfl) (Or.inl rfl) rfl rfl (by simp [PC.noCov])
      (by simp [LocInv]) (by simp [recorded])
  · have e : decide (C.val l.i ≠ .key l.op.key .fin) = true := by simp [hF]
    rw [e]; simp only [docRet, ite_true]
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := dsNext_val (h := h) l
    refine inv_of_unchanged hI hp ⟨rfl, fun _ _ => Iff.rfl, d3, by rw [d1, hv], fun _ => d2⟩ d4
      (Or.inl rfl) (by simp [d5]) ?_ ?_ (fun J hd => by rcases hd with ⟨h5 | h5, -⟩ | h5 <;> simp_all)
      (fun hd => by rcases hd with ⟨h5 | h5, -⟩ | h5 <;> simp_all) ?_ (fun h5 => absurd h5 d9)
    · intro _ c hc; rw [d3, d2] at hc; exact hI.p3' p (Or.inr hv) c hc
    · intro J hJp hJv _ hk ht hc
      rw [d3] at hk ht
      rcases covers_dsNext hc with h5 | h5
      · exact hI.a1 p J (Ne.symm hJp) hv hJv hk ht ((hcov0 _).2 h5)
      · exact hI.doc p J (Or.inr hpc) hJv h5 hk (by rw [← h5]; exact ht)
    · intro _ ht c hc
      simp only [d3, d2] at ht ⊢
      rcases covers_dsNext hc with h5 | h5
      · exact hI.a4 p c hv ht ((hcov0 c).2 h5)
      · rw [h5]; exact hF

lemma tau_l66LL (hI : Inv h N ts C) (hpc : (C.loc p).pc = .l66LL)
    (hs : (impl h).step C (.tau p) = some C') : Inv h (N + 1) ts C' := by
  set l := C.loc p with hl
  have hact : act h p l = .access l.j (.ll p) (fun r =>
      if r.1 = .key l.op.key .tent then { l with cur := r.1, pc := .l67SC }
      else if r.1 = .key l.op.key .reval then { l with cur := r.1, pc := .l69SC }
      else { l with cur := r.1, pc := .dcLL76 }) := by
    simp only [act, hpc, l]
  obtain ⟨hp, rfl⟩ := step_tau_access hs hact
  have hv : l.pc.isVal := by simp [hpc, PC.isVal]
  show Inv h (N + 1) ts (upd C p (if C.val l.j = .key l.op.key .tent then
      { l with cur := C.val l.j, pc := .l67SC }
      else if C.val l.j = .key l.op.key .reval then { l with cur := C.val l.j, pc := .l69SC }
      else { l with cur := C.val l.j, pc := .dcLL76 })
    l.j (C.val l.j, if p ∈ C.lks l.j then C.lks l.j else p :: C.lks l.j))
  have hlink : ∀ l' : Loc K m, recorded l' = some (l.j, C.val l.j) →
      ∀ y w, recorded l' = some (y, w) →
      p ∈ (upd C p l' l.j (C.val l.j, if p ∈ C.lks l.j then C.lks l.j else p :: C.lks l.j)).lks y →
      (upd C p l' l.j (C.val l.j, if p ∈ C.lks l.j then C.lks l.j else p :: C.lks l.j)).val y = w := by
    intro l' h1 y w hr _; rw [h1] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; simp
  by_cases h1 : C.val l.j = .key l.op.key .tent
  · rw [if_pos h1]
    exact inv_dup_same hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl
      rfl (by simp [PC.isVal]) (by simpa [LocInv] using h1) (hlink _ (by simp [recorded]))
      (fun c _ => by show covers h l c; simp [covers, hpc]) (fun J hd => by simp at hd)
      (fun hd => by simp at hd) (by simp)
  rw [if_neg h1]
  by_cases h2 : C.val l.j = .key l.op.key .reval
  · rw [if_pos h2]
    exact inv_dup_same hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl
      rfl (by simp [PC.isVal]) (by simpa [LocInv] using h2) (hlink _ (by simp [recorded]))
      (fun c _ => by show covers h l c; simp [covers, hpc]) (fun J hd => by simp at hd)
      (fun hd => by simp at hd) (by simp)
  · rw [if_neg h2]
    exact inv_val_noCov hI hp hv rfl (fun q hq => mem_addLink_iff hq) (Or.inr (Or.inl rfl)) rfl
      rfl (by simp [PC.noCov]) (by simp [LocInv]) (by simp [recorded])

end Podc.LockFreeLinearProbing
