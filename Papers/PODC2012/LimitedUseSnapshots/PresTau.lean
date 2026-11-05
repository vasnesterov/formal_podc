import Papers.PODC2012.LimitedUseSnapshots.PresSteps

/-!
# Preservation of the invariant: internal steps
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-- The invariant after an internal step of `p`, from its process-specific parts. -/
lemma inv_step_tau_core {α : List (Label P maxArrObj)} {C C' : Cfg P} {p : P}
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C) (hT : TStep T C p C')
    (hpinv : PInv T (α ++ [.tau p]) C' p)
    (hg1 : ∀ a b, sc C' (a ++ [b]) ≤ sc C' a)
    (hq : ∀ c, 0 < sc C' c → Past T (α ++ [.tau p]) (fun D => sc D [] = sc C' c ∧ LeftDom c (sw D)))
    (hfs : ∀ a, sw C' a = true → ∃ pU v,
      InvBefore T (α ++ [.tau p]) pU (.upd0 v) (fun _ D => LeftDom a (sw D)) ∧
        Below T C' (a ++ [true]) v)
    (hw : 0 < sc C' [] → ∃ pU, InvBefore T (α ++ [.tau p]) pU (.upd1 (sc C' []))
      (fun _ D => sc D [] < sc C' [])) :
    Inv T (α ++ [.tau p]) C' := by
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  have hf := hT.frameOK
  have hℓ : ∀ q r, (Label.tau p : Label P maxArrObj) ≠ .ret q r := by simp
  refine ⟨fun q => ?_, hg1, hq, hfs, hw, fun y hy => ?_, fun y r hy hr => ?_, fun y r hy hr => ?_,
    fun y o' r hy hr => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hpinv
    · exact (hI.pinv q).frame T hf hqp rfl
  · rw [completed_append_of_not_ret hℓ] at hy
    rw [contribOf_append_of_completed hwf hy]; exact (hI.comp y hy).memLE hf.mem
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact (hI.compScan y r h1 h2).frame T hf
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact (hI.hist y r h1 h2).append T _
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact hI.resp0 y o' r h1 h2

/-- The global components when the memory does not change. -/
lemma inv_step_tau_memEq {α : List (Label P maxArrObj)} {C C' : Cfg P} {p : P}
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C) (hT : TStep T C p C')
    (hmem : C'.mem = C.mem) (hpinv : PInv T (α ++ [.tau p]) C' p) :
    Inv T (α ++ [.tau p]) C' := by
  have hsw : ∀ a, sw C' a = sw C a := fun a => by simp [sw, hmem]
  have hsc : ∀ a, sc C' a = sc C a := fun a => by simp [sc, hmem]
  have hm : MemLE C C' := hT.memLE
  refine inv_step_tau_core T hI hrun hT hpinv (fun a b => by rw [hsc, hsc]; exact hI.g1 a b)
    (fun c hc => ?_) (fun a ha => ?_) (fun h => ?_)
  · rw [hsc] at hc ⊢; exact (hI.q c hc).append _
  · rw [hsw] at ha
    obtain ⟨pU, v, h1, h2⟩ := hI.fs a ha
    exact ⟨pU, v, h1.append _, h2.memLE hm⟩
  · rw [hsc] at h ⊢; exact (hI.w h).imp fun _ h => h.append _

/-- A pending left propagation at `a` carries a value `≤ a.second`. -/
lemma Inv.s3_le {α : List (Label P maxArrObj)} {C : Cfg P} (hI : Inv T α C) {q : P} {e : Bool}
    {a : List Bool} {y : ℕ} (hq : C.loc q = .s3 e a y) : y ≤ sc C a := by
  have := hI.pinv q
  rw [pinv_iff T hq] at this
  exact (this.2.2.2.2.2.2.1 y rfl).1

/-! ### Scan steps that do not write -/

lemma inv_tau_s1node {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool} {l r : Shape} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hl : C.loc p = .s1 e a) (hn : T.subD a = .node l r) :
    Inv T (α ++ [.tau p]) (setLoc C p (.s2 e a (sc C a))) := by
  have hT := TStep.s1node e a l r hl hn
  have hf := hT.frameOK
  refine inv_step_tau_memEq T hI hrun hT rfl ?_
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  rw [pinv_iff T (l := .s2 e a (sc C a)) (by simp)]
  obtain ⟨h1, h2, h3, -, h5, h6, -, h8⟩ := hP
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  refine ⟨fun he => ?_, fun he => ?_, h3, fun _ => ⟨l, r, hn⟩, by simpa using h5,
    h6.frame h5 hf le_rfl, fun x hx => ?_, fun hc => ?_⟩
  · obtain ⟨hp, hc⟩ := h1 he; exact ⟨hp, hc.append hℓ⟩
  · obtain ⟨v, hp, hv, hc⟩ := h2 he; exact ⟨v, hp, hv, hc.append hℓ⟩
  · cases hx
    refine ⟨by simp, ?_⟩
    by_cases h0 : sc C a = 0
    · exact Or.inl h0
    · exact Or.inr ((hI.q a (Nat.pos_of_ne_zero h0)).append _)
  · obtain ⟨pU, v, h1, h2⟩ := h8 hc
    exact ⟨pU, v, h1.append _, h2.memLE hf.mem⟩

lemma inv_tau_s4 {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hl : C.loc p = .s4 e a) :
    Inv T (α ++ [.tau p]) (setLoc C p (.s5 e a (sc C a))) := by
  have hT := TStep.s4 (T := T) e a hl
  have hf := hT.frameOK
  refine inv_step_tau_memEq T hI hrun hT rfl ?_
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  rw [pinv_iff T (l := .s5 e a (sc C a)) (by simp)]
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := hP
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  refine ⟨fun he => ?_, fun he => ?_, h3, h4, by simpa using h5,
    h6.frame h5 hf le_rfl, fun x hx => ?_, fun hc => ?_⟩
  · obtain ⟨hp, hc⟩ := h1 he; exact ⟨hp, hc.append hℓ⟩
  · obtain ⟨v, hp, hv, hc⟩ := h2 he; exact ⟨v, hp, hv, hc.append hℓ⟩
  · cases hx
    refine ⟨by simp, ?_⟩
    by_cases h0 : sc C a = 0
    · exact Or.inl h0
    · exact Or.inr (((hI.q a (Nat.pos_of_ne_zero h0)).append _).mono
        fun D h => ⟨h.1, leftDom_append_true h.2⟩)
  · obtain ⟨pU, v, h1, h2⟩ := h8 hc
    exact ⟨pU, v, h1.append _, h2.memLE hf.mem⟩

lemma inv_tau_s2 {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool} {x : ℕ} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hl : C.loc p = .s2 e a x) :
    Inv T (α ++ [.tau p]) (setLoc C p (if sw C a then .s4 e a else .s3 e a x)) := by
  have hT := TStep.s2 (T := T) e a x hl
  have hf := hT.frameOK
  refine inv_step_tau_memEq T hI hrun hT rfl ?_
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
  obtain ⟨hx1, hx2⟩ := h7 x rfl
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  by_cases hsw : sw C a = true
  · rw [pinv_iff T (l := .s4 e a) (by simp [hsw])]
    refine ⟨fun he => ?_, fun he => ?_, h3, h4, rightDom_append_true (by simpa using h5)
      (by simpa using hsw), fun u y hu => ?_, fun y hy => (nomatch hy), fun _ => ?_⟩
    · obtain ⟨hp, hc⟩ := h1 he
      exact ⟨hp, (hc.append hℓ).mono fun _ _ h => ⟨leftDom_append_true h.1, h.2.trans hx1⟩⟩
    · obtain ⟨v, hp, hv, hc⟩ := h2 he; exact ⟨v, hp, hv.trans hx1, hc.append hℓ⟩
    · rcases rightStep_append_singleton hu with ⟨rfl, -⟩ | ⟨x', rfl⟩
      · refine ⟨by simpa using hI.g1 u false, fun q e' y hq => ?_⟩
        by_cases hqp : q = p
        · subst hqp; simp [hsw] at hq
        · rw [setLoc_other hqp] at hq; simpa using hI.s3_le T hq
      · exact (h6 u x' rfl).frame (h5 u x' rfl) hf hx1
    · obtain ⟨pU, v, hI1, hB⟩ := hI.fs a hsw
      exact ⟨pU, v, (hI1.append _).mono fun _ _ h => leftDom_append_true h, hB.memLE hf.mem⟩
  · have hsw' : sw C a = false := by simpa using hsw
    rw [pinv_iff T (l := .s3 e a x) (by simp [hsw'])]
    have hD : ∀ D : Cfg P, MemLE D C → sw D a = false := fun D hm => by
      cases h : sw D a; · rfl
      · simp [hm.1 a h] at hsw'
    refine ⟨fun he => ?_, fun he => ?_, h3, h4, rightDom_append_false (by simpa using h5),
      fun u y hu => ?_, fun y hy => ?_, fun hc => ?_⟩
    · obtain ⟨hp, hc⟩ := h1 he
      exact ⟨hp, (hc.mono' hrun fun β D _ _ hm h =>
        ⟨leftDom_append_false h.1 (hD D hm), h.2⟩).append hℓ⟩
    · obtain ⟨v, hp, hv, hc⟩ := h2 he; exact ⟨v, hp, hv, hc.append hℓ⟩
    · rcases rightStep_append_singleton hu with ⟨rfl, h⟩ | ⟨x', rfl⟩
      · cases h
      · exact (h6 u x' rfl).frame (h5 u x' rfl) hf le_rfl
    · cases hy
      refine ⟨by simpa using hx1, hx2.imp id fun h => ?_⟩
      exact (h.mono' hrun fun β D _ _ hm h => ⟨h.1, leftDom_append_false h.2 (hD D hm)⟩).append _
    · obtain ⟨u, y, hu⟩ := hc
      rcases rightStep_append_singleton hu with ⟨rfl, h⟩ | ⟨x', hx'⟩
      · cases h
      · obtain ⟨pU, v, hI1, hB⟩ := h8 ⟨u, x', hx'⟩
        obtain ⟨l', r', hn⟩ := h4 rfl
        refine ⟨pU, v, (hI1.mono' hrun fun β D _ _ hm h =>
          leftDom_append_false h (hD D hm)).append _, (hB.left hn hsw').memLE hf.mem⟩

/-! ### The final step of a scan -/

/-- A value `g` stored at a leaf reachable under the switches of `D` is at most the result of a
scan that reached the leaf `a` by a path consistent with `D` (Lemma 3.1 + 3.2 + 3.3). -/
lemma good1_le {D C : Cfg P} (hg : ∀ a b, sc D (a ++ [b]) ≤ sc D a) (hm : MemLE D C) {g : ℕ}
    (hG : Good1 T D g) {a : List Bool} (ha : IsLeaf T a) (hld : LeftDom a (sw D)) {b : ℕ}
    (hrg : RG C a b) (hab : sc C a ≤ b) : g ≤ b := by
  obtain ⟨ℓ, hℓ, hrd, hgle⟩ := hG
  rcases Shape.path_trichotomy ℓ a with rfl | ⟨c, hc, h⟩ | ⟨c, hc, h⟩ |
      ⟨u, x, y, h1, h2⟩ | ⟨u, x, y, h1, h2⟩
  · exact hgle.trans ((hm.2 ℓ).trans hab)
  · exact absurd (h ▸ ha.1) (Shape.not_isAddr_of_leaf hℓ.2 hc)
  · exact absurd (h ▸ hℓ.1) (Shape.not_isAddr_of_leaf ha.2 hc)
  · calc g ≤ sc D ℓ := hgle
      _ = sc D ((u ++ [false]) ++ x) := by rw [h1]; simp
      _ ≤ sc D (u ++ [false]) := sc_append_le hg _ _
      _ ≤ sc C (u ++ [false]) := hm.2 _
      _ ≤ b := (hrg u y h2).1
  · have := hrd u x h1; have := hld u y h2; simp_all

lemma inv_tau_s1leaf {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool}
    (hpast : ∀ β D, β <+: α → (alg P T true).run β = some D → Inv T β D)
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hl : C.loc p = .s1 e a) (hleaf : T.subD a = .leaf) :
    Inv T (α ++ [.tau p]) (setLoc C p (.rt (if e then (0, 0) else (T.lo a, sc C a)))) := by
  have hT := TStep.s1leaf (T := T) e a hl hleaf
  have hf := hT.frameOK
  refine inv_step_tau_memEq T hI hrun hT rfl ?_
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  obtain ⟨h1, h2, h3, -, h5, h6, -, h8⟩ := hP
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  have hA : IsLeaf T a := ⟨h3, hleaf⟩
  cases e with
  | true =>
    rw [pinv_iff T (l := .rt (0, 0)) (by simp)]
    obtain ⟨v, hp, hv, hc⟩ := h2 rfl
    refine Or.inr ⟨v, hp, rfl, ⟨a, hA, by simpa using h5, by simpa using hv⟩, ?_, hc.append hℓ⟩
    simpa using hv.trans (by simpa using sc_append_le hI.g1 [] a)
  | false =>
    rw [pinv_iff T (l := .rt (T.lo a, sc C a)) (by simp)]
    obtain ⟨hp, hc⟩ := h1 rfl
    refine Or.inl ⟨hp, ?_, fun hpos => ?_, fun hpos => ?_, ?_⟩
    · refine (hc.mono' hrun fun β D hβ hD _ h z hz => ?_).append hℓ
      have hc' := (hpast β D hβ hD).comp z hz
      exact Prod.mk_le_mk.2 ⟨hc'.1 a hA h.1, hc'.2.1.trans h.2⟩
    · have hrs : ∃ u x, a = u ++ true :: x := by
        by_contra hn
        simp only [not_exists] at hn
        simp [Shape.lo_eq_zero_of_noTrue T a hn] at hpos
      obtain ⟨pU, v, hIB, hB⟩ := h8 hrs
      have hv := hIB.upd0_lt hrun
      obtain ⟨hlo, -⟩ := hB.leaf hv hleaf
      rw [hlo]
      refine ⟨pU, (hIB.mono' hrun fun β D hβ hD hm h z hz => ?_).append _⟩
      have hI' := hpast β D hβ hD
      have hc' := hI'.comp z hz
      rw [← hlo]
      exact Prod.mk_le_mk.2 ⟨hc'.1 a hA h,
        good1_le T hI'.g1 hm hc'.2.2 hA h h6 le_rfl⟩
    · obtain ⟨β, D, hβ, hD, hDa, hld⟩ := hI.q a hpos
      have hI' := hpast β D hβ hD
      obtain ⟨pU, hIB⟩ := hI'.w (by rw [hDa]; exact hpos)
      rw [hDa] at hIB
      refine ⟨pU, ((hIB.mono' hD fun β' D' hβ' hD' hm' h z hz => ?_).of_prefix
        (hβ.trans (List.prefix_append _ _)))⟩
      have hc' := (hpast β' D' (hβ'.trans hβ) hD').comp z hz
      exact Prod.mk_le_mk.2 ⟨hc'.1 a hA (leftDom_of_memLE hld hm'), (hc'.2.1.trans h.le)⟩
    · have hlt : T.lo a < T.size := by
        have := Shape.lo_add_size_le T a h3; rw [hleaf] at this; simp [Shape.size] at this; omega
      have haddr := Shape.addr_lo T a h3 hleaf
      refine ⟨hlt, ?_, ?_, ?_⟩ <;> simp only [haddr]
      · simpa using h5
      · simp
      · exact h6.frame h5 hf le_rfl

/-! ### Writes to `second` below the root (lines 13, 17) -/

lemma inv_tau_secWrite {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool} {b : Bool} {x : ℕ} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hT : TStep T C p (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p
      (.s1 e (a ++ [b]))))
    (hxa : x ≤ sc C a)
    (hxq : x = 0 ∨ Past T α (fun D => sc D [] = x ∧ LeftDom (a ++ [b]) (sw D)))
    (hpinv : PInv T (α ++ [.tau p])
      (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p (.s1 e (a ++ [b]))) p) :
    Inv T (α ++ [.tau p])
      (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p (.s1 e (a ++ [b]))) := by
  have hm := hT.memLE
  have hne : a ++ [b] ≠ [] := by simp
  refine inv_step_tau_core T hI hrun hT hpinv (fun a' b' => ?_) (fun c hc => ?_) (fun a' ha => ?_)
    (fun h => ?_)
  · simp only [sc_setLoc, sc_setSec]
    by_cases h : a' ++ [b'] = a ++ [b]
    · obtain ⟨rfl, rfl⟩ : a' = a ∧ b' = b := by simpa using h
      simp only [↓reduceIte, max_le_iff]
      have hne' : a' ≠ a' ++ [b'] := by simp
      simp only [hne', ↓reduceIte]
      exact ⟨hI.g1 _ _, hxa⟩
    · simp only [h, ↓reduceIte]
      refine (hI.g1 a' b').trans ?_
      split_ifs <;> simp_all
  · simp only [sc_setLoc, sc_setSec] at hc ⊢
    split_ifs at hc ⊢ with h
    · subst h
      by_cases hx : x ≤ sc C (a ++ [b])
      · rw [max_eq_left hx] at hc ⊢; exact (hI.q _ hc).append _
      · rw [max_eq_right (by omega)] at hc ⊢
        rcases hxq with h0 | hP
        · omega
        · exact hP.append _
    · exact (hI.q c hc).append _
  · simp only [sw_setLoc, sw_setSec] at ha
    obtain ⟨pU, v, h1, h2⟩ := hI.fs a' ha
    exact ⟨pU, v, h1.append _, h2.memLE hm⟩
  · have h0 : sc (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p (.s1 e (a ++ [b]))) []
        = sc C [] := by simp [sc_setSec, hne.symm]
    rw [h0] at h ⊢; exact (hI.w h).imp fun _ h => h.append _

lemma inv_tau_s35 {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {e : Bool}
    {a : List Bool} {b : Bool} {x : ℕ} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hT : TStep T C p (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p
      (.s1 e (a ++ [b]))))
    (hS : ScanInv T α C p e a (a ++ [b]) x true (some x)) :
    Inv T (α ++ [.tau p])
      (setLoc (setSec C (a ++ [b]) (max (sc C (a ++ [b])) x)) p (.s1 e (a ++ [b]))) := by
  have hf := hT.frameOK
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hS
  obtain ⟨hx1, hx2⟩ := h7 x rfl
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  have hxb : x ≤ max (sc C (a ++ [b])) x := le_max_right _ _
  refine inv_tau_secWrite T hI hrun hT hx1 hx2 ?_
  rw [pinv_iff T (l := .s1 e (a ++ [b])) (by simp)]
  obtain ⟨l, r, hn⟩ := h4 rfl
  refine ⟨fun he => ?_, fun he => ?_, Shape.isAddr_append_bool h3 hn b, fun h => (nomatch h),
    by simpa using h5, ?_, fun y hy => (nomatch hy), fun hc => ?_⟩
  · obtain ⟨hp, hc⟩ := h1 he
    exact ⟨hp, (hc.append hℓ).mono fun _ _ h => ⟨h.1, h.2.trans (by simp [sc_setSec])⟩⟩
  · obtain ⟨v, hp, hv, hc⟩ := h2 he
    exact ⟨v, hp, hv.trans (by simp [sc_setSec]), hc.append hℓ⟩
  · exact h6.frame h5 hf (by simp [sc_setSec])
  · obtain ⟨pU, v, hI1, hB⟩ := h8 hc
    exact ⟨pU, v, hI1.append _, hB.memLE hf.mem⟩

/-! ### `MaxUpdate1` (line 9) -/

lemma inv_tau_w1 {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {v : ℕ}
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C) (hl : C.loc p = .w1 v)
    (hs : (alg P T true).step C (.tau p) =
      some (setLoc (setSec C [] (max (sc C []) v)) p (.s1 true []))) :
    Inv T (α ++ [.tau p]) (setLoc (setSec C [] (max (sc C []) v)) p (.s1 true [])) := by
  have hT := TStep.w1 (T := T) v hl
  have hm := hT.memLE
  have hrun' : (alg P T true).run (α ++ [.tau p]) =
      some (setLoc (setSec C [] (max (sc C []) v)) p (.s1 true [])) := by
    rw [Impl.run_concat, hrun]; exact hs
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  obtain ⟨hp, hc⟩ := hP
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  refine inv_step_tau_core T hI hrun hT ?_ (fun a' b' => ?_) (fun c hc => ?_) (fun a' ha => ?_)
    (fun h => ?_)
  · rw [pinv_iff T (l := .s1 true []) (by simp)]
    refine ⟨fun h => (nomatch h), fun _ => ⟨v, hp, by simp [sc_setSec], hc.append hℓ⟩,
      Shape.isAddr_nil T, fun h => (nomatch h), rightDom_nil _, ?_, fun y hy => (nomatch hy), ?_⟩
    · intro u x hu; cases u <;> simp at hu
    · rintro ⟨u, x, hu⟩; cases u <;> simp at hu
  · simp only [sc_setLoc, sc_setSec, show a' ++ [b'] ≠ [] by simp, ↓reduceIte]
    refine (hI.g1 a' b').trans ?_
    split_ifs with h
    · subst h; simp
    · simp
  · by_cases h : c = []
    · subst h; exact past_self hrun' ⟨rfl, leftDom_nil _⟩
    · simp only [sc_setLoc, sc_setSec, h, ↓reduceIte] at hc ⊢
      exact (hI.q c hc).append _
  · simp only [sw_setLoc, sw_setSec] at ha
    obtain ⟨pU, v', h1, h2⟩ := hI.fs a' ha
    exact ⟨pU, v', h1.append _, h2.memLE hm⟩
  · simp only [sc_setLoc, sc_setSec, ↓reduceIte] at h ⊢
    by_cases hv : v ≤ sc C []
    · rw [max_eq_left hv] at h ⊢; exact (hI.w h).imp fun _ h => h.append _
    · rw [max_eq_right (by omega)]
      refine ⟨p, ((hc.invBefore).mono' hrun fun β D _ _ hm' _ => ?_).append _⟩
      exact lt_of_le_of_lt (hm'.2 []) (by omega)

/-! ### `MaxUpdate0` -/

lemma inv_tau_d0rd {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {v : ℕ} {a : List Bool}
    {n : ℕ} {l r : Shape} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hl : C.loc p = .d0 v a) (hn : T.subD (a ++ List.replicate n true) = .node l r)
    (hlt : v - T.lo (a ++ List.replicate n true) < l.size)
    (hpre : v < T.size → a <+: T.addr v → a ++ List.replicate n true <+: T.addr v) :
    Inv T (α ++ [.tau p]) (setLoc C p (if sw C (a ++ List.replicate n true) then
        .up v (a ++ List.replicate n true) else .d0 v (a ++ List.replicate n true ++ [false]))) := by
  have hT := TStep.d0rd (T := T) v a n l r hl hn hlt hpre
  refine inv_step_tau_memEq T hI hrun hT rfl ?_
  have hP := hI.pinv p
  rw [pinv_iff T hl] at hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  set c := a ++ List.replicate n true with hcdef
  have hc : c <+: T.addr v := hpre h2 h3
  have hcf : c ++ [false] <+: T.addr v := (Shape.prefix_addr_child h2 hc hn).1 hlt
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  have h4' : CurInv T α p (.upd0 v) (fun _ D => LeftDom c (sw D)) :=
    h4.mono fun _ _ h => leftDom_append_replicate_true h n
  by_cases hsw : sw C c = true
  · rw [pinv_iff T (l := .up v c) (by simp [hsw])]
    exact ⟨h1, h2, hc, below_of_abort hcf (by simpa using hsw), h4'.append hℓ⟩
  · have hsw' : sw C c = false := by simpa using hsw
    rw [pinv_iff T (l := .d0 v (c ++ [false])) (by simp [hsw'])]
    refine ⟨h1, h2, hcf, (h4'.mono' hrun fun β D _ _ hm h => leftDom_append_false h ?_).append hℓ⟩
    cases h' : sw D c; · rfl
    · simp [hm.1 c h'] at hsw'

/-- Setting the switch of the deepest right step `a'` above `c` (line 7). -/
lemma inv_tau_swWrite {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {v : ℕ}
    {c a' : List Bool} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hT : TStep T C p (setLoc (setSw C a' true) p (.up v a')))
    (h1 : C.pend p = some (.upd0 v)) (h2 : v < T.size) (hc : c <+: T.addr v)
    (hB : Below T C c v) (hcur : CurInv T α p (.upd0 v) (fun _ D => LeftDom c (sw D)))
    (hdr : deepRight c = some a') :
    Inv T (α ++ [.tau p]) (setLoc (setSw C a' true) p (.up v a')) := by
  have hm := hT.memLE
  obtain ⟨rest, hcr, hrest⟩ := deepRight_eq_some hdr
  have hsw : sw (setLoc (setSw C a' true) p (.up v a')) a' = true := by simp [sw_setSw]
  obtain ⟨hB1, hB2⟩ := hB.up hcr hrest hm hsw
  have hℓ : (Label.tau p : Label P maxArrObj).proc = p →
      (Label.tau p : Label P maxArrObj) = .tau p := fun _ => rfl
  have hcur' : CurInv T α p (.upd0 v) (fun _ D => LeftDom a' (sw D)) :=
    hcur.mono fun _ _ h => LeftDom.of_append (d := true :: rest) (hcr ▸ h)
  refine inv_step_tau_core T hI hrun hT ?_ (fun a b => by simpa using hI.g1 a b)
    (fun c' hc' => ?_) (fun a'' ha => ?_) (fun h => ?_)
  · rw [pinv_iff T (l := .up v a') (by simp)]
    exact ⟨by simpa using h1, h2, (List.prefix_append _ _).trans (hcr ▸ hc), hB1, hcur'.append hℓ⟩
  · simp only [sc_setLoc, sc_setSw] at hc' ⊢; exact (hI.q c' hc').append _
  · by_cases h : a'' = a'
    · subst h
      exact ⟨p, v, hcur'.invBefore.append _, hB2⟩
    · simp only [sw_setLoc, sw_setSw, h, ↓reduceIte] at ha
      obtain ⟨pU, v', h1, h2⟩ := hI.fs a'' ha
      exact ⟨pU, v', h1.append _, h2.memLE hm⟩
  · simp only [sc_setLoc, sc_setSw] at h ⊢; exact (hI.w h).imp fun _ h => h.append _

end Podc.LimitedUseSnapshots
