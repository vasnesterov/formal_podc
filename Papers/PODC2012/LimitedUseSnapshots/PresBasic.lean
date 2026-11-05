import Papers.PODC2012.LimitedUseSnapshots.Invariant

/-!
# Stability lemmas for the invariant of the corrected Algorithm 2

How the components of `Inv` behave when the execution grows by one label: history records
(`Past`, `InvBefore`, `CurInv`) persist, configuration facts are monotone in the memory
(`MemLE`), and guards survive the steps of other processes (`FrameOK`, `Guard.frame`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-! ### History records persist -/

section Records

variable {T}

lemma Past.append {α : List (Label P maxArrObj)} {Q : Cfg P → Prop} (h : Past T α Q)
    (δ : List (Label P maxArrObj)) : Past T (α ++ δ) Q := by
  obtain ⟨β, D, hβ, hD, hQ⟩ := h
  exact ⟨β, D, hβ.trans (List.prefix_append _ _), hD, hQ⟩

lemma Past.mono {α : List (Label P maxArrObj)} {Q Q' : Cfg P → Prop} (h : Past T α Q)
    (hQ : ∀ D, Q D → Q' D) : Past T α Q' := by
  obtain ⟨β, D, hβ, hD, h'⟩ := h; exact ⟨β, D, hβ, hD, hQ D h'⟩

lemma past_self {α : List (Label P maxArrObj)} {C : Cfg P} {Q : Cfg P → Prop}
    (h : (alg P T true).run α = some C) (hQ : Q C) : Past T α Q :=
  ⟨α, C, List.prefix_refl _, h, hQ⟩

lemma InvBefore.append {α : List (Label P maxArrObj)} {pU : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : InvBefore T α pU o Q)
    (δ : List (Label P maxArrObj)) : InvBefore T (α ++ δ) pU o Q := by
  obtain ⟨β, γ, D, rfl, hD, hQ⟩ := h
  exact ⟨β, γ ++ δ, D, by simp, hD, hQ⟩

lemma InvBefore.of_prefix {α α' : List (Label P maxArrObj)} {pU : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : InvBefore T α pU o Q) (hp : α <+: α') :
    InvBefore T α' pU o Q := by
  obtain ⟨δ, rfl⟩ := hp; exact h.append δ

lemma InvBefore.mono {α : List (Label P maxArrObj)} {pU : P} {o : MAOp}
    {Q Q' : List (Label P maxArrObj) → Cfg P → Prop} (h : InvBefore T α pU o Q)
    (hQ : ∀ β D, Q β D → Q' β D) : InvBefore T α pU o Q' := by
  obtain ⟨β, γ, D, h1, h2, h3⟩ := h; exact ⟨β, γ, D, h1, h2, hQ _ _ h3⟩

lemma CurInv.append {α : List (Label P maxArrObj)} {p : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : CurInv T α p o Q)
    {ℓ : Label P maxArrObj} (hℓ : ℓ.proc = p → ℓ = .tau p) : CurInv T (α ++ [ℓ]) p o Q := by
  obtain ⟨β, γ, D, rfl, hγ, hD, hQ⟩ := h
  refine ⟨β, γ ++ [ℓ], D, by simp, fun ℓ' hℓ' hp => ?_, hD, hQ⟩
  rcases List.mem_append.1 hℓ' with h' | h'
  · exact hγ ℓ' h' hp
  · simp at h'; subst h'; exact hℓ hp

lemma CurInv.mono {α : List (Label P maxArrObj)} {p : P} {o : MAOp}
    {Q Q' : List (Label P maxArrObj) → Cfg P → Prop} (h : CurInv T α p o Q)
    (hQ : ∀ β D, Q β D → Q' β D) : CurInv T α p o Q' := by
  obtain ⟨β, γ, D, h1, h2, h3, h4⟩ := h; exact ⟨β, γ, D, h1, h2, h3, hQ _ _ h4⟩

lemma CurInv.invBefore {α : List (Label P maxArrObj)} {p : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : CurInv T α p o Q) :
    InvBefore T α p o Q := by
  obtain ⟨β, γ, D, h1, -, h3, h4⟩ := h; exact ⟨β, γ, D, h1, h3, h4⟩

lemma curInv_new {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : (alg P T true).run α = some C)
    (hQ : Q α C) : CurInv T (α ++ [.inv p o]) p o Q :=
  ⟨α, [], C, rfl, by simp, h, hQ⟩

end Records

/-! ### Memory monotonicity of configuration facts -/

section Mono

variable {T}

lemma rightDom_of_memLE {c : List Bool} {C C' : Cfg P} (h : RightDom c (sw C)) (hm : MemLE C C') :
    RightDom c (sw C') := RightDom.mono h hm.1

lemma leftDom_of_memLE {c : List Bool} {C C' : Cfg P} (h : LeftDom c (sw C')) (hm : MemLE C C') :
    LeftDom c (sw C) := LeftDom.mono h hm.1

lemma Below.memLE {C C' : Cfg P} {c : List Bool} {v : ℕ} (h : Below T C c v) (hm : MemLE C C') :
    Below T C' c v := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  refine ⟨e, h1, h2, fun u x hu hcu => hm.1 _ (h3 u x hu hcu), ?_⟩
  rcases h4 with h4 | ⟨h4, h5⟩
  · exact Or.inl h4
  · exact Or.inr ⟨hm.1 _ h4, h5⟩

lemma Good1.memLE {C C' : Cfg P} {g : ℕ} (h : Good1 T C g) (hm : MemLE C C') : Good1 T C' g := by
  obtain ⟨ℓ, h1, h2, h3⟩ := h
  exact ⟨ℓ, h1, rightDom_of_memLE h2 hm, h3.trans (hm.2 ℓ)⟩

lemma CompFacts.memLE {C C' : Cfg P} {c : ℕ × ℕ} (h : CompFacts T C c) (hm : MemLE C C') :
    CompFacts T C' c :=
  ⟨fun ℓ hℓ hl => h.1 ℓ hℓ (leftDom_of_memLE hl hm), h.2.1.trans (hm.2 []), h.2.2.memLE hm⟩

end Mono

/-! ### Frames: steps of one process seen by the others -/

/-- The step `C → C'` is taken by `p`: memory grows, other processes are unchanged, `p` enters a
left propagation at `u` only after reading the switch of `u` as `0`, and the left child of `u`
grows only through a left propagation of `p` at `u`. -/
structure FrameOK (C C' : Cfg P) (p : P) : Prop where
  mem : MemLE C C'
  other : ∀ q, q ≠ p → C'.loc q = C.loc q ∧ C'.pend q = C.pend q
  s3new : ∀ e u y, C'.loc p = .s3 e u y → C.loc p = .s3 e u y ∨ sw C u = false
  leftw : ∀ u, sc C' (u ++ [false]) ≤ sc C (u ++ [false]) ∨
    ∃ e y, C.loc p = .s3 e u y ∧ sc C' (u ++ [false]) ≤ max (sc C (u ++ [false])) y

lemma Guard.frame {C C' : Cfg P} {p : P} {u : List Bool} {b b' : ℕ} (hsw : sw C u = true)
    (h : Guard C u b) (hf : FrameOK C C' p) (hb : b ≤ b') : Guard C' u b' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun q e y hq => ?_⟩
  · rcases hf.leftw u with h | ⟨e, y, hp, h⟩
    · exact h.trans (h1.trans hb)
    · exact h.trans (max_le (h1.trans hb) ((h2 p e y hp).trans hb))
  · by_cases hqp : q = p
    · subst hqp
      rcases hf.s3new e u y hq with h | h
      · exact (h2 q e y h).trans hb
      · simp [hsw] at h
    · rw [(hf.other q hqp).1] at hq; exact (h2 q e y hq).trans hb

lemma RG.frame {C C' : Cfg P} {p : P} {c : List Bool} {b b' : ℕ} (hrd : RightDom c (sw C))
    (h : RG C c b) (hf : FrameOK C C' p) (hb : b ≤ b') : RG C' c b' :=
  fun u x hu => (h u x hu).frame (hrd u x hu) hf hb

lemma CompScan.frame {C C' : Cfg P} {p : P} {r : ℕ × ℕ} (h : CompScan T C r)
    (hf : FrameOK C C' p) : CompScan T C' r :=
  ⟨h.1, rightDom_of_memLE h.2.1 hf.mem, h.2.2.1.trans (hf.mem.2 _),
    h.2.2.2.frame h.2.1 hf le_rfl⟩

lemma ScanInv.frame {α : List (Label P maxArrObj)} {C C' : Cfg P} {p q : P} {e : Bool}
    {a c : List Bool} {b b' : ℕ} {node : Bool} {xo : Option ℕ}
    (h : ScanInv T α C q e a c b node xo) (hf : FrameOK C C' p) (hqp : q ≠ p) (hb : b ≤ b')
    {ℓ : Label P maxArrObj} (hℓ : ℓ.proc = p) :
    ScanInv T (α ++ [ℓ]) C' q e a c b' node xo := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hpend := (hf.other q hqp).2
  have hℓ' : ℓ.proc = q → ℓ = .tau q := fun h => absurd (hℓ ▸ h) (Ne.symm hqp)
  refine ⟨fun he => ?_, fun he => ?_, h3, h4, rightDom_of_memLE h5 hf.mem, h6.frame h5 hf hb,
    fun x hx => ?_, fun hc => ?_⟩
  · obtain ⟨hp, hc⟩ := h1 he
    exact ⟨hpend ▸ hp, (hc.append hℓ').mono fun _ _ h => ⟨h.1, h.2.trans hb⟩⟩
  · obtain ⟨v, hp, hv, hc⟩ := h2 he
    exact ⟨v, hpend ▸ hp, hv.trans hb, hc.append hℓ'⟩
  · obtain ⟨hx1, hx2⟩ := h7 x hx
    exact ⟨hx1.trans (hf.mem.2 a), hx2.imp id (fun h => h.append _)⟩
  · obtain ⟨pU, v, hI, hB⟩ := h8 hc
    exact ⟨pU, v, hI.append _, hB.memLE hf.mem⟩

/-- The per-process invariant of a process that does not take the step. -/
lemma PInv.frame {α : List (Label P maxArrObj)} {C C' : Cfg P} {p q : P}
    (h : PInv T α C q) (hf : FrameOK C C' p) (hqp : q ≠ p)
    {ℓ : Label P maxArrObj} (hℓ : ℓ.proc = p) : PInv T (α ++ [ℓ]) C' q := by
  have hl := (hf.other q hqp).1
  have hpend := (hf.other q hqp).2
  have hℓ' : ℓ.proc = q → ℓ = .tau q := fun h => absurd (hℓ ▸ h) (Ne.symm hqp)
  rw [pinv_iff T rfl] at h
  rw [pinv_iff T hl]
  cases hq : C.loc q with
  | idle => rw [hq] at h; simp only [PInvL] at h ⊢; rw [hpend]; exact h
  | d0 v a =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨hpend ▸ h1, h2, h3, h4.append hℓ'⟩
  | up v a =>
    rw [hq] at h; obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact ⟨hpend ▸ h1, h2, h3, h4.memLE hf.mem, h5.append hℓ'⟩
  | w1 v =>
    rw [hq] at h; obtain ⟨h1, h2⟩ := h
    exact ⟨hpend ▸ h1, h2.append hℓ'⟩
  | s1 e a =>
    rw [hq] at h; exact h.frame T hf hqp (hf.mem.2 a) hℓ
  | s2 e a x => rw [hq] at h; exact h.frame T hf hqp le_rfl hℓ
  | s3 e a x => rw [hq] at h; exact h.frame T hf hqp le_rfl hℓ
  | s4 e a => rw [hq] at h; exact h.frame T hf hqp (hf.mem.2 a) hℓ
  | s5 e a x => rw [hq] at h; exact h.frame T hf hqp le_rfl hℓ
  | rt r =>
    rw [hq] at h
    rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨v, h1, h2, h3, h4, h5⟩
    · refine Or.inl ⟨hpend ▸ h1, h2.append hℓ', fun h => (h3 h).imp fun _ h => h.append _,
        fun h => (h4 h).imp fun _ h => h.append _, h5.frame T hf⟩
    · exact Or.inr ⟨v, hpend ▸ h1, h2, h3.memLE hf.mem, h4.trans (hf.mem.2 []), h5.append hℓ'⟩

/-! ### Every step is a frame step -/

lemma frameOK_inv {C : Cfg P} {p : P} {o : MAOp} :
    FrameOK C ⟨Function.update C.loc p (invokeLoc o), Function.update C.pend p (some o), C.mem⟩ p where
  mem := MemLE.refl C
  other q hq := by simp [Function.update_of_ne hq]
  s3new e u y h := by cases o <;> simp [invokeLoc] at h
  leftw u := Or.inl (le_of_eq rfl)

lemma frameOK_ret {C : Cfg P} {p : P} :
    FrameOK C ⟨Function.update C.loc p .idle, Function.update C.pend p none, C.mem⟩ p where
  mem := MemLE.refl C
  other q hq := by simp [Function.update_of_ne hq]
  s3new e u y h := by simp at h
  leftw u := Or.inl (le_of_eq rfl)

lemma setLoc_other {C : Cfg P} {p q : P} {l : Loc} (hq : q ≠ p) :
    (setLoc C p l).loc q = C.loc q := by simp [Function.update_of_ne hq]

lemma TStep.frameOK {C C' : Cfg P} {p : P} (h : TStep T C p C') : FrameOK C C' p := by
  have hm := h.memLE
  cases h with
  | s3 e a x hl =>
    refine ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩, fun e' u y h => ?_,
      fun u => ?_⟩
    · simp at h
    · by_cases hu : u = a
      · subst hu; right; refine ⟨e, x, hl, ?_⟩; simp [sc_setSec]
      · left; simp [sc_setSec, hu]
  | s2 e a x hl =>
    refine ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩, fun e' u y h => ?_,
      fun u => Or.inl (by simp)⟩
    simp only [setLoc_loc, Function.update_self] at h
    split_ifs at h with hs
    · cases h; right; simpa using hs
  | s5 e a x hl =>
    refine ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩, fun e' u y h => by simp at h,
      fun u => Or.inl ?_⟩
    simp only [sc_setLoc, sc_setSec]
    split_ifs with hu
    · exfalso; have := congrArg List.getLast? hu; simp at this
    · exact le_rfl
  | w1 v hl =>
    refine ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩, fun e' u y h => by simp at h,
      fun u => Or.inl ?_⟩
    simp [sc_setSec]
  | d0rd v a n l r hl _ _ _ =>
    refine ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩, fun e' u y h => ?_,
      fun u => Or.inl (by simp)⟩
    simp only [setLoc_loc, Function.update_self] at h; split_ifs at h
  | d0wr | upwr =>
    exact ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩,
      fun e' u y h => by simp at h, fun u => Or.inl (by simp)⟩
  | s1leaf | s1node | s4 =>
    exact ⟨hm, fun q hq => ⟨by simp [Function.update_of_ne hq], rfl⟩,
      fun e' u y h => by simp at h, fun u => Or.inl (by simp)⟩

/-! ### The descent of `MaxUpdate0` (`Below`) -/

section BelowLemmas

variable {T}

lemma prefix_of_rightStep_of_noTrue {a e u x : List Bool} (ha : ∀ y ∈ a, y = false)
    (hae : a <+: e) (hu : e = u ++ true :: x) : a <+: u := by
  have hue : u <+: e := hu ▸ List.prefix_append u _
  by_cases hl : a.length ≤ u.length
  · exact List.prefix_of_prefix_length_le hae hue hl
  · exfalso
    obtain ⟨w, rfl⟩ := List.prefix_of_prefix_length_le hue hae (by omega)
    have hwx : w <+: true :: x := (List.prefix_append_right_inj u).1 (hu ▸ hae)
    have hwne : w ≠ [] := by rintro rfl; simp at hl
    obtain ⟨w0, w', rfl⟩ := List.exists_cons_of_ne_nil hwne
    have : w0 = true := by simpa using (List.cons_prefix_cons.1 hwx).1
    subst this
    simpa using ha true (by simp)

lemma Below.nil_of_noTrue {C : Cfg P} {a : List Bool} {v : ℕ} (h : Below T C a v)
    (ha : ∀ y ∈ a, y = false) : Below T C [] v := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  exact ⟨e, List.nil_prefix, h2, fun u x hu _ => h3 u x hu (prefix_of_rightStep_of_noTrue ha h1 hu),
    h4⟩

/-- After setting the switch of the deepest right step `a'` above `c`. -/
lemma Below.up {C C' : Cfg P} {c a' rest : List Bool} {v : ℕ} (h : Below T C c v)
    (hc : c = a' ++ true :: rest) (hrest : ∀ y ∈ rest, y = false) (hm : MemLE C C')
    (hsw : sw C' a' = true) : Below T C' a' v ∧ Below T C' (a' ++ [true]) v := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  have h4' : T.subD e = .leaf ∨ (sw C' e = true ∧ e ++ [false] <+: T.addr v) := by
    rcases h4 with h4 | ⟨h4, h5⟩
    · exact Or.inl h4
    · exact Or.inr ⟨hm.1 _ h4, h5⟩
  have hce : a' ++ true :: rest <+: e := hc ▸ h1
  refine ⟨⟨e, ?_, h2, fun u x hu hau => ?_, h4'⟩, ⟨e, ?_, h2, fun u x hu hau => ?_, h4'⟩⟩
  · exact (List.prefix_append _ _).trans hce
  · rcases rightStep_cases hrest hce hu hau with rfl | h
    · exact hsw
    · exact hm.1 _ (h3 u x hu (hc ▸ h))
  · exact List.IsPrefix.trans ⟨rest, by simp⟩ hce
  · have hau' : a' <+: u := (List.prefix_append _ _).trans hau
    rcases rightStep_cases hrest hce hu hau' with rfl | h
    · exfalso; have := hau.length_le; simp at this
    · exact hm.1 _ (h3 u x hu (hc ▸ h))

lemma below_of_leaf {C : Cfg P} {c : List Bool} {v : ℕ} (hc : c <+: T.addr v)
    (hl : T.subD c = .leaf) : Below T C c v :=
  ⟨c, List.prefix_refl c, hc, fun u x hu hcu => by
    exfalso; have := hcu.length_le; rw [hu] at this; simp at this, Or.inl hl⟩

lemma below_of_abort {C : Cfg P} {c : List Bool} {v : ℕ} (hc : c ++ [false] <+: T.addr v)
    (hsw : sw C c = true) : Below T C c v :=
  ⟨c, List.prefix_refl c, (List.prefix_append _ _).trans hc, fun u x hu hcu => by
    exfalso; have := hcu.length_le; rw [hu] at this; simp at this, Or.inr ⟨hsw, hc⟩⟩

lemma Below.leaf {C : Cfg P} {a : List Bool} {v : ℕ} (h : Below T C a v) (hv : v < T.size)
    (hl : T.subD a = .leaf) : T.lo a = v ∧ T.addr v = a := by
  obtain ⟨e, h1, h2, -, -⟩ := h
  have he := Shape.eq_of_prefix_of_leaf hl (Shape.isAddr_of_prefix_addr h2) h1
  subst he
  have := Shape.eq_addr_of_leaf hl h2
  exact ⟨by rw [← this, Shape.lo_addr T v hv], this⟩

lemma Below.left {C : Cfg P} {a : List Bool} {v : ℕ} {l r : Shape} (h : Below T C a v)
    (hn : T.subD a = .node l r) (hsw : sw C a = false) :
    Below T C (a ++ [false]) v := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  obtain ⟨c, rfl⟩ := h1
  rcases c with _ | ⟨b, c⟩
  · exfalso
    rcases h4 with h4 | ⟨h4, -⟩
    · simp [hn] at h4
    · simp [hsw] at h4
  · cases b
    · refine ⟨a ++ false :: c, ⟨c, by simp⟩, h2, fun u x hu hau => h3 u x hu
        ((List.prefix_append _ _).trans hau), h4⟩
    · exfalso; have := h3 a c rfl (List.prefix_refl a); simp [hsw] at this

lemma Below.prefix {C : Cfg P} {a : List Bool} {v : ℕ} (h : Below T C a v) : a <+: T.addr v := by
  obtain ⟨e, h1, h2, -, -⟩ := h; exact h1.trans h2

/-- A completed `MaxUpdate0(v)` is seen by every traversal consistent with the switches. -/
lemma Below.le_lo {C : Cfg P} {v : ℕ} (h : Below T C [] v) (hv : v < T.size) {ℓ : List Bool}
    (hℓ : IsLeaf T ℓ) (hld : LeftDom ℓ (sw C)) : v ≤ T.lo ℓ := by
  obtain ⟨e, -, h2, h3, h4⟩ := h
  have hA := Shape.isAddr_addr T v
  have hlo := Shape.lo_addr T v hv
  rcases Shape.path_trichotomy (T.addr v) ℓ with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩ |
      ⟨u, x, y, h1, h5⟩ | ⟨u, x, y, h1, h5⟩
  · rw [← h, hlo]
  · exact absurd (h ▸ hℓ.1) (Shape.not_isAddr_of_leaf (Shape.subD_addr T v) hc)
  · exact absurd (h ▸ hA) (Shape.not_isAddr_of_leaf hℓ.2 hc)
  · have := Shape.lo_lt_of_diverge (h1 ▸ hA) (h5 ▸ hℓ.1)
    rw [← h1, hlo, ← h5] at this; exact this.le
  · exfalso
    have hsw0 := hld u y h5
    have hut : u ++ [true] <+: T.addr v := ⟨x, by simp [h1]⟩
    have hu : u <+: T.addr v := (List.prefix_append _ _).trans hut
    by_cases hl : (u ++ [true]).length ≤ e.length
    · obtain ⟨x', hx'⟩ := List.prefix_of_prefix_length_le hut h2 hl
      have := h3 u x' (by simp [← hx']) List.nil_prefix
      simp [hsw0] at this
    · have heu : e <+: u := List.prefix_of_prefix_length_le h2 hu (by simp at hl; omega)
      have hℓu : u <+: ℓ := ⟨false :: y, h5.symm⟩
      rcases h4 with h4 | ⟨h4, h6⟩
      · have := Shape.eq_of_prefix_of_leaf h4 (Shape.isAddr_of_append (h5 ▸ hℓ.1)) heu
        subst this
        exact Shape.not_isAddr_of_leaf h4 (by simp) (h5 ▸ hℓ.1)
      · by_cases heq : e = u
        · subst heq
          obtain ⟨z, hz⟩ := h6
          rw [h1] at hz; simp at hz
        · have hlt : e.length < u.length := by
            rcases Nat.lt_or_eq_of_le heu.length_le with h | h
            · exact h
            · exact absurd (List.IsPrefix.eq_of_length heu h) heq
          have hef : e ++ [false] <+: u :=
            List.prefix_of_prefix_length_le h6 hu (by simp; omega)
          obtain ⟨z, hz⟩ := hef.trans hℓu
          have := hld e (z) (by simp [← hz])
          simp [h4] at this

end BelowLemmas

/-! ### Records with access to the prefix -/

section Prime

variable {T}

lemma CurInv.mono' {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {o : MAOp}
    {Q Q' : List (Label P maxArrObj) → Cfg P → Prop} (hrun : (alg P T true).run α = some C)
    (h : CurInv T α p o Q)
    (hQ : ∀ β D, β <+: α → (alg P T true).run β = some D → MemLE D C → Q β D → Q' β D) :
    CurInv T α p o Q' := by
  obtain ⟨β, γ, D, hα, h2, h3, h4⟩ := h
  have hp : β <+: α := hα ▸ List.prefix_append _ _
  exact ⟨β, γ, D, hα, h2, h3, hQ β D hp h3 (run_memLE T h3 hrun hp) h4⟩

lemma InvBefore.mono' {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {o : MAOp}
    {Q Q' : List (Label P maxArrObj) → Cfg P → Prop} (hrun : (alg P T true).run α = some C)
    (h : InvBefore T α p o Q)
    (hQ : ∀ β D, β <+: α → (alg P T true).run β = some D → MemLE D C → Q β D → Q' β D) :
    InvBefore T α p o Q' := by
  obtain ⟨β, γ, D, hα, h3, h4⟩ := h
  have hp : β <+: α := hα ▸ List.prefix_append _ _
  exact ⟨β, γ, D, hα, h3, hQ β D hp h3 (run_memLE T h3 hrun hp) h4⟩

lemma Past.mono' {α : List (Label P maxArrObj)} {C : Cfg P} {Q Q' : Cfg P → Prop}
    (hrun : (alg P T true).run α = some C) (h : Past T α Q)
    (hQ : ∀ β D, β <+: α → (alg P T true).run β = some D → MemLE D C → Q D → Q' D) :
    Past T α Q' := by
  obtain ⟨β, D, hp, h3, h4⟩ := h
  exact ⟨β, D, hp, h3, hQ β D hp h3 (run_memLE T h3 hrun hp) h4⟩

lemma InvBefore.upd0_lt {α : List (Label P maxArrObj)} {C : Cfg P} {pU : P} {v : ℕ}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (hrun : (alg P T true).run α = some C)
    (h : InvBefore T α pU (.upd0 v) Q) : v < T.size := by
  obtain ⟨β, γ, D, rfl, -, -⟩ := h
  have := Impl.allowed_of_mem_opsOf (alg P T true) ⟨C, hrun⟩ (p := pU) (o := .upd0 v)
    (by simp [opsOf_append])
  exact this

end Prime

lemma leftDom_append_replicate_true {a : List Bool} {σ : List Bool → Bool} (h : LeftDom a σ) :
    ∀ n, LeftDom (a ++ List.replicate n true) σ
  | 0 => by simpa using h
  | n + 1 => by
    rw [List.replicate_succ', ← List.append_assoc]
    exact leftDom_append_true (leftDom_append_replicate_true h n)

/-- Right steps of `a ++ [b]`. -/
lemma rightStep_append_singleton {a u x : List Bool} {b : Bool} (h : a ++ [b] = u ++ true :: x) :
    (u = a ∧ b = true) ∨ ∃ x', a = u ++ true :: x' := by
  rcases eq_append_singleton_cases h.symm with ⟨rfl, hb, -⟩ | ⟨x', -, hx⟩
  · exact Or.inl ⟨rfl, hb.symm⟩
  · exact Or.inr ⟨x', hx⟩

end Podc.LimitedUseSnapshots
