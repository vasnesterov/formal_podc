import Papers.PODC2012.LimitedUseSnapshots.PresBasic

/-!
# Preservation of the invariant: invocations and responses
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-! ### History helpers -/

lemma HFacts.append {α : List (Label P maxArrObj)} {y : OpId P} {r : ℕ × ℕ}
    (h : HFacts T α y r) (δ : List (Label P maxArrObj)) : HFacts T (α ++ δ) y r := by
  obtain ⟨⟨β, γ, h1, h2, h3⟩, α', h4, h5, h6, h7⟩ := h
  exact ⟨⟨β, γ, h1.trans (List.prefix_append _ _), h2, h3⟩, α', h4.trans (List.prefix_append _ _),
    h5, h6, h7⟩

/-- Completed operations and their data do not change when a non-response is appended. -/
lemma data_of_not_ret {α : List (Label P maxArrObj)} (hwf : WellFormed α)
    {ℓ : Label P maxArrObj} (hℓ : ∀ p r, ℓ ≠ .ret p r) {y : OpId P} {o : MAOp} {r : ℕ × ℕ}
    (ho : opOf (α ++ [ℓ]) y = some o) (hr : respOf (α ++ [ℓ]) y = some r) :
    opOf α y = some o ∧ respOf α y = some r := by
  rw [respOf_append_of_not_ret hℓ] at hr
  have hc : Completed α y := Completed.of_respOf_eq_some hr
  rw [opOf_append_of_invoked (hwf.invoked_of_completed hc)] at ho
  exact ⟨ho, hr⟩

lemma contribOf_append_of_completed {α : List (Label P maxArrObj)} (hwf : WellFormed α)
    {y : OpId P} (hc : Completed α y) (δ : List (Label P maxArrObj)) :
    contribOf (α ++ δ) y = contribOf α y := by
  simp [contribOf, opOf_append_of_invoked (hwf.invoked_of_completed hc),
    respOf_append_of_completed hc]

/-- The current operation of a process with a `CurInv` record. -/
lemma CurInv.curOp {α : List (Label P maxArrObj)} (hwf : WellFormed α) {p : P} {o : MAOp}
    {Q : List (Label P maxArrObj) → Cfg P → Prop} (h : CurInv T α p o Q) :
    ∃ β γ D, α = β ++ .inv p o :: γ ∧ (alg P T true).run β = some D ∧ Q β D ∧
      (respsOf α p).length = (opsOf β p).length ∧ opOf α (curOp α p) = some o := by
  obtain ⟨β, γ, D, rfl, hγ, hD, hQ⟩ := h
  have hops : opsOf γ p = [] := by
    simp only [opsOf, List.filterMap_eq_nil_iff]
    intro ℓ hℓ
    by_cases hp : ℓ.proc = p
    · rw [hγ ℓ hℓ hp]; rfl
    · exact Label.invOf_eq_none_of_proc_ne hp
  have hresps : respsOf γ p = [] := by
    simp only [respsOf, List.filterMap_eq_nil_iff]
    intro ℓ hℓ
    by_cases hp : ℓ.proc = p
    · rw [hγ ℓ hℓ hp]; rfl
    · exact Label.retOf_eq_none_of_proc_ne hp
  have hwfβ := (hwf β (.inv p o) γ rfl p).1 (by simp)
  have hlen : (respsOf (β ++ .inv p o :: γ) p).length = (opsOf β p).length := by
    simp [respsOf_append, hresps, hwfβ]
  refine ⟨β, γ, D, rfl, hD, hQ, hlen, ?_⟩
  simp only [hlen, opOf, opsOf_append, opsOf_cons, Label.invOf_inv, ↓reduceIte,
    Option.toList_some, hops]
  simp

/-! ### Invocations -/

lemma inv_step_inv {α : List (Label P maxArrObj)} {C C' : Cfg P} {p : P} {o : MAOp}
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hs : (alg P T true).step C (.inv p o) = some C') : Inv T (α ++ [.inv p o]) C' := by
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  obtain ⟨hpend, hallow, rfl⟩ := step_inv_cases T hs
  have hf := frameOK_inv (C := C) (p := p) (o := o)
  have hℓ : ∀ q r, (Label.inv p o : Label P maxArrObj) ≠ .ret q r := by simp
  refine ⟨fun q => ?_, hI.g1, fun c hc => (hI.q c hc).append _,
    fun a ha => ?_, fun h => (hI.w h).imp fun _ h => h.append _, fun y hy => ?_,
    fun y r hy hr => ?_, fun y r hy hr => ?_, fun y o' r hy hr => ?_⟩
  · by_cases hqp : q = p
    · subst hqp
      cases o with
      | upd0 v =>
        rw [pinv_iff T (l := .d0 v []) (by simp [invokeLoc])]
        exact ⟨by simp, hallow, List.nil_prefix, curInv_new hrun (by simp)⟩
      | upd1 v =>
        rw [pinv_iff T (l := .w1 v) (by simp [invokeLoc])]
        exact ⟨by simp, curInv_new hrun trivial⟩
      | scan =>
        rw [pinv_iff T (l := .s1 false []) (by simp [invokeLoc])]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; exact ⟨by simp, curInv_new hrun ⟨by simp, le_rfl⟩⟩
        · intro h; cases h
        · exact Shape.isAddr_nil T
        · intro h; cases h
        · exact rightDom_nil _
        · intro u x hu; cases u <;> simp at hu
        · intro x hx; cases hx
        · rintro ⟨u, x, hu⟩; cases u <;> simp at hu
    · exact (hI.pinv q).frame T hf hqp rfl
  · obtain ⟨pU, v, h1, h2⟩ := hI.fs a ha
    exact ⟨pU, v, h1.append _, h2⟩
  · rw [completed_append_of_not_ret hℓ] at hy
    rw [contribOf_append_of_completed hwf hy]; exact hI.comp y hy
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact (hI.compScan y r h1 h2).frame T hf
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact (hI.hist y r h1 h2).append T _
  · obtain ⟨h1, h2⟩ := data_of_not_ret hwf hℓ hy hr
    exact hI.resp0 y o' r h1 h2

/-! ### Responses -/

lemma data_append_ret {α : List (Label P maxArrObj)} {p : P} {r : ℕ × ℕ} {y : OpId P}
    {o : MAOp} {s : ℕ × ℕ} (ho : opOf (α ++ [.ret p r]) y = some o)
    (hs : respOf (α ++ [.ret p r]) y = some s) :
    (opOf α y = some o ∧ respOf α y = some s) ∨ (y = curOp α p ∧ s = r ∧ opOf α y = some o) := by
  rw [opOf_concat_of_ne (by simp)] at ho
  rcases respOf_concat_cases hs with h | ⟨h1, h2⟩
  · exact Or.inl ⟨ho, h⟩
  · simp only [Label.ret.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr ⟨by ext <;> simp [h2], rfl, ho⟩

/-- The invariant after a response, from the facts about the returning operation. -/
lemma inv_step_ret_core {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {r : ℕ × ℕ}
    {o : MAOp} (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hpend : C.pend p = some o)
    (hcur : CurInv T α p o (fun β _ => o = .scan → SeenLE β r))
    (hcomp : CompFacts T C (o.contrib r))
    (hscan : o = .scan → CompScan T C r ∧
      (0 < r.1 → ∃ pU, InvBefore T α pU (.upd0 r.1) (fun β _ => SeenLE β r)) ∧
      (0 < r.2 → ∃ pU, InvBefore T α pU (.upd1 r.2) (fun β _ => SeenLE β r)))
    (hr0 : o ≠ .scan → r = (0, 0)) :
    Inv T (α ++ [.ret p r])
      ⟨Function.update C.loc p .idle, Function.update C.pend p none, C.mem⟩ := by
  have hwf : WellFormed α := Impl.Valid.wellFormed _ ⟨C, hrun⟩
  have hf := frameOK_ret (C := C) (p := p)
  obtain ⟨β, γ, D, hαβ, hD, hQ, hlen, hop⟩ := hcur.curOp T hwf
  refine ⟨fun q => ?_, hI.g1, fun c hc => (hI.q c hc).append _,
    fun a ha => ?_, fun h => (hI.w h).imp fun _ h => h.append _, fun y hy => ?_,
    fun y s hy hs => ?_, fun y s hy hs => ?_, fun y o' s hy hs => ?_⟩
  · by_cases hqp : q = p
    · subst hqp
      rw [pinv_iff T (l := .idle) (by simp)]
      simp [PInvL]
    · exact (hI.pinv q).frame T hf hqp rfl
  · obtain ⟨pU, v, h1, h2⟩ := hI.fs a ha
    exact ⟨pU, v, h1.append _, h2⟩
  · rcases (completed_append_ret y).1 hy with hy | rfl
    · rw [contribOf_append_of_completed hwf hy]; exact hI.comp y hy
    · have : contribOf (α ++ [.ret p r]) (curOp α p) = o.contrib r := by
        simp [contribOf, opOf_append_of_eq_some hop, respOf_append_ret]
      rw [this]; exact hcomp
  · rcases data_append_ret hy hs with ⟨h1, h2⟩ | ⟨rfl, rfl, h⟩
    · exact (hI.compScan y s h1 h2).frame T hf
    · rw [hop] at h; cases h
      exact (hscan rfl).1.frame T hf
  · rcases data_append_ret hy hs with ⟨h1, h2⟩ | ⟨rfl, rfl, h⟩
    · exact (hI.hist y s h1 h2).append T _
    · rw [hop] at h; cases h
      obtain ⟨-, h3a, h3b⟩ := hscan rfl
      refine ⟨⟨β, γ ++ [.ret p s], by rw [hαβ]; simp, hlen.symm, hQ rfl⟩, α,
        List.prefix_append _ _, ?_, h3a, h3b⟩
      simp [Completed]
  · rcases data_append_ret hy hs with ⟨h1, h2⟩ | ⟨rfl, rfl, h⟩
    · exact hI.resp0 y o' s h1 h2
    · rw [hop] at h; cases h; exact hr0

lemma good1_zero (C : Cfg P) : Good1 T C 0 :=
  ⟨T.addr 0, ⟨Shape.isAddr_addr T 0, Shape.subD_addr T 0⟩,
    fun u x h => absurd h (Shape.addr_zero_noTrue T u x), Nat.zero_le _⟩

lemma CompScan.compFacts {C : Cfg P} (hg : ∀ a b, sc C (a ++ [b]) ≤ sc C a) {r : ℕ × ℕ}
    (h : CompScan T C r) : CompFacts T C r := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨fun ℓ hℓ hl => ?_, ?_, ⟨T.addr r.1, ⟨Shape.isAddr_addr T _, Shape.subD_addr T _⟩, h2, h3⟩⟩
  · have := Shape.lo_le_lo_of_rightDom_leftDom (Shape.isAddr_addr T r.1) hℓ.1
      (Shape.subD_addr T r.1) hℓ.2 h2 hl
    rwa [Shape.lo_addr T r.1 h1] at this
  · exact h3.trans (by simpa using sc_append_le hg [] (T.addr r.1))

lemma pend_ne_none_of_pinv_idle {α : List (Label P maxArrObj)} {C : Cfg P} {p : P}
    (h : PInv T α C p) (hl : C.loc p = .idle) : C.pend p = none := by
  rw [pinv_iff T hl] at h; exact h

/-- Responses preserve the invariant. -/
lemma inv_step_ret {α : List (Label P maxArrObj)} {C C' : Cfg P} {p : P} {r : ℕ × ℕ}
    (hI : Inv T α C) (hrun : (alg P T true).run α = some C)
    (hs : (alg P T true).step C (.ret p r) = some C') : Inv T (α ++ [.ret p r]) C' := by
  obtain ⟨hpend, hR, rfl⟩ := step_ret_cases T hs
  have hP := hI.pinv p
  cases hR with
  | idle hl => exact absurd (pend_ne_none_of_pinv_idle T hP hl) hpend
  | d0 v a n hl hleaf hdr hpre =>
    rw [pinv_iff T hl] at hP
    obtain ⟨h1, h2, h3, h4⟩ := hP
    have hB : Below T C [] v :=
      (below_of_leaf (hpre h2 h3) hleaf).nil_of_noTrue (deepRight_eq_none hdr)
    refine inv_step_ret_core T hI hrun h1 (h4.mono fun _ _ _ h => by cases h)
      ⟨fun ℓ hℓ hl => hB.le_lo h2 hℓ hl, Nat.zero_le _, good1_zero T C⟩ (fun h => by cases h)
      (fun _ => rfl)
  | up v a hl hdr =>
    rw [pinv_iff T hl] at hP
    obtain ⟨h1, h2, h3, h4, h5⟩ := hP
    have hB : Below T C [] v := h4.nil_of_noTrue (deepRight_eq_none hdr)
    refine inv_step_ret_core T hI hrun h1 (h5.mono fun _ _ _ h => by cases h)
      ⟨fun ℓ hℓ hl => hB.le_lo h2 hℓ hl, Nat.zero_le _, good1_zero T C⟩ (fun h => by cases h)
      (fun _ => rfl)
  | rt r hl =>
    rw [pinv_iff T hl] at hP
    rcases hP with ⟨h1, h2, h3, h4, h5⟩ | ⟨v, h1, rfl, h3, h4, h5⟩
    · exact inv_step_ret_core T hI hrun h1 (h2.mono fun _ _ h _ => h) (h5.compFacts T hI.g1)
        (fun _ => ⟨h5, h3, h4⟩) (fun h => absurd rfl h)
    · exact inv_step_ret_core T hI hrun h1 (h5.mono fun _ _ _ h => by cases h)
        ⟨fun _ _ _ => Nat.zero_le _, h4, h3⟩ (fun h => by cases h) (fun _ => rfl)

end Podc.LimitedUseSnapshots
