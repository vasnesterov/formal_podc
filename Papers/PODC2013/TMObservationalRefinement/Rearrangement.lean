import Papers.PODC2013.TMObservationalRefinement.Trace

/-!
# Lemma 17 (Rearrangement) and Lemma 22

`rearrangement` is Lemma 17 for the repaired definitions (Definitions 2 and 12): a well-formed
trace `τH` whose history `H` is in the opacity relation with `S` can be rearranged into a trace
`τS` with history `S` that is observationally equivalent to `τH`. The proof follows the paper:
`rearrange_step` is Lemma 22 (Cases I and II of the paper), iterated by induction on `S`
(the paper's induction on `i`); a common prefix `pre` plays the role of the paper's `τ₁`.

`lemma_17_false_literal`: with Definition 2 as printed (`txcommit` not required to be inside a
transaction), Lemma 17 is false: two pending `txcommit`s of different threads, outside any
transaction, can be swapped by `⊑` but not by `∼`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act

variable {T O M C : Type} [DecidableEq T]

lemma history_eq_append_cons {τ : List (Act T O M C)} {A B : List (IAct T O M)} {ψ : IAct T O M}
    (h : history τ = A ++ ψ :: B) :
    ∃ τ₃ τ₄, τ = τ₃ ++ iface ψ.1 ψ.2 :: τ₄ ∧ history τ₃ = A ∧ history τ₄ = B := by
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.mp h
  obtain ⟨l₃, a, l₄, rfl, h3, h4, h5⟩ := List.filterMap_eq_cons_iff.mp h2
  have ha : a = iface ψ.1 ψ.2 := by cases a <;> simp [Act.toI] at h4; subst h4; rfl
  subst ha
  refine ⟨l₁ ++ l₃, l₄, by simp, ?_, h5⟩
  simp only [history, List.filterMap_append] at h1 ⊢
  rw [h1, List.filterMap_eq_nil_iff.mpr h3]; simp

lemma tproj_map_fst (L : List (Act T O M C × Bool)) (u : T) :
    tproj u (L.map Prod.fst) = (L.filter (fun p => p.1.thread = u)).map Prod.fst := by
  simp only [tproj, List.filter_map]; rfl

lemma filter_map_fst (L : List (Act T O M C × Bool)) (q : Act T O M C → Bool) :
    (L.filter (fun p => q p.1)).map Prod.fst = (L.map Prod.fst).filter q := by
  simp only [List.filter_map]; rfl

/-- A list in which `true` flags never precede `false` flags is its `false` part followed by
its `true` part. -/
lemma filter_false_append_true : ∀ (L : List (Act T O M C × Bool)),
    L.Pairwise (fun x y => x.2 = true → y.2 = true) →
    L.filter (fun p => !p.2) ++ L.filter (fun p => p.2) = L
  | [], _ => rfl
  | (a, b) :: L, h => by
    rw [List.pairwise_cons] at h
    cases b with
    | false => simp [List.filter_cons, filter_false_append_true L h.2]
    | true =>
      have h1 : L.filter (fun p => !p.2) = [] := List.filter_eq_nil_iff.mpr (fun x hx => by
        simp [h.1 x hx rfl])
      have h2 : L.filter (fun p => p.2) = L := List.filter_eq_self.mpr (fun x hx => h.1 x hx rfl)
      simp [List.filter_cons, h1, h2]

lemma stAfter_of_no_iface (st : T → Bool) (t : T) (l : List (Act T O M C))
    (hl : ∀ x ∈ l, x.thread = t → x.toI = none) : stAfter st l t = st t := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    simp only [stAfter_cons]
    rw [ih _ (fun x hx => hl x (by simp [hx]))]
    by_cases ha : a.thread = t
    · have := hl a (by simp) ha
      cases a with
      | iface u k => simp [Act.toI] at this
      | cmd u c => rfl
    · exact upd_apply_of_ne st a ha

lemma ann_all_true (u : T) : ∀ (st : T → Bool) (l : List (Act T O M C)),
    st u = true → (∀ x ∈ l, x.isEndA = false) → (∀ x ∈ l, x.thread = u) →
    ∀ y ∈ ann st l, y.2 = true
  | _, [], _, _, _ => by simp
  | st, a :: l, hst, hE, hT => by
    have ha := hT a (by simp)
    have haE := hE a (by simp)
    have hupd : upd st a u = true := by
      cases a with
      | cmd => simpa [upd] using hst
      | iface w k => simp at ha; subst ha; cases k <;> simp_all [upd, Act.isEndA, isEnd]
    intro y hy
    simp only [ann_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp only [flag]; rw [ha, hst]; simp
    · exact ann_all_true u _ l hupd (fun x hx => hE x (by simp [hx]))
        (fun x hx => hT x (by simp [hx])) y hy

/-- Without `committed`/`aborted` actions, flags of a single thread are monotone. -/
lemma ann_mono (u : T) : ∀ (st : T → Bool) (l : List (Act T O M C)),
    (∀ x ∈ l, x.isEndA = false) → (∀ x ∈ l, x.thread = u) →
    (ann st l).Pairwise (fun x y => x.2 = true → y.2 = true)
  | _, [], _, _ => by simp
  | st, a :: l, hE, hT => by
    have ha := hT a (by simp)
    have haE := hE a (by simp)
    simp only [ann_cons, List.pairwise_cons]
    refine ⟨fun y hy hf => ?_, ann_mono u _ l (fun x hx => hE x (by simp [hx]))
      (fun x hx => hT x (by simp [hx]))⟩
    have hupd : upd st a u = true := by
      cases a with
      | cmd w c => simp [flag, Act.isBoundA] at hf; simp [upd, ← ha, hf]
      | iface w k =>
        simp at ha; subst ha
        cases k <;> simp_all [upd, flag, Act.isEndA, Act.isBoundA, isEnd, isBound]
    exact ann_all_true u _ l hupd (fun x hx => hE x (by simp [hx]))
      (fun x hx => hT x (by simp [hx])) y hy

lemma history_map_eq_nil (L : List (Act T O M C × Bool)) (h : ∀ p ∈ L, p.1.toI = none) :
    history (L.map Prod.fst) = [] := by
  simp only [history, List.filterMap_map]
  exact List.filterMap_eq_nil_iff.mpr (fun p hp => h p hp)

lemma history_map_filter (L : List (Act T O M C × Bool)) (q : Act T O M C × Bool → Bool)
    (h : ∀ p ∈ L, q p = false → p.1.toI = none) :
    history ((L.filter q).map Prod.fst) = history (L.map Prod.fst) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have ih := ih (fun r hr => h r (by simp [hr]))
    by_cases hq : q p = true
    · simp [List.filter_cons, hq, history, List.filterMap_cons] at ih ⊢; rw [ih]
    · have hn := h p (by simp) (by simpa using hq)
      simp [List.filter_cons, hq, history, List.filterMap_cons, hn] at ih ⊢; rw [ih]

lemma filter_comm' {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).filter q = (l.filter q).filter p := by
  simp only [List.filter_filter]
  apply List.filter_congr; intro x _; exact Bool.and_comm _ _

variable [CmdClass T C]

/-- **Lemma 22** (one rearrangement step), for the repaired definitions. Here `pre ++ τ₃` is the
paper's `τ₁ τ₃` and `(t, k)` is `ψ`; Case I is `k ≠ txbegin`, Case II is `k = txbegin`. -/
theorem rearrange_step {pre τ₃ τ₄ : List (Act T O M C)} {t : T} {k : IKind O M}
    (hwf : WFTrace (pre ++ (τ₃ ++ iface t k :: τ₄)))
    (hA : ∀ a ∈ history τ₃, ¬ Constrained a (t, k)) :
    ∃ ρ ρ', history ρ = [(t, k)] ∧ history ρ' = history τ₃ ++ history τ₄ ∧
      ObsEq (pre ++ (τ₃ ++ iface t k :: τ₄)) (pre ++ (ρ ++ ρ')) := by
  have hwf' : WFTrace ((pre ++ τ₃) ++ iface t k :: τ₄) := by simpa using hwf
  obtain ⟨st, hst⟩ : ∃ st, stAfter (fun _ => false) pre = st := ⟨_, rfl⟩
  -- facts about `τ₃`
  have hnoT : ∀ x ∈ τ₃, x.thread = t → x.toI = none := by
    intro x hx hxt
    cases x with
    | cmd => rfl
    | iface u k' =>
      simp at hxt; subst hxt
      exact absurd (Or.inl rfl) (hA (u, k') (by
        simp only [history]; exact List.mem_filterMap.mpr ⟨_, hx, rfl⟩))
  have hs3 : stAfter st τ₃ t = st t := stAfter_of_no_iface st t τ₃ hnoT
  have hstk : st t = !k.isTxbegin := by
    rw [← hs3, ← hst, ← stAfter_append]; exact hwf'.st_before_iface
  have hb : flag (stAfter st τ₃) (iface t k : Act T O M C) = true := by
    have := hwf'.flag_iface; rwa [stAfter_append, hst] at this
  obtain ⟨L3, hL3⟩ : ∃ L, ann st τ₃ = L := ⟨_, rfl⟩
  obtain ⟨L4, hL4⟩ : ∃ L, ann (upd (stAfter st τ₃) (iface t k : Act T O M C)) τ₄ = L := ⟨_, rfl⟩
  have hL : ann st (τ₃ ++ iface t k :: τ₄) = L3 ++ ((iface t k : Act T O M C), true) :: L4 := by
    rw [ann_append, ann_cons, hb, hL3, hL4]
  have hm3 : L3.map Prod.fst = τ₃ := by rw [← hL3, map_fst_ann]
  have hm4 : L4.map Prod.fst = τ₄ := by rw [← hL4, map_fst_ann]
  have hmem : ∀ p ∈ L3, p.1 ∈ τ₃ := fun p hp => by rw [← hm3]; exact List.mem_map_of_mem hp
  -- interface actions of `τ₃` are transactional
  have hI : ∀ p ∈ L3, p.2 = false → p.1.toI = none := by
    rintro ⟨x, f⟩ hp hf
    rw [← hL3] at hp
    obtain ⟨l₁, l₂, rfl, rfl⟩ := (mem_ann_iff st τ₃ x f).mp hp
    cases x with
    | cmd => rfl
    | iface u k' =>
      have hw : WFTrace ((pre ++ l₁) ++ iface u k' :: (l₂ ++ iface t k :: τ₄)) := by simpa using hwf
      have := hw.flag_iface; rw [stAfter_append, hst] at this; simp [this] at hf
  -- actions of thread `t` in `τ₃` are commands with flag `st t`
  have hT : ∀ p ∈ L3, p.1.thread = t → p.2 = st t := by
    rintro ⟨x, f⟩ hp hx
    rw [← hL3] at hp
    obtain ⟨l₁, l₂, rfl, rfl⟩ := (mem_ann_iff st _ x f).mp hp
    have hn := hnoT x (by simp) hx
    cases x with
    | iface => simp [Act.toI] at hn
    | cmd u c =>
      simp at hx; subst hx
      simp only [flag, Act.isBoundA, Bool.false_or, Act.thread_cmd]
      exact stAfter_of_no_iface st u l₁ (fun y hy => hnoT y (by simp [hy]))
  -- the generic conclusion
  have finish : ∀ L' : List (Act T O M C × Bool),
      (∀ u, L'.filter (fun p => p.1.thread = u) =
        (L3 ++ ((iface t k : Act T O M C), true) :: L4).filter (fun p => p.1.thread = u)) →
      L'.filter (fun p => !p.2) = (L3 ++ ((iface t k : Act T O M C), true) :: L4).filter
        (fun p => !p.2) →
      ObsEq (pre ++ (τ₃ ++ iface t k :: τ₄)) (pre ++ L'.map Prod.fst) := by
    intro L' hp hn
    rw [← hL] at hp hn
    have hann := ann_eq_of_perThread st _ L' hp
    refine obsEq_append_of pre _ _ (fun u => ?_) ?_
    · conv_lhs => rw [← map_fst_ann st (τ₃ ++ iface t k :: τ₄)]
      rw [tproj_map_fst, tproj_map_fst, hp]
    · rw [hst]; simp only [nontransFrom]; rw [hann, hn]
  by_cases hk : k.isTxbegin = true
  · -- Case II: `ψ = (t, txbegin)`
    have hk' : k = txbegin := by cases k <;> simp_all [isTxbegin]
    subst hk'
    have hstf : st t = false := by simpa [isTxbegin] using hstk
    have hE : ∀ x ∈ τ₃, x.isEndA = false := by
      intro x hx
      cases x with
      | cmd => rfl
      | iface u k' =>
        by_contra hc
        exact hA (u, k') (by simp only [history]; exact List.mem_filterMap.mpr ⟨_, hx, rfl⟩)
          (Or.inr ⟨by simpa [Act.isEndA] using hc, rfl⟩)
    refine ⟨(L3.filter (fun p => !p.2)).map Prod.fst ++ [iface t txbegin],
      (L3.filter (fun p => p.2)).map Prod.fst ++ τ₄, ?_, ?_, ?_⟩
    · rw [history_append, history_map_eq_nil _ (fun p hp => by
        simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
        exact hI p hp.1 hp.2)]
      simp
    · rw [history_append, history_map_filter L3 _ (fun p hp hq => hI p hp hq), hm3]
    · let L' := L3.filter (fun p => !p.2) ++ ((iface t txbegin : Act T O M C), true) ::
        (L3.filter (fun p => p.2) ++ L4)
      have hmap : L'.map Prod.fst = (L3.filter (fun p => !p.2)).map Prod.fst ++
          [iface t txbegin] ++ ((L3.filter (fun p => p.2)).map Prod.fst ++ τ₄) := by
        simp [L', hm4]
      rw [← hmap]
      refine finish L' (fun u => ?_) ?_
      · have hsort := filter_false_append_true (L3.filter (fun p => p.1.thread = u)) (by
          rw [← hL3, ann_tproj]
          exact ann_mono u st _ (fun x hx => hE x (by simp [tproj] at hx; exact hx.1))
            (fun x hx => by simp [tproj] at hx; exact hx.2))
        simp only [L', List.filter_append, List.filter_cons, Act.thread_iface]
        have c1 : (L3.filter (fun p => !p.2)).filter (fun p => p.1.thread = u) =
            (L3.filter (fun p => p.1.thread = u)).filter (fun p => !p.2) := filter_comm' _ _ _
        have c2 : (L3.filter (fun p => p.2)).filter (fun p => p.1.thread = u) =
            (L3.filter (fun p => p.1.thread = u)).filter (fun p => p.2) := filter_comm' _ _ _
        rw [c1, c2]
        by_cases hu : t = u
        · subst hu
          have h0 : (L3.filter (fun p => p.1.thread = t)).filter (fun p => p.2) = [] :=
            List.filter_eq_nil_iff.mpr (fun x hx => by
              simp only [List.mem_filter, decide_eq_true_eq] at hx
              simp [hT x hx.1 hx.2, hstf])
          rw [h0] at hsort ⊢
          simp only [List.append_nil] at hsort
          simp [hsort]
        · simp only [hu, decide_false, Bool.false_eq_true, ite_false]
          rw [← List.append_assoc, hsort]
      · simp [L', List.filter_append, List.filter_cons, List.filter_filter]
  · -- Case I: `ψ ≠ (t, txbegin)`
    have hstt : st t = true := by simpa [hk] using hstk
    refine ⟨(L3.filter (fun p => p.1.thread = t)).map Prod.fst ++ [iface t k],
      (L3.filter (fun p => !(p.1.thread = t))).map Prod.fst ++ τ₄, ?_, ?_, ?_⟩
    · rw [history_append, history_map_eq_nil _ (fun p hp => by
        simp only [List.mem_filter, decide_eq_true_eq] at hp
        exact hnoT p.1 (hmem p hp.1) hp.2)]
      simp
    · rw [history_append, history_map_filter L3 _ (fun p hp hq => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hq
        exact hnoT p.1 (hmem p hp) hq), hm3]
    · let L' := L3.filter (fun p => p.1.thread = t) ++ ((iface t k : Act T O M C), true) ::
        (L3.filter (fun p => !(p.1.thread = t)) ++ L4)
      have hmap : L'.map Prod.fst = (L3.filter (fun p => p.1.thread = t)).map Prod.fst ++
          [iface t k] ++ ((L3.filter (fun p => !(p.1.thread = t))).map Prod.fst ++ τ₄) := by
        simp [L', hm4]
      rw [← hmap]
      refine finish L' (fun u => ?_) ?_
      · simp only [L', List.filter_append, List.filter_cons, Act.thread_iface, List.filter_filter]
        by_cases hu : t = u
        · subst hu
          simp
        · simp only [hu, decide_false, Bool.false_eq_true, ite_false]
          rw [List.filter_eq_nil_iff.mpr (fun x _ => by
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]; intro h1 h2; exact hu (h2 ▸ h1))]
          simp only [List.nil_append]
          congr 1
          apply List.filter_congr; intro x _
          by_cases h : x.1.thread = u
          · simp [h, Ne.symm hu]
          · simp [h]
      · have h1 : (L3.filter (fun p => p.1.thread = t)).filter (fun p => !p.2) = [] :=
          List.filter_eq_nil_iff.mpr (fun x hx => by
            simp only [List.mem_filter, decide_eq_true_eq] at hx; simp [hT x hx.1 hx.2, hstt])
        have h2 : (L3.filter (fun p => !(p.1.thread = t))).filter (fun p => !p.2) =
            L3.filter (fun p => !p.2) := by
          rw [List.filter_filter]
          apply List.filter_congr; intro x hx
          by_cases h : x.1.thread = t
          · simp [h, hT x hx h, hstt]
          · simp [h]
        simp only [L', List.filter_append, List.filter_cons, h1, h2]
        simp

lemma opac_nil_right {H : List (IAct T O M)} (h : Opac H []) : H = [] := by
  obtain ⟨θ, -, -⟩ := h
  have := Fin.equiv_iff_eq.mp ⟨θ⟩
  simpa using this

/-- The rearrangement, generalized to traces with a fixed common prefix `pre`. -/
theorem rearrangement_gen : ∀ (S : List (IAct T O M)) (pre τ : List (Act T O M C)),
    WFTrace (pre ++ τ) → Opac (history τ) S →
    ∃ τ', history τ' = S ∧ ObsEq (pre ++ τ) (pre ++ τ')
  | [], pre, τ, _, h => ⟨τ, opac_nil_right h, ObsEq.refl _⟩
  | ψ :: S, pre, τ, hwf, h => by
    obtain ⟨A, B, hAB, hA, hrest⟩ := h.cons_elim
    obtain ⟨τ₃, τ₄, rfl, h3, h4⟩ := history_eq_append_cons hAB
    obtain ⟨ρ, ρ', hρ, hρ', heq⟩ := rearrange_step (pre := pre) (t := ψ.1) (k := ψ.2) hwf
      (by rw [h3]; exact hA)
    have hwf2 : WFTrace ((pre ++ ρ) ++ ρ') := by
      rw [List.append_assoc]; exact hwf.of_tproj heq.1
    obtain ⟨τ'', h1, h2⟩ := rearrangement_gen S (pre ++ ρ) ρ' hwf2 (by rw [hρ', h3, h4]; exact hrest)
    refine ⟨ρ ++ τ'', by simp [hρ, h1], heq.trans ?_⟩
    simpa [List.append_assoc] using h2

/-- **Lemma 17 (Rearrangement)**, for the repaired Definitions 2 and 12: if `H ⊑ S` and `τH` is a
well-formed trace with history `H`, then there is a well-formed trace `τS` with history `S` and
`τH ∼ τS`. (Well-formedness of `H` and `S` is implied by that of the traces and not needed.) -/
theorem rearrangement {H S : List (IAct T O M)} (hHS : Opac H S) {τH : List (Act T O M C)}
    (hτ : WFTrace τH) (hh : history τH = H) :
    ∃ τS, WFTrace τS ∧ history τS = S ∧ ObsEq τH τS := by
  obtain ⟨τS, h1, h2⟩ := rearrangement_gen S [] τH (by simpa using hτ) (hh ▸ hHS)
  simp only [List.nil_append] at h2
  exact ⟨τS, hτ.of_tproj h2.1, h1, h2⟩

/-- **Lemma 17** in the paper's form (repaired definitions). -/
theorem lemma_17 (H S : List (IAct T O M)) (_hH : WellFormed H) (_hS : WellFormed S)
    (hHS : Opac H S) (τH : List (Act T O M C)) (hτ : WFTrace τH) (hh : history τH = H) :
    ∃ τS, WFTrace τS ∧ history τS = S ∧ ObsEq τH τS :=
  rearrangement hHS hτ hh

/-! ### Lemma 17 is false for Definitions 2 and 12 as printed -/

lemma wfThreadLit_nil : WFThreadLit ([] : List (IKind O M)) :=
  ⟨trivial, trivial, fun l₁ a l₂ h => by simp at h⟩

lemma wfThreadLit_txcommit : WFThreadLit ([txcommit] : List (IKind O M)) := by
  refine ⟨rfl, by simp [List.filter, isBound, TxAlt], ?_⟩
  intro l₁ a l₂ h ha
  rcases l₁ with _ | ⟨b, l₁⟩
  · simp at h; obtain ⟨rfl, -⟩ := h; simp [isCallRet] at ha
  · simp at h

lemma eq_map_history_of_iface {τ : List (Act T O M C)} (h : ∀ x ∈ τ, x.toI.isSome) :
    τ = (history τ).map (fun p => iface p.1 p.2) := by
  induction τ with
  | nil => rfl
  | cons a τ ih =>
    have ha := h a (by simp)
    cases a with
    | cmd => simp [Act.toI] at ha
    | iface u k =>
      have e := ih (fun x hx => h x (by simp [hx]))
      simp only [history_cons_iface, List.map_cons]
      exact congrArg _ e

/-- **Lemma 17 is false as stated** (for Definition 2 as printed, where `txcommit` need not be
inside a transaction, and Definition 12 as printed): with two threads `t₁ ≠ t₂`, the histories
`H = (t₁, txcommit) (t₂, txcommit)` and `S = (t₂, txcommit) (t₁, txcommit)` are well-formed and
`H ⊑ S`, the trace `τH = H` is well-formed, but no trace with history `S` is observationally
equivalent to `τH`: both `txcommit` actions are non-transactional, so `nontrans` fixes their order. -/
theorem lemma_17_false_literal (t₁ t₂ : T) (hne : t₁ ≠ t₂) :
    ¬ ∀ H S : List (IAct T O M), WellFormedLit H → WellFormedLit S → Opac H S →
      ∀ τH : List (Act T O M C), WFTraceLit τH → history τH = H →
        ∃ τS, WFTraceLit τS ∧ history τS = S ∧ ObsEq τH τS := by
  intro hall
  have wf : ∀ a b : T, a ≠ b →
      WellFormedLit ([(a, txcommit), (b, txcommit)] : List (IAct T O M)) := by
    intro a b hab t
    by_cases ha : t = a
    · subst ha; simpa [proj, List.filter_cons, Ne.symm hab] using wfThreadLit_txcommit
    by_cases hb : t = b
    · subst hb; simpa [proj, List.filter_cons, hab] using wfThreadLit_txcommit
    · simpa [proj, List.filter_cons, Ne.symm ha, Ne.symm hb] using wfThreadLit_nil
  have hop : Opac ([(t₁, txcommit), (t₂, txcommit)] : List (IAct T O M))
      [(t₂, txcommit), (t₁, txcommit)] := by
    have h1 : Opac ([(t₁, txcommit)] : List (IAct T O M)) [(t₁, txcommit)] := by
      have := Opac.cons_intro (A := []) (B := []) (S := []) (ψ := ((t₁, txcommit) : IAct T O M))
        (by simp) ((opac_nil_left _).mpr rfl)
      simpa using this
    have := Opac.cons_intro (A := [(t₁, txcommit)]) (B := []) (ψ := ((t₂, txcommit) : IAct T O M))
      (by simp [Constrained, hne, isEnd]) (by simpa using h1)
    simpa using this
  let τH : List (Act T O M C) := [iface t₁ txcommit, iface t₂ txcommit]
  have hτH : WFTraceLit τH := by
    refine ⟨by simpa [τH, history] using wf t₁ t₂ hne, by simp [τH], ?_⟩
    intro τ₁ t c τ₂ h
    rcases τ₁ with _ | ⟨a, _ | ⟨b, τ₁⟩⟩ <;> simp [τH] at h
  obtain ⟨τS, -, hS, hobs⟩ := hall _ _ (wf t₁ t₂ hne) (wf t₂ t₁ (Ne.symm hne)) hop τH hτH
    (by simp [τH, history])
  have hiface : ∀ x ∈ τS, x.toI.isSome := by
    intro x hx
    have : x ∈ tproj x.thread τS := by simp [tproj, hx]
    rw [← hobs.1] at this
    simp only [tproj, τH, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this.1 with rfl | rfl <;> rfl
  have hτS : τS = [iface t₂ txcommit, iface t₁ txcommit] := by
    rw [eq_map_history_of_iface hiface, hS]; rfl
  have := hobs.2
  rw [hτS] at this
  simp [nontrans, nontransFrom, τH, flag, upd, Act.isBoundA, isBound] at this
  exact hne this.1

end Podc.TMObservationalRefinement
