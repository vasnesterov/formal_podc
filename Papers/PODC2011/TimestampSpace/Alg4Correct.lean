import Papers.PODC2011.TimestampSpace.Alg4Inv2
import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Algorithms 3 and 4 are correct (Lemma 6.4)

History invariant `InvH`: every completed `getTS` returned a timestamp `(k, t)` with
`R[k] ≠ ⊥` and all of `R[1..t]` written after `R[k]` became non-`⊥`; a pending `getTS` invoked
after such a `getTS` completed is "on track" to return a larger timestamp (`PcOK`); completed
`getTS`s ordered in real time returned increasing timestamps; `compare` answers by the
lexicographic order.

The proof follows the paper's proof of Lemma 6.4 (via Claims 6.1 and 6.3): if `getTS(p)`
returned `(k, t)` before `getTS(q)` started, then `myrnd_q ≥ k`, and if `myrnd_q = k` then
`getTS(q)` fails every iteration `j ≤ t`, because `R[j]` has been written after `R[k]`
became non-`⊥`, hence after the scan that produced `q`'s copy of `R[k]`, hence (fresh ids) its
last id differs from the one recorded in `r[k].seq[j]`.

No bound on the number of `getTS` calls is needed for correctness (the register array is
unbounded).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- `getTS` of the current process is on track to return a timestamp larger than `(k, t)`. -/
def PcOK : PC P → ℕ × ℕ → Prop
  | .loop k' i _ s, (k, t) => k ≤ k' ∧ (s = .s8 → k < k' ∨ t < i)
  | .scan k', (k, _) => k ≤ k'
  | .fin k' _, (k, _) => k ≤ k'
  | .done (.inl t'), kt => lexLt kt t' = true
  | _, _ => True

/-- The history invariant. -/
structure InvH (α : List (Label P TS)) (C : ACfg P) (G : Gh P) : Prop where
  ts : ∀ g r, opOf α g = some .getTS → respOf α g = some r →
    ∃ k t, r = .inl (k, t) ∧ 1 ≤ k ∧ Rg C k ≠ none ∧ ∀ j, 1 ≤ j → j ≤ t → G.bt k < G.wt j
  pend : ∀ g k t q, opOf α g = some .getTS → respOf α g = some (.inl (k, t)) →
    C.pend q = some .getTS → Precedes α g (q, (C.loc q).cnt) → PcOK (C.loc q).pc (k, t)
  order : ∀ g₁ g₂ t₁ t₂, opOf α g₁ = some .getTS → respOf α g₁ = some (.inl t₁) →
    opOf α g₂ = some .getTS → respOf α g₂ = some (.inl t₂) → Precedes α g₁ g₂ →
    lexLt t₁ t₂ = true
  cmp : ∀ c a b r, opOf α c = some (.compare a b) → respOf α c = some r → r = .inr (lexLt a b)

/-! ### History bookkeeping -/

lemma cur_op {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C)
    (h1 : Inv1 α C) {q : P} {o : TSOp (ℕ × ℕ)} (hp : C.pend q = some o) :
    opOf α (q, (C.loc q).cnt) = some o ∧ Invoked α (q, (C.loc q).cnt) ∧
      ¬ Completed α (q, (C.loc q).cnt) := by
  have hc := h1.cnt q
  have hl := Impl.run_pend _ h hp
  rcases Impl.run_counts _ h q with ⟨h2, -⟩ | ⟨-, h2⟩
  · simp [hp] at h2
  refine ⟨?_, ?_, ?_⟩
  · simp only [opOf]
    rw [List.getLast?_eq_getElem?] at hl
    rw [hc, ← hl]; congr 1; omega
  · simp only [Invoked]; omega
  · simp only [Completed]; omega

lemma opOf_tau {α : List (Label P TS)} {q : P} (g : OpId P) :
    opOf (α ++ [.tau q]) g = opOf α g := by
  simp [opOf, opsOf, List.filterMap_cons]

lemma respOf_tau {α : List (Label P TS)} {q : P} (g : OpId P) :
    respOf (α ++ [.tau q]) g = respOf α g := by
  simp [respOf, respsOf, List.filterMap_cons]

lemma respOf_inv {α : List (Label P TS)} {q : P} {o : TSOp (ℕ × ℕ)} (g : OpId P) :
    respOf (α ++ [.inv q o]) g = respOf α g := by
  simp [respOf, respsOf, List.filterMap_cons]

lemma invoked_of_completed {α : List (Label P TS)} {C : ACfg P}
    (h : (alg4 (P := P)).run α = some C) {g : OpId P} (hc : Completed α g) : Invoked α g := by
  obtain ⟨p, k⟩ := g
  simp only [Completed, Invoked] at *
  rcases Impl.run_counts _ h p with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega

/-! ### Ghost monotonicity -/

lemma gstep_wt_mono {C : ACfg P} {G : Gh P} (hI : Inv2 C G) (ℓ : Label P TS) (j : ℕ) :
    G.wt j ≤ (gstep G C ℓ).wt j := by
  have := hI.wt_le j
  cases ℓ with
  | inv p o => cases o <;> simp [gstep]
  | ret p r => simp [gstep]
  | tau p =>
    simp only [gstep]
    split
    · split <;> simp
    · rw [gwrite_wt]; split_ifs <;> omega
    · rw [gwrite_wt]; split_ifs <;> omega
    · split_ifs <;> simp
    · rw [gwrite_wt]; split_ifs <;> omega
    · simp

lemma gstep_bt {C : ACfg P} {G : Gh P} (ℓ : Label P TS) {k : ℕ} (hk : Rg C k ≠ none) :
    (gstep G C ℓ).bt k = G.bt k := by
  cases ℓ with
  | inv p o => cases o <;> simp [gstep]
  | ret p r => simp [gstep]
  | tau p =>
    simp only [gstep]
    split
    · split <;> simp
    · exact gwrite_bt_of_ne_none hk
    · exact gwrite_bt_of_ne_none hk
    · split_ifs <;> simp
    · exact gwrite_bt_of_ne_none hk
    · simp

lemma lexLt_lt_succ {k k' t : ℕ} (h : k ≤ k') (t' : ℕ) : lexLt (k, t) (k' + 1, t') = true := by
  simp [lexLt]; omega

lemma TauEff.pcOK {q : P} {c : ℕ} {R R' : Mem P} {pc pc' : PC P} {loc : P → Loc P} {G : Gh P}
    {k t : ℕ} (h : TauEff q c R pc pc' R') (hpi1 : PI1 R q ⟨c, pc⟩)
    (hpi2 : PI2 R loc G q ⟨c, pc⟩) (hM : MemOK R) (hRk : R k ≠ none)
    (hst : ∀ j, 1 ≤ j → j ≤ t → G.bt k < G.wt j) (hok : PcOK pc (k, t)) : PcOK pc' (k, t) := by
  cases h with
  | whS _ => trivial
  | @whN j v hx =>
    simp only [PI1] at hpi1
    have hkj : k < j := by
      by_contra hc
      exact hM.contig k j hRk hpi1.1 (by omega) hx
    unfold endWh; split_ifs
    · simp only [PcOK]; exact ⟨by omega, by simp⟩
    · simp only [PcOK]; omega
  | s6N _ => simpa [PcOK] using hok
  | s6S _ => simp only [PcOK] at hok ⊢; exact lexLt_lt_succ hok.1 0
  | @s7T k' i v hx =>
    simp only [PcOK] at hok ⊢
    refine ⟨hok.1, fun _ => ?_⟩
    by_contra hc
    push Not at hc
    have hkk : k = k' := by omega
    subst hkk
    simp only [PI1] at hpi1
    simp only [PI2] at hpi2
    have h3 := hst i hpi1.1 hc.2
    have h4 := hpi2.1.bt hpi1.2.2
    exact hpi2.1.ne i hpi1.1 (by omega) (by omega) hx
  | s7F _ => simpa [PcOK] using hok
  | @s8 k' i v =>
    simp only [PcOK] at hok ⊢
    have h3 : k < k' ∨ t < i := by simpa using hok.2
    simp [lexLt]; omega
  | s10T _ => simpa [PcOK] using hok
  | s10F _ | s11 =>
    simp only [PcOK] at hok
    unfold nextIt; split_ifs
    · simp only [PcOK]; exact ⟨hok.1, by simp⟩
    · simp only [PcOK]; exact hok.1
  | scN _ => simpa [PcOK] using hok
  | scS _ => simp only [PcOK] at hok ⊢; exact lexLt_lt_succ hok 0
  | fin => simp only [PcOK] at hok ⊢; exact lexLt_lt_succ hok 0

lemma respOf_ret {α : List (Label P TS)} {q : P} {r : (ℕ × ℕ) ⊕ Bool} {g : OpId P}
    {r' : (ℕ × ℕ) ⊕ Bool} (h : respOf (α ++ [.ret q r]) g = some r') :
    (g = (q, (respsOf α q).length) ∧ r' = r) ∨ respOf α g = some r' := by
  obtain ⟨p, k⟩ := g
  simp only [respOf, respsOf_append] at h ⊢
  by_cases hk : k < (respsOf α p).length
  · right; rwa [List.getElem?_append_left hk] at h
  · rw [List.getElem?_append_right (by omega)] at h
    by_cases hp : q = p
    · subst hp
      simp only [respsOf, List.filterMap_cons, List.filterMap_nil, Label.retOf_ret,
        ite_true] at h
      rw [List.getElem?_singleton] at h
      split_ifs at h with h5
      · left
        simp only [Option.some.injEq] at h
        refine ⟨?_, h.symm⟩
        simp only [Prod.mk.injEq, true_and]
        simp only [respsOf] at hk h5 ⊢
        omega
    · simp [respsOf, hp] at h

lemma respOf_ret_self {α : List (Label P TS)} {q : P} {r : (ℕ × ℕ) ⊕ Bool} :
    respOf (α ++ [.ret q r]) (q, (respsOf α q).length) = some r := by
  simp [respOf, respsOf]

lemma opOf_ret {α : List (Label P TS)} {q : P} {r : (ℕ × ℕ) ⊕ Bool} (g : OpId P) :
    opOf (α ++ [.ret q r]) g = opOf α g := by
  simp [opOf, opsOf, List.filterMap_cons]

lemma opOf_inv_of_invoked {α : List (Label P TS)} {q : P} {o : TSOp (ℕ × ℕ)} {g : OpId P}
    (h : Invoked α g) : opOf (α ++ [.inv q o]) g = opOf α g :=
  opOf_append_of_invoked h

lemma InvH.init : InvH ([] : List (Label P TS)) (alg4 (P := P)).initCfg Gh.init := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [respOf, Impl.initCfg]

theorem InvH.step {α : List (Label P TS)} {C C' : ACfg P} {G : Gh P} {ℓ : Label P TS}
    (hrun : (alg4 (P := P)).run α = some C) (hs : (alg4 (P := P)).step C ℓ = some C')
    (h1 : Inv1 α C) (h2 : Inv2 C G) (hH : InvH α C G) :
    InvH (α ++ [ℓ]) C' (gstep G C ℓ) := by
  have hrun' : (alg4 (P := P)).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_append_of_eq _ hrun, Impl.runFrom_singleton]; exact hs
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, hpe, hloc, hmem⟩ := step_inv' hs
    have hR : Rg C' = Rg C := by simp [Rg, hmem]
    have hG1 : (gstep G C (.inv q o)).bt = G.bt := by cases o <;> rfl
    have hG2 : (gstep G C (.inv q o)).wt = G.wt := by cases o <;> rfl
    have hop : ∀ g r, respOf (α ++ [.inv q o]) g = some r →
        respOf α g = some r ∧ opOf (α ++ [.inv q o]) g = opOf α g := by
      intro g r hr
      rw [respOf_inv] at hr
      exact ⟨hr, opOf_inv_of_invoked (invoked_of_completed hrun (Completed.of_respOf_eq_some hr))⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g r hg hr
      obtain ⟨hr', ho⟩ := hop g r hr
      rw [ho] at hg
      rw [hR, hG1, hG2]; exact hH.ts g r hg hr'
    · intro g k t q' hg hr hq' hpr
      obtain ⟨hr', ho⟩ := hop g _ hr
      rw [ho] at hg
      by_cases hqq : q' = q
      · subst hqq
        rw [hloc, Function.update_self]
        rw [hpe, Function.update_self] at hq'
        simp only [Option.some.injEq] at hq'; subst hq'
        simp [alg4, PcOK]
      · rw [hpe, Function.update_of_ne hqq] at hq'
        rw [hloc, Function.update_of_ne hqq] at hpr ⊢
        exact hH.pend g k t q' hg hr' hq'
          (hpr.of_append_of_invoked (cur_op hrun h1 hq').2.1)
    · intro g₁ g₂ t₁ t₂ hg₁ hr₁ hg₂ hr₂ hpr
      obtain ⟨hr₁', ho₁⟩ := hop g₁ _ hr₁
      obtain ⟨hr₂', ho₂⟩ := hop g₂ _ hr₂
      rw [ho₁] at hg₁; rw [ho₂] at hg₂
      exact hH.order g₁ g₂ t₁ t₂ hg₁ hr₁' hg₂ hr₂'
        (hpr.of_append_of_invoked (invoked_of_completed hrun (Completed.of_respOf_eq_some hr₂')))
    · intro c a b r hc hr
      obtain ⟨hr', ho⟩ := hop c _ hr
      rw [ho] at hc
      exact hH.cmp c a b r hc hr'
  | ret q r =>
    obtain ⟨h0, hpe, hmem, h3⟩ := step_ret' hs
    rcases h3 with ⟨hpc, hloc⟩ | hpc
    swap
    · exact absurd ((h1.idle q).2 hpc) h0
    have hR : Rg C' = Rg C := by simp [Rg, hmem]
    have hG1 : (gstep G C (.ret q r)).bt = G.bt := rfl
    have hG2 : (gstep G C (.ret q r)).wt = G.wt := rfl
    obtain ⟨o₀, ho₀⟩ := Option.ne_none_iff_exists'.1 h0
    obtain ⟨hcur, hinv, hncomp⟩ := cur_op hrun h1 ho₀
    have hcq := h1.cnt q
    -- the newly completed operation
    set g₀ : OpId P := (q, (C.loc q).cnt) with hg₀
    have hnew : ∀ g r', respOf (α ++ [.ret q r]) g = some r' →
        (g = g₀ ∧ r' = r) ∨ respOf α g = some r' := by
      intro g r' h; rw [hg₀, hcq]; exact respOf_ret h
    have hr₀ : respOf (α ++ [.ret q r]) g₀ = some r := by rw [hg₀, hcq]; exact respOf_ret_self
    have hold : ∀ g x, Precedes (α ++ [.ret q r]) g x → Invoked α x → Precedes α g x ∧ g ≠ g₀ := by
      intro g x h hx
      have h4 := h.of_append_of_invoked hx
      refine ⟨h4, ?_⟩
      rintro rfl; exact hncomp h4.completed
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g r' hg hr'
      rw [opOf_ret] at hg
      rw [hR, hG1, hG2]
      rcases hnew g r' hr' with ⟨rfl, h7⟩ | h4
      · rw [h7]
        rw [hcur] at hg
        simp only [Option.some.injEq] at hg; subst hg
        have h5 := h1.pi q
        have h6 := h2.pi q
        rcases r with ⟨k, t⟩ | b
        · simp only [PI1, hpc] at h5
          simp only [PI2, hpc] at h6
          exact ⟨k, t, rfl, h5.1, h5.2, h6⟩
        · exact absurd hpc (h1.gts q b ho₀)
      · exact hH.ts g r' hg h4
    · intro g k t q' hg hr hq' hpr
      rw [opOf_ret] at hg
      have hqq : q' ≠ q := by
        rintro rfl; rw [hpe, Function.update_self] at hq'; simp at hq'
      rw [hpe, Function.update_of_ne hqq] at hq'
      rw [hloc, Function.update_of_ne hqq] at hpr ⊢
      obtain ⟨hpr', hne⟩ := hold g _ hpr (cur_op hrun h1 hq').2.1
      rcases hnew g _ hr with ⟨h4, -⟩ | h4
      · exact absurd h4 hne
      · exact hH.pend g k t q' hg h4 hq' hpr'
    · intro g₁ g₂ t₁ t₂ hg₁ hr₁ hg₂ hr₂ hpr
      rw [opOf_ret] at hg₁ hg₂
      rcases hnew g₂ _ hr₂ with ⟨rfl, h4⟩ | h4
      · -- `g₂` is the newly completed operation
        obtain ⟨hpr', hne⟩ := hold g₁ _ hpr hinv
        rcases hnew g₁ _ hr₁ with ⟨h5, -⟩ | h5
        · exact absurd h5 hne
        rw [hcur] at hg₂
        obtain ⟨k, t⟩ := t₁
        have := hH.pend g₁ k t q hg₁ h5 (by rw [ho₀, hg₂]) hpr'
        rw [hpc, ← h4] at this
        exact this
      · obtain ⟨hpr', hne⟩ := hold g₁ _ hpr (invoked_of_completed hrun (Completed.of_respOf_eq_some h4))
        rcases hnew g₁ _ hr₁ with ⟨h5, -⟩ | h5
        · exact absurd h5 hne
        exact hH.order g₁ g₂ t₁ t₂ hg₁ h5 hg₂ h4 hpr'
    · intro c a b r' hc hr'
      rw [opOf_ret] at hc
      rcases hnew c _ hr' with ⟨rfl, rfl⟩ | h4
      · rw [hcur] at hc
        simp only [Option.some.injEq] at hc; subst hc
        have := h1.cmp q a b ho₀
        rw [hpc] at this
        simp only [PC.done.injEq] at this
        exact this
      · exact hH.cmp c a b r' hc h4
  | tau q =>
    obtain ⟨pc', h0, hpe, hloc, hT⟩ := tau_step hs
    have hpi1 := h1.pi q
    have hpi2 := h2.pi q
    have hmono := hT.mono
    have hprec : ∀ g x, Precedes (α ++ [.tau q]) g x → Invoked α x → Precedes α g x :=
      fun g x h hx => h.of_append_of_invoked hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g r hg hr
      rw [opOf_tau] at hg; rw [respOf_tau] at hr
      obtain ⟨k, t, hr1, hk, hRk, hst⟩ := hH.ts g r hg hr
      refine ⟨k, t, hr1, hk, hmono k hRk, fun j h3 h4 => ?_⟩
      rw [gstep_bt _ hRk]
      exact (hst j h3 h4).trans_le (gstep_wt_mono h2 _ j)
    · intro g k t q' hg hr hq' hpr
      rw [opOf_tau] at hg; rw [respOf_tau] at hr
      rw [hpe] at hq'
      have hpr' := hprec g _ hpr (by
        rw [hloc]
        by_cases hqq : q' = q
        · subst hqq; simpa using (cur_op hrun h1 hq').2.1
        · rw [Function.update_of_ne hqq]; exact (cur_op hrun h1 hq').2.1)
      by_cases hqq : q' = q
      · subst hqq
        rw [hloc, Function.update_self] at hpr' ⊢
        simp only at hpr' ⊢
        obtain ⟨k', t', hr1, hk, hRk, hst⟩ := hH.ts g _ hg hr
        simp only [Sum.inl.injEq, Prod.mk.injEq] at hr1
        obtain ⟨rfl, rfl⟩ := hr1
        have hok := hH.pend g k t q' hg hr hq' hpr'
        generalize hl : C.loc q' = l at hpi1 hpi2 hT hok
        obtain ⟨c, pc⟩ := l
        exact hT.pcOK hpi1 hpi2 h1.mem hRk hst hok
      · rw [hloc, Function.update_of_ne hqq] at hpr' ⊢
        exact hH.pend g k t q' hg hr hq' hpr'
    · intro g₁ g₂ t₁ t₂ hg₁ hr₁ hg₂ hr₂ hpr
      rw [opOf_tau] at hg₁ hg₂; rw [respOf_tau] at hr₁ hr₂
      exact hH.order g₁ g₂ t₁ t₂ hg₁ hr₁ hg₂ hr₂
        (hprec _ _ hpr (invoked_of_completed hrun (Completed.of_respOf_eq_some hr₂)))
    · intro c a b r hc hr
      rw [opOf_tau] at hc; rw [respOf_tau] at hr
      exact hH.cmp c a b r hc hr

theorem invH_of_run {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    InvH α C (ghostOf α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; exact InvH.init
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := run_append_singleton h
    rw [ghostOf_append h₀ hs]
    exact (ih h₀).step h₀ hs (inv1_of_run h₀) (inv2_of_run h₀) |> fun h => by
      simpa using h

/-- **Lemma 6.4** (correctness of Algorithms 3 and 4): every execution of the implementation
satisfies the timestamp specification `TSCorrect` — for any number of `getTS` calls (the register
array is unbounded; the bound `M` only matters for the space). -/
theorem alg4_correct (α : List (Label P TS)) (hα : (alg4 (P := P)).Valid α) : TSCorrect α := by
  obtain ⟨C, hC⟩ := hα
  have hH := invH_of_run hC
  refine ⟨fun g r hg hr => ?_, fun g₁ g₂ c t₁ t₂ o r hg₁ hr₁ hg₂ hr₂ h12 h2c hc hrc => ?_⟩
  · obtain ⟨k, t, rfl, -⟩ := hH.ts g r hg hr
    exact ⟨_, rfl⟩
  · have hlt := hH.order g₁ g₂ t₁ t₂ hg₁ hr₁ hg₂ hr₂ h12
    constructor
    · rintro rfl
      rw [hH.cmp c t₁ t₂ r hc hrc, hlt]
    · rintro rfl
      rw [hH.cmp c t₂ t₁ r hc hrc]
      congr 1
      revert hlt
      obtain ⟨a, b⟩ := t₁; obtain ⟨a', b'⟩ := t₂
      simp only [lexLt, decide_eq_true_eq, decide_eq_false_iff_not]
      omega

end Cslib.SharedMemory.Timestamp.Alg4
