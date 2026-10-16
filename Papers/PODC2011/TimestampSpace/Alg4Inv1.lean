import Papers.PODC2011.TimestampSpace.Alg4

/-!
# Algorithm 4: basic invariant

`Inv1`: the local operation counters match the history, `compare` returns at once with the
lexicographic comparison of its arguments (Algorithm 3), the non-`⊥` registers form a prefix
`R[1..K]` (Claim 6.1 (a), (d)), every timestamp `(rnd, turn)` about to be returned has
`R[rnd] ≠ ⊥` (Claim 6.1 (c)), and the local variables are consistent with the memory
(`R[myrnd] ≠ ⊥`, …).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- Per-process part of the basic invariant. -/
def PI1 (R : Mem P) (p : P) (l : Loc P) : Prop :=
  match l.pc with
  | .wh j _ => 1 ≤ j ∧ (2 ≤ j → R (j - 1) ≠ none)
  | .loop k i _ _ => 1 ≤ i ∧ i + 1 ≤ k ∧ R k ≠ none
  | .scan k => 1 ≤ k → R k ≠ none
  | .fin k w => (1 ≤ k → R k ≠ none) ∧ w.rnd = k + 1 ∧ lastId (some w) = some (p, l.cnt)
  | .done (.inl (k, _)) => 1 ≤ k ∧ R k ≠ none
  | _ => True

lemma PI1.mono {R R' : Mem P} {p : P} {l : Loc P} (h : PI1 R p l)
    (hm : ∀ j, R j ≠ none → R' j ≠ none) : PI1 R' p l := by
  unfold PI1 at h ⊢
  rcases l with ⟨c, pc⟩
  cases pc with
  | idle => trivial
  | done r =>
    rcases r with ⟨k, t⟩ | b
    · exact ⟨h.1, hm _ h.2⟩
    · trivial
  | wh j v => exact ⟨h.1, fun hj => hm _ (h.2 hj)⟩
  | loop k i v s => exact ⟨h.1, h.2.1, hm _ h.2.2⟩
  | scan k => exact fun hk => hm _ (h hk)
  | fin k w => exact ⟨fun hk => hm _ (h.1 hk), h.2⟩

/-- Memory part of the basic invariant: `R[0] = ⊥`, the non-`⊥` registers form a prefix
(Claim 6.1 (d)), every stored value has a last id, and a value with `rnd > j` stored in `R[j]`
(written at line 8 or 11) has `R[rnd] ≠ ⊥`. -/
structure MemOK (R : Mem P) : Prop where
  r0 : R 0 = none
  contig : ∀ j i, R j ≠ none → 1 ≤ i → i ≤ j → R i ≠ none
  regs : ∀ j w, R j = some w →
    lastId (some w) ≠ none ∧ 1 ≤ w.rnd ∧ (w.rnd = j ∨ (j < w.rnd ∧ R w.rnd ≠ none))

/-- The basic invariant. -/
structure Inv1 (α : List (Label P TS)) (C : ACfg P) : Prop where
  cnt : ∀ p, (C.loc p).cnt = (respsOf α p).length
  idle : ∀ p, C.pend p = none ↔ (C.loc p).pc = .idle
  gts : ∀ p b, C.pend p = some .getTS → (C.loc p).pc ≠ .done (.inr b)
  cmp : ∀ p a b, C.pend p = some (.compare a b) → (C.loc p).pc = .done (.inr (lexLt a b))
  mem : MemOK (Rg C)
  pi : ∀ p, PI1 (Rg C) p (C.loc p)

lemma inv1_init : Inv1 ([] : List (Label P TS)) (alg4 (P := P)).initCfg := by
  refine ⟨fun p => rfl, fun p => by simp [Impl.initCfg, alg4], fun p b h => by
    simp [Impl.initCfg] at h, fun p a b h => by simp [Impl.initCfg] at h, ⟨rfl,
    fun j i h => by simp [Impl.initCfg, alg4] at h, fun j w h => by
    simp [Impl.initCfg, alg4] at h⟩, fun p => by simp [PI1, Impl.initCfg, alg4]⟩

/-- Memory after a write. -/
lemma upd_ne_none {R : Mem P} {i j : ℕ} {v : Val P} (h : R j ≠ none) :
    Function.update R i (some v) j ≠ none := by
  by_cases hj : j = i
  · subst hj; simp
  · rwa [Function.update_of_ne hj]

lemma lastId_newSeq (r : Mem P) (k : ℕ) (id : P × ℕ) (rnd : ℕ) :
    lastId (some (⟨newSeq r k id, rnd⟩ : Val P)) = some id := by
  simp [lastId, newSeq]

/-- Effect of a `tau` step on the configuration, in terms of `eff`. -/
lemma tau_cfg {C C' : ACfg P} {p : P} (hs : (alg4 (P := P)).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ (C.loc p).pc.isAcc ∧ C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p (eff p (C.loc p) (Rg C)).1 ∧
      Rg C' = (eff p (C.loc p) (Rg C)).2 := step_tau' hs

/-- The possible effects of a `tau` step of `p` with local state `⟨c, pc⟩`. -/
inductive TauEff (p : P) (c : ℕ) (R : Mem P) : PC P → PC P → Mem P → Prop where
  | whS {j v x} : R j = some x → TauEff p c R (.wh j v) (.wh (j + 1) (some x)) R
  | whN {j v} : R j = none → TauEff p c R (.wh j v) (endWh j v) R
  | s6N {k i v} : R (k + 1) = none → TauEff p c R (.loop k i v .s6) (.loop k i v .s7) R
  | s6S {k i v x} : R (k + 1) = some x →
      TauEff p c R (.loop k i v .s6) (.done (.inl (k + 1, 0))) R
  | s7T {k i v} : seqAt v i = lastId (R i) → TauEff p c R (.loop k i v .s7) (.loop k i v .s8) R
  | s7F {k i v} : seqAt v i ≠ lastId (R i) →
      TauEff p c R (.loop k i v .s7) (.loop k i v .s10) R
  | s8 {k i v} : TauEff p c R (.loop k i v .s8) (.done (.inl (k, i)))
      (Function.update R i (some ⟨[(p, c)], k⟩))
  | s10T {k i v} : rndOf (R i) < k → TauEff p c R (.loop k i v .s10) (.loop k i v .s11) R
  | s10F {k i v} : ¬ rndOf (R i) < k → TauEff p c R (.loop k i v .s10) (nextIt k i v) R
  | s11 {k i v} : TauEff p c R (.loop k i v .s11) (nextIt k i v)
      (Function.update R i (some ⟨[(p, c)], k⟩))
  | scN {k} : R (k + 1) = none → TauEff p c R (.scan k) (.fin k ⟨newSeq R k (p, c), k + 1⟩) R
  | scS {k x} : R (k + 1) = some x → TauEff p c R (.scan k) (.done (.inl (k + 1, 0))) R
  | fin {k w} : TauEff p c R (.fin k w) (.done (.inl (k + 1, 0)))
      (Function.update R (k + 1) (some w))

lemma tauEff_of {p : P} {c : ℕ} {pc : PC P} (R : Mem P) (h : pc.isAcc) :
    TauEff p c R pc (eff p ⟨c, pc⟩ R).1.pc (eff p ⟨c, pc⟩ R).2 ∧ (eff p ⟨c, pc⟩ R).1.cnt = c := by
  cases pc with
  | idle => exact absurd h id
  | done r => exact absurd h id
  | wh j v =>
    cases hj : R j with
    | some x => rw [eff_wh_some p c R hj]; exact ⟨.whS hj, rfl⟩
    | none => rw [eff_wh_none p c R hj]; exact ⟨.whN hj, rfl⟩
  | loop k i v s =>
    cases s with
    | s6 =>
      cases hk : R (k + 1) with
      | some x => rw [eff_s6_some p c R hk]; exact ⟨.s6S hk, rfl⟩
      | none => rw [eff_s6_none p c R hk]; exact ⟨.s6N hk, rfl⟩
    | s7 =>
      rw [eff_s7]
      by_cases ht : seqAt v i = lastId (R i)
      · simp only [ht, ite_true]; exact ⟨.s7T ht, trivial⟩
      · simp only [ht, ite_false]; exact ⟨.s7F ht, trivial⟩
    | s8 => rw [eff_s8]; exact ⟨.s8, rfl⟩
    | s10 =>
      rw [eff_s10]
      by_cases ht : rndOf (R i) < k
      · simp only [ht, ite_true]; exact ⟨.s10T ht, trivial⟩
      · simp only [ht, ite_false]; exact ⟨.s10F ht, trivial⟩
    | s11 => rw [eff_s11]; exact ⟨.s11, rfl⟩
  | scan k =>
    cases hk : R (k + 1) with
    | some x => rw [eff_scan_some p c R hk]; exact ⟨.scS hk, rfl⟩
    | none => rw [eff_scan_none p c R hk]; exact ⟨.scN hk, rfl⟩
  | fin k w => rw [eff_fin]; exact ⟨.fin, rfl⟩

/-- A `tau` step, in explicit form. -/
lemma tau_step {C C' : ACfg P} {p : P} (hs : (alg4 (P := P)).step C (.tau p) = some C') :
    ∃ pc', C.pend p ≠ none ∧ C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p ⟨(C.loc p).cnt, pc'⟩ ∧
      TauEff p (C.loc p).cnt (Rg C) (C.loc p).pc pc' (Rg C') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tau_cfg hs
  generalize hl : C.loc p = l at h2 h4 h5
  obtain ⟨c, pc⟩ := l
  obtain ⟨hT, hc⟩ := tauEff_of (p := p) (c := c) (Rg C) h2
  simp only at hT hc h4 h5
  generalize eff p ⟨c, pc⟩ (Rg C) = E at hT hc h4 h5
  obtain ⟨⟨c', pc'⟩, R'⟩ := E
  simp only at hc hT h4 h5
  subst hc
  exact ⟨pc', h1, h3, h4, h5 ▸ hT⟩

section TauEffLemmas

variable {p : P} {c : ℕ} {R R' : Mem P} {pc pc' : PC P}

lemma TauEff.mono (h : TauEff p c R pc pc' R') : ∀ j, R j ≠ none → R' j ≠ none := by
  intro j hj
  cases h <;> first | exact hj | exact upd_ne_none hj

lemma endWh_ne_idle (j : ℕ) (v : Option (Val P)) : endWh j v ≠ .idle := by
  unfold endWh; split_ifs <;> simp

lemma nextIt_ne_idle (k i : ℕ) (v : Option (Val P)) : nextIt k i v ≠ .idle := by
  unfold nextIt; split_ifs <;> simp

lemma endWh_ne_done (j : ℕ) (v : Option (Val P)) (r) : endWh j v ≠ .done r := by
  unfold endWh; split_ifs <;> simp

lemma nextIt_ne_done (k i : ℕ) (v : Option (Val P)) (r) : nextIt k i v ≠ .done r := by
  unfold nextIt; split_ifs <;> simp

lemma TauEff.ne_idle (h : TauEff p c R pc pc' R') : pc' ≠ .idle := by
  cases h <;> simp [endWh_ne_idle, nextIt_ne_idle]

lemma TauEff.ne_inr (h : TauEff p c R pc pc' R') (b : Bool) : pc' ≠ .done (.inr b) := by
  cases h <;> simp [endWh_ne_done, nextIt_ne_done]

lemma TauEff.src_acc (h : TauEff p c R pc pc' R') : pc.isAcc := by
  cases h <;> trivial

lemma TauEff.memOK (hM : MemOK R) (hpi : PI1 R p ⟨c, pc⟩) (h : TauEff p c R pc pc' R') :
    MemOK R' := by
  cases h with
  | @s8 k i v | @s11 k i v =>
    simp only [PI1] at hpi
    obtain ⟨hi1, hik, hk⟩ := hpi
    have hi : R i ≠ none := hM.contig k i hk hi1 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact hM.r0
    · intro j i' hj hi' hij
      apply upd_ne_none
      by_cases hji : j = i
      · subst hji; exact hM.contig _ _ hi hi' hij
      · rw [Function.update_of_ne hji] at hj; exact hM.contig _ _ hj hi' hij
    · intro j w hj
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Option.some.injEq] at hj
        subst hj
        simp only [lastId, Option.bind_some, List.getLast?_singleton, ne_eq, reduceCtorEq,
          not_false_eq_true, true_and]
        exact ⟨by omega, Or.inr ⟨by omega, upd_ne_none hk⟩⟩
      · rw [Function.update_of_ne hji] at hj
        obtain ⟨h1, h2, h3⟩ := hM.regs j w hj
        exact ⟨h1, h2, h3.imp_right fun h => ⟨h.1, upd_ne_none h.2⟩⟩
  | @fin k w =>
    simp only [PI1] at hpi
    obtain ⟨hk, hw, hl⟩ := hpi
    refine ⟨?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact hM.r0
    · intro j i' hj hi' hij
      by_cases hik : i' = k + 1
      · subst hik; simp
      apply upd_ne_none
      by_cases hji : j = k + 1
      · subst hji
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · omega
        · exact hM.contig _ _ (hk h0) hi' (by omega)
      · rw [Function.update_of_ne hji] at hj; exact hM.contig _ _ hj hi' hij
    · intro j w' hj
      by_cases hji : j = k + 1
      · subst hji
        simp only [Function.update_self, Option.some.injEq] at hj
        subst hj
        simp [hl, hw]
      · rw [Function.update_of_ne hji] at hj
        obtain ⟨h1, h2, h3⟩ := hM.regs j w' hj
        exact ⟨h1, h2, h3.imp_right fun h => ⟨h.1, upd_ne_none h.2⟩⟩
  | _ => exact hM

lemma TauEff.pi (hpi : PI1 R p ⟨c, pc⟩) (h : TauEff p c R pc pc' R') :
    PI1 R' p ⟨c, pc'⟩ := by
  have hm := h.mono
  cases h with
  | @whS j v x hx =>
    simp only [PI1] at hpi ⊢
    exact ⟨by omega, fun _ => by simp [hx]⟩
  | @whN j v hx =>
    simp only [PI1] at hpi ⊢
    unfold endWh
    split_ifs with h3
    · simp only; exact ⟨le_rfl, by omega, hpi.2 (by omega)⟩
    · simp only; intro h1; exact hpi.2 (by omega)
  | s6N hx => simpa [PI1] using hpi
  | @s6S k i v x hx => simp [PI1, hx]
  | s7T _ => simpa [PI1] using hpi
  | s7F _ => simpa [PI1] using hpi
  | @s8 k i v =>
    simp only [PI1] at hpi ⊢
    exact ⟨by omega, upd_ne_none hpi.2.2⟩
  | s10T _ => simpa [PI1] using hpi
  | @s10F k i v _ =>
    simp only [PI1] at hpi ⊢
    unfold nextIt
    split_ifs with h2
    · simp only; exact ⟨by omega, h2, hpi.2.2⟩
    · simp only; exact fun _ => hpi.2.2
  | @s11 k i v =>
    simp only [PI1] at hpi ⊢
    unfold nextIt
    split_ifs with h2
    · simp only; exact ⟨by omega, h2, upd_ne_none hpi.2.2⟩
    · simp only; exact fun _ => upd_ne_none hpi.2.2
  | @scN k hx =>
    simp only [PI1] at hpi ⊢
    refine ⟨hpi, ?_, ?_⟩ <;> first | trivial | rfl | exact lastId_newSeq _ _ _ _
  | @scS k x hx => simp [PI1, hx]
  | @fin k w => simp [PI1]

end TauEffLemmas

theorem Inv1.step {α : List (Label P TS)} {C C' : ACfg P} {ℓ : Label P TS} (hI : Inv1 α C)
    (hs : (alg4 (P := P)).step C ℓ = some C') : Inv1 (α ++ [ℓ]) C' := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, h1, h2, h3⟩ := step_inv' hs
    have hR : Rg C' = Rg C := by simp [Rg, h3]
    have hq := (hI.idle q).1 h0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      rw [h2]
      by_cases hp : p = q
      · subst hp; cases o <;> simp [alg4, hI.cnt, respsOf]
      · simp [Function.update_of_ne hp, hI.cnt, respsOf]
    · intro p
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; cases o <;> simp [alg4]
      · simp [Function.update_of_ne hp, hI.idle p]
    · intro p b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; cases o <;> simp [alg4]
      · simp only [Function.update_of_ne hp]; exact hI.gts p b
    · intro p a b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp
        cases o with
        | getTS => simp [alg4]
        | compare a' b' => simp only [alg4, Function.update_self]; simp; rintro rfl rfl; rfl
      · simp only [Function.update_of_ne hp]; exact hI.cmp p a b
    · rw [hR]; exact hI.mem
    · intro p
      rw [hR, h2]
      by_cases hp : p = q
      · subst hp; cases o <;> simp [alg4, PI1]
      · simp only [Function.update_of_ne hp]; exact hI.pi p
  | ret q r =>
    obtain ⟨h0, h1, h3, h2⟩ := step_ret' hs
    have hR : Rg C' = Rg C := by simp [Rg, h3]
    rcases h2 with ⟨hpc, h2⟩ | hpc
    swap
    · exact absurd ((hI.idle q).2 hpc) h0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      rw [h2]
      by_cases hp : p = q
      · subst hp; simp [hI.cnt, respsOf]
      · simp [Function.update_of_ne hp, hI.cnt, respsOf, Ne.symm hp]
    · intro p
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp
      · simp [Function.update_of_ne hp, hI.idle p]
    · intro p b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp
      · simp only [Function.update_of_ne hp]; exact hI.gts p b
    · intro p a b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp
      · simp only [Function.update_of_ne hp]; exact hI.cmp p a b
    · rw [hR]; exact hI.mem
    · intro p
      rw [hR, h2]
      by_cases hp : p = q
      · subst hp; simp [PI1]
      · simp only [Function.update_of_ne hp]; exact hI.pi p
  | tau q =>
    obtain ⟨pc', h0, h1, h2, hT⟩ := tau_step hs
    have hpi := hI.pi q
    have hidl := hI.idle q
    have hgts := hI.gts q
    have hcmp := hI.cmp q
    generalize hl : C.loc q = l at h2 hT hpi hidl hgts hcmp
    obtain ⟨c, pc⟩ := l
    generalize hR' : Rg C' = R' at hT
    have hmono := hT.mono
    simp only at hT hidl hgts hcmp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      rw [h2]
      by_cases hp : p = q
      · subst hp; have := hI.cnt p; rw [hl] at this; simpa [respsOf, List.filterMap_cons] using this
      · simp [Function.update_of_ne hp, hI.cnt, respsOf]
    · intro p
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp [h0, hT.ne_idle]
      · simp [Function.update_of_ne hp, hI.idle p]
    · intro p b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; simp [hT.ne_inr]
      · simp only [Function.update_of_ne hp]; exact hI.gts p b
    · intro p a b
      rw [h1, h2]
      by_cases hp : p = q
      · subst hp; intro h
        have := hcmp a b h
        have h' := hT.src_acc
        rw [this] at h'; exact h'.elim
      · simp only [Function.update_of_ne hp]; exact hI.cmp p a b
    · rw [hR']; exact hT.memOK hI.mem hpi
    · intro p
      rw [h2, hR']
      by_cases hp : p = q
      · subst hp; simp only [Function.update_self]; exact hT.pi hpi
      · simp only [Function.update_of_ne hp]; exact (hI.pi p).mono hmono

theorem inv1_of_run {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C) :
    Inv1 α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; exact inv1_init
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := run_append_singleton h
    exact (ih h₀).step hs

end Cslib.SharedMemory.Timestamp.Alg4
