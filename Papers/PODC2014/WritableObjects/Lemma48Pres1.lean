import Papers.PODC2014.WritableObjects.Lemma48Tr

/-!
# Lemma 4.8, part 6: preservation of the local and transcript invariants
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

theorem Inv.qok_step (hI : Inv W c) (hs : Step W c c') : ∀ p, QOK p (c'.loc p).qs := by
  intro p'
  cases hs
  case rec27 p v f h hf =>
    by_cases hp : p' = p
    · subst hp; simpa using (((hI.qok p').erase f).updQ 0 _).updQ 1 _
    · simpa [Function.update_of_ne hp] using hI.qok p'
  case rec29 p v f h =>
    by_cases hp : p' = p
    · subst hp; simpa using (hI.qok p').updQ 2 _
    · simpa [Function.update_of_ne hp] using hI.qok p'
  case rec31 p v f h =>
    by_cases hp : p' = p
    · subst hp; simpa using (hI.qok p').updQ 3 _
    · simpa [Function.update_of_ne hp] using hI.qok p'
  all_goals
    simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simpa using hI.qok p'
    · exact hI.qok p'


theorem Inv.chosen_step (hI : Inv W c) (hs : Step W c c') : ∀ p f, curF (c'.loc p).pc = some f →
    f.1 = p ∧ (c'.loc p).Prot f (4 * ((c'.loc p).ctr + 2 * n + 2)) ∧
      (c'.loc p).lc f = (c'.loc p).ctr := by
  intro p' f' hf'
  cases hs
  case rec27 p v f h hf =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, curF, Option.some.injEq] at hf' ⊢; subst hf'
      exact ⟨(hI.qok p').freeOwn _ hf, Loc.r27_chosen h (hI.qok p') hf, by simp⟩
    · simp only [Function.update_of_ne hp] at hf' ⊢; exact hI.chosen p' f' hf'
  case rec29 p v f h =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, curF, Option.some.injEq] at hf' ⊢; subst hf'
      obtain ⟨h1, h2, h3⟩ := hI.chosen p' f (by simp [h, curF])
      exact ⟨h1, Loc.r29_Prot h (hI.qok p') h2 (by omega), h3⟩
    · simp only [Function.update_of_ne hp] at hf' ⊢; exact hI.chosen p' f' hf'
  case rec31 p v f h =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, curF, Option.some.injEq] at hf' ⊢; subst hf'
      obtain ⟨h1, h2, h3⟩ := hI.chosen p' f (by simp [h, curF])
      exact ⟨h1, Loc.r31_Prot h (hI.qok p') h2 (by omega), h3⟩
    · simp only [Function.update_of_ne hp] at hf' ⊢; exact hI.chosen p' f' hf'
  all_goals
    simp only [Function.update_apply] at hf' ⊢; split_ifs at hf' ⊢ with hp
    · subst hp
      simp only [curF, Option.some.injEq, reduceCtorEq] at hf'
      all_goals
        obtain ⟨h1, h2, h3⟩ := hI.chosen p' f' (by simp [*, curF])
        exact ⟨h1, h2.congr rfl (Loc.U_congr rfl (by simp [stage, *])), h3⟩
    · exact hI.chosen p' f' hf'

theorem Inv.prePtr_step (hI : Inv W c) (hs : Step W c c') : ∀ p f, curF (c'.loc p).pc = some f →
    isPrePtr (c'.loc p).pc → (c'.loc p).pp f = none := by
  intro p' f' hf' hpre
  cases hs
  case rec27 p v f h hf =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, curF, Option.some.injEq] at hf' ⊢; subst hf'; simp
    · simp only [Function.update_of_ne hp] at hf' hpre ⊢; exact hI.prePtr p' f' hf' hpre
  all_goals
    simp only [Function.update_apply] at hf' hpre ⊢
    split_ifs at hf' hpre ⊢ with hp
    all_goals first
      | exact hI.prePtr p' f' hf' hpre
      | (subst hp
         simp only [curF, isPrePtr, Option.some.injEq, reduceCtorEq] at hf' hpre
         all_goals first
           | exact hI.prePtr p' f' (by simp [*, curF]) (by simp [*, isPrePtr])
           | (simp only [Function.update_apply]; split_ifs <;> simp_all))

theorem Inv.w21_step (hI : Inv W c) (hs : Step W c c') : ∀ p v f s' m19 τ19 π,
    (c'.loc p).pc = .w21 v f s' m19 τ19 π → (c'.loc p).pp f = some π ∧ τ19 ≤ π := by
  intro p' v' f' s'' m19' τ19' π' hpc
  cases hs
  case l20 p v f s' m19 τ19 h =>
    by_cases hp : p' = p
    · subst hp
      simp only [Function.update_self, PC.w21.injEq] at hpc ⊢
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpc
      have := (hI.locRd p').2.2.2.2 s' m19 τ19 (by simp [h, s19Of])
      simp [this.2.2.2]
    · simp only [Function.update_of_ne hp] at hpc ⊢; exact hI.w21 p' _ _ _ _ _ _ hpc
  all_goals
    simp only [Function.update_apply] at hpc ⊢
    split_ifs at hpc ⊢ with hp
    all_goals first
      | exact hI.w21 p' _ _ _ _ _ _ hpc
      | (subst hp; simp only [reduceCtorEq] at hpc)
      | (subst hp; exact hI.w21 _ _ _ _ _ _ _ (by simp_all))

theorem Inv.ptrEq_step (hI : Inv W c) (hs : Step W c c') : c'.ptr = ptrAt c'.tr c'.tr.length := by
  have h0 := hI.ptrEq
  cases hs
  case l20 => simp only [List.length_append, List.length_singleton]; rw [ptrAt_concat_ptr]
  case l23 => simp only [List.length_append, List.length_singleton]; rw [ptrAt_concat_ptr]
  all_goals
    first
      | exact h0
      | (simp only [List.length_append, List.length_singleton]
         rw [ptrAt_concat_of_ne (by simp)]; exact h0)

theorem Inv.sEq_step (hI : Inv W c) (hs : Step W c c') : ∀ q, c'.S q = Sval n (c'.loc q).m := by
  intro q'
  cases hs
  case l35 q o x h =>
    by_cases hq : q' = q
    · subst hq
      have := hI.exec q'; simp only [ExecInv, h] at this
      simp only [Function.update_self]
      rw [Sval_succ, ← hI.sEq q', this.2]
    · simp only [Function.update_of_ne hq]; exact hI.sEq q'
  all_goals
    simp only [Function.update_apply]; try split_ifs with hq
    all_goals first | exact hI.sEq q' | (subst hq; exact hI.sEq _)

theorem Inv.ptrProt_step (hI : Inv W c) (hs : Step W c c') : ∀ i, c'.ptr = some i →
    (c'.loc i.1).Prot i (4 * ((c'.loc i.1).ctr + 2 * n + 1)) ∧ (c'.loc i.1).pp i ≠ none ∧
    ∀ v f s' m19 τ19 π, (c'.loc i.1).pc = .w21 v f s' m19 τ19 π → f = i := by
  intro i hi
  cases hs
  case l20 p v f s' m19 τ19 h =>
    simp only [Option.some.injEq] at hi; subst hi
    obtain ⟨h1, h2, h3⟩ := hI.chosen p f (by simp [h, curF])
    subst h1
    simp only [Function.update_self]
    refine ⟨(h2.mono (by omega)).congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simp, ?_⟩
    intro v' f' _ _ _ _ hpc; simp only [PC.w21.injEq] at hpc; exact hpc.2.1.symm
  case l23 p v f h =>
    simp only [Option.some.injEq] at hi; subst hi
    obtain ⟨h1, h2, h3⟩ := hI.chosen p f (by simp [h, curF])
    subst h1
    simp only [Function.update_self]
    refine ⟨Loc.Prot.congr (h2.mono (by omega)) rfl (by funext o; have := o.isLt; simp [Loc.U, stage, h]; omega), by simp, ?_⟩
    intro v' f' _ _ _ _ hpc; simp at hpc
  case rec27 p v f h hf =>
    obtain ⟨h1, h2, h3⟩ := hI.ptrProt i hi
    by_cases hp : i.1 = p
    · subst hp; simp only [Function.update_self]
      have hfi : i ≠ f := fun e => h1.1 (e ▸ hf)
      refine ⟨Loc.r27_Prot h (hI.qok _) h1 (by omega), by simpa [Function.update_of_ne hfi] using h2,
        by simp⟩
    · simp only [Function.update_of_ne hp]; exact ⟨h1, h2, h3⟩
  case rec29 p v f h =>
    obtain ⟨h1, h2, h3⟩ := hI.ptrProt i hi
    by_cases hp : i.1 = p
    · subst hp; simp only [Function.update_self]
      exact ⟨Loc.r29_Prot h (hI.qok _) h1 (by omega), h2, by simp⟩
    · simp only [Function.update_of_ne hp]; exact ⟨h1, h2, h3⟩
  case rec31 p v f h =>
    obtain ⟨h1, h2, h3⟩ := hI.ptrProt i hi
    by_cases hp : i.1 = p
    · subst hp; simp only [Function.update_self]
      exact ⟨Loc.r31_Prot h (hI.qok _) h1 (by omega), h2, by simp⟩
    · simp only [Function.update_of_ne hp]; exact ⟨h1, h2, h3⟩
  case l21 p v f s' m19 τ19 π h =>
    obtain ⟨h1, h2, h3⟩ := hI.ptrProt i hi
    by_cases hp : i.1 = p
    · subst hp; simp only [Function.update_self]
      have hfi := h3 _ _ _ _ _ _ h
      subst hfi
      obtain ⟨-, h5, -⟩ := hI.chosen f.1 f (by simp [h, curF])
      refine ⟨Loc.Prot.congr (h5.mono (by omega)) rfl (by funext o; have := o.isLt; simp [Loc.U, stage, h]; omega), h2, by simp⟩
    · simp only [Function.update_of_ne hp]; exact ⟨h1, h2, h3⟩
  all_goals
    obtain ⟨h1, h2, h3⟩ := hI.ptrProt i hi
    simp only [Function.update_apply]
    split_ifs with hp
    all_goals first
      | exact ⟨h1, h2, h3⟩
      | (subst hp
         refine ⟨h1.congr rfl (Loc.U_congr rfl (by simp [stage, *])), by simpa using h2, ?_⟩
         intro _ _ _ _ _ _ hpc; simp at hpc)

/-- A new `Ptr.Write(f)` event: all `SWrite`s on `f` have returned. -/
lemma Inv.swf_new (hI : Inv W c) {p : Fin n} {f : Idx n} (hpc : curF (c.loc p).pc = some f)
    (hnot : ∀ v, (c.loc p).pc ≠ .wSW v f) (e : Ev (Fin n) (Idx n) T)
    (he : ∀ p v, e ≠ .swinv p f v) : SWF (c.tr ++ [e]) f (c.tr.length + 1) := by
  refine SWF.concat ?_ he
  intro a p' v' ha
  rcases hI.swdone a p' f v' ha with ⟨b, r, h1, h2, h3⟩ | ⟨v'', hpc'⟩
  · exact ⟨b, r, h1, by omega, h3⟩
  · have e1 := (hI.chosen p' f (by simp [hpc', curF])).1
    have e2 := (hI.chosen p f hpc).1
    rw [e1] at e2; subst e2
    exact absurd hpc' (hnot v'')

lemma Inv.swf_concat (hI : Inv W c) (e : Ev (Fin n) (Idx n) T) {p i π} (h : (c.loc p).pp i = some π)
    (he : ∀ p v, e ≠ .swinv p i v) :
    i.1 = p ∧ (c.tr ++ [e])[π]? = some (.ptr p i) ∧ SWF (c.tr ++ [e]) i (π + 1) := by
  obtain ⟨h1, h2, h3⟩ := hI.swf p i π h
  exact ⟨h1, get_concat_of h2, h3.concat he⟩

theorem Inv.swf_step (hI : Inv W c) (hs : Step W c c') : ∀ p i π, (c'.loc p).pp i = some π →
    i.1 = p ∧ c'.tr[π]? = some (.ptr p i) ∧ SWF c'.tr i (π + 1) := by
  intro p' i π hpp
  cases hs
  case rec27 p v f h hf =>
    by_cases hp : p' = p
    · subst hp; simp only [Function.update_self] at hpp
      by_cases hif : i = f
      · subst hif; simp at hpp
      · rw [Function.update_of_ne hif] at hpp; exact hI.swf p' i π hpp
    · simp only [Function.update_of_ne hp] at hpp; exact hI.swf p' i π hpp
  case l20 p v f s' m19 τ19 h =>
    by_cases hp : p' = p
    · subst hp; simp only [Function.update_self] at hpp
      by_cases hif : i = f
      · subst hif; simp only [Function.update_self, Option.some.injEq] at hpp; subst hpp
        exact ⟨(hI.chosen p' i (by simp [h, curF])).1, get_concat_len,
          hI.swf_new (p := p') (by simp [h, curF]) (by simp [h]) _ (by simp)⟩
      · rw [Function.update_of_ne hif] at hpp; exact hI.swf_concat _ hpp (by simp)
    · simp only [Function.update_of_ne hp] at hpp; exact hI.swf_concat _ hpp (by simp)
  case l23 p v f h =>
    by_cases hp : p' = p
    · subst hp; simp only [Function.update_self] at hpp
      by_cases hif : i = f
      · subst hif; simp only [Function.update_self, Option.some.injEq] at hpp; subst hpp
        exact ⟨(hI.chosen p' i (by simp [h, curF])).1, get_concat_len,
          hI.swf_new (p := p') (by simp [h, curF]) (by simp [h]) _ (by simp)⟩
      · rw [Function.update_of_ne hif] at hpp; exact hI.swf_concat _ hpp (by simp)
    · simp only [Function.update_of_ne hp] at hpp; exact hI.swf_concat _ hpp (by simp)
  case swinv p v f h =>
    have hpp' : (c.loc p').pp i = some π := by
      by_cases hp : p' = p
      · subst hp; simpa using hpp
      · simpa [Function.update_of_ne hp] using hpp
    refine hI.swf_concat _ hpp' ?_
    intro p'' v'' he
    simp only [Ev.swinv.injEq] at he
    obtain ⟨-, hif, -⟩ := he
    subst hif
    have e1 := (hI.swf p' f π hpp').1
    have e2 := (hI.chosen p f (by simp [h, curF])).1
    rw [e1] at e2; subst e2
    rw [hI.prePtr p' f (by simp [h, curF]) (by simp [h, isPrePtr])] at hpp'
    simp at hpp'
  all_goals
    have hpp' : (c.loc p').pp i = some π := by
      simp only [Function.update_apply] at hpp
      split_ifs at hpp with hp
      · subst hp; simpa using hpp
      · exact hpp
    first
      | exact hI.swf p' i π hpp'
      | exact hI.swf_concat _ hpp' (by simp)

theorem Inv.swdone_step (hI : Inv W c) (hs : Step W c c') : ∀ a p i v,
    c'.tr[a]? = some (.swinv p i v) →
    (∃ b r, a < b ∧ b < c'.tr.length ∧ c'.tr[b]? = some (.aret p i r)) ∨
      ∃ v', (c'.loc p).pc = .wSW v' i := by
  intro a p' i v' ha
  cases hs
  case swinv p v f h =>
    rcases get_concat_iff.1 ha with ha | ⟨rfl, he⟩
    · rcases hI.swdone a p' i v' ha with ⟨b, r, h1, h2, h3⟩ | ⟨v'', hpc⟩
      · left; exact ⟨b, r, h1, by simp; omega, get_concat_of h3⟩
      · right
        by_cases hp : p' = p
        · subst hp; rw [h] at hpc; cases hpc
        · exact ⟨v'', by simpa [Function.update_of_ne hp] using hpc⟩
    · simp only [Ev.swinv.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      right; exact ⟨v, by simp⟩
  case swret p v f r h =>
    rcases get_concat_iff.1 ha with ha0 | ⟨rfl, he⟩
    · rcases hI.swdone a p' i v' ha0 with ⟨b, r', h1, h2, h3⟩ | ⟨v'', hpc⟩
      · left; exact ⟨b, r', h1, by simp; omega, get_concat_of h3⟩
      · by_cases hp : p' = p
        · subst hp; rw [h] at hpc; simp only [PC.wSW.injEq] at hpc; obtain ⟨rfl, rfl⟩ := hpc
          left; exact ⟨c.tr.length, r, lt_of_get ha0, by simp, get_concat_len⟩
        · right; exact ⟨v'', by simpa [Function.update_of_ne hp] using hpc⟩
    · simp at he
  all_goals
    first
    | (rcases hI.swdone a p' i v' ha with ⟨b, r, h1, h2, h3⟩ | ⟨v'', hpc⟩
       · exact Or.inl ⟨b, r, h1, h2, h3⟩
       · right; refine ⟨v'', ?_⟩; simp only [Function.update_apply]
         split_ifs with hp
         · subst hp; simp_all
         · exact hpc)
    | (rcases get_concat_iff.1 ha with ha | ⟨rfl, he⟩
       · rcases hI.swdone a p' i v' ha with ⟨b, r, h1, h2, h3⟩ | ⟨v'', hpc⟩
         · exact Or.inl ⟨b, r, h1, by simp; omega, get_concat_of h3⟩
         · right; refine ⟨v'', ?_⟩; simp only [Function.update_apply]
           split_ifs with hp
           · subst hp; simp_all
           · exact hpc
       · simp at he)

theorem Inv.notInUse_step (hI : Inv W c) (hs : Step W c c') : ∀ t p f v,
    c'.tr[t]? = some (.swinv p f v) → ptrAt c'.tr t ≠ some f := by
  intro t p' f' v' ht
  cases hs
  case swinv p v f h =>
    rcases get_concat_iff.1 ht with ht | ⟨rfl, he⟩
    · rw [ptrAt_concat_le (le_of_lt (lt_of_get ht))]; exact hI.notInUse t p' f' v' ht
    · simp only [Ev.swinv.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      rw [ptrAt_concat_le le_rfl, ← hI.ptrEq]
      intro hptr
      obtain ⟨-, hpp, -⟩ := hI.ptrProt f hptr
      obtain ⟨hf1, -, -⟩ := hI.chosen p f (by simp [h, curF])
      rw [hf1] at hpp
      exact hpp (hI.prePtr p f (by simp [h, curF]) (by simp [h, isPrePtr]))
  all_goals first
    | exact hI.notInUse t p' f' v' ht
    | (rcases get_concat_iff.1 ht with ht | ⟨rfl, he⟩
       · rw [ptrAt_concat_le (le_of_lt (lt_of_get ht))]; exact hI.notInUse t p' f' v' ht
       · simp at he)

theorem Inv.opRet_step (hI : Inv W c) (hs : Step W c c') : ∀ t q i o,
    c'.tr[t]? = some (.opinv q i o) →
    (∃ c'' r, t < c'' ∧ c'.tr[c'']? = some (.aret q i r)) ∨
      ∃ x ts, (c'.loc q).pc = .eOp x i ts t := by
  intro t q' i' o' ht
  cases hs
  case opinv q o x i ts h =>
    rcases get_concat_iff.1 ht with ht | ⟨rfl, he⟩
    · rcases hI.opRet t q' i' o' ht with ⟨c'', r, h1, h2⟩ | ⟨x', ts', hpc⟩
      · left; exact ⟨c'', r, h1, get_concat_of h2⟩
      · right
        by_cases hq : q' = q
        · subst hq; rw [h] at hpc; cases hpc
        · exact ⟨x', ts', by simpa [Function.update_of_ne hq] using hpc⟩
    · simp only [Ev.opinv.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      right; exact ⟨x, ts, by simp⟩
  case opret q x i ts t0 r h =>
    rcases get_concat_iff.1 ht with ht0 | ⟨rfl, he⟩
    · rcases hI.opRet t q' i' o' ht0 with ⟨c'', r', h1, h2⟩ | ⟨x', ts', hpc⟩
      · left; exact ⟨c'', r', h1, get_concat_of h2⟩
      · by_cases hq : q' = q
        · subst hq; rw [h] at hpc; simp only [PC.eOp.injEq] at hpc
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hpc
          left; exact ⟨c.tr.length, r, lt_of_get ht0, get_concat_len⟩
        · right; exact ⟨x', ts', by simpa [Function.update_of_ne hq] using hpc⟩
    · simp at he
  all_goals
    first
    | (rcases hI.opRet t q' i' o' ht with ⟨c'', r, h1, h2⟩ | ⟨x', ts', hpc⟩
       · exact Or.inl ⟨c'', r, h1, h2⟩
       · right; refine ⟨x', ts', ?_⟩; simp only [Function.update_apply]
         split_ifs with hq
         · subst hq; simp_all
         · exact hpc)
    | (rcases get_concat_iff.1 ht with ht | ⟨rfl, he⟩
       · rcases hI.opRet t q' i' o' ht with ⟨c'', r, h1, h2⟩ | ⟨x', ts', hpc⟩
         · exact Or.inl ⟨c'', r, h1, get_concat_of h2⟩
         · right; refine ⟨x', ts', ?_⟩; simp only [Function.update_apply]
           split_ifs with hq
           · subst hq; simp_all
           · exact hpc
       · simp at he)

lemma TemplateUpTo.of_nonev {c c' : Cfg n T} (h : TemplateUpTo W c) (htr : c'.tr = c.tr)
    (habs : ∀ p, absPC (c'.loc p).pc = absPC (c.loc p).pc) : TemplateUpTo W c' := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun p => ⟨(hσ p).1, ?_, ?_⟩⟩
  · intro t ht
    have ht' : t < c.tr.length := htr ▸ ht
    have e : c'.tr[t] = c.tr[t] := by simp [htr]
    rw [e]; exact (hσ p).2.1 t ht'
  · rw [htr, habs]; exact (hσ p).2.2

lemma TemplateUpTo.of_ev {c c' : Cfg n T} (h : TemplateUpTo W c) (e : Ev (Fin n) (Idx n) T)
    (htr : c'.tr = c.tr ++ [e])
    (habs : ∀ p, p ≠ e.proc → absPC (c'.loc p).pc = absPC (c.loc p).pc)
    (hstep : PStep W owner e.proc (absPC (c.loc e.proc).pc) e (absPC (c'.loc e.proc).pc)) :
    TemplateUpTo W c' := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨fun p t => if t ≤ c.tr.length then σ p t else absPC (c'.loc p).pc, fun p => ⟨?_, ?_, ?_⟩⟩
  · simp [(hσ p).1]
  · intro t ht
    have ht' : t < c.tr.length + 1 := by simpa [htr] using ht
    rcases Nat.lt_or_ge t c.tr.length with hlt | hge
    · have e1 : c'.tr[t] = c.tr[t] := by simp [htr, List.getElem_append_left hlt]
      rw [e1]
      simp only [show t ≤ c.tr.length by omega, show t + 1 ≤ c.tr.length by omega, if_true]
      exact (hσ p).2.1 t hlt
    · have ht2 : t = c.tr.length := by omega
      subst ht2
      have e1 : c'.tr[c.tr.length] = e := by simp [htr]
      rw [e1]
      simp only [le_refl, if_true, show ¬ c.tr.length + 1 ≤ c.tr.length by omega, if_false,
        (hσ p).2.2]
      constructor
      · intro hp; subst hp; exact hstep
      · intro hp; exact habs p (Ne.symm hp)
  · simp [htr]

theorem Inv.tmpl_step (hI : Inv W c) (hs : Step W c c') : TemplateUpTo W c' := by
  have h0 := hI.tmpl
  have frame : ∀ (q : Fin n) (l : Loc n T), absPC l.pc = absPC (c.loc q).pc →
      ∀ p, absPC ((Function.update c.loc q l) p).pc = absPC (c.loc p).pc := by
    intro q l hl p; by_cases hp : p = q
    · subst hp; simpa using hl
    · simp [Function.update_of_ne hp]
  have frame' : ∀ (q : Fin n) (l : Loc n T),
      ∀ p, p ≠ q → absPC ((Function.update c.loc q l) p).pc = absPC (c.loc p).pc := by
    intro q l p hp; simp [Function.update_of_ne hp]
  cases hs
  case winv p v h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.winv v)
  case swinv p v f h =>
    exact h0.of_ev _ rfl (frame' _ _) (by
      simpa [Ev.proc, h, absPC] using
        PStep.swinv (W := W) (owner := owner) v f (hI.chosen p f (by simp [h, curF])).1)
  case swret p v f r h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.swret v f r)
  case l20 p v f s' m19 τ19 h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.ptr v f)
  case l23 p v f h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.ptr v f)
  case wret p v h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.wret v)
  case einv q o ho h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.einv o ho)
  case opinv q o x i ts h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.opinv o i)
  case opret q x i ts t r h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.opret i r)
  case eret q r h =>
    exact h0.of_ev _ rfl (frame' _ _) (by simpa [Ev.proc, h, absPC] using PStep.eret r)
  all_goals exact h0.of_nonev rfl (frame _ _ (by simp [*, absPC]))

theorem Inv.tau35_step (hI : Inv W c) (hs : Step W c c') :
    ∀ q, (c'.loc q).τ35 ≤ c'.tr.length := by
  intro q
  have := hI.tau35 q
  cases hs <;> (simp only [Function.update_apply]; split_ifs <;> simp_all <;> omega)

end Podc.WritableObjects.WF
