import Papers.PODC2025.StrangerFreeTasks.Alg1SafetyBasic

/-!
# Safety of Algorithm 1: obliterating all registers needs `k + 1` processes (Lemma A)

Fix a set `S`. A triple is `S`-*dirty* if `S ⊆ seen`, otherwise *clean*. If all registers are
dirty at some configuration `C₁` and all registers are clean at a later configuration `C₂`,
then the union of the `seen` sets of the registers at `C₂` has at least `k + 1` elements.

The proof runs a ghost state alongside the execution after `C₁`:
* `wrote z` — `z` has written after `C₁`;
* `tgt z = some r` — the first write of `z` after `C₁` was clean and went to register `r`
  (a *type-0 write*);
* `t0 r = some z` — the current value of register `r` is the type-0 write of `z`.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {k : ℕ}

/-- The ghost invariant of Lemma A. -/
structure GInv (S : Finset P) (C : Cfg P k) (wrote : P → Prop) (tgt : P → Option (Fin (k + 1)))
    (t0 : Fin (k + 1) → Option P) : Prop where
  tgt_wrote : ∀ z r, tgt z = some r → wrote z
  t0_tgt : ∀ r z, t0 r = some z → tgt z = some r
  wrote_ph : ∀ z, wrote z → (C.loc z).phase ≠ .idle
  reg : ∀ r, ¬ S ⊆ (C.mem r).seen →
    k + 1 ≤ (C.mem r).seen.card ∨ ∃ z, t0 r = some z ∧ z ∈ (C.mem r).seen
  col1 : ∀ x, wrote x → ¬ S ⊆ (C.loc x).seen → (C.loc x).phase = .col1 →
    k + 1 ≤ (C.loc x).seen.card ∨ ∀ i < (C.loc x).j, ∃ z ∈ (C.loc x).seen, tgt z = some i
  big : ∀ x, wrote x → ¬ S ⊆ (C.loc x).seen →
    ((C.loc x).phase = .col2 ∨ (C.loc x).phase = .wr) → k + 1 ≤ (C.loc x).seen.card

/-- Distinct type-0 targets give `k + 1` distinct elements. -/
lemma card_of_tgt {s : Finset P} {tgt : P → Option (Fin (k + 1))}
    (h : ∀ i : Fin (k + 1), ∃ z ∈ s, tgt z = some i) : k + 1 ≤ s.card := by
  choose f hf1 hf2 using h
  have := Finset.card_le_card_of_injOn f (s := Finset.univ) (t := s)
    (fun i _ => hf1 i) (fun i _ j _ hij => by
      have h1 := hf2 i; have h2 := hf2 j; rw [hij, h2] at h1; exact (Option.some_injective _ h1).symm)
  simpa using this


section Steps

variable {S : Finset P} {wrote : P → Prop} {tgt : P → Option (Fin (k + 1))}
  {t0 : Fin (k + 1) → Option P}

/-- `GInv` only depends on the memory and on the local states of processes that wrote. -/
lemma GInv.congr {C C' : Cfg P k} (hG : GInv S C wrote tgt t0) (hm : C'.mem = C.mem)
    (hl : ∀ z, wrote z → C'.loc z = C.loc z) :
    GInv S C' wrote tgt t0 where
  tgt_wrote := hG.tgt_wrote
  t0_tgt := hG.t0_tgt
  wrote_ph z hz := by rw [hl z hz]; exact hG.wrote_ph z hz
  reg r := by rw [hm]; exact hG.reg r
  col1 x hx := by rw [hl x hx]; exact hG.col1 x hx
  big x hx := by rw [hl x hx]; exact hG.big x hx

lemma GInv.inv {C C' : Cfg P k} {p : P} {o : Unit} (hG : GInv S C wrote tgt t0)
    (h : (alg1 k).step C (.inv p o) = some C') : GInv S C' wrote tgt t0 := by
  obtain ⟨-, -, h3, h4⟩ := step_inv_alg1 h
  refine hG.congr h4 (fun z hz => ?_)
  rw [h3]
  by_cases hzp : z = p
  · subst hzp; simp [hG.wrote_ph z hz]
  · simp [hzp]

lemma GInv.ret {C C' : Cfg P k} {p : P} {o : Finset P} (hG : GInv S C wrote tgt t0)
    (h : (alg1 k).step C (.ret p o) = some C') : GInv S C' wrote tgt t0 := by
  obtain ⟨-, -, h3, h4, -⟩ := step_ret_alg1 h
  exact hG.congr h3 (fun z _ => by rw [h4])


lemma not_subset_of_union_left {S A B : Finset P} (h : ¬ S ⊆ A ∪ B) : ¬ S ⊆ A :=
  fun h' => h (h'.trans Finset.subset_union_left)

lemma not_subset_of_union_right {S A B : Finset P} (h : ¬ S ⊆ A ∪ B) : ¬ S ⊆ B :=
  fun h' => h (h'.trans Finset.subset_union_right)

/-- The key step of a first-collect read: extend the witnesses by the register just read. -/
lemma GInv.read_witness {C : Cfg P k} (hG : GInv S C wrote tgt t0) {x : P} (hx : wrote x)
    (hph : (C.loc x).phase = .col1)
    (hcl : ¬ S ⊆ (C.loc x).seen ∪ (C.mem (C.loc x).j).seen) :
    k + 1 ≤ ((C.loc x).seen ∪ (C.mem (C.loc x).j).seen).card ∨
      ∀ i ≤ (C.loc x).j, ∃ z ∈ (C.loc x).seen ∪ (C.mem (C.loc x).j).seen, tgt z = some i := by
  rcases hG.col1 x hx (not_subset_of_union_left hcl) hph with h1 | h1
  · exact Or.inl (h1.trans (Finset.card_le_card Finset.subset_union_left))
  rcases hG.reg _ (not_subset_of_union_right hcl) with h2 | ⟨z, hz1, hz2⟩
  · exact Or.inl (h2.trans (Finset.card_le_card Finset.subset_union_right))
  right
  intro i hi
  rcases lt_or_eq_of_le hi with hi | rfl
  · obtain ⟨z', hz', ht⟩ := h1 i hi
    exact ⟨z', Finset.mem_union_left _ hz', ht⟩
  · exact ⟨z, Finset.mem_union_right _ hz2, hG.t0_tgt _ _ hz1⟩

lemma GInv.col1_step {C C' : Cfg P k} {p : P} (hG : GInv S C wrote tgt t0)
    (hph : (C.loc p).phase = .col1) (hm : C'.mem = C.mem)
    (hl : C'.loc = Function.update C.loc p (afterCol1 k (C.loc p) (C.mem (C.loc p).j))) :
    GInv S C' wrote tgt t0 := by
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by rw [hl]; simp [hq]
  have hlp : C'.loc p = afterCol1 k (C.loc p) (C.mem (C.loc p).j) := by rw [hl]; simp
  refine ⟨hG.tgt_wrote, hG.t0_tgt, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzp : z = p
    · subst hzp; rw [hlp, afterCol1_phase]; split_ifs <;> simp [hph]
    · rw [hlq z hzp]; exact hG.wrote_ph z hz
  · rw [hm]; exact hG.reg
  · intro x hx hcl hph'
    by_cases hxp : x = p
    · subst hxp
      rw [hlp] at hcl hph' ⊢
      rw [afterCol1_phase] at hph'
      split_ifs at hph' with hj
      simp only [afterCol1_seen] at hcl ⊢
      rcases hG.read_witness hx hph hcl with h1 | h1
      · exact Or.inl h1
      · right; intro i hi
        rw [afterCol1_j, ite_eq_right hj, Fin.lt_def, fin_val_add_one hj] at hi
        exact h1 i (Fin.le_def.2 (by omega))
    · rw [hlq x hxp] at hcl hph' ⊢; exact hG.col1 x hx hcl hph'
  · intro x hx hcl hph'
    by_cases hxp : x = p
    · subst hxp
      rw [hlp] at hcl hph' ⊢
      rw [afterCol1_phase] at hph'
      split_ifs at hph' with hj
      · simp only [afterCol1_seen] at hcl ⊢
        rcases hG.read_witness hx hph hcl with h1 | h1
        · exact h1
        · refine card_of_tgt (fun i => h1 i (Fin.le_def.2 ?_))
          have := i.isLt; omega
      · rw [hph] at hph'; simp at hph'
    · rw [hlq x hxp] at hcl hph' ⊢; exact hG.big x hx hcl hph'

lemma GInv.col2_step {C C' : Cfg P k} {p : P} (hG : GInv S C wrote tgt t0)
    (hph : (C.loc p).phase = .col2) (hm : C'.mem = C.mem)
    (hl : C'.loc = Function.update C.loc p (afterCol2 k (C.loc p) (C.mem (C.loc p).j))) :
    GInv S C' wrote tgt t0 := by
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by rw [hl]; simp [hq]
  have hlp : C'.loc p = afterCol2 k (C.loc p) (C.mem (C.loc p).j) := by rw [hl]; simp
  have hph2 := afterCol2_phase (C.loc p) (C.mem (C.loc p).j) hph
  refine ⟨hG.tgt_wrote, hG.t0_tgt, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzp : z = p
    · subst hzp; rw [hlp]; rcases hph2 with h' | h' | ⟨h', -⟩ <;> simp [h']
    · rw [hlq z hzp]; exact hG.wrote_ph z hz
  · rw [hm]; exact hG.reg
  · intro x hx hcl hph'
    by_cases hxp : x = p
    · subst hxp; rw [hlp] at hph'
      rcases hph2 with h' | h' | ⟨h', -⟩ <;> simp [h'] at hph'
    · rw [hlq x hxp] at hcl hph' ⊢; exact hG.col1 x hx hcl hph'
  · intro x hx hcl hph'
    by_cases hxp : x = p
    · subst hxp
      rw [hlp] at hcl ⊢
      simp only [afterCol2_seen] at hcl ⊢
      exact (hG.big x hx (not_subset_of_union_left hcl) (Or.inl hph)).trans
        (Finset.card_le_card Finset.subset_union_left)
    · rw [hlq x hxp] at hcl hph' ⊢; exact hG.big x hx hcl hph'


lemma GInv.write_step {C C' : Cfg P k} {p : P} (hG : GInv S C wrote tgt t0)
    (hself : p ∈ (C.loc p).seen) (hph : (C.loc p).phase = .wr)
    (hm : C'.mem = Function.update C.mem (C.loc p).i ⟨some p, (C.loc p).seq, (C.loc p).seen⟩)
    (hl : C'.loc = Function.update C.loc p (wrNext k (C.loc p))) :
    ∃ (wrote' : P → Prop) (tgt' : P → Option (Fin (k + 1))) (t0' : Fin (k + 1) → Option P),
      GInv S C' wrote' tgt' t0' := by
  have hlq : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by rw [hl]; simp [hq]
  have hlp : C'.loc p = wrNext k (C.loc p) := by rw [hl]; simp
  set r₀ := (C.loc p).i with hr₀
  have hmr : ∀ r, r ≠ r₀ → C'.mem r = C.mem r := fun r hr => by
    rw [hm, Function.update_of_ne hr]
  have hm0 : (C'.mem r₀).seen = (C.loc p).seen := by rw [hm]; simp
  by_cases hA : S ⊆ (C.loc p).seen ∨ wrote p
  · -- the write is not a type-0 write
    refine ⟨fun z => z = p ∨ wrote z, tgt, Function.update t0 r₀ none, ?_⟩
    refine ⟨fun z r h => Or.inr (hG.tgt_wrote z r h), ?_, ?_, ?_, ?_, ?_⟩
    · intro r z h
      by_cases hr : r = r₀
      · subst hr; simp at h
      · rw [Function.update_of_ne hr] at h; exact hG.t0_tgt r z h
    · rintro z (rfl | hz)
      · rw [hlp]; simp
      · by_cases hzp : z = p
        · subst hzp; rw [hlp]; simp
        · rw [hlq z hzp]; exact hG.wrote_ph z hz
    · intro r hcl
      by_cases hr : r = r₀
      · subst hr; rw [hm0] at hcl ⊢
        rcases hA with hA | hA
        · exact absurd hA hcl
        · exact Or.inl (hG.big p hA hcl (Or.inr hph))
      · rw [hmr r hr] at hcl ⊢; rw [Function.update_of_ne hr]; exact hG.reg r hcl
    · rintro x hx hcl hph'
      by_cases hxp : x = p
      · subst hxp; rw [hlp]; right; intro i hi; simp at hi
      · have hx' : wrote x := hx.resolve_left hxp
        rw [hlq x hxp] at hcl hph' ⊢; exact hG.col1 x hx' hcl hph'
    · rintro x hx hcl hph'
      by_cases hxp : x = p
      · subst hxp; rw [hlp] at hph'; simp at hph'
      · have hx' : wrote x := hx.resolve_left hxp
        rw [hlq x hxp] at hcl hph' ⊢; exact hG.big x hx' hcl hph'
  · -- a type-0 write
    push Not at hA
    obtain ⟨hcl0, hnw⟩ := hA
    have htp : tgt p = none := by
      cases h : tgt p with
      | none => rfl
      | some r => exact absurd (hG.tgt_wrote p r h) hnw
    refine ⟨fun z => z = p ∨ wrote z, Function.update tgt p (some r₀),
      Function.update t0 r₀ (some p), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z r h
      by_cases hzp : z = p
      · exact Or.inl hzp
      · rw [Function.update_of_ne hzp] at h; exact Or.inr (hG.tgt_wrote z r h)
    · intro r z h
      by_cases hr : r = r₀
      · subst hr; simp only [Function.update_self, Option.some.injEq] at h; subst h; simp
      · rw [Function.update_of_ne hr] at h
        have h1 := hG.t0_tgt r z h
        have hzp : z ≠ p := by rintro rfl; rw [htp] at h1; simp at h1
        rw [Function.update_of_ne hzp]; exact h1
    · rintro z (rfl | hz)
      · rw [hlp]; simp
      · by_cases hzp : z = p
        · subst hzp; rw [hlp]; simp
        · rw [hlq z hzp]; exact hG.wrote_ph z hz
    · intro r hcl
      by_cases hr : r = r₀
      · subst hr; right; refine ⟨p, by simp, ?_⟩; rw [hm0]; exact hself
      · rw [hmr r hr] at hcl ⊢; rw [Function.update_of_ne hr]; exact hG.reg r hcl
    · rintro x hx hcl hph'
      by_cases hxp : x = p
      · subst hxp; rw [hlp]; right; intro i hi; simp at hi
      · have hx' : wrote x := hx.resolve_left hxp
        rw [hlq x hxp] at hcl hph' ⊢
        rcases hG.col1 x hx' hcl hph' with h1 | h1
        · exact Or.inl h1
        · right; intro i hi
          obtain ⟨z, hz, ht⟩ := h1 i hi
          have hzp : z ≠ p := by rintro rfl; rw [htp] at ht; simp at ht
          exact ⟨z, hz, by rw [Function.update_of_ne hzp]; exact ht⟩
    · rintro x hx hcl hph'
      by_cases hxp : x = p
      · subst hxp; rw [hlp] at hph'; simp at hph'
      · have hx' : wrote x := hx.resolve_left hxp
        rw [hlq x hxp] at hcl hph' ⊢; exact hG.big x hx' hcl hph'

end Steps


lemma GInv.step {S : Finset P} {wrote : P → Prop} {tgt : P → Option (Fin (k + 1))}
    {t0 : Fin (k + 1) → Option P} {α : List (Label P (laObj P))} {C C' : Cfg P k}
    {ℓ : Label P (laObj P)} (hG : GInv S C wrote tgt t0) (hB : BInv α C)
    (h : (alg1 k).step C ℓ = some C') :
    ∃ (wrote' : P → Prop) (tgt' : P → Option (Fin (k + 1))) (t0' : Fin (k + 1) → Option P),
      GInv S C' wrote' tgt' t0' := by
  cases ℓ with
  | inv p o => exact ⟨_, _, _, hG.inv h⟩
  | ret p o => exact ⟨_, _, _, hG.ret h⟩
  | tau p =>
    obtain ⟨-, -, h3⟩ := step_tau_alg1 h
    rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
    · exact hG.write_step (hB.self p) hph hm hl
    · exact ⟨_, _, _, hG.col1_step hph hm hl⟩
    · exact ⟨_, _, _, hG.col2_step hph hm hl⟩

lemma run_snoc_iff {β : List (Label P (laObj P))} {ℓ : Label P (laObj P)} {C' : Cfg P k} :
    (alg1 k).run (β ++ [ℓ]) = some C' ↔
      ∃ C, (alg1 k).run β = some C ∧ (alg1 k).step C ℓ = some C' := by
  rw [Impl.run, Impl.runFrom_append]
  cases hβ : (alg1 k).runFrom (alg1 k).initCfg β with
  | none => simp [Impl.run, hβ]
  | some C => simp [Impl.run, hβ]

/-- The ghost invariant holds along every extension of an execution in which all registers are
dirty. -/
lemma exists_gInv {S : Finset P} {α₁ : List (Label P (laObj P))} {C₁ : Cfg P k}
    (h₁ : (alg1 k).run α₁ = some C₁) (hdirty : ∀ r, S ⊆ (C₁.mem r).seen)
    (α₂ : List (Label P (laObj P))) {C₂ : Cfg P k} (h₂ : (alg1 k).run (α₁ ++ α₂) = some C₂) :
    ∃ (wrote : P → Prop) (tgt : P → Option (Fin (k + 1))) (t0 : Fin (k + 1) → Option P),
      GInv S C₂ wrote tgt t0 := by
  induction α₂ using List.reverseRecOn generalizing C₂ with
  | nil =>
    rw [List.append_nil, h₁, Option.some.injEq] at h₂; subst h₂
    refine ⟨fun _ => False, fun _ => none, fun _ => none, ?_⟩
    exact ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ h => h.elim,
      fun r h => absurd (hdirty r) h, fun _ h => h.elim, fun _ h => h.elim⟩
  | append_singleton α₂ ℓ ih =>
    rw [← List.append_assoc, run_snoc_iff] at h₂
    obtain ⟨C, hC, hs⟩ := h₂
    obtain ⟨w, t, t', hG⟩ := ih hC
    exact hG.step (bInv_of_run hC) hs

/-- **Lemma A** (obliteration needs `k + 1` processes). If all registers are `S`-dirty at `C₁`
and all registers are `S`-clean at a later configuration `C₂`, then the registers at `C₂`
together have seen at least `k + 1` processes: every `U` containing all their `seen` sets has
`k + 1` elements. -/
theorem card_union_of_obliterate {S : Finset P} {α₁ α₂ : List (Label P (laObj P))}
    {C₁ C₂ : Cfg P k} (h₁ : (alg1 k).run α₁ = some C₁) (h₂ : (alg1 k).run (α₁ ++ α₂) = some C₂)
    (hdirty : ∀ r, S ⊆ (C₁.mem r).seen) (hclean : ∀ r, ¬ S ⊆ (C₂.mem r).seen)
    {U : Finset P} (hU : ∀ r, (C₂.mem r).seen ⊆ U) : k + 1 ≤ U.card := by
  obtain ⟨wrote, tgt, t0, hG⟩ := exists_gInv h₁ hdirty α₂ h₂
  by_cases hbig : ∃ r, k + 1 ≤ (C₂.mem r).seen.card
  · obtain ⟨r, hr⟩ := hbig
    exact hr.trans (Finset.card_le_card (hU r))
  · push Not at hbig
    have hz : ∀ r, ∃ z, t0 r = some z ∧ z ∈ (C₂.mem r).seen := fun r =>
      ((hG.reg r (hclean r)).resolve_left (by have := hbig r; omega))
    refine card_of_tgt (tgt := tgt) (fun i => ?_)
    obtain ⟨z, h1, h2⟩ := hz i
    exact ⟨z, hU i h2, hG.t0_tgt i z h1⟩

end Cslib.SharedMemory.StrangerFree
