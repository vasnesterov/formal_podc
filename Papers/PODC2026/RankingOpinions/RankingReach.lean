import Papers.PODC2026.RankingOpinions.RankingInv
import Mathlib.Data.Fintype.Fin
import Podc.Foundations.Data.Fin.Cyclic

/-!
# The Ranking protocol: reachability, part 1 (Lemmas 6.8–6.11)

From every configuration satisfying the global invariants we reach, in turn, a configuration with
* exactly one token per color (Lemma 6.8),
* pairwise distinct token rankings (Lemma 6.9),
* all bras and kets consistent with the token rankings (Lemma 6.10),
* Circles stabilized on the rankings (Lemma 6.11).

Each phase is proved by a well-founded progress measure: from every configuration of the phase
that is not yet done, one interaction (with a rule that we compute explicitly) decreases it.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ} [NeZero k] {A : Type*} [DecidableEq A] [Fintype A]

/-! ### Generic tools -/

/-- A measure `∑ₓ f (C x)` decreases if only `a, b` change and their contribution decreases. -/
lemma sum_lt_of_pair (f : RState k → ℕ) {C C' : Config A (RState k)} {a b : A} (hab : a ≠ b)
    (hrest : ∀ x, x ≠ a → x ≠ b → C' x = C x)
    (hlt : f (C' a) + f (C' b) < f (C a) + f (C b)) :
    ∑ x, f (C' x) < ∑ x, f (C x) := by
  rw [sum_split (fun x => f (C' x)) hab, sum_split (fun x => f (C x)) hab]
  have : ∑ x ∈ (univ.erase a).erase b, f (C' x) = ∑ x ∈ (univ.erase a).erase b, f (C x) := by
    apply Finset.sum_congr rfl
    intro x hx; simp only [mem_erase] at hx; rw [hrest x hx.2.1 hx.1]
  omega

/-- At most one token per color. -/
def OneTok (C : Config A (RState k)) : Prop :=
  ∀ a b, (C a).tok → (C b).tok → (C a).kc = (C b).kc → a = b

lemma OneTok.of_eq {C C' : Config A (RState k)} (h : OneTok C)
    (he : ∀ x, (C' x).tok = (C x).tok ∧ (C' x).kc = (C x).kc) : OneTok C' := by
  intro a b ha hb hc
  rw [(he a).1] at ha; rw [(he b).1] at hb; rw [(he a).2, (he b).2] at hc
  exact h a b ha hb hc

lemma OneTok.of_swap {C C' : Config A (RState k)} (h : OneTok C) {a b : A}
    (he : ∀ x, (C' x).tok = (C (Equiv.swap a b x)).tok ∧
      (C' x).kc = (C (Equiv.swap a b x)).kc) : OneTok C' := by
  intro x y hx hy hc
  rw [(he x).1] at hx; rw [(he y).1] at hy; rw [(he x).2, (he y).2] at hc
  exact (Equiv.swap a b).injective (h _ _ hx hy hc)

/-- The token of color `c` is held by `a` (in the presence of `OneTok`). -/
lemma OneTok.holder {C : Config A (RState k)} (h : OneTok C) {a b : A} (ha : (C a).tok)
    (hb : (C b).tok) (hc : (C a).kc = (C b).kc) : a = b := h a b ha hb hc

/-- The token rankings are given by `σ`. -/
def TR (σ : Fin k → Fin k) (C : Config A (RState k)) : Prop :=
  ∀ a, (C a).tok → (C a).kr = σ (C a).kc

/-- All bras and kets are consistent with `σ`. -/
def Cons (σ : Fin k → Fin k) (C : Config A (RState k)) : Prop := ∀ a, SCons σ (C a)

lemma Cons.tr {σ : Fin k → Fin k} {C : Config A (RState k)} (h : Cons σ C) : TR σ C :=
  fun a _ => (h a).2

/-! ### Phase 1: one token per color (Lemma 6.8) -/

/-- Number of tokens. -/
def ntoks (C : Config A (RState k)) : ℕ := ∑ x, (C x).tok.toNat

lemma phase1 (input : A → Fin k) : ∀ C : Config A (RState k), Inv input C →
    ∃ C', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' := by
  intro C
  induction h : ntoks C using Nat.strong_induction_on generalizing C with
  | _ n ih =>
  intro hC
  by_cases h1 : OneTok C
  · exact ⟨C, Relation.ReflTransGen.refl, hC, h1⟩
  · simp only [OneTok, not_forall] at h1
    obtain ⟨a, b, ha, hb, hc, hab⟩ := h1
    set C1 := (ranking k).interact C a b
    have hlt : ntoks C1 < n := by
      rw [← h]
      apply sum_lt_of_pair (fun s => s.tok.toNat) hab
      · intro x hxa hxb; simp only [C1, interact_apply, ite_eq_right hxa, ite_eq_right hxb]
      · simp only [C1, interact_apply, ite_eq_right (Ne.symm hab)]
        exact rδ_del ha hb hc
    obtain ⟨C', h1, h2, h3⟩ := ih _ hlt C1 rfl (hC.step ⟨a, b, hab, rfl⟩)
    exact ⟨C', (step_of hab).trans h1, h2, h3⟩

/-! ### Phase 2: distinct token rankings (Lemma 6.9) -/

lemma Inv.holder {input : A → Fin k} {C : Config A (RState k)} (hC : Inv input C) (c : Fin k) :
    ∃ a, (C a).tok ∧ (C a).kc = c := hC.tok c

/-- One application of rule (3). -/
lemma phase2_step {input : A → Fin k} {C : Config A (RState k)} {σ : Fin k → Fin k}
    (hC : Inv input C) (h1 : OneTok C) (h2 : TR σ C) {c d : Fin k} (hcd : c < d)
    (he : σ c = σ d) :
    ∃ C', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ TR (Function.update σ d (σ d + 1)) C' := by
  obtain ⟨a, ha, hac⟩ := hC.holder c
  obtain ⟨b, hb, hbd⟩ := hC.holder d
  have hab : a ≠ b := by rintro rfl; rw [hac] at hbd; exact hcd.ne hbd
  have hr := rδ_r3 (a := C a) (b := C b) ha hb (by rw [h2 a ha, h2 b hb, hac, hbd, he])
    (by rw [hac, hbd]; exact hcd) (hC.normal a)
  have hI := interact_eq hr
  refine ⟨_, step_of hab, hC.step ⟨a, b, hab, rfl⟩, ?_, ?_⟩
  · apply h1.of_eq; intro x; rw [hI]; dsimp only; split_ifs with hx hx'
    · subst hx; exact ⟨rfl, rfl⟩
    · subst hx'; exact ⟨norm_tok _, norm_kc _⟩
    · exact ⟨rfl, rfl⟩
  · intro x hx; rw [hI] at hx ⊢; dsimp only at hx ⊢; split_ifs at hx ⊢ with hxa hxb
    · subst hxa; rw [h2 x ha, hac, Function.update_of_ne hcd.ne]
    · subst hxb; rw [norm_kr, norm_kc]; simp only; rw [hbd, Function.update_self, h2 x hb, hbd]
    · have : (C x).kc ≠ d := fun e => hxb (h1 x b hx hb (e.trans hbd.symm))
      rw [h2 x hx, Function.update_of_ne this]

lemma phase2_inner {input : A → Fin k} (d : Fin k) (j : ℕ) :
    ∀ (C : Config A (RState k)) (σ : Fin k → Fin k), Inv input C → OneTok C → TR σ C →
    (· + 1)^[j] (σ d) ∉ σ '' {c | c < d} →
    ∃ C' σ', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ TR σ' C' ∧ (∀ c, c ≠ d → σ' c = σ c) ∧
      σ' d ∉ σ '' {c | c < d} := by
  induction j with
  | zero =>
    intro C σ hC h1 h2 hj
    exact ⟨C, σ, Relation.ReflTransGen.refl, hC, h1, h2, fun _ _ => rfl, by simpa using hj⟩
  | succ j ih =>
    intro C σ hC h1 h2 hj
    by_cases hd : σ d ∈ σ '' {c | c < d}
    · obtain ⟨c, hc, he⟩ := hd
      obtain ⟨C1, r1, i1, o1, t1⟩ := phase2_step hC h1 h2 hc he
      set σ1 := Function.update σ d (σ d + 1)
      have himg : σ1 '' {c | c < d} = σ '' {c | c < d} := by
        apply Set.image_congr; intro c hc; exact Function.update_of_ne (ne_of_lt hc) _ _
      have hj' : (· + 1)^[j] (σ1 d) ∉ σ1 '' {c | c < d} := by
        rw [himg]; simp only [σ1, Function.update_self]
        rwa [← Function.iterate_succ_apply]
      obtain ⟨C', σ', r', i', o', t', hrest, hnot⟩ := ih C1 σ1 i1 o1 t1 hj'
      refine ⟨C', σ', r1.trans r', i', o', t', fun c hc => ?_, by rwa [← himg]⟩
      rw [hrest c hc]; exact Function.update_of_ne hc _ _
    · exact ⟨C, σ, Relation.ReflTransGen.refl, hC, h1, h2, fun _ _ => rfl, hd⟩

lemma phase2_outer {input : A → Fin k} (n : ℕ) (hn : n ≤ k) :
    ∀ C : Config A (RState k), Inv input C → OneTok C →
    ∃ C' σ, (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ TR σ C' ∧
      Set.InjOn σ {c | c.val < n} := by
  induction n with
  | zero =>
    intro C hC h1
    choose a ha using hC.tok
    refine ⟨C, fun c => (C (a c)).kr, Relation.ReflTransGen.refl, hC, h1, ?_, ?_⟩
    · intro x hx
      have := h1 x (a (C x).kc) hx (ha _).1 (ha _).2.symm
      simp only; rw [← this]
    · intro c hc; simp at hc
  | succ n ih =>
    intro C hC h1
    obtain ⟨C1, σ1, r1, i1, o1, t1, inj1⟩ := ih (by omega) C hC h1
    set d : Fin k := ⟨n, by omega⟩
    -- a free ranking
    obtain ⟨y, hy⟩ : ∃ y, y ∉ σ1 '' {c | c < d} := by
      by_contra hall; push Not at hall
      have hsub : (univ : Finset (Fin k)) ⊆ (univ.filter (· < d)).image σ1 := by
        intro y _
        obtain ⟨c, hc, rfl⟩ := hall y
        exact mem_image_of_mem _ (by simpa using hc)
      have := card_le_card hsub
      rw [card_univ, Fintype.card_fin] at this
      have h2 := card_image_le (s := univ.filter (· < d)) (f := σ1)
      have h3 : (univ.filter (· < d)).card = n := by
        have : univ.filter (· < d) = univ.filter (fun c : Fin k => (c : ℕ) < n) := by
          ext c; simp [Fin.lt_def, d]
        rw [this, Fin.card_filter_val_lt]; omega
      omega
    obtain ⟨j, hj⟩ := Fin.exists_iterate_add_one_eq (σ1 d) y
    rw [← hj] at hy
    obtain ⟨C', σ', r', i', o', t', hrest, hnot⟩ := phase2_inner d j C1 σ1 i1 o1 t1 hy
    refine ⟨C', σ', r1.trans r', i', o', t', ?_⟩
    intro c hc c' hc' he
    simp only [Set.mem_ofPred_eq] at hc hc'
    have key : ∀ c, c.val < n → σ' c = σ1 c := fun c h =>
      hrest c (fun e => by rw [e] at h; simp [d] at h)
    by_cases h1 : c.val < n
    · by_cases h2 : c'.val < n
      · rw [key c h1, key c' h2] at he; exact inj1 h1 h2 he
      · have : c' = d := Fin.ext (by simp [d]; omega)
        subst this
        exact absurd ⟨c, h1, (key c h1).symm.trans he⟩ hnot
    · have : c = d := Fin.ext (by simp [d]; omega)
      subst this
      by_cases h2 : c'.val < n
      · exact absurd ⟨c', h2, (key c' h2).symm.trans he.symm⟩ hnot
      · exact Fin.ext (by simp [d] at *; omega)

/-- **Lemma 6.9**: distinct token rankings. -/
lemma phase2 {input : A → Fin k} (C : Config A (RState k)) (hC : Inv input C) (h1 : OneTok C) :
    ∃ C' σ, (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ TR σ C' ∧ Function.Injective σ := by
  obtain ⟨C', σ, r, i, o, t, inj⟩ := phase2_outer k le_rfl C hC h1
  exact ⟨C', σ, r, i, o, t, fun c c' he => inj c.isLt c'.isLt he⟩

/-! ### Phase 3: consistency (Lemma 6.10) -/

/-- Number of fields of a state inconsistent with `σ`. -/
def incon (σ : Fin k → Fin k) (s : RState k) : ℕ :=
  (if s.br = σ s.bc then 0 else 1) + (if s.kr = σ s.kc then 0 else 1)

lemma tok_false {s : RState k} (h : ¬ s.tok) : s.tok = false := by simpa using h

/-- **Lemma 6.10**: broadcasting the token rankings (rule (4)) makes all bras and kets consistent. -/
lemma phase3 {input : A → Fin k} {σ : Fin k → Fin k} (hσ : Function.Injective σ) :
    ∀ C : Config A (RState k), Inv input C → OneTok C → TR σ C →
    ∃ C', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ Cons σ C' := by
  intro C
  induction h : ∑ x, incon σ (C x) using Nat.strong_induction_on generalizing C with
  | _ n ih =>
  intro hC h1 h2
  -- one step at `(g, a)` that only changes `a`, keeping its token and ket, and decreasing `incon`
  have key : ∀ g a s, g ≠ a → rδ (C g) (C a) = (C g, s) → s.tok = (C a).tok → s.kc = (C a).kc →
      (s.tok → s.kr = (C a).kr) → incon σ s < incon σ (C a) →
      ∃ C', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ Cons σ C' := by
    intro g a s hga hr hst hsc hsr hlt
    have hI := interact_eq hr
    have o1 : OneTok ((ranking k).interact C g a) := by
      apply h1.of_eq; intro x; rw [hI]; dsimp only
      split_ifs with h3 h4
      · subst h3; exact ⟨rfl, rfl⟩
      · subst h4; exact ⟨hst, hsc⟩
      · exact ⟨rfl, rfl⟩
    have t1 : TR σ ((ranking k).interact C g a) := by
      intro x hx; rw [hI] at hx ⊢; dsimp only at hx ⊢
      split_ifs at hx ⊢ with h3 h4
      · subst h3; exact h2 x hx
      · subst h4; rw [hsr hx, hsc]; exact h2 x (hst ▸ hx)
      · exact h2 x hx
    have hlt' : ∑ x, incon σ ((ranking k).interact C g a x) < n := by
      rw [← h]
      apply sum_lt_of_pair (incon σ) hga
      · intro x hx1 hx2; rw [hI]; simp [hx1, hx2]
      · rw [hI]; simp only [↓reduceIte, ite_eq_right hga.symm]; omega
    obtain ⟨C', r', i', o', c'⟩ := ih _ hlt' _ rfl (hC.step ⟨g, a, hga, rfl⟩) o1 t1
    exact ⟨C', (step_of hga).trans r', i', o', c'⟩
  by_cases hk : ∀ a, (C a).kr = σ (C a).kc
  · by_cases hb : ∀ a, (C a).br = σ (C a).bc
    · exact ⟨C, Relation.ReflTransGen.refl, hC, h1, fun a => ⟨hb a, hk a⟩⟩
    -- an inconsistent bra
    push Not at hb
    obtain ⟨a, ha⟩ := hb
    obtain ⟨g, hg, hgc⟩ := hC.holder (C a).bc
    have hga : g ≠ a := by
      rintro rfl
      exact ha (by rw [hC.normal g hg hgc.symm, hk g, hgc])
    have hr := rδ_r4b (h := C g) (a := C a) hg hgc.symm (by rw [h2 g hg, hgc]; exact ha)
      (fun h' => hga (h1 g a hg h'.1 h'.2.symm))
      (fun ht e => hga (h1 g a hg ht (hσ (by rw [← h2 g hg, ← h2 a ht, e]))))
      (fun _ e => by rw [hk a, hk g, e]) (hC.normal g)
    refine key g a _ hga hr rfl rfl (fun _ => rfl) ?_
    unfold incon; simp only; rw [h2 g hg, hgc, ite_eq_left rfl, ite_eq_right ha]
    split_ifs <;> omega
  -- an inconsistent ket
  push Not at hk
  obtain ⟨a, ha⟩ := hk
  have hat : (C a).tok = false := tok_false (fun ht => ha (h2 a ht))
  obtain ⟨g, hg, hgc⟩ := hC.holder (C a).kc
  have hga : g ≠ a := by rintro rfl; rw [hg] at hat; exact Bool.noConfusion hat
  have hr := rδ_r4a (h := C g) (a := C a) hg hat hgc (by rw [h2 g hg, hgc]; exact ha)
    (hC.normal g)
  refine key g a _ hga hr rfl rfl (fun ht => by rw [hat] at ht; exact Bool.noConfusion ht) ?_
  unfold incon; simp only; rw [h2 g hg, hgc, ite_eq_left rfl, ite_eq_right ha]
  split_ifs <;> omega

/-! ### Phase 4: Circles stabilizes on the rankings (Lemma 6.11) -/

/-- The braket configuration on rankings. -/
def brk (C : Config A (RState k)) : Config A (Braket k) := fun x => ((C x).br, (C x).kr)

/-- **Lemma 6.11**: from a consistent configuration, Circles (rule (5)) stabilizes. -/
lemma phase4 {input : A → Fin k} {σ : Fin k → Fin k} :
    ∀ C : Config A (RState k), Inv input C → OneTok C → Cons σ C →
    ∃ C', (ranking k).Reachable C C' ∧ Inv input C' ∧ OneTok C' ∧ Cons σ C' ∧
      Stable (brk C') := by
  intro C
  induction h : Fintype.card A * 3 ^ k - pot (brk C) using Nat.strong_induction_on
    generalizing C with
  | _ n ih =>
  intro hC h1 h2
  by_cases hs : Stable (brk C)
  · exact ⟨C, Relation.ReflTransGen.refl, hC, h1, h2, hs⟩
  simp only [Stable, not_forall, not_not] at hs
  obtain ⟨a, b, hab, hp⟩ := hs
  have hr := rδ_r5 (h2 a) (h2 b) hp
  have hI := interact_eq hr
  have hbrk : brk ((ranking k).interact C a b) = (circlesCore k).interact (brk C) a b := by
    rw [core_interact _ hab, ite_eq_left hp, hI]
    funext x
    simp only [brk]
    split_ifs with h3 h4
    · subst h3; simp
    · subst h4; simp
    · simp [Equiv.swap_apply_of_ne_of_ne h3 h4]
  have hlt := pot_lt_interact (C := brk C) hab hp
  have hle := pot_le ((circlesCore k).interact (brk C) a b)
  obtain ⟨C', r', i', o', c', s'⟩ := ih _ (by rw [← h, hbrk]; omega) _ rfl
    (hC.step ⟨a, b, hab, rfl⟩)
    (h1.of_swap (a := a) (b := b) (fun x => by
      rw [hI]; dsimp only; split_ifs with h3 h4
      · subst h3; simp
      · subst h4; simp
      · simp [Equiv.swap_apply_of_ne_of_ne h3 h4]))
    (fun x => by
      rw [hI]; dsimp only; split_ifs with h3 h4
      · subst h3; exact ⟨(h2 x).1, (h2 b).2⟩
      · subst h4; exact ⟨(h2 x).1, (h2 a).2⟩
      · exact h2 x)
  exact ⟨C', (step_of hab).trans r', i', o', c', s'⟩

end RankingOpinions.Ranking
