import Papers.PODC2019.HotStuff.Chained.Model
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Chained HotStuff with the height check is safe (Theorem 5, repaired)

For the variant `heightCheck` of Algorithm 3 (a replica only processes a proposal `b*` with
`b*.height = curView`), no two nodes committed by correct replicas conflict, for every `n > 3f`
and at most `f` Byzantine replicas.

The proof is by an inductive invariant `Inv` (no execution traces needed) and a strong induction
on the view number of a QC (`extends_of_valid`), which replaces the paper's choice of a
view-minimal "switching" QC `qc_s`.
-/

namespace HotStuff.Chained

open Node Cslib.Quorum

namespace Node

variable {C : Type}

theorem isAnc_refl : ∀ a : Node C, IsAnc a a
  | gen => rfl
  | mk _ _ _ _ => Or.inl rfl

theorem IsAnc.trans {a b : Node C} : ∀ {c : Node C}, IsAnc a b → IsAnc b c → IsAnc a c
  | gen, hab, hbc => by
    simp only [IsAnc] at hbc; subst hbc; exact hab
  | mk p cmd v n, hab, hbc => by
    rcases hbc with rfl | hbc
    · exact hab
    · exact Or.inr (IsAnc.trans hab hbc)

theorem IsAnc.height_le {a : Node C} : ∀ {b : Node C}, IsAnc a b → a.height ≤ b.height
  | gen, h => by simp only [IsAnc] at h; subst h; rfl
  | mk p cmd v n, h => by
    rcases h with rfl | h
    · rfl
    · have := IsAnc.height_le h; simp only [height]; omega

theorem StrictAnc.height_lt {a : Node C} : ∀ {b : Node C}, StrictAnc a b → a.height < b.height
  | gen, h => h.elim
  | mk p cmd v n, h => by have := IsAnc.height_le (b := p) h; simp only [height]; omega

theorem StrictAnc.isAnc {a : Node C} : ∀ {b : Node C}, StrictAnc a b → IsAnc a b
  | gen, h => h.elim
  | mk _ _ _ _, h => Or.inr h

theorem isAnc_of_parent {b p : Node C} (h : b.parent? = some p) : IsAnc p b := by
  cases b with
  | gen => cases h
  | mk q _ _ _ =>
    simp only [parent?, Option.some.injEq] at h; subst h; exact Or.inr (isAnc_refl _)

theorem height_of_parent {b p : Node C} (h : b.parent? = some p) : b.height = p.height + 1 := by
  cases b with
  | gen => cases h
  | mk q _ _ _ => simp only [parent?, Option.some.injEq] at h; subst h; rfl

theorem ne_gen_of_parent {b p : Node C} (h : b.parent? = some p) : b ≠ gen := by
  rintro rfl; cases h

end Node

variable {P C : Type} [Fintype P] [DecidableEq P] [DecidableEq C] {f : ℕ} {F : Finset P}

/-! ### Signatures and quorums -/

theorem signers_mono {V V' : Finset (P × ℕ × Node C)} (h : V ⊆ V') (q : ℕ × Node C) :
    signers F V q ⊆ signers F V' q := by
  intro i hi
  simp only [signers, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.imp_right (fun h' => h h')

theorem Valid.mono {V V' : Finset (P × ℕ × Node C)} (h : V ⊆ V') {q : ℕ × Node C}
    (hq : Valid f F V q) : Valid f F V' q :=
  hq.imp_right fun h' => h'.trans (Finset.card_le_card (signers_mono h q))

theorem mem_votes_of_signer {V : Finset (P × ℕ × Node C)} {q : ℕ × Node C} {r : P}
    (h : r ∈ signers F V q) (hr : r ∉ F) : (r, q.1, q.2) ∈ V := by
  simp only [signers, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.resolve_left hr

/-! ### The inductive invariant -/

/-- Inductive invariant of the `heightCheck` variant. -/
structure Inv (f : ℕ) (F : Finset P) (s : State P C) : Prop where
  view_pos : ∀ r ∉ F, 1 ≤ (s.loc r).view
  vote : ∀ r ∉ F, ∀ u x, (r, u, x) ∈ s.votes → 1 ≤ u ∧ u ≤ (s.loc r).view ∧
    (u = (s.loc r).view → (s.loc r).done = true) ∧ x.height = u ∧ StrictAnc x.jn x ∧
    Valid f F s.votes x.justify
  one_vote : ∀ r ∉ F, ∀ u x y, (r, u, x) ∈ s.votes → (r, u, y) ∈ s.votes → x = y
  lock : ∀ r ∉ F, Valid f F s.votes (s.loc r).lock ∧ (s.loc r).lock.1 < (s.loc r).view
  lock_ge : ∀ r ∉ F, ∀ v b, (r, v, b) ∈ s.votes → Chain2 b → v - 2 ≤ (s.loc r).lock.1
  vote_lock : ∀ r ∉ F, ∀ u x v b, (r, u, x) ∈ s.votes → (r, v, b) ∈ s.votes → v < u →
    Chain2 b → ∃ q : ℕ × Node C, Valid f F s.votes q ∧ v - 2 ≤ q.1 ∧ q.1 < u ∧ SafeNode q x
  commit : ∀ r ∉ F, ∀ b ∈ (s.loc r).committed, ∃ b₂ : Node C, Chain2 b₂ ∧ b₂.jn.jn = b ∧
    ∃ v, Valid f F s.votes (v, b₂)

theorem inv_init : Inv f F (init : State P C) where
  view_pos _ _ := le_rfl
  vote _ _ _ _ h := by simp [init] at h
  one_vote _ _ _ _ _ h := by simp [init] at h
  lock _ _ := ⟨Or.inl ⟨rfl, rfl⟩, Nat.zero_lt_one⟩
  lock_ge _ _ _ _ h := by simp [init] at h
  vote_lock _ _ _ _ _ _ h := by simp [init] at h
  commit _ _ _ h := by simp [init] at h

section Facts

variable (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f)
include hn hF

/-- (F1) Valid QCs are well formed: the view equals the height, and a QC of view `≥ 1` has a
correct voter, who checked that the justify QC of its node is valid and points to an ancestor. -/
theorem Inv.wf {s : State P C} (hI : Inv f F s) {u : ℕ} {x : Node C}
    (h : Valid f F s.votes (u, x)) :
    x.height = u ∧ (u = 0 → x = gen) ∧ (1 ≤ u → StrictAnc x.jn x ∧ Valid f F s.votes x.justify) := by
  rcases h with ⟨h1, h2⟩ | h
  · simp only at h1 h2; subst h1 h2; exact ⟨rfl, fun _ => rfl, fun h => absurd h (by omega)⟩
  · obtain ⟨r, hr, -, hrF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hF h h
    obtain ⟨h1, -, -, h4, h5, h6⟩ := hI.vote r hrF u x (mem_votes_of_signer hr hrF)
    exact ⟨h4, fun h => absurd h (by omega), fun _ => ⟨h5, h6⟩⟩

/-- (F2) Two valid QCs of the same view refer to the same node. -/
theorem Inv.unique {s : State P C} (hI : Inv f F s) {u : ℕ} {x y : Node C}
    (hx : Valid f F s.votes (u, x)) (hy : Valid f F s.votes (u, y)) : x = y := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · rw [(hI.wf hn hF hx).2.1 rfl, (hI.wf hn hF hy).2.1 rfl]
  · have hx' := hx.resolve_left (by rintro ⟨h, -⟩; simp at h; omega)
    have hy' := hy.resolve_left (by rintro ⟨h, -⟩; simp at h; omega)
    obtain ⟨r, hr1, hr2, hrF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hF hx' hy'
    exact hI.one_vote r hrF u x y (mem_votes_of_signer hr1 hrF) (mem_votes_of_signer hr2 hrF)

/-- A valid Two-Chain node `b₂` at view `v` yields valid QCs `(v - 1, b₂.jn)` and
`(v - 2, b₂.jn.jn)`; heights equal views. -/
theorem Inv.chain {s : State P C} (hI : Inv f F s) {b₂ : Node C} (hc : Chain2 b₂) {v : ℕ}
    (hv : Valid f F s.votes (v, b₂)) :
    b₂.height = v ∧ 2 ≤ v ∧ b₂.jv = v - 1 ∧ b₂.jn.jv = v - 2 ∧ b₂.jn.jn.height = v - 2 ∧
      Valid f F s.votes (v - 1, b₂.jn) ∧ Valid f F s.votes (v - 2, b₂.jn.jn) := by
  obtain ⟨hc1, hc2⟩ := hc
  have hh1 := height_of_parent hc1
  have hh2 := height_of_parent hc2
  obtain ⟨hw1, hw2, hw3⟩ := hI.wf hn hF hv
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · exact absurd (hw2 rfl) (ne_gen_of_parent hc1)
    · exact h
  obtain ⟨-, hj⟩ := hw3 hv1
  obtain ⟨hj1, hj2, hj3⟩ := hI.wf hn hF hj
  have hjv1 : 1 ≤ b₂.jv := by
    rcases Nat.eq_zero_or_pos b₂.jv with h | h
    · exact absurd (hj2 h) (ne_gen_of_parent hc2)
    · exact h
  obtain ⟨-, hk⟩ := hj3 hjv1
  obtain ⟨hk1, -, -⟩ := hI.wf hn hF hk
  have e1 : b₂.jv = v - 1 := by omega
  have e2 : b₂.jn.jv = v - 2 := by omega
  refine ⟨hw1, by omega, e1, e2, by omega, ?_, ?_⟩
  · rw [← e1]; exact hj
  · rw [← e2]; exact hk

/-! ### Preservation -/

omit hn hF in
theorem Inv.nextView {s : State P C} (hI : Inv f F s) {r : P} {v : ℕ}
    (ha : Enabled .heightCheck f F (.nextView r v) s) :
    Inv f F (apply .heightCheck (.nextView r v) s) := by
  obtain ⟨hrF, hlt⟩ := ha
  have hloc : ∀ r', (apply .heightCheck (.nextView r v) s : State P C).loc r' =
      if r' = r then { s.loc r with view := v, done := false } else s.loc r' := by
    intro r'; simp [apply, Function.update_apply]
  have hV : (apply .heightCheck (.nextView r v) s).votes = s.votes := rfl
  constructor
  · intro r' hr'; rw [hloc]; split_ifs with h
    · subst h; have := hI.view_pos r' hr'; dsimp; omega
    · exact hI.view_pos r' hr'
  · intro r' hr' u x hx; rw [hV] at hx ⊢; rw [hloc]
    obtain ⟨h1, h2, h3, h4⟩ := hI.vote r' hr' u x hx; split_ifs with h
    · subst h; exact ⟨h1, by dsimp; omega, fun h => by dsimp at h; omega, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
  · rw [hV]; exact hI.one_vote
  · intro r' hr'; rw [hV, hloc]; split_ifs with h
    · subst h; obtain ⟨h1, h2⟩ := hI.lock r' hr'; exact ⟨h1, by dsimp; omega⟩
    · exact hI.lock r' hr'
  · intro r' hr' v' b hb hc; rw [hV] at hb; rw [hloc]; split_ifs with h
    · subst h; exact hI.lock_ge r' hr' v' b hb hc
    · exact hI.lock_ge r' hr' v' b hb hc
  · rw [hV]; exact hI.vote_lock
  · intro r' hr' b hb; rw [hV]; rw [hloc] at hb; split_ifs at hb with h
    · subst h; exact hI.commit r' hr' b hb
    · exact hI.commit r' hr' b hb

theorem Inv.process {s : State P C} (hI : Inv f F s) {r : P} {b : Node C}
    (ha : Enabled .heightCheck f F (.process r b) s) :
    Inv f F (apply .heightCheck (.process r b) s) := by
  obtain ⟨hrF, hdone, hval, hsa, hh⟩ := ha
  have hh := hh rfl
  have hloc : ∀ r', (apply .heightCheck (.process r b) s).loc r' =
      if r' = r then (s.loc r).process .heightCheck b else s.loc r' := by
    intro r'; simp [apply, Function.update_apply]
  have hV : (apply .heightCheck (.process r b) s).votes =
      if SafeNode (s.loc r).lock b then insert (r, (s.loc r).view, b) s.votes else s.votes := rfl
  have hsub : s.votes ⊆ (apply .heightCheck (.process r b) s).votes := by
    rw [hV]; split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl
  have hmem : ∀ r' u x, (r', u, x) ∈ (apply .heightCheck (.process r b) s).votes →
      ((r' = r ∧ u = (s.loc r).view ∧ x = b) ∧ SafeNode (s.loc r).lock b) ∨ (r', u, x) ∈ s.votes := by
    intro r' u x h; rw [hV] at h; split_ifs at h with hs
    · rcases Finset.mem_insert.1 h with h | h
      · simp only [Prod.mk.injEq] at h; exact Or.inl ⟨h, hs⟩
      · exact Or.inr h
    · exact Or.inr h
  have hview : ((s.loc r).process .heightCheck b).view = (s.loc r).view := rfl
  have hdone' : ((s.loc r).process .heightCheck b).done = true := rfl
  have hlock : ((s.loc r).process .heightCheck b).lock =
      if Chain2 b then b.jn.justify else (s.loc r).lock := rfl
  have hcomm : ((s.loc r).process .heightCheck b).committed =
      if Chain2 b ∧ b.jn.jn.parent? = some b.jn.jn.jn then insert b.jn.jn.jn (s.loc r).committed
      else (s.loc r).committed := rfl
  have hvp := hI.view_pos r hrF
  have hnew : Chain2 b → Valid f F s.votes b.jn.justify ∧ b.jn.jv = (s.loc r).view - 2 := by
    intro ⟨hc1, hc2⟩
    have hh1 := height_of_parent hc1
    have hh2 := height_of_parent hc2
    obtain ⟨hw1, hw2, hw3⟩ := hI.wf hn hF hval
    have hjv1 : 1 ≤ b.jv := by
      rcases Nat.eq_zero_or_pos b.jv with h | h
      · exact absurd (hw2 h) (ne_gen_of_parent hc2)
      · exact h
    obtain ⟨-, hk⟩ := hw3 hjv1
    obtain ⟨hk1, -, -⟩ := hI.wf hn hF hk
    exact ⟨hk, by omega⟩
  constructor
  · intro r' hr'; rw [hloc]; split_ifs with h
    · subst h; rw [hview]; exact hvp
    · exact hI.view_pos r' hr'
  · intro r' hr' u x hx; rw [hloc]
    rcases hmem r' u x hx with ⟨⟨hr1, hu1, hx1⟩, -⟩ | hxo
    · subst hr1 hu1 hx1
      rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hview, hdone']
      exact ⟨hvp, le_rfl, fun _ => rfl, hh, hsa, hval.mono hsub⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.vote r' hr' u x hxo
      split_ifs with h
      · subst h; rw [hview, hdone']; exact ⟨h1, h2, fun _ => rfl, h4, h5, h6.mono hsub⟩
      · exact ⟨h1, h2, h3, h4, h5, h6.mono hsub⟩
  · intro r' hr' u x y hx hy
    rcases hmem r' u x hx with ⟨⟨hr1, hu1, hx1⟩, -⟩ | hxo <;>
      rcases hmem r' u y hy with ⟨⟨hr2, hu2, hy2⟩, -⟩ | hyo
    · rw [hx1, hy2]
    · subst hr1 hu1
      exact absurd ((hI.vote r' hr' _ y hyo).2.2.1 rfl) (by simp [hdone])
    · subst hr2 hu2
      exact absurd ((hI.vote r' hr' _ x hxo).2.2.1 rfl) (by simp [hdone])
    · exact hI.one_vote r' hr' u x y hxo hyo
  · intro r' hr'; rw [hloc]; split_ifs with h
    · subst h; rw [hlock, hview]; split_ifs with hc
      · obtain ⟨h1, h2⟩ := hnew hc; exact ⟨h1.mono hsub, show b.jn.jv < _ by omega⟩
      · obtain ⟨h1, h2⟩ := hI.lock r' hr'; exact ⟨h1.mono hsub, h2⟩
    · obtain ⟨h1, h2⟩ := hI.lock r' hr'; exact ⟨h1.mono hsub, h2⟩
  · intro r' hr' v b' hb hc; rw [hloc]; split_ifs with h
    · subst h; rw [hlock]
      have hvle : v ≤ (s.loc r').view := by
        rcases hmem r' v b' hb with ⟨⟨-, hv1, -⟩, -⟩ | hbo
        · exact hv1.le
        · exact (hI.vote r' hr' v b' hbo).2.1
      split_ifs with hcb
      · show v - 2 ≤ b.jn.jv
        rw [(hnew hcb).2]; omega
      · rcases hmem r' v b' hb with ⟨⟨-, -, hb1⟩, -⟩ | hbo
        · subst hb1; exact absurd hc hcb
        · exact hI.lock_ge r' hr' v b' hbo hc
    · rcases hmem r' v b' hb with ⟨⟨hr1, -, -⟩, -⟩ | hbo
      · exact absurd hr1 h
      · exact hI.lock_ge r' hr' v b' hbo hc
  · intro r' hr' u x v b' hx hb hvu hc
    rcases hmem r' u x hx with ⟨⟨hr1, hu1, hx1⟩, hsafe⟩ | hxo
    · subst hr1 hu1 hx1
      rcases hmem r' v b' hb with ⟨⟨-, hv1, -⟩, -⟩ | hbo
      · omega
      · obtain ⟨h1, h2⟩ := hI.lock r' hr'
        exact ⟨(s.loc r').lock, h1.mono hsub, hI.lock_ge r' hr' v b' hbo hc, h2, hsafe⟩
    · rcases hmem r' v b' hb with ⟨⟨hr1, hv1, -⟩, -⟩ | hbo
      · subst hr1 hv1; have := (hI.vote r' hr' u x hxo).2.1; omega
      · obtain ⟨q, h1, h2, h3, h4⟩ := hI.vote_lock r' hr' u x v b' hxo hbo hvu hc
        exact ⟨q, h1.mono hsub, h2, h3, h4⟩
  · intro r' hr' c hcm; rw [hloc] at hcm; split_ifs at hcm with h
    · subst h; rw [hcomm] at hcm; split_ifs at hcm with h3
      · rcases Finset.mem_insert.1 hcm with rfl | hcm
        · exact ⟨b.jn, ⟨h3.1.2, h3.2⟩, rfl, b.jv, hval.mono hsub⟩
        · obtain ⟨b₂, h1, h2, v, h4⟩ := hI.commit r' hr' c hcm
          exact ⟨b₂, h1, h2, v, h4.mono hsub⟩
      · obtain ⟨b₂, h1, h2, v, h4⟩ := hI.commit r' hr' c hcm
        exact ⟨b₂, h1, h2, v, h4.mono hsub⟩
    · obtain ⟨b₂, h1, h2, v, h4⟩ := hI.commit r' hr' c hcm
      exact ⟨b₂, h1, h2, v, h4.mono hsub⟩

theorem Inv.step {s s' : State P C} (hI : Inv f F s) (hs : Step .heightCheck f F s s') :
    Inv f F s' := by
  obtain ⟨a, ha, rfl⟩ := hs
  cases a with
  | nextView r v => exact hI.nextView ha
  | process r b => exact hI.process hn hF ha

theorem Reachable.inv {s : State P C} (hs : Reachable .heightCheck f F s) : Inv f F s := by
  induction hs with
  | refl => exact inv_init
  | tail _ hst ih => exact ih.step hn hF hst

/-! ### The key lemma and Theorem 5 -/

/-- Key lemma (the paper's "switching point" argument, as a strong induction on views): if `b₂`
is a Two-Chain node with a valid QC (so `w := b₂.jn.jn` has valid QCs at views `h, h+1, h+2`,
where `h = height w`), then every valid QC of view `≥ h` refers to a node extending `w`. -/
theorem Inv.extends_of_valid {s : State P C} (hI : Inv f F s) {b₂ : Node C} (hc : Chain2 b₂)
    {v : ℕ} (hv : Valid f F s.votes (v, b₂)) :
    ∀ u x, Valid f F s.votes (u, x) → v - 2 ≤ u → IsAnc b₂.jn.jn x := by
  obtain ⟨-, hv2, -, -, -, hv1', hv0⟩ := hI.chain hn hF hc hv
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro x hx hu
  rcases (by omega : u = v - 2 ∨ u = v - 1 ∨ u = v ∨ v < u) with rfl | rfl | rfl | hvu
  · rw [hI.unique hn hF hx hv0]; exact isAnc_refl _
  · rw [hI.unique hn hF hx hv1']; exact isAnc_of_parent hc.2
  · rw [hI.unique hn hF hx hv]; exact (isAnc_of_parent hc.2).trans (isAnc_of_parent hc.1)
  · -- a correct replica `r` voted both for `x` (view `u`) and for `b₂` (view `v < u`)
    have hx' := hx.resolve_left (by rintro ⟨h, -⟩; simp at h; omega)
    have hv' := hv.resolve_left (by rintro ⟨h, -⟩; simp at h; omega)
    obtain ⟨r, hr1, hr2, hrF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hF hx' hv'
    have hvx := mem_votes_of_signer hr1 hrF
    have hvb := mem_votes_of_signer hr2 hrF
    -- when voting for `x`, `r` was locked on a valid QC `q` of view in `[v - 2, u)`
    obtain ⟨q, hq, hq1, hq2, hsafe⟩ := hI.vote_lock r hrF u x v b₂ hvx hvb hvu hc
    have hqw : IsAnc b₂.jn.jn q.2 := ih q.1 hq2 q.2 hq hq1
    obtain ⟨-, -, -, hxh, hxs, hxj⟩ := hI.vote r hrF u x hvx
    rcases hsafe with h | h
    · exact hqw.trans h
    · have hjh := (hI.wf hn hF hxj).1
      have hlt := hxs.height_lt
      have : IsAnc b₂.jn.jn x.jn := ih x.jv (by omega) x.jn hxj
        (by omega)
      exact this.trans hxs.isAnc

end Facts

/-- **Theorem 5, repaired.** For Algorithm 3 with the additional check `b*.height = curView`,
if `n > 3f` and at most `f` replicas are Byzantine, then in every reachable state no two nodes
committed by correct replicas (the same or different ones) conflict. -/
theorem theorem5_fixed (hn : 3 * f < Fintype.card P) (hF : F.card ≤ f) :
    Safe P C .heightCheck f F := by
  intro s hs r₁ r₂ h₁ h₂ b₁ hb₁ b₂ hb₂
  have hI := hs.inv hn hF
  obtain ⟨c₁, hc₁, rfl, v₁, hv₁⟩ := hI.commit r₁ h₁ b₁ hb₁
  obtain ⟨c₂, hc₂, rfl, v₂, hv₂⟩ := hI.commit r₂ h₂ b₂ hb₂
  obtain ⟨-, -, -, -, -, -, hq₁⟩ := hI.chain hn hF hc₁ hv₁
  obtain ⟨-, -, -, -, -, -, hq₂⟩ := hI.chain hn hF hc₂ hv₂
  rintro ⟨hn1, hn2⟩
  rcases le_total v₁ v₂ with h | h
  · exact hn1 (hI.extends_of_valid hn hF hc₁ hv₁ _ _ hq₂ (by omega))
  · exact hn2 (hI.extends_of_valid hn hF hc₂ hv₂ _ _ hq₁ (by omega))

end HotStuff.Chained
