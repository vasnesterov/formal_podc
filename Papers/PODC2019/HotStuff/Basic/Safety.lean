import Papers.PODC2019.HotStuff.Basic.Invariants

/-!
# Basic HotStuff: safety (Theorem 2)

**Theorem 2** of the paper: two conflicting nodes cannot both be committed by correct replicas.

## The paper's proof and its gap

The paper fixes a commit QC `qc₁` on `w` (view `v₁`) and takes the *lowest view* `v_s ∈ (v₁, v₂]`
with a valid `prepareQC` `qc_s` on a node *conflicting* with `w`. It then claims that a correct
replica `r` in both quorums is still locked "on the branch led by `w`" when it votes for `qc_s`,
and that the justification of `qc_s` cannot have a view `> v₁` "by minimality of `v_s`". Both
steps are not justified by view-minimality over *conflicting* nodes:

* `r`'s lock may have moved (at some view in `(v₁, v_s)`) to a `precommitQC` on a *strict
  ancestor* of `w` — such a node does not conflict with `w`, so minimality says nothing, and a
  proposal conflicting with `w` may well extend it;
* the justification `m.justify` of the proposal may be a QC on a common ancestor of `w` and
  `qc_s.node` (not conflicting with `w`) with a view in `(v₁, v_s)`, or a QC with a view `> v_s`
  (correct replicas never check that `m.justify.viewNumber < curView`, and before GST replicas
  may be in different views), again not excluded by minimality.

The statement is nevertheless true. We prove it with a different invariant: call a `prepareQC`
*bad* if its view is `> v₁` and its node does *not extend* `w` (this includes ancestors of `w`).
Argue about the **first moment in time** at which a bad QC becomes valid rather than about the
smallest view: before that moment, a correct replica that voted `commit` for `w` at `v₁` is locked
on a node extending `w`, and every justification with a view `> v₁` extends `w`, so it never votes
for a node not extending `w`. Hence once a bad QC is valid, at most `f` correct replicas have
voted (or can still vote) `commit` for `w` at `v₁`, and the commit QC on `w` can never form
(`SInv.inv1`). This is formalized below as a state invariant (no traces needed).
-/

namespace HotStuff.Basic

open Classical

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {F : Finset P}

/-- A *bad* QC (relative to a commit of `w` at view `v₁`): a valid `prepareQC` with a view
`> v₁` on a node that does not extend `w`. -/
def Bad (f : ℕ) (F : Finset P) (s : St P C) (v₁ : ℕ) (w : Node C) : Prop :=
  ∃ u x, v₁ < u ∧ ¬ w <:+ x ∧ Valid f F s.votes ⟨.prepare, u, x⟩

/-- Correct replicas that voted `commit` for `(v₁, w)` or may still do so. -/
noncomputable def Pot (F : Finset P) (s : St P C) (v₁ : ℕ) (w : Node C) : Finset P :=
  Finset.univ.filter fun r => r ∉ F ∧ ((r, (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes ∨
    (s.loc r).view < v₁ ∨ ((s.loc r).view = v₁ ∧ (s.loc r).phase ≤ 2))

/-- The safety invariant for a fixed `(v₁, w)`. -/
structure SInv (f : ℕ) (F : Finset P) (s : St P C) (v₁ : ℕ) (w : Node C) : Prop where
  inv2 : ¬ Bad f F s v₁ w → ∀ r ∉ F, (r, (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes → ∀ u x, v₁ < u →
    (r, (⟨.prepare, u, x⟩ : QC C)) ∈ s.votes → w <:+ x
  inv1 : Bad f F s v₁ w → (Pot F s v₁ w).card + F.card < Fintype.card P - f

variable (hF : F.card ≤ f) (h3 : 3 * f < Fintype.card P)
include hF h3

/-- Before any bad QC exists, a correct replica that voted `commit` for `w` at `v₁` is locked on
a node extending `w`, with a lock view `≥ v₁`. -/
theorem lock_extends {s : St P C} (hI : Inv f F s) {v₁ : ℕ} {w : Node C}
    (hnb : ¬ Bad f F s v₁ w) {r : P} (hr : r ∉ F) (hc : (r, (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes) :
    w <:+ (s.loc r).lock.node ∧ v₁ ≤ (s.loc r).lock.view := by
  have h2 : 2 * f < Fintype.card P := by omega
  have hL := hI.loc r hr
  have hge := hL.lock_ge _ hc rfl
  have hv1 := (hL.vote _ hc).1
  refine ⟨?_, hge⟩
  rcases Nat.lt_or_ge v₁ (s.loc r).lock.view with hlt | hle
  · by_contra hw
    exact hnb ⟨_, _, hlt, hw, hI.valid_prepare hF h2 hL.lock_valid.1⟩
  · have heq : (s.loc r).lock.view = v₁ := by simp at hge ⊢; omega
    have hpc := (hL.just _ hc).2 rfl
    have := hI.node_eq hF h3 hL.lock_valid.1 hpc heq
    rw [this]

/-- Before any bad QC exists, such a replica only votes for nodes extending `w`. -/
theorem vote_extends {s : St P C} (hI : Inv f F s) {v₁ : ℕ} {w : Node C}
    (hnb : ¬ Bad f F s v₁ w) {r : P} (hr : r ∉ F) (hc : (r, (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes)
    {x : Node C} {j : QC C} (hj : Valid f F s.votes j) (hjx : j.node <:+ x)
    (hsafe : SafeNode (s.loc r).lock x j) : w <:+ x := by
  have h2 : 2 * f < Fintype.card P := by omega
  obtain ⟨hw, hge⟩ := lock_extends hF h3 hI hnb hr hc
  rcases hsafe with hs | hs
  · exact hw.trans hs
  · by_contra hwx
    have hjw : ¬ w <:+ j.node := fun h => hwx (h.trans hjx)
    exact hnb ⟨_, _, by omega, hjw, hI.valid_prepare hF h2 hj⟩

omit hF h3 in
theorem mem_step_votes {s : St P C} {r r' : P} {o : Option (QC C)} {q : QC C} :
    (r', q) ∈ s.votes ∪ newVotes r o ↔ (r', q) ∈ s.votes ∨ (r' = r ∧ o = some q) := by
  rw [Set.mem_union, mem_newVotes]

/-- The heart of the argument: if no bad QC exists before a step, then after the step no correct
replica has voted both `commit` for `(v₁, w)` and `prepare` for a node not extending `w` at a
higher view. -/
theorem no_commit_and_bad {s : St P C} (hI : Inv f F s) {v₁ : ℕ} {w : Node C}
    (hS : SInv f F s v₁ w) (hnb : ¬ Bad f F s v₁ w) {r : P} {l' : Loc C} {o : Option (QC C)}
    (hl : LStep f F s.votes (s.loc r) l' o) {r' : P} (hr' : r' ∉ F)
    (hc : (r', (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes ∪ newVotes r o) {u : ℕ} {x : Node C}
    (hu : v₁ < u) (hp : (r', (⟨.prepare, u, x⟩ : QC C)) ∈ s.votes ∪ newVotes r o) :
    w <:+ x := by
  rw [mem_step_votes] at hc hp
  rcases hc with hc | ⟨rfl, ho⟩
  · rcases hp with hp | ⟨rfl, ho⟩
    · exact hS.inv2 hnb r' hr' hc u x hu hp
    · cases hl with
      | prepVote x' j _ hj hjx hsafe =>
        simp only [Option.some.injEq, QC.mk.injEq] at ho
        obtain ⟨-, -, rfl⟩ := ho
        exact vote_extends hF h3 hI hnb hr' hc hj hjx hsafe
      | _ => simp_all
  · rcases hp with hp | ⟨-, ho'⟩
    · have hv := ((hI.loc r' hr').vote _ hp).2.1
      cases hl with
      | commitVote q _ _ _ _ =>
        simp only [Option.some.injEq, QC.mk.injEq] at ho
        simp at hv; omega
      | _ => simp_all
    · rw [ho] at ho'; simp at ho'

omit hF h3 in
/-- `Pot` can only shrink. -/
theorem pot_mono {s : St P C} {v₁ : ℕ} {w : Node C} {r : P} {l' : Loc C} {o : Option (QC C)}
    (hl : LStep f F s.votes (s.loc r) l' o) :
    Pot F ⟨Function.update s.loc r l', s.votes ∪ newVotes r o⟩ v₁ w ⊆ Pot F s v₁ w := by
  intro r' hr'
  simp only [Pot, Finset.mem_filter, Finset.mem_univ, true_and] at hr' ⊢
  refine ⟨hr'.1, ?_⟩
  obtain ⟨-, hr'⟩ := hr'
  rw [mem_step_votes] at hr'
  by_cases h : r' = r
  · subst h
    simp only [Function.update_self] at hr'
    cases hl with
    | prepVote x j h0 _ _ _ => simp_all
    | prepSkip h0 => simp_all
    | precommitVote q h1 _ _ _ => simp_all
    | commitVote q h2 _ _ _ =>
      simp only [Option.some.injEq, QC.mk.injEq] at hr'
      rcases hr' with (hr' | ⟨-, -, h', -⟩) | hr' | hr'
      · exact Or.inl hr'
      · right; right; exact ⟨h', by omega⟩
      · exact Or.inr (Or.inl hr')
      · right; right; exact ⟨hr'.1, by simp at hr'⟩
    | decide q h3 _ _ _ => simp_all
    | newView v hlt =>
      rcases hr' with (hr' | ⟨-, h'⟩) | hr' | hr'
      · exact Or.inl hr'
      · simp at h'
      · right; left; simp at hr'; omega
      · right; left; simp at hr'; omega
  · simp only [Function.update_of_ne h] at hr'
    rcases hr' with (hr' | ⟨h', -⟩) | hr'
    · exact Or.inl hr'
    · exact absurd h' h
    · exact Or.inr hr'

theorem SInv.init (v₁ : ℕ) (w : Node C) : SInv f F (St.init : St P C) v₁ w where
  inv2 := by simp [St.init]
  inv1 := by
    rintro ⟨u, x, hu, -, hv⟩
    rcases hv with hv | hv
    · simp [QC.IsGen] at hv; omega
    · have : signers F (St.init : St P C).votes ⟨.prepare, u, x⟩ ⊆ F := by
        intro i hi; rw [mem_signers] at hi; simpa [St.init] using hi
      have := Finset.card_le_card this
      omega

theorem SInv.step {s s' : St P C} (hI : Inv f F s) {v₁ : ℕ} {w : Node C}
    (hS : SInv f F s v₁ w) (hs : Step f F s s') : SInv f F s' v₁ w := by
  have hI' := hI.step hs
  cases hs with
  | mk r l' o hr hl =>
  have hV : s.votes ⊆ s.votes ∪ newVotes r o := Set.subset_union_left
  have hbad : ¬ Bad f F ⟨Function.update s.loc r l', s.votes ∪ newVotes r o⟩ v₁ w →
      ¬ Bad f F s v₁ w := by
    rintro h ⟨u, x, hu, hx, hv⟩; exact h ⟨u, x, hu, hx, hv.mono hV⟩
  refine ⟨?_, ?_⟩
  · intro hnb r' hr' hc u x hu hp
    exact no_commit_and_bad hF h3 hI hS (hbad hnb) hl hr' hc hu hp
  · intro hb
    by_cases hb0 : Bad f F s v₁ w
    · have := Finset.card_le_card (pot_mono (w := w) (v₁ := v₁) hl)
      have := hS.inv1 hb0
      omega
    · obtain ⟨u, x, hu, hx, hv⟩ := hb
      set s' : St P C := ⟨Function.update s.loc r l', s.votes ∪ newVotes r o⟩ with hs'
      let T := Finset.univ.filter fun i => i ∉ F ∧ (i, (⟨.prepare, u, x⟩ : QC C)) ∈ s'.votes
      have hT : Fintype.card P - f ≤ F.card + T.card := by
        rcases hv with hv | hv
        · simp [QC.IsGen] at hv; omega
        · refine hv.trans ((card_signers_le (F := F) (V := s'.votes) _).trans (le_of_eq ?_))
          congr 2; ext i; simp [T]
      have hsub : Pot F s' v₁ w ⊆ (Finset.univ.filter fun i => i ∉ F) \ T := by
        intro i hi
        simp only [Pot, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, T, not_and]
        refine ⟨hi.1, fun _ hp => ?_⟩
        have hvi := ((hI'.loc i hi.1).vote _ hp).2.1
        simp only at hvi
        rcases hi.2 with hc | h' | h'
        · exact hx (no_commit_and_bad hF h3 hI hS hb0 hl hi.1 hc hu hp)
        · omega
        · omega
      have hc1 := Finset.card_le_card hsub
      have hc2 : ((Finset.univ.filter fun i => i ∉ F) \ T).card + T.card ≤
          Fintype.card P - F.card := by
        have hTsub : T ⊆ Finset.univ.filter fun i => i ∉ F := by
          intro i hi; simp only [T, Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩
        rw [Finset.card_sdiff_add_card_eq_card hTsub]
        have : (Finset.univ.filter fun i => i ∉ F) = Finset.univ \ F := by ext; simp
        rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have hFn : F.card ≤ Fintype.card P := Finset.card_le_univ _
      omega

theorem Reach.sinv {s : St P C} (hs : Reach f F s) (v₁ : ℕ) (w : Node C) :
    SInv f F s v₁ w := by
  induction hs with
  | refl => exact SInv.init hF h3 v₁ w
  | tail hr hst ih => exact ih.step hF h3 (Reach.inv hr) hst

/-- Safety at the level of certificates: two valid commit QCs are never on conflicting nodes. -/
theorem commitQC_safety {s : St P C} (hs : Reach f F s) {v₁ v₂ : ℕ} {w b : Node C}
    (h₁ : Valid f F s.votes ⟨.commit, v₁, w⟩) (h₂ : Valid f F s.votes ⟨.commit, v₂, b⟩) :
    ¬ Conflict w b := by
  have h2 : 2 * f < Fintype.card P := by omega
  wlog hle : v₁ ≤ v₂ generalizing v₁ v₂ w b
  · intro hc
    exact this h₂ h₁ (by omega) ⟨hc.2, hc.1⟩
  intro hc
  have hI := hs.inv
  rcases Nat.lt_or_ge v₁ v₂ with hlt | hge
  swap
  · have := hI.node_eq hF h3 h₁ h₂ (by simp; omega)
    simp at this
    exact hc.1 (this ▸ List.suffix_refl _)
  have hbad : Bad f F s v₁ w := ⟨v₂, b, hlt, hc.1, hI.valid_prepare hF h2 h₂⟩
  have hp := (hs.sinv hF h3 v₁ w).inv1 hbad
  rcases h₁ with h₁ | h₁
  · simp only [QC.IsGen] at h₁
    exact hc.1 (h₁.2 ▸ List.nil_suffix)
  have hsub : (Finset.univ.filter fun i => i ∉ F ∧ (i, (⟨.commit, v₁, w⟩ : QC C)) ∈ s.votes) ⊆
      Pot F s v₁ w := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pot] at hi ⊢
    exact ⟨hi.1, Or.inl hi.2⟩
  have := (card_signers_le (F := F) (V := s.votes) ⟨.commit, v₁, w⟩).trans
    (Nat.add_le_add_left (Finset.card_le_card hsub) _)
  omega

/-- **Theorem 2.** If `w` and `b` are conflicting nodes, then they cannot both be committed, each
by a correct replica. (Valid for any `n > 3f` with quorums of size `n − f`; the paper takes
`n = 3f + 1`.) -/
theorem theorem_2 {s : St P C} (hs : Reach f F s) {r₁ r₂ : P} (hr₁ : r₁ ∉ F) (hr₂ : r₂ ∉ F)
    {w b : Node C} (hw : w ∈ (s.loc r₁).committed) (hb : b ∈ (s.loc r₂).committed) :
    ¬ Conflict w b := by
  obtain ⟨v₁, h₁⟩ := (hs.inv.loc r₁ hr₁).committed w hw
  obtain ⟨v₂, h₂⟩ := (hs.inv.loc r₂ hr₂).committed b hb
  exact commitQC_safety hF h3 hs h₁ h₂

end HotStuff.Basic
