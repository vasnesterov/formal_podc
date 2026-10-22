import Papers.PODC2021.WeakAsyncDecisionPower.Star

/-!
# Adversarial selection cannot count beyond `β + 1` (Lemma 3.4)

The paper proves Lemma 3.4 on cliques with the synchronous schedule, which is only available for
liberal or synchronous selection (for exclusive selection the paper relies on the
selection-independence result of Esparza–Reiter). We prove it directly for all three selection
constraints, on stars: under the schedule "all leaves, then the centre" (or the synchronous
schedule), leaves with equal labels always have equal states, and the centre only sees the leaf
counts per label cut off at `β`.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

variable {Λ Q : Type*}

/-- Cut-off counts of preimages are determined by the cut-off counts of fibres. -/
lemma min_ncard_preimage_eq {X A B : Type*} [Finite A] [Finite B] (β : ℕ) (g : A → X)
    (h : B → X) (hgh : ∀ x, min β (g ⁻¹' {x}).ncard = min β (h ⁻¹' {x}).ncard) (U : Set X) :
    min β (g ⁻¹' U).ncard = min β (h ⁻¹' U).ncard := by
  classical
  have key : ∀ T : Finset X, min β (g ⁻¹' ↑T).ncard = min β (h ⁻¹' ↑T).ncard := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert x T hx ih =>
      rw [Finset.coe_insert, insert_eq, preimage_union, preimage_union,
        ncard_union_eq _ (toFinite _) (toFinite _), ncard_union_eq _ (toFinite _) (toFinite _)]
      · have := hgh x; omega
      · exact Disjoint.preimage _ (by simpa using hx)
      · exact Disjoint.preimage _ (by simpa using hx)
  set S := (toFinite (U ∩ (range g ∪ range h))).toFinset
  have hg : g ⁻¹' U = g ⁻¹' ↑S := by ext a; simp [S]
  have hh : h ⁻¹' U = h ⁻¹' ↑S := by ext a; simp [S]
  rw [hg, hh]
  exact key S

lemma ncard_nbr_none {L : Type*} [Finite L] (D : Option L → Q) (q : Q) :
    {u | (starG L).Adj none u ∧ D u = q}.ncard = {l | D (some l) = q}.ncard := by
  rw [← ncard_image_of_injective _ (Option.some_injective L)]
  congr 1
  ext u; cases u <;> simp

/-- **Lemma 3.4 on stars.** Two labelled stars with the same centre label whose leaf-label counts
agree up to the cutoff `β` are accepted or rejected together by an automaton with adversarial
scheduling. -/
theorem star_cutoff (A : Automaton Λ Q) (hfair : A.fair = .adversarial) (hA : A.Consistent ⊤)
    {LG LH : Type} [Finite LG] [Finite LH] (c : Λ) (lg : LG → Λ) (lh : LH → Λ)
    (hLG : 2 ≤ Nat.card LG) (hLH : 2 ≤ Nat.card LH)
    (hcnt : ∀ ℓ, min A.M.β (lg ⁻¹' {ℓ}).ncard = min A.M.β (lh ⁻¹' {ℓ}).ncard) :
    A.Accepts (starL LG c lg) ↔ A.Accepts (starL LH c lh) := by
  classical
  have hβ := A.M.one_le_β
  have hneG : Nonempty LG := by
    by_contra h; rw [not_nonempty_iff] at h; rw [Nat.card_of_isEmpty] at hLG; omega
  have hneH : Nonempty LH := by
    by_contra h; rw [not_nonempty_iff] at h; rw [Nat.card_of_isEmpty] at hLH; omega
  have hex : ∀ u : LH, ∃ x : LG, lg x = lh u := by
    intro u
    have h1 : 1 ≤ min A.M.β (lh ⁻¹' {lh u}).ncard :=
      le_min hβ ((ncard_pos (toFinite _)).2 ⟨u, rfl⟩)
    rw [← hcnt] at h1
    obtain ⟨x, hx⟩ := (ncard_pos (toFinite _)).1 (by omega : 0 < (lg ⁻¹' {lh u}).ncard)
    exact ⟨x, hx⟩
  have hex' : ∀ x : LG, ∃ u : LH, lh u = lg x := by
    intro x
    have h1 : 1 ≤ min A.M.β (lg ⁻¹' {lg x}).ncard :=
      le_min hβ ((ncard_pos (toFinite _)).2 ⟨x, rfl⟩)
    rw [hcnt] at h1
    obtain ⟨u, hu⟩ := (ncard_pos (toFinite _)).1 (by omega : 0 < (lh ⁻¹' {lg x}).ncard)
    exact ⟨u, hu⟩
  let πL : LH → LG := fun u => (hex u).choose
  have hπL : ∀ u, lg (πL u) = lh u := fun u => (hex u).choose_spec
  let π : Option LH → Option LG := Option.map πL
  -- the reference schedule on the star `G`
  let R : ℕ → Set (Option LG) := fun t =>
    if A.sel = .exclusive then (if t % 2 = 0 then range some else {none}) else univ
  have hRleaf : ∀ t, (∀ l, some l ∈ R t) ∨ (∀ l, some l ∉ R t) := by
    intro t
    simp only [R]
    split_ifs <;> simp
  set G := starL LG c lg
  set H := starL LH c lh
  let runG : ℕ → Option LG → Q := runFrom A.M (starG LG) (A.init G) R
  -- invariant: leaves with equal labels have equal states
  have hinv : ∀ t, ∀ x x', lg x = lg x' → runG t (some x) = runG t (some x') := by
    intro t
    induction t with
    | zero => intro x x' h; simp [runG, Automaton.init, G, starL, h]
    | succ t ih =>
      intro x x' h
      simp only [runG, runFrom_succ]
      have hv : view A.M.β (starG LG) (runG t) (some x) =
          view A.M.β (starG LG) (runG t) (some x') := by
        funext q; simp only [view]
        congr 2; ext u; cases u <;> simp
      rcases hRleaf t with hR | hR
      · rw [step_of_mem _ _ (hR x), step_of_mem _ _ (hR x')]
        simp only [runG] at hv ih
        rw [ih x x' h, hv]
      · rw [step_of_notMem _ _ (hR x), step_of_notMem _ _ (hR x')]
        exact ih x x' h
  -- views are preserved along `π`
  have hview : ∀ t w, view A.M.β (starG LH) (runG t ∘ π) w =
      view A.M.β (starG LG) (runG t) (π w) := by
    intro t w
    cases w with
    | some u =>
      apply view_comp_of_bijOn
      show BijOn π {u' | (starG LH).Adj (some u) u'} {x | (starG LG).Adj (some (πL u)) x}
      rw [starG_nbr_some, starG_nbr_some]
      exact ⟨by simp [MapsTo, π], by simp [InjOn], by simp [SurjOn, π]⟩
    | none =>
      funext q
      simp only [view]
      rw [ncard_nbr_none, show π none = none from rfl, ncard_nbr_none]
      set U : Set Λ := {ℓ | ∃ x, lg x = ℓ ∧ runG t (some x) = q}
      have h1 : {u : LH | (runG t ∘ π) (some u) = q} = lh ⁻¹' U := by
        ext u
        simp only [Function.comp, π, Option.map_some, mem_ofPred_eq, mem_preimage, U]
        constructor
        · intro h; exact ⟨πL u, hπL u, h⟩
        · rintro ⟨x, hx, hq⟩; rw [hinv t _ x (by rw [hπL, hx])]; exact hq
      have h2 : {x : LG | runG t (some x) = q} = lg ⁻¹' U := by
        ext x
        simp only [mem_ofPred_eq, mem_preimage, U]
        constructor
        · intro h; exact ⟨x, rfl, h⟩
        · rintro ⟨x', hx, hq⟩; rw [hinv t _ x' hx.symm]; exact hq
      rw [h1, h2]
      exact (min_ncard_preimage_eq _ lg lh hcnt U).symm
  have hlift : ∀ t, runFrom A.M (starG LH) (A.init H) (fun t => π ⁻¹' R t) t = runG t ∘ π := by
    intro t
    funext w
    refine sim A.M (starG LG) (starG LH) π R (A.init G) (A.init H) (fun _ => univ) ?_
      (fun _ => subset_rfl) (fun _ _ _ _ _ => trivial) (fun t w _ => hview t w) t w trivial
    intro w _
    cases w with
    | none => rfl
    | some u => simp [Automaton.init, H, G, starL, π, hπL]
  -- liftability and fairness of the reference schedules
  have hliftG : ∀ t, A.sel.Liftable (starG LG) (R t) := by
    intro t
    cases hsel : A.sel with
    | liberal => trivial
    | synchronous => simp [R, hsel]; rfl
    | exclusive =>
      simp only [R, hsel, ite_true]
      split_ifs
      · refine ⟨?_, range_nonempty _⟩
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _; simp
      · exact ⟨by simp, singleton_nonempty _⟩
  have hliftH : ∀ t, A.sel.Liftable (starG LH) (π ⁻¹' R t) := by
    intro t
    cases hsel : A.sel with
    | liberal => trivial
    | synchronous => simp [R, hsel]; rfl
    | exclusive =>
      simp only [R, hsel, ite_true]
      split_ifs
      · refine ⟨?_, ⟨some (Classical.arbitrary LH), by simp [π]⟩⟩
        rintro a ha b hb _
        cases a <;> cases b <;> simp_all [π]
      · refine ⟨?_, ⟨none, by simp [π]⟩⟩
        rintro a ha b hb _
        cases a <;> cases b <;> simp_all [π]
  have hfairR : ∀ w N, ∃ t ≥ N, w ∈ R t := by
    intro w N
    by_cases hsel : A.sel = .exclusive
    · cases w with
      | none => exact ⟨2 * N + 1, by omega, by simp [R, hsel, Nat.add_mod]⟩
      | some l => exact ⟨2 * N, by omega, by simp [R, hsel]⟩
    · exact ⟨N, le_rfl, by simp [R, hsel]⟩
  have hfairH : ∀ w N, ∃ t ≥ N, w ∈ π ⁻¹' R t := fun w N => hfairR (π w) N
  obtain ⟨σG, hσG, hevG⟩ := exists_fair_of_liftable A.M (starG LG) A.sel R hliftG hfairR
    (A.init G)
  obtain ⟨σH, hσH, hevH⟩ := exists_fair_of_liftable A.M (starG LH) A.sel _ hliftH hfairH
    (A.init H)
  rw [← hfair] at hσG hσH
  have hG := starL_admissible c lg hLG
  have hH := starL_admissible c lh hLH
  rw [A.accepts_iff hA hG hσG, A.accepts_iff hA hH hσH]
  simp only [Automaton.run]
  rw [hevG, hevH]
  constructor
  · rintro ⟨t₀, ht₀⟩
    refine ⟨t₀, fun t ht w => ?_⟩
    rw [hlift]
    exact ht₀ t ht (π w)
  · rintro ⟨t₀, ht₀⟩
    refine ⟨t₀, fun t ht x => ?_⟩
    have key : ∀ w, runG t (π w) ∈ A.M.Y := fun w => by
      have := ht₀ t ht w; rw [hlift] at this; exact this
    cases x with
    | none => exact key none
    | some x =>
      obtain ⟨u, hu⟩ := hex' x
      have := key (some u)
      simp only [π, Option.map_some] at this
      have e := hinv t (πL u) x (by rw [hπL, hu])
      rw [e] at this
      exact this

/-- **Lemma 3.4.** Let `A` be an automaton with adversarial scheduling (a `DAf`-automaton, any
selection constraint) with counting bound `β` that decides a labelling property. If
`⌈L_G⌉_{β+1} = ⌈L_H⌉_{β+1}`, then `A` accepts `G` iff it accepts `H`. -/
theorem lemma_3_4 (A : Automaton Λ Q) (hfair : A.fair = .adversarial) (hA : A.Consistent ⊤)
    (hL : A.IsLabelling ⊤) {G H : LGraph Λ} (hG : G.Admissible ⊤) (hH : H.Admissible ⊤)
    (hcut : cutoff (A.M.β + 1) G.count = cutoff (A.M.β + 1) H.count) :
    A.Accepts G ↔ A.Accepts H := by
  classical
  obtain ⟨v₀⟩ := hG.nonempty
  set c := G.label v₀
  have hcG : 1 ≤ G.count c := (ncard_pos (toFinite _)).2 ⟨v₀, rfl⟩
  have hcH : 0 < H.count c := by
    have := congrFun hcut c
    simp only [cutoff] at this
    omega
  obtain ⟨w₀, hw₀⟩ := (ncard_pos (toFinite _)).1 hcH
  obtain ⟨LG, _, lg, hLG, -, hsG⟩ := exists_star hG v₀
  obtain ⟨LH, _, lh, hLH, -, hsH⟩ := exists_star hH w₀
  simp only [mem_ofPred_eq] at hw₀
  rw [hw₀] at hsH
  rw [hL G _ hG (starL_admissible _ _ hLG) hsG.symm, hL H _ hH (starL_admissible _ _ hLH) hsH.symm]
  refine star_cutoff A hfair hA c lg lh hLG hLH fun ℓ => ?_
  have h1 := congrFun hsG ℓ
  have h2 := congrFun hsH ℓ
  have h3 := congrFun hcut ℓ
  rw [starL_count] at h1 h2
  simp only [cutoff] at h3
  change min A.M.β {l | lg l = ℓ}.ncard = min A.M.β {l | lh l = ℓ}.ncard
  split_ifs at h1 h2 <;> omega

end Podc.WeakAsyncDecisionPower
