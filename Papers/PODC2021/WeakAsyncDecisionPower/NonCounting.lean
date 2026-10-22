import Papers.PODC2021.WeakAsyncDecisionPower.Star
import Papers.PODC2021.WeakAsyncDecisionPower.Dickson

/-!
# Non-counting automata cannot count beyond a cutoff (Lemma 3.5)

Following the paper's proof on stars:

* `accepts_iff_reach_stablyIn`, `not_accepts_iff_reach_stablyIn`: under the consistency condition,
  `A` accepts (rejects) `G` iff a stably accepting (rejecting) configuration is reachable from the
  initial one. This holds for every fairness constraint (`exists_fair_frequently`).
* `reach_lift`: for non-counting machines, runs on a star lift along any surjection of leaves
  (the new leaves copy old ones; claim (1) of the paper).
* `escapes_iff`: whether a star configuration can reach a configuration outside `Z` only depends on
  its abstraction (centre state, leaf state count), and the set of such abstractions is upward
  closed for `StarLE`; by `exists_cutoff_of_upward_closed` it is determined by a cutoff `m`.
* `reach_stable_extend`: adding a leaf in a state already occupied by more than `(m - 1) |Q|`
  leaves preserves the reachability of a stably-`Z` configuration (pigeonhole + copying).
* `lemma_3_5`: every non-counting automaton (`dAF`, and also `dAf`; any selection) that decides a
  labelling property admits a cutoff.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

variable {Λ : Type*} {Q : Type}

section Stable

variable {V : Type*}

/-- All configurations reachable from `C` are in `Z` everywhere. -/
def StablyIn (M : Machine Λ Q) (G : SimpleGraph V) (κ : Selection) (Z : Set Q) (C : V → Q) :
    Prop :=
  ∀ D, Reach M G κ C D → ∀ v, D v ∈ Z

lemma Selection.liftable_of_permitted' {G : SimpleGraph V} {κ : Selection} {S : Set V}
    (h : κ.Permitted S) : κ.Liftable G S := Selection.liftable_of_permitted h

variable {A : Automaton Λ Q}

lemma exists_fair_eventuallyIn_of_reach {G : LGraph Λ} [Nonempty G.V] {Z : Set Q} {D : G.V → Q}
    (hR : Reach A.M G.graph A.sel (A.init G) D) (hD : StablyIn A.M G.graph A.sel Z D) :
    ∃ σ, A.FairSchedule G σ ∧ EventuallyIn Z (A.run G σ) := by
  obtain ⟨σ₀, hσ₀⟩ := exists_fair (V := G.V) A.sel A.fair
  obtain ⟨l, hl, rfl⟩ := hR
  refine ⟨prepend l σ₀, hσ₀.prepend hl, l.length, fun t ht v => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Automaton.run, runFrom_prepend]
  exact hD _ (reach_runFrom_of_liftable (fun t => Selection.liftable_of_permitted (hσ₀.1 t)) _ s) v

lemma exists_fair_not_eventuallyIn {G : LGraph Λ} [Nonempty G.V] {Z : Set Q}
    (h : ¬ ∃ D, Reach A.M G.graph A.sel (A.init G) D ∧ StablyIn A.M G.graph A.sel Z D) :
    ∃ σ, A.FairSchedule G σ ∧ ¬ EventuallyIn Z (A.run G σ) := by
  obtain ⟨σ, hσ, hP⟩ := exists_fair_frequently A.M G.graph A.sel A.fair
    (fun D => ∃ v, D v ∉ Z) (A.init G) (by
      intro C hC
      by_contra hno
      push_neg at hno
      exact h ⟨C, hC, fun D hD v => hno D hD v⟩)
  refine ⟨σ, hσ, fun ⟨t₀, ht₀⟩ => ?_⟩
  obtain ⟨t, ht, v, hv⟩ := hP t₀
  exact hv (ht₀ t ht v)

/-- Under the consistency condition, `A` accepts `G` iff a stably accepting configuration is
reachable. -/
theorem accepts_iff_reach_stablyIn {k : ℕ∞} (hA : A.Consistent k) {G : LGraph Λ}
    (hG : G.Admissible k) :
    A.Accepts G ↔ ∃ D, Reach A.M G.graph A.sel (A.init G) D ∧ StablyIn A.M G.graph A.sel A.M.Y D := by
  have := hG.nonempty
  constructor
  · intro hacc
    by_contra h
    obtain ⟨σ, hσ, hn⟩ := exists_fair_not_eventuallyIn h
    exact hn ((A.accepts_iff hA hG hσ).1 hacc)
  · rintro ⟨D, hR, hD⟩
    obtain ⟨σ, hσ, hev⟩ := exists_fair_eventuallyIn_of_reach hR hD
    exact ⟨σ, hσ, hev⟩

/-- Under the consistency condition, `A` rejects `G` iff a stably rejecting configuration is
reachable. -/
theorem not_accepts_iff_reach_stablyIn {k : ℕ∞} (hA : A.Consistent k) {G : LGraph Λ}
    (hG : G.Admissible k) :
    ¬ A.Accepts G ↔
      ∃ D, Reach A.M G.graph A.sel (A.init G) D ∧ StablyIn A.M G.graph A.sel A.M.N D := by
  have := hG.nonempty
  constructor
  · intro hrej
    by_contra h
    obtain ⟨σ, hσ, hn⟩ := exists_fair_not_eventuallyIn h
    exact hn ((A.not_accepts_iff hA hG hσ).1 hrej)
  · rintro ⟨D, hR, hD⟩
    obtain ⟨σ, hσ, hev⟩ := exists_fair_eventuallyIn_of_reach hR hD
    exact (A.not_accepts_iff hA hG hσ).2 hev

end Stable

section StarLift

variable {M : Machine Λ Q}

lemma option_map_surjective {α β : Type*} {π : α → β} (hπ : Function.Surjective π) :
    Function.Surjective (Option.map π) := by
  intro v
  cases v with
  | none => exact ⟨none, rfl⟩
  | some b =>
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨some a, rfl⟩

lemma step_comp {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (π : W → V)
    (hview : ∀ (C : V → Q) w, view M.β H (C ∘ π) w = view M.β G C (π w)) (C : V → Q) (S : Set V) :
    step M H (C ∘ π) (π ⁻¹' S) = step M G C S ∘ π :=
  sim_global M G H π (fun _ => S) C hview 1

variable {L L' : Type*} [Finite L] [Finite L']

lemma star_view_lift (hβ : M.β = 1) {π : L' → L} (hπ : Function.Surjective π) (C : Option L → Q)
    (w : Option L') :
    view M.β (starG L') (C ∘ Option.map π) w = view M.β (starG L) C (Option.map π w) := by
  rw [hβ]
  apply view_one_comp_of_image_eq
  cases w with
  | none =>
    rw [starG_nbr_none]
    show Option.map π '' range some = {x | (starG L).Adj none x}
    rw [starG_nbr_none]
    ext x
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨_, ⟨l', rfl⟩, rfl⟩; exact ⟨π l', rfl⟩
    · rintro ⟨l, rfl⟩
      obtain ⟨l', rfl⟩ := hπ l
      exact ⟨some l', ⟨l', rfl⟩, rfl⟩
  | some l' =>
    rw [starG_nbr_some]
    show Option.map π '' {none} = {x | (starG L).Adj (some (π l')) x}
    rw [starG_nbr_some]
    simp

lemma liftable_preimage {κ : Selection} {π : L' → L} (hπ : Function.Surjective π) {S : Set (Option L)}
    (hS : κ.Permitted S) : κ.Liftable (starG L') (Option.map π ⁻¹' S) := by
  cases κ with
  | liberal => trivial
  | synchronous =>
    show Option.map π ⁻¹' S = univ
    rw [show S = univ from hS, preimage_univ]
  | exclusive =>
    obtain ⟨v, rfl⟩ := hS
    refine ⟨?_, ?_⟩
    · rintro a ha b hb - hab
      simp only [mem_preimage, mem_singleton_iff] at ha hb
      rw [starG_adj] at hab
      rcases hab with ⟨rfl, hb'⟩ | ⟨rfl, ha'⟩
      · cases b with
        | none => exact hb' rfl
        | some b => rw [← hb] at ha; simp at ha
      · cases a with
        | none => exact ha' rfl
        | some a => rw [← hb] at ha; simp at ha
    · obtain ⟨w, hw⟩ := option_map_surjective hπ v
      exact ⟨w, hw⟩

/-- **Claim (1) in the proof of Lemma 3.5.** For a non-counting machine, every run on a star lifts
to a star with more leaves, each new leaf copying an old one (`π` maps leaves to the leaves they
copy). -/
lemma reach_lift (hβ : M.β = 1) {κ : Selection} {π : L' → L} (hπ : Function.Surjective π)
    {C D : Option L → Q} (h : Reach M (starG L) κ C D) :
    Reach M (starG L') κ (C ∘ Option.map π) (D ∘ Option.map π) := by
  obtain ⟨l, hl, rfl⟩ := h
  induction l generalizing C with
  | nil => exact Reach.refl κ _
  | cons S l ih =>
    rw [runList_cons]
    have h1 : Reach M (starG L') κ (C ∘ Option.map π) (step M (starG L) C S ∘ Option.map π) := by
      rw [← step_comp _ (fun C w => star_view_lift hβ hπ C w)]
      exact reach_step_of_liftable (liftable_preimage hπ (hl S List.mem_cons_self)) _
    exact h1.trans (ih (fun S' hS' => hl S' (List.mem_cons_of_mem _ hS')))

end StarLift

section Abstraction

variable {L L' : Type*}

/-- The abstraction of a star configuration: centre state and number of leaves in each state. -/
noncomputable def absC (C : Option L → Q) : Q × (Q → ℕ) := (C none, fun q => {l | C (some l) = q}.ncard)

/-- If the abstraction of `C` is below that of `C'` (`StarLE`), then `C'` is obtained from `C` by
copying leaves: `C' = C ∘ Option.map π` for a surjection `π`. -/
lemma exists_surj_of_starLE [Finite L] [Finite L'] {C : Option L → Q} {C' : Option L' → Q}
    (h : StarLE (absC C) (absC C')) :
    ∃ π : L' → L, Function.Surjective π ∧ C' = C ∘ Option.map π := by
  classical
  obtain ⟨hctr, hle, hsupp⟩ := h
  let F : Q → Type _ := fun q => {l // C (some l) = q}
  let F' : Q → Type _ := fun q => {l' // C' (some l') = q}
  have hcard : ∀ q, Nat.card (F q) ≤ Nat.card (F' q) := by
    intro q
    simp only [F, F']
    rw [← Set.coe_ofPred, ← Set.coe_ofPred, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact hle q
  have hne : ∀ q, Nonempty (F' q) → Nonempty (F q) := by
    rintro q ⟨⟨l', hl'⟩⟩
    have : ({l | C' (some l) = q}).ncard ≠ 0 :=
      ((ncard_pos (toFinite _)).2 ⟨l', hl'⟩).ne'
    have h' := (hsupp q).not.2 this
    obtain ⟨l, hl⟩ := nonempty_of_ncard_ne_zero h'
    exact ⟨⟨l, hl⟩⟩
  -- a surjection `F' q → F q` for each `q`
  have hs : ∀ q, ∃ s : F' q → F q, Function.Surjective s := by
    intro q
    by_cases hq : Nonempty (F' q)
    · have := hne q hq
      have : Fintype (F q) := Fintype.ofFinite _
      have : Fintype (F' q) := Fintype.ofFinite _
      obtain ⟨i⟩ := Function.Embedding.nonempty_of_card_le (α := F q) (β := F' q)
        (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard q)
      exact ⟨Function.invFun i, Function.invFun_surjective i.injective⟩
    · rw [not_nonempty_iff] at hq
      refine ⟨fun x => (IsEmpty.false x).elim, fun y => ?_⟩
      exfalso
      obtain ⟨y, hy⟩ := y
      have : ({l | C (some l) = q}).ncard ≠ 0 := ((ncard_pos (toFinite _)).2 ⟨y, hy⟩).ne'
      have h' := (hsupp q).not.1 this
      obtain ⟨l', hl'⟩ := nonempty_of_ncard_ne_zero h'
      exact IsEmpty.false (⟨l', hl'⟩ : F' q)
  choose s hsurj using hs
  let π : L' → L := fun l' => (s (C' (some l')) ⟨l', rfl⟩).val
  have hπC : ∀ l', C (some (π l')) = C' (some l') := fun l' => (s _ _).prop
  refine ⟨π, fun l => ?_, ?_⟩
  · obtain ⟨⟨l', hl'⟩, hy⟩ := hsurj (C (some l)) ⟨l, rfl⟩
    refine ⟨l', ?_⟩
    simp only [π]
    have key : ∀ q (e : C' (some l') = q) (x : F' q), x = ⟨l', e⟩ →
        (s (C' (some l')) ⟨l', rfl⟩).val = (s q x).val := by
      rintro q rfl x rfl; rfl
    rw [key _ hl' _ rfl, hy]
  · funext o
    cases o with
    | none => exact hctr.symm
    | some l' => exact (hπC l').symm

variable (M : Machine Λ Q) (κ : Selection) (Z : Set Q)

/-- `C` can reach a configuration with some node outside `Z`. -/
def Escapes {L : Type*} (C : Option L → Q) : Prop :=
  ∃ D, Reach M (starG L) κ C D ∧ ∃ v, D v ∉ Z

/-- The abstractions of star configurations that can escape `Z`. -/
def EscSet : Set (Q × (Q → ℕ)) :=
  {X | ∃ (L : Type) (_ : Finite L) (C : Option L → Q), absC C = X ∧ Escapes M κ Z C}

variable {M}

lemma escapes_of_starLE (hβ : M.β = 1) {X : Q × (Q → ℕ)} (hX : X ∈ EscSet M κ Z) {L' : Type}
    [Finite L'] (C' : Option L' → Q) (h : StarLE X (absC C')) : Escapes M κ Z C' := by
  obtain ⟨L, _, C, rfl, D, hR, v, hv⟩ := hX
  obtain ⟨π, hπ, rfl⟩ := exists_surj_of_starLE h
  obtain ⟨w, rfl⟩ := option_map_surjective hπ v
  exact ⟨D ∘ Option.map π, reach_lift hβ hπ hR, w, hv⟩

lemma escapes_iff (hβ : M.β = 1) {L : Type} [Finite L] (C : Option L → Q) :
    Escapes M κ Z C ↔ absC C ∈ EscSet M κ Z :=
  ⟨fun h => ⟨L, inferInstance, C, rfl, h⟩, fun h => escapes_of_starLE κ Z hβ h C (StarLE.refl _)⟩

lemma escSet_upward [Finite Q] (hβ : M.β = 1) (X Y : Q × (Q → ℕ)) (hX : X ∈ EscSet M κ Z)
    (h : StarLE X Y) : Y ∈ EscSet M κ Z := by
  -- the canonical star configuration with abstraction `Y`
  let L := Σ q : Q, Fin (Y.2 q)
  let C : Option L → Q := fun o => o.elim Y.1 Sigma.fst
  have hC : absC C = Y := by
    refine Prod.ext rfl (funext fun q => ?_)
    show {p : L | p.1 = q}.ncard = Y.2 q
    rw [← Nat.card_coe_set_eq, Set.coe_ofPred, Nat.card_congr (Equiv.sigmaSubtype q),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨L, inferInstance, C, hC, escapes_of_starLE κ Z hβ hX C (hC ▸ h)⟩

end Abstraction

section Extend

variable {M : Machine Λ Q} {κ : Selection} {Z : Set Q} {L : Type}

/-- Adding a new leaf (`some none`) in state `q`. -/
def extendC (C : Option L → Q) (q : Q) : Option (Option L) → Q
  | none => C none
  | some none => q
  | some (some l) => C (some l)

/-- **Main step of the proof of Lemma 3.5.** If `{X | X ∈ EscSet}` is determined by the cutoff
`m`, adding a leaf in a state occupied by more than `(m - 1) |Q|` leaves preserves the
reachability of a configuration that cannot escape `Z`. -/
lemma reach_stable_extend [Finite Q] [Finite L] (hβ : M.β = 1) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : ∀ X, X ∈ EscSet M κ Z ↔ cutStar m X ∈ EscSet M κ Z) (C : Option L → Q) (q : Q)
    (hq : (m - 1) * Nat.card Q < {l | C (some l) = q}.ncard)
    (h : ∃ D, Reach M (starG L) κ C D ∧ ¬ Escapes M κ Z D) :
    ∃ D', Reach M (starG (Option L)) κ (extendC C q) D' ∧ ¬ Escapes M κ Z D' := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  obtain ⟨D, hR, hD⟩ := h
  -- pigeonhole: many leaves that start in `q` end in the same state `r`
  obtain ⟨r, -, hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (toFinite {l | C (some l) = q}).toFinset) (t := Finset.univ)
    (f := fun l => D (some l)) (n := m - 1) (fun _ _ => Finset.mem_univ _)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_eq_toFinset_card _ (toFinite _), mul_comm]; exact hq)
  obtain ⟨lold, hlold⟩ : (Finset.filter (fun l => D (some l) = r)
      (toFinite {l | C (some l) = q}).toFinset).Nonempty := Finset.card_pos.1 (by omega)
  simp only [Finset.mem_filter, Finite.mem_toFinset, mem_ofPred_eq] at hlold
  have hDr : m ≤ {l | D (some l) = r}.ncard := by
    refine (show m ≤ _ by omega : m ≤ (Finset.filter (fun l => D (some l) = r)
      (toFinite {l | C (some l) = q}).toFinset).card).trans ?_
    · rw [ncard_eq_toFinset_card _ (toFinite {l | D (some l) = r})]
      apply Finset.card_le_card
      intro l hl
      simp only [Finset.mem_filter, Finite.mem_toFinset, mem_ofPred_eq] at hl
      simpa using hl.2
  let π : Option L → L := fun o => o.elim lold id
  have hπ : Function.Surjective π := fun l => ⟨some l, rfl⟩
  have hext : extendC C q = C ∘ Option.map π := by
    funext o
    rcases o with _ | _ | l
    · rfl
    · exact hlold.1.symm
    · rfl
  refine ⟨D ∘ Option.map π, hext ▸ reach_lift hβ hπ hR, ?_⟩
  rw [escapes_iff κ Z hβ, hm]
  rw [escapes_iff κ Z hβ, hm] at hD
  convert hD using 2
  refine Prod.ext rfl (funext fun q' => ?_)
  simp only [cutStar, absC, Function.comp, Option.map_some]
  have h1 := ncard_option (fun o : Option L => D (some (π o)) = q')
  rw [h1]
  have h2 : π none = lold := rfl
  have h3 : ∀ l, π (some l) = l := fun _ => rfl
  simp only [h2, h3]
  split_ifs with h
  · rw [← h, hlold.2]
    omega
  · simp

end Extend

section Graph

variable (A : Automaton Λ Q)

lemma stablyIn_iff_not_escapes {M : Machine Λ Q} {κ : Selection} {Z : Set Q} {L : Type*}
    (C : Option L → Q) : StablyIn M (starG L) κ Z C ↔ ¬ Escapes M κ Z C := by
  simp only [StablyIn, Escapes, not_exists, not_and, not_not]

lemma init_extend {L : Type} [Finite L] (c ℓ : Λ) (lab : L → Λ) :
    A.init (starL (Option L) c fun o => o.elim ℓ lab) =
      extendC (A.init (starL L c lab)) (A.M.init ℓ) := by
  funext o; rcases o with _ | _ | l <;> rfl

/-- Adding a leaf with a label carried by many leaves does not change acceptance (stars). -/
theorem star_add_leaf [Finite Q] (hβ : A.M.β = 1) (hA : A.Consistent ⊤) :
    ∃ B, ∀ (L : Type) [Finite L] (c ℓ : Λ) (lab : L → Λ), 2 ≤ Nat.card L →
      B ≤ {l | lab l = ℓ}.ncard →
      (A.Accepts (starL L c lab) ↔ A.Accepts (starL (Option L) c fun o => o.elim ℓ lab)) := by
  obtain ⟨mY, hmY1, hmY⟩ := exists_cutoff_of_upward_closed (EscSet A.M A.sel A.M.Y)
    (escSet_upward A.sel A.M.Y hβ)
  obtain ⟨mN, hmN1, hmN⟩ := exists_cutoff_of_upward_closed (EscSet A.M A.sel A.M.N)
    (escSet_upward A.sel A.M.N hβ)
  refine ⟨max mY mN * Nat.card Q + 1, fun L _ c ℓ lab hL hB => ?_⟩
  set S := starL L c lab
  set S' := starL (Option L) c fun o => o.elim ℓ lab
  have hS := starL_admissible c lab hL
  have hS' := starL_admissible c (fun o : Option L => o.elim ℓ lab)
    (by rw [Finite.card_option]; omega)
  have hmany : ∀ m, m ≤ max mY mN →
      (m - 1) * Nat.card Q < {l | A.init S (some l) = A.M.init ℓ}.ncard := by
    intro m hm
    have h1 : {l | lab l = ℓ}.ncard ≤ {l | A.init S (some l) = A.M.init ℓ}.ncard := by
      apply ncard_le_ncard _ (toFinite _)
      intro l hl
      simp only [mem_ofPred_eq] at hl ⊢
      simp [Automaton.init, S, starL, hl]
    have h2 : (m - 1) * Nat.card Q ≤ max mY mN * Nat.card Q :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hext : ∀ Z : Set Q, ∀ m, 1 ≤ m → m ≤ max mY mN →
      (∀ X, X ∈ EscSet A.M A.sel Z ↔ cutStar m X ∈ EscSet A.M A.sel Z) →
      (∃ D, Reach A.M S.graph A.sel (A.init S) D ∧ StablyIn A.M S.graph A.sel Z D) →
      (∃ D, Reach A.M S'.graph A.sel (A.init S') D ∧ StablyIn A.M S'.graph A.sel Z D) := by
    intro Z m hm1 hm hcut ⟨D, hR, hD⟩
    rw [stablyIn_iff_not_escapes] at hD
    obtain ⟨D', hR', hD'⟩ := reach_stable_extend hβ hm1 hcut (A.init S) (A.M.init ℓ)
      (hmany m hm) ⟨D, hR, hD⟩
    refine ⟨D', ?_, (stablyIn_iff_not_escapes D').2 hD'⟩
    show Reach A.M (starG (Option L)) A.sel (A.init S') D'
    rw [show A.init S' = extendC (A.init S) (A.M.init ℓ) from init_extend A c ℓ lab]
    exact hR'
  constructor
  · intro hacc
    rw [accepts_iff_reach_stablyIn hA hS] at hacc
    exact (accepts_iff_reach_stablyIn hA hS').2
      (hext A.M.Y mY hmY1 (le_max_left _ _) hmY hacc)
  · intro hacc
    by_contra hrej
    rw [not_accepts_iff_reach_stablyIn hA hS] at hrej
    exact (not_accepts_iff_reach_stablyIn hA hS').2
      (hext A.M.N mN hmN1 (le_max_right _ _) hmN hrej) hacc

/-- **Lemma 3.5.** A non-counting automaton (`β = 1`; the paper states it for `dAF`, i.e.
pseudo-stochastic scheduling, and the proof works for any fairness and selection constraint)
that decides a labelling property admits a cutoff `K`: whether it accepts `G` only depends on
`⌈L_G⌉_K`. -/
theorem lemma_3_5 [Finite Q] (hβ : A.M.β = 1) (hA : A.Consistent ⊤) (hL : A.IsLabelling ⊤) :
    ∃ K, ∀ G H : LGraph Λ, G.Admissible ⊤ → H.Admissible ⊤ →
      cutoff K G.count = cutoff K H.count → (A.Accepts G ↔ A.Accepts H) := by
  classical
  obtain ⟨B, hB⟩ := star_add_leaf A hβ hA
  set K := B + 3
  -- removing a node whose label occurs more than `K` times
  have hremove : ∀ G : LGraph Λ, G.Admissible ⊤ → ∀ ℓ, K < G.count ℓ →
      ∃ G' : LGraph Λ, G'.Admissible ⊤ ∧ Nat.card G'.V < Nat.card G.V ∧
        cutoff K G'.count = cutoff K G.count ∧ (A.Accepts G ↔ A.Accepts G') := by
    intro G hG ℓ hℓ
    obtain ⟨v₀⟩ := hG.nonempty
    obtain ⟨L, _, lab, hL2, hcardL, hcnt⟩ := exists_star hG v₀
    set c := G.label v₀
    have hleaves : K ≤ {l | lab l = ℓ}.ncard := by
      have := congrFun hcnt ℓ
      rw [starL_count] at this
      split_ifs at this <;> omega
    obtain ⟨l₁, hl₁⟩ := nonempty_of_ncard_ne_zero (s := {l | lab l = ℓ}) (by omega)
    simp only [mem_ofPred_eq] at hl₁
    let L₁ := {l // l ≠ l₁}
    let lab₁ : L₁ → Λ := fun x => lab x.1
    have hn₁ : ∀ ℓ', {x : L₁ | lab₁ x = ℓ'}.ncard + (if ℓ = ℓ' then 1 else 0) =
        {l | lab l = ℓ'}.ncard := by
      intro ℓ'
      have himg : Subtype.val '' {x : L₁ | lab₁ x = ℓ'} = {l | lab l = ℓ'} \ {l₁} := by
        ext l; simp [lab₁, L₁, and_comm]
      rw [← ncard_image_of_injective _ Subtype.val_injective, himg]
      split_ifs with h
      · exact ncard_sdiff_singleton_add_one (by simp [h ▸ hl₁]) (toFinite _)
      · rw [Set.sdiff_singleton_eq_self (by simpa [hl₁] using h)]; simp
    have hcard₁ : Nat.card L₁ + 1 = Nat.card L := by
      rw [← Finite.card_option]; exact Nat.card_congr (Equiv.optionSubtypeNe l₁)
    have hL₁ : 2 ≤ Nat.card L₁ := by
      have : {l | lab l = ℓ}.ncard ≤ Nat.card L := by
        rw [← Nat.card_coe_set_eq]; exact Finite.card_subtype_le _
      omega
    set G₁ := starL L₁ c lab₁
    set G₂ := starL (Option L₁) c fun o => o.elim ℓ lab₁
    have hG₁ := starL_admissible c lab₁ hL₁
    have hG₂ := starL_admissible c (fun o : Option L₁ => o.elim ℓ lab₁)
      (by rw [Finite.card_option]; omega)
    have hS := starL_admissible c lab hL2
    have hc₂ : (starL L c lab).count = G₂.count := by
      refine count_eq_of_equiv (Equiv.optionCongr (Equiv.optionSubtypeNe l₁).symm) fun o => ?_
      cases o with
      | none => rfl
      | some l =>
        show (Option.some ((Equiv.optionSubtypeNe l₁).symm l)).elim c
          (fun o => o.elim ℓ lab₁) = lab l
        rw [Equiv.optionSubtypeNe_symm_apply]
        by_cases h : l = l₁
        · rw [dif_pos h, h, hl₁]; rfl
        · rw [dif_neg h]; rfl
    have hc₁ : ∀ ℓ', G₁.count ℓ' + (if ℓ = ℓ' then 1 else 0) = G.count ℓ' := by
      intro ℓ'
      rw [← hcnt, hc₂, starL_count, starL_count]
      have := ncard_option (fun o : Option L₁ => o.elim ℓ lab₁ = ℓ')
      rw [show {o : Option L₁ | o.elim ℓ lab₁ = ℓ'}.ncard = _ from this]
      have e1 : {l : L₁ | (some l).elim ℓ lab₁ = ℓ'} = {l | lab₁ l = ℓ'} := rfl
      have e2 : (none : Option L₁).elim ℓ lab₁ = ℓ := rfl
      rw [e1, e2]
      omega
    refine ⟨G₁, hG₁, ?_, ?_, ?_⟩
    · show Nat.card (Option L₁) < Nat.card G.V
      rw [Finite.card_option]; omega
    · funext ℓ'
      have := hc₁ ℓ'
      simp only [cutoff]
      split_ifs at this with h
      · subst h; omega
      · omega
    · rw [hL G _ hG hS hcnt.symm, hL _ G₂ hS hG₂ hc₂]
      exact (hB L₁ c ℓ lab₁ hL₁ (by have := hn₁ ℓ; simp at this; omega)).symm
  -- reduce every graph to one with all label counts at most `K`
  have hred : ∀ n, ∀ G : LGraph Λ, Nat.card G.V = n → G.Admissible ⊤ →
      ∃ G' : LGraph Λ, G'.Admissible ⊤ ∧ (∀ ℓ, G'.count ℓ ≤ K) ∧
        cutoff K G'.count = cutoff K G.count ∧ (A.Accepts G ↔ A.Accepts G') := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G hn hG
      by_cases hall : ∀ ℓ, G.count ℓ ≤ K
      · exact ⟨G, hG, hall, rfl, Iff.rfl⟩
      · push_neg at hall
        obtain ⟨ℓ, hℓ⟩ := hall
        obtain ⟨G₁, hG₁, hlt, hcut, hacc⟩ := hremove G hG ℓ hℓ
        obtain ⟨G', hG', hle, hcut', hacc'⟩ := ih _ (hn ▸ hlt) G₁ rfl hG₁
        exact ⟨G', hG', hle, hcut'.trans hcut, hacc.trans hacc'⟩
  refine ⟨K, fun G H hG hH hGH => ?_⟩
  obtain ⟨G', hG', hleG, hcutG, haccG⟩ := hred _ G rfl hG
  obtain ⟨H', hH', hleH, hcutH, haccH⟩ := hred _ H rfl hH
  have hcnt : G'.count = H'.count := by
    funext ℓ
    have h1 := congrFun (hcutG.trans (hGH.trans hcutH.symm)) ℓ
    simp only [cutoff] at h1
    have := hleG ℓ; have := hleH ℓ
    omega
  rw [haccG, haccH]
  exact hL G' H' hG' hH' hcnt

end Graph

end Podc.WeakAsyncDecisionPower
