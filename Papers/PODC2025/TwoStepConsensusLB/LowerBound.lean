import Papers.PODC2025.TwoStepConsensusLB.Basic

/-!
# Lower bounds: Theorem 1 and Theorem 2 ("only if"), §B

* `lemma_3`: Lemma 3 (generalized to every `n` with `2e + 1 ≤ n ≤ 2e + f − 1` instead of
  `n = 2e + f − 1`).
* `theorem_1_lower`: an `f`-resilient `e`-two-step consensus **task** needs
  `n ≥ max {2e + f, 2f + 1}`.
* `theorem_2_lower`: an `f`-resilient `e`-two-step consensus **object** needs
  `n ≥ max {2e + f − 1, 2f + 1}`. Only item (1) of Definition 5 is used.

All statements assume `n ≥ 2` and two distinct values (the paper assumes `n ≥ 3`).
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

open Finset

variable {P V M S : Type*} [Fintype P] [DecidableEq P]

theorem card_compl_union {X Y : Finset P} (hXY : Disjoint X Y) :
    (X ∪ Y)ᶜ.card = Fintype.card P - X.card - Y.card := by
  rw [card_compl, card_union_of_disjoint hXY]; omega

theorem card_mergeFaulty_le (X Y : Finset P) (d d' : P) :
    (mergeFaulty X Y d d').card ≤ (X ∪ Y)ᶜ.card + 2 := by
  unfold mergeFaulty
  calc ((X ∪ Y)ᶜ ∪ {d, d'}).card ≤ (X ∪ Y)ᶜ.card + ({d, d'} : Finset P).card := card_union_le _ _
    _ ≤ (X ∪ Y)ᶜ.card + 2 := by gcongr; exact card_le_two

theorem card_mergeFaulty_le_of_mem {X Y : Finset P} {d d' : P} (h : d' ∈ (X ∪ Y)ᶜ) :
    (mergeFaulty X Y d d').card ≤ (X ∪ Y)ᶜ.card + 1 := by
  have : mergeFaulty X Y d d' ⊆ insert d (X ∪ Y)ᶜ := by
    intro x hx
    simp only [mergeFaulty, mem_union, mem_insert, mem_singleton] at hx
    rcases hx with hx | rfl | rfl
    · exact mem_insert_of_mem hx
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem h
  exact (card_le_card this).trans (card_insert_le _ _)

theorem not_mem_mergeFaulty_of {X Y : Finset P} {d d' x : P} (hx : x ∈ X ∨ x ∈ Y) (hd : x ≠ d)
    (hd' : x ≠ d') : x ∉ mergeFaulty X Y d d' := by
  rw [mem_mergeFaulty]; tauto

/-- Swapping a decided process `d ∈ E₁` with some `q ∈ F₁` (proof of Lemma 3, induction step). -/
theorem exists_swap {E₀ E₁ F₁ : Finset P} (h01 : Disjoint E₀ E₁) (h0F : Disjoint E₀ F₁)
    (h1F : Disjoint E₁ F₁) {q d : P} (hq : q ∈ F₁) (hd : d ∉ E₀) :
    ∃ Eh Fh : Finset P, Disjoint E₀ Eh ∧ Disjoint E₀ Fh ∧ Disjoint Eh Fh ∧
      Eh.card = E₁.card ∧ Fh.card = F₁.card ∧ Eh ∪ Fh = E₁ ∪ F₁ ∧ d ∉ Eh := by
  have hq1 : q ∉ E₁ := fun h => disjoint_left.mp h1F h hq
  have hq0 : q ∉ E₀ := fun h => disjoint_left.mp h0F h hq
  by_cases hdE : d ∈ E₁
  · have hdF : d ∉ F₁ := fun h => disjoint_left.mp h1F hdE h
    have hqd : q ≠ d := by rintro rfl; exact hq1 hdE
    refine ⟨insert q (E₁.erase d), insert d (F₁.erase q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [disjoint_insert_right]
      exact ⟨hq0, disjoint_of_subset_right (erase_subset _ _) h01⟩
    · rw [disjoint_insert_right]
      exact ⟨hd, disjoint_of_subset_right (erase_subset _ _) h0F⟩
    · rw [disjoint_insert_left, disjoint_insert_right]
      refine ⟨by simp [hqd], by simp, ?_⟩
      exact disjoint_of_subset_left (erase_subset _ _) (disjoint_of_subset_right (erase_subset _ _) h1F)
    · rw [card_insert_of_notMem (by simp [hq1]), card_erase_of_mem hdE]
      have := card_pos.mpr ⟨d, hdE⟩; omega
    · rw [card_insert_of_notMem (by simp [hdF]), card_erase_of_mem hq]
      have := card_pos.mpr ⟨q, hq⟩; omega
    · ext x
      simp only [mem_union, mem_insert, mem_erase]
      constructor
      · rintro ((rfl | ⟨-, h⟩) | (rfl | ⟨-, h⟩)) <;> tauto
      · rintro (h | h)
        · by_cases hx : x = d
          · exact Or.inr (Or.inl hx)
          · exact Or.inl (Or.inr ⟨hx, h⟩)
        · by_cases hx : x = q
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inr ⟨hx, h⟩)
    · simp [hqd.symm]
  · exact ⟨E₁, F₁, h01, h0F, h1F, rfl, rfl, rfl, hdE⟩

section task
variable {A : Protocol P V M S} {e f : ℕ}

/-- **Lemma 3.** Assume `e ≥ 1` and `2e + 1 ≤ n ≤ 2e + f − 1`. For every partition
`Π = E₀ ⊔ E₁ ⊔ F₀ ⊔ F₁` with `|E₀| = |E₁| = e`, `|F₁| = k e`, and the initial configuration `Iₖ`
in which `E₀ ∪ F₀` propose `a` and `E₁ ∪ F₁` propose `b`, every process that decides by time `2Δ`
in an `E₀`-faulty synchronous run from `Iₖ` decides `a`. (The paper states the existence of such
a run, which then follows from Definition 4 (1).) -/
theorem lemma_3 (hA : SolvesTask A f) (h2 : TwoStepTask A e) {a b : V} (hab : a ≠ b)
    (he : 1 ≤ e) (hef : e ≤ f) (hlo : 2 * e + 1 ≤ Fintype.card P)
    (hhi : Fintype.card P + 1 ≤ 2 * e + f) :
    ∀ (k : ℕ) (E₀ E₁ F₁ : Finset P), Disjoint E₀ E₁ → Disjoint E₀ F₁ → Disjoint E₁ F₁ →
      E₀.card = e → E₁.card = e → F₁.card = k * e →
      ∀ o, IsOrder o → ∀ d τ v, τ ≤ 3 →
        (syncRun (M := M) E₀ (taskInv fun x => if x ∈ E₁ ∪ F₁ then b else a) o).DecidesAt A d τ v →
        v = a := by
  intro k
  induction k with
  | zero =>
    intro E₀ E₁ F₁ h01 h0F h1F c0 c1 cF o ho d τ v hτ hdec
    have hF : F₁ = ∅ := card_eq_zero.mp (by simpa using cF)
    subst hF
    set I : P → V := fun x => if x ∈ E₁ ∪ ∅ then b else a
    have hd : d ∉ E₀ := not_mem_of_decidesAt hA hab hdec
    by_contra hva
    obtain ⟨q, hq⟩ := syncRun_decides_mem hA (by omega : E₀.card ≤ f) ho hdec
    have hvb : v = b := by
      simp only [I] at hq; split_ifs at hq
      · exact hq.symm
      · exact absurd hq.symm hva
    have hF0 : (E₀ ∪ E₁)ᶜ.card = Fintype.card P - 2 * e := by
      rw [card_compl_union h01]; omega
    obtain ⟨d', hd'⟩ : (E₀ ∪ E₁)ᶜ.Nonempty := by rw [← card_pos, hF0]; omega
    have hd'1 : d' ∉ E₁ := by simp at hd'; tauto
    have hd'0 : d' ∉ E₀ := by simp at hd'; tauto
    obtain ⟨o', ho', τ', hτ', w, hw⟩ := (h2 E₁ c1).2 I
      (fun p hp q hq => by simp [I, hp, hq]) d' hd'1
    have hwa : w = a := syncRun_decides_eq hA (by omega) (fun x hx => by simp [I, hx]) ho' hw
    obtain ⟨x, hx⟩ : E₀.Nonempty := by rw [← card_pos]; omega
    have := merge_task hA h01 (I := I) (I' := I) (fun _ _ _ => rfl) ho ho' hd hd'1 hτ hτ' hdec hw
      ((card_mergeFaulty_le_of_mem hd').trans (by omega))
      ⟨x, not_mem_mergeFaulty_of (Or.inl hx) (by rintro rfl; exact hd hx)
        (by rintro rfl; exact hd'0 hx)⟩
    exact hab (by rw [← hwa, ← this, hvb])
  | succ k ih =>
    intro E₀ E₁ F₁ h01 h0F h1F c0 c1 cF o ho d τ v hτ hdec
    set I : P → V := fun x => if x ∈ E₁ ∪ F₁ then b else a
    have hd : d ∉ E₀ := not_mem_of_decidesAt hA hab hdec
    by_contra hva
    obtain ⟨q, hq⟩ := syncRun_decides_mem hA (by omega : E₀.card ≤ f) ho hdec
    have hvb : v = b := by
      simp only [I] at hq; split_ifs at hq
      · exact hq.symm
      · exact absurd hq.symm hva
    obtain ⟨q, hqF⟩ : F₁.Nonempty := by
      rw [← card_pos, cF]; exact Nat.mul_pos (by omega) he
    obtain ⟨Eh, Fh, h0Eh, h0Fh, hEhFh, cEh, cFh, hU, hdEh⟩ := exists_swap h01 h0F h1F hqF hd
    obtain ⟨E₁', hE₁'Fh, cE₁'⟩ := exists_subset_card_eq (s := Fh) (n := e)
      (by rw [cFh, cF]; nlinarith)
    set F₁' := Fh \ E₁'
    have cF₁' : F₁'.card = k * e := by
      rw [card_sdiff_of_subset hE₁'Fh, cFh, cF, cE₁']; rw [Nat.succ_mul]; omega
    have hU' : E₁' ∪ F₁' = Fh := union_sdiff_of_subset hE₁'Fh
    have hEhE₁' : Disjoint Eh E₁' := disjoint_of_subset_right hE₁'Fh hEhFh
    have hEhF₁' : Disjoint Eh F₁' := disjoint_of_subset_right sdiff_subset hEhFh
    have hE₁'F₁' : Disjoint E₁' F₁' := disjoint_sdiff
    set I' : P → V := fun x => if x ∈ E₁' ∪ F₁' then b else a
    obtain ⟨o', ho', d', τ', hτ', w, hw⟩ := (h2 Eh (by rw [cEh, c1])).1 I'
    have hwa : w = a := ih Eh E₁' F₁' hEhE₁' hEhF₁' hE₁'F₁' (by rw [cEh, c1]) cE₁' cF₁' o' ho' d' τ'
      w hτ' hw
    have hd'Eh : d' ∉ Eh := not_mem_of_decidesAt hA hab hw
    have hZ : ∀ z, z ∉ E₀ → z ∉ Eh → I z = I' z := by
      intro z _ hz
      simp only [I, I', hU']
      rw [← hU]
      simp [hz]
    have hcd : d ∈ (E₀ ∪ Eh)ᶜ := by simp [hd, hdEh]
    have hcard : (mergeFaulty E₀ Eh d d').card ≤ f := by
      rw [← mergeFaulty_comm]
      refine (card_mergeFaulty_le_of_mem (by rwa [union_comm])).trans ?_
      rw [union_comm, card_compl_union h0Eh, c0, cEh, c1]; omega
    obtain ⟨x, hx⟩ : Eh.Nonempty := by rw [← card_pos, cEh, c1]; omega
    have := merge_task hA h0Eh (I := I) (I' := I') hZ ho ho' hd hd'Eh hτ hτ' hdec hw hcard
      ⟨x, not_mem_mergeFaulty_of (Or.inr hx) (by rintro rfl; exact hdEh hx)
        (by rintro rfl; exact hd'Eh hx)⟩
    exact hab (by rw [← hwa, ← this, hvb])

/-- **Theorem 1, "only if"** (§B.1). If a protocol implements an `f`-resilient `e`-two-step
consensus task (Definitions 1 and 4) for `n ≥ 2` processes, with `e ≤ f` and at least two
values, then `n ≥ max {2e + f, 2f + 1}`. -/
theorem theorem_1_lower (hA : SolvesTask A f) (h2 : TwoStepTask A e) {a b : V} (hab : a ≠ b)
    (hn : 2 ≤ Fintype.card P) (hef : e ≤ f) :
    2 * e + f ≤ Fintype.card P ∧ 2 * f + 1 ≤ Fintype.card P := by
  have h2f := two_f_lt_task hA hab hn
  refine ⟨?_, h2f⟩
  by_contra hlt
  have he : 1 ≤ e := by omega
  set n := Fintype.card P
  set m := n - 2 * e
  set k := m / e
  have hkm : k * e ≤ m := Nat.div_mul_le_self m e
  have hmod : m - k * e < e := by
    have h1 := Nat.div_add_mod m e
    have h2 := Nat.mod_lt m (show 0 < e by omega)
    have h3 : k * e = e * (m / e) := Nat.mul_comm _ _
    omega
  obtain ⟨E₀, -, c0⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := e) (by simp; omega)
  obtain ⟨E₁, hE₁, c1⟩ := exists_subset_card_eq (s := E₀ᶜ) (n := e)
    (by rw [card_compl, c0]; omega)
  have h01 : Disjoint E₀ E₁ := disjoint_of_subset_right hE₁ disjoint_compl_right
  obtain ⟨F₁, hF₁, cF₁⟩ := exists_subset_card_eq (s := (E₀ ∪ E₁)ᶜ) (n := k * e)
    (by rw [card_compl_union h01, c0, c1]; omega)
  have h0F : Disjoint E₀ F₁ :=
    disjoint_of_subset_right hF₁ (disjoint_of_subset_left subset_union_left disjoint_compl_right)
  have h1F : Disjoint E₁ F₁ :=
    disjoint_of_subset_right hF₁ (disjoint_of_subset_left subset_union_right disjoint_compl_right)
  set F₀ := (E₀ ∪ E₁ ∪ F₁)ᶜ
  have cF₀ : F₀.card = m - k * e := by
    rw [card_compl, card_union_of_disjoint (disjoint_union_left.mpr ⟨h0F, h1F⟩),
      card_union_of_disjoint h01, c0, c1, cF₁]; omega
  set Ik : P → V := fun x => if x ∈ E₁ ∪ F₁ then b else a
  obtain ⟨o, ho, d, τ, hτ, v, hdec⟩ := (h2 E₀ c0).1 Ik
  have hva : v = a := lemma_3 hA h2 hab he hef (by omega) (by omega) k E₀ E₁ F₁ h01 h0F h1F c0 c1
    cF₁ o ho d τ v hτ hdec
  have hd : d ∉ E₀ := not_mem_of_decidesAt hA hab hdec
  have hF₀E₀ : F₀ ⊆ E₀ᶜ := by
    intro x hx; simp only [F₀, mem_compl, mem_union, not_or] at hx ⊢; exact hx.1.1
  obtain ⟨E, hF₀E, hEE₀, cE⟩ := exists_subsuperset_card_eq (n := e) hF₀E₀ (by omega)
    (by rw [card_compl, c0]; omega)
  have h0E : Disjoint E₀ E := disjoint_of_subset_right hEE₀ disjoint_compl_right
  have cF : (E₀ ∪ E)ᶜ.card = m := by rw [card_compl_union h0E, c0, cE]; omega
  obtain ⟨d', hd'⟩ : (E₀ ∪ E)ᶜ.Nonempty := by rw [← card_pos, cF]; omega
  have hd'E : d' ∉ E := by simp at hd'; tauto
  have hd'0 : d' ∉ E₀ := by simp at hd'; tauto
  set I : P → V := fun x => if x ∈ E₀ then b else Ik x
  have hIE : ∀ x ∉ E, I x = b := by
    intro x hx
    by_cases hx0 : x ∈ E₀
    · simp [I, hx0]
    · have : x ∉ F₀ := fun h => hx (hF₀E h)
      simp only [F₀, mem_compl, not_not, mem_union] at this
      simp only [I, Ik, hx0, ite_false, mem_union]
      rw [ite_eq_left (by tauto)]
  obtain ⟨o', ho', τ', hτ', w, hw⟩ := (h2 E cE).2 I
    (fun p hp q hq => by rw [hIE p hp, hIE q hq]) d' hd'E
  have hwb : w = b := syncRun_decides_eq hA (by omega) hIE ho' hw
  have hZ : ∀ z, z ∉ E₀ → z ∉ E → Ik z = I z := fun z hz _ => by simp [I, hz]
  obtain ⟨x, hx⟩ : E₀.Nonempty := by rw [← card_pos]; omega
  have := merge_task hA h0E (I := Ik) (I' := I) hZ ho ho' hd hd'E hτ hτ' hdec hw
    ((card_mergeFaulty_le_of_mem hd').trans (by rw [cF]; omega))
    ⟨x, not_mem_mergeFaulty_of (Or.inl hx) (by rintro rfl; exact hd hx)
      (by rintro rfl; exact hd'0 hx)⟩
  exact hab (by rw [← hva, this, hwb])

end task

section object
variable {A : Protocol P V M S} {e f : ℕ}

theorem singleInv_wellFormed (E : Finset P) (p : P) (t₀ : ℕ) (v : V)
    (o : P → ℕ → List (P × M) → List (P × M)) : (syncRun E (singleInv p t₀ v) o).WellFormed := by
  intro q τ τ' h h'
  simp only [syncRun, singleInv] at h h'
  split_ifs at h h' <;> simp_all

/-- In a synchronous run in which only `p` proposes `v`, only `v` can be returned. -/
theorem singleInv_responds_eq (hA : SolvesObject A f) {E : Finset P} (hE : E.card ≤ f) {p : P}
    {t₀ : ℕ} {v : V} {o : P → ℕ → List (P × M) → List (P × M)} (ho : IsOrder o) {d : P} {τ : ℕ}
    {u : V} (h : (syncRun E (singleInv p t₀ v) o).RespondsAt A d τ u) : u = v := by
  obtain ⟨q, t, -, hq⟩ := hA.validity _ (syncRun_valid hE _ ho)
    (singleInv_wellFormed E p t₀ v o) d τ u h
  simp only [syncRun, singleInv] at hq
  split_ifs at hq
  exact (Option.some.inj hq).symm

/-- **Theorem 2, "only if"**, strong form (§B.2: "item 2 is actually not required for the lower
bound"): only item (1) of Definition 5 is assumed. -/
theorem theorem_2_lower_of_item1 (hA : SolvesObject A f)
    (h2 : ∀ E : Finset P, E.card = e → ∀ (v : V), ∀ p ∉ E, ∃ t₀ ord, IsOrder ord ∧
      (syncRun (M := M) E (singleInv p t₀ v) ord).RespondedBy2 A p)
    {a b : V} (hab : a ≠ b) (hn : 2 ≤ Fintype.card P) (hef : e ≤ f) :
    2 * e + f ≤ Fintype.card P + 1 ∧ 2 * f + 1 ≤ Fintype.card P := by
  have h2f := two_f_lt_object hA hab hn
  refine ⟨?_, h2f⟩
  by_contra hlt
  set n := Fintype.card P
  obtain ⟨X₀, -, c0⟩ := exists_subset_card_eq (s := (univ : Finset P)) (n := e) (by simp; omega)
  obtain ⟨X₁, hX₁, c1⟩ := exists_subset_card_eq (s := X₀ᶜ) (n := e)
    (by rw [card_compl, c0]; omega)
  have h01 : Disjoint X₀ X₁ := disjoint_of_subset_right hX₁ disjoint_compl_right
  obtain ⟨p, hp⟩ : X₁.Nonempty := by rw [← card_pos]; omega
  obtain ⟨q, hq⟩ : X₀.Nonempty := by rw [← card_pos]; omega
  have hp0 : p ∉ X₀ := fun h => disjoint_left.mp h01 h hp
  have hq1 : q ∉ X₁ := fun h => disjoint_left.mp h01 hq h
  obtain ⟨t₀, o₀, ho₀, τ, hτ, u, hu⟩ := h2 X₀ c0 a p hp0
  obtain ⟨t₁, o₁, ho₁, τ', hτ', u', hu'⟩ := h2 X₁ c1 b q hq1
  have hua : u = a := singleInv_responds_eq hA (by omega) ho₀ hu
  have hub : u' = b := singleInv_responds_eq hA (by omega) ho₁ hu'
  -- a process `r ∈ X₀ ∪ X₁` other than `p`, `q`
  obtain ⟨r, hr⟩ : ((X₀ ∪ X₁) \ {p, q}).Nonempty := by
    rw [← card_pos]
    have := le_card_sdiff ({p, q} : Finset P) (X₀ ∪ X₁)
    rw [card_union_of_disjoint h01, c0, c1] at this
    have := card_le_two (a := p) (b := q)
    omega
  simp only [mem_sdiff, mem_union, mem_insert, mem_singleton, not_or] at hr
  obtain ⟨hrXY, hrp, hrq⟩ := hr
  have hZ : ∀ z, z ∉ X₀ → z ∉ X₁ → singleInv p t₀ a z 0 = singleInv q t₁ b z 0 := by
    intro z hz0 hz1
    have : z ≠ p := by rintro rfl; exact hz1 hp
    have : z ≠ q := by rintro rfl; exact hz0 hq
    simp_all [singleInv]
  have hcard : (mergeFaulty X₀ X₁ p q).card ≤ f :=
    (card_mergeFaulty_le X₀ X₁ p q).trans (by rw [card_compl_union h01, c0, c1]; omega)
  have := merge_object hA h01 hZ ho₀ ho₁ (singleInv_wellFormed _ _ _ _ _)
    (singleInv_wellFormed _ _ _ _ _) hp0 hq1 hτ hτ' hu hu' hcard
    (not_mem_mergeFaulty_of hrXY hrp hrq) (fun t => by simp [singleInv, hrp, hrq])
  exact hab (by rw [← hua, this, hub])

/-- **Theorem 2, "only if"** (§B.2). If a protocol implements an `f`-resilient `e`-two-step
consensus object (Definition 5) for `n ≥ 2` processes, with `e ≤ f` and at least two values, then
`n ≥ max {2e + f − 1, 2f + 1}`. -/
theorem theorem_2_lower (hA : SolvesObject A f) (h2 : TwoStepObject A e) {a b : V} (hab : a ≠ b)
    (hn : 2 ≤ Fintype.card P) (hef : e ≤ f) :
    2 * e + f ≤ Fintype.card P + 1 ∧ 2 * f + 1 ≤ Fintype.card P :=
  theorem_2_lower_of_item1 hA (fun E hE => (h2 E hE).1) hab hn hef

end object

end TwoStepConsensus
