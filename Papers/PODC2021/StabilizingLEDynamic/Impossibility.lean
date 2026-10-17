import Papers.PODC2021.StabilizingLEDynamic.Model

/-!
# Impossibility results (Section 3)

* `lemma_1`: in the quasi-complete graph `PK(V, p)` (all edges except those leaving `p`), the
  processes cannot keep electing `p` forever (they cannot tell `p` from a fake identifier).
* `theorem_2`: no self-stabilizing leader election in `J^B_{1,*}(Δ)`.
* `theorem_3`: no pseudo-stabilizing leader election in `J^Q_{1,*}(Δ)` (adaptive adversary
  alternating `K(V)` and `PK(V, ℓ)`).
* `theorem_4`: no pseudo-stabilizing leader election in `J^B_{*,1}(Δ)` (`n ≥ 3`, in-star).
* `theorem_5`: the pseudo-stabilization time in `J^B_{1,*}(Δ)` cannot be bounded.

All statements are per system size `n` (the algorithm may know `n` and `Δ`), and need an infinite
identifier domain (so that fake identifiers exist; see `Counterexample.lean` for why) and a
nonempty state type.
-/

namespace StabilizingLEDynamic

open Cslib.HeardOf
open Cslib.DynNet (Journey tdist tdist_le_iff)

variable {ι σ : Type*}

/-! ### The graphs used in the proofs -/

/-- The complete digraph `K(X)` (Definition 4). -/
def K (X : Finset ι) : Graph ι := fun p q => p ∈ X ∧ q ∈ X ∧ p ≠ q

/-- The quasi-complete digraph `PK(X, y)`: all edges between distinct vertices of `X` except
those leaving `y` (Definition 3). -/
def PK (X : Finset ι) (y : ι) : Graph ι := fun p q => p ∈ X ∧ q ∈ X ∧ p ≠ y ∧ p ≠ q

/-- The in-star `S(X, y)`: edges `p → y` for all `p ∈ X \ {y}` (Definition 5). -/
def InStar (X : Finset ι) (y : ι) : Graph ι := fun p q => p ∈ X ∧ q = y ∧ p ≠ y

/-- A dynamic graph in which some vertex `z` has an edge to every other vertex in every round
belongs to `J^B_{1,*}(Δ)`. -/
theorem mem_J1sB_of_outStar {V : Finset ι} {G : DG ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hG : IsDG V G)
    {z : ι} (hz : z ∈ V) (hout : ∀ t, ∀ p ∈ V, p ≠ z → G t z p) : G ∈ J1sB Δ V := by
  refine ⟨hG, z, hz, fun p hp i => tdist_le_iff.mpr ?_⟩
  by_cases hpz : p = z
  · subst hpz; exact Journey.self (by omega)
  · exact (Journey.single (hout i p hp hpz)).mono_right (by omega)

/-- A dynamic graph in which some vertex `z` infinitely often has an edge to every other vertex
belongs to `J^Q_{1,*}(Δ)`. -/
theorem mem_J1sQ_of_outStar {V : Finset ι} {G : DG ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hG : IsDG V G)
    {z : ι} (hz : z ∈ V) (hout : ∀ i, ∃ j ≥ i, ∀ p ∈ V, p ≠ z → G j z p) : G ∈ J1sQ Δ V := by
  refine ⟨hG, z, hz, fun p hp i => ?_⟩
  obtain ⟨j, hji, hj⟩ := hout i
  refine ⟨j, hji, tdist_le_iff.mpr ?_⟩
  by_cases hpz : p = z
  · subst hpz; exact Journey.self (by omega)
  · exact (Journey.single (hj p hp hpz)).mono_right (by omega)

theorem isDG_K (V : Finset ι) : IsDG V (fun _ => K V) := fun _ _ _ h => h

theorem isDG_PK (V : Finset ι) (y : ι) : IsDG V (fun _ => PK V y) :=
  fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.2⟩

theorem exists_other {V : Finset ι} (hV : 2 ≤ V.card) (y : ι) : ∃ z ∈ V, z ≠ y := by
  by_contra h
  push Not at h
  have : V ⊆ {y} := fun z hz => Finset.mem_singleton.mpr (h z hz)
  have := Finset.card_le_card this
  simp at this; omega

theorem PK_mem_J1sB {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hV : 2 ≤ V.card) (y : ι) :
    (fun _ => PK V y) ∈ J1sB Δ V := by
  obtain ⟨z, hz, hzy⟩ := exists_other hV y
  exact mem_J1sB_of_outStar hΔ (isDG_PK V y) hz fun _ p hp hpz => ⟨hz, hp, hzy, Ne.symm hpz⟩

theorem PK_mem_J1sQ {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hV : 2 ≤ V.card) (y : ι) :
    (fun _ => PK V y) ∈ J1sQ Δ V := by
  obtain ⟨z, hz, hzy⟩ := exists_other hV y
  exact mem_J1sQ_of_outStar hΔ (isDG_PK V y) hz
    fun i => ⟨i, le_rfl, fun p hp hpz => ⟨hz, hp, hzy, Ne.symm hpz⟩⟩

theorem K_mem_J1sB {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) {z : ι} (hz : z ∈ V) :
    (fun _ => K V) ∈ J1sB Δ V :=
  mem_J1sB_of_outStar hΔ (isDG_K V) hz fun _ p hp hpz => ⟨hz, hp, Ne.symm hpz⟩

theorem InStar_mem_Js1B {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) {y : ι} (hy : y ∈ V) :
    (fun _ => InStar V y) ∈ Js1B Δ V := by
  refine ⟨fun _ p q h => ⟨h.1, h.2.1 ▸ hy, h.2.1 ▸ h.2.2⟩, y, hy, fun p hp i => ?_⟩
  refine tdist_le_iff.mpr ?_
  by_cases hpy : p = y
  · subst hpy; exact Journey.self (by omega)
  · exact (Journey.single (show InStar V y p y from ⟨hp, rfl, hpy⟩)).mono_right (by omega)

/-- Swap one process of a vertex set for a fresh one: same cardinality. -/
theorem card_swap [DecidableEq ι] {V : Finset ι} {p v : ι} (hp : p ∈ V) (hv : v ∉ V) :
    (insert v (V.erase p)).card = V.card := by
  rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_of_mem_erase h)),
    Finset.card_erase_of_mem hp]
  have := Finset.card_pos.mpr ⟨p, hp⟩
  omega

/-- Any class containing all the dynamic graphs `PK(X, y)` (`|X| = n`, `y ∈ X`). -/
def ContainsPK (C : DGClass ι) (n : ℕ) : Prop :=
  ∀ X : Finset ι, X.card = n → ∀ y ∈ X, (fun _ => PK X y) ∈ C X

/-! ### Lemma 1 -/

/-- **Lemma 1** (Lemma 3.2 of the PODC version). Let `A` be pseudo-stabilizing for a class
containing all `PK(X, y)` (e.g. `J^B_{1,*}(Δ)`), `|V| = n ≥ 2`, `p ∈ V`. Then in the execution of
`A` in `PK(V, p)` from any configuration, some process of `V` eventually does not elect `p`. -/
theorem lemma_1 [Infinite ι] {A : Algorithm ι σ} {C : DGClass ι} {n : ℕ}
    (hA : PseudoStab A C n) (hC : ContainsPK C n) {V : Finset ι} (hV : V.card = n)
    (h2 : 2 ≤ n) {p : ι} (hp : p ∈ V) (γ : ι → σ) :
    ∃ t, ∃ q ∈ V, A.lid q (exec A (fun _ => PK V p) γ t q) ≠ p := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset V
  set V' := insert v (V.erase p) with hV'
  have hcard : V'.card = n := by rw [card_swap hp hv, hV]
  have hvp : v ≠ p := fun h => hv (h ▸ hp)
  -- the processes of `V \ {p}` behave identically in `PK(V, p)` and `PK(V', v)`
  have hagree : ∀ t, ∀ q ∈ (↑(V.erase p) : Set ι),
      exec A (fun _ => PK V p) γ t q = exec A (fun _ => PK V' v) γ t q := by
    refine conf_agree _ (fun t q hq j => ?_) (fun t q hq j hj => ?_) (fun _ _ => rfl)
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hq
      simp only [Hears, PK, hV', Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (h | ⟨h1, -, h3, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr ⟨h3, h1⟩, Or.inr ⟨hq.2, hq.1⟩, fun h => hv (h ▸ h1), h4⟩
      · rintro (h | ⟨h1, -, h3, h4⟩)
        · exact Or.inl h
        · refine Or.inr ⟨?_, hq.1, ?_, h4⟩
          · rcases h1 with h1 | h1
            · exact absurd h1 h3
            · exact h1.2
          · rcases h1 with h1 | h1
            · exact absurd h1 h3
            · exact h1.1
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hq ⊢
      rcases hj with rfl | ⟨h1, -, h3, -⟩
      · exact hq
      · exact ⟨h1, h3⟩
  obtain ⟨z, hz, hzp⟩ := exists_other (hV ▸ h2) p
  have hz' : z ∈ V.erase p := Finset.mem_erase.mpr ⟨hzp, hz⟩
  obtain ⟨i, ℓ, hℓ, hall⟩ := hA V' hcard _ (hC V' hcard v (Finset.mem_insert_self _ _)) γ
  have h1 := hall 0 z (Finset.mem_insert_of_mem hz')
  simp only [Nat.add_zero] at h1
  rw [← hagree i z (by simp [hz, hzp]), hcon i z hz] at h1
  subst h1
  rcases Finset.mem_insert.mp hℓ with h | h
  · exact hvp h.symm
  · exact (Finset.notMem_erase _ _) h

theorem containsPK_J1sB {Δ n : ℕ} (hΔ : 1 ≤ Δ) (h2 : 2 ≤ n) :
    ContainsPK (ι := ι) (J1sB Δ) n :=
  fun _ hX y _ => PK_mem_J1sB hΔ (hX ▸ h2) y

theorem containsPK_J1sQ {Δ n : ℕ} (hΔ : 1 ≤ Δ) (h2 : 2 ≤ n) :
    ContainsPK (ι := ι) (J1sQ Δ) n :=
  fun _ hX y _ => PK_mem_J1sQ hΔ (hX ▸ h2) y

/-! ### Theorem 2 -/

/-- **Theorem 2** (Theorem 3.3 of the PODC version). There is no deterministic self-stabilizing
leader election algorithm for `J^B_{1,*}(Δ)` (for any number `n ≥ 2` of processes). -/
theorem theorem_2 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h2 : 2 ≤ n) : ¬ SelfStab A (J1sB Δ) n := by
  intro hS
  have hP : PseudoStab A (J1sB Δ) n := hS.pseudoStab fun _ _ hG i => J_shift hG i
  obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι n
  obtain ⟨L, hconv, hcorr⟩ := hS V hV
  obtain ⟨z, hz, -⟩ := exists_other (hV ▸ h2) (Classical.arbitrary ι)
  obtain ⟨i, hi⟩ := hconv _ (K_mem_J1sB hΔ hz) (fun _ => Classical.arbitrary σ)
  set γ := exec A (fun _ => K V) (fun _ => Classical.arbitrary σ) i
  obtain ⟨ℓ, hℓ, hK⟩ := hcorr _ (K_mem_J1sB hΔ hz) γ hi
  obtain ⟨ℓ', -, hPK⟩ := hcorr _ (PK_mem_J1sB hΔ (hV ▸ h2) ℓ) γ hi
  have hℓℓ' : ℓ' = ℓ := by
    have h1 := hPK 0 z hz; have h2 := hK 0 z hz
    simp only [exec, conf_zero] at h1 h2
    rw [← h1, h2]
  subst hℓℓ'
  obtain ⟨t, q, hq, hne⟩ := lemma_1 hP (containsPK_J1sB hΔ h2) hV h2 hℓ γ
  exact hne (hPK t q hq)

/-! ### Theorem 3 -/

/-- All processes of `V` elect `ℓ` in configuration `C`. -/
def Unan (A : Algorithm ι σ) (V : Finset ι) (C : ι → σ) (ℓ : ι) : Prop :=
  ∀ q ∈ V, A.lid q (C q) = ℓ

theorem Unan.unique {A : Algorithm ι σ} {V : Finset ι} {C : ι → σ} {ℓ ℓ' : ι}
    (hV : V.Nonempty) (h : Unan A V C ℓ) (h' : Unan A V C ℓ') : ℓ = ℓ' := by
  obtain ⟨q, hq⟩ := hV
  rw [← h q hq, h' q hq]

open Classical in
/-- The adversary of Theorem 3: if the last two configurations have the same unanimous leader
`ℓ`, play `PK(V, ℓ)`, otherwise play `K(V)`. -/
noncomputable def advGraph (A : Algorithm ι σ) (V : Finset ι) (C C' : ι → σ) : Graph ι :=
  if h : ∃ ℓ, ℓ ∈ V ∧ Unan A V C ℓ ∧ Unan A V C' ℓ then PK V h.choose else K V

/-- The pair (configuration `t`, configuration `t + 1`) of the adaptive execution. -/
noncomputable def advPair (A : Algorithm ι σ) (V : Finset ι) (γ : ι → σ) :
    ℕ → (ι → σ) × (ι → σ)
  | 0 => (γ, next A.step (K V) γ)
  | t + 1 => ((advPair A V γ t).2,
      next A.step (advGraph A V (advPair A V γ t).1 (advPair A V γ t).2) (advPair A V γ t).2)

/-- The dynamic graph built on the fly in the proof of Theorem 3. -/
noncomputable def advDG (A : Algorithm ι σ) (V : Finset ι) (γ : ι → σ) : DG ι
  | 0 => K V
  | t + 1 => advGraph A V (advPair A V γ t).1 (advPair A V γ t).2

theorem advPair_eq (A : Algorithm ι σ) (V : Finset ι) (γ : ι → σ) (t : ℕ) :
    (advPair A V γ t).1 = exec A (advDG A V γ) γ t ∧
      (advPair A V γ t).2 = exec A (advDG A V γ) γ (t + 1) := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    refine ⟨ih.2, ?_⟩
    change next A.step (advDG A V γ (t + 1)) (advPair A V γ t).2 = _
    rw [ih.2]; rfl

theorem advDG_succ (A : Algorithm ι σ) (V : Finset ι) (γ : ι → σ) (t : ℕ) :
    advDG A V γ (t + 1) =
      advGraph A V (exec A (advDG A V γ) γ t) (exec A (advDG A V γ) γ (t + 1)) := by
  change advGraph A V _ _ = _
  rw [(advPair_eq A V γ t).1, (advPair_eq A V γ t).2]

/-- If from some time on all configurations have the same unanimous leader, the adversary of
Theorem 3 plays `PK(V, ℓ)` forever, contradicting Lemma 1. -/
theorem adv_not_eventually_unan [Infinite ι] {A : Algorithm ι σ} {C : DGClass ι} {n : ℕ}
    (hP : PseudoStab A C n) (hC : ContainsPK C n) {V : Finset ι} (hV : V.card = n) (h2 : 2 ≤ n)
    (γ : ι → σ) {i : ℕ} {ℓ : ι} (hℓ : ℓ ∈ V)
    (h : ∀ t ≥ i, Unan A V (exec A (advDG A V γ) γ t) ℓ) : False := by
  have hVne : V.Nonempty := ⟨ℓ, hℓ⟩
  have hG : ∀ t ≥ i, advDG A V γ (t + 1) = PK V ℓ := by
    intro t ht
    have hex : ∃ ℓ', ℓ' ∈ V ∧ Unan A V (exec A (advDG A V γ) γ t) ℓ' ∧
        Unan A V (exec A (advDG A V γ) γ (t + 1)) ℓ' := ⟨ℓ, hℓ, h t ht, h (t + 1) (by omega)⟩
    rw [advDG_succ, advGraph, dif_pos hex]
    congr 1
    exact hex.choose_spec.2.1.unique hVne (h t ht)
  have hsh : shift (i + 1) (advDG A V γ) = fun _ => PK V ℓ := by
    funext t; simp only [shift]; rw [show i + 1 + t = (i + t) + 1 by omega]; exact hG _ (by omega)
  obtain ⟨t, q, hq, hne⟩ := lemma_1 hP hC hV h2 hℓ (exec A (advDG A V γ) γ (i + 1))
  apply hne
  rw [← hsh, ← exec_add]
  exact h _ (by omega) q hq

/-- **Theorem 3** (Theorem 3.5 of the PODC version). There is no deterministic
pseudo-stabilizing leader election algorithm for `J^Q_{1,*}(Δ)` (for any `n ≥ 2`). -/
theorem theorem_3 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h2 : 2 ≤ n) : ¬ PseudoStab A (J1sQ Δ) n := by
  intro hP
  have hC := containsPK_J1sQ (ι := ι) hΔ h2
  obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι n
  obtain ⟨z, hz, -⟩ := exists_other (hV ▸ h2) (Classical.arbitrary ι)
  have hVne : V.Nonempty := ⟨z, hz⟩
  set γ : ι → σ := fun _ => Classical.arbitrary σ
  set G := advDG A V γ
  -- `K(V)` is played infinitely often
  have hinf : ∀ i, ∃ j ≥ i, G j = K V := by
    intro i
    by_contra hcon
    push Not at hcon
    have hu : ∀ t ≥ i, ∃ ℓ, ℓ ∈ V ∧ Unan A V (exec A G γ t) ℓ ∧
        Unan A V (exec A G γ (t + 1)) ℓ := by
      intro t ht
      by_contra hno
      apply hcon (t + 1) (by omega)
      change advDG A V γ (t + 1) = K V
      rw [advDG_succ, advGraph, dif_neg hno]
    obtain ⟨ℓ, hℓV, hℓ0, -⟩ := hu i le_rfl
    have hall : ∀ t ≥ i, Unan A V (exec A G γ t) ℓ := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact hℓ0
      | succ t ht ih =>
        obtain ⟨ℓ', -, h1, h2⟩ := hu t ht
        rwa [← ih.unique hVne h1] at h2
    exact adv_not_eventually_unan hP hC hV h2 γ hℓV hall
  have hdg : IsDG V G := by
    intro t a b hab
    cases t with
    | zero => exact hab
    | succ t =>
      change advDG A V γ (t + 1) a b at hab
      rw [advDG_succ, advGraph] at hab
      split_ifs at hab
      · exact ⟨hab.1, hab.2.1, hab.2.2.2⟩
      · exact hab
  have hGQ : G ∈ J1sQ Δ V := mem_J1sQ_of_outStar hΔ hdg hz fun i => by
    obtain ⟨j, hj, hGj⟩ := hinf i
    exact ⟨j, hj, fun p hp hpz => by rw [hGj]; exact ⟨hz, hp, Ne.symm hpz⟩⟩
  obtain ⟨i, ℓ, hℓ, hall⟩ := hP V hV G hGQ γ
  refine adv_not_eventually_unan hP hC hV h2 γ hℓ (i := i) fun t ht q hq => ?_
  have := hall (t - i) q hq
  simp only at this
  rwa [show i + (t - i) = t by omega] at this

/-! ### Theorem 4 -/

/-- **Theorem 4** (Theorem 3.8 of the PODC version). There is no deterministic
pseudo-stabilizing leader election algorithm for `J^B_{*,1}(Δ)` (for any `n ≥ 3`). -/
theorem theorem_4 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h3 : 3 ≤ n) : ¬ PseudoStab A (Js1B Δ) n := by
  classical
  intro hP
  obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι n
  obtain ⟨p, hp, -⟩ := exists_other (show 2 ≤ V.card by omega) (Classical.arbitrary ι)
  set G : DG ι := fun _ => InStar V p
  set γ : ι → σ := fun _ => Classical.arbitrary σ
  obtain ⟨i, ℓ, hℓ, hall⟩ := hP V hV G (InStar_mem_Js1B hΔ hp) γ
  -- every leaf of the star elects itself
  have hleaf : ∀ q ∈ V, q ≠ p → ℓ = q := by
    intro q hq hqp
    by_contra hℓq
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset V
    set V' := insert w (V.erase ℓ)
    have hcard : V'.card = n := by rw [card_swap hℓ hw, hV]
    have hqV' : q ∈ V' := Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hℓq, hq⟩)
    have hwV' : w ∈ V' := Finset.mem_insert_self _ _
    set γ' := exec A G γ i
    obtain ⟨i', ℓ', hℓ', hall'⟩ := hP V' hcard _ (InStar_mem_Js1B hΔ hwV') γ'
    have hdeaf : exec A (fun _ => InStar V' w) γ' i' q = exec A G γ (i + i') q := by
      rw [exec_add]
      refine conf_agree_deaf (fun _ j hj => ?_) (fun _ j hj => ?_) rfl i'
      · exact absurd hj.2.1 (fun h => (h ▸ hw) (hq))
      · exact absurd hj.2.1 hqp
    have h1 := hall' 0 q hqV'
    simp only [Nat.add_zero] at h1
    rw [hdeaf, hall i' q hq] at h1
    subst h1
    rcases Finset.mem_insert.mp hℓ' with h | h
    · exact hw (h ▸ hℓ)
    · exact (Finset.notMem_erase _ _) h
  obtain ⟨q₁, hq₁, hq₁p⟩ := exists_other (show 2 ≤ V.card by omega) p
  obtain ⟨q₂, hq₂, hq₂ne⟩ : ∃ q₂ ∈ V.erase p, q₂ ≠ q₁ := by
    refine exists_other ?_ q₁
    rw [Finset.card_erase_of_mem hp]; omega
  rw [Finset.mem_erase] at hq₂
  exact hq₂ne ((hleaf q₂ hq₂.2 hq₂.1).symm.trans (hleaf q₁ hq₁ hq₁p))

/-! ### Theorem 5 -/

/-- **Theorem 5** (Theorem 3.11 of the PODC version). The pseudo-stabilization time of leader
election in `J^B_{1,*}(Δ)` cannot be bounded: for `n ≥ 2` processes, no algorithm has all its
pseudo-stabilization phases of length at most `T`, for any `T`. (The paper assumes `A`
pseudo-stabilizing; a bound on the phase length implies it.) -/
theorem theorem_5 [Infinite ι] [Nonempty σ] (A : Algorithm ι σ) {Δ n : ℕ} (hΔ : 1 ≤ Δ)
    (h2 : 2 ≤ n) (T : ℕ) : ¬ PseudoStabWithin A (J1sB Δ) n T := by
  intro hT
  have hP := hT.pseudoStab
  obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι n
  obtain ⟨z, hz, -⟩ := exists_other (hV ▸ h2) (Classical.arbitrary ι)
  set γ : ι → σ := fun _ => Classical.arbitrary σ
  obtain ⟨ℓ, hℓ, hK⟩ := hT V hV _ (K_mem_J1sB hΔ hz) γ
  obtain ⟨z', hz', hz'ℓ⟩ := exists_other (hV ▸ h2) ℓ
  set G : DG ι := splice (fun _ => K V) T (fun _ => PK V ℓ)
  have hG : G ∈ J1sB Δ V := by
    refine mem_J1sB_of_outStar hΔ (fun t a b h => ?_) hz' (fun t p hp hpz => ?_)
    · simp only [G, splice] at h; split_ifs at h
      · exact h
      · exact ⟨h.1, h.2.1, h.2.2.2⟩
    · simp only [G, splice]; split_ifs
      · exact ⟨hz', hp, Ne.symm hpz⟩
      · exact ⟨hz', hp, hz'ℓ, Ne.symm hpz⟩
  obtain ⟨ℓ', -, hG'⟩ := hT V hV G hG γ
  have hsplice : ∀ t, exec A G γ (T + t) =
      exec A (fun _ => PK V ℓ) (exec A (fun _ => K V) γ T) t := fun t => conf_splice _ _ _ _ _
  have hℓℓ' : ℓ' = ℓ := by
    have h1 : A.lid z (exec A G γ (T + 0) z) = ℓ' := hG' 0 z hz
    have h2 : A.lid z (exec A (fun _ => K V) γ (T + 0) z) = ℓ := hK 0 z hz
    rw [hsplice] at h1
    exact h1.symm.trans h2
  subst hℓℓ'
  obtain ⟨t, q, hq, hne⟩ :=
    lemma_1 hP (containsPK_J1sB hΔ h2) hV h2 hℓ (exec A (fun _ => K V) γ T)
  apply hne
  have := hG' t q hq
  simp only [hsplice] at this
  exact this

end StabilizingLEDynamic
