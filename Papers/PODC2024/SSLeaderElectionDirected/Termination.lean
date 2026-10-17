import Papers.PODC2024.SSLeaderElectionDirected.CMAI

/-!
# Termination of C-MAI (Lemma 4)

We prove that every run of C-MAI whose inputs are eventually constant is eventually constant
(`Run.eventually_const`), under an arbitrary (unfair, distributed) choice of activated processes.

The paper proves Lemma 4 with limit inferiors of key sequences. We use an equivalent but more
elementary argument, by well-founded induction over the finitely many keys that can occur: once all
keys `< k` are frozen, a process that *moves to* `k` is supported by a frozen predecessor (or by its
own constant input) and stays at `k` forever; hence each process enters/leaves `k` at most once
more, and keys `≤ k` freeze as well.
-/

set_option linter.unusedSectionVars false

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

namespace CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {D : Type*} [LinearOrder D]
  {α : ℕ} {I : ℕ → V → D} {K : ℕ → V → Key D} {A : ℕ → Set V}

/-- All keys `≤ k` (at time `t` or at time `T`) are constant from time `T` on. -/
def Frozen (K : ℕ → V → Key D) (k : Key D) (T : ℕ) : Prop :=
  ∀ t, T ≤ t → ∀ p, (K t p ≤ k ∨ K T p ≤ k) → K t p = K T p

/-- All keys `< k` (at time `t` or at time `T`) are constant from time `T` on. -/
def FrozenBelow (K : ℕ → V → Key D) (k : Key D) (T : ℕ) : Prop :=
  ∀ t, T ≤ t → ∀ p, (K t p < k ∨ K T p < k) → K t p = K T p

theorem Frozen.mono_time {k : Key D} {T T' : ℕ} (h : Frozen K k T) (hT : T ≤ T') :
    Frozen K k T' := by
  intro t ht p hp
  have e1 : K T' p = K T p := by
    rcases hp with hp | hp
    · have := h t (by omega) p (Or.inl hp)
      exact h T' hT p (Or.inr (this ▸ hp))
    · exact h T' hT p (Or.inl hp)
  rcases hp with hp | hp
  · rw [h t (by omega) p (Or.inl hp), e1]
  · rw [h t (by omega) p (Or.inr (e1 ▸ hp)), e1]

/-- A Boolean property with no "rising edge" after which it fails is eventually constant. -/
theorem eventually_iff_const (b : ℕ → Prop) (T₀ : ℕ)
    (h : ∀ s, T₀ ≤ s → ¬ b s → b (s + 1) → ∀ t, s + 1 ≤ t → b t) :
    ∃ T', T₀ ≤ T' ∧ ∀ t, T' ≤ t → (b t ↔ b T') := by
  by_cases hrise : ∃ s, T₀ ≤ s ∧ ¬ b s ∧ b (s + 1)
  · obtain ⟨s, hs, h1, h2⟩ := hrise
    have hall := h s hs h1 h2
    exact ⟨s + 1, by omega, fun t ht => ⟨fun _ => hall _ le_rfl, fun _ => hall t ht⟩⟩
  · push Not at hrise
    by_cases hfall : ∃ s, T₀ ≤ s ∧ ¬ b s
    · obtain ⟨s, hs, h1⟩ := hfall
      have hall : ∀ t, s ≤ t → ¬ b t := by
        intro t ht
        induction ht with
        | refl => exact h1
        | step hle ih => exact fun hb => hrise _ (le_trans hs hle) ih hb
      exact ⟨s, hs, fun t ht => ⟨fun hb => absurd hb (hall t ht), fun hb => absurd hb h1⟩⟩
    · push Not at hfall
      exact ⟨T₀, le_rfl, fun t ht => ⟨fun _ => hfall T₀ le_rfl, fun _ => hfall t ht⟩⟩

variable (hR : Run G α I K A) {T : ℕ} (hI : ∀ t, T ≤ t → I t = I T)
include hR hI

/-- Once keys `< k` are frozen, a process that moves to `k` stays at `k` forever. -/
theorem stick {k : Key D} {T₀ : ℕ} (hT₀ : T ≤ T₀) (hF : FrozenBelow K k T₀) {s : ℕ} (hs : T₀ ≤ s)
    {p : V} (h1 : K s p ≠ k) (h2 : K (s + 1) p = k) : ∀ t, s + 1 ≤ t → K t p = k := by
  have hpA : p ∈ A s := by
    by_contra hp; exact h1 (hR.stay s p hp ▸ h2)
  have hbk : bestKey G α (I s) (K s) p = k := hR.move s p hpA ▸ h2
  -- `K s p` is not below `k`: otherwise `p` would be frozen below `k`
  have hnotbelow : ¬ K T₀ p < k := by
    intro hlt
    have := hF (s + 1) (by omega) p (Or.inr hlt)
    rw [h2] at this
    exact absurd (this ▸ hlt) (lt_irrefl _)
  -- the support of `k` persists
  have hsupp : ∀ t, s ≤ t → k ∈ keySet G α (I t) (K t) p := by
    intro t ht
    have hk := hbk ▸ bestKey_mem (G := G) (α := α) (I := I s) (K := K s) (p := p)
    rcases mem_keySet.mp hk with hk | ⟨q, hq, hd, hk⟩
    · rw [hk, hI t (by omega), ← hI s (by omega)]; exact selfKey_mem_keySet
    · have hqlt : K s q < k := hk ▸ Key.lt_succ _
      have e1 := hF s hs q (Or.inl hqlt)
      have e2 := hF t (by omega) q (Or.inr (e1 ▸ hqlt))
      have : K t q = K s q := e2.trans e1.symm
      rw [hk, ← this]; exact succ_mem_keySet hq (this ▸ hd)
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h2
  | succ t hle ih =>
    by_cases hpt : p ∈ A t
    · rw [hR.move t p hpt]
      have hle' : bestKey G α (I t) (K t) p ≤ k := bestKey_le (hsupp t (by omega))
      rcases lt_or_eq_of_le hle' with hlt | heq
      · exfalso
        have hm := hR.move t p hpt
        have := hF (t + 1) (by omega) p (Or.inl (hm ▸ hlt))
        exact hnotbelow (this ▸ hm ▸ hlt)
      · exact heq
    · rw [hR.stay t p hpt]; exact ih

/-- Inductive step of the freezing argument. -/
theorem frozen_of_frozenBelow {k : Key D} {T₀ : ℕ} (hT₀ : T ≤ T₀) (hF : FrozenBelow K k T₀) :
    ∃ T₁, T₀ ≤ T₁ ∧ Frozen K k T₁ := by
  classical
  have hev : ∀ p, ∃ T', T₀ ≤ T' ∧ ∀ t, T' ≤ t → (K t p = k ↔ K T' p = k) := fun p =>
    eventually_iff_const (fun t => K t p = k) T₀ fun s hs h1 h2 =>
      stick hR hI hT₀ hF hs h1 h2
  choose Tp hTp1 hTp2 using hev
  refine ⟨T₀ ⊔ Finset.univ.sup Tp, le_sup_left, ?_⟩
  set T₁ := T₀ ⊔ Finset.univ.sup Tp
  have hpT : ∀ p, Tp p ≤ T₁ := fun p =>
    le_sup_of_le_right (Finset.le_sup (f := Tp) (Finset.mem_univ p))
  have hT01 : T₀ ≤ T₁ := le_sup_left
  intro t ht p hp
  have heq : ∀ u, T₁ ≤ u → (K u p = k ↔ K T₁ p = k) := fun u hu =>
    (hTp2 p u (by have := hpT p; omega)).trans (hTp2 p T₁ (hpT p)).symm
  rcases hp with hp | hp
  · rcases lt_or_eq_of_le hp with hp | hp
    · rw [hF t (by omega) p (Or.inl hp)]
      have hlt : K T₀ p < k := (hF t (by omega) p (Or.inl hp)) ▸ hp
      exact (hF T₁ hT01 p (Or.inr hlt)).symm
    · rw [hp, ((heq t ht).mp hp)]
  · rcases lt_or_eq_of_le hp with hp | hp
    · have e1 := hF T₁ hT01 p (Or.inl hp)
      rw [hF t (by omega) p (Or.inr (e1 ▸ hp)), e1]
    · rw [hp, (heq t ht).mpr hp]

/-- Finitely many frozen keys can be frozen at a common time. -/
theorem frozen_finset (s : Finset (Key D)) (h : ∀ k ∈ s, ∃ T₁, T ≤ T₁ ∧ Frozen K k T₁) :
    ∃ T₀, T ≤ T₀ ∧ ∀ k ∈ s, Frozen K k T₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨T, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T₀, h0, hs⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    obtain ⟨T₁, h1, ha⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨max T₀ T₁, le_max_of_le_left h0, fun k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ha.mono_time (le_max_right _ _)
    · exact (hs k hk).mono_time (le_max_left _ _)

open Classical in
/-- The finite set of keys that can occur from time `T` on. -/
noncomputable def keysFrom (K : ℕ → V → Key D) (I : ℕ → V → D) (α T : ℕ) : Finset (Key D) :=
  Finset.univ.image (K T) ∪
    ((Finset.univ.image (fun p => (K T p).M) ∪ Finset.univ.image (I T)) ×ˢ Finset.range (α + 1)).image
      fun x => ⟨x.1, x.2⟩

omit hR hI in
theorem M_mem_of_mem_keysFrom {k : Key D} (hk : k ∈ keysFrom K I α T) :
    k.M ∈ Finset.univ.image (fun p => (K T p).M) ∪ Finset.univ.image (I T) := by
  classical
  simp only [keysFrom, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_product, Finset.mem_range] at hk ⊢
  rcases hk with ⟨p, rfl⟩ | ⟨⟨a, b⟩, ⟨ha, -⟩, rfl⟩
  · exact Or.inl ⟨p, rfl⟩
  · exact ha

theorem mem_keysFrom : ∀ t, T ≤ t → ∀ p, K t p ∈ keysFrom K I α T := by
  classical
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro p; simp [keysFrom]
  | succ t hle ih =>
    intro p
    by_cases hp : p ∈ A t
    · rw [hR.move t p hp]
      have hmem := bestKey_mem (G := G) (α := α) (I := I t) (K := K t) (p := p)
      have hd := bestKey_d_le (G := G) (α := α) (I := I t) (K := K t) (p := p)
      set b := bestKey G α (I t) (K t) p
      have hM : b.M ∈ Finset.univ.image (fun p => (K T p).M) ∪ Finset.univ.image (I T) := by
        rcases mem_keySet.mp hmem with hb | ⟨q, -, -, hb⟩
        · rw [hb, hI t hle]; simp
        · rw [hb, Key.succ_M]; exact M_mem_of_mem_keysFrom (ih q)
      simp only [keysFrom, Finset.mem_union, Finset.mem_image, Finset.mem_product,
        Finset.mem_range]
      exact Or.inr ⟨⟨b.M, b.d⟩, ⟨by simpa using hM, by omega⟩, rfl⟩
    · rw [hR.stay t p hp]; exact ih p

theorem frozen_all : ∀ k ∈ keysFrom K I α T, ∃ T₁, T ≤ T₁ ∧ Frozen K k T₁ := by
  classical
  set F := keysFrom K I α T
  suffices h : ∀ n, ∀ k ∈ F, (F.filter (· < k)).card = n → ∃ T₁, T ≤ T₁ ∧ Frozen K k T₁ from
    fun k hk => h _ k hk rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hn
    obtain ⟨T₀, hT₀, hfr⟩ := frozen_finset hR hI (F.filter (· < k)) fun k' hk' => by
      have hk'F := (Finset.mem_filter.mp hk').1
      have hk'k := (Finset.mem_filter.mp hk').2
      refine ih _ ?_ k' hk'F rfl
      rw [← hn]
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun x hx => ?_, fun heq => ?_⟩
      · simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hk'k⟩
      · have : k' ∈ F.filter (· < k) := hk'
        rw [← heq] at this
        exact lt_irrefl _ (Finset.mem_filter.mp this).2
    have hFB : FrozenBelow K k T₀ := by
      intro t ht p hp
      rcases hp with hp | hp
      · have hmem : K t p ∈ F.filter (· < k) :=
          Finset.mem_filter.mpr ⟨mem_keysFrom hR hI t (by omega) p, hp⟩
        exact hfr _ hmem t ht p (Or.inl le_rfl)
      · have hmem : K T₀ p ∈ F.filter (· < k) :=
          Finset.mem_filter.mpr ⟨mem_keysFrom hR hI T₀ hT₀ p, hp⟩
        exact hfr _ hmem t ht p (Or.inr le_rfl)
    obtain ⟨T₁, h01, hT₁⟩ := frozen_of_frozenBelow hR hI hT₀ hFB
    exact ⟨T₁, by omega, hT₁⟩

/-- **Lemma 4 (generalised).** A run of C-MAI whose inputs are constant from time `T` on is
eventually constant, whatever the (unfair) choice of activated processes. -/
theorem Run.eventually_const : ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → K t = K T' := by
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨T, le_rfl, fun t _ => funext fun p => isEmptyElim p⟩
  · set F := keysFrom K I α T
    have hne : F.Nonempty := ⟨_, mem_keysFrom hR hI T le_rfl (Classical.arbitrary V)⟩
    obtain ⟨T₁, hT₁, hfr⟩ := frozen_all hR hI _ (F.max'_mem hne)
    refine ⟨T₁, hT₁, fun t ht => funext fun p => hfr t ht p (Or.inl ?_)⟩
    exact F.le_max' _ (mem_keysFrom hR hI t (by omega) p)

end CMAI

end Papers.PODC2024.SSLeaderElectionDirected
