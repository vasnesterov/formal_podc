import Papers.PODC2011.RulesOfThumb.Theorem41

/-!
# Theorem 4.1 for non-stationary 1-recall reaction functions (Theorem F.14)

For `1`-recall (but possibly non-stationary) self-independent reaction functions, the limit `c`
of a fair dynamics in a *convergent* system is eventually absorbing
(`absorbingAfter_of_oneRecall`). Otherwise some node `i` deviates from `c` (when it sees `c`) at
infinitely many time steps; following the converging dynamics, letting `i` deviate at such a step
and then activating `i` alone until a step at which it reproduces `c i` (such steps exist, because
the converging dynamics activates `i` infinitely often), and repeating, gives a fair dynamics
that changes infinitely often.

With `not_convergent_of_absorbing` this proves Theorem 4.1 for non-stationary `1`-recall
reaction functions, without the finiteness of the action spaces assumed in Theorem F.14.
-/

namespace Podc.RulesOfThumb

open Filter

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

namespace System

variable {F : System A}

lemma HasRecall.eq_of_cur_eq {i : ι} (hrec : F.HasRecall i 1) {g g' : Hist A}
    (ht : g.time = g'.time) (hc : g.cur = g'.cur) : F.f i (g.time + 1) g = F.f i (g.time + 1) g' :=
  hrec g g' ht g.time_pos (by simp [Hist.toList, hc])

lemma othersEq_setCur (i : ι) (g : Hist A) (c : Profile A) (hc : ∀ l, l ≠ i → g.cur l = c l) :
    OthersEq i g ⟨c, g.past⟩ :=
  List.Forall₂.cons hc (List.forall₂_same.mpr fun _ _ _ _ => rfl)

variable [Fintype ι]

/-- In a convergent system with self-independent `1`-recall reaction functions, the limit of a
fair dynamics is eventually absorbing. -/
theorem absorbingAfter_of_oneRecall (hrec : ∀ i, F.HasRecall i 1) (hsi : F.SelfIndependent)
    (hconv : F.Convergent) {h₀ : Hist A} {σ : ℕ → Finset ι} {c : Profile A} (hσ : IsSchedule σ)
    (hf : Fair σ) (hc : F.ConvergesTo h₀ σ c) : ∃ T, F.AbsorbingAfter 1 c T := by
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := (hσ 0)
    exact ⟨i⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hc
  set B := h₀.time + N₀
  -- nodes activated by the converging dynamics reproduce `c`
  have hF1 : ∀ (g : Hist A) j, B ≤ g.time → g.cur = c → j ∈ σ (g.time + 1) →
      F.f j (g.time + 1) g = c j := by
    intro g j hB hg hj
    set m := g.time - h₀.time
    have htm : (F.run h₀ σ m).time = g.time := by simp [m]; omega
    have h1 : (F.run h₀ σ (m + 1)).cur j = c j := by rw [hN₀ _ (by omega)]
    rw [run_succ, step_cur_of_mem _ (htm ▸ hj), htm] at h1
    rw [← h1]
    exact (hrec j).eq_of_cur_eq htm.symm (by rw [hg, hN₀ _ (by omega)])
  -- `dev j t`: node `j`, seeing `c` at time `t`, deviates at time step `t + 1`
  let dev : ι → ℕ → Prop := fun j t => ∃ g : Hist A, g.time = t ∧ g.cur = c ∧ F.f j (t + 1) g ≠ c j
  have dev_iff : ∀ j (g : Hist A), g.cur = c → (dev j g.time ↔ F.f j (g.time + 1) g ≠ c j) := by
    intro j g hg
    refine ⟨fun ⟨g', ht, hc', hne⟩ => ?_, fun hne => ⟨g, rfl, hg, hne⟩⟩
    rw [(hrec j).eq_of_cur_eq ht.symm (by rw [hg, hc'])]
    exact ht ▸ hne
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ : ∃ i, ∃ᶠ t in atTop, dev i t := by
    by_contra hall
    push Not at hall
    obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_all.mpr hall)
    refine hne T fun j g hTg _ htake => ?_
    have hg : g.cur = c := by simpa [Hist.toList] using htake
    by_contra hfj
    exact hT g.time hTg j ((dev_iff j g hg).mpr hfj)
  have hnotdev : ∃ᶠ t in atTop, ¬ dev i t := by
    rw [frequently_atTop]
    intro N
    obtain ⟨s, hs, hge⟩ := ((hf i).and_eventually (eventually_gt_atTop (N + B))).exists
    refine ⟨s - 1, by omega, fun ⟨g, hgt, hgc, hne'⟩ => hne' ?_⟩
    have := hF1 g i (by omega) hgc (by rw [hgt, show s - 1 + 1 = s by omega]; exact hs)
    rwa [hgt] at this
  let S : Hist A → Prop := fun g => g.cur = c ∧ B ≤ g.time
  let X : Hist A → (ℕ → Finset ι) → ℕ → Prop := fun g τ m =>
    ∃ j < m, (F.run g τ j).cur ≠ (F.run g τ (j + 1)).cur
  have seg : ∀ g, S g → ∀ i', ∃ τ m, IsSegment g τ m ∧
      (∃ t, g.time < t ∧ t ≤ g.time + m ∧ i' ∈ τ t) ∧ S (F.run g τ m) ∧ X g τ m := by
    rintro g ⟨hgc, hgB⟩ i'
    obtain ⟨t₁, hi't₁, ht₁⟩ := ((hf i').and_eventually (eventually_gt_atTop g.time)).exists
    obtain ⟨d, hdev, hd⟩ := (hi.and_eventually (eventually_ge_atTop t₁)).exists
    obtain ⟨e, hnd, he⟩ := (hnotdev.and_eventually (eventually_gt_atTop d)).exists
    let τ : ℕ → Finset ι := fun s => if s ≤ d then σ s else if s = d + 1 then insert i (σ s)
      else {i}
    set m := e + 1 - g.time
    have hA : ∀ j, g.time + j ≤ d → (F.run g τ j).cur = c := by
      intro j hj
      induction j with
      | zero => exact hgc
      | succ j ih =>
        have ih := ih (by omega)
        have hτ : τ ((F.run g τ j).time + 1) = σ ((F.run g τ j).time + 1) := by
          simp only [τ, run_time]; rw [if_pos (by omega)]
        rw [run_succ, hτ]
        funext l
        by_cases hl : l ∈ σ ((F.run g τ j).time + 1)
        · rw [step_cur_of_mem _ hl]
          exact hF1 _ l (by simp; omega) ih hl
        · rw [step_cur_of_not_mem _ hl, ih]
    set jd := d - g.time
    have hjd : (F.run g τ jd).cur = c := hA jd (by omega)
    have hjdt : (F.run g τ jd).time = d := by simp [jd]; omega
    have hB1 : ∀ l, l ≠ i → (F.run g τ (jd + 1)).cur l = c l := by
      intro l hl
      have hτ : τ ((F.run g τ jd).time + 1) = insert i (σ (d + 1)) := by
        simp only [τ, hjdt]; simp
      rw [run_succ, hτ]
      by_cases hl' : l ∈ σ (d + 1)
      · rw [step_cur_of_mem _ (Finset.mem_insert_of_mem hl')]
        exact hF1 _ l (by omega) hjd (by rw [hjdt]; exact hl')
      · rw [step_cur_of_not_mem _ (by simp [hl, hl']), hjd]
    have hB2 : (F.run g τ (jd + 1)).cur i ≠ c i := by
      have hτ : τ ((F.run g τ jd).time + 1) = insert i (σ (d + 1)) := by
        simp only [τ, hjdt]; simp
      rw [run_succ, hτ, step_cur_of_mem _ (Finset.mem_insert_self _ _)]
      exact (dev_iff i _ hjd).mp (hjdt ▸ hdev)
    have hC : ∀ j, jd + 1 ≤ j → g.time + j ≤ e + 1 → ∀ l, l ≠ i → (F.run g τ j).cur l = c l := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact fun _ => hB1
      | succ j hj ih =>
        intro hje l hl
        have hτ : τ ((F.run g τ j).time + 1) = {i} := by
          simp only [τ, run_time]; rw [if_neg (by omega), if_neg (by omega)]
        rw [run_succ, hτ, step_cur_of_not_mem _ (by simpa using hl)]
        exact ih (by omega) l hl
    have hD : (F.run g τ m).cur = c := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have htm' : (F.run g τ m').time = e := by simp; omega
      have hτ : τ ((F.run g τ m').time + 1) = {i} := by
        simp only [τ, htm']; rw [if_neg (by omega), if_neg (by omega)]
      have hC' := hC m' (by omega) (by omega)
      rw [hm', run_succ, hτ]
      funext l
      by_cases hl : l = i
      · subst hl
        rw [step_cur_of_mem _ (Finset.mem_singleton_self _), hsi _ _ _ (othersEq_setCur _ _ c hC')]
        by_contra hne'
        exact hnd ((htm' ▸ (dev_iff l ⟨c, (F.run g τ m').past⟩ rfl).mpr hne' : dev l e))
      · rw [step_cur_of_not_mem _ (by simpa using hl)]
        exact hC' l hl
    refine ⟨τ, m, fun s h1 h2 => ?_, ⟨t₁, ht₁, by omega, ?_⟩, ⟨hD, by simp; omega⟩,
      ⟨jd, by omega, fun heq => hB2 (by rw [← heq, hjd])⟩⟩
    · simp only [τ]
      split_ifs
      · exact hσ s
      · exact Finset.insert_nonempty _ _
      · exact Finset.singleton_nonempty _
    · simp only [τ]; rw [if_pos hd]; exact hi't₁
  -- the starting point: the converging dynamics at time `B`
  have h₁S : S (F.run h₀ σ N₀) := ⟨hN₀ _ le_rfl, by simp [B]⟩
  obtain ⟨σ', hσ', hf', hinf⟩ := exists_fair_of_segments (F := F) S X h₁S seg
  obtain ⟨a, ha⟩ := hconv _ σ' hσ' hf'
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  obtain ⟨n, hn, τ, m, -, ⟨j, hjm, hj⟩, hseg⟩ := hinf N
  apply hj
  rw [← hseg j hjm.le, ← hseg (j + 1) hjm, ← add_assoc, hN _ (by omega), hN _ (by omega)]

/-- **Theorem 4.1 for non-stationary reaction functions with `1`-recall** (Theorem F.14, without
its assumption that the action spaces are finite): if every reaction function is deterministic,
self-independent and has `1`-recall, then two distinct stable states imply that the system is
not convergent. -/
theorem theorem_4_1_oneRecall (hrec : ∀ i, F.HasRecall i 1) (hsi : F.SelfIndependent)
    (h2 : ∃ a b, a ≠ b ∧ F.IsStableState a ∧ F.IsStableState b) : ¬ F.Convergent := by
  obtain ⟨a, b, hab, ha, hb⟩ := h2
  exact not_convergent_of_absorbing le_rfl hrec hsi
    (fun hconv _ _ _ hσ hf hc => absorbingAfter_of_oneRecall hrec hsi hconv hσ hf hc) hab ha hb

end System

end Podc.RulesOfThumb
