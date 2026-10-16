import Papers.PODC2024.SSLeaderElectionDirected.Correctness

/-!
# Stabilization time of C-MAI (Lemmas 5–10, Theorem 2)

All statements are about a `Run` of C-MAI whose inputs are constant (`= I T`) from time `T` on, and
a sequence of times `r` with `r 0 = T` such that every interval `[r i, r (i+1)]` contains a complete
*round* of the run (`RunRound`): every process enabled at `r i` executes `ReplaceKey` or becomes
disabled during the interval.

* `fake_d_moved` (Lemmas 5 and 7), `enabled_of_bad` (Lemma 6).
* `noFake_within` (Lemma 9): after `α + 1` rounds there is no fake value.
* `target_within_of_noFake` (Lemma 10): from a configuration without fake values, all keys are
  correct (hence the configuration is terminal) after `MAD + 1` rounds.
* `Run.target_within` (Theorem 2): all keys are correct after `α + MAD + 2` rounds.
-/

set_option linter.unusedSectionVars false

open Podc.AtomicState

namespace Papers.PODC2024.SSLeaderElectionDirected

namespace CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {D : Type*} [LinearOrder D]
  {α : ℕ} {I : ℕ → V → D} {K : ℕ → V → Key D} {A : ℕ → Set V}

variable (G α) in
/-- Process `p` is enabled at time `t` of a run. -/
def RunEnabled (I : ℕ → V → D) (K : ℕ → V → Key D) (t : ℕ) (p : V) : Prop :=
  bestKey G α (I t) (K t) p ≠ K t p

variable (G α) in
/-- `[s, s']` contains a complete round of the run: every process enabled at `s` executes
`ReplaceKey` or becomes disabled during `[s, s']`. -/
def RunRound (I : ℕ → V → D) (K : ℕ → V → Key D) (A : ℕ → Set V) (s s' : ℕ) : Prop :=
  ∀ p, RunEnabled G α I K s p → ∃ u, s ≤ u ∧ u < s' ∧ (p ∈ A u ∨ ¬ RunEnabled G α I K (u + 1) p)

variable (G) in
/-- `K q` holds a fake value for `q`: its `M` is not the input of any ancestor of `q`. -/
def Fake (I₀ : V → D) (K : V → Key D) (q : V) : Prop := ∀ q', Anc G q' q → I₀ q' ≠ (K q).M

theorem minI_le_of_not_fake {I₀ : V → D} {K₀ : V → Key D} {q : V} (h : ¬ Fake G I₀ K₀ q) :
    minI G I₀ q ≤ (K₀ q).M := by
  simp only [Fake, not_forall, not_not] at h
  obtain ⟨q', hq', heq⟩ := h
  exact heq ▸ minI_le hq'

variable (hR : Run G α I K A) {T : ℕ} (hI : ∀ t, T ≤ t → I t = I T)
include hR hI

/-- Lemmas 5 and 7: if all fake keys at time `t` have distance `≥ j`, a process that moves at `t`
and holds a fake key at `t + 1` has distance `≥ j + 1`. -/
theorem fake_d_moved {j t : ℕ} (ht : T ≤ t) (h : ∀ q, Fake G (I T) (K t) q → j ≤ (K t q).d)
    {q : V} (hq : q ∈ A t) (hf : Fake G (I T) (K (t + 1)) q) : j + 1 ≤ (K (t + 1) q).d := by
  have hm := hR.move t q hq
  have hmem := bestKey_mem (G := G) (α := α) (I := I t) (K := K t) (p := q)
  rw [← hm, hI t ht] at hmem
  rcases mem_keySet.mp hmem with hk | ⟨q', hq', -, hk⟩
  · exact absurd (by rw [hk]) (hf q (Anc.refl q))
  · have hf' : Fake G (I T) (K t) q' := fun q'' h'' => by
      have := hf q'' (h''.tail hq'); rwa [hk, Key.succ_M] at this
    have := h q' hf'
    rw [hk, Key.succ_d]; omega

/-- Lemma 5: the minimum distance of fake keys does not decrease. -/
theorem fake_d_mono {j t : ℕ} (ht : T ≤ t) (h : ∀ q, Fake G (I T) (K t) q → j ≤ (K t q).d) :
    ∀ q, Fake G (I T) (K (t + 1)) q → j ≤ (K (t + 1) q).d := by
  intro q hf
  by_cases hq : q ∈ A t
  · have := fake_d_moved hR hI ht h hq hf; omega
  · have e := hR.stay t q hq
    have hf' : Fake G (I T) (K t) q := fun q' h' => by have := hf q' h'; rwa [e] at this
    rw [e]; exact h q hf'

omit hR in
/-- Lemma 6: a process holding a fake key of minimum distance is enabled. -/
theorem enabled_of_bad {j t : ℕ} (ht : T ≤ t) (h : ∀ q, Fake G (I T) (K t) q → j ≤ (K t q).d)
    {q : V} (hf : Fake G (I T) (K t) q) (hd : (K t q).d = j) : RunEnabled G α I K t q := by
  intro heq
  have hmem := bestKey_mem (G := G) (α := α) (I := I t) (K := K t) (p := q)
  rw [heq, hI t ht] at hmem
  rcases mem_keySet.mp hmem with hk | ⟨q', hq', -, hk⟩
  · exact hf q (Anc.refl q) (by rw [hk])
  · have hf' : Fake G (I T) (K t) q' := fun q'' h'' => by
      have := hf q'' (h''.tail hq'); rwa [hk, Key.succ_M] at this
    have := h q' hf'
    have hd' : (K t q).d = (K t q').d + 1 := by rw [hk, Key.succ_d]
    omega

/-- **Lemma 9.** After `j` rounds, every fake key has distance `≥ j`. -/
theorem fake_d_within {r : ℕ → ℕ} (hr0 : r 0 = T)
    (hr : ∀ i, r i ≤ r (i + 1) ∧ RunRound G α I K A (r i) (r (i + 1))) :
    ∀ j t, r j ≤ t → ∀ q, Fake G (I T) (K t) q → j ≤ (K t q).d := by
  have hrT : ∀ i, T ≤ r i := by
    intro i; induction i with
    | zero => omega
    | succ i ih => exact le_trans ih (hr i).1
  -- monotonicity in time
  have hmono : ∀ j s, T ≤ s → (∀ q, Fake G (I T) (K s) q → j ≤ (K s q).d) →
      ∀ t, s ≤ t → ∀ q, Fake G (I T) (K t) q → j ≤ (K t q).d := by
    intro j s hs hP t ht
    induction t, ht using Nat.le_induction with
    | base => exact hP
    | succ t hst ih => exact fake_d_mono hR hI (by omega) ih
  intro j
  induction j with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ j ih =>
    apply hmono (j + 1) _ (hrT _)
    intro q hf
    have hj := ih (r (j + 1)) (hr j).1 q hf
    by_contra hlt
    have hd : (K (r (j + 1)) q).d = j := by omega
    -- `Bad t` : `q` holds a fake key of distance `j` at time `t`
    let Bad : ℕ → Prop := fun t => Fake G (I T) (K t) q ∧ (K t q).d = j
    have hstep : ∀ t, r j ≤ t → ¬ Bad t → ¬ Bad (t + 1) := by
      intro t ht hb hb1
      by_cases hq : q ∈ A t
      · have := fake_d_moved hR hI (le_trans (hrT j) ht) (ih t ht) hq hb1.1; omega
      · have e := hR.stay t q hq
        apply hb
        refine ⟨fun q' h' => ?_, by rw [← e]; exact hb1.2⟩
        have := hb1.1 q' h'; rwa [e] at this
    have hbad : ∀ t, r j ≤ t → t ≤ r (j + 1) → Bad t := by
      intro t ht ht'
      by_contra hb
      have : ∀ u, t ≤ u → ¬ Bad u := by
        intro u hu
        induction u, hu using Nat.le_induction with
        | base => exact hb
        | succ u htu ihu => exact hstep u (by omega) ihu
      exact this _ ht' ⟨hf, hd⟩
    have hen := enabled_of_bad (α := α) hI (hrT j) (ih _ le_rfl) (hbad _ le_rfl (hr j).1).1
      (hbad _ le_rfl (hr j).1).2
    obtain ⟨u, hu1, hu2, hu3⟩ := (hr j).2 q hen
    have hb1 := hbad (u + 1) (by omega) (by omega)
    rcases hu3 with hq | hne
    · have := fake_d_moved hR hI (le_trans (hrT j) hu1) (ih u hu1) hq hb1.1; omega
    · exact hne (enabled_of_bad (α := α) hI (by have := hrT j; omega) (ih (u + 1) (by omega))
        hb1.1 hb1.2)

/-- **Lemma 9.** After `α + 1` rounds there is no fake value, forever. -/
theorem noFake_within (hbound : ∀ t, T ≤ t → ∀ p, (K t p).d ≤ α) {r : ℕ → ℕ} (hr0 : r 0 = T)
    (hr : ∀ i, r i ≤ r (i + 1) ∧ RunRound G α I K A (r i) (r (i + 1))) :
    ∀ t, r (α + 1) ≤ t → ∀ q, ¬ Fake G (I T) (K t) q := by
  have hrT : ∀ i, T ≤ r i := by
    intro i; induction i with
    | zero => omega
    | succ i ih => exact le_trans ih (hr i).1
  intro t ht q hf
  have h1 := fake_d_within hR hI hr0 hr (α + 1) t ht q hf
  have h2 := hbound t (le_trans (hrT _) ht) q
  omega

/-- If `bestKey` satisfies `Q` throughout `[s, ∞)`, then after a round starting at `s` the key of
`p` satisfies `Q` forever. -/
theorem settle {Q : Key D → Prop} {p : V} {s s' : ℕ} (hss : s ≤ s')
    (hQ : ∀ t, s ≤ t → Q (bestKey G α (I t) (K t) p)) (hround : RunRound G α I K A s s') :
    ∀ t, s' ≤ t → Q (K t p) := by
  have hex : ∃ w, s ≤ w ∧ w ≤ s' ∧ Q (K w p) := by
    by_cases hen : RunEnabled G α I K s p
    · obtain ⟨u, hu1, hu2, hu3⟩ := hround p hen
      refine ⟨u + 1, by omega, by omega, ?_⟩
      rcases hu3 with hp | hne
      · rw [hR.move u p hp]; exact hQ u hu1
      · simp only [RunEnabled, ne_eq, not_not] at hne
        rw [← hne]; exact hQ (u + 1) (by omega)
    · simp only [RunEnabled, ne_eq, not_not] at hen
      exact ⟨s, le_rfl, hss, hen ▸ hQ s le_rfl⟩
  obtain ⟨w, hw1, hw2, hw3⟩ := hex
  have : ∀ t, w ≤ t → Q (K t p) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hw3
    | succ t hwt ih =>
      by_cases hp : p ∈ A t
      · rw [hR.move t p hp]; exact hQ t (by omega)
      · rw [hR.stay t p hp]; exact ih
  exact fun t ht => this t (by omega)

omit hR in
/-- Lower bound on the candidate keys of `p` once fake values are gone and the induction hypothesis
of Lemma 10 holds for `i`. -/
theorem keySet_lower {i t : ℕ} (ht : T ≤ t) (hnf : ∀ q, ¬ Fake G (I T) (K t) q)
    (hc1 : ∀ q, mind G (I T) q < i → K t q = target G (I T) q)
    (hc2 : ∀ q, i ≤ mind G (I T) q → (⟨minI G (I T) q, i⟩ : Key D) ≤ K t q) (p : V) :
    ∀ k ∈ keySet G α (I t) (K t) p,
      (⟨minI G (I T) p, min (mind G (I T) p) (i + 1)⟩ : Key D) ≤ k := by
  intro k hk
  rw [hI t ht] at hk
  rcases mem_keySet.mp hk with rfl | ⟨q, hq, -, rfl⟩
  · by_cases h0 : mind G (I T) p = 0
    · have hm : minI G (I T) p = I T p := ((mind_eq_zero_iff (G := G)).mp h0).symm
      rw [h0, hm]; simp
    · exact (Key.lt_of_M_lt (minI_lt_of_mind_pos (by omega))).le
  · have hM : minI G (I T) q ≤ (K t q).M := minI_le_of_not_fake (hnf q)
    have hpq : minI G (I T) p ≤ minI G (I T) q := minI_mono (Anc.of_adj hq)
    rcases lt_or_eq_of_le (hpq.trans hM) with hlt | heq
    · exact (Key.lt_of_M_lt (by simpa using hlt)).le
    · have hqp : minI G (I T) q = minI G (I T) p := le_antisymm (heq ▸ hM) hpq
      have hP1 : mind G (I T) p ≤ mind G (I T) q + 1 := by
        rcases Key.le_iff.mp (target_le_succ_target (I := I T) hq) with h | h
        · simp [target, hqp] at h
        · simpa [target] using h.2
      by_cases hqi : mind G (I T) q < i
      · rw [hc1 q hqi]
        refine Key.le_iff.mpr (Or.inr ⟨by simp [target, hqp], ?_⟩)
        simp only [target, Key.succ_d]; omega
      · have h2 := hc2 q (by omega)
        refine Key.le_iff.mpr (Or.inr ⟨by simp [heq], ?_⟩)
        rcases Key.le_iff.mp h2 with h | h
        · exact absurd (hqp ▸ heq ▸ h) (lt_irrefl _)
        · have h22 := h.2
          dsimp only at h22
          simp only [Key.succ_d]; omega

/-- **Lemma 10.** Starting from a time `r 0 = s₀` after which there is no fake value, after `i`
rounds every process `p` with `Mind(p) < i` has its correct key and every other process has a key
`⪰ (MinI(p), i)`; both forever. -/
theorem claim_within (hα : MADLe G α) {s₀ : ℕ} (hs₀ : T ≤ s₀)
    (hnf : ∀ t, s₀ ≤ t → ∀ q, ¬ Fake G (I T) (K t) q) {r : ℕ → ℕ} (hr0 : r 0 = s₀)
    (hr : ∀ i, r i ≤ r (i + 1) ∧ RunRound G α I K A (r i) (r (i + 1))) :
    ∀ i t, r i ≤ t → ∀ p, (mind G (I T) p < i → K t p = target G (I T) p) ∧
      (i ≤ mind G (I T) p → (⟨minI G (I T) p, i⟩ : Key D) ≤ K t p) := by
  have hrs : ∀ i, s₀ ≤ r i := by
    intro i; induction i with
    | zero => omega
    | succ i ih => exact le_trans ih (hr i).1
  intro i
  induction i with
  | zero =>
    intro t ht p
    refine ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => ?_⟩
    have hM := minI_le_of_not_fake (hnf t (by rw [← hr0]; exact ht) p)
    rcases lt_or_eq_of_le hM with h | h
    · exact (Key.lt_of_M_lt h).le
    · exact Key.le_iff.mpr (Or.inr ⟨h, Nat.zero_le _⟩)
  | succ i ih =>
    have hlow : ∀ t, r i ≤ t → ∀ p, ∀ k ∈ keySet G α (I t) (K t) p,
        (⟨minI G (I T) p, min (mind G (I T) p) (i + 1)⟩ : Key D) ≤ k := fun t ht =>
      keySet_lower hI (by have := hrs i; omega) (hnf t (by have := hrs i; omega))
        (fun q hq => (ih t ht q).1 hq) (fun q hq => (ih t ht q).2 hq)
    intro t ht p
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · by_cases hpi : mind G (I T) p < i
      · exact (ih t (le_trans (hr i).1 ht) p).1 hpi
      · have hpi' : mind G (I T) p = i := by omega
        refine settle hR hI (hr i).1 (Q := fun k => k = target G (I T) p) (fun u hu => ?_) (hr i).2
          t ht
        apply le_antisymm
        · apply bestKey_le
          rw [hI u (by have := hrs i; omega)]
          rcases hm : mind G (I T) p with _ | m
          · have hmI : minI G (I T) p = I T p := ((mind_eq_zero_iff (G := G)).mp hm).symm
            have : target G (I T) p = ⟨I T p, 0⟩ := Key.ext hmI hm
            rw [this]; exact selfKey_mem_keySet
          · obtain ⟨q, hq, hmin, hmq⟩ := exists_pred_of_mind hm
            have hKq : K u q = target G (I T) q := (ih u hu q).1 (by omega)
            have heq : target G (I T) p = (K u q).succ := by
              rw [hKq]; exact Key.ext hmin.symm (by simp [target, hmq, hm])
            have hle := mind_le_of_madLe (I := I T) hα p
            rw [heq]
            exact succ_mem_keySet hq (by rw [hKq]; simp only [target]; omega)
        · have := le_bestKey (hlow u hu p)
          simpa [hpi', target] using this
    · refine settle hR hI (hr i).1 (Q := fun k => (⟨minI G (I T) p, i + 1⟩ : Key D) ≤ k)
        (fun u hu => ?_) (hr i).2 t ht
      have := le_bestKey (hlow u hu p)
      simpa [show min (mind G (I T) p) (i + 1) = i + 1 by omega] using this

/-- **Theorem 2.** If `MAD ≤ m ≤ α`, then after `α + m + 2` rounds every key is correct (and stays
so); in particular the run is terminal from then on (`bestKey_target`). -/
theorem Run.target_within (hbound : ∀ t, T ≤ t → ∀ p, (K t p).d ≤ α) {m : ℕ} (hm : MADLe G m)
    (hmα : m ≤ α) {r : ℕ → ℕ} (hr0 : r 0 = T)
    (hr : ∀ i, r i ≤ r (i + 1) ∧ RunRound G α I K A (r i) (r (i + 1))) :
    ∀ t, r (α + m + 2) ≤ t → ∀ p, K t p = target G (I T) p := by
  have hrT : ∀ i, T ≤ r i := by
    intro i; induction i with
    | zero => omega
    | succ i ih => exact le_trans ih (hr i).1
  have hnf := noFake_within hR hI hbound hr0 hr
  have hcl := claim_within hR hI (hm.mono hmα) (hrT (α + 1)) hnf (r := fun i => r (α + 1 + i))
    (by simp) (fun i => hr (α + 1 + i))
  intro t ht p
  exact (hcl (m + 1) t (by rwa [show α + 1 + (m + 1) = α + m + 2 by omega]) p).1
    (Nat.lt_succ_of_le (mind_le_of_madLe hm p))

end CMAI

namespace CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {D : Type*} [LinearOrder D] {α : ℕ} {I : V → D}

/-- **Theorem 2** for the algorithm C-MAI(D, ≺, I) under the distributed unfair daemon: if
`MAD ≤ m ≤ α`, the execution is terminal, with all keys correct, after at most `α + m + 2` rounds
(for any round boundaries `r`, in particular the paper's). -/
theorem theorem2 {e : ℕ → V → CState D α} {S : ℕ → Set V} (h : IsRun (next G α I) e S) {m : ℕ}
    (hm : MADLe G m) (hmα : m ≤ α) {r : ℕ → ℕ} (hr : RoundBounds (next G α I) e S r) :
    ∀ t, r (α + m + 2) ≤ t → Terminal (next G α I) (e t) ∧ ∀ p, (e t p).1 = target G I p := by
  have hR := run_of_isRun h
  have key := hR.target_within (T := 0) (fun _ _ => rfl) (fun t _ p => (e t p).2) hm hmα hr.1
    (fun i => ⟨(hr.2 i).1, fun p hp => by
      obtain ⟨u, h1, h2, h3⟩ := (hr.2 i).2 p (enabled_iff.mpr hp)
      exact ⟨u, h1, h2, h3.imp_right fun h' h'' => h' (enabled_iff.mpr h'')⟩⟩)
  intro t ht
  have hK : (fun q => (e t q).1) = target G I := funext (key t ht)
  refine ⟨terminal_iff.mpr fun p => ?_, key t ht⟩
  rw [hK, key t ht p]
  exact bestKey_target (hm.mono hmα) p

end CMAI

end Papers.PODC2024.SSLeaderElectionDirected
