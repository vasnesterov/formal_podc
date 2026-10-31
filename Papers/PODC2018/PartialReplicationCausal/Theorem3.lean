import Papers.PODC2018.PartialReplicationCausal.Preservation

/-!
# Theorem 3: the algorithm of Section 3.2 achieves replica-centric causal consistency

* `lemma_3`: Lemma 3 of the paper.
* `lemma_5`: Lemma 5 of the paper (safety at the moment an update is applied).
* `theorem_3_safety`: the safety half of Definition 5 holds in every reachable state.
* `theorem_3_liveness`: the liveness half of Definition 5 holds in every fair execution.
* `eventually_applied`: consequently, in a fair execution every update is eventually applied at
  every replica storing its register.
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*} {X : ι → Set Reg} {s : State ι Reg}

/-- **Lemma 3** of the paper. Let `u` be an update from replica `j` to replica `i` with timestamp
`T`. If `τ_i[e_ji] ≥ T[e_ji]`, then `u` has already been applied at `i`. -/
theorem lemma_3 (hs : Reachable X s) {i : ι} {u : ℕ} (hu : u < s.n) (hji : (s.log u).src ≠ i)
    (hx : (s.log u).reg ∈ X i)
    (hle : (s.log u).ts (s.log u).src i ≤ s.τ i (s.log u).src i) : u ∈ s.app i := by
  have h := Inv.of_reachable hs
  have hadj : Adj X (s.log u).src i := adj_of_mem hji (h.reg_src hu) hx
  rw [h.count i _ hji hadj u hu rfl hx, ← h.ts_own u hu i hadj hx]
  exact hle

/-- **Lemma 5** of the paper. When replica `i` applies an update `u` (the predicate of Step 4
holds), every update `a ↪ u` on a register of `X_i` has already been applied at `i`. -/
theorem lemma_5 (hs : Reachable X s) {i : ι} {u : ℕ} (hu : Enabled X s i u) {a : ℕ}
    (hax : (s.log a).reg ∈ X i) (hau : HB s a u) : a ∈ s.app i :=
  deps_applied (Inv.of_reachable hs) hu hax hau

/-- **Theorem 3 (safety).** In every reachable state of the algorithm of Section 3.2, the safety
property of replica-centric causal consistency (Definition 5) holds. -/
theorem theorem_3_safety (hs : Reachable X s) : Safe X s :=
  (Inv.of_reachable hs).safe

/-! ### Liveness -/

/-- An infinite execution of the algorithm (idle steps allowed). -/
structure Execution (X : ι → Set Reg) where
  /-- The state at time `t`. -/
  σ : ℕ → State ι Reg
  init : IsInit (σ 0)
  step : ∀ t, Step X (σ t) (σ (t + 1)) ∨ σ (t + 1) = σ t

/-- Weak fairness: an update that stays applicable at a replica (it has been received — channels
are reliable — and the predicate of Step 4 holds) is eventually applied. -/
def Execution.Fair (E : Execution X) : Prop :=
  ∀ i a t₀, (∀ t ≥ t₀, Enabled X (E.σ t) i a) → ∃ t, a ∈ (E.σ t).app i

lemma Step.mono {s s' : State ι Reg} (hs : Step X s s') :
    s.n ≤ s'.n ∧ (∀ c < s.n, s'.log c = s.log c) ∧ ∀ i, s.app i ⊆ s'.app i := by
  cases hs with
  | write i x hx =>
    refine ⟨by simp, fun c hc => write_log_of_lt hc, fun r => ?_⟩
    rw [write_app]; split_ifs with hr
    · subst hr; exact Set.subset_insert _ _
    · exact le_rfl
  | apply i a ha =>
    refine ⟨le_rfl, fun c _ => rfl, fun r => ?_⟩
    rw [apply_app]; split_ifs with hr
    · subst hr; exact Set.subset_insert _ _
    · exact le_rfl

namespace Execution

variable (E : Execution X)

lemma reachable (t : ℕ) : Reachable X (E.σ t) := by
  refine ⟨E.σ 0, E.init, ?_⟩
  induction t with
  | zero => exact .refl
  | succ t ih =>
    rcases E.step t with h | h
    · exact ih.tail h
    · rw [h]; exact ih

lemma mono {t t' : ℕ} (htt : t ≤ t') : (E.σ t).n ≤ (E.σ t').n ∧
    (∀ c < (E.σ t).n, (E.σ t').log c = (E.σ t).log c) ∧ ∀ i, (E.σ t).app i ⊆ (E.σ t').app i := by
  induction t', htt using Nat.le_induction with
  | base => exact ⟨le_rfl, fun _ _ => rfl, fun _ => le_rfl⟩
  | succ t' htt ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rcases E.step t' with hs | hs
    · obtain ⟨g1, g2, g3⟩ := Step.mono hs
      exact ⟨h1.trans g1, fun c hc => (g2 c (by omega)).trans (h2 c hc),
        fun i => (h3 i).trans (g3 i)⟩
    · rw [hs]; exact ⟨h1, h2, h3⟩

lemma hb_iff {t t' : ℕ} (htt : t ≤ t') {a b : ℕ} (hb : b < (E.σ t).n) :
    HB (E.σ t') a b ↔ HB (E.σ t) a b := by
  obtain ⟨h1, h2, -⟩ := E.mono htt
  exact ⟨fun hab => hb_back h2 (fun c hc d hd => (Inv.of_reachable (E.reachable t)).pre_lt_n hc hd)
    hab hb, hb_mono h1 h2⟩

end Execution

/-- If all dependencies of a received update on registers of `X_i` have been applied at `i`, the
predicate of Step 4 holds (no false dependencies). -/
theorem ready_of_deps (h : Inv X s) {i : ι} {u : ℕ} (hu : u < s.n) (hki : (s.log u).src ≠ i)
    (hux : (s.log u).reg ∈ X i) (hnot : u ∉ s.app i)
    (hdeps : ∀ a, (s.log a).reg ∈ X i → HB s a u → a ∈ s.app i) : Ready X s i (s.log u) := by
  have hadj : Adj X (s.log u).src i := adj_of_mem hki (h.reg_src hu) hux
  refine ⟨?_, ?_⟩
  · rw [h.ts_own u hu i hadj hux]
    have hnot' := mt (h.count i _ hki hadj u hu rfl hux).2 hnot
    have hsucc : cnt X s (s.log u).src i (u + 1) = cnt X s (s.log u).src i u + 1 := by
      rw [cnt_succ, ite_eq_left ⟨rfl, hux⟩]
    rcases Nat.eq_zero_or_pos (cnt X s (s.log u).src i u) with h0 | hpos
    · omega
    obtain ⟨c, hcu, hc1, hc2, hc3⟩ := exists_cnt_eq s _ i u _ hpos le_rfl
    have hcapp : c ∈ s.app i :=
      hdeps c hc2 (.single ⟨hu, h.pre_own u hu c hcu hc1⟩)
    have := (h.count i _ hki hadj c (hcu.trans hu) hc1 hc2).1 hcapp
    omega
  · intro j hji hjk _ hj
    rcases Nat.eq_zero_or_pos ((s.log u).ts j i) with h0 | hpos
    · omega
    obtain ⟨c, hc, hc1, hc2, hc3, hc4⟩ := h.ts_wit u hu j i hj hpos
    have hcu : HB s c u := by
      rcases hc4 with rfl | hc4
      · exact absurd hc1.symm hjk
      · exact hc4
    rw [← hc3]
    exact (h.count i j hji (adj_of_mem hji (hc1 ▸ h.reg_src hc) hc2) c hc hc1 hc2).1
      (hdeps c hc2 hcu)

/-- **Theorem 3 (liveness).** In a fair execution, an update `u` issued by replica `k` for a
register `x` is applied at each replica `i` with `x ∈ X_i` within finite time after all its
dependencies (the updates `a ↪ u` on registers of `X_i`) have been applied at `i`. -/
theorem theorem_3_liveness (E : Execution X) (hE : E.Fair) {t u : ℕ} (hu : u < (E.σ t).n)
    {i : ι} (hux : ((E.σ t).log u).reg ∈ X i)
    (hdeps : ∀ a, ((E.σ t).log a).reg ∈ X i → HB (E.σ t) a u → a ∈ (E.σ t).app i) :
    ∃ t' ≥ t, u ∈ (E.σ t').app i := by
  by_contra hcon
  push Not at hcon
  -- `u` is not applied by its issuer only if `i` is not the issuer
  have hki : ((E.σ t).log u).src ≠ i := by
    intro hki
    exact hcon t le_rfl (hki ▸ (Inv.of_reachable (E.reachable t)).own u hu)
  obtain ⟨t₁, ht₁⟩ := hE i u t (by
    intro t' ht'
    obtain ⟨h1, h2, h3⟩ := E.mono ht'
    have hinv := Inv.of_reachable (E.reachable t')
    have hlog : (E.σ t').log u = (E.σ t).log u := h2 u hu
    refine ⟨by omega, by rw [hlog]; exact hki, by rw [hlog]; exact hux, hcon t' ht', ?_⟩
    refine ready_of_deps hinv (by omega) (by rw [hlog]; exact hki) (by rw [hlog]; exact hux)
      (hcon t' ht') ?_
    intro a ha hau
    have hau' := (E.hb_iff ht' hu).1 hau
    have han : a < (E.σ t).n := ((Inv.of_reachable (E.reachable t)).hb_lt hau').trans hu
    rw [h2 a han] at ha
    exact h3 i (hdeps a ha hau'))
  rcases le_total t t₁ with h | h
  · exact hcon t₁ h ht₁
  · exact hcon t le_rfl ((E.mono h).2.2 i ht₁)

/-- In a fair execution every issued update is eventually applied at every replica that stores
its register (no update waits forever, in particular there are no false dependencies). -/
theorem eventually_applied (E : Execution X) (hE : E.Fair) {t u : ℕ} (hu : u < (E.σ t).n)
    {i : ι} (hux : ((E.σ t).log u).reg ∈ X i) : ∃ t', u ∈ (E.σ t').app i := by
  induction u using Nat.strong_induction_on generalizing i with
  | _ u ih =>
  -- every dependency is eventually applied; take a common time
  have hT : ∀ a < u, ∃ ta, ((E.σ t).log a).reg ∈ X i → a ∈ (E.σ ta).app i := by
    intro a hau
    by_cases ha : ((E.σ t).log a).reg ∈ X i
    · obtain ⟨ta, hta⟩ := ih a hau (by omega) ha
      exact ⟨ta, fun _ => hta⟩
    · exact ⟨0, fun h' => absurd h' ha⟩
  choose! ta hta using hT
  let T := max t ((Finset.range u).sup ta)
  have hTt : t ≤ T := le_max_left _ _
  have hlogT : ∀ c < (E.σ t).n, (E.σ T).log c = (E.σ t).log c := (E.mono hTt).2.1
  obtain ⟨t', -, ht'⟩ := theorem_3_liveness E hE (t := T) (u := u)
    (lt_of_lt_of_le hu (E.mono hTt).1) (by rw [hlogT u hu]; exact hux) (by
      intro a ha hau
      have hau' := (E.hb_iff hTt hu).1 hau
      have hlt := (Inv.of_reachable (E.reachable t)).hb_lt hau'
      rw [hlogT a (hlt.trans hu)] at ha
      have hle : ta a ≤ T :=
        (Finset.le_sup (f := ta) (Finset.mem_range.2 hlt)).trans (le_max_right _ _)
      exact (E.mono hle).2.2 i (hta a hlt ha))
  exact ⟨t', ht'⟩

end Podc.PartialReplicationCausal
