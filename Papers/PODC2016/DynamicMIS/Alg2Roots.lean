import Papers.PODC2016.DynamicMIS.Alg2Rounds

/-!
# Algorithm 2: trigger chains, Lemma 12, and the number of state changes (Lemmas 8, 12)

Every `C`-entry of a node `v` at time `t` is the end of a *trigger chain*
`z = w₀, w₁, …, w_t = v` of rank-increasing nodes, `w_j` entering `C` at time `j` (`run_entry`);
its *root* `z` is a node that is in `C` initially. We only record what the chain implies
(`IsRoot`):

* (`IsRoot.changing`) while `v` stays in `C` during `[t, T]`, the root stays in `C` during
  `[0, T + t]`: a node cannot leave `C` while a later-ranked neighbour that it triggered is in `C`
  (`changing_back`);
* (`IsRoot.final`) if `v` is in `M`/`M̄` at time `τ ≥ t`, the root was in `M`/`M̄` at some time
  `τ₀ ≤ τ - t`: a node leaves `R` only after all its predecessors are in `M`/`M̄`.

Consequences, valid for every network and every admissible initial configuration:

* **Lemma 12 (first part)** (`entry_spacing`): if `v` enters `C` at times `t₁ < t₂`, then
  `t₂ ≥ 3 t₁ + 4` (the paper, counting rounds from `1`, states `t₂ ≥ 3 t₁ + 1`).
* **Lemma 12 (second part)** (`card_entries_le_initC`): different `C`-entries of the same node have
  different roots, so a node enters `C` at most as many times as there are initially-`C` nodes.
* **Lemma 8** (`changes_le`): the number of changes of the visible state of a node is at most three
  times its number of `C`-entries (`M`/`M̄` → `C` → `R` → `M`/`M̄`).
* `card_le_log` turns the spacing of Lemma 12 into a logarithmic bound on the number of entries.
-/

open Finset

namespace DynamicMIS

namespace Alg2

variable {V : Type*} {N : Net V} {c₀ : V → St}

/-! ### Chains -/

/-- A node that has just changed to `C` and has a predecessor `v` in `C` during `[k + 1, T]` stays in
`C` during `[k, T + 1]`. -/
theorem changing_back {u v : V} (hv : v ∈ N.part) (huv : N.Pred u v) {k T : ℕ}
    (hu : run N c₀ k u = .changing 0)
    (hvC : ∀ τ, k + 1 ≤ τ → τ ≤ T → (run N c₀ τ v).IsChanging) :
    ∀ τ, k ≤ τ → τ ≤ T + 1 → (run N c₀ τ u).IsChanging := by
  intro τ
  induction τ with
  | zero => intro h1 _; obtain rfl : k = 0 := by omega
            rw [hu]; simp
  | succ τ ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [hu]; simp
    obtain ⟨a, ha⟩ := St.isChanging_iff.1 (ih (by omega) (by omega))
    rw [run_succ, step_of_changing N _ huv.2.1 ha]
    split_ifs with hc
    · exfalso
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h1) with rfl | h3
      · rw [hu] at ha; cases ha; omega
      · exact hc.2 v ⟨huv.1.symm, hv, huv.2.2⟩ (hvC τ (by omega) (by omega))
    · simp

/-- If `u` is outside `M`/`M̄` during `[a, L]` and `u` is a predecessor of `v`, which is outside
`M`/`M̄` at time `a + 1`, then `v` is outside `M`/`M̄` during `[a + 1, L + 1]`. -/
theorem nonfinal_forward {u v : V} (hv : v ∈ N.part) (huv : N.Pred u v) {a L : ℕ}
    (hu : ∀ τ, a ≤ τ → τ ≤ L → ¬ (run N c₀ τ u).IsFinal)
    (hv1 : ¬ (run N c₀ (a + 1) v).IsFinal) :
    ∀ τ, a + 1 ≤ τ → τ ≤ L + 1 → ¬ (run N c₀ τ v).IsFinal := by
  intro τ h1 h2 hf
  obtain ⟨τ', h3, h4, h5, h6⟩ := exists_finalize hv1 τ h1 hf
  exact hu τ' (by omega) (by omega) (run_finalize_preds hv h5 h6 u huv)

/-- `z` is a root of the `C`-entry of `v` at time `t`. -/
structure IsRoot (N : Net V) (c₀ : V → St) (z v : V) (t : ℕ) : Prop where
  mem : z ∈ N.part
  init : c₀ z = .changing 0
  changing : ∀ T, (∀ τ, t ≤ τ → τ ≤ T → (run N c₀ τ v).IsChanging) →
    ∀ τ, τ ≤ T + t → (run N c₀ τ z).IsChanging
  final : ∀ τ, t ≤ τ → (run N c₀ τ v).IsFinal → ∃ τ₀, τ₀ + t ≤ τ ∧ (run N c₀ τ₀ z).IsFinal

/-- Every `C`-entry has a root. -/
theorem exists_isRoot : ∀ t, ∀ v ∈ N.part, run N c₀ t v = .changing 0 → ∃ z, IsRoot N c₀ z v t := by
  intro t
  induction t with
  | zero =>
    intro v hv h
    exact ⟨v, hv, h, fun T hT τ hτ => hT τ (Nat.zero_le _) (by omega),
      fun τ _ hf => ⟨τ, by omega, hf⟩⟩
  | succ t ih =>
    intro v hv h
    obtain ⟨-, u, huv, hu⟩ := run_entry hv h
    obtain ⟨z, hz⟩ := ih u huv.2.1 hu
    refine ⟨z, hz.mem, hz.init, fun T hT τ hτ => ?_, fun τ hτ hf => ?_⟩
    · have := changing_back hv huv hu hT
      exact hz.changing (T + 1) (fun τ h1 h2 => this τ h1 h2) τ (by omega)
    · obtain ⟨τ', h3, h4, h5, h6⟩ := exists_finalize (v := v) (s := t + 1) (by rw [h]; simp) τ hτ hf
      obtain ⟨τ₀, h7, h8⟩ := hz.final τ' (by omega) (run_finalize_preds hv h5 h6 u huv)
      exact ⟨τ₀, by omega, h8⟩

/-- A node that has just changed to `C` is still in `C` one round later. -/
theorem run_changing_one {v : V} (hv : v ∈ N.part) {t : ℕ} (h : run N c₀ t v = .changing 0) :
    run N c₀ (t + 1) v = .changing 1 := by
  rw [run_succ, step_of_changing N _ hv h, ite_eq_right (by omega)]

/-- The root of a `C`-entry at time `t` stays in `C` during `[0, 2t + 1]` and is outside `M`/`M̄`
during `[0, 2t + 2]`. -/
theorem IsRoot.nonfinal {z v : V} {t : ℕ} (hv : v ∈ N.part) (h : run N c₀ t v = .changing 0)
    (hz : IsRoot N c₀ z v t) : ∀ τ, τ ≤ 2 * t + 2 → ¬ (run N c₀ τ z).IsFinal := by
  have hC : ∀ τ, τ ≤ 2 * t + 1 → (run N c₀ τ z).IsChanging := by
    refine fun τ hτ => hz.changing (t + 1) (fun τ h1 h2 => ?_) τ (by omega)
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [h]; simp
    · obtain rfl : τ = t + 1 := by omega
      rw [run_changing_one hv h]; simp
  intro τ hτ hf
  rcases Nat.lt_or_ge τ (2 * t + 2) with h1 | h1
  · exact St.not_isChanging_of_isFinal hf (hC τ (by omega))
  · obtain rfl : τ = 2 * t + 2 := by omega
    rcases step_changing_isChanging_or_ready (N := N) (hC (2 * t + 1) le_rfl) with h2 | h2
    · exact St.not_isChanging_of_isFinal hf h2
    · rw [run_succ, h2] at hf; exact hf

/-! ### Lemma 12 -/

/-- **Lemma 12 (first part).** If `v` changes to `C` at times `t₁ < t₂` (time `0` = the initial
changes), then `t₂ ≥ 3 t₁ + 4`. -/
theorem entry_spacing {v : V} (hv : v ∈ N.part) {t₁ t₂ : ℕ} (h₁ : run N c₀ t₁ v = .changing 0)
    (h₂ : run N c₀ t₂ v = .changing 0) (hlt : t₁ < t₂) : 3 * t₁ + 4 ≤ t₂ := by
  obtain ⟨z, hz⟩ := exists_isRoot t₁ v hv h₁
  obtain ⟨s, rfl⟩ : ∃ s, t₂ = s + 1 := ⟨t₂ - 1, by omega⟩
  obtain ⟨hfin, -⟩ := run_entry hv h₂
  obtain ⟨τ₀, h3, h4⟩ := hz.final s (by omega) hfin
  by_contra hcon
  exact hz.nonfinal hv h₁ τ₀ (by omega) h4

/-- Different `C`-entries of a node have different roots. -/
theorem IsRoot.ne {v z₁ z₂ : V} (hv : v ∈ N.part) {t₁ t₂ : ℕ} (h₂ : run N c₀ t₂ v = .changing 0) (hlt : t₁ < t₂) (hz₁ : IsRoot N c₀ z₁ v t₁)
    (hz₂ : IsRoot N c₀ z₂ v t₂) : z₁ ≠ z₂ := by
  rintro rfl
  obtain ⟨s, rfl⟩ : ∃ s, t₂ = s + 1 := ⟨t₂ - 1, by omega⟩
  obtain ⟨hfin, -⟩ := run_entry hv h₂
  obtain ⟨τ₀, h3, h4⟩ := hz₁.final s (by omega) hfin
  exact hz₂.nonfinal hv h₂ τ₀ (by omega) h4

/-- The `C`-entry times of `v` up to time `T`. -/
noncomputable def entries (N : Net V) (c₀ : V → St) (v : V) (T : ℕ) : Finset ℕ :=
  (range (T + 1)).filter fun t => run N c₀ t v = .changing 0

/-! ### A logarithmic bound from the spacing -/

/-- A finite set of naturals `≤ M` in which any two elements satisfy `b ≥ 3 a + 4` has
`2 · 3 ^ #s ≤ 3 (M + 2)`. -/
theorem two_mul_pow_le (s : Finset ℕ) : ∀ M, (∀ a ∈ s, a ≤ M) →
    (∀ a ∈ s, ∀ b ∈ s, a < b → 3 * a + 4 ≤ b) → 2 * 3 ^ #s ≤ 3 * (M + 2) := by
  induction s using Finset.induction_on_max with
  | empty => intro M _ _; simp; omega
  | insert a s hlt ih =>
    intro M hM hsp
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has, pow_succ]
    have haM := hM a (mem_insert_self a s)
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp; omega
    · have hm := s.max'_mem hne
      have h1 := ih (s.max' hne) (fun x hx => s.le_max' x hx)
        (fun x hx y hy => hsp x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      have h2 := hsp _ (mem_insert_of_mem hm) a (mem_insert_self a s) (hlt _ hm)
      generalize 3 ^ #s = p at h1 ⊢
      omega

/-- The logarithmic form: such a set has at most `log₃ (M + 2) + 1` elements. -/
theorem card_le_log (s : Finset ℕ) (M : ℕ) (hM : ∀ a ∈ s, a ≤ M)
    (hsp : ∀ a ∈ s, ∀ b ∈ s, a < b → 3 * a + 4 ≤ b) : #s ≤ Nat.log 3 (M + 2) + 1 := by
  have h := two_mul_pow_le s M hM hsp
  rcases Nat.eq_zero_or_pos #s with h0 | h0
  · omega
  obtain ⟨k, hk⟩ : ∃ k, #s = k + 1 := ⟨#s - 1, by omega⟩
  rw [hk, pow_succ] at h
  have : 3 ^ k ≤ M + 2 := by
    generalize 3 ^ k = p at h ⊢
    omega
  have := Nat.le_log_of_pow_le (by norm_num) this
  omega

/-! ### Counting visible state changes (Lemma 8) -/

/-- The number of rounds among the first `T` in which `v` changes its visible state. -/
noncomputable def changes (N : Net V) (c₀ : V → St) (v : V) (T : ℕ) : ℕ :=
  #((range T).filter fun t => (run N c₀ (t + 1) v).cls ≠ (run N c₀ t v).cls)

/-- Potential used for counting: `C` ↦ 2, `R` ↦ 1, `M`/`M̄` ↦ 0. -/
def St.pot : St → ℕ
  | .changing _ => 2
  | .ready => 1
  | _ => 0

theorem step_pot {v : V} (hv : v ∈ N.part) (c : V → St) :
    (if (step N c v).cls ≠ (c v).cls then 1 else 0) + (step N c v).pot ≤
      (c v).pot + 3 * (if step N c v = .changing 0 then 1 else 0) := by
  rcases St.trichotomy (c v) with hf | hc | hr
  · rcases St.isFinal_iff.1 hf with h | h
    · rcases step_inM (N := N) h with h' | h' <;> rw [h, h'] <;> decide
    · rcases step_outM (N := N) h with h' | h' <;> rw [h, h'] <;> decide
  · obtain ⟨a, ha⟩ := St.isChanging_iff.1 hc
    rw [step_of_changing N c hv ha, ha]
    split_ifs <;> simp_all [St.cls, St.pot]
  · rcases step_ready (N := N) hr with h' | h'
    · rcases St.isFinal_iff.1 h' with h'' | h'' <;> rw [hr, h''] <;> decide
    · rw [hr, h']; decide

theorem changes_succ (v : V) (T : ℕ) : changes N c₀ v (T + 1) = changes N c₀ v T +
    if (run N c₀ (T + 1) v).cls ≠ (run N c₀ T v).cls then 1 else 0 := by
  unfold changes
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem card_entries_succ (v : V) (T : ℕ) : #(entries N c₀ v (T + 1)) = #(entries N c₀ v T) +
    if run N c₀ (T + 1) v = .changing 0 then 1 else 0 := by
  unfold entries
  rw [range_add_one (n := T + 1), filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem changes_of_notMem {v : V} (hv : v ∉ N.part) (T : ℕ) : changes N c₀ v T = 0 := by
  simp only [changes, card_eq_zero, filter_eq_empty_iff, mem_range, ne_eq, not_not]
  intro t _
  rw [run_of_notMem hv, run_of_notMem hv]

/-- **Lemma 8 (counting form).** A node changes its visible state at most three times per
`C`-entry. -/
theorem changes_le (h₀ : InitOK N c₀) (v : V) (T : ℕ) :
    changes N c₀ v T ≤ 3 * #(entries N c₀ v T) := by
  by_cases hv : v ∈ N.part
  · suffices changes N c₀ v T + (run N c₀ T v).pot ≤ 3 * #(entries N c₀ v T) by omega
    induction T with
    | zero =>
      simp only [changes, range_zero, filter_empty, card_empty, zero_add, run_zero]
      rcases h₀ v hv with h | h
      · rcases St.isFinal_iff.1 h with h | h <;> rw [h] <;> simp [St.pot]
      · have : entries N c₀ v 0 = {0} := by
          ext t
          simp only [entries, mem_filter, mem_range, mem_singleton]
          constructor
          · rintro ⟨h1, -⟩; omega
          · rintro rfl; exact ⟨by omega, h⟩
        rw [h, this]; simp [St.pot]
    | succ T ih =>
      rw [changes_succ, card_entries_succ]
      have := step_pot hv (run N c₀ T)
      rw [← run_succ] at this
      omega
  · rw [changes_of_notMem hv]; omega

variable [Fintype V]

open Classical in
/-- The nodes in `C` initially. -/
noncomputable def initC (N : Net V) (c₀ : V → St) : Finset V :=
  univ.filter fun z => z ∈ N.part ∧ c₀ z = .changing 0

/-- **Lemma 12 (second part).** A node enters `C` at most as many times as there are initially-`C`
nodes. -/
theorem card_entries_le_initC {v : V} (hv : v ∈ N.part) (T : ℕ) :
    #(entries N c₀ v T) ≤ #(initC N c₀) := by
  have : ∀ t, ∃ z, run N c₀ t v = .changing 0 → IsRoot N c₀ z v t := by
    intro t
    by_cases h : run N c₀ t v = .changing 0
    · obtain ⟨z, hz⟩ := exists_isRoot t v hv h
      exact ⟨z, fun _ => hz⟩
    · exact ⟨v, fun h' => absurd h' h⟩
  choose f hf using this
  refine card_le_card_of_injOn f (fun t ht => ?_) (fun t₁ ht₁ t₂ ht₂ heq => ?_)
  · simp only [entries, coe_filter, Set.mem_ofPred_eq, mem_range] at ht
    have := hf t ht.2
    simp [initC, this.mem, this.init]
  · simp only [entries, coe_filter, Set.mem_ofPred_eq, mem_range] at ht₁ ht₂
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact IsRoot.ne hv ht₂.2 h (hf t₁ ht₁.2) (hf t₂ ht₂.2) heq
    · exact IsRoot.ne hv ht₁.2 h (hf t₂ ht₂.2) (hf t₁ ht₁.2) heq.symm

/-- The total number of broadcasts in the first `T` rounds is the total number of visible state
changes. -/
theorem sum_broadcastsAt (T : ℕ) :
    ∑ t ∈ range T, broadcastsAt N c₀ t = ∑ v, changes N c₀ v T := by
  classical
  simp only [broadcastsAt, changes, card_filter]
  rw [Finset.sum_comm]

/-- The total number of broadcasts is at most `3 · |X| · B` if only nodes of `X` change and each
of them enters `C` at most `B` times. -/
theorem sum_broadcastsAt_le (h₀ : InitOK N c₀) (X : Finset V)
    (hX : ∀ v, v ∉ X → ∀ t, run N c₀ t v = c₀ v) (B T : ℕ)
    (hB : ∀ v ∈ X, v ∈ N.part → #(entries N c₀ v T) ≤ B) :
    ∑ t ∈ range T, broadcastsAt N c₀ t ≤ 3 * #X * B := by
  rw [sum_broadcastsAt, ← Finset.sum_subset (subset_univ X)]
  · calc ∑ v ∈ X, changes N c₀ v T ≤ ∑ _v ∈ X, 3 * B :=
          Finset.sum_le_sum fun v hv => by
            by_cases hvP : v ∈ N.part
            · exact (changes_le h₀ v T).trans (by have := hB v hv hvP; omega)
            · rw [changes_of_notMem hvP]; omega
      _ = 3 * #X * B := by rw [sum_const, smul_eq_mul]; ring
  · intro v _ hv
    simp only [changes, card_eq_zero, filter_eq_empty_iff, mem_range, ne_eq, not_not]
    intro t _
    rw [hX v hv, hX v hv]

end Alg2

end DynamicMIS
