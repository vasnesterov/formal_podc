import Papers.PODC2025.AmnesiacFloodingFaults.Lift

/-!
# The termination dichotomy (Theorem 5.1, Corollary 5.1.1, Theorem 5.5, Theorem 2.1)

Here "balanced" means balanced along *every* closed walk (`BalancedAll`). The equivalence with
the paper's Definition 5.4 (balance on cycles and faux-even cycles only) is in `Balance.lean`.

* `iterate_eq_empty_of_balancedAll` — a balanced configuration on a finite graph terminates within
  `2|E|` rounds (Corollary 5.1.1). Proof: if a message survives `2|E|` rounds, follow its
  ancestors back to round `0`; by pigeonhole some directed edge carries an ancestor twice, so a
  message travelled once around a closed walk, contradicting `not_balancedOn_of_front`.
* `terminates_iff_balancedAll` — Theorem 5.1 for closed walks.
* `theorem_5_5_walks` — terminating ⇔ reachable from `∅` by multicasts ⇔ balanced.
* `theorem_2_1` — multicast amnesiac flooding terminates (Theorem 2.1 / Lemma 3.1, from the
  literature; here it is a corollary).
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- `S` is balanced along every closed walk of `G`. -/
def BalancedAll (G : SimpleGraph V) (S : Config V) : Prop :=
  ∀ (L : ℕ) [NeZero L] (w : ZMod L → V), IsClosedWalk G w → BalancedOn S w

lemma balancedAll_empty : BalancedAll G (∅ : Config V) := fun _ _ w _ => balancedOn_empty w

lemma balancedAll_step_iff {I : Set V} {S : Config V} :
    BalancedAll G (step G I S) ↔ BalancedAll G S :=
  ⟨fun h L _ w hw => (balancedOn_step_iff hw I S).1 (h L w hw),
    fun h L _ w hw => (balancedOn_step_iff hw I S).2 (h L w hw)⟩

lemma balancedAll_iterate_iff {S : Config V} (k : ℕ) :
    BalancedAll G ((af G)^[k] S) ↔ BalancedAll G S :=
  ⟨fun h L _ w hw => (balancedOn_iterate_iff hw S k).1 (h L w hw),
    fun h L _ w hw => (balancedOn_iterate_iff hw S k).2 (h L w hw)⟩

lemma balancedAll_rev_iff {S : Config V} : BalancedAll G (rev S) ↔ BalancedAll G S :=
  ⟨fun h L _ w hw => (balancedOn_rev_iff S w).1 (h L w hw),
    fun h L _ w hw => (balancedOn_rev_iff S w).2 (h L w hw)⟩

lemma Reachable.balancedAll {S : Config V} (h : Reachable G S) : BalancedAll G S := by
  obtain ⟨Is, rfl⟩ := h
  intro L _ w hw
  exact (balancedOn_runFrom_iff hw Is ∅).2 (balancedOn_empty w)

/-- A terminating configuration is balanced along every closed walk (Corollary A.1.1). -/
theorem Terminates.balancedAll {S : Config V} (h : Terminates G S) : BalancedAll G S := by
  obtain ⟨k, hk⟩ := h
  rw [← balancedAll_iterate_iff k, hk]
  exact balancedAll_empty

lemma zmod_val_add_one {L : ℕ} [NeZero L] (k : ZMod L) : (k + 1).val = (k.val + 1) % L := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  rw [← Nat.cast_add_one, ZMod.val_natCast]

/-- Every message of `A^N(S)` has a chain of ancestors back to `S`. -/
lemma exists_ancestors (S : Config V) :
    ∀ (N : ℕ) (m : V × V), m ∈ (af G)^[N] S → ∃ c : ℕ → V × V, c N = m ∧
      (∀ k ≤ N, c k ∈ (af G)^[k] S) ∧ ∀ k < N, (c k).2 = (c (k + 1)).1 := by
  intro N
  induction N with
  | zero => intro m hm; exact ⟨fun _ => m, rfl, fun k hk => by simpa [Nat.le_zero.1 hk] using hm,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    intro m hm
    rw [Function.iterate_succ_apply'] at hm
    obtain ⟨x, hx⟩ := hm.2.2.resolve_left (Set.notMem_empty _)
    obtain ⟨c, hcN, hcmem, hclink⟩ := ih (x, m.1) hx
    refine ⟨Function.update c (N + 1) m, by simp, fun k hk => ?_, fun k hk => ?_⟩
    · rcases Nat.lt_or_ge k (N + 1) with h | h
      · rw [Function.update_of_ne (by omega)]; exact hcmem k (by omega)
      · obtain rfl : k = N + 1 := by omega
        rw [Function.update_self, Function.iterate_succ_apply']
        exact hm
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_or_ge (k + 1) (N + 1) with h | h
      · rw [Function.update_of_ne (by omega)]; exact hclink k (by omega)
      · obtain rfl : k = N := by omega
        rw [Function.update_self, hcN]

/-- **Corollary 5.1.1.** On a finite graph, amnesiac flooding from a configuration that is balanced
along every closed walk terminates within `2|E|` rounds. -/
theorem iterate_eq_empty_of_balancedAll [Fintype V] [DecidableRel G.Adj] {S : Config V}
    (hS : IsConfig G S) (h : BalancedAll G S) : (af G)^[2 * #G.edgeFinset] S = ∅ := by
  classical
  set N := 2 * #G.edgeFinset
  by_contra hne
  obtain ⟨m, hm⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨c, -, hcmem, hclink⟩ := exists_ancestors S N m hm
  have hadj : ∀ k ≤ N, G.Adj (c k).1 (c k).2 := fun k hk =>
    isConfig_iterate hS k _ _ (hcmem k hk)
  let f : Fin (N + 1) → G.Dart := fun k => ⟨c k, hadj k (by omega)⟩
  have hcard : Fintype.card G.Dart < Fintype.card (Fin (N + 1)) := by
    rw [dart_card_eq_twice_card_edges, Fintype.card_fin]; omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hcab : c a = c b := congrArg Dart.toProd hfab
  -- order the two indices
  obtain ⟨i, j, hij, hjN, hcij⟩ : ∃ i j : ℕ, i < j ∧ j ≤ N ∧ c i = c j := by
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact ⟨a, b, h, by omega, hcab⟩
    · exact ⟨b, a, h, by omega, hcab.symm⟩
  set L := j - i with hL
  have : NeZero L := ⟨by omega⟩
  let w : ZMod L → V := fun k => (c (i + k.val)).1
  have hstep : ∀ k : ZMod L, (w k, w (k + 1)) = c (i + k.val) := by
    intro k
    have hk : k.val < L := ZMod.val_lt k
    apply Prod.ext
    · rfl
    · simp only [w]
      rcases Nat.lt_or_ge (k.val + 1) L with h1 | h1
      · have : (k + 1).val = k.val + 1 := by
          rw [ZMod.val_add, ZMod.val_one'' (by omega), Nat.mod_eq_of_lt h1]
        rw [this, ← add_assoc, hclink (i + k.val) (by omega)]
      · have hkL : k.val + 1 = L := by omega
        have : (k + 1).val = 0 := by
          rw [zmod_val_add_one, hkL, Nat.mod_self]
        rw [this, add_zero, hcij, hclink (i + k.val) (by omega)]
        congr 2; omega
  have hw : IsClosedWalk G w := by
    intro k
    have := hadj (i + k.val) (by have := ZMod.val_lt k; omega)
    rwa [← hstep k] at this
  let S' : ℕ → Config V := fun t => (af G)^[i + t] S
  have hS' : ∀ t, S' (t + 1) = step G ∅ (S' t) := by
    intro t; simp only [S', ← add_assoc, Function.iterate_succ_apply']
  have hfront : ∀ t ≤ classSize L, cw (S' t) w (0 + t) := by
    intro t ht
    have htL : t ≤ L := ht.trans classSize_le
    simp only [cw, zero_add, S']
    rcases Nat.lt_or_ge t L with h1 | h1
    · rw [hstep, ZMod.val_natCast, Nat.mod_eq_of_lt h1]
      exact hcmem _ (by omega)
    · obtain rfl : t = L := by omega
      rw [hstep, ZMod.natCast_self, ZMod.val_zero, add_zero, hcij]
      have : i + L = j := by omega
      rw [this]; exact hcmem j hjN
  have := not_balancedOn_of_front hw S' (fun _ => ∅) hS' 0 hfront
  apply this
  simp only [S', add_zero]
  exact (balancedOn_iterate_iff hw S i).2 (h L w hw)

/-- **Theorem 5.1 (closed-walk form).** On a finite graph, amnesiac flooding started from a
configuration `S` terminates iff `S` is balanced along every closed walk. -/
theorem terminates_iff_balancedAll [Fintype V] {S : Config V} (hS : IsConfig G S) :
    Terminates G S ↔ BalancedAll G S := by
  classical
  exact ⟨Terminates.balancedAll, fun h => ⟨_, iterate_eq_empty_of_balancedAll hS h⟩⟩

/-- A terminating configuration terminates within `2|E|` rounds. -/
theorem Terminates.iterate_eq_empty [Fintype V] [DecidableRel G.Adj] {S : Config V}
    (hS : IsConfig G S) (h : Terminates G S) : (af G)^[2 * #G.edgeFinset] S = ∅ :=
  iterate_eq_empty_of_balancedAll hS h.balancedAll

/-- **Theorem 2.1** (termination of multicast amnesiac flooding, Hussak–Trehan / Turau): every
configuration reachable from `∅` by multicasts terminates. -/
theorem theorem_2_1 [Fintype V] {S : Config V} (h : Reachable G S) : Terminates G S :=
  (terminates_iff_balancedAll h.isConfig).2 h.balancedAll

/-- **Lemma 3.1** (multicast amnesiac flooding terminates). -/
theorem lemma_3_1 [Fintype V] (Is : List (Set V)) :
    ∃ m, (af G)^[m] (runFrom G Is ∅) = ∅ :=
  theorem_2_1 ⟨Is, rfl⟩

/-- Statements (1) ⇒ (2) of Theorem 5.5: a terminating configuration is reachable from `∅` by a
sequence of multicasts. -/
theorem Terminates.reachable [Fintype V] {S : Config V} (hS : IsConfig G S)
    (h : Terminates G S) : Reachable G S := by
  have hrev : Terminates G (rev S) :=
    (terminates_iff_balancedAll hS.rev).2 (balancedAll_rev_iff.2 h.balancedAll)
  obtain ⟨k, hk⟩ := hrev
  obtain ⟨Is, -, hIs⟩ := lemma_5_3 hS k
  rw [hk, rev_empty] at hIs
  exact ⟨Is, hIs⟩

/-- **Theorem 5.5 (closed-walk form).** For a configuration `S` on a finite graph the following are
equivalent: (1) amnesiac flooding from `S` terminates; (2) `S` arises from `∅` by a sequence of
multicasts; (3) `S` is balanced along every closed walk. -/
theorem theorem_5_5_walks [Fintype V] {S : Config V} (hS : IsConfig G S) :
    [Terminates G S, Reachable G S, BalancedAll G S].TFAE := by
  tfae_have 1 → 2 := Terminates.reachable hS
  tfae_have 2 → 3 := Reachable.balancedAll
  tfae_have 3 → 1 := (terminates_iff_balancedAll hS).2
  tfae_finish

end AmnesiacFloodingFaults
