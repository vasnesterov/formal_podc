import Papers.PODC2019.FloodingTermination.Model

/-!
# Termination of synchronous amnesiac flooding (Section 2 of Hussak–Trehan)

* `theorem_2_2` — every node lies in at most two round-sets (for any graph, finite or not).
* `corollary_2_4` — on a finite graph with `n` vertices, `R_t = ∅` for all `t ≥ 2n`, so flooding
  terminates (in fewer than `2n + 1` rounds).
* `exists_isTerminationTime` — hence every finite graph has a termination time.
-/

namespace FloodingTermination

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : V}

/-- Two round-sets containing the same node with indices of the same parity coincide. -/
lemma eq_of_mem_roundSet {v : V} {a b : ℕ} (ha : v ∈ roundSet G s a) (hb : v ∈ roundSet G s b)
    (hab : a % 2 = b % 2) : a = b :=
  (mem_roundSet_iff.1 ha).eq_of_mod_two_eq (mem_roundSet_iff.1 hb) hab

/-- **Theorem 2.2** of [Hussak–Trehan, PODC'19]. Any node is contained in at most two distinct
round-sets. -/
theorem theorem_2_2 (v : V) {a b c : ℕ} (ha : v ∈ roundSet G s a) (hb : v ∈ roundSet G s b)
    (hc : v ∈ roundSet G s c) : a = b ∨ a = c ∨ b = c := by
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
  rcases Nat.mod_two_eq_zero_or_one c with h3 | h3
  all_goals first
    | exact Or.inl (eq_of_mem_roundSet ha hb (by omega))
    | exact Or.inr (Or.inl (eq_of_mem_roundSet ha hc (by omega)))
    | exact Or.inr (Or.inr (eq_of_mem_roundSet hb hc (by omega)))

/-- Theorem 2.2, set form: the set of rounds in which a node receives the message has at most two
elements. -/
theorem theorem_2_2' (v : V) : {t | v ∈ roundSet G s t}.encard ≤ 2 := by
  by_contra h
  push Not at h
  have h3 : (3 : ℕ∞) ≤ {t | v ∈ roundSet G s t}.encard := by
    exact Order.add_one_le_of_lt h
  obtain ⟨T, hT, hcard⟩ := Set.exists_subset_encard_eq h3
  have hT' : T.ncard = 3 := by
    rw [Set.ncard_def, hcard]; rfl
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 hT'
  have := theorem_2_2 (G := G) (s := s) v (a := a) (b := b) (c := c) (hT (by simp))
    (hT (by simp)) (hT (by simp))
  omega

/-- **Corollary 2.4** of [Hussak–Trehan, PODC'19] (via the paper's argument "Theorem 2.2 implies
`R_i = ∅` for `i ≥ 2|G|`"). On a finite graph with `n` nodes no message is sent in any round
`t ≥ 2n`; in particular synchronous amnesiac flooding always terminates, in fewer than `2n + 1`
rounds. -/
theorem corollary_2_4 [Fintype V] (s : V) {t : ℕ} (ht : 2 * Fintype.card V ≤ t) :
    roundSet G s t = ∅ := by
  classical
  by_contra hne
  -- all rounds `≤ 2n` are active
  have hact : ∀ i : Fin (2 * Fintype.card V + 1), (roundSet G s i).Nonempty := by
    intro i
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hne (roundSet_eq_empty_of_le he (by omega))
  let f : Fin (2 * Fintype.card V + 1) → V := fun i => (hact i).some
  obtain ⟨y, hy⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (n := 2) f (by simp; omega)
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hmem : ∀ i, f i = y → y ∈ roundSet G s i := fun i hi => hi ▸ (hact i).some_mem
  rcases theorem_2_2 y (hmem a ha) (hmem b hb) (hmem c hc) with h | h | h
  · exact hab (Fin.ext h)
  · exact hac (Fin.ext h)
  · exact hbc (Fin.ext h)

/-- Synchronous amnesiac flooding terminates on every finite graph. -/
theorem terminates [Fintype V] (s : V) : TerminatesAfter G s (2 * Fintype.card V) :=
  fun _ ht => corollary_2_4 s (by omega)

/-- Every finite graph has a (unique) termination time, which is `< 2n` if `n ≥ 1`
(`2n - 1` in natural-number subtraction). -/
theorem exists_isTerminationTime_lt [Fintype V] (s : V) :
    ∃ T, T < 2 * Fintype.card V ∧ IsTerminationTime G s T := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨s⟩
  obtain ⟨T, hT, h⟩ := exists_isTerminationTime (G := G) (s := s)
    (T := 2 * Fintype.card V - 1) (fun _ ht => corollary_2_4 s (by omega))
  exact ⟨T, by omega, h⟩

end FloodingTermination
