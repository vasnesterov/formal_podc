import Papers.PODC2019.FloodingTermination.TerminationTime

/-!
# A computable simulation of amnesiac flooding

`simulate G s t : Finset (V × V)` is the set of messages `(u, v)` sent in round `t`, computed by
iterating the round map on finite sets. `mem_simulate` shows it agrees with `sends`, so concrete
termination times can be checked by `decide`.
-/

namespace FloodingTermination

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : V)

/-- One round on finite message sets. -/
def simStep (M : Finset (V × V)) : Finset (V × V) :=
  Finset.univ.filter fun p => G.Adj p.1 p.2 ∧ (∃ u, (u, p.1) ∈ M) ∧ (p.2, p.1) ∉ M

/-- The messages sent in round `t`. -/
def simulate : ℕ → Finset (V × V)
  | 0 => ∅
  | 1 => Finset.univ.filter fun p => p.1 = s ∧ G.Adj p.1 p.2
  | t + 2 => simStep G (simulate (t + 1))

variable {G s}

theorem mem_simulate (t : ℕ) (u v : V) : (u, v) ∈ simulate G s t ↔ sends G s t u v := by
  induction t using Nat.strong_induction_on generalizing u v with
  | _ t ih =>
    match t, ih with
    | 0, _ => simp [simulate]
    | 1, _ => simp [simulate]
    | t + 2, ih =>
      simp only [simulate, simStep, Finset.mem_filter, Finset.mem_univ, true_and, sends_add_two,
        ih (t + 1) (by omega)]

theorem mem_roundSet_iff_simulate {t : ℕ} (v : V) :
    v ∈ roundSet G s (t + 1) ↔ ∃ u, (u, v) ∈ simulate G s (t + 1) := by
  simp [mem_roundSet_succ, mem_simulate]

theorem roundSet_succ_eq_empty_iff {t : ℕ} :
    roundSet G s (t + 1) = ∅ ↔ simulate G s (t + 1) = ∅ := by
  constructor
  · intro h
    ext ⟨u, v⟩
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    have : v ∈ roundSet G s (t + 1) := (mem_roundSet_iff_simulate v).2 ⟨u, hm⟩
    rw [h] at this; exact this
  · intro h
    ext v
    simp [mem_roundSet_iff_simulate, h]

/-- Decidable criterion for the termination time `T + 1`. -/
theorem isTerminationTime_succ_iff {T : ℕ} :
    IsTerminationTime G s (T + 1) ↔ simulate G s (T + 1) ≠ ∅ ∧ simulate G s (T + 2) = ∅ := by
  rw [IsTerminationTime, terminatesAfter_iff, roundSet_succ_eq_empty_iff, ← Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    obtain ⟨u, hu⟩ := (mem_roundSet_iff_simulate v).1 hv
    exact ⟨⟨_, hu⟩, h⟩
  · rintro ⟨⟨⟨u, v⟩, hm⟩, h⟩
    exact ⟨⟨v, (mem_roundSet_iff_simulate v).2 ⟨u, hm⟩⟩, h⟩

instance decidableMemRoundSet (t : ℕ) : DecidablePred (· ∈ roundSet G s t) := fun v =>
  match t with
  | 0 => decidable_of_iff (v = s) (by simp)
  | t + 1 => decidable_of_iff _ (mem_roundSet_iff_simulate v).symm

instance decidableIsFirstIn (v : V) (j : ℕ) : Decidable (IsFirstIn G s v j) :=
  inferInstanceAs (Decidable (_ ∧ ∀ i < j, _))

/-! ### Distances, eccentricity and diameter read off from flooding

Since the first round in which `v` receives the message is `d(s, v)` (`isFirstIn_iff`), the
simulation also computes distances. -/

section Metric

variable {W : Type*} {H : SimpleGraph W}

lemma edist_le_of_mem_roundSet {r v : W} {j : ℕ} (h : v ∈ roundSet H r j) : H.edist r v ≤ j :=
  edist_le_of_mem_walkSet (mem_roundSet_iff.1 h).1

lemma edist_eq_of_isFirstIn {r v : W} {j : ℕ} (h : IsFirstIn H r v j) : H.edist r v = j := by
  obtain ⟨hr, hd⟩ := isFirstIn_iff.1 h
  rw [← hr.coe_dist_eq_edist, hd]

lemma eccent_eq_of_roundSet {r : W} {e : ℕ} (hle : ∀ v, ∃ j ≤ e, v ∈ roundSet H r j)
    (hex : ∃ v, IsFirstIn H r v e) : H.eccent r = e := by
  apply le_antisymm
  · rw [eccent_le_iff]
    intro v
    obtain ⟨j, hj, hv⟩ := hle v
    exact (edist_le_of_mem_roundSet hv).trans (by exact_mod_cast hj)
  · obtain ⟨v, hv⟩ := hex
    rw [← edist_eq_of_isFirstIn hv]
    exact edist_le_eccent

lemma connected_of_roundSet [Nonempty W] {r : W} (h : ∀ v, ∃ j, v ∈ roundSet H r j) :
    H.Connected := by
  refine Connected.mk fun u v => ?_
  obtain ⟨j, hj⟩ := h u
  obtain ⟨k, hk⟩ := h v
  exact (reachable_of_mem_roundSet hj).symm.trans (reachable_of_mem_roundSet hk)

lemma diam_eq_of_roundSet {d : ℕ} (hle : ∀ u v, ∃ j ≤ d, v ∈ roundSet H u j)
    (hex : ∃ u v, IsFirstIn H u v d) : H.diam = d := by
  have hed : H.ediam = d := by
    apply le_antisymm
    · rw [ediam_le_iff]
      intro u v
      obtain ⟨j, hj, hv⟩ := hle u v
      exact (edist_le_of_mem_roundSet hv).trans (by exact_mod_cast hj)
    · obtain ⟨u, v, hv⟩ := hex
      rw [← edist_eq_of_isFirstIn hv]
      exact edist_le_ediam
  rw [diam, hed]
  rfl

end Metric

end FloodingTermination
