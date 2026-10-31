import Papers.PODC2010.TruncatedGaleShapley.Invariants
import Podc.Foundations.Combinatorics.SimpleGraph.BallCard

/-!
# Locality of the truncated Gale–Shapley algorithm (§2.1, §6.3)

"Each round of the algorithm propagates information for at most two hops": the state of a node at
the end of round `j` depends only on the preferences of the nodes within distance `2j`
(`run_congr_of_agree`). Used for the query bound of Theorem 3.
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

namespace Bicoloured

/-- The communication graph of a bicoloured graph. -/
def graph (I : Bicoloured V) : SimpleGraph V where
  Adj u v := v ∈ I.N u
  symm := ⟨fun _ _ h => I.symm h⟩
  loopless := ⟨fun _ h => I.red_ne h rfl⟩

instance (I : Bicoloured V) : DecidableRel I.graph.Adj := fun u v =>
  inferInstanceAs (Decidable (v ∈ I.N u))

lemma graph_degree [Fintype V] (I : Bicoloured V) (v : V) : I.graph.degree v = (I.N v).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1; ext u; rw [SimpleGraph.mem_neighborFinset]; rfl

/-- The state after `t` turns (blue turns at even `t`, red turns at odd `t`). -/
noncomputable def turns (I : Bicoloured V) : ℕ → State V
  | 0 => I.init
  | t + 1 => if t % 2 = 0 then I.blueTurn (turns I t) else I.redTurn (turns I t)

lemma turns_two_mul (I : Bicoloured V) (i : ℕ) : I.turns (2 * i) = I.run i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [e, turns, turns, run_succ, ← ih]
    simp [round, show (2 * i + 1) % 2 = 1 by omega]

lemma turns_c_blue (I : Bicoloured V) {v : V} (hv : I.red v = false) (t : ℕ) :
    (I.turns t).c v = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [turns]; split_ifs
    · exact ih
    · rw [(I.redTurn_blue _ hv).2.1, ih]

/-- Pointers and candidate lists stay among the neighbours. -/
structure NbrFacts (I : Bicoloured V) (s : State V) : Prop where
  c_mem : ∀ v b, s.c v = some b → b ∈ I.N v
  p_mem : ∀ v b, s.p v = some b → b ∈ I.N v
  C_sub : ∀ v, I.red v = true → s.C v ⊆ I.N v

lemma Inv.nbrFacts {I : Bicoloured V} {s : State V} (hs : I.Inv s)
    (hc : ∀ v, I.red v = false → s.c v = none) : I.NbrFacts s where
  c_mem v b h := by
    cases hv : I.red v
    · rw [hc v hv] at h; cases h
    · rcases hp : s.p v with _ | b'
      · rw [hs.red_unmatched v hv hp] at h; exact hs.C_sub v hv (I.best_mem h)
      · rw [hs.c_eq_none hv hp] at h; cases h
  p_mem := hs.p_mem
  C_sub := hs.C_sub

lemma nbrFacts_turns (I : Bicoloured V) (t : ℕ) : I.NbrFacts (I.turns t) := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, t = 2 * i ∨ t = 2 * i + 1 := ⟨t / 2, by omega⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨fun v b h => by simp [turns] at h, fun v b h => by simp [turns] at h,
        fun v hv => by simp [turns, hv]⟩
    · rw [turns_two_mul]
      exact (I.inv_run hi).nbrFacts fun v hv => by rw [← turns_two_mul]; exact I.turns_c_blue hv _
  · rw [turns, ite_eq_left (by omega), turns_two_mul]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · refine ⟨fun v b h => by simp [run_zero] at h, fun v b h => ?_, fun v hv => by
        simp [run_zero, hv]⟩
      rw [run_zero, blueTurn_init_p] at h; cases h
    · have hs := I.inv_run hi
      have hc : ∀ v, I.red v = false → (I.run i).c v = none := fun v hv => by
        rw [← turns_two_mul]; exact I.turns_c_blue hv _
      refine ⟨fun v b h => (hs.nbrFacts hc).c_mem v b h, fun v b h => ?_,
        fun v hv => hs.C_sub v hv⟩
      cases hv : I.red v
      · exact hs.blueTurn_p_mem hv h
      · rw [I.blueTurn_p_red _ hv] at h; exact hs.p_mem v b h

/-! ### Agreement -/

/-- `I` and `I'` have the same local data at `u` (neighbours, preferences, colour). -/
def AgreeAt (I I' : Bicoloured V) (u : V) : Prop :=
  I.N u = I'.N u ∧ (∀ x ∈ I.N u, I.rank u x = I'.rank u x) ∧ I.red u = I'.red u

/-- `I` and `I'` agree on all nodes reachable from `v` in at most `k` hops (in `I`). -/
def AgreeBall (I I' : Bicoloured V) : V → ℕ → Prop
  | v, 0 => AgreeAt I I' v
  | v, k + 1 => AgreeAt I I' v ∧ ∀ u ∈ I.N v, AgreeBall I I' u k

lemma AgreeBall.agreeAt {I I' : Bicoloured V} {v : V} {k : ℕ} (h : AgreeBall I I' v k) :
    AgreeAt I I' v := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

lemma best_congr {I I' : Bicoloured V} {v : V} (h : AgreeAt I I' v) {S : Finset V}
    (hS : S ⊆ I.N v) : I.best v S = I'.best v S := by
  have hS' : S ⊆ I'.N v := h.1 ▸ hS
  rcases hb : I.best v S with _ | x
  · rw [eq_comm, I'.best_eq_none]; exact I.best_eq_none.1 hb
  · obtain ⟨hx, hmin⟩ := I.best_spec hb
    symm
    rw [I'.best_eq_some_iff hS']
    refine ⟨hx, fun y hy => ?_⟩
    rw [← h.2.1 x (hS hx), ← h.2.1 y (hS hy)]
    exact hmin y hy

/-- Two states agree at `u`. -/
def StAgree (s s' : State V) (u : V) : Prop := s.C u = s'.C u ∧ s.c u = s'.c u ∧ s.p u = s'.p u

lemma blueTurn_agree {I I' : Bicoloured V} {s s' : State V} (hF : I.NbrFacts s) {v : V}
    (hv : AgreeAt I I' v) (hsv : StAgree s s' v) (hN : ∀ u ∈ I.N v, StAgree s s' u) :
    StAgree (I.blueTurn s) (I'.blueTurn s') v := by
  refine ⟨hsv.1, hsv.2.1, ?_⟩
  have hP : I.proposers s v = I'.proposers s' v := by
    unfold proposers; rw [← hv.1]
    exact filter_congr fun u hu => by rw [(hN u hu).2.1]
  simp only [blueTurn]
  rw [← hv.2.2, hP, ← hsv.2.2]
  split_ifs with h
  · apply best_congr hv
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · rw [← hP] at hx; exact (I.mem_proposers.1 hx).1
    · exact hF.p_mem v x (by simpa using hx)
  · rfl

lemma redStep2_C_sub (s : State V) (v : V) (x : Finset V × Option V) :
    (redStep2 s v x).1 ⊆ x.1 := by
  obtain ⟨C, _ | b⟩ := x
  · exact subset_rfl
  · simp only [redStep2]; split_ifs
    · exact subset_rfl
    · exact erase_subset _ _

lemma redTurn_agree {I I' : Bicoloured V} {s s' : State V} (hF : I.NbrFacts s) {v : V}
    (hv : AgreeAt I I' v) (hsv : StAgree s s' v) (hN : ∀ u ∈ I.N v, StAgree s s' u) :
    StAgree (I.redTurn s) (I'.redTurn s') v := by
  cases hr : I.red v
  · have hr' : I'.red v = false := hv.2.2 ▸ hr
    obtain ⟨h1, h2, h3⟩ := I.redTurn_blue s hr
    obtain ⟨h1', h2', h3'⟩ := I'.redTurn_blue s' hr'
    exact ⟨h1.trans (hsv.1.trans h1'.symm), h2.trans (hsv.2.1.trans h2'.symm),
      h3.trans (hsv.2.2.trans h3'.symm)⟩
  · have hr' : I'.red v = true := hv.2.2 ▸ hr
    have e1 : redStep1 s v = redStep1 s' v := by
      unfold redStep1
      rw [← hsv.2.1]
      rcases hc : s.c v with _ | b
      · simp [hsv.1, hsv.2.2]
      · simp only [hsv.1, hsv.2.2, (hN b (hF.c_mem v b hc)).2.2]
    have hmem : ∀ b, (redStep1 s v).2 = some b → b ∈ I.N v := by
      intro b hb
      unfold redStep1 at hb
      rcases hc : s.c v with _ | b'
      · rw [hc] at hb; exact hF.p_mem v b hb
      · rw [hc] at hb
        simp only at hb
        split_ifs at hb
        · cases hb; exact hF.c_mem v _ hc
        · exact hF.p_mem v b hb
    have e2 : redStep2 s v (redStep1 s v) = redStep2 s' v (redStep1 s' v) := by
      rw [← e1]
      rcases hx : redStep1 s v with ⟨C, _ | b⟩
      · rfl
      · have hb := hmem b (by rw [hx])
        simp only [redStep2, (hN b hb).2.2]
    have hsub : (redStep2 s v (redStep1 s v)).1 ⊆ I.N v := by
      refine Subset.trans ?_ (hF.C_sub v hr)
      refine Subset.trans (redStep2_C_sub _ _ _) ?_
      unfold redStep1
      rcases s.c v with _ | b
      · exact subset_rfl
      · simp only; split_ifs
        · exact subset_rfl
        · exact erase_subset _ _
    obtain ⟨h1, h2, h3⟩ := I.redTurn_red s hr
    obtain ⟨h1', h2', h3'⟩ := I'.redTurn_red s' hr'
    refine ⟨by rw [h1, h1', e2], by rw [h2, h2', ← e2, best_congr hv hsub], by rw [h3, h3', e2]⟩

/-- **Locality.** If `I` and `I'` agree on all nodes within `k` hops of `v` and `t ≤ k`, then the
states after `t` turns agree at `v`. -/
theorem turns_agree {I I' : Bicoloured V} (t : ℕ) :
    ∀ k v, t ≤ k → AgreeBall I I' v k → StAgree (I.turns t) (I'.turns t) v := by
  induction t with
  | zero =>
    intro k v _ h
    have hv := h.agreeAt
    refine ⟨?_, rfl, rfl⟩
    simp only [turns, init_C]; rw [hv.1, hv.2.2]
  | succ t ih =>
    intro k v htk h
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hv := h.1
    have hsv := ih (k + 1) v (by omega) h
    have hN : ∀ u ∈ I.N v, StAgree (I.turns t) (I'.turns t) u :=
      fun u hu => ih k u (by omega) (h.2 u hu)
    simp only [turns]
    split_ifs
    · exact blueTurn_agree (I.nbrFacts_turns t) hv hsv hN
    · exact redTurn_agree (I.nbrFacts_turns t) hv hsv hN

lemma agreeBall_of_closedBall {I I' : Bicoloured V} (k : ℕ) :
    ∀ v, (∀ u ∈ I.graph.closedBall v k, AgreeAt I I' u) → AgreeBall I I' v k := by
  induction k with
  | zero => intro v h; exact h v (by simp)
  | succ k ih =>
    intro v h
    refine ⟨h v (I.graph.mem_closedBall_self), fun u hu => ih u fun x hx => h x ?_⟩
    rw [SimpleGraph.mem_closedBall'] at hx ⊢
    have := I.graph.edist_le_add_one_of_adj (u := x) (show I.graph.Adj v u from hu).symm
    rw [SimpleGraph.edist_comm] at hx
    calc I.graph.edist v x = I.graph.edist x v := SimpleGraph.edist_comm
      _ ≤ I.graph.edist x u + 1 := this
      _ ≤ (k : ℕ∞) + 1 := by gcongr
      _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- **Locality of `M_j`** (§6.3): whether and with whom `v` is matched at the end of round `j`
depends only on the local data (neighbours, preferences, colours) of the nodes within distance `2j`
of `v`. -/
theorem run_congr_of_agree {I I' : Bicoloured V} (j : ℕ) (v : V)
    (h : ∀ u ∈ I.graph.closedBall v (2 * j : ℕ), AgreeAt I I' u) :
    (I.run j).p v = (I'.run j).p v := by
  have := turns_agree (I := I) (I' := I') (2 * j) (2 * j) v le_rfl (agreeBall_of_closedBall _ v h)
  rw [turns_two_mul, turns_two_mul] at this
  exact this.2.2

end Bicoloured

end Podc.TruncatedGaleShapley
