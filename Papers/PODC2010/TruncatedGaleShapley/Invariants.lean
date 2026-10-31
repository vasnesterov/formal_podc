import Papers.PODC2010.TruncatedGaleShapley.Basic

/-!
# Invariants of the truncated Gale–Shapley algorithm

The states `run I i`, `i ≥ 1`, satisfy the invariant `Inv`: the partner function is a matching, a
matched red node is matched to the head of its candidate list, an unmatched red node has an
outstanding proposal to the head of its candidate list, and a blue node `b` removed from the list
of a red node `r` is matched to a node it strictly prefers to `r`.

`red_outcome` describes what happens to a red node in one round (unchanged, accepted, or one
lost edge).
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

namespace Bicoloured

variable (I : Bicoloured V)

/-! ### Basic simp lemmas -/

@[simp] lemma blueTurn_C (s : State V) : (I.blueTurn s).C = s.C := rfl
@[simp] lemma blueTurn_c (s : State V) : (I.blueTurn s).c = s.c := rfl

lemma blueTurn_p_red (s : State V) {v : V} (hv : I.red v = true) : (I.blueTurn s).p v = s.p v := by
  simp [blueTurn, hv]

lemma blueTurn_p_empty (s : State V) {v : V} (hv : ¬ (I.proposers s v).Nonempty) :
    (I.blueTurn s).p v = s.p v := by
  simp [blueTurn, hv]

lemma blueTurn_p_nonempty (s : State V) {v : V} (hv : I.red v = false)
    (hP : (I.proposers s v).Nonempty) :
    (I.blueTurn s).p v = I.best v (I.proposers s v ∪ (s.p v).toFinset) := by
  simp [blueTurn, hv, hP]

lemma mem_proposers {s : State V} {b r : V} : r ∈ I.proposers s b ↔ r ∈ I.N b ∧ s.c r = some b := by
  simp [proposers]

lemma redTurn_blue (s : State V) {v : V} (hv : I.red v = false) :
    (I.redTurn s).C v = s.C v ∧ (I.redTurn s).c v = s.c v ∧ (I.redTurn s).p v = s.p v := by
  simp [redTurn, hv]

lemma redTurn_red (s : State V) {v : V} (hv : I.red v = true) :
    (I.redTurn s).C v = (redStep2 s v (redStep1 s v)).1 ∧
    (I.redTurn s).c v = (if (redStep2 s v (redStep1 s v)).2 = none then
        I.best v (redStep2 s v (redStep1 s v)).1 else none) ∧
    (I.redTurn s).p v = (redStep2 s v (redStep1 s v)).2 := by
  simp [redTurn, hv]

lemma round_p_blue (s : State V) {v : V} (hv : I.red v = false) :
    (I.round s).p v = (I.blueTurn s).p v := (I.redTurn_blue _ hv).2.2

lemma round_C_blue (s : State V) {v : V} (hv : I.red v = false) :
    (I.round s).C v = s.C v := (I.redTurn_blue _ hv).1

/-! ### The state after round 1 -/

@[simp] lemma init_C (v : V) : I.init.C v = if I.red v then I.N v else ∅ := rfl
@[simp] lemma init_c (v : V) : I.init.c v = none := rfl
@[simp] lemma init_p (v : V) : I.init.p v = none := rfl

lemma blueTurn_init_p : (I.blueTurn I.init).p = fun _ => none := by
  funext v
  rw [blueTurn_p_empty]
  · rfl
  · simp [proposers, init]

lemma run_zero : I.run 0 = I.init := rfl

lemma run_one_C (v : V) : (I.run 1).C v = I.init.C v := by
  rw [run_succ, run_zero]
  by_cases hv : I.red v
  · simp [round, redTurn, hv, redStep1, redStep2, blueTurn_init_p]
  · simp [round, redTurn, hv]

lemma run_one_p (v : V) : (I.run 1).p v = none := by
  rw [run_succ, run_zero]
  by_cases hv : I.red v
  · simp [round, redTurn, redStep1, redStep2, blueTurn_init_p]
  · have hv' : I.red v = false := by simpa using hv
    rw [round_p_blue _ _ hv', blueTurn_init_p]

lemma run_one_c (v : V) : (I.run 1).c v = if I.red v then I.best v (I.N v) else none := by
  rw [run_succ, run_zero]
  by_cases hv : I.red v
  · simp [round, redTurn, hv, redStep1, redStep2, blueTurn_init_p]
  · simp [round, redTurn, hv]

/-! ### The invariant -/

/-- The invariant of the states at the end of rounds `i ≥ 1`. -/
structure Inv (s : State V) : Prop where
  C_sub : ∀ r, I.red r = true → s.C r ⊆ I.N r
  p_mem : ∀ u v, s.p u = some v → v ∈ I.N u
  p_symm : ∀ u v, s.p u = some v → s.p v = some u
  red_unmatched : ∀ r, I.red r = true → s.p r = none → s.c r = I.best r (s.C r)
  red_matched : ∀ r b, I.red r = true → s.p r = some b → s.c r = none ∧ I.best r (s.C r) = some b
  lost : ∀ r b, I.red r = true → b ∈ I.N r → b ∉ s.C r →
    ∃ r₀, s.p b = some r₀ ∧ I.rank b r₀ < I.rank b r

lemma inv_run_one : I.Inv (I.run 1) where
  C_sub r hr := by simp [run_one_C, init, hr]
  p_mem u v h := by simp [run_one_p] at h
  p_symm u v h := by simp [run_one_p] at h
  red_unmatched r hr _ := by simp [run_one_C, run_one_c, init, hr]
  red_matched r b _ h := by simp [run_one_p] at h
  lost r b hr hb h := by simp [run_one_C, init, hr, hb] at h

variable {I}

lemma red_of_mem_blue {u v : V} (h : v ∈ I.N u) (hu : I.red u = false) : I.red v = true := by
  have := I.red_ne h; simp_all

lemma blue_of_mem_red {u v : V} (h : v ∈ I.N u) (hu : I.red u = true) : I.red v = false := by
  have := I.red_ne h; simp_all

/-- A matched red node has no outstanding proposal. -/
lemma Inv.c_eq_none {s : State V} (hs : I.Inv s) {r b : V} (hr : I.red r = true)
    (h : s.p r = some b) : s.c r = none := (hs.red_matched r b hr h).1

/-- The blue turn: a matched blue node stays matched with a node it does not like less. -/
lemma Inv.blue_mono {s : State V} (_hs : I.Inv s) {b r₀ : V} (hb : I.red b = false)
    (h : s.p b = some r₀) : ∃ q, (I.blueTurn s).p b = some q ∧ I.rank b q ≤ I.rank b r₀ := by
  by_cases hP : (I.proposers s b).Nonempty
  · rw [I.blueTurn_p_nonempty s hb hP]
    obtain ⟨q, hq⟩ := I.best_isSome (v := b) (hP.mono subset_union_left)
    exact ⟨q, hq, (I.best_spec hq).2 r₀ (by simp [h])⟩
  · rw [I.blueTurn_p_empty s hP, h]; exact ⟨r₀, rfl, le_rfl⟩

/-- The blue turn: if `r ∈ P ∪ {p(b)}`, then `b` ends up matched to a node `q` it does not like
less than `r`, and `q = r` or `b` strictly prefers `q`. -/
lemma Inv.blue_of_mem_Q {s : State V} (hs : I.Inv s) {b r : V} (hb : I.red b = false)
    (hr : r ∈ I.proposers s b ∨ s.p b = some r) :
    ∃ q, (I.blueTurn s).p b = some q ∧ (q = r ∨ I.rank b q < I.rank b r) := by
  have hsub : I.proposers s b ∪ (s.p b).toFinset ⊆ I.N b := by
    intro x hx
    rcases mem_union.1 hx with hx | hx
    · exact (I.mem_proposers.1 hx).1
    · exact hs.p_mem b x (by simpa using hx)
  have hrQ : r ∈ I.proposers s b ∪ (s.p b).toFinset := by
    rcases hr with hr | hr
    · exact mem_union_left _ hr
    · exact mem_union_right _ (by simp [hr])
  by_cases hP : (I.proposers s b).Nonempty
  · rw [I.blueTurn_p_nonempty s hb hP]
    obtain ⟨q, hq⟩ := I.best_isSome (v := b) ⟨r, hrQ⟩
    refine ⟨q, hq, ?_⟩
    have hle := (I.best_spec hq).2 r hrQ
    rcases hle.lt_or_eq with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl (I.rank_inj (hsub (I.best_mem hq)) (hsub hrQ) heq)
  · rcases hr with hr | hr
    · exact absurd ⟨r, hr⟩ hP
    · rw [I.blueTurn_p_empty s hP, hr]; exact ⟨r, rfl, Or.inl rfl⟩

/-- After the blue turn, a blue node points to a neighbour. -/
lemma Inv.blueTurn_p_mem {s : State V} (hs : I.Inv s) {u v : V} (hu : I.red u = false)
    (h : (I.blueTurn s).p u = some v) : v ∈ I.N u := by
  by_cases hP : (I.proposers s u).Nonempty
  · rw [I.blueTurn_p_nonempty s hu hP] at h
    rcases mem_union.1 (I.best_mem h) with hx | hx
    · exact (I.mem_proposers.1 hx).1
    · exact hs.p_mem u v (by simpa using hx)
  · rw [I.blueTurn_p_empty s hP] at h; exact hs.p_mem u v h

/-- After the blue turn, a blue node `u` points to a proposer or to its old partner. -/
lemma Inv.blue_choice {s : State V} (hs : I.Inv s) {u v : V} (hu : I.red u = false)
    (h : (I.blueTurn s).p u = some v) : s.c v = some u ∨ s.p v = some u := by
  by_cases hP : (I.proposers s u).Nonempty
  · rw [I.blueTurn_p_nonempty s hu hP] at h
    rcases mem_union.1 (I.best_mem h) with hx | hx
    · exact Or.inl (I.mem_proposers.1 hx).2
    · exact Or.inr (hs.p_symm u v (by simpa using hx))
  · rw [I.blueTurn_p_empty s hP] at h; exact Or.inr (hs.p_symm u v h)

/-- What happens to a red node in one round. Either nothing changes (`r` is matched and not
dumped, or `r` is unmatched with an empty list), or its proposal is accepted, or it loses the
head `b` of its list (a 'reject' or a 'break'). -/
lemma Inv.red_outcome {s : State V} (hs : I.Inv s) {r : V} (hr : I.red r = true) :
    ((I.round s).C r = s.C r ∧ (I.round s).p r = s.p r ∧ (I.round s).c r = s.c r ∧
        ((∃ b, s.p r = some b ∧ (I.blueTurn s).p b = some r) ∨
          (s.p r = none ∧ s.c r = none ∧ s.C r = ∅))) ∨
      (∃ b, s.p r = none ∧ s.c r = some b ∧ (I.blueTurn s).p b = some r ∧
        (I.round s).C r = s.C r ∧ (I.round s).p r = some b ∧ (I.round s).c r = none) ∨
      (∃ b, I.best r (s.C r) = some b ∧ (s.c r = some b ∨ s.p r = some b) ∧
        (I.blueTurn s).p b ≠ some r ∧
        (I.round s).C r = (s.C r).erase b ∧ (I.round s).p r = none ∧
        (I.round s).c r = I.best r ((s.C r).erase b)) := by
  have hC : (I.round s).C r = (redStep2 (I.blueTurn s) r (redStep1 (I.blueTurn s) r)).1 := by
    simp [round, redTurn, hr]
  have hp : (I.round s).p r = (redStep2 (I.blueTurn s) r (redStep1 (I.blueTurn s) r)).2 := by
    simp [round, redTurn, hr]
  have hc : (I.round s).c r = if (redStep2 (I.blueTurn s) r (redStep1 (I.blueTurn s) r)).2 = none
      then I.best r (redStep2 (I.blueTurn s) r (redStep1 (I.blueTurn s) r)).1 else none := by
    simp [round, redTurn, hr]
  have hpr : (I.blueTurn s).p r = s.p r := I.blueTurn_p_red s hr
  rcases hpm : s.p r with _ | b
  · -- unmatched
    have hcr := hs.red_unmatched r hr hpm
    rcases hcm : s.c r with _ | b
    · left
      have hCe : s.C r = ∅ := I.best_eq_none.1 (hcr ▸ hcm).symm.symm
      simp only [redStep1, blueTurn_c, hcm, blueTurn_C, hpr, hpm, redStep2] at hC hp hc
      simp [hC, hp, hc, hCe, I.best_eq_none]
    · by_cases hacc : (I.blueTurn s).p b = some r
      · right; left
        simp only [redStep1, blueTurn_c, hcm, hacc, ite_true, blueTurn_C, redStep2] at hC hp hc
        exact ⟨b, rfl, rfl, hacc, hC, hp, by simp [hc]⟩
      · right; right
        simp only [redStep1, blueTurn_c, hcm, hacc, ite_false, blueTurn_C, hpr, hpm, redStep2]
          at hC hp hc
        exact ⟨b, (hcr ▸ hcm).symm.symm, Or.inl rfl, hacc, hC, hp, by simp [hc]⟩
  · -- matched to `b`
    have ⟨hcr, hbest⟩ := hs.red_matched r b hr hpm
    by_cases hbrk : (I.blueTurn s).p b = some r
    · left
      simp only [redStep1, blueTurn_c, hcr, blueTurn_C, hpr, hpm, redStep2, hbrk, ite_true]
        at hC hp hc
      exact ⟨hC, hp, by simp [hc, hcr], Or.inl ⟨b, rfl, hbrk⟩⟩
    · right; right
      simp only [redStep1, blueTurn_c, hcr, blueTurn_C, hpr, hpm, redStep2, hbrk, ite_false]
        at hC hp hc
      exact ⟨b, hbest, Or.inr rfl, hbrk, hC, hp, by simp [hc]⟩

/-- The invariant is preserved by a round. -/
lemma Inv.round {s : State V} (hs : I.Inv s) : I.Inv (I.round s) where
  C_sub r hr := by
    refine Subset.trans ?_ (hs.C_sub r hr)
    rcases hs.red_outcome hr with ⟨h, -⟩ | ⟨b, -, -, -, h, -⟩ | ⟨b, -, -, -, h, -⟩ <;> rw [h]
    exact erase_subset _ _
  p_mem u v h := by
    cases hu : I.red u
    · rw [I.round_p_blue s hu] at h
      by_cases hP : (I.proposers s u).Nonempty
      · rw [I.blueTurn_p_nonempty s hu hP] at h
        rcases mem_union.1 (I.best_mem h) with hx | hx
        · exact (I.mem_proposers.1 hx).1
        · exact hs.p_mem u v (by simpa using hx)
      · rw [I.blueTurn_p_empty s hP] at h; exact hs.p_mem u v h
    · rcases hs.red_outcome hu with ⟨-, h1, -⟩ | ⟨b, hpn, hc, -, -, h1, -⟩ | ⟨b, -, -, -, -, h1, -⟩
      · exact hs.p_mem u v (h1 ▸ h)
      · rw [h1] at h; cases h
        have := hs.red_unmatched u hu hpn
        rw [hc] at this
        exact hs.C_sub u hu (I.best_mem this.symm)
      · simp [h1] at h
  p_symm u v h := by
    cases hu : I.red u
    · -- `u` blue
      rw [I.round_p_blue s hu] at h
      have hch := hs.blue_choice hu h
      have hv : I.red v = true := red_of_mem_blue (hs.blueTurn_p_mem hu h) hu
      rcases hs.red_outcome hv with
          ⟨-, h1, -, ⟨b, hb, hbt⟩ | ⟨hpn, hcn, -⟩⟩ | ⟨b, hpn, hc, hacc, -, h1, -⟩ |
          ⟨b, -, hcb, hbt, -, -, -⟩
      · rw [h1]
        rcases hch with hch | hch
        · rw [hs.c_eq_none hv hb] at hch; cases hch
        · exact hch
      · rcases hch with hch | hch
        · rw [hcn] at hch; cases hch
        · rw [hpn] at hch; cases hch
      · rw [h1]
        rcases hch with hch | hch
        · rw [hc] at hch; exact hch
        · rw [hpn] at hch; cases hch
      · exfalso
        have hub : b = u := by
          rcases hch with hch | hch <;> rcases hcb with hcb | hcb
          · rw [hcb] at hch; cases hch; rfl
          · rw [hs.c_eq_none hv hcb] at hch; cases hch
          · rw [hs.c_eq_none hv hch] at hcb; cases hcb
          · rw [hcb] at hch; cases hch; rfl
        subst hub
        exact hbt h
    · -- `u` red
      rcases hs.red_outcome hu with ⟨-, h1, -, ⟨b, hb, hbt⟩ | ⟨hpn, -⟩⟩ |
          ⟨b, hpn, hcu, hacc, -, h1, -⟩ | ⟨b, -, -, -, -, h1, -⟩
      · rw [h1, hb] at h; cases h
        rw [I.round_p_blue s (blue_of_mem_red (hs.p_mem u v hb) hu), hbt]
      · rw [h1, hpn] at h; cases h
      · rw [h1] at h; cases h
        have : v ∈ I.N u := by
          have := hs.red_unmatched u hu hpn
          rw [hcu] at this
          exact hs.C_sub u hu (I.best_mem this.symm)
        rw [I.round_p_blue s (blue_of_mem_red this hu), hacc]
      · simp [h1] at h
  red_unmatched r hr h := by
    rcases hs.red_outcome hr with ⟨hC, hp, hc, ⟨b, hb, -⟩ | ⟨-, hcn, hCe⟩⟩ |
        ⟨b, -, -, -, -, hp, -⟩ | ⟨b, -, -, -, hC, -, hc⟩
    · rw [hp, hb] at h; cases h
    · rw [hc, hC, hcn, hCe]; exact (I.best_eq_none.2 rfl).symm
    · rw [hp] at h; cases h
    · rw [hc, hC]
  red_matched r b hr h := by
    rcases hs.red_outcome hr with ⟨hC, hp, hc, -⟩ | ⟨b', hpn, hcb, -, hC, hp, hc⟩ |
        ⟨b', -, -, -, -, hp, -⟩
    · rw [hp] at h; rw [hc, hC]; exact hs.red_matched r b hr h
    · rw [hp] at h; cases h
      refine ⟨hc, ?_⟩
      rw [hC, ← hs.red_unmatched r hr hpn, hcb]
    · rw [hp] at h; cases h
  lost r b hr hb h := by
    have hbblue := blue_of_mem_red hb hr
    rw [I.round_p_blue s hbblue]
    by_cases hbs : b ∈ s.C r
    · -- `b` was lost in this round
      rcases hs.red_outcome hr with ⟨hC, -⟩ | ⟨b', -, -, -, hC, -⟩ |
          ⟨b', hbest, hcb, hbt, hC, -, -⟩
      · rw [hC] at h; exact absurd hbs h
      · rw [hC] at h; exact absurd hbs h
      · have hbb : b = b' := by
          by_contra hne; rw [hC] at h; exact h (mem_erase.2 ⟨hne, hbs⟩)
        subst hbb
        have hQ : r ∈ I.proposers s b ∨ s.p b = some r := by
          rcases hcb with hcb | hcb
          · exact Or.inl (I.mem_proposers.2 ⟨I.symm hb, hcb⟩)
          · exact Or.inr (hs.p_symm r b hcb)
        obtain ⟨q, hq, hqr⟩ := hs.blue_of_mem_Q hbblue hQ
        rcases hqr with rfl | hlt
        · exact absurd hq hbt
        · exact ⟨q, hq, hlt⟩
    · obtain ⟨r₀, h₀, hlt⟩ := hs.lost r b hr hb hbs
      obtain ⟨q, hq, hle⟩ := hs.blue_mono hbblue h₀
      exact ⟨q, hq, lt_of_le_of_lt hle hlt⟩

variable (I)

/-- The invariant holds at the end of every round `i ≥ 1`. -/
lemma inv_run {i : ℕ} (hi : 1 ≤ i) : I.Inv (I.run i) := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact I.inv_run_one
    · rw [run_succ]; exact (ih hpos).round

end Bicoloured

end Podc.TruncatedGaleShapley
