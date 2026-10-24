import Papers.PODC2023.TreeExplorationBFDN.Main

/-!
# Non-vacuity: BFDN executions exist

Every configuration has a successor under `Round` (for every set of robots allowed to move): the
sequential decisions of Algorithm 1 can always be made. Hence executions exist for every tree,
every number of robots and every break-down pattern (`exists_exec`), and Theorem 2.1 is not
vacuous.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem load_congr {c : Config V k} {na na' : Fin k → V} {i : Fin k}
    (h : ∀ j < i, na j = na' j) (v : V) : load c na i v = load c na' i v := by
  unfold load curAnchor
  congr 1; ext j
  simp only [mem_filter, mem_univ, true_and]
  split_ifs with hj
  · rw [h j hj]
  · rfl

omit [Fintype V] in
theorem reanchorOK_congr {act : Finset (Fin k)} {c : Config V k} {na na' : Fin k → V} {i : Fin k}
    (h : ∀ j ≤ i, na j = na' j) : ReanchorOK T act c na i ↔ ReanchorOK T act c na' i := by
  have hl : ∀ v, load c na i v = load c na' i v := load_congr (fun j hj => h j hj.le)
  have hi := h i le_rfl
  unfold ReanchorOK
  simp only [hl, hi]

omit [Fintype V] in
theorem moveOK_congr {act : Finset (Fin k)} {c : Config V k} {na tgt tgt' : Fin k → V} {i : Fin k}
    (h : ∀ j ≤ i, tgt j = tgt' j) : MoveOK T act c na tgt i ↔ MoveOK T act c na tgt' i := by
  have hf : ∀ w, FreeDangling T c tgt i w ↔ FreeDangling T c tgt' i w := by
    intro w; unfold FreeDangling
    constructor
    · rintro ⟨a, b, d, f⟩; exact ⟨a, b, d, fun j hj => (h j hj.le) ▸ f j hj⟩
    · rintro ⟨a, b, d, f⟩; exact ⟨a, b, d, fun j hj => (h j hj.le).symm ▸ f j hj⟩
  have hi := h i le_rfl
  unfold MoveOK
  simp only [hf, hi]

theorem exists_na (act : Finset (Fin k)) (c : Config V k) :
    ∃ na : Fin k → V, ∀ i, ReanchorOK T act c na i := by
  classical
  suffices H : ∀ m ≤ k, ∃ na : Fin k → V, ∀ i : Fin k, i.val < m → ReanchorOK T act c na i by
    obtain ⟨na, h⟩ := H k le_rfl; exact ⟨na, fun i => h i i.isLt⟩
  intro m
  induction m with
  | zero => intro _; exact ⟨c.anchor, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨na, hna⟩ := ih (by omega)
    set i0 : Fin k := ⟨m, by omega⟩
    -- the value chosen for robot `i0`
    have hv : ∃ v, ReanchorOK T act c (Function.update na i0 v) i0 := by
      by_cases hr : i0 ∈ act ∧ c.pos i0 = T.root
      · by_cases hex : ∃ v, IsCand T c v
        · obtain ⟨v, hv, hmin⟩ := (univ.filter fun v => IsCand T c v).exists_min_image
            (load c na i0) (by obtain ⟨v, hv⟩ := hex; exact ⟨v, by simpa using hv⟩)
          simp only [mem_filter, mem_univ, true_and] at hv hmin
          refine ⟨v, ?_⟩
          unfold ReanchorOK
          rw [ite_eq_left hr]
          have hl : ∀ u, load c (Function.update na i0 v) i0 u = load c na i0 u :=
            fun u => (load_congr (fun j hj => Function.update_of_ne (ne_of_lt hj) _ _) u)
          simp only [hl, Function.update_self]
          exact ⟨fun _ => ⟨hv, hmin⟩, fun h => absurd hex h⟩
        · refine ⟨T.root, ?_⟩
          unfold ReanchorOK
          rw [ite_eq_left hr]
          simp only [Function.update_self]
          exact ⟨fun h => absurd h hex, fun _ => by first | rfl | trivial⟩
      · refine ⟨c.anchor i0, ?_⟩
        unfold ReanchorOK
        rw [ite_eq_right hr]
        simp
    obtain ⟨v, hv⟩ := hv
    refine ⟨Function.update na i0 v, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · have hcongr : ∀ j ≤ i, na j = Function.update na i0 v j := by
        intro j hj
        have hne : j ≠ i0 := by
          intro h'; rw [h'] at hj; have := Fin.le_def.1 hj; simp only [i0] at this; omega
        rw [Function.update_of_ne hne]
      exact (reanchorOK_congr hcongr).1 (hna i hi)
    · have : i = i0 := Fin.ext hi
      rw [this]; exact hv

theorem exists_tgt (act : Finset (Fin k)) (c : Config V k) (na : Fin k → V) :
    ∃ tgt : Fin k → V, ∀ i, MoveOK T act c na tgt i := by
  classical
  suffices H : ∀ m ≤ k, ∃ tgt : Fin k → V, ∀ i : Fin k, i.val < m → MoveOK T act c na tgt i by
    obtain ⟨tgt, h⟩ := H k le_rfl; exact ⟨tgt, fun i => h i i.isLt⟩
  intro m
  induction m with
  | zero => intro _; exact ⟨c.pos, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨tgt, htgt⟩ := ih (by omega)
    set i0 : Fin k := ⟨m, by omega⟩
    have hfd : ∀ v w, FreeDangling T c (Function.update tgt i0 v) i0 w ↔ FreeDangling T c tgt i0 w := by
      intro v w; unfold FreeDangling
      constructor
      · rintro ⟨a, b, d, f⟩
        exact ⟨a, b, d, fun j hj => by have := f j hj; rwa [Function.update_of_ne (ne_of_lt hj)] at this⟩
      · rintro ⟨a, b, d, f⟩
        exact ⟨a, b, d, fun j hj => by rw [Function.update_of_ne (ne_of_lt hj)]; exact f j hj⟩
    have hv : ∃ v, MoveOK T act c na (Function.update tgt i0 v) i0 := by
      by_cases hi : i0 ∈ act
      · by_cases hb : bf0 T act c na i0 = true
        · refine ⟨towards T (c.pos i0) (na i0), ?_⟩
          unfold MoveOK; rw [ite_eq_left hi, ite_eq_left hb]; simp
        · by_cases hex : ∃ w, FreeDangling T c tgt i0 w
          · obtain ⟨w, hw⟩ := hex
            refine ⟨w, ?_⟩
            unfold MoveOK; rw [ite_eq_left hi, ite_eq_right hb]
            simp only [hfd, Function.update_self]
            exact ⟨fun _ => hw, fun h => absurd ⟨w, hw⟩ h⟩
          · refine ⟨T.parent (c.pos i0), ?_⟩
            unfold MoveOK; rw [ite_eq_left hi, ite_eq_right hb]
            simp only [hfd, Function.update_self]
            exact ⟨fun h => absurd h hex, fun _ => by first | rfl | trivial⟩
      · refine ⟨c.pos i0, ?_⟩
        unfold MoveOK; rw [ite_eq_right hi]; simp
    obtain ⟨v, hv⟩ := hv
    refine ⟨Function.update tgt i0 v, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · have hcongr : ∀ j ≤ i, tgt j = Function.update tgt i0 v j := by
        intro j hj
        have hne : j ≠ i0 := by
          intro h'; rw [h'] at hj; have := Fin.le_def.1 hj; simp only [i0] at this; omega
        rw [Function.update_of_ne hne]
      exact (moveOK_congr hcongr).1 (htgt i hi)
    · have : i = i0 := Fin.ext hi
      rw [this]; exact hv

/-- Every configuration has a successor under `Round`. -/
theorem exists_round (act : Finset (Fin k)) (c : Config V k) : ∃ c', Round T act c c' := by
  obtain ⟨na, hna⟩ := exists_na (T := T) act c
  obtain ⟨tgt, htgt⟩ := exists_tgt (T := T) act c na
  exact ⟨_, na, tgt, hna, htgt, rfl⟩

/-- BFDN executions exist, for every break-down pattern `act`. -/
theorem exists_exec (act : ℕ → Finset (Fin k)) : ∃ e : ℕ → Config V k, IsExec T act e := by
  classical
  let next : ℕ → Config V k → Config V k := fun t c => Classical.choose (exists_round (T := T) (act t) c)
  let e : ℕ → Config V k := fun t => Nat.rec (init T k) (fun t c => next t c) t
  exact ⟨e, rfl, fun t => Classical.choose_spec (exists_round (T := T) (act t) (e t))⟩

/-- Synchronous BFDN executions exist (non-vacuity of Theorem 2.1). -/
theorem exists_syncExec : ∃ e : ℕ → Config V k, IsSyncExec T e := exists_exec _

end Podc.TreeExplorationBFDN
