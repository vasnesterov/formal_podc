import Papers.PODC2025.GeneralizedQuorums.Defs

/-!
# Examples: Figure 1, the reading of "strongly connected", non-uniqueness of `U_f`

* `figure_1_isGQS` (Examples 2, 7, 8): the fail-prone system of Figure 1 with read quorums
  `R_i` and write quorums `W_i` is a generalized quorum system; no read quorum is strongly
  connected (`figure_1_R1_not_stronglyConnected`).
* `proposition_1_false_induced`: Proposition 1 is false if "strongly connected" is read as
  "the induced subgraph is strongly connected": the union `U` of the available write quorums may
  only be strongly connected through processes outside `U`. With the reading used throughout
  (mutual reachability in `G \ f`, as in the proof and in the definition of `U_f`) it holds.
* `Uf_not_unique`: `U_f` depends on the chosen quorum system, not only on `F`.
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures

variable {P : Type}

/-- A set closed under successors (avoiding `X`) cannot be left by walks avoiding `X`. -/
lemma not_reachableAvoiding_of_closed {G : Digraph P} {X S : Set P}
    (hS : ∀ a b, G.Adj a b → a ∉ X → b ∉ X → a ∈ S → b ∈ S) {u v : P} (hu : u ∈ S)
    (hv : v ∉ S) : ¬ G.ReachableAvoiding X u v := by
  rintro ⟨-, h⟩
  have : ∀ w, Relation.ReflTransGen (G.deleteVerts X).Adj u w → w ∈ S := by
    intro w hw
    induction hw with
    | refl => exact hu
    | tail _ e ih => exact hS _ _ e.1 e.2.1 e.2.2 ih
  exact hv (this v h)

/-- A set closed under successors in `G \ f` cannot be left. -/
lemma not_reach_of_closed {f : FailurePattern P} {S : Set P}
    (hS : ∀ a b, f.Edge a b → a ∈ S → b ∈ S) {u v : P} (hu : u ∈ S) (hv : v ∉ S) :
    ¬ f.Reach u v :=
  not_reachableAvoiding_of_closed (fun a b e ha hb => hS a b ⟨ha, hb, e⟩) hu hv

/-! ### Figure 1 -/

section Figure1

/-- Processes `a, b, c, d` of Figure 1 are `0, 1, 2, 3`. -/
abbrev Q4 := Fin 4

/-- The failure pattern `f_i` of Figure 1 (`i = 0..3`, i.e. `f₁..f₄`): process `i + 3` may crash;
among the others only the channels `(i+2, i)`, `(i, i+1)`, `(i+1, i)` are reliable. -/
def fig1 (i : Fin 4) : FailurePattern Q4 where
  procs := {i + 3}
  chans := {e | e.1 ≠ i + 3 ∧ e.2 ≠ i + 3 ∧ e.1 ≠ e.2 ∧
    e ≠ (i + 2, i) ∧ e ≠ (i, i + 1) ∧ e ≠ (i + 1, i)}

/-- Read quorums `R_i = {i, i + 2}`. -/
def fig1R (i : Fin 4) : Set Q4 := {i, i + 2}

/-- Write quorums `W_i = {i, i + 1}`. -/
def fig1W (i : Fin 4) : Set Q4 := {i, i + 1}

lemma fig1_edge (i : Fin 4) {a b : Q4} (h : (a, b) = (i + 2, i) ∨ (a, b) = (i, i + 1) ∨
    (a, b) = (i + 1, i)) : (fig1 i).Edge a b := by
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;>
    fin_cases i <;> simp [FailurePattern.Edge, fig1]

/-- **Examples 2 and 8.** `(F, R, W)` of Figure 1 is a generalized quorum system. -/
theorem figure_1_isGQS :
    IsGQS (Set.range fig1) (Set.range fig1R) (Set.range fig1W) := by
  refine ⟨?_, ?_⟩
  · rintro r ⟨i, rfl⟩ w ⟨j, rfl⟩
    fin_cases i <;> fin_cases j <;> simp [fig1R, fig1W, Set.Nonempty]
  · rintro f ⟨i, rfl⟩
    have e1 := fig1_edge i (a := i + 2) (b := i) (Or.inl rfl)
    have e2 := fig1_edge i (a := i) (b := i + 1) (Or.inr (Or.inl rfl))
    have e3 := fig1_edge i (a := i + 1) (b := i) (Or.inr (Or.inr rfl))
    have r12 := reach_of_edge e2
    have r21 := reach_of_edge e3
    have r31 := reach_of_edge e1
    have r11 := reach_refl e2.1
    have r22 := reach_refl e2.2.1
    refine ⟨fig1W i, ⟨i, rfl⟩, fig1R i, ⟨i, rfl⟩, ?_, ?_, ?_, ?_⟩
    · simp only [Available, fig1W, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro u (rfl | rfl) v (rfl | rfl) <;> assumption
    · simp only [fig1W, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro w (rfl | rfl)
      · exact e2.1
      · exact e2.2.1
    · simp only [fig1R, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro r (rfl | rfl)
      · exact e2.1
      · exact e1.1
    · simp only [fig1R, fig1W, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro r (rfl | rfl) w (rfl | rfl)
      · exact r11
      · exact r12
      · exact r31
      · exact reach_trans r31 r12

/-- **Example 2.** The read quorum `R₁ = {a, c}` is not strongly connected under `f₁`: `a` cannot
reach `c`. -/
theorem figure_1_R1_not_stronglyConnected : ¬ (fig1 0).Reach 0 2 := by
  refine not_reach_of_closed (S := {0, 1}) ?_ (by simp) (by decide)
  intro a b he ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  revert he
  rcases ha with rfl | rfl <;> fin_cases b <;> simp [FailurePattern.Edge, fig1]


/-- `f₁'` of Example 9: `f₁` where the channel `(a, b)` may also fail. -/
def fig1' : FailurePattern Q4 := ⟨{3}, (fig1 0).chans ∪ {(0, 1)}⟩

lemma fig1'_pred {z : Q4} (hz : z = 1 ∨ z = 2) : ∀ a b : Q4, fig1'.residual.Adj a b →
    a ∉ fig1'.procs → b ∈ ({z} : Set Q4) → a ∈ ({z} : Set Q4) := by
  intro a b h ha hb
  simp only [Set.mem_singleton_iff] at hb ⊢
  subst hb
  rcases hz with rfl | rfl <;> fin_cases a <;>
    simp_all [fig1', fig1, FailurePattern.residual]

/-- In `G \ f₁'`, only `b` reaches `b`, only `c` reaches `c`, and `a` reaches only `a`. -/
lemma fig1'_reach {x y : Q4} (h : fig1'.Reach x y) :
    (y = 1 → x = 1) ∧ (y = 2 → x = 2) ∧ (x = 0 → y = 0) := by
  refine ⟨fun hy => ?_, fun hy => ?_, fun hx => ?_⟩
  · subst hy
    have := Digraph.ReachableAvoiding.mem_of_closed (L := ({1} : Set Q4))
      (fig1'_pred (Or.inl rfl)) (show fig1'.residual.ReachableAvoiding fig1'.procs x 1 from h) rfl
    simpa using this
  · subst hy
    have := Digraph.ReachableAvoiding.mem_of_closed (L := ({2} : Set Q4))
      (fig1'_pred (Or.inr rfl)) (show fig1'.residual.ReachableAvoiding fig1'.procs x 2 from h) rfl
    simpa using this
  · subst hx
    by_contra hy
    refine not_reach_of_closed (S := {0}) ?_ rfl hy h
    intro a b he ha
    simp only [Set.mem_singleton_iff] at ha ⊢
    subst ha
    fin_cases b <;> simp_all [fig1', fig1, FailurePattern.Edge]

/-- **Example 9.** If `f₁` is replaced by `f₁'` (the channel `(a, b)` may also fail), the
fail-prone system has no generalized quorum system. -/
theorem example_9 : ¬ ∃ R W : Set (Set Q4), IsGQS {fig1', fig1 1, fig1 2, fig1 3} R W := by
  rintro ⟨R, W, hQ⟩
  obtain ⟨w₁, hw₁, r₁, hr₁, hav₁, hre₁⟩ := hQ.availability fig1' (by simp)
  obtain ⟨x, hxr, hxw⟩ := hQ.consistency r₁ hr₁ w₁ hw₁
  have hx3 : x ≠ 3 := fun h => hre₁.1 x hxw (by simp [h, fig1'])
  -- members of `r₁` reach `x`
  have hreach : ∀ r ∈ r₁, fig1'.Reach r x := fun r hr => hre₁.2.2 r hr x hxw
  fin_cases x
  · -- `x = a`: `w₁ = {a}`, but `a` crashes in `f₂`
    obtain ⟨w₂, hw₂, r₂, hr₂, -, hre₂⟩ := hQ.availability (fig1 1) (by simp)
    obtain ⟨y, hyr, hyw⟩ := hQ.consistency r₂ hr₂ w₁ hw₁
    have hy : y = 0 := (fig1'_reach (hav₁ _ hxw y hyw)).2.2 rfl
    exact hre₂.2.1 y hyr (by simp [hy, fig1])
  · -- `x = b`: `r₁ = {b}`, but `b` crashes in `f₃`
    obtain ⟨w₃, hw₃, r₃, hr₃, -, hre₃⟩ := hQ.availability (fig1 2) (by simp)
    obtain ⟨y, hyr, hyw⟩ := hQ.consistency r₁ hr₁ w₃ hw₃
    have hy : y = 1 := (fig1'_reach (hreach y hyr)).1 rfl
    exact hre₃.1 y hyw (by simp [hy, fig1])
  · -- `x = c`: `r₁ = {c}`, but `c` crashes in `f₄`
    obtain ⟨w₄, hw₄, r₄, hr₄, -, hre₄⟩ := hQ.availability (fig1 3) (by simp)
    obtain ⟨y, hyr, hyw⟩ := hQ.consistency r₁ hr₁ w₄ hw₄
    have hy : y = 2 := (fig1'_reach (hreach y hyr)).2.1 rfl
    exact hre₄.1 y hyw (by simp [hy, fig1])
  · exact absurd rfl hx3

end Figure1

/-! ### Proposition 1 needs mutual reachability in `G \ f` -/

section Induced

/-- The failure pattern on `{0, 1, 2}` disconnecting `0 ↔ 1` (channels via `2` stay). -/
def fInd : FailurePattern (Fin 3) where
  procs := ∅
  chans := {(0, 1), (1, 0)}

/-- `({fInd}, {{0, 1}}, {{0}, {1}})` is a generalized quorum system. -/
theorem induced_isGQS : IsGQS {fInd} {{0, 1}} {{0}, {1}} := by
  have edge : ∀ a b : Fin 3, (a, b) ∉ fInd.chans → fInd.Edge a b := fun a b h => ⟨by simp [fInd],
    by simp [fInd], h⟩
  have r02 := reach_of_edge (edge 0 2 (by simp [fInd]))
  have r20 := reach_of_edge (edge 2 0 (by simp [fInd]))
  have r12 := reach_of_edge (edge 1 2 (by simp [fInd]))
  have r21 := reach_of_edge (edge 2 1 (by simp [fInd]))
  have r00 : fInd.Reach 0 0 := reach_refl (by simp [fInd])
  have r11 : fInd.Reach 1 1 := reach_refl (by simp [fInd])
  refine ⟨?_, ?_⟩
  · rintro r rfl w (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro f rfl
    refine ⟨{0}, by simp, {0, 1}, by simp, ?_, ?_, ?_, ?_⟩
    · rintro u rfl v rfl; exact r00
    · intro w _; simp [fInd]
    · intro r _; simp [fInd]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro r (rfl | rfl) w rfl
      · exact r00
      · exact reach_trans r12 r20

/-- **Proposition 1 fails for the "induced subgraph" reading of strong connectivity.** In the
quorum system above, `U = {0, 1}`, but `0` cannot reach `1` inside `U` (only through `2`). -/
theorem proposition_1_false_induced :
    0 ∈ U {{0, 1}} {{0}, {1}} fInd ∧ 1 ∈ U {{0, 1}} {{0}, {1}} fInd ∧
      ¬ fInd.residual.ReachableAvoiding (fInd.procs ∪ {2}) 0 1 := by
  have edge : ∀ a b : Fin 3, (a, b) ∉ fInd.chans → fInd.Edge a b := fun a b h => ⟨by simp [fInd],
    by simp [fInd], h⟩
  have r02 := reach_of_edge (edge 0 2 (by simp [fInd]))
  have r20 := reach_of_edge (edge 2 0 (by simp [fInd]))
  have r12 := reach_of_edge (edge 1 2 (by simp [fInd]))
  have r21 := reach_of_edge (edge 2 1 (by simp [fInd]))
  have r00 : fInd.Reach 0 0 := reach_refl (by simp [fInd])
  have r11 : fInd.Reach 1 1 := reach_refl (by simp [fInd])
  have hR : ∀ x : Fin 3, x ∉ fInd.procs := fun x => by simp [fInd]
  refine ⟨⟨{0}, ⟨by simp, ?_, {0, 1}, by simp, ?_⟩, rfl⟩,
    ⟨{1}, ⟨by simp, ?_, {0, 1}, by simp, ?_⟩, rfl⟩, ?_⟩
  · rintro u rfl v rfl; exact r00
  · refine ⟨fun w _ => hR w, fun r _ => hR r, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro r (rfl | rfl) w rfl
    · exact r00
    · exact reach_trans r12 r20
  · rintro u rfl v rfl; exact r11
  · refine ⟨fun w _ => hR w, fun r _ => hR r, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro r (rfl | rfl) w rfl
    · exact reach_trans r02 r21
    · exact r11
  · refine not_reachableAvoiding_of_closed (S := {0}) ?_ rfl (by decide)
    intro a b e ha hb hS
    simp only [Set.mem_singleton_iff] at hS ⊢
    subst hS
    simp only [FailurePattern.residual, fInd, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.empty_union] at e hb
    fin_cases b <;> simp_all

end Induced

end Podc.GeneralizedQuorums
