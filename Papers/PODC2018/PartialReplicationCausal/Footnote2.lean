import Papers.PODC2018.PartialReplicationCausal.Runs

/-!
# Footnote 2 is false: the algorithm does not satisfy Constraint 1

Section 4 imposes *Constraint 1*: "for any replica `i`, its timestamp at any given time is a
function of its causal past at that time", where the causal past is the *set* `S` of updates of
Definition 8 (the paper stresses that different causal dependency graphs may have the same causal
past). Footnote 2 claims: "our proposed algorithm in Section 3.2 actually satisfies this
constraint". This is false.

Six replicas `0, …, 5` and registers `a = 0, b = 1, c = 2, d = 3, e = 4`:

```
X₀ = {e, b}  X₁ = {a, b}  X₂ = {a, c}  X₃ = {c, d}  X₄ = {e, d}  X₅ = {c, e, d}
```

Here `e_25 ∈ E₀` (loop `(0, 5, 2, 1)`) but `e_25 ∉ E₄` (`X₄ ⊆ X₅` and `4` is not a neighbour
of `2`). Each of the replicas `2, 3, 4, 5` writes once: `u_c` (by 2), `u_d` (by 3), `u_e⁴` (by 4),
`u_e⁵` (by 5).

* Execution A: `2` writes `c`; `3` applies it and writes `d`; `4` applies that and writes `e`;
  `5` applies `u_c` and writes `e`; `0` applies `u_e⁴`, then `u_e⁵`.
* Execution B: `5` writes `e` first; then `2` writes `c`; `3` applies it and writes `d`; `4` applies
  `u_e⁵` and `u_d` and writes `e`; `0` applies `u_e⁵`, then `u_e⁴`.

In both, the causal past of replica `0` is `{u_c, u_d, u_e⁴, u_e⁵}`, but `τ₀[e_25] = 1` in A
(`u_e⁵` carries `u_c`, and `5` tracks `e_25`) and `τ₀[e_25] = 0` in B (`u_c` reaches `0` only
through `4`, which does not track `e_25`).
-/

namespace Podc.PartialReplicationCausal.Footnote2

open Classical

/-- The causal past of replica `i` (Definition 8): the applied updates and all updates that
happened before them. -/
def CausalPast {ι Reg : Type*} (s : State ι Reg) (i : ι) : Set ℕ :=
  {a | a ∈ s.app i ∨ ∃ b ∈ s.app i, HB s a b}

/-- Registers `a = 0, b = 1, c = 2, d = 3, e = 4`. -/
def X : Fin 6 → Set (Fin 5) := ![{4, 1}, {0, 1}, {0, 2}, {2, 3}, {4, 3}, {2, 4, 3}]

lemma adj_iff (j k : Fin 6) : Adj X j k ↔ j ≠ k ∧ ∃ x, x ∈ X j ∧ x ∈ X k := by
  simp [Adj, Set.Nonempty]

lemma adj_2_5 : Adj X 2 5 := (adj_iff _ _).2 ⟨by decide, 2, by simp [X], by simp [X]⟩

/-- `e_25 ∈ E₀`: `(0, 5, 2, 1)` is a `(0, e_25)`-loop. -/
lemma tsEdge_0 : TsEdge X 0 2 5 := by
  refine ⟨adj_2_5, Or.inr (Or.inr ⟨[], [1], ?_⟩)⟩
  refine ⟨by decide, ?_, ⟨2, by simp [X], by simp⟩, ⟨0, by simp [X], by simp⟩, ?_⟩
  · simp only [List.nil_append, List.cons_append, List.isChain_cons_cons, List.isChain_singleton,
      and_true]
    exact ⟨(adj_iff _ _).2 ⟨by decide, 4, by simp [X], by simp [X]⟩, adj_symm adj_2_5,
      (adj_iff _ _).2 ⟨by decide, 0, by simp [X], by simp [X]⟩,
      (adj_iff _ _).2 ⟨by decide, 1, by simp [X], by simp [X]⟩⟩
  · simp only [List.cons_append, List.nil_append, List.isChain_cons_cons, List.isChain_singleton,
      and_true]
    exact ⟨1, by simp [X], by simp [X], by simp⟩

/-- `e_25 ∉ E₄`. -/
lemma not_tsEdge_4 : ¬ TsEdge X 4 2 5 := by
  rintro ⟨-, h | h | ⟨l, r, hl⟩⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · refine not_isLoop_of_subset ?_ ?_ l r hl
    · intro x hx; simp [X] at hx ⊢; omega
    · rw [adj_iff]; rintro ⟨-, x, hx, hx'⟩; simp [X] at hx hx'; omega

lemma tsEdge_5 : TsEdge X 5 2 5 := tsEdge_in_iff.2 adj_2_5
lemma tsEdge_2 : TsEdge X 2 2 5 := tsEdge_self_iff.2 adj_2_5

/-- Initial state. -/
noncomputable def s₀ : State (Fin 6) (Fin 5) :=
  ⟨0, fun _ => ⟨0, 0, fun _ _ => 0, ∅⟩, fun _ _ _ => 0, fun _ => ∅⟩

lemma r₀ : Reachable X s₀ := ⟨s₀, ⟨rfl, rfl, rfl⟩, .refl⟩

/-! ### Execution A -/

noncomputable def a₁ := s₀.write X 2 2   -- 2 writes c (update 0)
noncomputable def a₂ := a₁.apply X 3 0   -- 3 applies it
noncomputable def a₃ := a₂.write X 3 3   -- 3 writes d (update 1)
noncomputable def a₄ := a₃.apply X 4 1   -- 4 applies it
noncomputable def a₅ := a₄.write X 4 4   -- 4 writes e (update 2)
noncomputable def a₆ := a₅.apply X 5 0   -- 5 applies update 0
noncomputable def a₇ := a₆.write X 5 4   -- 5 writes e (update 3)
noncomputable def a₈ := a₇.apply X 0 2   -- 0 applies update 2
noncomputable def a₉ := a₈.apply X 0 3   -- 0 applies update 3

lemma reach_a : Reachable X a₉ := by
  have r₁ : Reachable X a₁ := r₀.write (by simp [X])
  have r₂ : Reachable X a₂ := r₁.apply (by simp [a₁, s₀, State.write])
    (by simp [a₁, s₀, State.write]) (by simp [a₁, s₀, State.write, X])
    (by simp [a₁, s₀, State.write]) (by intro a ha; omega)
  have r₃ : Reachable X a₃ := r₂.write (by simp [X])
  have r₄ : Reachable X a₄ := r₃.apply (by simp [a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₃, a₂, a₁, s₀, State.write, State.apply, X])
    (by simp [a₃, a₂, a₁, s₀, State.write, State.apply])
    (by intro a ha; interval_cases a; simp [a₃, a₂, a₁, s₀, State.write, State.apply, X])
  have r₅ : Reachable X a₅ := r₄.write (by simp [X])
  have r₆ : Reachable X a₆ := r₅.apply
    (by simp [a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, X])
    (by simp [a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by intro a ha; omega)
  have r₇ : Reachable X a₇ := r₆.write (by simp [X])
  have r₈ : Reachable X a₈ := r₇.apply
    (by simp [a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, X])
    (by simp [a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, X])
  exact r₈.apply
    (by simp [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by simp [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, X])
    (by simp [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, X])

/-! ### Execution B -/

noncomputable def b₁ := s₀.write X 5 4   -- 5 writes e (update 0)
noncomputable def b₂ := b₁.write X 2 2   -- 2 writes c (update 1)
noncomputable def b₃ := b₂.apply X 3 1   -- 3 applies it
noncomputable def b₄ := b₃.write X 3 3   -- 3 writes d (update 2)
noncomputable def b₅ := b₄.apply X 4 0   -- 4 applies update 0
noncomputable def b₆ := b₅.apply X 4 2   -- 4 applies update 2
noncomputable def b₇ := b₆.write X 4 4   -- 4 writes e (update 3)
noncomputable def b₈ := b₇.apply X 0 0   -- 0 applies update 0
noncomputable def b₉ := b₈.apply X 0 3   -- 0 applies update 3

lemma reach_b : Reachable X b₉ := by
  have r₁ : Reachable X b₁ := r₀.write (by simp [X])
  have r₂ : Reachable X b₂ := r₁.write (by simp [X])
  have r₃ : Reachable X b₃ := r₂.apply (by simp [b₂, b₁, s₀, State.write])
    (by simp [b₂, b₁, s₀, State.write]) (by simp [b₂, b₁, s₀, State.write, X])
    (by simp [b₂, b₁, s₀, State.write])
    (by intro a ha; interval_cases a; simp [b₂, b₁, s₀, State.write, X])
  have r₄ : Reachable X b₄ := r₃.write (by simp [X])
  have r₅ : Reachable X b₅ := r₄.apply (by simp [b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])
    (by simp [b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by intro a ha; omega)
  have r₆ : Reachable X b₆ := r₅.apply
    (by simp [b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])
    (by simp [b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])
  have r₇ : Reachable X b₇ := r₆.write (by simp [X])
  have r₈ : Reachable X b₈ := r₇.apply
    (by simp [b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])
    (by simp [b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by intro a ha; omega)
  exact r₈.apply
    (by simp [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by simp [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])
    (by simp [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])
    (by intro a ha
        interval_cases a <;> simp [b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, X])

/-! ### The causal pasts of replica `0` -/

lemma causalPast_eq {s : State (Fin 6) (Fin 5)} (hs : Reachable X s) (hn : s.n = 4)
    (h0 : ∀ a < 4, a ∈ CausalPast s 0) : CausalPast s 0 = {a | a < 4} := by
  have h := Inv.of_reachable hs
  ext a
  refine ⟨fun ha => ?_, fun ha => h0 a ha⟩
  rcases ha with ha | ⟨b, hb, hab⟩
  · have := h.app_lt _ _ ha; simp only [Set.mem_ofPred_eq]; omega
  · have := (h.hb_lt hab).trans (h.app_lt _ _ hb); simp only [Set.mem_ofPred_eq]; omega

/-- Identification of updates across the two executions: issuer and register (every replica
writes at most once in both executions). -/
def ident {ι Reg : Type*} (s : State ι Reg) (a : ℕ) : ι × Reg := ((s.log a).src, (s.log a).reg)

/-- **Footnote 2 is false.** Two reachable states of the algorithm of Section 3.2 in which
replica `0` has the same causal past (the same four updates, each replica issuing at most one
update, so updates are identified by issuer and register) but different timestamps. -/
theorem footnote_2_false :
    Reachable X a₉ ∧ Reachable X b₉ ∧
    a₉.n = 4 ∧ b₉.n = 4 ∧
    Set.InjOn (ident a₉) {a | a < 4} ∧ Set.InjOn (ident b₉) {a | a < 4} ∧
    ident a₉ '' CausalPast a₉ 0 = ident b₉ '' CausalPast b₉ 0 ∧
    a₉.τ 0 2 5 = 1 ∧ b₉.τ 0 2 5 = 0 := by
  have hna : a₉.n = 4 := rfl
  have hnb : b₉.n = 4 := rfl
  have hA : CausalPast a₉ 0 = {a | a < 4} := by
    refine causalPast_eq reach_a hna (fun a ha => ?_)
    have e : ∀ x y : ℕ, y < a₉.n → x ∈ (a₉.log y).pre → HB a₉ x y :=
      fun x y hy hxy => .single ⟨hy, hxy⟩
    interval_cases a
    · exact Or.inr ⟨2, by simp [a₉, a₈, State.apply], .trans (e 0 1 (by simp [hna])
        (by simp [a₉, a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply]))
        (e 1 2 (by simp [hna])
        (by simp [a₉, a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply]))⟩
    · exact Or.inr ⟨2, by simp [a₉, a₈, State.apply], e 1 2 (by simp [hna])
        (by simp [a₉, a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply])⟩
    · exact Or.inl (by simp [a₉, a₈, State.apply])
    · exact Or.inl (by simp [a₉, a₈, State.apply])
  have hB : CausalPast b₉ 0 = {a | a < 4} := by
    refine causalPast_eq reach_b hnb (fun a ha => ?_)
    have e : ∀ x y : ℕ, y < b₉.n → x ∈ (b₉.log y).pre → HB b₉ x y :=
      fun x y hy hxy => .single ⟨hy, hxy⟩
    interval_cases a
    · exact Or.inl (by simp [b₉, b₈, State.apply])
    · exact Or.inr ⟨3, by simp [b₉, b₈, State.apply], .trans (e 1 2 (by simp [hnb])
        (by simp [b₉, b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply]))
        (e 2 3 (by simp [hnb])
        (by simp [b₉, b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply]))⟩
    · exact Or.inr ⟨3, by simp [b₉, b₈, State.apply], e 2 3 (by simp [hnb])
        (by simp [b₉, b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply])⟩
    · exact Or.inl (by simp [b₉, b₈, State.apply])
  have ia : ∀ a, ident a₉ a = if a = 0 then (2, 2) else if a = 1 then (3, 3)
      else if a = 2 then (4, 4) else if a = 3 then (5, 4) else ident s₀ a := by
    intro a
    simp only [ident, a₉, a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply,
      Function.update_apply]
    by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;> by_cases h3 : a = 3 <;>
      simp_all
  have ib : ∀ a, ident b₉ a = if a = 0 then (5, 4) else if a = 1 then (2, 2)
      else if a = 2 then (3, 3) else if a = 3 then (4, 4) else ident s₀ a := by
    intro a
    simp only [ident, b₉, b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply,
      Function.update_apply]
    by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;> by_cases h3 : a = 3 <;>
      simp_all
  refine ⟨reach_a, reach_b, hna, hnb, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [ia, ia] at hxy
    interval_cases x <;> interval_cases y <;> simp_all
  · intro x hx y hy hxy
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [ib, ib] at hxy
    interval_cases x <;> interval_cases y <;> simp_all
  · rw [hA, hB]
    ext p
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [ia]
      interval_cases x
      · exact ⟨1, by omega, by rw [ib]; simp⟩
      · exact ⟨2, by omega, by rw [ib]; simp⟩
      · exact ⟨3, by omega, by rw [ib]; simp⟩
      · exact ⟨0, by omega, by rw [ib]; simp⟩
    · rintro ⟨x, hx, rfl⟩
      rw [ib]
      interval_cases x
      · exact ⟨3, by omega, by rw [ia]; simp⟩
      · exact ⟨0, by omega, by rw [ia]; simp⟩
      · exact ⟨1, by omega, by rw [ia]; simp⟩
      · exact ⟨2, by omega, by rw [ia]; simp⟩
  · have t0 := tsEdge_0; have t5 := tsEdge_5; have t2 := tsEdge_2; have t4 := not_tsEdge_4
    simp only [X] at t0 t5 t2 t4
    simp [a₉, a₈, a₇, a₆, a₅, a₄, a₃, a₂, a₁, s₀, State.write, State.apply, incr, merge,
      t0, t5, t2, t4, X]
  · have t0 := tsEdge_0; have t5 := tsEdge_5; have t2 := tsEdge_2; have t4 := not_tsEdge_4
    simp only [X] at t0 t5 t2 t4
    simp [b₉, b₈, b₇, b₆, b₅, b₄, b₃, b₂, b₁, s₀, State.write, State.apply, incr, merge,
      t0, t5, t4, X]

end Podc.PartialReplicationCausal.Footnote2
