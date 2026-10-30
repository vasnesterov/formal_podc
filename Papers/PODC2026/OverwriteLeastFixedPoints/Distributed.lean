import Papers.PODC2026.OverwriteLeastFixedPoints.Parallel

/-!
# Section 4: distributed execution with bounded staleness (Theorem 4.1)

Process `i` owns coordinate `i` of the global state `G t : (i : ι) → β i`. In round `t` every active
process `i ∈ S t` applies `f i` to its *view* `V t i` and commits only its own coordinate:
`G (t+1) i = f i (V t i) i`; inactive coordinates are unchanged (`IsDistExec`).

* `StaleView G t i V`: the view has the current own coordinate and, for every other coordinate,
  *some* past value (the stale-read model of Section 4);
* `BoundedStale T G t i V` (Definition 5): moreover every coordinate is at most `T` rounds old.
* `IsLocal f` (Definition 4): `f i` changes only coordinate `i`.

Results: `distributed_converges_from`, `theorem_4_1` (with strong fairness, as in the paper),
`theorem_4_1_fair` (plain fairness suffices), `unbounded_staleness_cex` (the paper's example in
Section 4), `corollary_4_2_distributed`, and `distCommit_mem` (the commit stays in any sup-closed
set of states containing the views).
-/

namespace Podc.OverwriteLeastFixedPoints

variable {ι : Type*} {β : ι → Type*}

/-- Definition 4: every `f i` is `i`-local (changes only coordinate `i`). -/
def IsLocal (f : ι → ((i : ι) → β i) → ((i : ι) → β i)) : Prop :=
  ∀ i x j, j ≠ i → f i x j = x j

/-- A (possibly stale) view of process `i` in round `t`: own coordinate current, every other
coordinate the value it had in some earlier round. -/
def StaleView (G : ℕ → (i : ι) → β i) (t : ℕ) (i : ι) (V : (i : ι) → β i) : Prop :=
  V i = G t i ∧ ∀ j, ∃ s, s ≤ t ∧ V j = G s j

/-- Definition 5 (bounded staleness with parameter `T`): the view has the current own coordinate and
every coordinate is at most `T` rounds old. -/
def BoundedStale (T : ℕ) (G : ℕ → (i : ι) → β i) (t : ℕ) (i : ι) (V : (i : ι) → β i) : Prop :=
  V i = G t i ∧ ∀ j, ∃ s, t - T ≤ s ∧ s ≤ t ∧ V j = G s j

theorem BoundedStale.staleView {T : ℕ} {G : ℕ → (i : ι) → β i} {t : ℕ} {i : ι}
    {V : (i : ι) → β i} (h : BoundedStale T G t i V) : StaleView G t i V :=
  ⟨h.1, fun j => let ⟨s, _, hs, he⟩ := h.2 j; ⟨s, hs, he⟩⟩

/-- The coordinatewise commit rule of Theorem 4.1. -/
def IsDistExec (f : ι → ((i : ι) → β i) → ((i : ι) → β i)) (S : ℕ → Set ι)
    (V : ℕ → ι → (i : ι) → β i) (G : ℕ → (i : ι) → β i) : Prop :=
  ∀ t i, (i ∈ S t → G (t + 1) i = f i (V t i) i) ∧ (i ∉ S t → G (t + 1) i = G t i)

section Order

variable [∀ i, PartialOrder (β i)] {f : ι → ((i : ι) → β i) → ((i : ι) → β i)}
  {S : ℕ → Set ι} {V : ℕ → ι → (i : ι) → β i} {G : ℕ → (i : ι) → β i}

/-- With stale views, the global state is an ascending chain. -/
theorem IsDistExec.monotone (hG : IsDistExec f S V G) (hinf : ∀ i, Inflationary (f i))
    (hV : ∀ t, ∀ i ∈ S t, StaleView G t i (V t i)) : Monotone G := by
  refine monotone_nat_of_le_succ fun t i => ?_
  by_cases hi : i ∈ S t
  · rw [(hG t i).1 hi, ← (hV t i hi).1]
    exact hinf i _ i
  · rw [(hG t i).2 hi]

/-- With stale views (bounded or not), the execution stays below every common fixed point `Y` above
the initial state. -/
theorem IsDistExec.le_of_isCommonFixed (hG : IsDistExec f S V G) (hm : ∀ i, Monotone (f i))
    (hV : ∀ t, ∀ i ∈ S t, StaleView G t i (V t i)) {Y : (i : ι) → β i} (hY : IsCommonFixed f Y)
    (h0 : G 0 ≤ Y) : ∀ t, G t ≤ Y := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases t with _ | t
    · exact h0
    · intro i
      by_cases hi : i ∈ S t
      · rw [(hG t i).1 hi, ← hY i]
        refine hm i (fun j => ?_) i
        obtain ⟨s, hs, he⟩ := (hV t i hi).2 j
        rw [he]
        exact ih s (by omega) j
      · rw [(hG t i).2 hi]
        exact ih t (by omega) i

/-- Theorem 4.1 from an arbitrary initial state and under plain fairness: a distributed execution of
monotone, inflationary, `i`-local functions with `T`-bounded staleness terminates at the least
common fixed point above `G 0`. -/
theorem distributed_converges_from [WellFoundedGT ((i : ι) → β i)] (hm : ∀ i, Monotone (f i))
    (hinf : ∀ i, Inflationary (f i)) (hloc : IsLocal f) {T : ℕ} (hS : FairSets S)
    (hV : ∀ t, ∀ i ∈ S t, BoundedStale T G t i (V t i)) (hG : IsDistExec f S V G) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y ∧ G 0 ≤ y} x := by
  have hV' : ∀ t, ∀ i ∈ S t, StaleView G t i (V t i) := fun t i hi => (hV t i hi).staleView
  have hmono := hG.monotone hinf hV'
  obtain ⟨U, hU⟩ := exists_terminatesAt_of_monotone hmono
  refine ⟨G U, ⟨U, hU⟩, ⟨?_, hmono (Nat.zero_le _)⟩, fun y ⟨hy, h0⟩ =>
    hG.le_of_isCommonFixed hm hV' hy h0 U⟩
  intro i
  -- a round `t ≥ U + T` in which `i` is active: its view is exactly `G U`
  obtain ⟨t, ht, hti⟩ := hS i (U + T)
  have hview : V t i = G U := by
    funext j
    obtain ⟨s, hs, -, he⟩ := (hV t i hti).2 j
    rw [he, hU s (by omega)]
  have hi : f i (G U) i = G U i := by
    rw [← hview, ← (hG t i).1 hti, hview, hU (t + 1) (by omega)]
  funext j
  by_cases hj : j = i
  · subst hj; exact hi
  · exact hloc i _ j hj

/-- **Theorem 4.1** of [Garg–Garg, BA] (= Theorem 4 of the full version). Let the state space be a
finite product of finite posets with bottom, and `fᵢ` monotone, inflationary and `i`-local. A
distributed execution from `⊥` with a strongly fair scheduler (window `τ`) and views satisfying
bounded staleness (parameter `T`) terminates at the least common fixed point. -/
theorem theorem_4_1 [Finite ι] [∀ i, Finite (β i)] [∀ i, OrderBot (β i)]
    (hm : ∀ i, Monotone (f i)) (hinf : ∀ i, Inflationary (f i)) (hloc : IsLocal f) {τ T : ℕ}
    (hS : StronglyFair τ S) (hV : ∀ t, ∀ i ∈ S t, BoundedStale T G t i (V t i))
    (h0 : G 0 = ⊥) (hG : IsDistExec f S V G) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y} x := by
  obtain ⟨x, hx, hl⟩ := distributed_converges_from hm hinf hloc hS.fairSets hV hG
  exact ⟨x, hx, hl.1.1, fun y hy => hl.2 ⟨hy, by rw [h0]; exact bot_le⟩⟩

/-- Theorem 4.1 under plain fairness: strong fairness is not needed (every process scheduled
infinitely often suffices, together with bounded staleness). -/
theorem theorem_4_1_fair [Finite ι] [∀ i, Finite (β i)] [∀ i, OrderBot (β i)]
    (hm : ∀ i, Monotone (f i)) (hinf : ∀ i, Inflationary (f i)) (hloc : IsLocal f) {T : ℕ}
    (hS : FairSets S) (hV : ∀ t, ∀ i ∈ S t, BoundedStale T G t i (V t i))
    (h0 : G 0 = ⊥) (hG : IsDistExec f S V G) :
    ∃ x, TerminatesAt G x ∧ IsLeast {y | IsCommonFixed f y} x := by
  obtain ⟨x, hx, hl⟩ := distributed_converges_from hm hinf hloc hS hV hG
  exact ⟨x, hx, hl.1.1, fun y hy => hl.2 ⟨hy, by rw [h0]; exact bot_le⟩⟩

/-- **Corollary 4.2** of [Garg–Garg] (distributed version): deflationary monotone local functions,
start `⊤`, strong fairness and bounded staleness give the greatest common fixed point. -/
theorem corollary_4_2_distributed [Finite ι] [∀ i, Finite (β i)] [∀ i, OrderTop (β i)]
    (hm : ∀ i, Monotone (f i)) (hdef : ∀ i, Deflationary (f i)) (hloc : IsLocal f) {τ T : ℕ}
    (hS : StronglyFair τ S) (hV : ∀ t, ∀ i ∈ S t, BoundedStale T G t i (V t i))
    (h0 : G 0 = ⊤) (hG : IsDistExec f S V G) :
    ∃ x, TerminatesAt G x ∧ IsGreatest {y | IsCommonFixed f y} x := by
  have := @theorem_4_1 ι (fun i => (β i)ᵒᵈ) (fun i => inferInstance) f S V G
  exact this (fun i _ _ h => hm i h) (fun i x => hdef i x) hloc hS hV h0 hG

end Order

/-! ## Unbounded staleness (the example of Section 4) -/

/-- The functions of the Section 4 example on `{0,1}³`: `f₀ x = (1, x₁, x₂)`,
`f₁ x = (x₀, x₀ ∨ x₁, x₂)`, `f₂ x = (x₀, x₁, x₁ ∨ x₂)`. -/
def staleF : Fin 3 → (Fin 3 → Bool) → (Fin 3 → Bool)
  | 0, x => Function.update x 0 true
  | 1, x => Function.update x 1 (x 0 || x 1)
  | 2, x => Function.update x 2 (x 1 || x 2)

/-- The execution of the example: `000` then `100` forever. -/
def staleG (t : ℕ) : Fin 3 → Bool := if t = 0 then ⊥ else ![true, false, false]

/-- The views of the example: `P₀` reads the current state, `P₁` and `P₂` keep reading the initial
`000` forever. -/
def staleV (t : ℕ) (i : Fin 3) : Fin 3 → Bool := if i = 0 then staleG t else ⊥

/-- Section 4: without bounded staleness, Theorem 4.1 fails. The functions `staleF` are monotone,
inflationary and local; the schedule activates all processes every round (strongly fair with
`τ = 1`); the views are genuine stale views (own coordinate current, others from round `0`); the
execution terminates at `100`, which is not a common fixed point; and for no `T` are the views
`T`-bounded-stale. -/
theorem unbounded_staleness_cex :
    (∀ i, Monotone (staleF i)) ∧ (∀ i, Inflationary (staleF i)) ∧ IsLocal staleF ∧
      StronglyFair 1 (fun _ => (Set.univ : Set (Fin 3))) ∧
      (∀ t i, StaleView staleG t i (staleV t i)) ∧ staleG 0 = ⊥ ∧
      IsDistExec staleF (fun _ => Set.univ) staleV staleG ∧
      TerminatesAt staleG ![true, false, false] ∧ ¬ IsCommonFixed staleF ![true, false, false] ∧
      (∀ T, ¬ ∀ t, ∀ i, BoundedStale T staleG t i (staleV t i)) := by
  refine ⟨?_, ?_, ?_, fun i t => ⟨t, le_rfl, by omega, trivial⟩, ?_, rfl, ?_,
    ⟨1, fun t ht => by simp [staleG]; omega⟩, fun h => absurd (h 1) (by decide), ?_⟩
  · intro i x y h k
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    fin_cases i <;> fin_cases k <;> simp [staleF, Function.update] <;>
      first | exact h0 | exact h1 | exact h2 | exact sup_le_sup h0 h1 | exact sup_le_sup h1 h2
  · intro i x k
    fin_cases i <;> fin_cases k <;> simp [staleF, Function.update] <;> exact le_sup_right
  · intro i x j hj
    fin_cases i <;> fin_cases j <;> simp_all [staleF]
  · intro t i
    refine ⟨?_, fun j => ?_⟩
    · fin_cases i
      · rfl
      · rcases t with _ | t <;> rfl
      · rcases t with _ | t <;> rfl
    · by_cases hi : i = 0
      · exact ⟨t, le_rfl, by simp [staleV, hi]⟩
      · exact ⟨0, Nat.zero_le _, by simp [staleV, hi, staleG]⟩
  · intro t i
    refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
    rcases t with _ | t <;> fin_cases i <;> simp [staleG, staleV, staleF, Function.update]
  · intro T h
    obtain ⟨s, hs, -, he⟩ := (h (T + 1) 1).2 0
    have hs0 : s ≠ 0 := by omega
    have h1 : staleG s 0 = true := by simp [staleG, hs0]
    have h2 : staleV (T + 1) 1 0 = false := by simp [staleV]
    rw [he, h1] at h2
    exact absurd h2 (by decide)

/-! ## Well-definedness on sup-closed sets of states -/

/-- If the set `L` of admissible states is closed under (componentwise) joins, contains the current
state `G` and the views `V i ≤ G` of the active processes, and every `f i` maps `L` into `L`, is
inflationary and `i`-local, then the committed state (own coordinates updated by the active
processes of the finite set `s`) is again in `L`. So, unlike Theorem 3.1 (see
`sublattice_round_escapes`), the distributed model is well defined on sublattices of the product. -/
theorem distCommit_mem [DecidableEq ι] [∀ i, Lattice (β i)] {f : ι → ((i : ι) → β i) → ((i : ι) → β i)}
    {L : Set ((i : ι) → β i)} (hL : SupClosed L) (hf : ∀ i, ∀ x ∈ L, f i x ∈ L)
    (hinf : ∀ i, Inflationary (f i)) (hloc : IsLocal f) {G : (i : ι) → β i} (hG : G ∈ L)
    {V : ι → (i : ι) → β i} (s : Finset ι) (hV : ∀ i ∈ s, V i ∈ L ∧ V i ≤ G ∧ V i i = G i) :
    (fun j => if j ∈ s then f j (V j) j else G j) ∈ L := by
  induction s using Finset.induction_on with
  | empty => simpa using hG
  | insert i s his ih =>
    obtain ⟨hVL, hVG, hVi⟩ := hV i (Finset.mem_insert_self i s)
    have ih := ih fun j hj => hV j (Finset.mem_insert_of_mem hj)
    convert hL ih (hf i _ hVL) using 1
    funext j
    simp only [Finset.mem_insert, Pi.sup_apply]
    by_cases hj : j = i
    · subst hj
      simp only [true_or, ite_true, his, ite_false]
      rw [sup_eq_right.2]
      rw [← hVi]
      exact hinf j _ j
    · simp only [hj, false_or]
      rw [hloc i _ j hj]
      split_ifs with hjs
      · rw [sup_eq_left.2]
        obtain ⟨-, -, hVj⟩ := hV j (Finset.mem_insert_of_mem hjs)
        calc V i j ≤ G j := hVG j
          _ = V j j := hVj.symm
          _ ≤ f j (V j) j := hinf j _ j
      · exact (sup_eq_left.2 (hVG j)).symm

end Podc.OverwriteLeastFixedPoints
