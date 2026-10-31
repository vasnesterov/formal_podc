import Cslib.Computability.Distributed.SharedMemory.LinPoints

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/PastLinPoints.lean

/-!
# Linearization points in the past

A generic linearizability criterion from *linearization points*, where the points of read-only
operations may be chosen retroactively (in hindsight), i.e. at any configuration between the
invocation and the response of the operation, not necessarily at a step of the operation itself.

An execution `α : List (Label P A)` has configurations `0, …, α.length` (configuration `n` is
reached after the prefix `α.take n`). We are given

* an abstract state `abs n : A.State` for every configuration `n`;
* the *effectful* linearization points `eff n = some (x, o)`: step `n` (from configuration `n`
  to `n + 1`) is the linearization point of the instance `x` with operation `o`; it moves the
  abstract state by `A.δ`; all other steps leave the abstract state unchanged;
* a set `ro` of instances (typically: read-only operations) that are linearized at a
  configuration `pt x` between their invocation and their response, where they do not change the
  abstract state.

Then the history of `α` is linearizable (`exists_isLinearization_of_points`). The linearization
lists, configuration by configuration, the `ro` instances linearized at configuration `n`
followed by the effectful instance linearized at step `n`.

This is the form of argument used, e.g., for optimistic list traversals ("hindsight": a
traversal that ends at a node can be linearized at an earlier configuration where that node was
reachable).

## Main results

* `exists_isLinearization_of_points`: the criterion.
* helper lemmas: `sublist_pair_flatMap_range` (two elements of groups `i < j` of a `flatMap`
  over `range` appear in that order), `Completed.take_mono`, `Invoked.take_mono`.
-/

namespace Cslib.SharedMemory

open List

/-- Two elements of groups `i < j` of `(range M).flatMap G` appear in this order. -/
lemma sublist_pair_flatMap_range {X : Type} (G : ℕ → List X) {M i j : ℕ} {a b : X}
    (hij : i < j) (hj : j < M) (ha : a ∈ G i) (hb : b ∈ G j) :
    [a, b].Sublist ((range M).flatMap G) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rw [range_succ, flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact (ih hj).trans (sublist_append_left _ _)
    · rw [sublist_pair_iff]
      refine ⟨(range j).flatMap G, [j].flatMap G, rfl, ?_, by simpa using hb⟩
      exact mem_flatMap.2 ⟨i, mem_range.2 hij, ha⟩

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- `Completed` is monotone along the prefixes `α.take n`. -/
lemma Completed.take_mono {α : List (Label P A)} {x : OpId P} {s t : ℕ}
    (h : Completed (α.take s) x) (hst : s ≤ t) : Completed (α.take t) x := by
  obtain ⟨u, hu⟩ := (take_prefix_take_left (l := α) hst)
  rw [← hu]; exact h.mono

/-- `Invoked` is monotone along the prefixes `α.take n`. -/
lemma Invoked.take_mono {α : List (Label P A)} {x : OpId P} {s t : ℕ}
    (h : Invoked (α.take s) x) (hst : s ≤ t) : Invoked (α.take t) x := by
  obtain ⟨u, hu⟩ := (take_prefix_take_left (l := α) hst)
  rw [← hu]; exact h.mono

/-- A sequential history all of whose operations keep the state `q` and give the actual
responses is legal from `q` and ends in `q`. -/
lemma seqOK_of_fixed {α : List (Label P A)} {q : A.State} {l : List (OpId P × A.Op)}
    (h : ∀ y ∈ l, (A.δ q y.2).1 = q ∧ ∀ r, respOf α y.1 = some r → (A.δ q y.2).2 = r) :
    SeqOK α q l ∧ A.runOps q (l.map Prod.snd) = q := by
  induction l with
  | nil => exact ⟨trivial, rfl⟩
  | cons y l ih =>
    obtain ⟨x, o⟩ := y
    obtain ⟨h1, h2⟩ := h (x, o) (by simp)
    have ih' := ih (fun z hz => h z (by simp [hz]))
    refine ⟨⟨h2, h1.symm ▸ ih'.1⟩, ?_⟩
    simp only [map_cons, ObjSpec.runOps_cons, h1]
    exact ih'.2

/-- Linearizability from linearization points. The abstract state `abs j` is attached to the
`j`-th configuration of the execution `α` (`j ≤ α.length`). State-changing or otherwise
"effectful" operations are linearized at a step: `eff n = some (x, o)` says that step `n`
(label `α[n]`, from configuration `n` to `n+1`) is the linearization point of instance `x` with
operation `o`; all other steps leave the abstract state unchanged. Operations in `ro` are
linearized retroactively at the configuration `pt x` (between their invocation and response),
where they must not change the abstract state; only completed `ro` instances need a point. -/
theorem exists_isLinearization_of_points {α : List (Label P A)} (abs : ℕ → A.State)
    (eff : ℕ → Option (OpId P × A.Op)) (ro : OpId P → Prop) (pt : OpId P → ℕ)
    (h0 : abs 0 = A.init)
    (hnone : ∀ n < α.length, eff n = none → abs (n + 1) = abs n)
    (hsome : ∀ n < α.length, ∀ x o, eff n = some (x, o) →
       opOf α x = some o ∧ Invoked (α.take n) x ∧ ¬ Completed (α.take (n + 1)) x ∧
       (A.δ (abs n) o).1 = abs (n + 1) ∧ ∀ r, respOf α x = some r → (A.δ (abs n) o).2 = r)
    (hinj : ∀ n < α.length, ∀ n' < α.length, ∀ x o o',
       eff n = some (x, o) → eff n' = some (x, o') → n = n')
    (hro : ∀ x, ro x → Completed α x → ∃ o, opOf α x = some o ∧ pt x ≤ α.length ∧
       Invoked (α.take (pt x)) x ∧ ¬ Completed (α.take (pt x)) x ∧
       (A.δ (abs (pt x)) o).1 = abs (pt x) ∧
       ∀ r, respOf α x = some r → (A.δ (abs (pt x)) o).2 = r)
    (hcover : ∀ x, Completed α x → ro x ∨ ∃ n < α.length, ∃ o, eff n = some (x, o))
    (hdisj : ∀ x, ro x → ∀ n < α.length, ∀ o, eff n ≠ some (x, o)) :
    ∃ L, IsLinearization α L := by
  classical
  set N := α.length with hN
  -- the `ro` instances linearized at configuration `n`
  let R : ℕ → List (OpId P × A.Op) := fun n =>
    ((invIds α).filter (fun x => decide (ro x ∧ Completed α x ∧ pt x = n))).filterMap
      (fun x => (opOf α x).map (fun o => (x, o)))
  -- the effectful instance linearized at step `n`
  let E : ℕ → List (OpId P × A.Op) := fun n => if n < N then (eff n).toList else []
  let G : ℕ → List (OpId P × A.Op) := fun n => R n ++ E n
  have memR : ∀ n y, y ∈ R n ↔ ro y.1 ∧ Completed α y.1 ∧ pt y.1 = n ∧ opOf α y.1 = some y.2 := by
    rintro n ⟨x, o⟩
    simp only [R, mem_filterMap, mem_filter, mem_invIds, decide_eq_true_eq, Option.map_eq_some_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨x', ⟨-, h1, h2, h3⟩, o', h4, rfl, rfl⟩; exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨x, ⟨Invoked.of_opOf_eq_some h4, h1, h2, h3⟩, o, h4, rfl, rfl⟩
  have memE : ∀ n y, y ∈ E n ↔ n < N ∧ eff n = some y := by
    intro n y
    simp only [E]
    split_ifs with h <;> simp [h, Option.mem_toList]
  have memG : ∀ n y, y ∈ G n ↔ (ro y.1 ∧ Completed α y.1 ∧ pt y.1 = n ∧ opOf α y.1 = some y.2) ∨
      (n < N ∧ eff n = some y) := by
    intro n y; simp only [G, mem_append, memR, memE]
  -- group index: an instance lies in at most one group
  have grp : ∀ i j x o o', (x, o) ∈ G i → (x, o') ∈ G j → i = j := by
    intro i j x o o' hi hj
    rw [memG] at hi hj
    rcases hi with ⟨hr, -, rfl, -⟩ | ⟨hi, he⟩ <;> rcases hj with ⟨hr', -, rfl, -⟩ | ⟨hj, he'⟩
    · rfl
    · exact absurd he' (hdisj x hr _ hj _)
    · exact absurd he (hdisj x hr' _ hi _)
    · exact hinj i hi j hj x o o' he he'
  -- the position of an instance in the execution, relative to its group
  have before : ∀ i x o, (x, o) ∈ G i → ∀ s, Completed (α.take s) x → i < s := by
    intro i x o hi s hs
    rw [memG] at hi
    simp only at hi
    rcases hi with ⟨hr, hc, rfl, -⟩ | ⟨hi, he⟩
    · obtain ⟨-, -, -, -, hnc, -⟩ := hro x hr hc
      by_contra hle; exact hnc (hs.take_mono (by omega))
    · obtain ⟨-, -, hnc, -⟩ := hsome i hi x o he
      by_contra hle; exact hnc (hs.take_mono (by omega))
  have after : ∀ j x o, (x, o) ∈ G j → ∀ s, ¬ Invoked (α.take s) x → s < j := by
    intro j x o hj s hs
    rw [memG] at hj
    simp only at hj
    rcases hj with ⟨hr, hc, rfl, -⟩ | ⟨hj, he⟩
    · obtain ⟨-, -, -, hinv, -⟩ := hro x hr hc
      by_contra hle; exact hs (hinv.take_mono (by omega))
    · obtain ⟨-, hinv, -⟩ := hsome j hj x o he
      by_contra hle; exact hs (hinv.take_mono (by omega))
  have memL : ∀ x, x ∈ ((range (N + 1)).flatMap G).map Prod.fst ↔
      ∃ i < N + 1, ∃ o, (x, o) ∈ G i := by
    intro x
    simp only [mem_map, mem_flatMap, mem_range]
    constructor
    · rintro ⟨⟨x', o⟩, ⟨i, hi, hm⟩, rfl⟩; exact ⟨i, hi, o, hm⟩
    · rintro ⟨i, hi, o, hm⟩; exact ⟨(x, o), ⟨i, hi, hm⟩, rfl⟩
  -- legality: the state before group `n` is `abs n`
  have hRfix : ∀ n, SeqOK α (abs n) (R n) ∧ A.runOps (abs n) ((R n).map Prod.snd) = abs n := by
    intro n
    apply seqOK_of_fixed
    rintro ⟨x, o⟩ hy
    obtain ⟨hr, hc, rfl, hop⟩ := (memR _ _).1 hy
    obtain ⟨o', hop', -, -, -, h1, h2⟩ := hro x hr hc
    rw [hop] at hop'; cases hop'
    exact ⟨h1, h2⟩
  have hGstep : ∀ n < N, SeqOK α (abs n) (G n) ∧
      A.runOps (abs n) ((G n).map Prod.snd) = abs (n + 1) := by
    intro n hn
    obtain ⟨hR1, hR2⟩ := hRfix n
    simp only [G, E, hn, ite_true, seqOK_append, map_append, ObjSpec.runOps_append, hR2]
    cases he : eff n with
    | none => exact ⟨⟨hR1, trivial⟩, (hnone n hn he).symm⟩
    | some y =>
      obtain ⟨x, o⟩ := y
      obtain ⟨-, -, -, h1, h2⟩ := hsome n hn x o he
      exact ⟨⟨hR1, h2, trivial⟩, h1⟩
  have hpre : ∀ M ≤ N, SeqOK α A.init ((range M).flatMap G) ∧
      A.runOps A.init (((range M).flatMap G).map Prod.snd) = abs M := by
    intro M hM
    induction M with
    | zero => simp [SeqOK, h0]
    | succ M ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨g1, g2⟩ := hGstep M (by omega)
      rw [range_succ, flatMap_append, flatMap_singleton, seqOK_append, map_append,
        ObjSpec.runOps_append, ih2]
      exact ⟨⟨ih1, g1⟩, g2⟩
  refine ⟨(range (N + 1)).flatMap G, ?_, ?_, ?_, ?_, ?_⟩
  · -- nodup
    rw [map_flatMap, nodup_flatMap]
    refine ⟨fun n _ => ?_, ?_⟩
    · simp only [G, map_append, nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · simp only [R, map_filterMap]
        refine (nodup_invIds α).filter _ |>.filterMap ?_
        intro a a' b ha ha'
        simp only [Option.mem_def, Option.map_map, Option.map_eq_some_iff,
          Function.comp_apply] at ha ha'
        obtain ⟨_, -, rfl⟩ := ha
        obtain ⟨_, -, h⟩ := ha'
        exact h.symm
      · simp only [E]; split_ifs <;> cases eff n <;> simp
      · intro a ha b hb hab
        obtain ⟨⟨x, o⟩, hx, hxa⟩ := mem_map.1 ha
        obtain ⟨⟨x', o'⟩, hx', hxb⟩ := mem_map.1 hb
        simp only at hxa hxb
        have hxx : x' = x := by rw [hxb, hxa, hab]
        subst hxx
        obtain ⟨hr, -⟩ := (memR _ _).1 hx
        obtain ⟨hn, he⟩ := (memE _ _).1 hx'
        exact hdisj x' hr n hn o' he
    · refine (pairwise_lt_range).imp ?_
      · intro i j hij
        rw [Function.onFun, List.disjoint_left]
        intro x hi hj
        obtain ⟨⟨x₁, o⟩, h1, rfl⟩ := mem_map.1 hi
        obtain ⟨⟨x₂, o'⟩, h2, hx⟩ := mem_map.1 hj
        simp only at hx; subst hx
        exact absurd (grp i j _ _ _ h1 h2) (by omega)
  · -- operations
    intro y hy
    obtain ⟨n, -, hn⟩ := mem_flatMap.1 hy
    rcases (memG n y).1 hn with ⟨-, -, -, h⟩ | ⟨hnN, he⟩
    · exact h
    · obtain ⟨x, o⟩ := y
      exact (hsome n hnN x o he).1
  · -- completeness
    intro a ha
    rw [memL]
    rcases hcover a ha with hr | ⟨n, hn, o, he⟩
    · obtain ⟨o, hop, hpt, -⟩ := hro a hr ha
      exact ⟨pt a, by omega, o, (memG _ (a, o)).2 (Or.inl ⟨hr, ha, rfl, hop⟩)⟩
    · exact ⟨n, by omega, o, (memG _ (a, o)).2 (Or.inr ⟨hn, he⟩)⟩
  · -- real time
    intro a b hab hb
    obtain ⟨β, γ, hsplit, hca, hnb⟩ := hab
    have hβ : α.take β.length = β := by rw [hsplit, take_left]
    have ha : a ∈ ((range (N + 1)).flatMap G).map Prod.fst := by
      rw [memL]
      have hca' : Completed α a := by rw [hsplit]; exact hca.mono
      rcases hcover a hca' with hr | ⟨n, hn, o, he⟩
      · obtain ⟨o, hop, hpt, -⟩ := hro a hr hca'
        exact ⟨pt a, by omega, o, (memG _ (a, o)).2 (Or.inl ⟨hr, hca', rfl, hop⟩)⟩
      · exact ⟨n, by omega, o, (memG _ (a, o)).2 (Or.inr ⟨hn, he⟩)⟩
    obtain ⟨i, -, o, hi⟩ := (memL a).1 ha
    obtain ⟨j, hj, o', hj'⟩ := (memL b).1 hb
    have h1 := before i a o hi β.length (by rw [hβ]; exact hca)
    have h2 := after j b o' hj' β.length (by rw [hβ]; exact hnb)
    rw [map_flatMap]
    exact sublist_pair_flatMap_range _ (by omega) hj (mem_map_of_mem hi) (mem_map_of_mem hj')
  · -- legality
    obtain ⟨p1, p2⟩ := hpre N le_rfl
    rw [range_succ, flatMap_append, flatMap_singleton, seqOK_append, p2]
    refine ⟨p1, ?_⟩
    have hEN : E N = [] := by simp [E]
    simp only [G, hEN, append_nil]
    exact (hRfix N).1

end Cslib.SharedMemory
