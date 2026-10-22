import Papers.PODC2012.ResilientRouting.Model

/-!
# Counterexamples to Lemmas 4.1 and 4.2 and to Theorem 3.1 in degenerate readings

* `lemma_4_1_false`: Lemma 4.1 as stated is false. Network `d = 0 – 1`, triangle `1, 2, 3`.
  Node `2` has the path `2 – 3 – 1 – d`, which does not use the link `21`, yet the perfectly
  resilient pattern "every node forwards to `1`, node `1` forwards to `d`" sends packets
  travelling `1 → 2` back to `1`. (The path passes through node `1`; see `lemma_4_1` for the
  repaired statement.)
* `lemma_4_2_false`: Lemma 4.2 is false. On the path `d = 0 – 1 – 2 – 3` the pattern "forward to
  the neighbour closer to `d`" is perfectly resilient, but node `2` (connected to `d`, not
  adjacent to it) maps both its live links to `1`, which is not a cyclic ordering.
* `theorem_3_1_disconnected`: Theorem 3.1 needs a connected network: if a component without `d`
  has a link, packets in it bounce forever when nothing fails.
* `literal_K2`: if the destination is not a sink (the paper's definition of forwarding paths puts
  no constraint at `d`, so a path may continue after reaching `d`), then already on the network
  `d – 1` with no failure the path `d, 1, d, 1` is a forwarding loop, so no pattern is even
  0-resilient.
-/

namespace Podc.ResilientRouting.Counterexamples

open SimpleGraph

/-- Membership of an unordered pair in a list of pairs. -/
def memB {n : ℕ} (L : List (Fin n × Fin n)) (u v : Fin n) : Bool :=
  L.any fun p => (p.1 = u ∧ p.2 = v) || (p.1 = v ∧ p.2 = u)

theorem memB_comm {n : ℕ} (L : List (Fin n × Fin n)) (u v : Fin n) :
    memB L u v = memB L v u := by
  unfold memB; congr 1; funext p; rw [Bool.or_comm]

/-- The graph on `Fin n` with the links of `L`. -/
def listGraph (n : ℕ) (L : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ memB L u v = true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [memB_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} (L : List (Fin n × Fin n)) : DecidableRel (listGraph n L).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ memB L u v = true))

/-! ### Lemma 4.1 -/

/-- `d = 0`, `0 – 1`, and the triangle `1, 2, 3`. -/
abbrev G41 : SimpleGraph (Fin 4) := listGraph 4 [(0, 1), (1, 2), (2, 3), (3, 1)]

/-- Every node forwards to `1`, node `1` forwards to `d`. -/
def f41 : Pattern G41 where
  next v _ x := if v = 0 then x else if v = 1 then 0 else 1
  adj_next i A u hu := by clear A; revert i u; decide

theorem terminates_f41 (F : Set (Sym2 (Fin 4))) (δ : Fin 4 × Fin 4) :
    Terminates G41 0 f41 F δ := by
  obtain ⟨x, v⟩ := δ
  fin_cases v
  · exact .base (Or.inl rfl)
  · exact .step (.base (Or.inl rfl))
  · exact .step (.step (.base (Or.inl rfl)))
  · exact .step (.step (.base (Or.inl rfl)))

theorem f41_perfect : PerfectlyResilient G41 0 f41 := by
  intro F _
  refine good_of (terminates_f41 F) fun i hi hr => ?_
  have hS : ∀ i ∈ ({1, 2, 3} : Finset (Fin 4)), (G41.deleteEdges F).Reachable i 0 →
      Live G41 F 1 0 := fun i hi hr => by
    by_contra h
    exact not_reachable_of_dead {1, 2, 3} [(1, 0)] (by simpa using h) (by decide) hi (by decide) hr
  have del1 : ∀ x, Delivers G41 0 f41 F (x, 1) := fun x =>
    .of_next (by decide) rfl (hS i (by fin_cases i <;> simp_all) hr) (.base rfl)
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, hS 1 (by decide) hr, .base rfl⟩
  · by_cases h21 : Live G41 F 2 1
    · exact ⟨1, h21, del1 2⟩
    by_cases h23 : Live G41 F 2 3
    · by_cases h31 : Live G41 F 3 1
      · exact ⟨3, h23, .of_next (by decide) rfl h31 (del1 3)⟩
      · exact absurd hr (not_reachable_of_dead {2, 3} [(2, 1), (3, 1)] (by simp [h21, h31])
          (by decide) (by decide) (by decide))
    · exact absurd hr (not_reachable_of_dead {2} [(2, 1), (2, 3)] (by simp [h21, h23])
        (by decide) (by decide) (by decide))
  · by_cases h31 : Live G41 F 3 1
    · exact ⟨1, h31, del1 3⟩
    by_cases h32 : Live G41 F 3 2
    · by_cases h21 : Live G41 F 2 1
      · exact ⟨2, h32, .of_next (by decide) rfl h21 (del1 2)⟩
      · exact absurd hr (not_reachable_of_dead {2, 3} [(2, 1), (3, 1)] (by simp [h21, h31])
          (by decide) (by decide) (by decide))
    · exact absurd hr (not_reachable_of_dead {3} [(3, 1), (3, 2)] (by simp [h31, h32])
        (by decide) (by decide) (by decide))

/-- **Lemma 4.1 is false as stated.** In the network `G41` with no failures, node `2` has a
working path `2, 3, 1, d` to the destination that does not use the link `21`, but the perfectly
resilient pattern `f41` sends a packet travelling `1 → 2` back to `1`. -/
theorem lemma_4_1_false : ∃ f : Pattern G41, PerfectlyResilient G41 0 f ∧
    ∃ (u v : Fin 4) (p : (G41.deleteEdges ∅).Walk v 0), u ≠ 0 ∧ v ≠ 0 ∧ Live G41 ∅ u v ∧
      s(v, u) ∉ p.edges ∧ f.next v (view G41 ∅ v) u = u := by
  refine ⟨f41, f41_perfect, 1, 2,
    .cons (v := 3) (by simp; decide) (.cons (v := 1) (by simp; decide)
      (.cons (by simp; decide) .nil)), by decide, by decide, by simp [Live]; decide, ?_, rfl⟩
  simp [Walk.edges]

/-! ### Lemma 4.2 -/

/-- The paper's "cyclic ordering": the forwarding function `σ` of a node maps its set `A` of live
neighbours bijectively onto itself, in one cycle. -/
def RoutesCyclically {V : Type*} (σ : V → V) (A : Set V) : Prop :=
  Set.BijOn σ A A ∧ ∀ x ∈ A, ∀ y ∈ A, ∃ k, σ^[k] x = y

/-- The path `d = 0 – 1 – 2 – 3`. -/
abbrev G42 : SimpleGraph (Fin 4) := listGraph 4 [(0, 1), (1, 2), (2, 3)]

/-- Forward to the neighbour closer to `d`. -/
def f42 : Pattern G42 where
  next v _ x := if v = 0 then x else if v = 1 then 0 else if v = 2 then 1 else 2
  adj_next i A u hu := by clear A; revert i u; decide

theorem terminates_f42 (F : Set (Sym2 (Fin 4))) (δ : Fin 4 × Fin 4) :
    Terminates G42 0 f42 F δ := by
  obtain ⟨x, v⟩ := δ
  fin_cases v
  · exact .base (Or.inl rfl)
  · exact .step (.base (Or.inl rfl))
  · exact .step (.step (.base (Or.inl rfl)))
  · exact .step (.step (.step (.base (Or.inl rfl))))

theorem f42_perfect : PerfectlyResilient G42 0 f42 := by
  intro F _
  refine good_of (terminates_f42 F) fun i hi hr => ?_
  have l10 : i ∈ ({1, 2, 3} : Finset (Fin 4)) → Live G42 F 1 0 := fun h => by
    by_contra h'
    exact not_reachable_of_dead {1, 2, 3} [(1, 0)] (by simpa using h') (by decide) h (by decide) hr
  have l21 : i ∈ ({2, 3} : Finset (Fin 4)) → Live G42 F 2 1 := fun h => by
    by_contra h'
    exact not_reachable_of_dead {2, 3} [(2, 1)] (by simpa using h') (by decide) h (by decide) hr
  have l32 : i = 3 → Live G42 F 3 2 := fun h => by
    by_contra h'
    exact not_reachable_of_dead {3} [(3, 2)] (by simpa using h') (by decide) (by simp [h])
      (by decide) hr
  fin_cases i
  · exact absurd rfl hi
  · exact ⟨0, l10 (by decide), .base rfl⟩
  · exact ⟨1, l21 (by decide), .of_next (by decide) rfl (l10 (by decide)) (.base rfl)⟩
  · exact ⟨2, l32 rfl, .of_next (by decide) rfl (l21 (by decide))
      (.of_next (show (1 : Fin 4) ≠ 0 by decide) rfl (l10 (by decide)) (.base rfl))⟩

/-- **Lemma 4.2 is false.** On the path `d – 1 – 2 – 3` with no failures the pattern `f42` is
perfectly resilient, but node `2`, which is connected to `d`, forwards packets from `1` and from
`3` alike to `1`: its forwarding function is not a cyclic ordering of its live links. -/
theorem lemma_4_2_false : ∃ f : Pattern G42, PerfectlyResilient G42 0 f ∧
    ∃ (F : Set (Sym2 (Fin 4))) (i : Fin 4), F ⊆ G42.edgeSet ∧ i ≠ 0 ∧ ¬ G42.Adj i 0 ∧
      (G42.deleteEdges F).Reachable i 0 ∧ ¬ RoutesCyclically (f.next i (view G42 F i)) (view G42 F i) := by
  refine ⟨f42, f42_perfect, ∅, 2, Set.empty_subset _, by decide, by decide, ?_, ?_⟩
  · exact (show (G42.deleteEdges ∅).Adj 2 1 by simp; decide).reachable.trans
      (show (G42.deleteEdges ∅).Adj 1 0 by simp; decide).reachable
  · rintro ⟨hbij, -⟩
    have h1 : (1 : Fin 4) ∈ view G42 ∅ 2 := by simp [view, Live]; decide
    have h3 : (3 : Fin 4) ∈ view G42 ∅ 2 := by simp [view, Live]; decide
    exact absurd (hbij.injOn h1 h3 rfl) (by decide)

/-! ### Theorem 3.1 needs a connected network -/

/-- `d = 0` isolated, one link `1 – 2`. -/
abbrev Gdisc : SimpleGraph (Fin 3) := listGraph 3 [(1, 2)]

/-- **Theorem 3.1 fails for disconnected networks**: with the isolated destination of `Gdisc`,
no forwarding pattern is even 0-resilient (packets bounce on the link `12` forever). -/
theorem theorem_3_1_disconnected : ¬ ∃ f : Pattern Gdisc, IsResilient Gdisc 0 f 0 := by
  rintro ⟨f, hf⟩
  have h := (hf ∅ (Set.empty_subset _) (by simp)).2 [1, 2, 1, 2]
  have only : ∀ (i j : Fin 3) (A : Set (Fin 3)) (u : Fin 3), Gdisc.Adj i u →
      (∀ y, Gdisc.Adj i y → y = j) → f.next i A u = j := fun i j A u hu hy =>
    hy _ (f.adj_next i A u hu)
  have l12 : Live Gdisc ∅ 1 2 := by simp [Live]; decide
  have l21 : Live Gdisc ∅ 2 1 := by simp [Live]; decide
  have p := FwdPath.cons (d := 0) (f := f) l12 (by decide)
    (only 2 1 _ 1 (by decide) (by decide))
    (FwdPath.cons l21 (by decide) (only 1 2 _ 2 (by decide) (by decide)) (.single l12))
  exact absurd (h p) (by decide)

/-! ### The destination must be a sink -/

/-- Forwarding paths as literally defined in the paper: no constraint at the destination, so a
path may pass through `d`. -/
inductive FwdPathLit {V : Type*} (G : SimpleGraph V) (d : V) (f : Pattern G)
    (F : Set (Sym2 V)) : List V → Prop
  | single {u v : V} : Live G F u v → FwdPathLit G d f F [u, v]
  | cons {u v w : V} {l : List V} : Live G F u v → (v ≠ d → f.next v (view G F v) u = w) →
      FwdPathLit G d f F (v :: w :: l) → FwdPathLit G d f F (u :: v :: w :: l)

/-- The network `d = 0 – 1`. -/
abbrev K2 : SimpleGraph (Fin 2) := listGraph 2 [(0, 1)]

/-- With the literal definition, every pattern on `d – 1` has the forwarding loop `d, 1, d, 1`
when nothing fails: condition (2) fails, so no pattern is `t`-resilient for any `t`. -/
theorem literal_K2 (f : Pattern K2) :
    FwdPathLit K2 0 f ∅ [0, 1, 0, 1] ∧ ¬ ([0, 1, 0, 1].zip [1, 0, 1] : List (Fin 2 × Fin 2)).Nodup := by
  have l01 : Live K2 ∅ 0 1 := by simp [Live]; decide
  have l10 : Live K2 ∅ 1 0 := by simp [Live]; decide
  have h1 : f.next 1 (view K2 ∅ 1) 0 = 0 := by
    have := f.adj_next 1 (view K2 ∅ 1) 0 (by decide)
    revert this; generalize f.next 1 (view K2 ∅ 1) 0 = y; revert y; decide
  exact ⟨.cons l01 (fun _ => h1) (.cons l10 (fun h => absurd rfl h) (.single l01)), by decide⟩

end Podc.ResilientRouting.Counterexamples
