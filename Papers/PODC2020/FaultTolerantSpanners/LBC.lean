import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
import Mathlib

/-!
# Algorithm 2: the gap problem LBC(t, α) (Section 3.1 of Dinitz–Robelle, PODC'20)

**Length-Bounded Cut.** For terminals `u, v` of an unweighted graph `G`, a *length-`t` cut* is a set
`F ⊆ V \ {u, v}` with `d_{G \ F}(u, v) > t` (`IsLengthCut`). In the gap problem `LBC(t, α)` one must
answer YES if there is a length-`t` cut of size `≤ α` and NO if there is none of size `≤ α t`.

**Algorithm 2** (`lbc`): starting from `F = ∅`, repeat `α + 1` times: look for a `u`–`v` path of
length `≤ t` in `G \ F` (by BFS); if there is none, answer YES; otherwise add the interior vertices of
the path to `F`. After `α + 1` rounds answer NO.

The BFS step is modelled by an arbitrary *short-path oracle* `O` (`ShortPathOracle`): `O G u v t`
returns some `u`–`v` walk of length `≤ t` in `G` if one exists and `none` otherwise
(`ShortPathOracle.Spec`). Theorem 4 is proved for every such oracle, i.e. for every choice of the
path found in each round.

The core of the argument is the generic "frequency" approximation for hitting sets (`hitLoop`), which
we instantiate both for vertex cuts (`lbc`) and edge cuts (`lbcEdge`, the EFT variant).
-/

open Finset SimpleGraph

namespace FaultTolerantSpanners

/-! ### The generic hitting-set loop -/

section HitLoop

variable {X : Type*} [DecidableEq X]

/-- The greedy hitting-set loop: `find F` returns a member of the family disjoint from `F`, if any.
`hitLoop find n F` runs at most `n` rounds; `true` = YES (all members are hit), `false` = NO. -/
def hitLoop (find : Finset X → Option (Finset X)) : ℕ → Finset X → Bool
  | 0, _ => false
  | n + 1, F =>
    match find F with
    | none => true
    | some P => hitLoop find n (F ∪ P)

/-- Specification of `find` for a family `Pf` of subsets of a universe `U`, on inputs `F ⊆ U`. -/
structure FinderSpec (find : Finset X → Option (Finset X)) (U : Finset X) (Pf : Set (Finset X)) :
    Prop where
  subset : ∀ P ∈ Pf, P ⊆ U
  sound : ∀ F ⊆ U, ∀ P, find F = some P → P ∈ Pf ∧ Disjoint P F
  complete : ∀ F ⊆ U, find F = none → ∀ P ∈ Pf, ¬ Disjoint P F

variable {find : Finset X → Option (Finset X)} {U : Finset X} {Pf : Set (Finset X)}

/-- If some `F⋆` hits every member of `Pf`, each round of the loop adds a new element of `F⋆`, so the
loop answers YES once it has more rounds than elements of `F⋆` are missing from `F`. -/
theorem FinderSpec.hitLoop_eq_true (hf : FinderSpec find U Pf) {Fs : Finset X}
    (hFs : ∀ P ∈ Pf, ¬ Disjoint P Fs) :
    ∀ (n : ℕ) (F : Finset X), F ⊆ U → #Fs < n + #(F ∩ Fs) → hitLoop find n F = true := by
  intro n
  induction n with
  | zero =>
    intro F _ h
    have := card_le_card (inter_subset_right (s₁ := F) (s₂ := Fs))
    omega
  | succ n ih =>
    intro F hFU h
    simp only [hitLoop]
    cases hP : find F with
    | none => rfl
    | some P =>
      simp only
      obtain ⟨hPPf, hPF⟩ := hf.sound F hFU P hP
      apply ih _ (union_subset hFU (hf.subset P hPPf))
      obtain ⟨x, hxP, hxFs⟩ := not_disjoint_iff.mp (hFs P hPPf)
      have hxF : x ∉ F := disjoint_left.mp hPF hxP
      have hsub : insert x (F ∩ Fs) ⊆ (F ∪ P) ∩ Fs := by
        intro y hy
        rw [mem_insert] at hy
        rcases hy with rfl | hy
        · exact mem_inter.mpr ⟨mem_union_right _ hxP, hxFs⟩
        · exact mem_inter.mpr ⟨mem_union_left _ (mem_inter.mp hy).1, (mem_inter.mp hy).2⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem (fun h => hxF (mem_inter.mp h).1)] at this
      omega

/-- If the loop answers YES and all members of `Pf` have at most `t` elements, then some `F' ⊆ U`
of size `≤ |F| + (n - 1) t` hits every member of `Pf`. -/
theorem FinderSpec.exists_hitting_of_hitLoop (hf : FinderSpec find U Pf) {t : ℕ}
    (ht : ∀ P ∈ Pf, #P ≤ t) :
    ∀ (n : ℕ) (F : Finset X), F ⊆ U → hitLoop find n F = true →
      ∃ F', F ⊆ F' ∧ F' ⊆ U ∧ #F' + t ≤ #F + n * t ∧ ∀ P ∈ Pf, ¬ Disjoint P F' := by
  intro n
  induction n with
  | zero => intro F _ h; simp [hitLoop] at h
  | succ n ih =>
    intro F hFU h
    simp only [hitLoop] at h
    cases hP : find F with
    | none =>
      exact ⟨F, subset_rfl, hFU, by rw [add_mul]; omega, hf.complete F hFU hP⟩
    | some P =>
      rw [hP] at h
      simp only at h
      obtain ⟨hPPf, -⟩ := hf.sound F hFU P hP
      obtain ⟨F', hF', hF'U, hcard, hhit⟩ := ih _ (union_subset hFU (hf.subset P hPPf)) h
      refine ⟨F', subset_union_left.trans hF', hF'U, ?_, hhit⟩
      have h1 := card_union_le F P
      have h2 := ht P hPPf
      rw [add_mul]
      omega

end HitLoop

/-! ### Short-path oracles (BFS) -/

variable {V : Type*}

/-- A bounded-BFS oracle: on a graph `G`, terminals `u, v` and bound `t`, it may return a `u`–`v`
walk of `G`. -/
def ShortPathOracle (V : Type*) := (G : SimpleGraph V) → (u v : V) → (t : ℕ) → Option (G.Walk u v)

/-- Correctness of a bounded-BFS oracle: it returns a walk of length `≤ t` if there is one
(`d_G(u, v) ≤ t`), and `none` otherwise. -/
structure ShortPathOracle.Spec (O : ShortPathOracle V) : Prop where
  length_le : ∀ G u v t p, O G u v t = some p → p.length ≤ t
  none_iff : ∀ G u v t, O G u v t = none → (t : ℕ∞) < G.edist u v

/-- Correct oracles exist (BFS is one; here we just pick a walk by choice). -/
theorem ShortPathOracle.exists_spec : ∃ O : ShortPathOracle V, O.Spec := by
  classical
  refine ⟨fun G u v t => if h : ∃ p : G.Walk u v, p.length ≤ t then some h.choose else none,
    ⟨fun G u v t p hp => ?_, fun G u v t hp => ?_⟩⟩
  · split_ifs at hp with h
    · cases hp; exact h.choose_spec
  · split_ifs at hp with h
    rw [← not_le, edist_le_coe_iff]
    exact h

/-! ### Algorithm 2 (vertex cuts) -/

section Vertex

variable [DecidableEq V]

/-- A *length-`t` cut* for terminals `u, v`: a set `F ⊆ V \ {u, v}` with `d_{G \ F}(u, v) > t`. -/
def IsLengthCut (G : SimpleGraph V) (u v : V) (t : ℕ) (F : Finset V) : Prop :=
  u ∉ F ∧ v ∉ F ∧ (t : ℕ∞) < (G.deleteVerts F).edist u v

/-- The loop of Algorithm 2: `n` remaining rounds, current set `F`. -/
def lbcLoop (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t : ℕ) :
    ℕ → Finset V → Bool
  | 0, _ => false
  | n + 1, F =>
    match O (G.deleteVerts F) u v t with
    | none => true
    | some p => lbcLoop O G u v t n (F ∪ p.interior)

/-- **Algorithm 2**: decide `LBC(t, α)` for terminals `u, v` in `G`; `true` = YES. -/
def lbc (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t α : ℕ) : Bool :=
  lbcLoop O G u v t (α + 1) ∅

lemma lbcLoop_eq_hitLoop (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t : ℕ) :
    ∀ n F, lbcLoop O G u v t n F =
      hitLoop (fun F => (O (G.deleteVerts F) u v t).map Walk.interior) n F := by
  intro n
  induction n with
  | zero => intro F; rfl
  | succ n ih =>
    intro F
    simp only [lbcLoop, hitLoop]
    cases O (G.deleteVerts F) u v t with
    | none => rfl
    | some p => exact ih _

variable [Fintype V]

/-- The short `u`–`v` walks, seen through their interiors, and the BFS-based finder satisfy the
hitting-set specification on the universe `V \ {u, v}`. -/
lemma finderSpec_vertex {O : ShortPathOracle V} (hO : O.Spec) (G : SimpleGraph V) (u v : V)
    (t : ℕ) :
    FinderSpec (fun F => (O (G.deleteVerts F) u v t).map Walk.interior) (univ \ {u, v})
      {P | ∃ p : G.Walk u v, p.length ≤ t ∧ P = p.interior} := by
  have hsub : ∀ {F : Finset V}, F ⊆ univ \ {u, v} → u ∉ F ∧ v ∉ F := fun hF =>
    ⟨fun h => by simpa using hF h, fun h => by simpa using hF h⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro P ⟨p, -, rfl⟩ x hx
    rw [Walk.mem_interior] at hx
    simp [hx.2.1, hx.2.2]
  · intro F hF P hP
    cases hp : O (G.deleteVerts F) u v t with
    | none => simp [hp] at hP
    | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hP
      subst hP
      refine ⟨⟨p.mapLe (G.deleteVerts_le _), by simpa using hO.length_le _ _ _ _ _ hp,
        (Walk.interior_mapLe _ _).symm⟩, ?_⟩
      rw [Finset.disjoint_left]
      intro x hx hxF
      have hx' := (Walk.mem_interior.mp hx).1
      exact p.not_mem_of_mem_support_deleteVerts (by simpa using (hsub hF).1) x hx'
        (by simpa using hxF)
  · intro F hF hnone
    rintro P ⟨p, hpt, rfl⟩
    have hnone' : O (G.deleteVerts F) u v t = none := by simpa using hnone
    exact (lt_edist_deleteVerts_iff (hsub hF).1 (hsub hF).2).mp (hO.none_iff _ _ _ _ hnone') p hpt

lemma isLengthCut_iff {G : SimpleGraph V} {u v : V} {t : ℕ} {F : Finset V} :
    IsLengthCut G u v t F ↔ F ⊆ univ \ {u, v} ∧
      ∀ P ∈ {P | ∃ p : G.Walk u v, p.length ≤ t ∧ P = p.interior}, ¬ Disjoint P F := by
  constructor
  · rintro ⟨hu, hv, h⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
      rintro (rfl | rfl) <;> contradiction
    · rintro P ⟨p, hpt, rfl⟩
      exact (lt_edist_deleteVerts_iff hu hv).mp h p hpt
  · rintro ⟨hF, h⟩
    have hu : u ∉ F := fun h => by simpa using hF h
    have hv : v ∉ F := fun h => by simpa using hF h
    exact ⟨hu, hv, (lt_edist_deleteVerts_iff hu hv).mpr fun p hpt => h _ ⟨p, hpt, rfl⟩⟩

/-- **Theorem 4 (YES part)**: if there is a length-`t` cut of size `≤ α`, Algorithm 2 answers YES. -/
theorem lbc_eq_true_of_isLengthCut {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {u v : V} {t α : ℕ} {F : Finset V} (hF : IsLengthCut G u v t F) (hFα : #F ≤ α) :
    lbc O G u v t α = true := by
  rw [lbc, lbcLoop_eq_hitLoop]
  exact (finderSpec_vertex hO G u v t).hitLoop_eq_true (isLengthCut_iff.mp hF).2 _ _
    (empty_subset _) (by simp; omega)

/-- **Theorem 4 (NO part, contrapositive form)**: if Algorithm 2 answers YES, there is a length-`t`
cut of size `≤ α t`. -/
theorem exists_isLengthCut_of_lbc {O : ShortPathOracle V} (hO : O.Spec) {G : SimpleGraph V}
    {u v : V} {t α : ℕ} (h : lbc O G u v t α = true) :
    ∃ F, IsLengthCut G u v t F ∧ #F ≤ α * t := by
  rw [lbc, lbcLoop_eq_hitLoop] at h
  obtain ⟨F, -, hFU, hcard, hhit⟩ := (finderSpec_vertex hO G u v t).exists_hitting_of_hitLoop
    (t := t) (by rintro P ⟨p, hpt, rfl⟩; exact (p.card_interior_le).trans hpt) _ _
    (empty_subset _) h
  refine ⟨F, isLengthCut_iff.mpr ⟨hFU, hhit⟩, ?_⟩
  simp only [card_empty, zero_add, add_mul, one_mul] at hcard
  omega

/-- **Theorem 4 of Dinitz–Robelle.** For every correct BFS oracle, Algorithm 2 decides the gap
problem `LBC(t, α)`: it answers YES if there is a length-`t` cut of size `≤ α`, and NO if there is no
length-`t` cut of size `≤ α t`. (Running time: Algorithm 2 makes at most `α + 1` oracle calls, by
construction.) -/
theorem lbc_correct {O : ShortPathOracle V} (hO : O.Spec) (G : SimpleGraph V) (u v : V)
    (t α : ℕ) :
    ((∃ F, IsLengthCut G u v t F ∧ #F ≤ α) → lbc O G u v t α = true) ∧
      ((∀ F, IsLengthCut G u v t F → α * t < #F) → lbc O G u v t α = false) := by
  refine ⟨fun ⟨F, hF, hFα⟩ => lbc_eq_true_of_isLengthCut hO hF hFα, fun h => ?_⟩
  by_contra hne
  obtain ⟨F, hF, hFα⟩ := exists_isLengthCut_of_lbc hO (by simpa using hne)
  exact absurd (h F hF) (not_lt.mpr hFα)

end Vertex

/-! ### Algorithm 2, edge version -/

section Edge

variable [DecidableEq V]

/-- An *edge length-`t` cut* for terminals `u, v`: a set `F` of edges with `d_{G \ F}(u, v) > t`. -/
def IsEdgeLengthCut (G : SimpleGraph V) (u v : V) (t : ℕ) (F : Finset (Sym2 V)) : Prop :=
  (t : ℕ∞) < (G.deleteEdges F).edist u v

/-- The loop of the edge version of Algorithm 2: add the *edges* of the path found. -/
def lbcEdgeLoop (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t : ℕ) :
    ℕ → Finset (Sym2 V) → Bool
  | 0, _ => false
  | n + 1, F =>
    match O (G.deleteEdges F) u v t with
    | none => true
    | some p => lbcEdgeLoop O G u v t n (F ∪ p.edges.toFinset)

/-- **Algorithm 2, edge version**: decide the edge version of `LBC(t, α)`. -/
def lbcEdge (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t α : ℕ) : Bool :=
  lbcEdgeLoop O G u v t (α + 1) ∅

lemma lbcEdgeLoop_eq_hitLoop (O : ShortPathOracle V) (G : SimpleGraph V) (u v : V) (t : ℕ) :
    ∀ n F, lbcEdgeLoop O G u v t n F =
      hitLoop (fun F => (O (G.deleteEdges F) u v t).map (fun p => p.edges.toFinset)) n F := by
  intro n
  induction n with
  | zero => intro F; rfl
  | succ n ih =>
    intro F
    simp only [lbcEdgeLoop, hitLoop]
    cases O (G.deleteEdges F) u v t with
    | none => rfl
    | some p => exact ih _

variable [Fintype V]

lemma finderSpec_edge {O : ShortPathOracle V} (hO : O.Spec) (G : SimpleGraph V) (u v : V)
    (t : ℕ) :
    FinderSpec (fun F => (O (G.deleteEdges F) u v t).map (fun p => p.edges.toFinset)) univ
      {P | ∃ p : G.Walk u v, p.length ≤ t ∧ P = p.edges.toFinset} := by
  refine ⟨fun _ _ => subset_univ _, ?_, ?_⟩
  · intro F _ P hP
    cases hp : O (G.deleteEdges F) u v t with
    | none => simp [hp] at hP
    | some p =>
      simp only [hp, Option.map_some, Option.some.injEq] at hP
      subst hP
      refine ⟨⟨p.mapLe (G.deleteEdges_le _), by simpa using hO.length_le _ _ _ _ _ hp,
        by simp⟩, ?_⟩
      rw [Finset.disjoint_left]
      intro e he heF
      have := p.edges_subset_edgeSet (List.mem_toFinset.mp he)
      rw [edgeSet_deleteEdges] at this
      exact this.2 heF
  · intro F _ hnone
    rintro P ⟨p, hpt, rfl⟩
    have hnone' : O (G.deleteEdges F) u v t = none := by simpa using hnone
    exact lt_edist_deleteEdges_iff.mp (hO.none_iff _ _ _ _ hnone') p hpt

/-- **Theorem 4, edge version.** -/
theorem lbcEdge_correct {O : ShortPathOracle V} (hO : O.Spec) (G : SimpleGraph V) (u v : V)
    (t α : ℕ) :
    ((∃ F, IsEdgeLengthCut G u v t F ∧ #F ≤ α) → lbcEdge O G u v t α = true) ∧
      (lbcEdge O G u v t α = true → ∃ F, IsEdgeLengthCut G u v t F ∧ #F ≤ α * t) := by
  constructor
  · rintro ⟨F, hF, hFα⟩
    rw [lbcEdge, lbcEdgeLoop_eq_hitLoop]
    exact (finderSpec_edge hO G u v t).hitLoop_eq_true
      (by rintro P ⟨p, hpt, rfl⟩; exact lt_edist_deleteEdges_iff.mp hF p hpt) _ _
      (empty_subset _) (by simp; omega)
  · intro h
    rw [lbcEdge, lbcEdgeLoop_eq_hitLoop] at h
    obtain ⟨F, -, -, hcard, hhit⟩ := (finderSpec_edge hO G u v t).exists_hitting_of_hitLoop
      (t := t) (by rintro P ⟨p, hpt, rfl⟩; exact (p.card_edges_toFinset_le).trans hpt) _ _
      (empty_subset _) h
    refine ⟨F, lt_edist_deleteEdges_iff.mpr fun p hpt => hhit _ ⟨p, hpt, rfl⟩, ?_⟩
    simp only [card_empty, zero_add, add_mul, one_mul] at hcard
    omega

end Edge

end FaultTolerantSpanners
