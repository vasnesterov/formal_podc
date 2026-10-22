import Papers.PODC2016.ShortcutsNoEmbedding.Theorem2

/-!
# Lemma 3 and Corollary 6 of [HIZ16]: verifying the block parameter

Every node of a part must learn whether the part has at most `b₀` block components, in
`O(b₀ (D + c))` rounds. On the supergraph `S` of the part (connected, one node per block) the
paper's procedure is: min-flood IDs for `b₀` supersteps; every leader `r` builds a BFS tree of the
nodes that believe `r` is the leader; neighbouring nodes in different trees report failure;
otherwise the size of the tree is counted and broadcast.

The paper's sketch overlooks that the nodes believing in leader `r` need not be connected to `r`
inside this set (a node can be within distance `b₀` of `r` and of no smaller ID, while every path
to `r` passes through nodes that see a smaller ID). Such nodes are in no BFS tree and cannot learn
the outcome from it. The repaired procedure (all steps are `≤ b₀` supersteps of flooding /
convergecast / broadcast):

1. `lead B`: min-flooding of IDs for `b₀` supersteps;
2. `Reached B`: multi-source BFS for `b₀` supersteps from the sources (`id s = lead s`) along
   edges whose endpoints have the same leader; `B` is reached iff the BFS from its leader's source
   arrives within `b₀` supersteps;
3. `Flag B`: `B` is not reached, or has a neighbour with another leader or not reached (one
   superstep);
4. convergecast over each BFS tree (depth `≤ b₀`) of the number of nodes and of the OR of flags,
   and broadcast of the result (`2 b₀` supersteps). An unreached node outputs "more than `b₀`".

`verification_correct`: in a connected graph, every node outputs "at most `b₀`" (`Accept`) iff the
graph has at most `b₀` nodes. `corollary_6`: applied to the supergraph of a part, the output is
`blockParam P H ≤ b₀`, after `4 b₀ + 1` supersteps.
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset

variable {β : Type*} [Fintype β] [DecidableEq β] (S : SimpleGraph β) [DecidableRel S.Adj]
  (id : β → ℕ) (b₀ : ℕ)

/-- The leader believed by `B` after `b₀` supersteps of min-flooding. -/
noncomputable def lead (B : β) : ℕ := floodMin S id b₀ B

/-- The edges between nodes believing in the same leader. -/
def regionGraph : SimpleGraph β where
  Adj B N := S.Adj B N ∧ lead S id b₀ B = lead S id b₀ N
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => S.loopless.irrefl _ h.1⟩

/-- `B` is reached by the BFS (within `b₀` supersteps) from the source of its leader: a node `s`
with `id s = lead s = lead B`. -/
def Reached (B : β) : Prop :=
  ∃ s, id s = lead S id b₀ s ∧ lead S id b₀ s = lead S id b₀ B ∧
    WalkLE (regionGraph S id b₀) s B b₀

/-- Local failure detection. -/
def Flag (B : β) : Prop :=
  ¬ Reached S id b₀ B ∨
    ∃ N, S.Adj B N ∧ (lead S id b₀ N ≠ lead S id b₀ B ∨ ¬ Reached S id b₀ N)

open Classical in
/-- The BFS tree of `B`'s leader: the reached nodes believing in the same leader. -/
noncomputable def group (B : β) : Finset β :=
  univ.filter fun B' => Reached S id b₀ B' ∧ lead S id b₀ B' = lead S id b₀ B

/-- The output of node `B`: it is reached, no node of its BFS tree raised a flag (an OR
convergecast), and the tree has at most `b₀` nodes (a sum convergecast). -/
def Accept (B : β) : Prop :=
  Reached S id b₀ B ∧ (∀ B' ∈ group S id b₀ B, ¬ Flag S id b₀ B') ∧
    (group S id b₀ B).card ≤ b₀

variable {S id b₀}

theorem mem_group {B B' : β} :
    B' ∈ group S id b₀ B ↔ Reached S id b₀ B' ∧ lead S id b₀ B' = lead S id b₀ B := by
  classical
  unfold group; simp

/-- **Correctness of the verification procedure (Lemma 3 of [HIZ16], repaired).** In a connected
graph, a node accepts iff the graph has at most `b₀` nodes. -/
theorem verification_correct (hS : S.Connected) (B : β) :
    Accept S id b₀ B ↔ Fintype.card β ≤ b₀ := by
  classical
  constructor
  · rintro ⟨hB, hflag, hcard⟩
    -- the group of `B` is closed under adjacency, hence everything
    have hstep : ∀ u v (p : S.Walk u v), u ∈ group S id b₀ B → v ∈ group S id b₀ B := by
      intro u v p
      induction p with
      | nil => exact fun h => h
      | @cons u w v h p ih =>
        intro hu
        apply ih
        have hu' := hflag u hu
        simp only [Flag, not_or, not_exists, not_and, not_not] at hu'
        have := hu'.2 w h
        obtain ⟨-, hu2⟩ := mem_group.1 hu
        exact mem_group.2 ⟨this.2, by rw [this.1, hu2]⟩
    have hall : ∀ X, X ∈ group S id b₀ B := fun X =>
      hstep B X (hS.preconnected B X).some (mem_group.2 ⟨hB, rfl⟩)
    have : group S id b₀ B = univ := eq_univ_of_forall hall
    rw [this, card_univ] at hcard
    exact hcard
  · intro hcard
    -- every node sees the whole graph within `b₀` steps
    have hwalk : ∀ X Y, WalkLE S X Y b₀ := fun X Y =>
      (Connected.walkLE_card hS X Y).mono (by omega)
    have hlead : ∀ X, lead S id b₀ X = univ.inf' (univ_nonempty_iff.mpr ⟨B⟩) id := by
      intro X
      rw [lead, floodMin_spec]
      congr 1
      ext Y; simp [mem_ball, hwalk X Y]
    obtain ⟨s, -, hs⟩ := univ.exists_min_image id (univ_nonempty_iff.mpr ⟨B⟩)
    have hsrc : id s = lead S id b₀ s := by
      rw [hlead]
      exact le_antisymm (Finset.le_inf' _ _ fun Y _ => hs Y (mem_univ Y))
        (Finset.inf'_le _ (mem_univ s))
    have hreach : ∀ X, Reached S id b₀ X := by
      intro X
      refine ⟨s, hsrc, by rw [hlead, hlead], ?_⟩
      obtain ⟨p, hp⟩ := hwalk s X
      refine ⟨p.mapLe (show S ≤ regionGraph S id b₀ from fun u v h => ⟨h, by rw [hlead, hlead]⟩),
        by simpa using hp⟩
    have hgroup : group S id b₀ B = univ :=
      eq_univ_of_forall fun X => mem_group.2 ⟨hreach X, by rw [hlead, hlead]⟩
    refine ⟨hreach B, fun B' _ => ?_, by rw [hgroup, card_univ]; exact hcard⟩
    simp only [Flag, not_or, not_exists, not_and, not_not]
    exact ⟨hreach B', fun N _ => ⟨by rw [hlead, hlead], hreach N⟩⟩

/-- Supersteps of the verification procedure: `b₀` (flooding) + `b₀` (BFS) + `1` (flags) +
`b₀` (convergecast) + `b₀` (broadcast). -/
def verificationSupersteps (b₀ : ℕ) : ℕ := 4 * b₀ + 1

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Corollary 6 of [HIZ16] (Verification).** For a connected part `P` and a shortcut `H`, after
`4 b₀ + 1` supersteps on the supergraph (each taking `≤ 2 (D - 1 + c) + 1` rounds when the shortcut
is `T`-restricted with congestion `≤ c` and `T` has depth `≤ D`, see `theorem_2_intraBlock`),
every block (hence every node of the part) knows whether the part has at most `b₀` block
components. -/
theorem corollary_6 {P : Finset V} (hP : (G.induce (P : Set V)).Connected) (H : Finset (Sym2 V))
    (id : Blocks P H → ℕ) (b₀ : ℕ) (C : Blocks P H) :
    Accept (superGraph G P H) id b₀ C ↔ blockParam P H ≤ b₀ := by
  rw [verification_correct (superGraph_connected hP), card_blocks]

end ShortcutsNoEmbedding
