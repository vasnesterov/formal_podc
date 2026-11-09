import Papers.PODC2016.BCCConnectivitySketches.Model
import Papers.PODC2016.BCCConnectivitySketches.Sketch

/-!
# One-round `d`-pruning (Theorem 2)

The `d`-pruning of `G` is a sequence `(x₁, …, x_p)` of nodes such that each `xᵢ` has degree `≤ d`
in `G − {x₁, …, x_{i−1}}` and `G − {x₁, …, x_p}` has minimum degree `> d` (`IsPruning`).

Protocol (Theorem 2): node `i` broadcasts `(dᵢ, f(aᵢ))` (its degree and the sketch of its row,
Lemma 1). Every node then peels locally: it picks the least remaining node `k` whose current
degree is `≤ d`, recovers `k`'s current neighbourhood from its current sketch (injectivity on
`d`-sparse Boolean vectors), removes `k`, and updates the degrees and sketches of `k`'s neighbours
(`(M¹ⱼ − 1, M²ⱼ − f(e_k))`, linearity). This is `peelStep`; after `n` steps nothing changes.

Output: the pruning sequence and the set of edges incident to it (`theorem_2`). The message has
`⌈log₂((n+1)·p)⌉ ≤ (2d+2)⌈log₂(n+1)⌉ + 1` bits (`pruneBits_le`). For `d`-degenerate graphs the
sequence is the whole vertex set and the whole graph is reconstructed (`reconstruct_degenerate`).
-/

namespace Podc.BCCConnectivitySketches

open Finset Cslib.CongestedClique

variable {n : ℕ}

/-! ### `d`-prunings -/

/-- `xs` can be peeled from the vertex set `U`: each element is in the current set and has at most
`d` neighbours there; it is then removed. -/
def PrunesFrom (G : SimpleGraph (Fin n)) (d : ℕ) : Finset (Fin n) → List (Fin n) → Prop
  | _, [] => True
  | U, x :: xs => x ∈ U ∧ (nbrs G x ∩ U).card ≤ d ∧ PrunesFrom G d (U.erase x) xs

/-- `xs` is a `d`-pruning of `G`: each `xᵢ` has degree `≤ d` in `G − {x₁, …, x_{i−1}}`, and every
remaining vertex has more than `d` neighbours among the remaining vertices. -/
def IsPruning (G : SimpleGraph (Fin n)) (d : ℕ) (xs : List (Fin n)) : Prop :=
  PrunesFrom G d univ xs ∧ ∀ v, v ∉ xs → d < (nbrs G v ∩ (univ \ xs.toFinset)).card

lemma prunesFrom_append_singleton (G : SimpleGraph (Fin n)) (d : ℕ) (k : Fin n) :
    ∀ (xs : List (Fin n)) (U : Finset (Fin n)), PrunesFrom G d U (xs ++ [k]) ↔
      PrunesFrom G d U xs ∧ k ∈ U \ xs.toFinset ∧ (nbrs G k ∩ (U \ xs.toFinset)).card ≤ d
  | [], U => by simp [PrunesFrom]
  | x :: xs, U => by
      have e : U \ (x :: xs).toFinset = U.erase x \ xs.toFinset := by
        rw [List.toFinset_cons, sdiff_insert, erase_sdiff_comm]
      simp only [List.cons_append, PrunesFrom, prunesFrom_append_singleton G d k xs, e]
      tauto

lemma PrunesFrom.nodup {G : SimpleGraph (Fin n)} {d : ℕ} :
    ∀ {xs : List (Fin n)} {U : Finset (Fin n)}, PrunesFrom G d U xs → ∀ y ∈ xs, y ∈ U
  | [], _, _ => by simp
  | x :: xs, U, ⟨hx, _, h⟩ => by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact mem_of_mem_erase (h.nodup y hy)

/-- A `d`-pruning of a `d`-degenerate graph contains every vertex. -/
theorem IsPruning.mem_of_degenerate {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {d : ℕ}
    {xs : List (Fin n)} (h : IsPruning G d xs) (hG : Podc.CongestedCliquePower.IsDegenerate G d)
    (v : Fin n) : v ∈ xs := by
  by_contra hv
  obtain ⟨w, hw, hwd⟩ := hG (univ \ xs.toFinset) ⟨v, by simpa using hv⟩
  have hw' : w ∉ xs := by simpa using hw
  have e : (univ \ xs.toFinset).filter (G.Adj w) = nbrs G w ∩ (univ \ xs.toFinset) := by
    ext y; simp [and_comm]
  rw [e] at hwd
  exact absurd (h.2 w hw') (not_lt.2 hwd)

/-! ### The peeling performed by every node -/

section Peel

variable (n) (d : ℕ)

/-- The field of the sketches. -/
abbrev P := ZMod (sketchPrime n d)

/-- The message of a node: degree and sketch of its row. -/
abbrev PMsg := Fin (n + 1) × P n d

/-- The message of node `v` with row `N`. -/
noncomputable def pruneMsg (_v : Fin n) (N : Finset (Fin n)) : PMsg n d :=
  (⟨N.card, Nat.lt_succ_of_le ((card_le_univ N).trans (by simp))⟩, sk (sketchPoint n d) N)

/-- Recover a set of size `≤ d` from its sketch. -/
noncomputable def decode (z : P n d) : Finset (Fin n) :=
  if h : ∃ S : Finset (Fin n), S.card ≤ d ∧ sk (sketchPoint n d) S = z then h.choose else ∅

lemma decode_sk {S : Finset (Fin n)} (hS : S.card ≤ d) : decode n d (sk (sketchPoint n d) S) = S := by
  have h : ∃ S' : Finset (Fin n), S'.card ≤ d ∧ sk (sketchPoint n d) S' = sk (sketchPoint n d) S :=
    ⟨S, hS, rfl⟩
  rw [decode, dite_eq_left_of_eq_true (eq_true h)]
  exact sk_injOn n d h.choose_spec.1 hS h.choose_spec.2

/-- Local state of the peeling: remaining vertices, current (degree, sketch) of every vertex,
the pruning sequence so far, the recovered edges. -/
structure PState where
  /-- Remaining vertices. -/
  U : Finset (Fin n)
  /-- Current degree and sketch. -/
  D : Fin n → ℕ × P n d
  /-- Pruned vertices, in order. -/
  xs : List (Fin n)
  /-- Recovered edges (those incident to `xs`). -/
  E : Finset (Sym2 (Fin n))

variable {n d}

/-- Remaining vertices of current degree `≤ d`. -/
def PState.low (st : PState n d) : Finset (Fin n) := st.U.filter fun k => (st.D k).1 ≤ d

/-- One peeling step. -/
noncomputable def peelStep (st : PState n d) : PState n d :=
  if h : st.low.Nonempty then
    let k := st.low.min' h
    let S := decode n d (st.D k).2
    { U := st.U.erase k
      D := fun j => if j ∈ S then ((st.D j).1 - 1, (st.D j).2 - sketchPoint n d ^ (k : ℕ)) else st.D j
      xs := st.xs ++ [k]
      E := st.E ∪ S.image fun j => s(k, j) }
  else st

variable (n d)

/-- The decoder: start from the received messages and peel `n` times. -/
noncomputable def pruneDec (m : Fin n → PMsg n d) : List (Fin n) × Finset (Sym2 (Fin n)) :=
  let st := peelStep^[n] ⟨univ, fun j => ((m j).1.val, (m j).2), [], ∅⟩
  (st.xs, st.E)

variable {n d}

/-- The invariant of the peeling, relative to the input graph `G`. -/
structure Inv (G : SimpleGraph (Fin n)) (st : PState n d) : Prop where
  D_eq : ∀ j ∈ st.U, st.D j = ((nbrs G j ∩ st.U).card, sk (sketchPoint n d) (nbrs G j ∩ st.U))
  U_eq : st.U = univ \ st.xs.toFinset
  prunes : PrunesFrom G d univ st.xs
  E_eq : ∀ e, e ∈ st.E ↔ e ∈ G.edgeSet ∧ ∃ y ∈ st.xs, y ∈ e

lemma Inv.step {G : SimpleGraph (Fin n)} {st : PState n d} (hI : Inv G st) : Inv G (peelStep st) := by
  unfold peelStep
  split_ifs with h
  swap
  · exact hI
  set k := st.low.min' h
  have hk : k ∈ st.low := min'_mem _ h
  simp only [PState.low, mem_filter] at hk
  obtain ⟨hkU, hkd⟩ := hk
  rw [hI.D_eq k hkU] at hkd
  simp only at hkd
  have hS : decode n d (st.D k).2 = nbrs G k ∩ st.U := by
    rw [hI.D_eq k hkU]; exact decode_sk n d hkd
  have hkxs : k ∉ st.xs := by
    have := hI.U_eq ▸ hkU; simpa using this
  simp only [hS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    have hjU := mem_of_mem_erase hj
    have hjk := ne_of_mem_erase hj
    simp only
    split_ifs with hjS
    · have hkj : k ∈ nbrs G j ∩ st.U := by
        simp only [mem_inter, mem_nbrs] at hjS ⊢
        exact ⟨hjS.1.symm, hkU⟩
      have e : nbrs G j ∩ st.U.erase k = (nbrs G j ∩ st.U).erase k := by
        rw [inter_erase]
      rw [hI.D_eq j hjU, e, card_erase_of_mem hkj, sk_erase _ _ hkj]
    · have hkj : k ∉ nbrs G j := by
        simp only [mem_inter, mem_nbrs, not_and] at hjS ⊢
        exact fun h' => hjS h'.symm hjU
      have e : nbrs G j ∩ st.U.erase k = nbrs G j ∩ st.U := by
        rw [inter_erase, erase_eq_of_notMem (fun h' => hkj (mem_inter.1 h').1)]
      rw [hI.D_eq j hjU, e]
  · rw [hI.U_eq]
    ext y
    simp only [mem_erase, mem_sdiff, mem_univ, true_and, List.toFinset_append, mem_union,
      List.mem_toFinset, List.mem_singleton]
    tauto
  · rw [prunesFrom_append_singleton]
    refine ⟨hI.prunes, by simpa using hkxs, ?_⟩
    rw [← hI.U_eq]
    exact hkd
  · intro e
    simp only [mem_union, hI.E_eq, mem_image, mem_inter, mem_nbrs, List.mem_append,
      List.mem_singleton]
    constructor
    · rintro (⟨he, y, hy, hye⟩ | ⟨j, ⟨hkj, _⟩, rfl⟩)
      · exact ⟨he, y, Or.inl hy, hye⟩
      · exact ⟨hkj, k, Or.inr rfl, Sym2.mem_mk_left _ _⟩
    · rintro ⟨he, y, hy | rfl, hye⟩
      · exact Or.inl ⟨he, y, hy, hye⟩
      · by_cases hx : ∃ z ∈ st.xs, z ∈ e
        · exact Or.inl ⟨he, hx⟩
        · right
          obtain ⟨j, rfl⟩ := Sym2.mem_iff_exists.1 hye
          refine ⟨j, ⟨he, ?_⟩, rfl⟩
          rw [hI.U_eq]
          simp only [mem_sdiff, mem_univ, List.mem_toFinset, true_and]
          exact fun hj => hx ⟨j, hj, Sym2.mem_mk_right _ _⟩

lemma peelStep_U_card (st : PState n d) :
    ¬ st.low.Nonempty ∧ peelStep st = st ∨ (peelStep st).U.card + 1 = st.U.card := by
  unfold peelStep
  split_ifs with h
  · right
    have hk : st.low.min' h ∈ st.low := min'_mem _ h
    simp only [PState.low, mem_filter] at hk
    exact card_erase_add_one hk.1
  · exact Or.inl ⟨h, rfl⟩

/-- After `t` steps: either stuck, or `t` vertices were removed. -/
lemma peel_iter (st : PState n d) :
    ∀ t, ¬ (peelStep^[t] st).low.Nonempty ∨ (peelStep^[t] st).U.card + t ≤ st.U.card
  | 0 => Or.inr (by simp)
  | t + 1 => by
      rw [Function.iterate_succ_apply']
      rcases peel_iter st t with h | h
      · rcases peelStep_U_card (peelStep^[t] st) with ⟨h1, h2⟩ | h2
        · left; rw [h2]; exact h1
        · exfalso
          apply h
          unfold peelStep at h2
          split_ifs at h2 with h3
          · exact h3
          · omega
      · rcases peelStep_U_card (peelStep^[t] st) with ⟨h1, h2⟩ | h2
        · left; rw [h2]; exact h1
        · right; omega

/-- **Correctness of the local peeling**: from the messages of `G`, the decoder outputs a
`d`-pruning of `G` and the set of all edges of `G` incident to it. -/
theorem pruneDec_spec (G : SimpleGraph (Fin n)) :
    IsPruning G d (pruneDec n d fun v => pruneMsg n d v (nbrs G v)).1 ∧
      ∀ e, e ∈ (pruneDec n d fun v => pruneMsg n d v (nbrs G v)).2 ↔
        e ∈ G.edgeSet ∧ ∃ y ∈ (pruneDec n d fun v => pruneMsg n d v (nbrs G v)).1, y ∈ e := by
  set st0 : PState n d := ⟨univ, fun j => (((pruneMsg n d j (nbrs G j)).1 : ℕ),
    (pruneMsg n d j (nbrs G j)).2), [], ∅⟩
  show IsPruning G d (peelStep^[n] st0).xs ∧ ∀ e, e ∈ (peelStep^[n] st0).E ↔
    e ∈ G.edgeSet ∧ ∃ y ∈ (peelStep^[n] st0).xs, y ∈ e
  have h0 : Inv G st0 := by
    refine ⟨fun j _ => ?_, by simp [st0], trivial, fun e => by simp [st0]⟩
    simp [st0, pruneMsg]
  have hI : ∀ t, Inv G (peelStep^[t] st0) := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => rw [Function.iterate_succ_apply']; exact ih.step
  have hstuck : ¬ (peelStep^[n] st0).low.Nonempty := by
    rcases peel_iter st0 n with h | h
    · exact h
    · have hU : (peelStep^[n] st0).U = ∅ := by
        have : st0.U.card = n := by simp [st0]
        exact card_eq_zero.1 (by omega)
      simp [PState.low, hU]
  set st := peelStep^[n] st0
  have hIn := hI n
  refine ⟨⟨hIn.prunes, fun v hv => ?_⟩, hIn.E_eq⟩
  have hvU : v ∈ st.U := by rw [hIn.U_eq]; simpa using hv
  have := hIn.D_eq v hvU
  rw [← hIn.U_eq]
  by_contra hle
  apply hstuck
  refine ⟨v, mem_filter.2 ⟨hvU, ?_⟩⟩
  rw [this]
  exact not_lt.1 hle

end Peel

/-! ### Theorem 2 -/

/-- Bits per message of the pruning protocol: `⌈log₂((n+1) · p)⌉`. -/
noncomputable def pruneBits (n d : ℕ) : ℕ := Nat.clog 2 ((n + 1) * sketchPrime n d)

/-- The pruning protocol as a typed one-round algorithm. -/
noncomputable def pruneAlg (n d : ℕ) :
    TAlg (Fin n) (Finset (Fin n)) (Finset (Fin n) × Option (List (Fin n) × Finset (Sym2 (Fin n))))
      (PMsg n d) :=
  TAlg.oneRound (pruneMsg n d) (pruneDec n d)

lemma card_pmsg (n d : ℕ) : Fintype.card (PMsg n d) ≤ 2 ^ pruneBits n d := by
  simp only [PMsg, P, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  exact card_le_two_pow_clog _

/-- The pruning protocol in `BClique[pruneBits n d]`. -/
noncomputable def pruneBcast (n d : ℕ) :
    Bcast.Algorithm (Fin n) (Finset (Fin n))
      (Finset (Fin n) × Option (List (Fin n) × Finset (Sym2 (Fin n)))) (pruneBits n d) :=
  (pruneAlg n d).toBits _ (card_pmsg n d)

lemma pruneBcast_run (G : SimpleGraph (Fin n)) (d : ℕ) (v : Fin n) :
    (pruneBcast n d).run (nbrs G) 1 v =
      (nbrs G v, some (pruneDec n d fun w => pruneMsg n d w (nbrs G w))) := by
  rw [pruneBcast, TAlg.run_toBits]; rfl

/-- **Theorem 2** of [Montealegre–Todinca]: a deterministic one-round protocol in
`BClique[pruneBits n d]` (`pruneBits n d = O(d log n)`, see `pruneBits_le`) after which every node
knows a `d`-pruning `xs` of the input graph `G` together with all edges of `G` incident to `xs`. -/
theorem theorem_2 (n d : ℕ) :
    ∃ (σ : Type) (A : Bcast.Algorithm (Fin n) (Finset (Fin n)) σ (pruneBits n d))
      (out : σ → List (Fin n) × Finset (Sym2 (Fin n))),
      ∀ (G : SimpleGraph (Fin n)) (v : Fin n),
        IsPruning G d (out (A.run (nbrs G) 1 v)).1 ∧
        ∀ e, e ∈ (out (A.run (nbrs G) 1 v)).2 ↔
          e ∈ G.edgeSet ∧ ∃ y ∈ (out (A.run (nbrs G) 1 v)).1, y ∈ e := by
  refine ⟨_, pruneBcast n d, fun s => s.2.getD ([], ∅), fun G v => ?_⟩
  rw [pruneBcast_run]
  exact pruneDec_spec G

/-- The message size of Theorem 2 is `O(d log n)`: `pruneBits n d ≤ (2d + 2)⌈log₂(n+1)⌉ + 1`. -/
theorem pruneBits_le {n : ℕ} (hn : 0 < n) (d : ℕ) :
    pruneBits n d ≤ (2 * d + 2) * Nat.clog 2 (n + 1) + 1 := by
  unfold pruneBits
  apply Nat.clog_le_of_le_pow
  have hp := sketchPrime_le hn d
  have hc : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := card_le_two_pow_clog _
  calc (n + 1) * sketchPrime n d ≤ (n + 1) * (2 * ((1 + n) ^ (2 * d) * n)) :=
        Nat.mul_le_mul_left _ hp
    _ ≤ 2 * (n + 1) ^ (2 * d + 2) := by
        rw [add_comm 1 n]
        have : n ≤ n + 1 := by omega
        calc (n + 1) * (2 * ((n + 1) ^ (2 * d) * n))
            ≤ (n + 1) * (2 * ((n + 1) ^ (2 * d) * (n + 1))) := by gcongr
          _ = 2 * (n + 1) ^ (2 * d + 2) := by ring
    _ ≤ 2 * (2 ^ Nat.clog 2 (n + 1)) ^ (2 * d + 2) := by gcongr
    _ = 2 ^ ((2 * d + 2) * Nat.clog 2 (n + 1) + 1) := by ring

/-- Reconstruction of `d`-degenerate graphs (the special case of Becker et al.): for a
`d`-degenerate `G`, the pruning of Theorem 2 contains every vertex and the recovered edge set is
the edge set of `G`. -/
theorem reconstruct_degenerate {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {d : ℕ}
    (hG : Podc.CongestedCliquePower.IsDegenerate G d) {xs : List (Fin n)}
    {E : Finset (Sym2 (Fin n))} (hxs : IsPruning G d xs)
    (hE : ∀ e, e ∈ E ↔ e ∈ G.edgeSet ∧ ∃ y ∈ xs, y ∈ e) : (E : Set (Sym2 (Fin n))) = G.edgeSet := by
  ext e
  rw [mem_coe, hE]
  constructor
  · exact fun h => h.1
  · intro he
    refine ⟨he, ?_⟩
    induction e using Sym2.ind with
    | h a b => exact ⟨a, hxs.mem_of_degenerate hG a, Sym2.mem_mk_left _ _⟩

end Podc.BCCConnectivitySketches
