import Papers.PODC2020.TightBipartiteMatching.UpperBoundLabels
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Upper bound, part 2: the proposal algorithm and its invariants

Brandt–Olivetti, *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants*, PODC 2020,
§5.

The algorithm of §5, written as a synchronous local process (`Algorithm.ofLocal`) on a
`Δ`-regular, properly 2-coloured port-numbered graph. Every node keeps sets of ports
(`St`): `M` (matched), `S` (proposals sent), `R` (proposals received) and `B` (the batch of
proposals sent in the node's most recent proposing round; this is implicit in the paper and is used
only to bound the number of `M` edges by `y`). In round `r` the nodes of colour `act a0 r` are
active (`a0` is the colour active in round `0`; the roles alternate):

* an active node with `M = ∅` accepts the smallest port of `R` if `R ≠ ∅` (`St.acc`), and otherwise
  proposes over the `min(y, #free)` smallest ports not in `S` (`St.prop`, `batch`);
* a passive node with `M = ∅` records the acceptances it receives in `M` and the proposals it
  receives in `R`;
* nodes with `M ≠ ∅` do nothing.

`Inv` collects the invariants (consistency of `M` across edges, `|M| ≤ y`, "every proposal is
answered within one round", and the count of sent proposals); `inv_cfg` proves them for every
round.
-/

namespace TightBipartiteMatching

namespace UpperBound

open Finset Cslib.PortNumbering Cslib.PortNumbering.Algorithm

/-- The local state of a node: its colour and four sets of ports. -/
structure St where
  /-- The colour (`true` = white). -/
  col : Bool
  /-- Matched ports. -/
  M : Finset ℕ
  /-- Ports over which a proposal was sent. -/
  S : Finset ℕ
  /-- Ports over which a proposal was received. -/
  R : Finset ℕ
  /-- The ports of the most recent batch of proposals. -/
  B : Finset ℕ

/-- Initial state. -/
def St.init (c : Bool) : St := ⟨c, ∅, ∅, ∅, ∅⟩

/-- Pick one element (the smallest) of a nonempty set of ports. -/
def pick (R : Finset ℕ) : Finset ℕ := if h : R.Nonempty then {R.min' h} else ∅

theorem pick_subset (R : Finset ℕ) : pick R ⊆ R := by
  unfold pick; split_ifs with h
  · simpa using R.min'_mem h
  · exact empty_subset _

theorem card_pick_le (R : Finset ℕ) : (pick R).card ≤ 1 := by
  unfold pick; split_ifs <;> simp

theorem pick_eq_empty {R : Finset ℕ} : pick R = ∅ ↔ R = ∅ := by
  unfold pick; split_ifs with h
  · simp [h.ne_empty]
  · simp [not_nonempty_iff_eq_empty.1 h]

/-- The (at most) `y` smallest ports `< Δ` not in `S`. -/
def batch (Δ y : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (((range Δ).filter (· ∉ S)).sort.take y).toFinset

theorem mem_batch {Δ y : ℕ} {S : Finset ℕ} {i : ℕ} (h : i ∈ batch Δ y S) : i < Δ ∧ i ∉ S := by
  unfold batch at h
  have := List.mem_of_mem_take (List.mem_toFinset.1 h)
  simpa using this

theorem card_batch (Δ y : ℕ) (S : Finset ℕ) :
    (batch Δ y S).card = min y ((range Δ).filter (· ∉ S)).card := by
  unfold batch
  rw [List.toFinset_card_of_nodup ((sort_nodup _ _).sublist (List.take_sublist _ _)),
    List.length_take, length_sort]

theorem card_union_batch {Δ y : ℕ} {S : Finset ℕ} (hS : S ⊆ range Δ) :
    (S ∪ batch Δ y S).card = min Δ (S.card + y) := by
  rw [card_union_of_disjoint (disjoint_left.2 fun i hi hb => (mem_batch hb).2 hi), card_batch,
    ← sdiff_eq_filter, card_sdiff_of_subset hS, card_range]
  have := card_le_card hS
  rw [card_range] at this
  omega

/-- The colour active in round `r`, when colour `a0` is active in round `0`. -/
def act (a0 : Bool) (r : ℕ) : Bool := if r % 2 = 0 then a0 else !a0

theorem act_succ (a0 : Bool) (r : ℕ) : act a0 (r + 1) = !act a0 r := by
  unfold act
  rcases Nat.mod_two_eq_zero_or_one r with h | h
  · have : (r + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (r + 1) % 2 = 0 := by omega
    simp [h, this]

/-- The number of rounds `< t` in which colour `c` is active. -/
def nact (a0 c : Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => nact a0 c t + if act a0 t = c then 1 else 0

namespace St

/-- The ports over which an (active) node sends an acceptance. -/
def acc (s : St) : Finset ℕ := if s.M = ∅ then pick s.R else ∅

/-- The ports over which an (active) node sends a proposal. -/
def prop (Δ y : ℕ) (s : St) : Finset ℕ := if s.M = ∅ ∧ s.R = ∅ then batch Δ y s.S else ∅

theorem acc_subset (s : St) : s.acc ⊆ s.R := by
  unfold acc; split_ifs
  · exact pick_subset _
  · exact empty_subset _

theorem mem_acc {s : St} {i : ℕ} : i ∈ s.acc ↔ s.M = ∅ ∧ i ∈ pick s.R := by
  unfold acc; split_ifs with h <;> simp [h]

theorem mem_prop {Δ y : ℕ} {s : St} {i : ℕ} :
    i ∈ s.prop Δ y ↔ s.M = ∅ ∧ s.R = ∅ ∧ i ∈ batch Δ y s.S := by
  unfold prop; split_ifs with h
  · simp [h]
  · simp only [notMem_empty, false_iff]
    exact fun h' => h ⟨h'.1, h'.2.1⟩

theorem union_acc_eq_empty {s : St} : s.M ∪ s.acc = ∅ ↔ s.M = ∅ ∧ s.R = ∅ := by
  rw [union_eq_empty]
  unfold acc
  constructor
  · rintro ⟨h1, h2⟩
    rw [ite_eq_left h1, pick_eq_empty] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [ite_eq_left h1, pick_eq_empty]
    exact ⟨h1, h2⟩

end St

/-- The ports `i < Δ` such that the neighbour behind `i` "sends over its port" according to `f`
(`f` is `St.acc` or `St.prop Δ y`). -/
def recvd (Δ : ℕ) (f : St → Finset ℕ) (nb : ℕ → Option (St × ℕ)) : Finset ℕ :=
  (range Δ).filter fun i => (nb i).map (fun q => decide (q.2 ∈ f q.1)) = some true

/-- One round of the algorithm at a node in state `s` (round `r`, degree ignored), given the
states and port numbers of its neighbours `nb`. -/
def step (Δ y : ℕ) (a0 : Bool) (r _deg : ℕ) (s : St) (nb : ℕ → Option (St × ℕ)) : St :=
  if s.col = act a0 r then
    { s with M := s.M ∪ s.acc, S := s.S ∪ s.prop Δ y,
             B := if s.M = ∅ ∧ s.R = ∅ then batch Δ y s.S else s.B }
  else if s.M = ∅ then
    { s with M := recvd Δ St.acc nb, R := s.R ∪ recvd Δ (St.prop Δ y) nb }
  else s

theorem step_col (Δ y : ℕ) (a0 : Bool) (r dg : ℕ) (s : St) (nb : ℕ → Option (St × ℕ)) :
    (step Δ y a0 r dg s nb).col = s.col := by
  unfold step; split_ifs <;> rfl

theorem mem_recvd {V : Type} {G : PNGraph V} {Δ : ℕ} {c : V → St} {v : V} (hdeg : G.deg v = Δ)
    {f : St → Finset ℕ} {i : ℕ} :
    i ∈ recvd Δ f (nbrInfo G c v) ↔ i < Δ ∧ G.rport v i ∈ f (c (G.nbr v i)) := by
  simp only [recvd, mem_filter, mem_range, nbrInfo, hdeg]
  constructor
  · rintro ⟨h1, h2⟩
    rw [ite_eq_left h1] at h2
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [ite_eq_left h1]
    simpa using h2

section Invariants

variable {V : Type} (G : PNGraph V) (Δ y : ℕ) (a0 : Bool) (col : V → Bool)

/-- The invariants of the configuration `c` after `t` rounds. -/
structure Inv (t : ℕ) (c : V → St) : Prop where
  col_eq : ∀ v, (c v).col = col v
  M_sub : ∀ v, (c v).M ⊆ range Δ
  R_sub : ∀ v, (c v).R ⊆ range Δ
  S_sub : ∀ v, (c v).S ⊆ range Δ
  M_card : ∀ v, (c v).M.card ≤ y
  B_card : ∀ v, (c v).B.card ≤ y
  /-- `M` is consistent across edges. -/
  cons : ∀ v i, i < Δ → (i ∈ (c v).M ↔ G.rport v i ∈ (c (G.nbr v i)).M)
  /-- An unmatched node that is active next has received its proposals in the previous round:
  the proposer is unmatched and the port belongs to its last batch. -/
  recv : ∀ w j, col w = act a0 t → (c w).M = ∅ → j ∈ (c w).R →
    (c (G.nbr w j)).M = ∅ ∧ G.rport w j ∈ (c (G.nbr w j)).B
  /-- An unmatched node that was active in the previous round has no pending proposals. -/
  passive : ∀ w, col w ≠ act a0 t → (c w).M = ∅ → (c w).R = ∅
  /-- Every proposal reaches a matched node or is pending there. -/
  sent : ∀ v i, i ∈ (c v).S → (c (G.nbr v i)).M ≠ ∅ ∨ G.rport v i ∈ (c (G.nbr v i)).R
  /-- An unmatched node without pending proposals has proposed in all its active rounds. -/
  count : ∀ v, (c v).M = ∅ → (c v).R = ∅ → min Δ (y * nact a0 (col v) t) ≤ (c v).S.card

variable {G Δ y a0 col}

theorem inv_zero : Inv G Δ y a0 col 0 (fun v => St.init (col v)) where
  col_eq _ := rfl
  M_sub _ := empty_subset _
  R_sub _ := empty_subset _
  S_sub _ := empty_subset _
  M_card _ := by simp [St.init]
  B_card _ := by simp [St.init]
  cons _ _ _ := by simp [St.init]
  recv _ _ _ _ h := by simp [St.init] at h
  passive _ _ _ := rfl
  sent _ _ h := by simp [St.init] at h
  count _ _ _ := by simp [nact]

theorem Inv.next (hy : 1 ≤ y) (hdeg : ∀ v, G.deg v = Δ)
    (hcol : ∀ v i, i < Δ → col (G.nbr v i) = !col v) {t : ℕ} {c : V → St}
    (h : Inv G Δ y a0 col t c) :
    Inv G Δ y a0 col (t + 1) (fun v => step Δ y a0 t (G.deg v) (c v) (nbrInfo G c v)) := by
  set c' := fun v => step Δ y a0 t (G.deg v) (c v) (nbrInfo G c v) with hc'
  have nn : ∀ v i, i < Δ → G.nbr (G.nbr v i) (G.rport v i) = v :=
    fun v i hi => G.nbr_nbr (by rw [hdeg]; exact hi)
  have rr : ∀ v i, i < Δ → G.rport (G.nbr v i) (G.rport v i) = i :=
    fun v i hi => G.rport_rport (by rw [hdeg]; exact hi)
  have rl : ∀ v i, i < Δ → G.rport v i < Δ := fun v i hi => by
    have := G.rport_lt (v := v) (i := i) (by rw [hdeg]; exact hi)
    rwa [hdeg] at this
  have hrecvd : ∀ v f i,
      i ∈ recvd Δ f (nbrInfo G c v) ↔ i < Δ ∧ G.rport v i ∈ f (c (G.nbr v i)) :=
    fun v f i => mem_recvd (hdeg v)
  have flip : ∀ v i, i < Δ → (col (G.nbr v i) = act a0 t ↔ col v ≠ act a0 t) := by
    intro v i hi
    rw [hcol v i hi]
    cases col v <;> cases act a0 t <;> simp
  have hA : ∀ v, col v = act a0 t → c' v = { c v with
      M := (c v).M ∪ (c v).acc, S := (c v).S ∪ (c v).prop Δ y,
      B := if (c v).M = ∅ ∧ (c v).R = ∅ then batch Δ y (c v).S else (c v).B } := by
    intro v hv
    show step _ _ _ _ _ _ _ = _
    unfold step
    rw [ite_eq_left (by rw [h.col_eq]; exact hv)]
  have hP : ∀ v, col v ≠ act a0 t → (c v).M = ∅ → c' v = { c v with
      M := recvd Δ St.acc (nbrInfo G c v),
      R := (c v).R ∪ recvd Δ (St.prop Δ y) (nbrInfo G c v) } := by
    intro v hv hM
    show step _ _ _ _ _ _ _ = _
    unfold step
    rw [ite_eq_right (by rw [h.col_eq]; exact hv), ite_eq_left hM]
  have hQ : ∀ v, col v ≠ act a0 t → (c v).M ≠ ∅ → c' v = c v := by
    intro v hv hM
    show step _ _ _ _ _ _ _ = _
    unfold step
    rw [ite_eq_right (by rw [h.col_eq]; exact hv), ite_eq_right hM]
  -- monotonicity
  have monoM : ∀ v, (c v).M ⊆ (c' v).M := by
    intro v
    by_cases hv : col v = act a0 t
    · rw [hA v hv]; exact subset_union_left
    · by_cases hM : (c v).M = ∅
      · rw [hM]; exact empty_subset _
      · rw [hQ v hv hM]
  have monoR : ∀ v, (c v).R ⊆ (c' v).R := by
    intro v
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]; exact subset_union_left
      · rw [hQ v hv hM]
  have emptyM : ∀ v, (c' v).M = ∅ → (c v).M = ∅ := fun v h0 =>
    subset_empty.1 (h0 ▸ monoM v)
  have neM : ∀ v, (c v).M ≠ ∅ → (c' v).M ≠ ∅ := fun v h1 h0 => h1 (emptyM v h0)
  -- the consistency of `M`, one direction
  have fwd : ∀ v i, i < Δ → i ∈ (c' v).M → G.rport v i ∈ (c' (G.nbr v i)).M := by
    intro v i hi hiM
    by_cases hold : i ∈ (c v).M
    · exact monoM _ ((h.cons v i hi).1 hold)
    · by_cases hv : col v = act a0 t
      · rw [hA v hv] at hiM
        have hacc : i ∈ (c v).acc := (mem_union.1 hiM).resolve_left hold
        obtain ⟨hMv, hpick⟩ := St.mem_acc.1 hacc
        obtain ⟨hMw, -⟩ := h.recv v i hv hMv (pick_subset _ hpick)
        have hw : col (G.nbr v i) ≠ act a0 t := by
          rw [Ne, flip v i hi]; exact not_not.2 hv
        rw [hP _ hw hMw]
        show _ ∈ recvd _ _ _
        rw [hrecvd, nn v i hi, rr v i hi]
        exact ⟨rl v i hi, hacc⟩
      · by_cases hMv : (c v).M = ∅
        · rw [hP v hv hMv] at hiM
          change i ∈ recvd _ _ _ at hiM
          rw [hrecvd] at hiM
          rw [hA _ ((flip v i hi).2 hv)]
          exact mem_union_right _ hiM.2
        · rw [hQ v hv hMv] at hiM; exact absurd hiM hold
  refine
    { col_eq := fun v => by rw [hc', step_col, h.col_eq]
      M_sub := fun v => ?_
      R_sub := fun v => ?_
      S_sub := fun v => ?_
      M_card := fun v => ?_
      B_card := fun v => ?_
      cons := fun v i hi => ⟨fwd v i hi, fun hj => ?_⟩
      recv := fun w j hw hM'w hj' => ?_
      passive := fun w hw hM'w => ?_
      sent := fun v i hi' => ?_
      count := fun v hM' hR' => ?_ }
  · -- M_sub
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
      exact union_subset (h.M_sub v) ((St.acc_subset _).trans (h.R_sub v))
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]; exact filter_subset _ _
      · rw [hQ v hv hM]; exact h.M_sub v
  · -- R_sub
    by_cases hv : col v = act a0 t
    · rw [hA v hv]; exact h.R_sub v
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]; exact union_subset (h.R_sub v) (filter_subset _ _)
      · rw [hQ v hv hM]; exact h.R_sub v
  · -- S_sub
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
      refine union_subset (h.S_sub v) fun i hi => ?_
      exact mem_range.2 (mem_batch (St.mem_prop.1 hi).2.2).1
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]; exact h.S_sub v
      · rw [hQ v hv hM]; exact h.S_sub v
  · -- M_card
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
      show ((c v).M ∪ (c v).acc).card ≤ y
      by_cases hM : (c v).M = ∅
      · rw [hM, empty_union, St.acc, ite_eq_left hM]
        exact (card_pick_le _).trans hy
      · rw [St.acc, ite_eq_right hM, union_empty]; exact h.M_card v
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]
        refine le_trans (card_le_card fun i hi => ?_) (h.B_card v)
        change i ∈ recvd _ _ _ at hi
        rw [hrecvd] at hi
        obtain ⟨hi, hj⟩ := hi
        obtain ⟨hMw, hpick⟩ := St.mem_acc.1 hj
        have := h.recv _ _ ((flip v i hi).2 hv) hMw (pick_subset _ hpick)
        rw [nn v i hi, rr v i hi] at this
        exact this.2
      · rw [hQ v hv hM]; exact h.M_card v
  · -- B_card
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
      show (if (c v).M = ∅ ∧ (c v).R = ∅ then batch Δ y (c v).S else (c v).B).card ≤ y
      split_ifs
      · rw [card_batch]; exact min_le_left _ _
      · exact h.B_card v
    · by_cases hM : (c v).M = ∅
      · rw [hP v hv hM]; exact h.B_card v
      · rw [hQ v hv hM]; exact h.B_card v
  · -- cons, backward direction
    have := fwd (G.nbr v i) (G.rport v i) (rl v i hi) hj
    rwa [nn v i hi, rr v i hi] at this
  · -- recv
    rw [act_succ] at hw
    have hw' : col w ≠ act a0 t := by rw [hw]; cases act a0 t <;> simp
    have hMw := emptyM w hM'w
    have hRw := h.passive w hw' hMw
    rw [hP w hw' hMw] at hj'
    change j ∈ (c w).R ∪ recvd _ _ _ at hj'
    rw [hRw, empty_union, hrecvd] at hj'
    obtain ⟨hj, hprop⟩ := hj'
    obtain ⟨hMv, hRv, hb⟩ := St.mem_prop.1 hprop
    rw [hA _ ((flip w j hj).2 hw')]
    refine ⟨?_, ?_⟩
    · show (c (G.nbr w j)).M ∪ (c (G.nbr w j)).acc = ∅
      exact St.union_acc_eq_empty.2 ⟨hMv, hRv⟩
    · show _ ∈ if _ then _ else _
      rw [ite_eq_left ⟨hMv, hRv⟩]; exact hb
  · -- passive
    rw [act_succ] at hw
    have hw' : col w = act a0 t := by
      revert hw; cases col w <;> cases act a0 t <;> simp
    rw [hA w hw'] at hM'w ⊢
    exact (St.union_acc_eq_empty.1 hM'w).2
  · -- sent
    by_cases hi : i ∈ (c v).S
    · rcases h.sent v i hi with hM | hR
      · exact Or.inl (neM _ hM)
      · exact Or.inr (monoR _ hR)
    · by_cases hv : col v = act a0 t
      · rw [hA v hv] at hi'
        have hp := (mem_union.1 hi').resolve_left hi
        have hiΔ := (mem_batch (St.mem_prop.1 hp).2.2).1
        have hw : col (G.nbr v i) ≠ act a0 t := by
          rw [Ne, flip v i hiΔ]; exact not_not.2 hv
        by_cases hMw : (c (G.nbr v i)).M = ∅
        · right
          rw [hP _ hw hMw]
          refine mem_union_right _ ?_
          rw [hrecvd, nn v i hiΔ, rr v i hiΔ]
          exact ⟨rl v i hiΔ, hp⟩
        · exact Or.inl (neM _ hMw)
      · by_cases hMv : (c v).M = ∅
        · rw [hP v hv hMv] at hi'; exact absurd hi' hi
        · rw [hQ v hv hMv] at hi'; exact absurd hi' hi
  · -- count
    have hMv := emptyM v hM'
    have hRv : (c v).R = ∅ := subset_empty.1 (hR' ▸ monoR v)
    have hc := h.count v hMv hRv
    simp only [nact]
    by_cases hv : col v = act a0 t
    · rw [hA v hv]
      show _ ≤ ((c v).S ∪ (c v).prop Δ y).card
      have hMR : (c v).M = ∅ ∧ (c v).R = ∅ := ⟨hMv, hRv⟩
      rw [St.prop, ite_eq_left hMR, card_union_batch (h.S_sub v), ite_eq_left hv.symm, mul_add,
        mul_one]
      omega
    · rw [ite_eq_right (Ne.symm hv), Nat.add_zero, hP v hv hMv]
      exact hc

variable (G Δ y a0 col) in
/-- The configuration after `t` rounds, started from the initial states. -/
def cfg (t : ℕ) : V → St :=
  localRun G (step Δ y a0) (fun v => St.init (col v)) t

variable (G Δ y a0 col) in
theorem inv_cfg (hy : 1 ≤ y) (hdeg : ∀ v, G.deg v = Δ)
    (hcol : ∀ v i, i < Δ → col (G.nbr v i) = !col v) (t : ℕ) :
    Inv G Δ y a0 col t (cfg G Δ y a0 col t) := by
  induction t with
  | zero => exact inv_zero
  | succ t ih => exact ih.next hy hdeg hcol

end Invariants

end UpperBound

end TightBipartiteMatching
