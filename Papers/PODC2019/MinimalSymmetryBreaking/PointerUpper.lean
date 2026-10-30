import Papers.PODC2019.MinimalSymmetryBreaking.PointerProblem
import Papers.PODC2026.SinklessOrientation.Lemma22

/-!
# The `O(log n)` upper bound for `P*` (Lemma 17) and a repaired Lemma 3

Section 8.1 (Lemma 3) and Section 8.2 (Lemma 17) of *Hardness of Minimal Symmetry Breaking in
Distributed Computing* (Balliu, Hirvonen, Olivetti, Suomela, PODC 2019).

The paper's algorithm for Lemma 3 ("each node points to its closest irregularity") is not correct
as written (see the paper folder's notes); we use a repaired algorithm with a radius parameter `K`:

* `DL v` = distance to the nearest node of degree `< Δ`, `DZ v` = distance to the set `Z` of nodes
  on a *candidate cycle list* (`IsCand`: a duplicate-free list of `≥ 3` degree-`Δ` nodes, cyclically
  consecutive entries adjacent, pairwise distance `≤ 2K`), both truncated at `K + 1` (`tdist`).
* **Low mode** (`DL v ≤ DZ v`): nodes of degree `< Δ` output `(deg v, ⊥)`; others point to a
  neighbour with `DL` one smaller, and `d v` is the degree of the end of the pointer chain.
* **Cycle mode** (`DZ v < DL v`): `d v = 0`; nodes outside `Z` point to a neighbour with `DZ` one
  smaller, nodes of `Z` point to their successor in the least (for a fixed well-order on lists)
  candidate list through them; this choice is consistent, so pointers never backtrack.

## Main results

* `pstarAlg_happy`: every *covered* node (`DL v ≤ K` or `DZ v ≤ K`) is `P*`-happy.
* `pstarAlg_gLocal`: the labelling is computed in `6K + 3` rounds.
* `lemma3_repaired`: **Lemma 3** (repaired algorithm): every node with a node of degree `< Δ` or a
  cycle of degree-`Δ` nodes within distance `r` is `P*`-happy, in `6r + 3` rounds.
* `lemma17`: **Lemma 17**: `P*` is solvable in `6⌈log_{Δ-1} n⌉ + 3 = O(log n)` rounds.
* `theorem4`: **Theorem 4** (upper and lower bound together).
-/

namespace Podc.MinimalSymmetryBreaking

open SimpleGraph Cslib.Local

variable {V : Type*}

/-! ### Graph-only locality -/

-- CSLib candidate: `GLocal`, `Near`, `tdist` and `tdist_gLocal` (truncated distances to a locally
-- defined set are local) belong next to `Cslib.Local.IsLocal`.
section GLocal

/-- `q G v` only depends on the edges at nodes of distance `< R` from `v` (a quantity computed in
`R` rounds of the LOCAL model without inputs). -/
def GLocal {β : Sort*} (R : ℕ) (q : SimpleGraph V → V → β) : Prop :=
  ∀ G G' v, GAgree G G' v R → q G v = q G' v

lemma GLocal.at {β : Sort*} {R ρ a : ℕ} {q : SimpleGraph V → V → β} (hq : GLocal ρ q)
    {G G' : SimpleGraph V} {v u : V} (hA : GAgree G G' v R) (hu : G.edist v u ≤ a)
    (h : a + ρ ≤ R) : q G u = q G' u :=
  hq _ _ _ (hA.mono hu h)

lemma GLocal.self {β : Sort*} {R ρ : ℕ} {q : SimpleGraph V → V → β} (hq : GLocal ρ q)
    {G G' : SimpleGraph V} {v : V} (hA : GAgree G G' v R) (h : ρ ≤ R) : q G v = q G' v :=
  hq _ _ _ (hA.mono_radius h)

lemma deg_gLocal : GLocal 1 (deg (V := V)) := fun G G' v hA => by
  unfold deg; rw [hA.neighborSet_eq one_pos]

end GLocal

/-! ### Truncated distances to a set -/

section TDist

/-- Some node satisfying `P` is within distance `k` of `v`. -/
def Near (P : SimpleGraph V → V → Prop) (G : SimpleGraph V) (v : V) (k : ℕ) : Prop :=
  ∃ u, P G u ∧ G.edist v u ≤ k

/-- The distance from `v` to the set `P`, truncated at `K + 1`. -/
noncomputable def tdist (P : SimpleGraph V → V → Prop) (K : ℕ) (G : SimpleGraph V) (v : V) : ℕ :=
  sInf {k | k = K + 1 ∨ Near P G v k}

variable {P : SimpleGraph V → V → Prop} {K : ℕ} {G : SimpleGraph V} {u v : V} {k : ℕ}

lemma tdist_le : tdist P K G v ≤ K + 1 := Nat.sInf_le (Or.inl rfl)

lemma tdist_mem : tdist P K G v = K + 1 ∨ Near P G v (tdist P K G v) :=
  Nat.sInf_mem (s := {k | k = K + 1 ∨ Near P G v k}) ⟨K + 1, Or.inl rfl⟩

lemma near_mono {k' : ℕ} (h : Near P G v k) (hk : k ≤ k') : Near P G v k' :=
  let ⟨u, hu, hd⟩ := h; ⟨u, hu, hd.trans (by exact_mod_cast hk)⟩

lemma tdist_le_of_near (h : Near P G v k) : tdist P K G v ≤ k := Nat.sInf_le (Or.inr h)

lemma near_of_tdist_le (hk : k ≤ K) (h : tdist P K G v ≤ k) : Near P G v k := by
  rcases tdist_mem (P := P) (K := K) (G := G) (v := v) with h' | h'
  · omega
  · exact near_mono h' h

lemma tdist_eq_zero : tdist P K G v = 0 ↔ P G v := by
  constructor
  · intro h
    obtain ⟨u, hu, hd⟩ := near_of_tdist_le (P := P) (Nat.zero_le K) h.le
    have : G.edist v u = 0 := by simpa using hd
    rw [edist_eq_zero_iff] at this
    rwa [this]
  · intro h; exact Nat.le_zero.1 (tdist_le_of_near ⟨v, h, by simp⟩)

/-- Truncated distances are `1`-Lipschitz along edges. -/
lemma tdist_le_succ_of_adj (h : G.Adj u v) : tdist P K G v ≤ tdist P K G u + 1 := by
  rcases tdist_mem (P := P) (K := K) (G := G) (v := u) with h' | ⟨w, hw, hd⟩
  · have := tdist_le (P := P) (K := K) (G := G) (v := v); omega
  · apply tdist_le_of_near
    refine ⟨w, hw, ?_⟩
    calc G.edist v w ≤ G.edist u w + 1 := by
          rw [edist_comm, edist_comm (u := u)]; exact edist_le_add_one_of_adj h
      _ ≤ (tdist P K G u : ℕ∞) + 1 := by gcongr
      _ = ((tdist P K G u + 1 : ℕ) : ℕ∞) := by push_cast; rfl

private lemma enat_eq_of_le_not_le {e : ℕ∞} {t : ℕ} (h1 : e ≤ t) (h2 : ¬ e ≤ ((t - 1 : ℕ) : ℕ∞))
    (ht : 0 < t) : e = ((t - 1 + 1 : ℕ) : ℕ∞) := by
  have hne : e ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hne
  have h1' : m ≤ t := by exact_mod_cast h1
  have h2' : ¬ m ≤ t - 1 := by exact_mod_cast h2
  congr 1; omega

/-- A node at positive truncated distance `≤ K` has a neighbour one step closer. -/
lemma exists_adj_tdist (h0 : 0 < tdist P K G v) (hK : tdist P K G v ≤ K) :
    ∃ u, G.Adj v u ∧ tdist P K G u + 1 = tdist P K G v := by
  set t := tdist P K G v with ht
  obtain ⟨w, hw, hd⟩ := near_of_tdist_le (P := P) hK le_rfl
  have hge : ¬ G.edist v w ≤ ((t - 1 : ℕ) : ℕ∞) := fun h => by
    have := tdist_le_of_near (K := K) ⟨w, hw, h⟩; omega
  have heq : G.edist w v = ((t - 1 + 1 : ℕ) : ℕ∞) := by
    rw [edist_comm]; exact enat_eq_of_le_not_le hd hge h0
  obtain ⟨u, hu, hadj⟩ := exists_adj_of_edist_eq_succ heq
  refine ⟨u, hadj.symm, ?_⟩
  have h1 : tdist P K G u ≤ t - 1 := tdist_le_of_near ⟨w, hw, by rw [edist_comm, hu]⟩
  have h2 := tdist_le_succ_of_adj (P := P) (K := K) hadj
  omega

/-- If `P` is `ρ`-local, its distances truncated at `K + 1` are `R`-local for `K + ρ ≤ R`. -/
lemma near_of_gAgree {G G' : SimpleGraph V} {ρ R : ℕ} (hP : GLocal ρ P) (hA : GAgree G G' v R)
    (hk : k + ρ ≤ R) : Near P G v k → Near P G' v k := by
  rintro ⟨u, hu, hd⟩
  refine ⟨u, ?_, (hA.edist_le_iff (by omega)).2 hd⟩
  have := hP.at hA hd hk
  rw [← this]; exact hu

lemma tdist_gLocal {ρ R : ℕ} (hP : GLocal ρ P) (h : K + ρ ≤ R) : GLocal R (tdist P K) := by
  intro G G' v hA
  have key : ∀ {G G' : SimpleGraph V}, GAgree G G' v R → tdist P K G v ≤ tdist P K G' v := by
    intro G G' hA
    rcases tdist_mem (P := P) (K := K) (G := G') (v := v) with h' | h'
    · rw [h']; exact tdist_le
    · by_cases hk : tdist P K G' v ≤ K
      · exact tdist_le_of_near (near_of_gAgree hP hA.symm (by omega) h')
      · have := tdist_le (P := P) (K := K) (G := G) (v := v); omega
  exact le_antisymm (key hA) (key hA.symm)

end TDist

/-! ### Candidate cycle lists -/

section Cycles

variable [DecidableEq V]

/-- A *candidate cycle list*: a duplicate-free list of at least three nodes of degree `Δ`, such that
cyclically consecutive entries are adjacent and any two entries are at distance `≤ 2K`. This
condition is intrinsic, so all nodes compare the same candidates; it is checkable from distance
`4K + 1` of any entry. -/
structure IsCand (Δ K : ℕ) (G : SimpleGraph V) (l : List V) : Prop where
  nodup : l.Nodup
  three : 3 ≤ l.length
  deg_eq : ∀ a ∈ l, deg G a = Δ
  adj : ∀ i (h : i < l.length), G.Adj l[i] (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))
  close : ∀ a ∈ l, ∀ b ∈ l, G.edist a b ≤ ((2 * K : ℕ) : ℕ∞)

/-- The cyclic successor of `z` in `l`. -/
def cnext (l : List V) (z : V) : V := l.getD ((l.idxOf z + 1) % l.length) z

lemma cnext_eq {l : List V} {z : V} (hz : z ∈ l) :
    cnext l z = l[(l.idxOf z + 1) % l.length]'(Nat.mod_lt _ (List.length_pos_of_mem hz)) :=
  List.getD_eq_getElem _ _ _

lemma cnext_mem {l : List V} {z : V} (hz : z ∈ l) : cnext l z ∈ l := by
  rw [cnext_eq hz]; exact List.getElem_mem _

variable {Δ K : ℕ} {G : SimpleGraph V}

lemma IsCand.adj_cnext {l : List V} (hl : IsCand Δ K G l) {z : V} (hz : z ∈ l) :
    G.Adj z (cnext l z) := by
  have hi := List.idxOf_lt_length_of_mem hz
  have := hl.adj _ hi
  rw [List.getElem_idxOf hi] at this
  rw [cnext_eq hz]; exact this

lemma IsCand.cnext_cnext_ne {l : List V} (hl : IsCand Δ K G l) {z : V} (hz : z ∈ l) :
    cnext l (cnext l z) ≠ z := by
  have hlen := hl.three
  set n := l.length with hn
  have hi := List.idxOf_lt_length_of_mem hz
  set j := l.idxOf z with hj
  have hz' : l[j] = z := List.getElem_idxOf hi
  have h1 : cnext l z = l[(j + 1) % n]'(Nat.mod_lt _ (by omega)) := cnext_eq hz
  have hmem : cnext l z ∈ l := cnext_mem hz
  have h2 : cnext l (cnext l z) =
      l[(l.idxOf (cnext l z) + 1) % n]'(Nat.mod_lt _ (by omega)) := cnext_eq hmem
  have hidx : l.idxOf (cnext l z) = (j + 1) % n := by
    rw [h1]; exact hl.nodup.idxOf_getElem _ _
  rw [h2]
  conv_rhs => rw [← hz']
  intro he
  rw [hl.nodup.getElem_inj_iff, hidx] at he
  -- `((j + 1) % n + 1) % n = j` is impossible for `n ≥ 3`
  by_cases hj1 : j + 1 < n
  · rw [Nat.mod_eq_of_lt hj1] at he
    by_cases hj2 : j + 2 < n
    · rw [Nat.mod_eq_of_lt hj2] at he; omega
    · have : j + 1 + 1 = n := by omega
      rw [this, Nat.mod_self] at he; omega
  · have : j + 1 = n := by omega
    rw [this, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at he; omega

/-- The candidates through `z`. -/
def Cands (Δ K : ℕ) (G : SimpleGraph V) (z : V) : Set (List V) := {l | IsCand Δ K G l ∧ z ∈ l}

/-- `z ∈ Z`: `z` lies on a candidate cycle list. -/
def InZ (Δ K : ℕ) (G : SimpleGraph V) (z : V) : Prop := (Cands Δ K G z).Nonempty

-- CSLib candidate: a set-determined (hence locally consistent) choice of a cycle.
/-- The least element of a set of lists for a fixed well-order of `List V` (any fixed choice that
only depends on the set works). -/
noncomputable def wmin (S : Set (List V)) : List V :=
  open scoped Classical in
  if h : S.Nonempty then WellOrderingRel.isWellOrder.wf.min S h else []

omit [DecidableEq V] in
lemma wmin_mem {S : Set (List V)} (h : S.Nonempty) : wmin S ∈ S := by
  rw [wmin, dite_eq_left h]; exact WellFounded.min_mem _ _ _

omit [DecidableEq V] in
lemma wmin_def {S : Set (List V)} (h : S.Nonempty) :
    wmin S = WellOrderingRel.isWellOrder.wf.min S h := by
  rw [wmin, dite_eq_left h]

omit [DecidableEq V] in
lemma wmin_eq {S S' : Set (List V)} (h : S.Nonempty) (h' : S'.Nonempty) (ha : wmin S ∈ S')
    (hb : wmin S' ∈ S) : wmin S = wmin S' := by
  have := (WellOrderingRel.isWellOrder (α := List V))
  rcases trichotomous_of WellOrderingRel (wmin S) (wmin S') with hr | hr | hr
  · exfalso
    have := WellFounded.not_lt_min (WellOrderingRel.isWellOrder (α := List V)).wf S' ha
    rw [wmin_def h'] at hr
    exact this hr
  · exact hr
  · exfalso
    have := WellFounded.not_lt_min (WellOrderingRel.isWellOrder (α := List V)).wf S hb
    rw [wmin_def h] at hr
    exact this hr

/-- The chosen candidate list through `z`. -/
noncomputable def CZ (Δ K : ℕ) (G : SimpleGraph V) (z : V) : List V := wmin (Cands Δ K G z)

/-- The pointer of a node of `Z`: its successor in the chosen candidate list. -/
noncomputable def succZ (Δ K : ℕ) (G : SimpleGraph V) (z : V) : V := cnext (CZ Δ K G z) z

variable {z : V}

omit [DecidableEq V] in
lemma InZ.cz (h : InZ Δ K G z) : IsCand Δ K G (CZ Δ K G z) ∧ z ∈ CZ Δ K G z := wmin_mem h

lemma InZ.succZ_mem (h : InZ Δ K G z) : InZ Δ K G (succZ Δ K G z) :=
  ⟨CZ Δ K G z, h.cz.1, cnext_mem h.cz.2⟩

lemma InZ.adj_succZ (h : InZ Δ K G z) : G.Adj z (succZ Δ K G z) := h.cz.1.adj_cnext h.cz.2

omit [DecidableEq V] in
lemma InZ.deg (h : InZ Δ K G z) : deg G z = Δ := h.cz.1.deg_eq z h.cz.2

/-- Pointers on `Z` never backtrack: if `s(s(z)) = z`, then the chosen lists of `z` and `s(z)`
contain each other's node, so they coincide, and in a cycle of length `≥ 3`, `s ∘ s ≠ id`. -/
lemma InZ.succZ_succZ_ne (h : InZ Δ K G z) : succZ Δ K G (succZ Δ K G z) ≠ z := by
  intro heq
  have hs := h.succZ_mem
  have hC : CZ Δ K G z ∈ Cands Δ K G (succZ Δ K G z) := ⟨h.cz.1, cnext_mem h.cz.2⟩
  have hC' : CZ Δ K G (succZ Δ K G z) ∈ Cands Δ K G z := by
    refine ⟨hs.cz.1, ?_⟩
    have : succZ Δ K G (succZ Δ K G z) ∈ CZ Δ K G (succZ Δ K G z) := cnext_mem hs.cz.2
    rwa [heq] at this
  have he : CZ Δ K G z = CZ Δ K G (succZ Δ K G z) := wmin_eq h hs hC hC'
  apply h.cz.1.cnext_cnext_ne h.cz.2
  have : succZ Δ K G (succZ Δ K G z) = cnext (CZ Δ K G z) (cnext (CZ Δ K G z) z) := by
    rw [succZ, ← he]; rfl
  rw [← this, heq]

omit [DecidableEq V] in
/-- Candidates through `z` are determined by the radius-`(4K+1)` view of `z`. -/
lemma isCand_of_gAgree {G G' : SimpleGraph V} {R : ℕ} {l : List V} (hA : GAgree G G' z R)
    (hR : 4 * K + 1 ≤ R) (hl : IsCand Δ K G l) (hz : z ∈ l) : IsCand Δ K G' l := by
  have hd : ∀ a ∈ l, G.edist z a ≤ ((2 * K : ℕ) : ℕ∞) := fun a ha => hl.close z hz a ha
  have h1 : ∀ a ∈ l, GAgree G G' a 1 := fun a ha => hA.mono (hd a ha) (by omega)
  have h2 : ∀ a ∈ l, GAgree G G' a (2 * K) := fun a ha => hA.mono (hd a ha) (by omega)
  refine ⟨hl.nodup, hl.three, fun a ha => ?_, fun i hi => ?_, fun a ha b hb => ?_⟩
  · rw [← deg_gLocal G G' a (h1 a ha)]; exact hl.deg_eq a ha
  · exact ((h1 _ (List.getElem_mem hi)).adj_iff one_pos _).1 (hl.adj i hi)
  · exact ((h2 a ha).edist_le_iff le_rfl).2 (hl.close a ha b hb)

omit [DecidableEq V] in
lemma cands_gLocal (hR : 4 * K + 1 ≤ R) : GLocal R (Cands (V := V) Δ K) := by
  intro G G' z hA
  ext l
  exact ⟨fun h => ⟨isCand_of_gAgree hA hR h.1 h.2, h.2⟩,
    fun h => ⟨isCand_of_gAgree hA.symm hR h.1 h.2, h.2⟩⟩

omit [DecidableEq V] in
lemma inZ_gLocal : GLocal (4 * K + 1) (InZ (V := V) Δ K) := fun G G' z hA => by
  unfold InZ; rw [cands_gLocal le_rfl G G' z hA]

lemma succZ_gLocal : GLocal (4 * K + 1) (succZ (V := V) Δ K) := fun G G' z hA => by
  unfold succZ CZ; rw [cands_gLocal le_rfl G G' z hA]

omit [DecidableEq V] in
/-- A cycle in the radius-`K` ball of `v` all of whose nodes have degree `Δ` gives a candidate. -/
lemma isCand_of_cycle {v x : V} (c : G.Walk x x) (hc : c.IsCycle)
    (hball : ∀ y ∈ c.support, G.edist v y ≤ K) (hdeg : ∀ y ∈ c.support, deg G y = Δ) :
    IsCand Δ K G c.support.tail := by
  have hlen : c.support.tail.length = c.length := by simp
  have h3 := hc.three_le_length
  have hget : ∀ i (h : i < c.support.tail.length), c.support.tail[i] = c.getVert (i + 1) := by
    intro i h
    rw [Walk.getVert_eq_support_getElem _ (by omega), List.getElem_tail]
  refine ⟨hc.support_nodup, by omega, fun a ha => hdeg a (List.mem_of_mem_tail ha),
    fun i hi => ?_, fun a ha b hb => ?_⟩
  · rw [hget, hget]
    by_cases hi1 : i + 1 < c.support.tail.length
    · rw [Nat.mod_eq_of_lt hi1]
      exact c.adj_getVert_succ (by omega)
    · have : i + 1 = c.support.tail.length := by omega
      rw [this, Nat.mod_self, hlen, Walk.getVert_length]
      have := c.adj_getVert_succ (i := 0) (by omega)
      simpa using this
  · have ha' := hball a (List.mem_of_mem_tail ha)
    have hb' := hball b (List.mem_of_mem_tail hb)
    calc G.edist a b ≤ G.edist a v + G.edist v b := SimpleGraph.edist_triangle
      _ ≤ (K : ℕ∞) + K := by rw [SimpleGraph.edist_comm]; gcongr
      _ = ((2 * K : ℕ) : ℕ∞) := by push_cast; ring

end Cycles

/-! ### The algorithm -/

section Algorithm

variable [DecidableEq V] (Δ K : ℕ)

/-- Truncated distance to the nearest node of degree `< Δ`. -/
noncomputable def DL (G : SimpleGraph V) (v : V) : ℕ := tdist (fun G u => deg G u < Δ) K G v

/-- Truncated distance to `Z`. -/
noncomputable def DZ (G : SimpleGraph V) (v : V) : ℕ := tdist (InZ Δ K) K G v

/-- Some element of `S`, if any (any choice that only depends on `S`). -/
noncomputable def pick (S : Set V) : Option V :=
  open scoped Classical in if h : S.Nonempty then some h.some else none

/-- The pointer of `v`. -/
noncomputable def ptr (G : SimpleGraph V) (v : V) : Option V :=
  if DL Δ K G v ≤ DZ Δ K G v then
    (if DL Δ K G v = 0 then none
      else pick {u | G.Adj v u ∧ DL Δ K G u + 1 = DL Δ K G v})
  else
    (if DZ Δ K G v = 0 then some (succZ Δ K G v)
      else pick {u | G.Adj v u ∧ DZ Δ K G u + 1 = DZ Δ K G v})

/-- Follow the pointer (stay if there is none). -/
noncomputable def step (G : SimpleGraph V) (u : V) : V := (ptr Δ K G u).getD u

/-- The end of the pointer chain of a low-mode node (`DL v` steps). -/
noncomputable def endpt (G : SimpleGraph V) (v : V) : V := (step Δ K G)^[DL Δ K G v] v

/-- The number `d v`. -/
noncomputable def dval (G : SimpleGraph V) (v : V) : ℕ :=
  if DL Δ K G v ≤ DZ Δ K G v then deg G (endpt Δ K G v) else 0

/-- The output `(d v, p v)` of the algorithm with radius parameter `K`. -/
noncomputable def pstarAlg (G : SimpleGraph V) (v : V) : ℕ × Option V :=
  (dval Δ K G v, ptr Δ K G v)

variable {Δ K}

omit [DecidableEq V] in
lemma pick_mem {S : Set V} {u : V} (h : pick S = some u) : u ∈ S := by
  unfold pick at h
  split_ifs at h with hS
  · cases h; exact hS.some_mem

omit [DecidableEq V] in
lemma pick_some {S : Set V} (h : S.Nonempty) : ∃ u, pick S = some u :=
  ⟨h.some, by unfold pick; rw [dite_eq_left h]⟩

variable {G : SimpleGraph V} {u v : V}

omit [DecidableEq V] in
lemma DL_eq_zero : DL Δ K G v = 0 ↔ deg G v < Δ := tdist_eq_zero

omit [DecidableEq V] in
lemma DZ_eq_zero : DZ Δ K G v = 0 ↔ InZ Δ K G v := tdist_eq_zero

omit [DecidableEq V] in
lemma DL_lip (h : G.Adj u v) : DL Δ K G v ≤ DL Δ K G u + 1 := tdist_le_succ_of_adj h

omit [DecidableEq V] in
lemma DZ_lip (h : G.Adj u v) : DZ Δ K G v ≤ DZ Δ K G u + 1 := tdist_le_succ_of_adj h

lemma ptr_adj (h : ptr Δ K G v = some u) : G.Adj v u := by
  unfold ptr at h
  split_ifs at h with h1 h2 h3
  · exact (pick_mem h).1
  · cases h; exact (DZ_eq_zero.1 h3).adj_succZ
  · exact (pick_mem h).1

/-- `v` is covered: an irregularity (in the sense of the algorithm) is within distance `K`. -/
def Covered (Δ K : ℕ) (G : SimpleGraph V) (v : V) : Prop := DL Δ K G v ≤ K ∨ DZ Δ K G v ≤ K

/-- Pointers of low-mode nodes. -/
lemma ptr_low (hl : DL Δ K G v ≤ DZ Δ K G v) (hc : Covered Δ K G v) (h0 : DL Δ K G v ≠ 0) :
    ∃ u, ptr Δ K G v = some u ∧ G.Adj v u ∧ DL Δ K G u + 1 = DL Δ K G v := by
  have hK : DL Δ K G v ≤ K := by rcases hc with hc | hc <;> omega
  obtain ⟨u, hu1, hu2⟩ := exists_adj_tdist (Nat.pos_of_ne_zero h0) hK
  obtain ⟨w, hw⟩ := pick_some (S := {u | G.Adj v u ∧ DL Δ K G u + 1 = DL Δ K G v}) ⟨u, hu1, hu2⟩
  refine ⟨w, ?_, (pick_mem hw).1, (pick_mem hw).2⟩
  unfold ptr; rw [ite_eq_left hl, ite_eq_right h0]; exact hw

/-- Pointers of cycle-mode nodes. -/
lemma ptr_cyc (hl : ¬ DL Δ K G v ≤ DZ Δ K G v) :
    ∃ u, ptr Δ K G v = some u ∧ G.Adj v u ∧
      (DZ Δ K G u + 1 = DZ Δ K G v ∨ (InZ Δ K G v ∧ u = succZ Δ K G v)) := by
  have hK : DZ Δ K G v ≤ K := by
    have := tdist_le (P := fun G u => deg G u < Δ) (K := K) (G := G) (v := v)
    unfold DL at hl; omega
  by_cases h0 : DZ Δ K G v = 0
  · have hz := DZ_eq_zero.1 h0
    refine ⟨succZ Δ K G v, ?_, hz.adj_succZ, Or.inr ⟨hz, rfl⟩⟩
    unfold ptr; rw [ite_eq_right hl, ite_eq_left h0]
  · obtain ⟨u, hu1, hu2⟩ := exists_adj_tdist (Nat.pos_of_ne_zero h0) hK
    obtain ⟨w, hw⟩ :=
      pick_some (S := {u | G.Adj v u ∧ DZ Δ K G u + 1 = DZ Δ K G v}) ⟨u, hu1, hu2⟩
    refine ⟨w, ?_, (pick_mem hw).1, Or.inl (pick_mem hw).2⟩
    unfold ptr; rw [ite_eq_right hl, ite_eq_right h0]; exact hw

lemma ptr_low_zero (h0 : DL Δ K G v = 0) : ptr Δ K G v = none := by
  unfold ptr; rw [ite_eq_left (by omega), ite_eq_left h0]

/-- Low mode is closed under pointers, and pointer targets are covered. -/
lemma low_of_ptr (hl : DL Δ K G v ≤ DZ Δ K G v) (hc : Covered Δ K G v)
    (h : ptr Δ K G v = some u) :
    DL Δ K G u ≤ DZ Δ K G u ∧ Covered Δ K G u ∧ DL Δ K G u + 1 = DL Δ K G v := by
  have h0 : DL Δ K G v ≠ 0 := fun h0 => by rw [ptr_low_zero h0] at h; cases h
  obtain ⟨w, hw, hadj, hd⟩ := ptr_low hl hc h0
  rw [h] at hw; cases hw
  have := DZ_lip (K := K) (Δ := Δ) hadj.symm
  have hK : DL Δ K G v ≤ K := by rcases hc with hc | hc <;> omega
  exact ⟨by omega, Or.inl (by omega), hd⟩

/-- Cycle mode is closed under pointers. -/
lemma cyc_of_ptr (hl : ¬ DL Δ K G v ≤ DZ Δ K G v) (h : ptr Δ K G v = some u) :
    ¬ DL Δ K G u ≤ DZ Δ K G u := by
  obtain ⟨w, hw, hadj, hd⟩ := ptr_cyc hl
  rw [h] at hw; cases hw
  rcases hd with hd | ⟨hz, rfl⟩
  · have := DL_lip (K := K) (Δ := Δ) hadj.symm
    omega
  · have hs := hz.succZ_mem
    rw [(DZ_eq_zero (K := K)).2 hs]
    intro h0
    have := DL_eq_zero.1 (Nat.le_zero.1 h0)
    rw [hs.deg] at this; omega

omit [DecidableEq V] in
lemma covered_of_cyc (hl : ¬ DL Δ K G v ≤ DZ Δ K G v) : Covered Δ K G v := by
  have := tdist_le (P := fun G u => deg G u < Δ) (K := K) (G := G) (v := v)
  unfold DL at hl; right; omega

/-- The chain of a covered low-mode node ends at a node of degree `< Δ`, and the end does not
change along pointers. -/
lemma endpt_spec : ∀ n (v : V), DL Δ K G v = n → DL Δ K G v ≤ DZ Δ K G v → Covered Δ K G v →
    (∀ u, ptr Δ K G v = some u → endpt Δ K G v = endpt Δ K G u) ∧ deg G (endpt Δ K G v) < Δ := by
  intro n
  induction n with
  | zero =>
    intro v hn _ _
    refine ⟨fun u h => (by rw [ptr_low_zero hn] at h; cases h), ?_⟩
    rw [endpt, hn]; exact DL_eq_zero.1 hn
  | succ n ih =>
    intro v hn hl hc
    obtain ⟨u, hu, -, hd⟩ := ptr_low hl hc (by omega)
    obtain ⟨hlu, hcu, -⟩ := low_of_ptr hl hc hu
    have hstep : step Δ K G v = u := by rw [step, hu]; rfl
    have he : endpt Δ K G v = endpt Δ K G u := by
      rw [endpt, endpt, hn, Function.iterate_succ_apply, hstep, show DL Δ K G u = n by omega]
    refine ⟨fun u' h => by rw [hu] at h; cases h; exact he, ?_⟩
    rw [he]; exact (ih u (by omega) hlu hcu).2

/-- **Correctness**: every covered node is `P*`-happy. -/
theorem pstarAlg_happy (hΔ : 0 < Δ) (hc : Covered Δ K G v) :
    PHappy Δ G (dval Δ K G) (ptr Δ K G) v := by
  by_cases hl : DL Δ K G v ≤ DZ Δ K G v
  · have hdv : dval Δ K G v = deg G (endpt Δ K G v) := by rw [dval, ite_eq_left hl]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdv]; exact (endpt_spec _ v rfl hl hc).2
    · intro hd
      have h0 : DL Δ K G v ≠ 0 := fun h0 => by have := DL_eq_zero.1 h0; omega
      obtain ⟨u, hu, hadj, -⟩ := ptr_low hl hc h0
      exact ⟨u, hu, hadj⟩
    · intro hd
      have h0 := (DL_eq_zero (K := K)).2 hd
      refine ⟨ptr_low_zero h0, ?_⟩
      rw [hdv, endpt, h0]; rfl
    · intro u hu
      obtain ⟨hlu, -, -⟩ := low_of_ptr hl hc hu
      rw [dval, ite_eq_left hlu, hdv, (endpt_spec _ v rfl hl hc).1 u hu]
    · intro u hu hu'
      obtain ⟨hlu, hcu, hd⟩ := low_of_ptr hl hc hu
      obtain ⟨-, -, hd'⟩ := low_of_ptr hlu hcu hu'
      omega
    · intro u hu
      by_cases hpu : ptr Δ K G u = none
      · right
        obtain ⟨hlu, hcu, -⟩ := low_of_ptr hl hc hu
        have h0 : DL Δ K G u = 0 := by
          by_contra h0
          obtain ⟨w, hw, -⟩ := ptr_low hlu hcu h0
          rw [hpu] at hw; cases hw
        rw [hdv, (endpt_spec _ v rfl hl hc).1 u hu, endpt, h0]; rfl
      · exact Or.inl hpu
  · have hdv : dval Δ K G v = 0 := by rw [dval, ite_eq_right hl]
    have hdeg : ¬ deg G v < Δ := fun hd => hl (by rw [(DL_eq_zero (K := K)).2 hd]; omega)
    refine ⟨by rw [hdv]; exact hΔ, ?_, fun hd => absurd hd hdeg, ?_, ?_, ?_⟩
    · intro _
      obtain ⟨u, hu, hadj, -⟩ := ptr_cyc hl
      exact ⟨u, hu, hadj⟩
    · intro u hu
      have hlu := cyc_of_ptr hl hu
      rw [dval, ite_eq_right hlu, hdv]
    · intro u hu hu'
      have hlu := cyc_of_ptr hl hu
      obtain ⟨w, hw, -, hd⟩ := ptr_cyc hl
      rw [hu] at hw; cases hw
      obtain ⟨w', hw', -, hd'⟩ := ptr_cyc hlu
      rw [hu'] at hw'; cases hw'
      rcases hd with hd | ⟨hz, rfl⟩ <;> rcases hd' with hd' | ⟨hz', he⟩
      · omega
      · have h0 := (DZ_eq_zero (K := K)).2 hz'.succZ_mem
        rw [← he] at h0; omega
      · rw [(DZ_eq_zero (K := K)).2 hz.succZ_mem] at hd'; omega
      · exact hz.succZ_succZ_ne he.symm
    · intro u hu
      left
      obtain ⟨w, hw, -⟩ := ptr_cyc (cyc_of_ptr hl hu)
      rw [hw]; simp

/-! ### Locality -/

omit [DecidableEq V] in
lemma DL_gLocal : GLocal (K + 1) (DL (V := V) Δ K) :=
  tdist_gLocal (ρ := 1) (fun G G' v hA => by simp only [deg_gLocal G G' v hA]) le_rfl

omit [DecidableEq V] in
lemma DZ_gLocal : GLocal (5 * K + 1) (DZ (V := V) Δ K) :=
  tdist_gLocal inZ_gLocal (by omega)

lemma ptr_gLocal : GLocal (5 * K + 2) (ptr (V := V) Δ K) := by
  intro G G' v hA
  have h1 : DL Δ K G v = DL Δ K G' v := DL_gLocal.self hA (by omega)
  have h2 : DZ Δ K G v = DZ Δ K G' v := DZ_gLocal.self hA (by omega)
  have h3 : succZ Δ K G v = succZ Δ K G' v := succZ_gLocal.self hA (by omega)
  have hset : ∀ (q : SimpleGraph V → V → ℕ) (ρ : ℕ), GLocal ρ q → ρ + 1 ≤ 5 * K + 2 →
      {u | G.Adj v u ∧ q G u + 1 = q G v} = {u | G'.Adj v u ∧ q G' u + 1 = q G' v} := by
    intro q ρ hq hρ
    have hv : q G v = q G' v := hq.self hA (by omega)
    ext u
    simp only [Set.mem_ofPred_eq]
    have hadj := hA.adj_iff (by omega) u
    constructor
    · rintro ⟨ha, he⟩
      have : G.edist v u ≤ 1 := by rw [edist_eq_one_iff_adj.2 ha]
      rw [← hq.at hA this (by omega), ← hv]; exact ⟨hadj.1 ha, he⟩
    · rintro ⟨ha, he⟩
      have : G.edist v u ≤ 1 := by rw [edist_eq_one_iff_adj.2 (hadj.2 ha)]
      rw [hq.at hA this (by omega), hv]; exact ⟨hadj.2 ha, he⟩
  unfold ptr
  rw [hset _ _ DL_gLocal (by omega), hset _ _ DZ_gLocal (by omega), h1, h2, h3]

lemma step_gLocal : GLocal (5 * K + 2) (step (V := V) Δ K) := fun G G' v hA => by
  unfold step; rw [ptr_gLocal G G' v hA]

lemma step_eq_or_adj (G : SimpleGraph V) (u : V) :
    step Δ K G u = u ∨ G.Adj u (step Δ K G u) := by
  unfold step
  rcases h : ptr Δ K G u with _ | w
  · left; rfl
  · right; exact ptr_adj h

lemma iterate_step {G G' : SimpleGraph V} {R : ℕ} (hA : GAgree G G' v R) :
    ∀ k, k + (5 * K + 2) ≤ R →
      (step Δ K G)^[k] v = (step Δ K G')^[k] v ∧ G.edist v ((step Δ K G)^[k] v) ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨e, hd⟩ := ih (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← e]
    refine ⟨step_gLocal.at hA hd (by omega), ?_⟩
    rcases step_eq_or_adj (Δ := Δ) (K := K) G ((step Δ K G)^[k] v) with h | h
    · rw [h]; exact hd.trans (by exact_mod_cast Nat.le_succ k)
    · calc G.edist v _ ≤ G.edist v ((step Δ K G)^[k] v) + 1 := edist_le_add_one_of_adj h
        _ ≤ (k : ℕ∞) + 1 := by gcongr
        _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; rfl

lemma dval_gLocal : GLocal (6 * K + 3) (dval (V := V) Δ K) := by
  intro G G' v hA
  have h1 : DL Δ K G v = DL Δ K G' v := DL_gLocal.self hA (by omega)
  have h2 : DZ Δ K G v = DZ Δ K G' v := DZ_gLocal.self hA (by omega)
  have hle : DL Δ K G v ≤ K + 1 := tdist_le
  obtain ⟨e, hd⟩ := iterate_step (Δ := Δ) (K := K) hA (DL Δ K G v) (by omega)
  have he : endpt Δ K G v = endpt Δ K G' v := by rw [endpt, endpt, ← h1, e]
  have hdeg : deg G (endpt Δ K G v) = deg G' (endpt Δ K G v) :=
    deg_gLocal.at hA (a := K + 1) (hd.trans (by exact_mod_cast hle)) (by omega)
  unfold dval
  rw [h1, h2, hdeg, he]

/-- **Locality**: the algorithm runs in `6K + 3` rounds. -/
theorem pstarAlg_gLocal : GLocal (6 * K + 3) (pstarAlg (V := V) Δ K) := fun G G' v hA => by
  unfold pstarAlg
  rw [dval_gLocal G G' v hA, ptr_gLocal.self hA (by omega)]

theorem pstarAlg_isLocal {α : Type*} :
    IsLocal (6 * K + 3) (fun (G : SimpleGraph V) (_ : V → α) v => pstarAlg Δ K G v) :=
  fun G _ G' _ v hv => pstarAlg_gLocal G G' v hv.1

/-! ### Lemma 3 and Lemma 17 -/

omit [DecidableEq V] in
/-- A node with a degree-`< Δ` node or a cycle of degree-`Δ` nodes within distance `K` is
covered. -/
lemma covered_of_irregular
    (h : (∃ u, G.edist v u ≤ K ∧ deg G u < Δ) ∨
      (∃ (x : V) (c : G.Walk x x), c.IsCycle ∧
        ∀ y ∈ c.support, G.edist v y ≤ K ∧ deg G y = Δ)) :
    Covered Δ K G v := by
  rcases h with ⟨u, hu, hd⟩ | ⟨x, c, hc, hy⟩
  · exact Or.inl (tdist_le_of_near ⟨u, hd, hu⟩)
  · right
    have hcand := isCand_of_cycle (K := K) (Δ := Δ) (v := v) c hc (fun y hy' => (hy y hy').1)
      (fun y hy' => (hy y hy').2)
    have hx : x ∈ c.support.tail := Walk.end_mem_tail_support hc.not_nil
    exact tdist_le_of_near ⟨x, ⟨_, hcand, hx⟩, (hy x (List.mem_of_mem_tail hx)).1⟩

/-- **Lemma 3** of [BHOS19], for the repaired algorithm `pstarAlg Δ r`: in `6r + 3` rounds, every
node that has an irregularity within distance `r` — a node of degree `< Δ`, or a cycle of nodes of
degree `Δ` all of whose nodes are within distance `r` (this is implied by the paper's
`dist(v, C) ≤ r`) — is `P*`-happy. -/
theorem lemma3_repaired (hΔ : 0 < Δ) (r : ℕ) :
    IsLocal (6 * r + 3) (fun (G : SimpleGraph V) (_ : V → Unit) v => pstarAlg Δ r G v) ∧
    ∀ (G : SimpleGraph V) (v : V),
      ((∃ u, G.edist v u ≤ r ∧ deg G u < Δ) ∨
        (∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ ∀ y ∈ c.support, G.edist v y ≤ r ∧ deg G y = Δ)) →
      PHappy Δ G (fun v => (pstarAlg Δ r G v).1) (fun v => (pstarAlg Δ r G v).2) v :=
  ⟨pstarAlg_isLocal, fun _ _ h => pstarAlg_happy hΔ (covered_of_irregular h)⟩

omit [DecidableEq V] in
/-- In an `n`-node graph of maximum degree `Δ ≥ 3` with `n ≤ (Δ-1)^K`, every node is covered
(the radius-`K` ball contains a node of degree `< Δ` or a cycle; Lemma 2.2 of Nolin, PODC'26). -/
lemma covered_all [Fintype V] (hΔ : 3 ≤ Δ) (hdeg : ∀ v, deg G v ≤ Δ)
    (hK : Fintype.card V ≤ (Δ - 1) ^ K) (v : V) : Covered Δ K G v := by
  rcases SinklessOrientation.lemma_2_2_of_card_le G hΔ v hK with ⟨u, hu, hd⟩ | ⟨x, c, hc, hs⟩
  · exact covered_of_irregular (Or.inl ⟨u, SinklessOrientation.mem_cball.1 hu, hd⟩)
  · by_cases hlow : ∃ u, G.edist v u ≤ K ∧ deg G u < Δ
    · exact covered_of_irregular (Or.inl hlow)
    · push Not at hlow
      refine covered_of_irregular (Or.inr ⟨x, c, hc, fun y hy => ?_⟩)
      have hy' := SinklessOrientation.mem_cball.1 (hs y hy)
      exact ⟨hy', le_antisymm (hdeg y) (hlow y hy')⟩

/-- **Lemma 17** of [BHOS19]: `P*` can be solved deterministically in `O(log n)` rounds; precisely,
for `Δ ≥ 3`, in `6⌈log_{Δ-1} n⌉ + 3` rounds on every graph of maximum degree `≤ Δ` on `n` nodes
(the identifier set `V`). -/
theorem lemma17 [Fintype V] (hΔ : 3 ≤ Δ) :
    ∃ f : SimpleGraph V → (V → Unit) → V → ℕ × Option V,
      IsLocal (6 * Nat.clog (Δ - 1) (Fintype.card V) + 3) f ∧
      ∀ (G : SimpleGraph V) (x : V → Unit), (∀ v, deg G v ≤ Δ) → Solves Δ G (f G x) := by
  refine ⟨fun G _ v => pstarAlg Δ (Nat.clog (Δ - 1) (Fintype.card V)) G v, pstarAlg_isLocal,
    fun G _ hdeg v => pstarAlg_happy (by omega) (covered_all hΔ hdeg ?_ v)⟩
  exact Nat.le_pow_clog (by omega) _

end Algorithm

/-- **Theorem 4** of [BHOS19]: the complexity of `P*` is `Θ(log_Δ n)` (for any fixed `Δ ≥ 3`).
Upper bound (Lemma 17): on every identifier set `V` of size `n`, `P*` is solved deterministically in
`6⌈log_{Δ-1} n⌉ + 3` rounds on all graphs of maximum degree `≤ Δ`. Lower bound (Lemma 18): for every
`r` there is an identifier set of size `n ≤ Δ^(2r+2)` on which no `r`-round algorithm (with any
inputs, e.g. random bits; see `lemma18_randomized` for probabilities) solves `P*`. -/
theorem theorem4 {Δ : ℕ} (hΔ : 3 ≤ Δ) :
    (∀ (V : Type*) [Fintype V] [DecidableEq V],
      ∃ f : SimpleGraph V → (V → Unit) → V → ℕ × Option V,
        IsLocal (6 * Nat.clog (Δ - 1) (Fintype.card V) + 3) f ∧
        ∀ (G : SimpleGraph V) (x : V → Unit), (∀ v, deg G v ≤ Δ) → Solves Δ G (f G x)) ∧
    (∀ r : ℕ, Fintype.card (TNode Δ (r + 1)) ≤ Δ ^ (2 * r + 2) ∧
      ∀ {α : Type*} [Nonempty α]
        (f : SimpleGraph (TNode Δ (r + 1)) → (TNode Δ (r + 1) → α) → TNode Δ (r + 1) →
          ℕ × Option (TNode Δ (r + 1))), IsLocal r f →
        ¬ ∀ (G : SimpleGraph (TNode Δ (r + 1))) (x : TNode Δ (r + 1) → α),
          (∀ v, deg G v ≤ Δ) → Solves Δ G (f G x)) :=
  ⟨fun _ _ _ => lemma17 hΔ, fun r => lemma18_lowerBound hΔ r⟩

end Podc.MinimalSymmetryBreaking
