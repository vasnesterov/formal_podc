import Papers.PODC2024.ListDefectiveColoring.TwoSweep
import Podc.Local.LocallyIterative
import Podc.Local.Locality

/-!
# The Two-Sweep algorithm as a synchronous distributed algorithm (Lemma 3.3 of [FK24])

We implement Algorithm 1 of [FK24] in the synchronous round model of CSLib
(`Cslib.LocallyIterative.Algorithm`): in round `t` every node replaces its state by a function of
the round number, its own state and the **set** of its neighbours' states. A node's state
(`NodeState`) contains its identifier, its initial colour, its out-neighbourhood (as a set of
identifiers), its list and defect function (the local input), and the two outputs `S_v` and
`x_v` (initially `none`). Identifiers are only used to recognise out-neighbours; the step function
does not depend on the graph.

Model: synchronous, deterministic, fault-free LOCAL rounds; all nodes start at round `0` and know
`p` and `q`. Every node broadcasts its whole state each round, which is LOCAL; the paper's message
size claim (Lemma 3.3: "the nodes exchange a list of `p` colours"; in Phase I the only new
information is `S_v`, in Phase II only `x_v`) is not formalized.

* Rounds `0, …, q-1` (Phase I): in round `t` the nodes with initial colour `t` choose `S_v`
  (a best `min(p, |L_v|)`-subset for the score `d_v(x) − k_v(x)`).
* Rounds `q, …, 2q-1` (Phase II): in round `2q-1-c` the nodes with initial colour `c` choose
  `x_v ∈ S_v` with `k_v(x_v) + r_v(x_v) ≤ d_v(x_v)`.

## Main results

* `twoSweep_correct` (**Lemma 3.3**, and **Theorem 1.1** for `ε = 0`): from a proper
  `q`-colouring, after `2q` rounds every node has output a colour and the outputs form an oriented
  list defective colouring, provided the slack condition (2) holds.
* `twoSweep_listColoring`: the corollary for list colouring with lists of size `≥ β² + β + 1`
  (Section 1.1, "List coloring with bounded outdegree", `p = β + 1`, all defects `0`).
* `twoSweep_threeColoring`: list `d`-defective colouring with lists of size `3` whenever
  `d > (2Δ − 3)/3` (Section 1.1, generalizing [BHL+19]), using `out v = N(v)`.
-/

open Finset Cslib.LocallyIterative

namespace FK24

variable {V α : Type*}

/-- The local state of a node in the Two-Sweep algorithm. -/
structure NodeState (V α : Type*) where
  /-- The node's identifier. -/
  id : V
  /-- The initial colour (from the proper `q`-colouring). -/
  c : ℕ
  /-- The identifiers of the out-neighbours. -/
  out : Finset V
  /-- The colour list `L_v`. -/
  L : Finset α
  /-- The defect function `d_v`. -/
  d : α → ℕ
  /-- The sublist `S_v` chosen in Phase I. -/
  S : Option (Finset α)
  /-- The final colour `x_v` chosen in Phase II. -/
  col : Option α

namespace TwoSweepAlg

/-- A best `m`-subset of `L` for the score `g` (any fixed choice; Algorithm 1 sorts `L` by `g`). -/
noncomputable def bestSubset (L : Finset α) (m : ℕ) (g : α → ℤ) : Finset α :=
  if h : m ≤ L.card then Classical.choose (exists_isBestSubset L h g) else ∅

theorem bestSubset_spec (L : Finset α) {m : ℕ} (g : α → ℤ) (h : m ≤ L.card) :
    IsBestSubset L m g (bestSubset L m g) := by
  unfold bestSubset; simp only [h, ↓reduceDIte]; exact Classical.choose_spec (exists_isBestSubset L h g)

/-- `k_v(x)` as computed by the node with state `s` from the set `N` of its neighbours' states. -/
noncomputable def kOf (s : NodeState V α) (N : Set (NodeState V α)) (x : α) : ℕ :=
  Set.ncard {s' ∈ N | s'.id ∈ s.out ∧ s'.c < s.c ∧ x ∈ s'.S.getD ∅}

/-- `r_v(x)` as computed by the node with state `s` from the set `N` of its neighbours' states. -/
noncomputable def rOf (s : NodeState V α) (N : Set (NodeState V α)) (x : α) : ℕ :=
  Set.ncard {s' ∈ N | s'.id ∈ s.out ∧ s.c < s'.c ∧ s'.col = some x}

/-- Phase I action: choose `S_v` (line 4 of Algorithm 1). -/
noncomputable def phaseI (p : ℕ) (s : NodeState V α) (N : Set (NodeState V α)) :
    NodeState V α :=
  { s with S := some (bestSubset s.L (min p s.L.card) (fun x => (s.d x : ℤ) - kOf s N x)) }

/-- Phase II action: choose `x_v ∈ S_v` with `k_v(x_v) + r_v(x_v) ≤ d_v(x_v)` (line 9). -/
noncomputable def phaseII (s : NodeState V α) (N : Set (NodeState V α)) : NodeState V α :=
  if h : ∃ x, x ∈ s.S.getD ∅ ∧ kOf s N x + rOf s N x ≤ s.d x then
    { s with col := some (Classical.choose h) }
  else s

/-- The round function of Algorithm 1. -/
noncomputable def step (p q : ℕ) (t : ℕ) (s : NodeState V α) (N : Set (NodeState V α)) :
    NodeState V α :=
  if t < q then (if s.c = t then phaseI p s N else s)
  else if s.c + t + 1 = 2 * q then phaseII s N else s

variable {p q t : ℕ} {s : NodeState V α} {N : Set (NodeState V α)}

theorem step_id : (step p q t s N).id = s.id := by
  unfold step phaseI phaseII; split_ifs <;> rfl
theorem step_c : (step p q t s N).c = s.c := by
  unfold step phaseI phaseII; split_ifs <;> rfl
theorem step_out : (step p q t s N).out = s.out := by
  unfold step phaseI phaseII; split_ifs <;> rfl
theorem step_L : (step p q t s N).L = s.L := by
  unfold step phaseI phaseII; split_ifs <;> rfl
theorem step_d : (step p q t s N).d = s.d := by
  unfold step phaseI phaseII; split_ifs <;> rfl

theorem step_S_of_not (h : ¬ (t < q ∧ s.c = t)) : (step p q t s N).S = s.S := by
  unfold step phaseI phaseII; split_ifs <;> simp_all

theorem step_S_of_eq (h1 : t < q) (h2 : s.c = t) :
    (step p q t s N).S =
      some (bestSubset s.L (min p s.L.card) (fun x => (s.d x : ℤ) - kOf s N x)) := by
  unfold step phaseI; simp [h1, h2]

theorem step_col_of_not (h : ¬ (q ≤ t ∧ s.c + t + 1 = 2 * q)) : (step p q t s N).col = s.col := by
  unfold step phaseI phaseII; split_ifs <;> first | rfl | omega

theorem step_col_of_eq (h1 : q ≤ t) (h2 : s.c + t + 1 = 2 * q) :
    (step p q t s N).col = (phaseII s N).col := by
  unfold step; simp [show ¬ t < q by omega, h2]

end TwoSweepAlg

open TwoSweepAlg

/-- Algorithm 1 of [FK24] (Two-Sweep-Algorithm(q, p)) as a synchronous round algorithm. -/
noncomputable def twoSweep (p q : ℕ) : Algorithm (NodeState V α) := ⟨step p q⟩

/-- The initial state of node `v`: identifier, initial colour, out-neighbourhood, list and defect
function; no outputs yet. -/
def initState (out : V → Finset V) (c : V → ℕ) (I : ListInstance V α) (v : V) : NodeState V α :=
  ⟨v, c v, out v, I.L v, I.d v, none, none⟩

section Run

variable (G : SimpleGraph V) (out : V → Finset V) (c : V → ℕ) (I : ListInstance V α) (p q : ℕ)

/-- The state of node `v` after `t` rounds of the Two-Sweep algorithm. -/
noncomputable abbrev st (t : ℕ) (v : V) : NodeState V α :=
  (twoSweep p q).run G (initState out c I) t v

variable {G out c I p q}

theorem st_succ (t : ℕ) (v : V) :
    st G out c I p q (t + 1) v =
      step p q t (st G out c I p q t v) (nbrColors G (st G out c I p q t) v) :=
  Algorithm.run_succ_apply _ _ _ _

theorem st_fields (t : ℕ) (v : V) :
    (st G out c I p q t v).id = v ∧ (st G out c I p q t v).c = c v ∧
      (st G out c I p q t v).out = out v ∧ (st G out c I p q t v).L = I.L v ∧
      (st G out c I p q t v).d = I.d v := by
  induction t with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ t ih =>
    rw [st_succ, step_id, step_c, step_out, step_L, step_d]
    exact ih

theorem st_S_of_le {t : ℕ} {v : V} (h : t ≤ c v) : (st G out c I p q t v).S = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [st_succ, step_S_of_not, ih (by omega)]
    rw [(st_fields t v).2.1]; omega

theorem st_S_of_lt {t : ℕ} {v : V} (h : c v < t) :
    (st G out c I p q t v).S = (st G out c I p q (c v + 1) v).S := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge (c v) t with h' | h'
    · rw [st_succ, step_S_of_not, ih h']
      rw [(st_fields t v).2.1]; omega
    · have : t = c v := by omega
      subst this; rfl

theorem st_col_of_le {t : ℕ} {v : V} (h : t + c v + 1 ≤ 2 * q) :
    (st G out c I p q t v).col = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [st_succ, step_col_of_not, ih (by omega)]
    rw [(st_fields t v).2.1]; omega

theorem st_col_of_lt {t : ℕ} {v : V} (hcv : c v < q) (h : 2 * q < t + c v + 1) :
    (st G out c I p q t v).col = (st G out c I p q (2 * q - c v) v).col := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge (2 * q) (t + c v + 1) with h' | h'
    · rw [st_succ, step_col_of_not, ih h']
      rw [(st_fields t v).2.1]; omega
    · have : t + 1 = 2 * q - c v := by omega
      rw [this]

/-- The sublist chosen by `v` in Phase I. -/
noncomputable def Sfin (G : SimpleGraph V) (out : V → Finset V) (c : V → ℕ) (I : ListInstance V α)
    (p q : ℕ) (v : V) : Finset α :=
  ((st G out c I p q (c v + 1) v).S).getD ∅

/-- The (optional) colour chosen by `v` in Phase II. -/
noncomputable def colOpt (G : SimpleGraph V) (out : V → Finset V) (c : V → ℕ)
    (I : ListInstance V α) (p q : ℕ) (v : V) : Option α :=
  (st G out c I p q (2 * q - c v) v).col

theorem st_S_eq_Sfin {t : ℕ} {v : V} (h : c v < t) :
    (st G out c I p q t v).S.getD ∅ = Sfin G out c I p q v := by
  rw [st_S_of_lt h]; rfl

variable [DecidableEq α] (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (hcq : ∀ v, c v < q)
include hout hcq


omit hcq in
theorem kOf_eq (t : ℕ) (v : V) (hct : c v ≤ t) (x : α) :
    kOf (st G out c I p q t v) (nbrColors G (st G out c I p q t) v) x =
      kCount out c (Sfin G out c I p q) v x := by
  unfold kOf kCount
  rw [(st_fields t v).2.2.1, (st_fields t v).2.1]
  have := ncard_nbrColors_filter (G := G) (c := st G out c I p q t) (v := v) NodeState.id
    (fun u => (st_fields t u).1)
    (out v) (hout v) (fun s' => s'.c < c v ∧ x ∈ s'.S.getD ∅)
  rw [this]
  congr 1
  ext u
  simp only [Finset.mem_filter]
  rw [(st_fields t u).2.1]
  constructor
  · rintro ⟨hu, h1, h2⟩; exact ⟨hu, h1, by rwa [st_S_eq_Sfin (by omega)] at h2⟩
  · rintro ⟨hu, h1, h2⟩; exact ⟨hu, h1, by rwa [st_S_eq_Sfin (by omega)]⟩

theorem Sfin_eq (v : V) :
    Sfin G out c I p q v = bestSubset (I.L v) (min p (I.L v).card)
      (fun x => (I.d v x : ℤ) - kCount out c (Sfin G out c I p q) v x) := by
  show ((st G out c I p q (c v + 1) v).S).getD ∅ = _
  rw [st_succ, step_S_of_eq (hcq v) (st_fields (c v) v).2.1, Option.getD_some]
  rw [(st_fields (c v) v).2.2.2.1, (st_fields (c v) v).2.2.2.2]
  congr 1
  funext x
  rw [kOf_eq hout (c v) v le_rfl x]

/-- The outputs of Phase I satisfy the Phase I specification. -/
theorem isPhaseI_Sfin : IsPhaseI I out c p (Sfin G out c I p q) := by
  intro v
  rw [Sfin_eq hout hcq v]
  exact bestSubset_spec _ _ (min_le_right _ _)

theorem rOf_eq (v : V) (x : α) :
    rOf (st G out c I p q (2 * q - c v - 1) v) (nbrColors G (st G out c I p q (2 * q - c v - 1)) v) x
      = #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some x} := by
  unfold rOf
  set t := 2 * q - c v - 1
  rw [(st_fields t v).2.2.1, (st_fields t v).2.1]
  have := ncard_nbrColors_filter (G := G) (c := st G out c I p q t) (v := v) NodeState.id
    (fun u => (st_fields t u).1)
    (out v) (hout v) (fun s' => c v < s'.c ∧ s'.col = some x)
  rw [this]
  congr 1
  ext u
  simp only [Finset.mem_filter]
  rw [(st_fields t u).2.1]
  constructor
  · rintro ⟨hu, h1, h2⟩
    refine ⟨hu, h1, ?_⟩
    unfold colOpt; rwa [st_col_of_lt (hcq u) (by have := hcq v; omega)] at h2
  · rintro ⟨hu, h1, h2⟩
    refine ⟨hu, h1, ?_⟩
    unfold colOpt at h2; rwa [st_col_of_lt (hcq u) (by have := hcq v; omega)]

theorem colOpt_spec (hp : 1 ≤ p)
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v)
    (hslack : ∀ v, max (p ^ 2) (I.L v).card * beta out v < p * I.weight v) (v : V) :
    ∃ y, colOpt G out c I p q v = some y ∧ y ∈ Sfin G out c I p q v ∧
      kCount out c (Sfin G out c I p q) v y +
        #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y} ≤ I.d v y := by
  have hq := hcq v
  set t := 2 * q - c v - 1
  have ht1 : 2 * q - c v = t + 1 := by omega
  -- existence of a good colour
  have h34 := (isPhaseI_Sfin hout hcq (I := I) (p := p)).eq3_eq4 hp hc v (hslack v)
  set S := Sfin G out c I p q
  have hr : ∑ y ∈ S v, #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y} ≤
      #{u ∈ out v | c v < c u} := by
    have := sum_card_filter_mem_le (S v) {u ∈ out v | c v < c u}
      (fun u => (colOpt G out c I p q u).toFinset)
    refine le_trans (le_of_eq ?_) (this.trans ?_)
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun u _ => ?_
      rw [Option.mem_toFinset, Option.mem_def]
    · refine (Finset.sum_le_sum fun u _ => ?_).trans (le_of_eq (Finset.card_eq_sum_ones _).symm)
      rw [Option.card_toFinset]; cases colOpt G out c I p q u <;> simp
  have hex : ∃ y, y ∈ S v ∧ kCount out c S v y +
      #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y} ≤ I.d v y := by
    by_contra hne
    push Not at hne
    have hsum : ∑ y ∈ S v, (I.d v y + 1) ≤ ∑ y ∈ S v, (kCount out c S v y +
        #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y}) :=
      Finset.sum_le_sum fun y hy => hne y hy
    have hsum2 : ∑ y ∈ S v, (kCount out c S v y +
        #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y}) =
        ∑ y ∈ S v, kCount out c S v y +
          ∑ y ∈ S v, #{u ∈ out v | c v < c u ∧ colOpt G out c I p q u = some y} :=
      Finset.sum_add_distrib
    omega
  -- the step at round t
  have hstate : (st G out c I p q t v).S.getD ∅ = S v := st_S_eq_Sfin (by omega)
  have hcond : ∃ y, y ∈ (st G out c I p q t v).S.getD ∅ ∧
      kOf (st G out c I p q t v) (nbrColors G (st G out c I p q t) v) y +
        rOf (st G out c I p q t v) (nbrColors G (st G out c I p q t) v) y ≤
          (st G out c I p q t v).d y := by
    obtain ⟨y, hy, hle⟩ := hex
    refine ⟨y, by rw [hstate]; exact hy, ?_⟩
    rw [kOf_eq hout t v (by omega), rOf_eq hout hcq v, (st_fields t v).2.2.2.2]
    exact hle
  have hcol : colOpt G out c I p q v = some (Classical.choose hcond) := by
    unfold colOpt
    rw [ht1, st_succ, step_col_of_eq (by omega) (by rw [(st_fields t v).2.1]; omega)]
    unfold phaseII
    simp only [hcond, ↓reduceDIte]
  have hspec := Classical.choose_spec hcond
  generalize Classical.choose hcond = y at hcol hspec
  refine ⟨y, hcol, ?_, ?_⟩
  · rw [← hstate]; exact hspec.1
  · have := hspec.2
    rw [kOf_eq hout t v (by omega), rOf_eq hout hcq v,
      (st_fields t v).2.2.2.2] at this
    exact this

end Run

variable [DecidableEq α]

omit [DecidableEq α] in
/-- The Two-Sweep algorithm is a `2q`-round LOCAL algorithm: the state of a node after `2q`
rounds (in particular its output colour) only depends on the graph and the initial states
(identifiers, initial colours, out-neighbourhoods, lists and defects) within distance `2q`. -/
theorem twoSweep_isLocal (p q : ℕ) :
    Cslib.Local.IsLocal (2 * q) fun G (s₀ : V → NodeState V α) v =>
      (twoSweep p q).run G s₀ (2 * q) v :=
  Algorithm.run_isLocal _ _

/-- **Lemma 3.3** of [FK24] (Algorithm 1 is correct and takes `2q` rounds), which is also
**Theorem 1.1** for `ε = 0`. Let the out-neighbours of every node be neighbours in the
communication graph `G`, let `c` be an initial colouring with values `< q` that is proper along
out-edges (e.g. a proper `q`-colouring of `G`), let `p ≥ 1`, and assume the slack condition (2):
`∑_{x ∈ L_v} (d_v(x) + 1) > max(p, |L_v|/p) · β_v` for all `v`. Then after `2q` rounds of the
Two-Sweep algorithm every node `v` has output a colour `col v`, and `col` is an oriented list
defective colouring. -/
theorem twoSweep_correct (G : SimpleGraph V) (out : V → Finset V)
    (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (c : V → ℕ) (q : ℕ) (hcq : ∀ v, c v < q)
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v) (I : ListInstance V α) (p : ℕ) (hp : 1 ≤ p)
    (hslack : ∀ v, max (p : ℝ) ((I.L v).card / p) * beta out v < I.weight v) :
    ∃ col : V → α, (∀ v, ((twoSweep p q).run G (initState out c I) (2 * q) v).col = some (col v))
      ∧ IsOLDC I out col := by
  have hslack' : ∀ v, max (p ^ 2) (I.L v).card * beta out v < p * I.weight v :=
    fun v => (slack_iff_nat hp _ _ _).1 (hslack v)
  have hspec := fun v => colOpt_spec (G := G) hout hcq hp hc hslack' v
  choose col hcol hmem hle using hspec
  refine ⟨col, fun v => ?_, ?_⟩
  · have := hcq v
    rw [st_col_of_lt this (by omega)]; exact hcol v
  · refine IsPhaseII.isOLDC (isPhaseI_Sfin hout hcq) (fun v => ⟨hmem v, ?_⟩) hc
    refine le_trans (le_of_eq ?_) (hle v)
    congr 1
    unfold rCount
    congr 1
    refine Finset.filter_congr fun u _ => ?_
    rw [hcol u, Option.some_inj]

/-- **Lemma 3.3** / **Theorem 1.1** (`ε = 0`) for a proper `q`-colouring of `G` and an orientation
of (some of) the edges of `G`. -/
theorem twoSweep_correct_of_isProper (G : SimpleGraph V) (out : V → Finset V)
    (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (c : V → ℕ) (q : ℕ) (hcq : ∀ v, c v < q)
    (hc : IsProper G c) (I : ListInstance V α) (p : ℕ) (hp : 1 ≤ p)
    (hslack : ∀ v, max (p : ℝ) ((I.L v).card / p) * beta out v < I.weight v) :
    ∃ col : V → α, (∀ v, ((twoSweep p q).run G (initState out c I) (2 * q) v).col = some (col v))
      ∧ IsOLDC I out col :=
  twoSweep_correct G out hout c q hcq (fun v u hu => (hc (hout v u hu)).symm) I p hp hslack

/-- Section 1.1 of [FK24], "List coloring with bounded outdegree": with `p = β + 1` and all
defects `0`, the Two-Sweep algorithm properly list-colours an oriented graph with out-degrees
`≤ β` from lists of size `≥ β² + β + 1`, in `2q` rounds from a proper `q`-colouring (combined with
an `O(β²)`-colouring of Linial, this gives `O(β² + log* n)` rounds). -/
theorem twoSweep_listColoring (G : SimpleGraph V) (out : V → Finset V)
    (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (c : V → ℕ) (q : ℕ) (hcq : ∀ v, c v < q)
    (hc : IsProper G c) (L : V → Finset α) (β : ℕ) (hβ1 : 1 ≤ β) (hβ : ∀ v, (out v).card ≤ β)
    (hL : ∀ v, β ^ 2 + β + 1 ≤ (L v).card) :
    ∃ col : V → α, (∀ v, ((twoSweep (β + 1) q).run G (initState out c ⟨L, fun _ _ => 0⟩)
        (2 * q) v).col = some (col v)) ∧
      ∀ v, col v ∈ L v ∧ ∀ u ∈ out v, col u ≠ col v := by
  obtain ⟨col, hrun, hcol⟩ := twoSweep_correct_of_isProper G out hout c q hcq hc
    ⟨L, fun _ _ => 0⟩ (β + 1) (by omega) (by
      intro v
      rw [slack_iff_nat (by omega)]
      simp only [ListInstance.weight, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
      have hb : beta out v ≤ β := max_le hβ1 (hβ v)
      have hL' := hL v
      rcases le_total ((β + 1) ^ 2) (L v).card with h | h
      · rw [max_eq_right h]
        nlinarith
      · rw [max_eq_left h]
        nlinarith)
  refine ⟨col, hrun, fun v => ⟨(hcol v).1, fun u hu he => ?_⟩⟩
  have h2 : #{u ∈ out v | col u = col v} ≤ 0 := (hcol v).2
  have : 0 < #{u ∈ out v | col u = col v} :=
    Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨hu, he⟩⟩
  omega

/-- Section 1.1 of [FK24] (generalizing [BHL+19]): list `d`-defective colouring with lists of
size `3` from a proper `q`-colouring in `2q` rounds (with `p = 2`), whenever `d > (2Δ − 3)/3`,
i.e. `2Δ < 3(d + 1)`. Here the "orientation" is `out v = N(v)` (every edge in both directions),
so the output is a list defective colouring of `G`. With an initial `O(Δ)`-colouring this is the
paper's `O(Δ + log* n)`-round claim. -/
theorem twoSweep_threeColoring (G : SimpleGraph V) [G.LocallyFinite] (c : V → ℕ) (q : ℕ)
    (hcq : ∀ v, c v < q) (hc : IsProper G c) (L : V → Finset α) (d Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (hL : ∀ v, (L v).card = 3) (hd : 2 * Δ < 3 * (d + 1)) :
    ∃ col : V → α, (∀ v, ((twoSweep 2 q).run G
        (initState (fun v => G.neighborFinset v) c ⟨L, fun _ _ => d⟩) (2 * q) v).col =
          some (col v)) ∧
      IsListDefective G ⟨L, fun _ _ => d⟩ col := by
  obtain ⟨col, hrun, hcol⟩ := twoSweep_correct_of_isProper G (fun v => G.neighborFinset v)
    (fun v u hu => (G.mem_neighborFinset v u).1 hu) c q hcq hc ⟨L, fun _ _ => d⟩ 2 (by norm_num) (by
      intro v
      rw [slack_iff_nat (p := 2) (by norm_num)]
      simp only [ListInstance.weight, Finset.sum_const, smul_eq_mul, hL v]
      have hb : beta (fun v => G.neighborFinset v) v ≤ max 1 Δ :=
        max_le_max le_rfl (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hΔ v)
      have : max (2 ^ 2) 3 = 4 := rfl
      rw [this]
      rcases Nat.eq_zero_or_pos Δ with h0 | h0
      · subst h0
        have : beta (fun v => G.neighborFinset v) v ≤ 1 := by simpa using hb
        omega
      · have : beta (fun v => G.neighborFinset v) v ≤ Δ := hb.trans (max_le h0 le_rfl)
        omega)
  exact ⟨col, hrun, hcol⟩

end FK24

namespace FK24

variable {V α : Type*} [DecidableEq α]

/-- The form of Theorem 1.1 stated in the abstract of [FK24]: if all lists have size `p²` and
`∑_{x ∈ L_v} (d_v(x) + 1) > p · β_v`, then two sweeps (`2q` rounds from a proper `q`-colouring)
compute an oriented list defective colouring. -/
theorem twoSweep_correct_sq (G : SimpleGraph V) (out : V → Finset V)
    (hout : ∀ v, ∀ u ∈ out v, G.Adj v u) (c : V → ℕ) (q : ℕ) (hcq : ∀ v, c v < q)
    (hc : ∀ v, ∀ u ∈ out v, c u ≠ c v) (I : ListInstance V α) (p : ℕ) (hp : 1 ≤ p)
    (hL : ∀ v, (I.L v).card = p ^ 2) (hslack : ∀ v, p * beta out v < I.weight v) :
    ∃ col : V → α, (∀ v, ((twoSweep p q).run G (initState out c I) (2 * q) v).col = some (col v))
      ∧ IsOLDC I out col := by
  refine twoSweep_correct G out hout c q hcq hc I p hp fun v => ?_
  rw [slack_iff_nat hp, hL v, max_self, sq, mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left (hslack v) (by omega)

end FK24
