import Papers.PODC2010.TruncatedGaleShapley.Theorems
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# The truncated Gale–Shapley algorithm in the port-numbering model (§1.2, §4)

The model of §1.2 is CSLib's anonymous port-numbering model (`Cslib.PortNumbering`): synchronous
deterministic message passing; a node knows its degree, its colour and the constant `T`; its ports
are numbered by its preferences (port `0` = most preferred; the paper numbers from `1`).

* `NodeData`: the local data of a node (colour, a local ranking `rk` of its ports, and the
  variables `C`, `c`, `p` of §4, holding port numbers).
* `rule`: the local rule; even rounds are blue turns, odd rounds red turns. A node reads the data
  of its neighbours (full-information messages) but uses exactly the information carried by the
  messages of §4 ('propose', 'accept', 'reject', 'break').
* `gsAlg T`: the port-numbering algorithm (inputs: colour and port ranking; output: the port of the
  partner, if any).
* `toBicoloured`: the bicoloured graph with preferences defined by a simple port-numbered graph,
  a proper 2-colouring and port rankings.
* `dec_localRun`: after `2i` communication rounds the decoded configuration is the state
  `run i` of the centralised algorithm (`Theorems.lean`).
-/

namespace Podc.TruncatedGaleShapley

open Finset Cslib.PortNumbering

set_option linter.unusedSectionVars false

/-- Local data of a node: colour (`true` = red), ranking of its ports (smaller = preferred), the
candidate ports `C`, the port of the outstanding proposal `c`, and the port of the partner `p`. -/
structure NodeData : Type where
  /-- Colour. -/
  red : Bool
  /-- Local preference ranking of the ports. -/
  rk : ℕ → ℕ
  /-- Candidate ports (red nodes). -/
  C : Finset ℕ
  /-- Port of the outstanding proposal (red nodes). -/
  c : Option ℕ
  /-- Port of the partner. -/
  p : Option ℕ

/-- The most preferred port of `S` for the ranking `rk`. -/
noncomputable def pbest (rk : ℕ → ℕ) (S : Finset ℕ) : Option ℕ :=
  if h : S.Nonempty then some (S.exists_min_image rk h).choose else none

/-- Initial data from the degree and the input (colour, port ranking). -/
def initData (d : ℕ) (x : Bool × (ℕ → ℕ)) : NodeData where
  red := x.1
  rk := x.2
  C := if x.1 then range d else ∅
  c := none
  p := none

/-- Step 1 of the red turn at port level (`acc i`: the neighbour behind port `i` points back). -/
def pStep1 (x : NodeData) (acc : ℕ → Prop) [DecidablePred acc] : Finset ℕ × Option ℕ :=
  match x.c with
  | none => (x.C, x.p)
  | some i => if acc i then (x.C, some i) else (x.C.erase i, x.p)

/-- Step 2 of the red turn at port level. -/
def pStep2 (acc : ℕ → Prop) [DecidablePred acc] : Finset ℕ × Option ℕ → Finset ℕ × Option ℕ
  | (C, none) => (C, none)
  | (C, some i) => if acc i then (C, some i) else (C.erase i, none)

/-- The red node's update from the result `r = (C, p)` of steps 1–2: step 3 proposes to the best
remaining port if unmatched. -/
noncomputable def redUpdate (x : NodeData) (r : Finset ℕ × Option ℕ) : NodeData :=
  { x with C := r.1, p := r.2, c := if r.2 = none then pbest x.rk r.1 else none }

open Classical in
/-- The local rule. In round `t` (from `0`), node data `x`, degree `d`, information `m i =
(neighbour's data, neighbour's port)` from each port `i < d`:
* `t` even (blue turn): a blue node with proposers `P` (ports whose neighbour has an outstanding
  proposal on the connecting edge) takes the best port of `P ∪ {p}` as its partner;
* `t` odd (red turn): a red node with an outstanding proposal on port `i` is accepted iff the
  neighbour now points back ('accept'), otherwise rejected (port `i` removed); a matched red node
  whose partner no longer points back has received 'break' (port removed, unmatched); an
  unmatched red node then proposes to its best remaining port. -/
noncomputable def rule (t d : ℕ) (x : NodeData) (m : ℕ → Option (NodeData × ℕ)) : NodeData :=
  if t % 2 = 0 then
    if x.red then x else
      let P := (range d).filter fun i => ∃ y j, m i = some (y, j) ∧ y.c = some j
      if P.Nonempty then { x with p := pbest x.rk (P ∪ x.p.toFinset) } else x
  else
    if x.red then
      let acc : ℕ → Prop := fun i => ∃ y j, m i = some (y, j) ∧ y.p = some j
      redUpdate x (pStep2 acc (pStep1 x acc))
    else x

/-- The truncated Gale–Shapley algorithm, run for `T` communication rounds, in the port-numbering
model: input colour and port ranking, output the port of the partner (`none` = unmatched). -/
noncomputable def gsAlg (T : ℕ) : Algorithm (Bool × (ℕ → ℕ)) (Option ℕ) :=
  ((Algorithm.ofFun initData).seq 0 (Algorithm.ofLocal rule)).seq T
    (Algorithm.ofFun fun _ x => x.p)

variable {V : Type} [Fintype V] [DecidableEq V]

theorem gsAlg_eval (T : ℕ) (G : PNGraph V) (x : V → Bool × (ℕ → ℕ)) (v : V) :
    (gsAlg T).eval G T x v =
      (Algorithm.localRun G rule (fun u => initData (G.deg u) (x u)) T v).p := by
  change (gsAlg T).eval G (T + 0) x v = _
  rw [gsAlg, Algorithm.eval_seq, Algorithm.eval_ofFun]
  conv_lhs => rw [← zero_add T]
  rw [Algorithm.eval_seq, Algorithm.eval_ofLocal]
  rfl

/-! ### The bicoloured graph defined by a port-numbered graph -/

/-- The port of `v` leading to `u` (`0` if none). -/
noncomputable def portOf (G : PNGraph V) (v u : V) : ℕ :=
  open Classical in if h : ∃ i, i < G.deg v ∧ G.nbr v i = u then Nat.find h else 0

lemma portOf_nbr {G : PNGraph V} (hG : G.IsSimple) {v : V} {i : ℕ} (hi : i < G.deg v) :
    portOf G v (G.nbr v i) = i := by
  classical
  have h : ∃ j, j < G.deg v ∧ G.nbr v j = G.nbr v i := ⟨i, hi, rfl⟩
  unfold portOf
  split
  · rename_i h'
    have := Nat.find_spec h'
    exact G.port_unique hG this.1 hi this.2
  · contradiction

/-- Hypotheses on the input of the port-numbering algorithm: `G` is simple, `red` is a proper
2-colouring, and every node ranks its ports injectively. -/
structure GoodInput (G : PNGraph V) (red : V → Bool) (rk : V → ℕ → ℕ) : Prop where
  simple : G.IsSimple
  red_ne : ∀ v i, i < G.deg v → red (G.nbr v i) ≠ red v
  rk_inj : ∀ v i j, i < G.deg v → j < G.deg v → rk v i = rk v j → i = j

/-- The bicoloured graph with preferences: neighbours of `v` are the nodes behind its ports, and
`v` ranks the neighbour behind port `i` by `rk v i`. -/
noncomputable def toBicoloured (G : PNGraph V) (red : V → Bool) (rk : V → ℕ → ℕ)
    (h : GoodInput G red rk) : Bicoloured V where
  N v := (range (G.deg v)).image (G.nbr v)
  symm := by
    intro u v hv
    simp only [mem_image, mem_range] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    exact ⟨G.rport u i, G.rport_lt hi, G.nbr_nbr hi⟩
  rank v u := rk v (portOf G v u)
  rank_inj := by
    intro v u u' hu hu' he
    simp only [mem_image, mem_range] at hu hu'
    obtain ⟨i, hi, rfl⟩ := hu
    obtain ⟨j, hj, rfl⟩ := hu'
    rw [portOf_nbr h.simple hi, portOf_nbr h.simple hj] at he
    rw [h.rk_inj v i j hi hj he]
  red := red
  red_ne := by
    intro u v hv
    simp only [mem_image, mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact h.red_ne u i hi

/-! ### Decoding port-level configurations -/

section Decode

variable {G : PNGraph V} {red : V → Bool} {rk : V → ℕ → ℕ} (h : GoodInput G red rk)

/-- Decode a port-level configuration into a node-level state. -/
def dec (G : PNGraph V) (s : V → NodeData) : State V where
  C v := (s v).C.image (G.nbr v)
  c v := (s v).c.map (G.nbr v)
  p v := (s v).p.map (G.nbr v)

/-- Well-formed port-level configurations: the colour and ranking are the inputs, and all stored
ports exist. -/
structure PInv (G : PNGraph V) (red : V → Bool) (rk : V → ℕ → ℕ) (s : V → NodeData) : Prop where
  red : ∀ v, (s v).red = red v
  rk : ∀ v, (s v).rk = rk v
  C : ∀ v, (s v).C ⊆ range (G.deg v)
  c : ∀ v i, (s v).c = some i → i < G.deg v
  p : ∀ v i, (s v).p = some i → i < G.deg v

include h in
lemma nbr_eq_iff {v : V} {i j : ℕ} (hi : i < G.deg v) (hj : j < G.deg (G.nbr v i)) :
    G.nbr (G.nbr v i) j = v ↔ j = G.rport v i := by
  constructor
  · intro hv
    exact G.port_unique h.simple hj (G.rport_lt hi) (hv.trans (G.nbr_nbr hi).symm)
  · rintro rfl; exact G.nbr_nbr hi

include h in
/-- The neighbour behind port `i` of `v` stores port `j` pointing back to `v` iff its decoded
pointer is `v`. -/
lemma map_eq_some_iff {v : V} {i : ℕ} (hi : i < G.deg v) {o : Option ℕ}
    (ho : ∀ j, o = some j → j < G.deg (G.nbr v i)) :
    o.map (G.nbr (G.nbr v i)) = some v ↔ o = some (G.rport v i) := by
  constructor
  · intro he
    obtain ⟨j, hj, hjv⟩ := Option.map_eq_some_iff.1 he
    rw [hj, (nbr_eq_iff h hi (ho j hj)).1 hjv]
  · intro he; rw [he]; simp [G.nbr_nbr hi]

lemma pbest_spec {rk' : ℕ → ℕ} {S : Finset ℕ} {i : ℕ} (hb : pbest rk' S = some i) :
    i ∈ S ∧ ∀ j ∈ S, rk' i ≤ rk' j := by
  unfold pbest at hb
  split_ifs at hb with hS
  cases hb; exact (S.exists_min_image rk' hS).choose_spec

lemma pbest_eq_none {rk' : ℕ → ℕ} {S : Finset ℕ} : pbest rk' S = none ↔ S = ∅ := by
  unfold pbest; split_ifs with hS <;> simp_all [Finset.nonempty_iff_ne_empty]

include h in
lemma image_nbr_subset {v : V} {S : Finset ℕ} (hS : S ⊆ range (G.deg v)) :
    S.image (G.nbr v) ⊆ (toBicoloured G red rk h).N v :=
  image_subset_image hS

include h in
/-- The best port decodes to the best neighbour. -/
lemma pbest_map {v : V} {S : Finset ℕ} (hS : S ⊆ range (G.deg v)) :
    (pbest (rk v) S).map (G.nbr v) = (toBicoloured G red rk h).best v (S.image (G.nbr v)) := by
  rcases hb : pbest (rk v) S with _ | i
  · rw [pbest_eq_none.1 hb]; simp only [Option.map_none, image_empty]
    exact ((Bicoloured.best_eq_none _).2 rfl).symm
  · obtain ⟨hiS, hmin⟩ := pbest_spec hb
    symm
    rw [Option.map_some, Bicoloured.best_eq_some_iff _ (image_nbr_subset h hS)]
    refine ⟨mem_image_of_mem _ hiS, ?_⟩
    rintro y hy
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hy
    change rk v (portOf G v (G.nbr v i)) ≤ rk v (portOf G v (G.nbr v j))
    rw [portOf_nbr h.simple (mem_range.1 (hS hiS)), portOf_nbr h.simple (mem_range.1 (hS hj))]
    exact hmin j hj

include h in
lemma image_erase_nbr {v : V} {S : Finset ℕ} (hS : S ⊆ range (G.deg v)) {i : ℕ}
    (hi : i < G.deg v) : (S.erase i).image (G.nbr v) = (S.image (G.nbr v)).erase (G.nbr v i) := by
  ext y
  simp only [mem_image, mem_erase]
  constructor
  · rintro ⟨j, ⟨hji, hj⟩, rfl⟩
    exact ⟨fun he => hji (G.port_unique h.simple (mem_range.1 (hS hj)) hi he), j, hj, rfl⟩
  · rintro ⟨hne, j, hj, rfl⟩
    exact ⟨j, ⟨fun hji => hne (hji ▸ rfl), hj⟩, rfl⟩

lemma nbrInfo_of_lt {s : V → NodeData} {v : V} {i : ℕ} (hi : i < G.deg v) :
    Algorithm.nbrInfo G s v i = some (s (G.nbr v i), G.rport v i) := by
  simp [Algorithm.nbrInfo, hi]

/-- One communication round of the port-level algorithm. -/
noncomputable def pstep (G : PNGraph V) (t : ℕ) (s : V → NodeData) : V → NodeData :=
  fun v => rule t (G.deg v) (s v) (Algorithm.nbrInfo G s v)

lemma localRun_succ_eq (x : V → NodeData) (t : ℕ) :
    Algorithm.localRun G rule x (t + 1) = pstep G t (Algorithm.localRun G rule x t) := by
  funext v; exact Algorithm.localRun_succ G rule x t v

open Classical in
include h in
/-- The port-level proposers decode to the node-level proposers. -/
lemma proposers_dec {s : V → NodeData} (hs : PInv G red rk s) (v : V) :
    ((range (G.deg v)).filter fun i => ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧
        y.c = some j).image (G.nbr v) = (toBicoloured G red rk h).proposers (dec G s) v := by
  ext y
  simp only [Bicoloured.proposers, mem_image, mem_filter, mem_range]
  have hN : y ∈ (toBicoloured G red rk h).N v ↔ ∃ i, i < G.deg v ∧ G.nbr v i = y := by
    simp [toBicoloured]
  rw [hN]
  constructor
  · rintro ⟨i, ⟨hi, y', j, hm, hc⟩, rfl⟩
    rw [nbrInfo_of_lt hi] at hm
    cases hm
    refine ⟨⟨i, hi, rfl⟩, ?_⟩
    change ((s (G.nbr v i)).c).map _ = _
    rw [map_eq_some_iff h hi (hs.c _)]; exact hc
  · rintro ⟨⟨i, hi, rfl⟩, hc⟩
    change ((s (G.nbr v i)).c).map _ = _ at hc
    rw [map_eq_some_iff h hi (hs.c _)] at hc
    exact ⟨i, ⟨hi, _, _, nbrInfo_of_lt hi, hc⟩, rfl⟩

lemma image_union_toFinset {v : V} (S : Finset ℕ) (o : Option ℕ) :
    (S ∪ o.toFinset).image (G.nbr v) = S.image (G.nbr v) ∪ (o.map (G.nbr v)).toFinset := by
  cases o <;> simp

open Classical in
include h in
/-- A blue turn of the port-level algorithm decodes to the blue turn of §4. -/
lemma blue_step {s : V → NodeData} (hs : PInv G red rk s) {t : ℕ} (ht : t % 2 = 0) :
    PInv G red rk (pstep G t s) ∧
      dec G (pstep G t s) = (toBicoloured G red rk h).blueTurn (dec G s) := by
  set P : V → Finset ℕ := fun v => (range (G.deg v)).filter fun i =>
    ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧ y.c = some j
  have hv : ∀ v, pstep G t s v = if red v = true then s v else
      if (P v).Nonempty then { s v with p := pbest (rk v) (P v ∪ (s v).p.toFinset) } else s v := by
    intro v
    simp only [pstep, rule, ht, ite_true, hs.red v, hs.rk v, P]
  have hPsub : ∀ v, P v ∪ (s v).p.toFinset ⊆ range (G.deg v) := by
    intro v i hi
    rcases mem_union.1 hi with hi | hi
    · exact (mem_filter.1 hi).1
    · exact mem_range.2 (hs.p v i (by simpa using hi))
  refine ⟨⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v i hi => ?_⟩, ?_⟩
  · rw [hv]; split_ifs <;> simp [hs.red v]
  · rw [hv]; split_ifs <;> simp [hs.rk v]
  · rw [hv]; split_ifs <;> simp [hs.C v]
  · intro i hi; rw [hv] at hi; split_ifs at hi <;> exact hs.c v i hi
  · rw [hv] at hi
    split_ifs at hi
    · exact hs.p v i hi
    · exact mem_range.1 (hPsub v (pbest_spec hi).1)
    · exact hs.p v i hi
  · ext1
    · funext v; simp only [dec, Bicoloured.blueTurn_C, hv]; split_ifs <;> rfl
    · funext v; simp only [dec, Bicoloured.blueTurn_c, hv]; split_ifs <;> rfl
    · funext v
      have hprop : (P v).image (G.nbr v) = (toBicoloured G red rk h).proposers (dec G s) v :=
        proposers_dec h hs v
      change ((pstep G t s v).p).map (G.nbr v) = ((toBicoloured G red rk h).blueTurn (dec G s)).p v
      rw [hv]
      by_cases hr : red v = true
      · rw [ite_eq_left hr, Bicoloured.blueTurn_p_red _ _ (by exact hr)]; rfl
      · have hr' : red v = false := by simpa using hr
        rw [ite_eq_right hr]
        by_cases hP : (P v).Nonempty
        · have hP' : ((toBicoloured G red rk h).proposers (dec G s) v).Nonempty := by
            rw [← hprop]; exact hP.image _
          rw [ite_eq_left hP, Bicoloured.blueTurn_p_nonempty _ _ (by exact hr') hP', ← hprop,
            show (dec G s).p v = (s v).p.map (G.nbr v) from rfl, ← image_union_toFinset,
            ← pbest_map h (hPsub v)]
        · have hP' : ¬ ((toBicoloured G red rk h).proposers (dec G s) v).Nonempty := by
            rw [← hprop, Finset.image_nonempty]; exact hP
          rw [ite_eq_right hP, Bicoloured.blueTurn_p_empty _ _ hP']
          rfl

/-- A port-level pair `(C, p)` of node `v` decodes to the node-level pair `(C', p')`. -/
def DecPair (G : PNGraph V) (v : V) (a : Finset ℕ × Option ℕ) (b : Finset V × Option V) : Prop :=
  a.1 ⊆ range (G.deg v) ∧ (∀ i, a.2 = some i → i < G.deg v) ∧ a.1.image (G.nbr v) = b.1 ∧
    a.2.map (G.nbr v) = b.2

open Classical in
include h in
lemma acc_iff {s : V → NodeData} (hs : PInv G red rk s) {v : V} {i : ℕ} (hi : i < G.deg v) :
    (∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧ y.p = some j) ↔
      (dec G s).p (G.nbr v i) = some v := by
  rw [nbrInfo_of_lt hi]
  change _ ↔ ((s (G.nbr v i)).p).map _ = _
  rw [map_eq_some_iff h hi (hs.p _)]
  constructor
  · rintro ⟨y, j, he, hp⟩; cases he; exact hp
  · intro hp; exact ⟨_, _, rfl, hp⟩

open Classical in
include h in
lemma step1_dec {s : V → NodeData} (hs : PInv G red rk s) (v : V) :
    DecPair G v (pStep1 (s v) fun i => ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧
      y.p = some j) (Bicoloured.redStep1 (dec G s) v) := by
  unfold pStep1 Bicoloured.redStep1
  rcases hc : (s v).c with _ | i
  · have : (dec G s).c v = none := by simp [dec, hc]
    rw [this]
    exact ⟨hs.C v, hs.p v, rfl, rfl⟩
  · have hi := hs.c v i hc
    have : (dec G s).c v = some (G.nbr v i) := by simp [dec, hc]
    rw [this]
    simp only
    by_cases hacc : ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧ y.p = some j
    · rw [ite_eq_left hacc, ite_eq_left ((acc_iff h hs hi).1 hacc)]
      exact ⟨hs.C v, fun j hj => by cases hj; exact hi, rfl, rfl⟩
    · rw [ite_eq_right hacc, ite_eq_right (fun h' => hacc ((acc_iff h hs hi).2 h'))]
      exact ⟨(erase_subset _ _).trans (hs.C v), hs.p v, image_erase_nbr h (hs.C v) hi, rfl⟩

open Classical in
include h in
lemma step2_dec {s : V → NodeData} (hs : PInv G red rk s) (v : V) {a : Finset ℕ × Option ℕ}
    {b : Finset V × Option V} (hab : DecPair G v a b) :
    DecPair G v (pStep2 (fun i => ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧
      y.p = some j) a) (Bicoloured.redStep2 (dec G s) v b) := by
  obtain ⟨C, o⟩ := a
  obtain ⟨D, o'⟩ := b
  obtain ⟨hC, ho, hD, ho'⟩ := hab
  simp only at hC ho hD ho'
  subst hD ho'
  rcases o with _ | i
  · exact ⟨hC, fun _ hh => by simp [pStep2] at hh, rfl, rfl⟩
  · have hi := ho i rfl
    simp only [pStep2, Option.map_some, Bicoloured.redStep2]
    by_cases hacc : ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧ y.p = some j
    · rw [ite_eq_left hacc, ite_eq_left ((acc_iff h hs hi).1 hacc)]
      exact ⟨hC, fun j hj => by cases hj; exact hi, rfl, rfl⟩
    · rw [ite_eq_right hacc, ite_eq_right (fun h' => hacc ((acc_iff h hs hi).2 h'))]
      exact ⟨(erase_subset _ _).trans hC, fun _ hh => by simp at hh, image_erase_nbr h hC hi, rfl⟩

open Classical in
include h in
/-- A red turn of the port-level algorithm decodes to the red turn of §4. -/
lemma red_step {s : V → NodeData} (hs : PInv G red rk s) {t : ℕ} (ht : t % 2 = 1) :
    PInv G red rk (pstep G t s) ∧
      dec G (pstep G t s) = (toBicoloured G red rk h).redTurn (dec G s) := by
  set acc : V → ℕ → Prop := fun v i => ∃ y j, Algorithm.nbrInfo G s v i = some (y, j) ∧
    y.p = some j
  set r : V → Finset ℕ × Option ℕ := fun v => pStep2 (acc v) (pStep1 (s v) (acc v))
  have hv : ∀ v, pstep G t s v = if red v = true then redUpdate (s v) (r v) else s v := by
    intro v
    simp only [pstep, rule, ht, hs.red v, r, acc]
    simp
  have hdec : ∀ v, DecPair G v (r v) (Bicoloured.redStep2 (dec G s) v
      (Bicoloured.redStep1 (dec G s) v)) := fun v => step2_dec h hs v (step1_dec h hs v)
  refine ⟨⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩, ?_⟩
  · rw [hv]; split_ifs <;> simp [redUpdate, hs.red v]
  · rw [hv]; split_ifs <;> simp [redUpdate, hs.rk v]
  · rw [hv]; split_ifs
    · exact (hdec v).1
    · exact hs.C v
  · intro i hi; rw [hv] at hi; split_ifs at hi
    · simp only [redUpdate] at hi
      split_ifs at hi
      exact mem_range.1 ((hdec v).1 (pbest_spec hi).1)
    · exact hs.c v i hi
  · intro i hi; rw [hv] at hi; split_ifs at hi
    · exact (hdec v).2.1 i hi
    · exact hs.p v i hi
  · ext1 <;> funext v <;> by_cases hr : red v = true
    · change ((pstep G t s v).C).image (G.nbr v) = _
      rw [hv, ite_eq_left hr, ((toBicoloured G red rk h).redTurn_red _ (by exact hr)).1]
      exact (hdec v).2.2.1
    · have hr' : (toBicoloured G red rk h).red v = false := by
        have : red v = false := by simpa using hr
        exact this
      change ((pstep G t s v).C).image (G.nbr v) = _
      rw [hv, ite_eq_right hr, ((toBicoloured G red rk h).redTurn_blue _ hr').1]; rfl
    · change ((pstep G t s v).c).map (G.nbr v) = _
      rw [hv, ite_eq_left hr, ((toBicoloured G red rk h).redTurn_red _ (by exact hr)).2.1,
        ← (hdec v).2.2.2, ← (hdec v).2.2.1]
      by_cases h2 : (r v).2 = none
      · simp only [redUpdate, h2, Option.map_none, ↓reduceIte]
        rw [hs.rk v]; exact pbest_map h (hdec v).1
      · have h2' : (r v).2.map (G.nbr v) ≠ none := by simpa using h2
        simp only [redUpdate, h2, h2', ↓reduceIte, Option.map_none]
    · have hr' : (toBicoloured G red rk h).red v = false := by
        have : red v = false := by simpa using hr
        exact this
      change ((pstep G t s v).c).map (G.nbr v) = _
      rw [hv, ite_eq_right hr, ((toBicoloured G red rk h).redTurn_blue _ hr').2.1]; rfl
    · change ((pstep G t s v).p).map (G.nbr v) = _
      rw [hv, ite_eq_left hr, ((toBicoloured G red rk h).redTurn_red _ (by exact hr)).2.2]
      exact (hdec v).2.2.2
    · have hr' : (toBicoloured G red rk h).red v = false := by
        have : red v = false := by simpa using hr
        exact this
      change ((pstep G t s v).p).map (G.nbr v) = _
      rw [hv, ite_eq_right hr, ((toBicoloured G red rk h).redTurn_blue _ hr').2.2]; rfl

end Decode

/-! ### Correctness of the simulation -/

section Run

variable {G : PNGraph V} {red : V → Bool} {rk : V → ℕ → ℕ} (h : GoodInput G red rk)

/-- The initial port-level configuration. -/
def initConf (G : PNGraph V) (red : V → Bool) (rk : V → ℕ → ℕ) : V → NodeData :=
  fun v => initData (G.deg v) (red v, rk v)

include h in
/-- **Simulation.** After `2i` communication rounds (`i` blue and `i` red turns) the decoded
port-level configuration is the state `M_i`, `C_i`, `c_i` at the end of round `i` of §4. -/
theorem dec_localRun (i : ℕ) :
    PInv G red rk (Algorithm.localRun G rule (initConf G red rk) (2 * i)) ∧
      dec G (Algorithm.localRun G rule (initConf G red rk) (2 * i)) =
        (toBicoloured G red rk h).run i := by
  induction i with
  | zero =>
    refine ⟨⟨fun v => rfl, fun v => rfl, fun v => ?_, fun v i hi => by simp [initConf, initData] at hi,
      fun v i hi => by simp [initConf, initData] at hi⟩, ?_⟩
    · change (initConf G red rk v).C ⊆ range (G.deg v)
      simp only [initConf, initData]; split_ifs <;> simp
    · ext1 <;> funext v
      · simp only [Nat.mul_zero, Algorithm.localRun_zero, dec, initConf, initData,
          Bicoloured.run_zero, Bicoloured.init_C]
        change _ = if red v = true then _ else _
        split_ifs <;> simp [toBicoloured]
      · rfl
      · rfl
  | succ i ih =>
    obtain ⟨hP, hD⟩ := ih
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [e, localRun_succ_eq, localRun_succ_eq]
    obtain ⟨hP1, hD1⟩ := blue_step h hP (t := 2 * i) (by omega)
    obtain ⟨hP2, hD2⟩ := red_step h hP1 (t := 2 * i + 1) (by omega)
    refine ⟨hP2, ?_⟩
    rw [hD2, hD1, hD, Bicoloured.run_succ]
    rfl

include h in
/-- The output of `gsAlg (2i)` is the matching `M_i` (as ports). -/
theorem gsAlg_partner (i : ℕ) (v : V) :
    ((gsAlg (2 * i)).eval G (2 * i) (fun u => (red u, rk u)) v).map (G.nbr v) =
      ((toBicoloured G red rk h).run i).p v := by
  rw [gsAlg_eval, ← (dec_localRun h i).2]
  rfl

end Run

end Podc.TruncatedGaleShapley
