import Papers.PODC2012.WeakModelsModalLogic.SetSim
import Papers.PODC2012.WeakModelsModalLogic.Lemma15

/-!
# Separations `VB ≠ SV` and `SB ≠ MB`: Theorems 11 and 13 (§5.3 of Hella et al.)

* Theorem 11 (`theorem11`): selecting one leaf of a star is in `SV(1)` but not in `VB`.
* Theorem 13 (`theorem13`): marking the nodes with an odd number of odd-degree neighbours is in
  `MB(1)` but not in `SB`; the witness is the 23-node graph of the paper's figure (two components
  with centres `0` and `11`).
-/

namespace Podc.WeakModelsModalLogic

open Function Finset

/-! ### Theorem 11 -/

section Star

variable {V : Type}

/-- `G` is a `k`-star with `k > 1` and centre `c`: every edge contains `c`, `c` is adjacent to all
other nodes, and there are at least two other nodes. -/
def IsStarCentre (G : SimpleGraph V) (c : V) : Prop :=
  (∀ v, v ≠ c → G.Adj c v) ∧ (∀ u v, G.Adj u v → u = c ∨ v = c) ∧
    ∃ v₁ v₂, v₁ ≠ c ∧ v₂ ≠ c ∧ v₁ ≠ v₂

/-- The problem of Theorem 11: in a `k`-star (`k > 1`) the centre outputs `0` and exactly one leaf
outputs `1`; on all other graphs every output is allowed. -/
def starProblem : GraphProblem Bool := fun _ G =>
  {S | ∀ c, IsStarCentre G c → S c = false ∧ ∃ j, j ≠ c ∧ S j = true ∧
    ∀ i, i ≠ c → i ≠ j → S i = false}

open Classical in
/-- The `Set` algorithm of Theorem 11: send `i + 1` to port `i`; output `1` iff the degree is `1`
and message `1` was received. -/
noncomputable abbrev starMachine (Δ : ℕ) : Machine Δ Bool where
  Z := ℕ
  M := ℕ
  m0 := 0
  z0 d := .inr d
  μ _ i := i + 1
  δ d a := .inl (decide (d = 1 ∧ 1 ∈ Set.range a))

theorem starMachine_isSet (Δ : ℕ) : (starMachine Δ).IsSet := by
  intro z a b h
  simp only [starMachine, h]

open Classical in
theorem starMachine_state_one {G : SimpleGraph V} (P : PortNumbering G) (Δ : ℕ) (v : V) :
    (starMachine Δ).state G P 1 v = .inl (decide (deg G v = 1 ∧
      1 ∈ Set.range ((starMachine Δ).recv G P ((starMachine Δ).state G P 0) v))) := rfl

variable [Finite V]

theorem IsStarCentre.deg_leaf {G : SimpleGraph V} {c v : V} (h : IsStarCentre G c) (hv : v ≠ c) :
    deg G v = 1 := by
  have : G.neighborSet v = {c} := by
    ext u
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    constructor
    · intro hu
      rcases h.2.1 v u hu with h1 | h1
      · exact absurd h1 hv
      · exact h1
    · rintro rfl; exact (h.1 v hv).symm
  rw [deg, this, Nat.card_unique]

theorem IsStarCentre.two_le_deg {G : SimpleGraph V} {c : V} (h : IsStarCentre G c) :
    2 ≤ deg G c := by
  classical
  obtain ⟨v₁, v₂, h1, h2, h12⟩ := h.2.2
  have := PortNumbering.card_le_deg (G := G) {v₁, v₂} (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h.1 _ h1
    · rw [Finset.mem_singleton.1 hx]; exact h.1 _ h2)
  rwa [Finset.card_pair h12] at this

open Classical in
/-- The star algorithm is correct: in a `k`-star exactly the leaf behind out-port `0` of the
centre outputs `1`. -/
theorem starMachine_correct {G : SimpleGraph V} (P : PortNumbering G) (Δ : ℕ)
    (hG : MaxDegLE G Δ) :
    ∃ S, (starMachine Δ).StopsWith G P 1 S ∧ S ∈ starProblem G := by
  classical
  refine ⟨fun v => decide (deg G v = 1 ∧
    1 ∈ Set.range ((starMachine Δ).recv G P ((starMachine Δ).state G P 0) v)),
    fun v => starMachine_state_one P Δ v, ?_⟩
  intro c hc
  have hdc := hc.two_le_deg
  -- the leaf `v` receives `π(c, v) + 1`
  have hrecv : ∀ v, v ≠ c →
      (1 ∈ Set.range ((starMachine Δ).recv G P ((starMachine Δ).state G P 0) v) ↔
        P.outPort c v = 0) := by
    intro v hv
    have hdv := hc.deg_leaf hv
    have h0 : 0 < Δ := by have := hG v; omega
    constructor
    · rintro ⟨i, hi⟩
      by_cases hi' : (i : ℕ) < deg G v
      · rw [Machine.recv_apply_lt P _ _ v i hi'] at hi
        have hn : P.inNbr v ⟨i, hi'⟩ = c := by
          rcases hc.2.1 _ _ (P.adj_inNbr v ⟨i, hi'⟩) with h | h
          · exact absurd h hv
          · exact h
        rw [hn] at hi
        change P.outPort c v + 1 = 1 at hi
        omega
      · rw [Machine.recv_eq_m0 _ P _ i hi'] at hi
        exact absurd hi (show (0 : ℕ) ≠ 1 by decide)
    · intro h
      have hi' : ((⟨0, h0⟩ : Fin Δ) : ℕ) < deg G v := by simp [hdv]
      refine ⟨⟨0, h0⟩, ?_⟩
      rw [Machine.recv_apply_lt P _ _ v _ hi']
      have hn : P.inNbr v ⟨0, hi'⟩ = c := by
        rcases hc.2.1 _ _ (P.adj_inNbr v ⟨0, hi'⟩) with h | h
        · exact absurd h hv
        · exact h
      rw [hn]
      change P.outPort c v + 1 = 1
      omega
  refine ⟨by simp; omega, P.outNbr c ⟨0, by omega⟩, ?_, ?_, ?_⟩
  · exact (P.adj_outNbr c _).ne.symm
  · have hj : P.outNbr c ⟨0, by omega⟩ ≠ c := (P.adj_outNbr c _).ne.symm
    simp only [decide_eq_true_eq]
    refine ⟨hc.deg_leaf hj, (hrecv _ hj).2 ?_⟩
    rw [P.outPort_outNbr]
  · intro i hi hij
    simp only [decide_eq_false_iff_not, not_and]
    intro _ hmem
    apply hij
    have h0 := (hrecv i hi).1 hmem
    have := P.outNbr_outPort (hc.1 i hi)
    rw [← this]
    congr 1
    exact Fin.ext h0

/-- The star problem is in `SV(1)`. -/
theorem starProblem_mem_SV1 : starProblem ∈ SV1 Bool :=
  ⟨fun Δ => starMachine Δ, fun _ => 1, fun Δ => starMachine_isSet Δ,
    fun Δ _ _ _ hG P => starMachine_correct P Δ hG⟩

end Star

/-- The 2-star on `Fin 3` with centre `0`. -/
def star3 : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel star3.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (u = 0 ∨ v = 0)))

theorem star3_isStarCentre : IsStarCentre star3 0 := by
  refine ⟨?_, ?_, 1, 2, by decide, by decide, by decide⟩ <;> decide

theorem star3_deg (v : Fin 3) : deg star3 v = if v = 0 then 2 else 1 := by
  rw [deg_eq_card_filter]; revert v; decide

theorem star3_maxDeg : MaxDegLE star3 2 := by
  intro v; rw [star3_deg]; split <;> omega

/-- In the star, all leaves are bisimilar in `K_{+,-}(G, p)`, for every port numbering. -/
theorem star3_bisimPM (P : PortNumbering star3) (u v : Fin 3) (hu : u ≠ 0) (hv : v ≠ 0) :
    P.BisimilarPM u v := by
  refine ⟨fun a b => (a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b ≠ 0), ?_, Or.inr ⟨hu, hv⟩⟩
  -- every neighbour of a leaf is the centre
  have hleaf : ∀ a w, a ≠ 0 → star3.Adj a w → w = 0 := by decide
  have hdeg : ∀ a b : Fin 3, ((a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b ≠ 0)) → deg star3 a = deg star3 b := by
    intro a b h; rw [star3_deg, star3_deg]; rcases h with ⟨rfl, rfl⟩ | ⟨ha, hb⟩ <;> simp [*]
  -- the in-port `i` of `b` exists whenever it exists at `a`
  have hstep : ∀ a b : Fin 3, ((a = 0 ∧ b = 0) ∨ (a ≠ 0 ∧ b ≠ 0)) →
      ∀ i w, P.Rin i a w → ∃ w', P.Rin i b w' ∧ ((w = 0 ∧ w' = 0) ∨ (w ≠ 0 ∧ w' ≠ 0)) := by
    intro a b hab i w ⟨j, hR⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨ha, hb⟩
    · exact ⟨w, ⟨j, hR⟩, by tauto⟩
    · obtain ⟨hi, -, -⟩ := (P.R_iff _ _ _ _).1 hR
      have hi' : i < deg star3 b := hdeg a b (Or.inr ⟨ha, hb⟩) ▸ hi
      refine ⟨_, ⟨_, P.R_symm_apply b i hi'⟩, Or.inl ⟨hleaf a w ha (P.R_adj hR), ?_⟩⟩
      exact hleaf b _ hb (P.adj_inNbr b ⟨i, hi'⟩)
  intro a b hab
  refine ⟨hdeg a b hab, hstep a b hab, fun i w' hw' => ?_⟩
  have hba : (b = 0 ∧ a = 0) ∨ (b ≠ 0 ∧ a ≠ 0) := by tauto
  obtain ⟨w, hw, hww⟩ := hstep b a hba i w' hw'
  exact ⟨w, hw, by tauto⟩

/-- The star problem is not in `VB` (Corollary 3(b) with `X` = the leaves of `star3`). -/
theorem starProblem_not_mem_VB : starProblem ∉ VB Bool := by
  obtain ⟨P⟩ := exists_portNumbering star3
  refine cor3b star3 2 star3_maxDeg {v | v ≠ 0} starProblem ?_ P
    (fun u hu v hv => star3_bisimPM P u v hu hv)
  intro S hS
  obtain ⟨-, j, hj0, hj, hother⟩ := hS 0 star3_isStarCentre
  -- the other leaf outputs `0`
  obtain ⟨k, hk0, hkj⟩ : ∃ k : Fin 3, k ≠ 0 ∧ k ≠ j := by
    by_cases h : j = 1
    · exact ⟨2, by decide, by rw [h]; decide⟩
    · exact ⟨1, by decide, fun h' => h h'.symm⟩
  exact ⟨j, hj0, k, hk0, by rw [hj, hother k hk0 hkj]; decide⟩

/-- Theorem 11 of [Hella et al.]: there is a graph problem in `SV(1)` that is not in `VB`. -/
theorem theorem11 : ∃ Pr : GraphProblem Bool, Pr ∈ SV1 Bool ∧ Pr ∉ VB Bool :=
  ⟨starProblem, starProblem_mem_SV1, starProblem_not_mem_VB⟩

/-- Corollary 12 of [Hella et al.]: `VB ≠ SV` and `VB(1) ≠ SV(1)`. -/
theorem cor12 : VB Bool ≠ SV Bool ∧ VB1 Bool ≠ SV1 Bool := by
  refine ⟨fun h => starProblem_not_mem_VB ?_, fun h => starProblem_not_mem_VB ?_⟩
  · rw [h]; exact SV1_subset_SV starProblem_mem_SV1
  · exact VB1_subset_VB (h ▸ starProblem_mem_SV1)

/-! ### Theorem 13 -/

section Parity

variable {V : Type}

/-- The number of neighbours of `v` that have an odd degree. -/
noncomputable def oddNbrs (G : SimpleGraph V) (v : V) : ℕ := {u | G.Adj v u ∧ Odd (deg G u)}.ncard

/-- The problem of Theorem 13: `S(v) = 1` iff `v` has an odd number of neighbours of odd
degree. -/
def parityProblem : GraphProblem Bool := fun _ G => {S | ∀ v, S v = true ↔ Odd (oddNbrs G v)}

open Classical in
/-- The `Multiset ∩ Broadcast` algorithm of Theorem 13: broadcast the parity of the degree
(`1` = odd, `2` = even), output `1` iff an odd number of messages `1` was received. -/
noncomputable abbrev parityMachine (Δ : ℕ) : Machine Δ Bool where
  Z := ℕ
  M := ℕ
  m0 := 0
  z0 d := .inr d
  μ d _ := if Odd d then 1 else 2
  δ _ a := .inl (decide (Odd (Multiset.count 1 (Multiset.map a univ.val))))

theorem parityMachine_isMultiset (Δ : ℕ) : (parityMachine Δ).IsMultiset := by
  intro z a b h
  simp only [parityMachine, h]

theorem parityMachine_isBroadcast (Δ : ℕ) : (parityMachine Δ).IsBroadcast :=
  fun _ _ _ _ _ => rfl

variable [Finite V]

theorem parityMachine_count {G : SimpleGraph V} (P : PortNumbering G) {Δ : ℕ}
    (hG : MaxDegLE G Δ) (v : V) :
    Multiset.count 1 (Multiset.map ((parityMachine Δ).recv G P ((parityMachine Δ).state G P 0) v)
      univ.val) = oddNbrs G v := by
  classical
  set r := (parityMachine Δ).recv G P ((parityMachine Δ).state G P 0) v with hrdef
  have hr : ∀ i : Fin Δ, (1 = r i) ↔
      ∃ h : (i : ℕ) < deg G v, Odd (deg G (P.inNbr v ⟨i, h⟩)) := by
    intro i
    by_cases hi : (i : ℕ) < deg G v
    · rw [hrdef, Machine.recv_apply_lt P _ _ v i hi]
      change 1 = (if Odd (deg G (P.inNbr v ⟨i, hi⟩)) then 1 else 2) ↔ _
      constructor
      · intro h; refine ⟨hi, ?_⟩; by_contra ho; simp [ho] at h
      · rintro ⟨_, ho⟩; rw [if_pos ho]
    · rw [hrdef, Machine.recv_eq_m0 _ P _ i hi]
      constructor
      · intro h; exact absurd h (show (1 : ℕ) ≠ 0 by decide)
      · rintro ⟨h, _⟩; exact absurd h hi
  rw [Multiset.count_map]
  change (univ.filter (fun i => 1 = r i)).card = _
  let f : Fin Δ → V := fun i => if h : (i : ℕ) < deg G v then P.inNbr v ⟨i, h⟩ else v
  have himg : {u | G.Adj v u ∧ Odd (deg G u)} = ↑((univ.filter (fun i => 1 = r i)).image f) := by
    ext u
    simp only [Set.mem_ofPred_eq, coe_image, coe_filter, mem_univ, true_and, Set.mem_image]
    constructor
    · rintro ⟨hu, ho⟩
      obtain ⟨k, rfl⟩ := P.inNbr_surj v u hu
      refine ⟨⟨k, lt_of_lt_of_le k.2 (hG v)⟩, (hr _).2 ⟨k.2, ho⟩, ?_⟩
      simp [f, k.2]
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨h, ho⟩ := (hr i).1 hi
      simp only [f, dif_pos h]
      exact ⟨P.adj_inNbr v _, ho⟩
  rw [oddNbrs, himg, Set.ncard_coe_finset, card_image_of_injOn]
  intro i hi j hj hij
  obtain ⟨h1, -⟩ := (hr i).1 (by simpa using hi)
  obtain ⟨h2, -⟩ := (hr j).1 (by simpa using hj)
  simp only [f, dif_pos h1, dif_pos h2] at hij
  have := P.injective_inNbr v hij
  exact Fin.ext (by simpa using congrArg Fin.val this)

open Classical in
theorem parityMachine_correct {G : SimpleGraph V} (P : PortNumbering G) (Δ : ℕ)
    (hG : MaxDegLE G Δ) :
    ∃ S, (parityMachine Δ).StopsWith G P 1 S ∧ S ∈ parityProblem G := by
  refine ⟨fun v => decide (Odd (Multiset.count 1 (Multiset.map
    ((parityMachine Δ).recv G P ((parityMachine Δ).state G P 0) v) univ.val))),
    fun v => rfl, fun v => ?_⟩
  rw [decide_eq_true_iff, parityMachine_count P hG]

/-- The parity problem is in `MB(1)`. -/
theorem parityProblem_mem_MB1 : parityProblem ∈ MB1 Bool :=
  ⟨fun Δ => parityMachine Δ, fun _ => 1,
    fun Δ => ⟨parityMachine_isMultiset Δ, parityMachine_isBroadcast Δ⟩,
    fun Δ _ _ _ hG P => parityMachine_correct P Δ hG⟩

end Parity

/-- The edges of the graph in the proof of Theorem 13 (two components, centres `0` and `11`):
left: centre `0`, squares `1, 2` with leaves `3, 4` and `5, 6`, diamonds `7, 8` with leaves `9`,
`10`; right: centre `11`, squares `12, 13, 14` with leaves `15, 16`, `17, 18`, `19, 20`, diamond
`21` with leaf `22`. -/
def g13Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (0, 7), (0, 8), (7, 9), (8, 10),
   (11, 12), (11, 13), (11, 14), (12, 15), (12, 16), (13, 17), (13, 18), (14, 19), (14, 20),
   (11, 21), (21, 22)]

/-- The graph of Theorem 13. -/
def g13 : SimpleGraph (Fin 23) where
  Adj u v := (u.val, v.val) ∈ g13Edges ∨ (v.val, u.val) ∈ g13Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel g13.Adj := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ g13Edges ∨ (v.val, u.val) ∈ g13Edges))

/-- The five bisimilarity classes of the figure: white, square, diamond, blue leaf, red leaf. -/
def g13Kind (v : Fin 23) : ℕ :=
  if v.val = 0 ∨ v.val = 11 then 0
  else if v.val ∈ [1, 2, 12, 13, 14] then 1
  else if v.val ∈ [7, 8, 21] then 2
  else if v.val ∈ [9, 10, 22] then 4
  else 3

theorem g13_maxDeg : MaxDegLE g13 4 := by
  intro v; rw [deg_eq_card_filter]; revert v; decide

theorem g13_bisim : IsBisimMM g13 (fun a b => g13Kind a = g13Kind b) := by
  unfold IsBisimMM
  simp only [deg_eq_card_filter]
  decide

theorem g13_oddNbrs : oddNbrs g13 0 = 2 ∧ oddNbrs g13 11 = 3 := by
  simp only [oddNbrs, deg_eq_card_filter, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  decide

/-- The parity problem is not in `SB` (Corollary 3(c): the two white nodes are bisimilar in
`K_{-,-}` but must produce different outputs). -/
theorem parityProblem_not_mem_SB : parityProblem ∉ SB Bool := by
  obtain ⟨P⟩ := exists_portNumbering g13
  refine cor3c g13 4 g13_maxDeg {0, 11} parityProblem ?_ P ?_
  · intro S hS
    refine ⟨0, by simp, 11, by simp, fun h => ?_⟩
    have h0 := hS 0
    have h11 := hS 11
    rw [g13_oddNbrs.1] at h0
    rw [g13_oddNbrs.2] at h11
    have : S 11 = true := h11.2 (by decide)
    have : S 0 = true := h ▸ this
    exact absurd (h0.1 this) (by decide)
  · intro u hu v hv
    refine ⟨_, g13_bisim, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

/-- Theorem 13 of [Hella et al.]: there is a graph problem in `MB(1)` that is not in `SB`. -/
theorem theorem13 : ∃ Pr : GraphProblem Bool, Pr ∈ MB1 Bool ∧ Pr ∉ SB Bool :=
  ⟨parityProblem, parityProblem_mem_MB1, parityProblem_not_mem_SB⟩

/-- Corollary 14 of [Hella et al.]: `SB ≠ MB` and `SB(1) ≠ MB(1)`. -/
theorem cor14 : SB Bool ≠ MB Bool ∧ SB1 Bool ≠ MB1 Bool := by
  refine ⟨fun h => parityProblem_not_mem_SB ?_, fun h => parityProblem_not_mem_SB ?_⟩
  · rw [h]; exact MB1_subset_MB parityProblem_mem_MB1
  · exact SB1_subset_SB (h ▸ parityProblem_mem_MB1)

end Podc.WeakModelsModalLogic
