import Papers.PODC2019.HardnessOptimization.HamPathNec
import Papers.PODC2019.HardnessOptimization.HamPathSuff
import Papers.PODC2019.HardnessOptimization.HamPathWheel

/-!
# Theorem 2.2: deciding directed Hamiltonian path needs `Ω̃(n²)` CONGEST rounds

`k = 2 ^ (L + 1)`. The digraphs `D_{x,y}` (`dArc`) with the concrete wheel `hamWheel` satisfy
`D_{x,y}` has a directed Hamiltonian path `↔ DISJ(x, y) = FALSE` (`hamPath_iff`, Claims 2.1/2.2).

Communication network: the underlying undirected graph (`hamNet`); every node knows its out- and
in-arcs (`hamInp`). Partition: `V_A` = `start, s¹₁, s²₁`, the `A`-rows, all `g_c, r_c` and the
line vertices at positions `d < k/2`; `V_B` = the rest. The cut consists of `s²₁ – s¹₂` and, per
line `(c, q)`, of `σ^{k/2-1} – ℓ^{k/2}`, `β^{k/2-1} – ℓ^{k/2}`, `ℓ^{k/2-1} – β^{k/2}`,
`r_c – ℓ^{k-1}`, `g_{c+1} – σ^{k-1}`, `g_{c+1} – β^{k-1}` (`r_{2L-1}` instead of `g_{2L}`):
`|E_cut| ≤ 24 log k + 1` (`hamCut`).
-/

namespace HardnessOptimization.HamPath

open HV Finset Cslib.Congest Cslib.CommunicationComplexity

variable {L : ℕ}

/-- The arcs of `D_{x,y}` for `k = 2 ^ (L + 1)` (concrete wheel assignment). -/
def dArc (L : ℕ) (x y : Idx (L + 1) → Idx (L + 1) → Bool) : HV (L + 1) → HV (L + 1) → Prop :=
  Arc (hamWheel L) x y

instance (x y : Idx (L + 1) → Idx (L + 1) → Bool) : DecidableRel (dArc L x y) :=
  inferInstanceAs (DecidableRel (Arc _ _ _))

/-- **Claims 2.1 and 2.2.** `D_{x,y}` has a directed Hamiltonian path iff `DISJ(x, y) = FALSE`,
i.e. iff `x(i, j) = y(i, j) = 1` for some `(i, j)`. -/
theorem hamPath_iff (x y : Idx (L + 1) → Idx (L + 1) → Bool) :
    HasHamPath (dArc L x y) ↔ ∃ i j, x i j = true ∧ y i j = true :=
  ⟨claim_2_2 (Nat.succ_pos L) hamWheel_bit,
    claim_2_1 (Nat.succ_pos L) hamWheel_inj hamWheel_bit hamWheel_surj⟩

/-- The vertex set has `n = 6 + 4k + 2 log k (2 + 6k)` elements (`k = 2 ^ L`, `log k = L`). -/
lemma card_HV : Fintype.card (HV L) = 6 + 4 * 2 ^ L + 2 * L * (2 + 6 * 2 ^ L) := by
  let e : HV L ≃ Fin 6 ⊕ (Bool × Bool × Idx L) ⊕ (Fin (2 * L) × Bool) ⊕
      (Fin (2 * L) × Bool × Fin (2 ^ L) × Fin 3) :=
    { toFun := fun v => match v with
        | .start => .inl 0 | .stop => .inl 1 | .sA1 => .inl 2 | .sA2 => .inl 3
        | .sB1 => .inl 4 | .sB2 => .inl 5
        | .row s ℓ i => .inr (.inl (s, ℓ, i))
        | .g c => .inr (.inr (.inl (c, false))) | .r c => .inr (.inr (.inl (c, true)))
        | .la c q d => .inr (.inr (.inr (c, q, d, 0)))
        | .si c q d => .inr (.inr (.inr (c, q, d, 1)))
        | .be c q d => .inr (.inr (.inr (c, q, d, 2)))
      invFun := fun p => match p with
        | .inl k => ![.start, .stop, .sA1, .sA2, .sB1, .sB2] k
        | .inr (.inl (s, ℓ, i)) => .row s ℓ i
        | .inr (.inr (.inl (c, b))) => if b then .r c else .g c
        | .inr (.inr (.inr (c, q, d, k))) => ![.la c q d, .si c q d, .be c q d] k
      left_inv := fun v => by cases v <;> rfl
      right_inv := fun p => by
        rcases p with k | ⟨s, ℓ, i⟩ | ⟨c, b⟩ | ⟨c, q, d, k⟩
        · fin_cases k <;> rfl
        · rfl
        · cases b <;> rfl
        · fin_cases k <;> rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-! ### The family of lower bound graphs -/

/-- The communication network: the underlying undirected graph of `D_{x,y}` (inputs indexed by
pairs). -/
def hamNet (L : ℕ) (x y : Idx (L + 1) × Idx (L + 1) → Bool) : SimpleGraph (HV (L + 1)) :=
  SimpleGraph.fromRel (dArc L (fun i j => x (i, j)) (fun i j => y (i, j)))

instance (x y : Idx (L + 1) × Idx (L + 1) → Bool) : DecidableRel (hamNet L x y).Adj :=
  fun a b => decidable_of_iff _ (SimpleGraph.fromRel_adj _ a b).symm

/-- Node inputs: node `v` knows, for every `w`, whether `v → w` and whether `w → v` are arcs. -/
def hamInp (L : ℕ) (x y : Idx (L + 1) × Idx (L + 1) → Bool) (v : HV (L + 1)) :
    HV (L + 1) → Bool × Bool := fun w =>
  (decide (dArc L (fun i j => x (i, j)) (fun i j => y (i, j)) v w),
    decide (dArc L (fun i j => x (i, j)) (fun i j => y (i, j)) w v))

/-- Alice's part `V_A`. -/
def alice : HV (L + 1) → Bool
  | .start | .sA1 | .sA2 | .g _ | .r _ => true
  | .stop | .sB1 | .sB2 => false
  | .row s _ _ => !s
  | .la _ _ d | .si _ _ d | .be _ _ d => decide (d.val < 2 ^ L)

@[simp] lemma alice_la (c q d) : alice (L := L) (.la c q d) = decide (d.val < 2 ^ L) := rfl
@[simp] lemma alice_si (c q d) : alice (L := L) (.si c q d) = decide (d.val < 2 ^ L) := rfl
@[simp] lemma alice_be (c q d) : alice (L := L) (.be c q d) = decide (d.val < 2 ^ L) := rfl
@[simp] lemma alice_r (c) : alice (L := L) (.r c) = true := rfl

/-- Position `k/2 - 1`. -/
def pH1 (L : ℕ) : Fin (2 ^ (L + 1)) :=
  ⟨2 ^ L - 1, by rw [pow_succ]; have := Nat.two_pow_pos L; omega⟩
/-- Position `k/2`. -/
def pH (L : ℕ) : Fin (2 ^ (L + 1)) := ⟨2 ^ L, by rw [pow_succ]; have := Nat.two_pow_pos L; omega⟩
/-- Position `k - 1`. -/
def pK1 (L : ℕ) : Fin (2 ^ (L + 1)) := ⟨2 ^ (L + 1) - 1, by have := Nat.two_pow_pos (L + 1); omega⟩

/-- The forward target of the last position of box `c`: `g_{c+1}` or `r_{2L-1}`. -/
def fwdV (c : Fin (2 * (L + 1))) : HV (L + 1) :=
  if h : c.val + 1 < 2 * (L + 1) then .g ⟨c.val + 1, h⟩ else .r c

/-- The cut pairs `(a, b)`, `a ∈ V_A`, `b ∈ V_B`. -/
def cutPair : Option (Fin (2 * (L + 1)) × Bool × Fin 6) → HV (L + 1) × HV (L + 1)
  | none => (.sA2, .sB1)
  | some (c, q, k) =>
    ![(.si c q (pH1 L), .la c q (pH L)), (.be c q (pH1 L), .la c q (pH L)),
      (.la c q (pH1 L), .be c q (pH L)), (.r c, .la c q (pK1 L)),
      (fwdV c, .si c q (pK1 L)), (fwdV c, .be c q (pK1 L))] k

/-- `E_cut`. -/
def hamCut (L : ℕ) : Finset (HV (L + 1) × HV (L + 1)) := univ.image (cutPair (L := L))

lemma card_hamCut : (hamCut L).card ≤ 24 * (L + 1) + 1 := by
  refine (card_image_le).trans ?_
  simp [Fintype.card_option, Fintype.card_prod]
  ring_nf; omega

lemma mem_cut (o) : cutPair (L := L) o ∈ hamCut L := mem_image_of_mem _ (mem_univ _)

lemma alice_fwdV (c : Fin (2 * (L + 1))) : alice (fwdV c) = true := by
  unfold fwdV; split <;> rfl

lemma pow_succ' (L : ℕ) : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring

lemma hamCut_sub (p) (hp : p ∈ hamCut L) : alice p.1 = true ∧ alice p.2 = false := by
  obtain ⟨o, -, rfl⟩ := mem_image.1 hp
  have h1 := Nat.two_pow_pos L
  have h2 := pow_succ' L
  rcases o with _ | ⟨c, q, k⟩
  · simp [cutPair, alice]
  · fin_cases k <;> simp [cutPair, alice_fwdV, alice_la, alice_si, alice_be, alice_r, pH1, pH,
      pK1] <;> omega

lemma alice_wrow (c q d) : alice (wrow (hamWheel L) c q d) = decide (d.val < 2 ^ L) := by
  by_cases h : d.val < 2 ^ L
  · simp [wrow, alice, hamWheel_side, h]
  · simp [wrow, alice, hamWheel_side, h]; omega

/-- Every arc between `V_A` and `V_B` is a cut pair. -/
lemma cross {u v : HV (L + 1)} (h : baseArc (hamWheel L) u v) (hs : alice u ≠ alice v) :
    (u, v) ∈ hamCut L ∨ (v, u) ∈ hamCut L := by
  have h1 := Nat.two_pow_pos L
  have h2 := pow_succ' L
  cases u
  case start => obtain ⟨c, -, rfl⟩ := h; simp [alice] at hs
  case stop => exact h.elim
  case sA1 => obtain ⟨i, rfl⟩ := h; simp [alice] at hs
  case sA2 => subst h; exact Or.inl (mem_cut none)
  case sB1 => obtain ⟨i, rfl⟩ := h; simp [alice] at hs
  case sB2 => subst h; simp [alice] at hs
  case row s ℓ i =>
    rcases h with ⟨-, rfl⟩ | ⟨c, q, d, rfl, hw⟩
    · cases s <;> simp [alice] at hs
    · rw [← hw, alice_wrow] at hs; simp [alice] at hs
  case g c =>
    obtain ⟨q, d, hd, rfl⟩ := h; simp [alice] at hs; omega
  case r c =>
    obtain ⟨q, d, hd, rfl⟩ := h
    have : d = pK1 L := Fin.ext (by simp [pK1]; omega)
    subst this; exact Or.inl (mem_cut (some (c, q, 3)))
  case la c q d =>
    rcases h with rfl | rfl
    · simp [alice] at hs
    · rw [alice_wrow] at hs; simp [alice] at hs
  case si c q d =>
    rcases h with rfl | hf
    · simp [alice] at hs
    · cases v <;> simp only [IsFwd] at hf
      case la c' q' d' =>
        obtain ⟨rfl, rfl, hd⟩ := hf
        simp only [alice, ne_eq, decide_eq_decide] at hs
        have e1 : d = pH1 L := Fin.ext (by simp [pH1]; omega)
        have e2 : d' = pH L := Fin.ext (by simp [pH]; omega)
        subst e1 e2; exact Or.inl (mem_cut (some (_, _, 0)))
      case g c' =>
        obtain ⟨hd, hc⟩ := hf
        have e1 : d = pK1 L := Fin.ext (by simp [pK1]; omega)
        have e2 : HV.g c' = fwdV c := by
          have hlt : c.val + 1 < 2 * (L + 1) := by omega
          simp [fwdV, hlt, Fin.ext_iff, hc]
        subst e1; rw [e2]; exact Or.inr (mem_cut (some (c, q, 4)))
      case r c' =>
        obtain ⟨hd, hc, hcc⟩ := hf
        rw [hcc]
        have e1 : d = pK1 L := Fin.ext (by simp [pK1]; omega)
        have e2 : HV.r c = fwdV c := by
          have hlt : ¬ (c.val + 1 < 2 * (L + 1)) := by omega
          simp [fwdV, hlt]
        subst e1; rw [e2]; exact Or.inr (mem_cut (some (c, q, 4)))
  case be c q d =>
    rcases h with rfl | hf | hb
    · simp [alice] at hs
    · cases v <;> simp only [IsFwd] at hf
      case la c' q' d' =>
        obtain ⟨rfl, rfl, hd⟩ := hf
        simp only [alice, ne_eq, decide_eq_decide] at hs
        have e1 : d = pH1 L := Fin.ext (by simp [pH1]; omega)
        have e2 : d' = pH L := Fin.ext (by simp [pH]; omega)
        subst e1 e2; exact Or.inl (mem_cut (some (_, _, 1)))
      case g c' =>
        obtain ⟨hd, hc⟩ := hf
        have e1 : d = pK1 L := Fin.ext (by simp [pK1]; omega)
        have e2 : HV.g c' = fwdV c := by
          have hlt : c.val + 1 < 2 * (L + 1) := by omega
          simp [fwdV, hlt, Fin.ext_iff, hc]
        subst e1; rw [e2]; exact Or.inr (mem_cut (some (c, q, 5)))
      case r c' =>
        obtain ⟨hd, hc, hcc⟩ := hf
        rw [hcc]
        have e1 : d = pK1 L := Fin.ext (by simp [pK1]; omega)
        have e2 : HV.r c = fwdV c := by
          have hlt : ¬ (c.val + 1 < 2 * (L + 1)) := by omega
          simp [fwdV, hlt]
        subst e1; rw [e2]; exact Or.inr (mem_cut (some (c, q, 5)))
    · cases v <;> simp only [IsBwd] at hb
      case la c' q' d' =>
        obtain ⟨rfl, rfl, hd⟩ := hb
        simp only [alice, ne_eq, decide_eq_decide] at hs
        have e1 : d' = pH1 L := Fin.ext (by simp [pH1]; omega)
        have e2 : d = pH L := Fin.ext (by simp [pH]; omega)
        subst e1 e2; exact Or.inr (mem_cut (some (_, _, 2)))
      case r c' => obtain ⟨hd, -⟩ := hb; simp [alice, hd] at hs
      case sA1 => obtain ⟨hd, -⟩ := hb; simp [alice, hd] at hs

section Indep

variable {W : Wheel (L + 1)} {x x' y y' : Idx (L + 1) → Idx (L + 1) → Bool}

lemma arc_indep_y {u v : HV (L + 1)} (h : alice u = true ∨ alice v = true) :
    Arc W x y u v ↔ Arc W x y' u v := by
  unfold Arc
  constructor <;> rintro (h' | h' | h')
  all_goals first
    | exact Or.inl h'
    | exact Or.inr (Or.inl h')
    | (obtain ⟨i, j, rfl, rfl, -⟩ := h'; simp [alice] at h)

lemma arc_indep_x {u v : HV (L + 1)} (h : alice u = false ∨ alice v = false) :
    Arc W x y u v ↔ Arc W x' y u v := by
  unfold Arc
  constructor <;> rintro (h' | h' | h')
  all_goals first
    | exact Or.inl h'
    | exact Or.inr (Or.inr h')
    | (obtain ⟨i, j, rfl, rfl, -⟩ := h'; simp [alice] at h)

lemma arc_cross {u v : HV (L + 1)} (hs : alice u ≠ alice v) :
    Arc W x y u v ↔ baseArc W u v := by
  unfold Arc
  constructor
  · rintro (h' | h' | h')
    · exact h'
    · obtain ⟨i, j, rfl, rfl, -⟩ := h'; simp [alice] at hs
    · obtain ⟨i, j, rfl, rfl, -⟩ := h'; simp [alice] at hs
  · exact Or.inl

end Indep

/-- The directed Hamiltonian path graphs as a family of lower bound graphs (Definition 1.1). -/
def hamFamily (L : ℕ) :
    LBFamily (Idx (L + 1) × Idx (L + 1) → Bool) (Idx (L + 1) × Idx (L + 1) → Bool) (HV (L + 1))
      (HV (L + 1) → Bool × Bool) where
  G := hamNet L
  inp := hamInp L
  alice := alice
  Ecut := hamCut L
  Ecut_sub := hamCut_sub
  adj_cut x y a b ha hb hab := by
    rw [hamNet, SimpleGraph.fromRel_adj] at hab
    have hs : alice a ≠ alice b := by simp [ha, hb]
    rcases hab.2 with h | h
    · rcases cross ((arc_cross hs).1 h) hs with h' | h'
      · exact h'
      · simpa [ha] using (hamCut_sub _ h').2
    · rcases cross ((arc_cross hs.symm).1 h) hs.symm with h' | h'
      · simpa [ha] using (hamCut_sub _ h').2
      · exact h'
  adj_alice x y y' a b ha hb := by
    simp only [hamNet, SimpleGraph.fromRel_adj, dArc]
    rw [arc_indep_y (y' := fun i j => y' (i, j)) (Or.inl ha),
      arc_indep_y (y' := fun i j => y' (i, j)) (Or.inl hb)]
  adj_bob x x' y a b ha hb := by
    simp only [hamNet, SimpleGraph.fromRel_adj, dArc]
    rw [arc_indep_x (x' := fun i j => x' (i, j)) (Or.inl ha),
      arc_indep_x (x' := fun i j => x' (i, j)) (Or.inl hb)]
  adj_fixed x x' y y' a b ha hb := by
    have hs : alice a ≠ alice b := by simp [ha, hb]
    simp only [hamNet, SimpleGraph.fromRel_adj, dArc]
    rw [arc_cross hs, arc_cross hs.symm, arc_cross hs, arc_cross hs.symm]
  inp_alice x y y' v hv := by
    funext w
    simp only [hamInp, dArc, Prod.mk.injEq]
    exact ⟨decide_eq_decide.2 (arc_indep_y (Or.inl hv)), decide_eq_decide.2 (arc_indep_y (Or.inr hv))⟩
  inp_bob x x' y v hv := by
    funext w
    simp only [hamInp, dArc, Prod.mk.injEq]
    exact ⟨decide_eq_decide.2 (arc_indep_x (Or.inl hv)), decide_eq_decide.2 (arc_indep_x (Or.inr hv))⟩

instance (x y : Idx (L + 1) × Idx (L + 1) → Bool) : DecidableRel ((hamFamily L).G x y).Adj :=
  inferInstanceAs (DecidableRel (hamNet L x y).Adj)

/-- **Theorem 2.2** (deterministic, decision version). Let `k = 2 ^ (L + 1)`. If a deterministic
CONGEST algorithm with `B`-bit messages decides in `T` rounds, on every network `D_{x,y}` (nodes
know their incident arcs), whether the digraph has a directed Hamiltonian path (all nodes accept
iff it has one), then `k² ≤ 2 T (24 log k + 1) B + 2`. As `n = Θ(k log k)`, this is
`T = Ω(n² / (B log³ n)) = Ω(n² / log⁴ n)` for `B = Θ(log n)`. -/
theorem theorem_2_2 {σ : Type*} {B : ℕ}
    (A : Algorithm (HV (L + 1)) (HV (L + 1) → Bool × Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx (L + 1) × Idx (L + 1) → Bool,
      A.Accepts (hamNet L x y) (hamInp L x y) T ↔
        HasHamPath (dArc L (fun i j => x (i, j)) (fun i j => y (i, j)))) :
    4 ^ (L + 1) ≤ T * (2 * ((24 * (L + 1) + 1) * B)) + 2 := by
  have h := (hamFamily L).not_disj_lowerBound A T fun x y => by
    change A.Accepts (hamNet L x y) (hamInp L x y) T ↔ _
    rw [hA x y, hamPath_iff]
    simp [Protocol.disj]
  have hc : Fintype.card (Idx (L + 1) × Idx (L + 1)) = 4 ^ (L + 1) := by
    simp [Fintype.card_prod, ← mul_pow]
  rw [hc] at h
  refine h.trans ?_
  have : (hamFamily L).Ecut.card ≤ 24 * (L + 1) + 1 := card_hamCut
  gcongr

/-- **Theorem 2.2** in terms of `n = |V|`: `n² ≤ 441 log₂² n · (2 T (24 log₂ n + 1) B + 2)`,
i.e. `T = Ω(n² / (B log³ n)) = Ω(n² / log⁴ n)` for `B = Θ(log n)`. -/
theorem theorem_2_2_n {σ : Type*} {B : ℕ}
    (A : Algorithm (HV (L + 1)) (HV (L + 1) → Bool × Bool) σ B) (T : ℕ)
    (hA : ∀ x y : Idx (L + 1) × Idx (L + 1) → Bool,
      A.Accepts (hamNet L x y) (hamInp L x y) T ↔
        HasHamPath (dArc L (fun i j => x (i, j)) (fun i j => y (i, j)))) :
    Fintype.card (HV (L + 1)) ^ 2 ≤ 441 * Nat.log 2 (Fintype.card (HV (L + 1))) ^ 2 *
      (T * (2 * ((24 * Nat.log 2 (Fintype.card (HV (L + 1))) + 1) * B)) + 2) := by
  have h := theorem_2_2 A T hA
  rw [card_HV]
  set k := 2 ^ (L + 1) with hk
  set m := L + 1 with hm
  have hk2 : 2 ≤ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm1 : 1 ≤ m := by omega
  have hn : 6 + 4 * k + 2 * m * (2 + 6 * k) ≤ 21 * k * m := by nlinarith
  have hlog : m ≤ Nat.log 2 (6 + 4 * k + 2 * m * (2 + 6 * k)) :=
    Nat.le_log_of_pow_le (by norm_num) (by rw [hm, ← hk]; omega)
  have hk4 : k ^ 2 = 4 ^ m := by rw [hk, ← pow_mul, mul_comm, pow_mul]; norm_num
  calc (6 + 4 * k + 2 * m * (2 + 6 * k)) ^ 2 ≤ (21 * k * m) ^ 2 := Nat.pow_le_pow_left hn 2
    _ = 441 * m ^ 2 * k ^ 2 := by ring
    _ ≤ 441 * m ^ 2 * (T * (2 * ((24 * m + 1) * B)) + 2) := by rw [hk4]; gcongr
    _ ≤ _ := by gcongr

/-! ### Endpoints of Hamiltonian paths; the construction taken literally -/

section Endpoints

variable {V : Type*} [DecidableEq V] {R : V → V → Prop} {l : List V}

/-- A vertex without out-arcs is the last vertex of every Hamiltonian path. -/
lemma idxOf_of_no_out (hall : ∀ v, v ∈ l) (hc : l.IsChain R) {a : V} (ha : ∀ w, ¬ R a w) :
    l.idxOf a + 1 = l.length := by
  have hlt := List.idxOf_lt_length_iff.2 (hall a)
  by_contra hne
  have h1 : l.idxOf a + 1 < l.length := by omega
  have := List.isChain_iff_getElem.1 hc _ h1
  rw [List.getElem_idxOf hlt] at this
  exact ha _ this

/-- A vertex without in-arcs is the first vertex of every Hamiltonian path. -/
lemma idxOf_of_no_in (hall : ∀ v, v ∈ l) (hc : l.IsChain R) {a : V} (ha : ∀ w, ¬ R w a) :
    l.idxOf a = 0 := by
  have hlt := List.idxOf_lt_length_iff.2 (hall a)
  by_contra hne
  have h1 : l.idxOf a - 1 + 1 < l.length := by omega
  have := List.isChain_iff_getElem.1 hc _ h1
  have e : l[l.idxOf a - 1 + 1] = a := by
    simp only [show l.idxOf a - 1 + 1 = l.idxOf a by omega]
    exact List.getElem_idxOf hlt
  rw [e] at this
  exact ha _ this

/-- A digraph with two different vertices of out-degree `0` has no Hamiltonian path. -/
lemma eq_of_no_out (h : HasHamPath R) {a b : V} (ha : ∀ w, ¬ R a w) (hb : ∀ w, ¬ R b w) :
    a = b := by
  obtain ⟨l, -, hall, hc⟩ := h
  have := (idxOf_of_no_out hall hc ha).trans (idxOf_of_no_out hall hc hb).symm
  exact (List.idxOf_inj (hall a)).1 (by omega)

end Endpoints

/-- The paper's construction taken literally: the arcs `r_c → ℓ^{c,k-1}_q` (used in the proof of
Claim 2.1, never defined) are absent. -/
def paperArc {L : ℕ} (W : Wheel L) (x y : Idx L → Idx L → Bool) (u v : HV L) : Prop :=
  Arc W x y u v ∧ ∀ c, u ≠ .r c

/-- **Counterexample to the literal construction**: without the arcs out of `r_c`, both `end`
and `r_0` have out-degree `0`, so *no* `G_{x,y}` has a directed Hamiltonian path, and Claim 2.1
fails for every intersecting pair `x, y`. -/
theorem paperArc_not_hamPath {L : ℕ} (hL : 0 < L) (W : Wheel L) (x y : Idx L → Idx L → Bool) :
    ¬ HasHamPath (paperArc W x y) := fun h => by
  have := eq_of_no_out h (a := .stop) (b := .r ⟨0, by omega⟩)
    (fun w hw => not_arc_from_stop _ hw.1) (fun w hw => hw.2 _ rfl)
  simp at this

end HardnessOptimization.HamPath
