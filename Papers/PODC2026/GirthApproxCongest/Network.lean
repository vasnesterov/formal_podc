import Papers.PODC2026.GirthApproxCongest.Gadget

/-!
# The communication network: small diameter and the moving cut

* `ediam_le`: thanks to the shortcut tree, the underlying network of `G_{x,y}` has diameter at
  most `2(d + 1)` (`d = ⌈log₂ q⌉` gives `O(log n)`).
* `gadgetFamily`: the network with any node inputs that only depend on the incident arcs is a
  `Cslib.Congest.MovingCutFamily` for `T` rounds when `2T + 2 ≤ q`. Alice knows a node of column
  `c` (tree nodes: leftmost leaf `c`, padding: `0`) at time `t` iff `c ≤ q - 2 - t`, Bob iff
  `c ≥ t + 1`. Only tree arcs from a child to its parent (Alice) or from a parent to its child
  (Bob) cross the moving boundary, at most one per tree level (`card_toA_le`, `card_toB_le`):
  this is the simulation of Das Sarma et al. (Lemma 4.1 of [9] in the paper) for our network.
-/

namespace Podc.GirthApproxCongest

open Finset Podc.MinWeightCycleCongest Cslib.Congest Vtx TNode

variable {L R : Type*} [DecidableEq L] [DecidableEq R] {q d p : ℕ} {E : Finset (L × R)}
  {V : Type*} (e : V ≃ Vtx L R q d p)

/-! ### Distance to the root -/

section Diam

variable {G : SimpleGraph V} {x y : E → Bool}
  (hG : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (darc E x y (e a) (e b) ∨ darc E x y (e b) (e a)))
include hG

omit [DecidableEq L] [DecidableEq R] in
lemma adj_of_darc {a b : Vtx L R q d p} (h : darc E x y a b) : G.Adj (e.symm a) (e.symm b) := by
  rw [hG]
  refine ⟨fun h' => not_darc_self x y a ?_, Or.inl (by simpa using h)⟩
  have := congrArg e h'
  simp only [Equiv.apply_symm_apply] at this
  rwa [this] at h ⊢

omit [DecidableEq L] [DecidableEq R] in
lemma edist_tree_root (hqd : q ≤ 2 ^ d) (hq : 0 < q) :
    ∀ n (z : TNode q d), d - z.h = n →
      G.edist (e.symm (.t z)) (e.symm (.t (root hq))) ≤ n := by
  intro n
  induction n with
  | zero =>
    intro z hz
    rw [eq_root hqd hq z (by have := z.h_le; omega)]
    simp
  | succ n ih =>
    intro z hz
    have hzd : z.h < d := by omega
    have h1 := ih (z.parent hzd) (by simp only [parent_h]; omega)
    have hadj : G.Adj (e.symm (.t (z.parent hzd))) (e.symm (.t z)) :=
      adj_of_darc e hG (by simpa [darc] using child_parent z hzd)
    calc G.edist (e.symm (.t z)) (e.symm (.t (root hq)))
        ≤ G.edist (e.symm (.t z)) (e.symm (.t (z.parent hzd))) +
          G.edist (e.symm (.t (z.parent hzd))) (e.symm (.t (root hq))) :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + n := by
          gcongr
          rw [SimpleGraph.edist_comm]
          exact (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le
      _ = (n + 1 : ℕ) := by push_cast; ring

omit [DecidableEq L] [DecidableEq R] in
lemma edist_root (hqd : q ≤ 2 ^ d) (hq : 0 < q) (v : V) :
    G.edist v (e.symm (.t (root hq))) ≤ d + 1 := by
  have hv : v = e.symm (e v) := by simp
  rw [hv]
  generalize e v = a
  have hroot := edist_tree_root e hG hqd hq
  cases a with
  | t z => exact (hroot _ z rfl).trans (by norm_cast; omega)
  | pad i =>
    have hadj : G.Adj (e.symm (.t (root hq))) (e.symm (.pad i)) :=
      adj_of_darc e hG (by simp [darc])
    rw [SimpleGraph.edist_comm]
    refine (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le.trans ?_
    norm_cast; omega
  | l u c =>
    have hadj : G.Adj (e.symm (.l u c)) (e.symm (.t (leaf c))) :=
      adj_of_darc e hG (by simp [darc, leaf])
    calc G.edist (e.symm (.l u c)) (e.symm (.t (root hq)))
        ≤ G.edist (e.symm (.l u c)) (e.symm (.t (leaf c))) +
          G.edist (e.symm (.t (leaf c))) (e.symm (.t (root hq))) := SimpleGraph.edist_triangle
      _ ≤ 1 + d := by
          gcongr
          · exact (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le
          · exact hroot _ (leaf c) (by simp [leaf])
      _ = d + 1 := add_comm _ _
  | r w c =>
    have hadj : G.Adj (e.symm (.r w c)) (e.symm (.t (leaf c))) :=
      adj_of_darc e hG (by simp [darc, leaf])
    calc G.edist (e.symm (.r w c)) (e.symm (.t (root hq)))
        ≤ G.edist (e.symm (.r w c)) (e.symm (.t (leaf c))) +
          G.edist (e.symm (.t (leaf c))) (e.symm (.t (root hq))) := SimpleGraph.edist_triangle
      _ ≤ 1 + d := by
          gcongr
          · exact (SimpleGraph.edist_eq_one_iff_adj.2 hadj).le
          · exact hroot _ (leaf c) (by simp [leaf])
      _ = d + 1 := add_comm _ _

omit [DecidableEq L] [DecidableEq R] in
/-- **Small diameter.** With `q ≤ 2^d`, every vertex is within distance `d + 1` of the root of
the shortcut tree, so the network has diameter at most `2(d + 1)`. -/
theorem ediam_le (hqd : q ≤ 2 ^ d) (hq : 0 < q) : G.ediam ≤ 2 * (d + 1) := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  calc G.edist u v ≤ G.edist u (e.symm (.t (root hq))) + G.edist (e.symm (.t (root hq))) v :=
        SimpleGraph.edist_triangle
    _ ≤ (d + 1) + (d + 1) := by
        gcongr
        · exact edist_root e hG hqd hq u
        · rw [SimpleGraph.edist_comm]; exact edist_root e hG hqd hq v
    _ = 2 * (d + 1) := by ring

end Diam

/-! ### The moving cut -/

/-- Alice's knowledge horizon for a `T`-round simulation: column `≤ q - 2 - t` at time `t`. -/
def kaV (T : ℕ) (v : Vtx L R q d p) : ℕ := min (q - 1 - v.col) (T + 1)

/-- Bob's knowledge horizon: column `≥ t + 1` at time `t`. -/
def kbV (T : ℕ) (v : Vtx L R q d p) : ℕ := min v.col (T + 1)

/-- `a` is a child of `b` in the shortcut tree. -/
def IsChildOf : Vtx L R q d p → Vtx L R q d p → Prop
  | .t z', .t z => Child z' z
  | _, _ => False

instance : DecidableRel (IsChildOf (L := L) (R := R) (q := q) (d := d) (p := p)) := fun a b => by
  cases a <;> cases b <;> unfold IsChildOf <;> infer_instance

/-- Level of a tree node (`0` for other vertices). -/
def lvl : Vtx L R q d p → Fin (d + 1)
  | .t z => z.1.1
  | _ => 0

variable [Fintype V]

/-- Arcs `(w, v)` (child `w`, parent `v`) whose round-`t` messages Bob sends to Alice. -/
def toAV (T t : ℕ) : Finset (V × V) :=
  univ.filter fun pr => IsChildOf (e pr.1) (e pr.2) ∧ t + 1 < kaV T (e pr.2) ∧ kaV T (e pr.1) ≤ t

/-- Arcs `(w, v)` (parent `w`, child `v`) whose round-`t` messages Alice sends to Bob. -/
def toBV (T t : ℕ) : Finset (V × V) :=
  univ.filter fun pr => IsChildOf (e pr.2) (e pr.1) ∧ t + 1 < kbV T (e pr.2) ∧ kbV T (e pr.1) ≤ t

omit [DecidableEq L] [DecidableEq R] in
lemma mem_toAV {T t : ℕ} {pr : V × V} : pr ∈ toAV e T t ↔
    IsChildOf (e pr.1) (e pr.2) ∧ t + 1 < kaV T (e pr.2) ∧ kaV T (e pr.1) ≤ t := by
  unfold toAV; rw [mem_filter]; simp

omit [DecidableEq L] [DecidableEq R] in
lemma mem_toBV {T t : ℕ} {pr : V × V} : pr ∈ toBV e T t ↔
    IsChildOf (e pr.2) (e pr.1) ∧ t + 1 < kbV T (e pr.2) ∧ kbV T (e pr.1) ≤ t := by
  unfold toBV; rw [mem_filter]; simp

omit [DecidableEq L] [DecidableEq R] in
/-- A child `z'` of `z` with `z.c ≤ X < z'.c` is determined by `X` and the level of `z`. -/
lemma TNode.Child.determined {z' z : TNode q d} (h : Child z' z) {X : ℕ} (h1 : z.c ≤ X)
    (h2 : X < z'.c) : z.c = X / 2 ^ z.h * 2 ^ z.h ∧ z'.c = z.c + 2 ^ z'.h := by
  have hlt := h.lt
  have hH : z.h = z'.h + 1 := h.1.symm
  set m := 2 ^ z'.h with hm
  have hm0 : 0 < m := by positivity
  have h2H : 2 ^ z.h = 2 * m := by rw [hH, pow_succ]; ring
  obtain ⟨b, hb⟩ : m ∣ z'.c := z'.2
  have hza0 : z.c = (z'.c / (2 * m)) * (2 * m) := by rw [h.2, h2H]
  obtain ⟨a, ha⟩ : ∃ a, z'.c / (2 * m) = a := ⟨_, rfl⟩
  rw [ha] at hza0
  have hza := hza0
  rw [h2H] at hlt ⊢
  have hXa : X / (2 * m) = a := by
    apply Nat.div_eq_of_lt_le
    · rw [← hza]; exact h1
    · rw [Nat.succ_mul, ← hza]; omega
  refine ⟨by rw [hXa, hza], ?_⟩
  have hb1 : 2 * a < b := by
    have : m * (2 * a) < m * b := by rw [← hb]; nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have hb2 : b < 2 * a + 2 := by
    have : m * b < m * (2 * a + 2) := by rw [← hb]; nlinarith
    exact Nat.lt_of_mul_lt_mul_left this
  have : b = 2 * a + 1 := by omega
  rw [hb, this, hza]; ring

omit [DecidableEq L] [DecidableEq R] in
lemma TNode.Child.eq_of_determined {z₁' z₁ z₂' z₂ : TNode q d} (h₁ : Child z₁' z₁) (h₂ : Child z₂' z₂)
    {X : ℕ} (h11 : z₁.c ≤ X) (h12 : X < z₁'.c) (h21 : z₂.c ≤ X) (h22 : X < z₂'.c)
    (hl : z₁.h = z₂.h) : z₁ = z₂ ∧ z₁' = z₂' := by
  obtain ⟨a1, a2⟩ := h₁.determined h11 h12
  obtain ⟨b1, b2⟩ := h₂.determined h21 h22
  have hc : z₁.c = z₂.c := by rw [a1, b1, hl]
  have hl' : z₁'.h = z₂'.h := by have := h₁.1; have := h₂.1; omega
  have hc' : z₁'.c = z₂'.c := by rw [a2, b2, hc, hl']
  exact ⟨Subtype.ext (Prod.ext (Fin.ext hl) (Fin.ext hc)),
    Subtype.ext (Prod.ext (Fin.ext hl') (Fin.ext hc'))⟩

omit [DecidableEq L] [DecidableEq R] in
lemma IsChildOf.unique {a b a' b' : Vtx L R q d p} {X : ℕ} (h : IsChildOf a b)
    (h' : IsChildOf a' b') (hb : b.col ≤ X) (ha : X < a.col) (hb' : b'.col ≤ X)
    (ha' : X < a'.col) (hl : lvl b = lvl b') : a = a' ∧ b = b' := by
  cases a <;> cases b <;> simp only [IsChildOf] at h
  cases a' <;> cases b' <;> simp only [IsChildOf] at h'
  simp only [col, lvl] at hb ha hb' ha' hl
  obtain ⟨e1, e2⟩ := Child.eq_of_determined h h' hb ha hb' ha' (congrArg Fin.val hl)
  exact ⟨by rw [e2], by rw [e1]⟩

omit [DecidableEq L] [DecidableEq R] in
/-- At most `d + 1` arcs (one per level) enter Alice's set per round. -/
lemma card_toA_le (hq : 0 < q) (T t : ℕ) : (toAV e T t).card ≤ d + 1 := by
  classical
  have : (toAV e T t).card ≤ (univ : Finset (Fin (d + 1))).card := by
    refine Finset.card_le_card_of_injOn (fun pr => lvl (e pr.2)) (by simp) ?_
    intro pr₁ h₁ pr₂ h₂ hl
    simp only [Finset.mem_coe, mem_toAV, kaV] at h₁ h₂
    have k1 := col_lt hq (e pr₁.1)
    have k2 := col_lt hq (e pr₂.1)
    obtain ⟨u1, u2⟩ := IsChildOf.unique (X := q - 3 - t) h₁.1 h₂.1 (by omega) (by omega)
      (by omega) (by omega) hl
    exact Prod.ext (e.injective u1) (e.injective u2)
  simpa using this

omit [DecidableEq L] [DecidableEq R] in
/-- At most `d + 1` arcs (one per level) enter Bob's set per round. -/
lemma card_toB_le (hq : 0 < q) (T t : ℕ) : (toBV e T t).card ≤ d + 1 := by
  classical
  have : (toBV e T t).card ≤ (univ : Finset (Fin (d + 1))).card := by
    refine Finset.card_le_card_of_injOn (fun pr => lvl (e pr.1)) (by simp) ?_
    intro pr₁ h₁ pr₂ h₂ hl
    simp only [Finset.mem_coe, mem_toBV, kbV] at h₁ h₂
    have k1 := col_lt hq (e pr₁.1)
    have k2 := col_lt hq (e pr₂.1)
    obtain ⟨u1, u2⟩ := IsChildOf.unique (X := t) h₁.1 h₂.1 (by omega) (by omega)
      (by omega) (by omega) hl
    exact Prod.ext (e.injective u2) (e.injective u1)
  simpa using this

/-- The lower-bound graphs as a moving-cut family for `T`-round algorithms (`2T + 2 ≤ q`), for
any network `G x y` with the adjacency of `G_{x,y}` (transported along `e`) and any node inputs
that do not depend on `y` outside Bob's column `q - 1` and not on `x` outside Alice's column `0`.
-/
def gadgetFamily {I : Type*} (T : ℕ) (hT : 2 * T + 2 ≤ q)
    (G : (E → Bool) → (E → Bool) → SimpleGraph V) (inp : (E → Bool) → (E → Bool) → V → I)
    (hG : ∀ x y a b, (G x y).Adj a b ↔ a ≠ b ∧ (darc E x y (e a) (e b) ∨ darc E x y (e b) (e a)))
    (hinpA : ∀ x y y' v, (e v).col + 1 ≠ q → inp x y v = inp x y' v)
    (hinpB : ∀ x x' y v, (e v).col ≠ 0 → inp x y v = inp x' y v) :
    MovingCutFamily (E → Bool) (E → Bool) V I where
  G := G
  inp := inp
  ka v := kaV T (e v)
  kb v := kbV T (e v)
  toA := toAV e T
  toB := toBV e T
  inp_alice x y y' v hv := hinpA x y y' v (by simp only [kaV] at hv; omega)
  inp_bob x x' y v hv := hinpB x x' y v (by simp only [kbV] at hv; omega)
  adj_alice x y y' w v hv := by
    have hc : (e v).col + 1 ≠ q := by simp only [kaV] at hv; omega
    rw [hG, hG, darc_indep_y x y y' (Or.inr hc), darc_indep_y x y y' (u := e v) (Or.inl hc)]
  adj_bob x x' y w v hv := by
    have hc : (e v).col ≠ 0 := by simp only [kbV] at hv; omega
    rw [hG, hG, darc_indep_x x x' y (Or.inr hc), darc_indep_x x x' y (u := e v) (Or.inl hc)]
  toA_bob t pr hpr := by
    simp only [mem_toAV, kaV, kbV] at hpr ⊢
    obtain ⟨-, h1, h2⟩ := hpr
    have := col_lt (by omega) (e pr.1)
    omega
  toB_alice t pr hpr := by
    simp only [mem_toBV, kaV, kbV] at hpr ⊢
    obtain ⟨-, h1, h2⟩ := hpr
    have := col_lt (by omega) (e pr.1)
    omega
  bdry_alice x y t w v hv hwv hw := by
    rw [mem_toAV]
    refine ⟨?_, hv, hw⟩
    simp only [kaV] at hv hw
    obtain ⟨-, h⟩ := (hG x y w v).1 hwv
    rcases h with h | h
    · rcases darc_cases h with h' | ⟨z, z', h1, h2, h3⟩
      · omega
      · have := h3.c_le
        simp only [h1, h2, col] at hw hv
        omega
    · rcases darc_cases h with h' | ⟨z, z', h1, h2, h3⟩
      · omega
      · simp only [h1, h2, IsChildOf]; exact h3
  bdry_bob x y t w v hv hwv hw := by
    rw [mem_toBV]
    refine ⟨?_, hv, hw⟩
    simp only [kbV] at hv hw
    obtain ⟨-, h⟩ := (hG x y w v).1 hwv
    rcases h with h | h
    · rcases darc_cases h with h' | ⟨z, z', h1, h2, h3⟩
      · omega
      · simp only [h1, h2, IsChildOf]; exact h3
    · rcases darc_cases h with h' | ⟨z, z', h1, h2, h3⟩
      · omega
      · have := h3.c_le
        simp only [h1, h2, col] at hw hv
        omega

omit [DecidableEq L] [DecidableEq R] in
/-- With `2T + 2 ≤ q`, every node is known to Alice or to Bob after `T` rounds. -/
lemma cover (T : ℕ) (hT : 2 * T + 2 ≤ q) (v : V) :
    T < kaV T (e v) ∨ T < kbV T (e v) := by
  have := col_lt (by omega) (e v)
  simp only [kaV, kbV]
  omega

end Podc.GirthApproxCongest
