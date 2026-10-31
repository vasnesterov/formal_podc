import Papers.PODC2018.InteractiveDistributedProofs.Model
import Papers.PODC2018.InteractiveDistributedProofs.Hash
import Papers.PODC2018.InteractiveDistributedProofs.TreeSum

/-!
# Protocol 1: the `O(log n)`-bit dMAM protocol for `Sym` (Section 3.1)

Messages (one copy of every broadcast value per node; nodes compare copies with their neighbours):

* first prover message to `v`: `(r, ρ_v, t_v, d_v) ∈ V × V × V × Fin n` (claimed root, image,
  parent, depth);
* challenge of `v`: a hash index `i_v ∈ ZMod p` (the family `polyHash` of Theorem 3.2, `|H| = p`);
* second prover message to `v`: `(i, a_v, b_v) ∈ (ZMod p)³` (claimed root index and hash values).

The verification (`verify`) is the paper's, lines 1–4:
1. `v ≠ r` ⇒ `t_v ∈ N(v)` and `d_{t_v} = d_v - 1`; `v = r` ⇒ `d_v = 0`;
2. `C(v) = {u ∈ N(v) | t_u = v}`;
3. `a_v = h_i([v, N(v)]) + ∑_{u ∈ C(v)} a_u` and `b_v = h_i([ρ_v, ρ(N(v))]) + ∑_{u ∈ C(v)} b_u`;
4. `v = r` ⇒ `a_r = b_r`, `ρ_r ≠ r`, `i = i_r`;
plus the implicit broadcast checks (`r` and `i` agree with all neighbours).

In line 3 we read the paper's `N_ρ(v)` as `ρ(N(v))` = `{ρ_u | u ∈ N(v)}`, as in equation (1), in the
proof of Lemma 3.3 and in Protocol 2 (the paper's footnote-style definition "the vector whose `v`-th
coordinate is 1 iff there exists `c ∈ C(v)` with `ρ_c = v`" is a typo: with `C(v)` in place of `N(v)`
the honest prover fails).

The flag `excl` selects the version of line 2: `excl = false` is the paper's literal
`C(v) = {u ∈ N(v) | t_u = v}`, `excl = true` the repaired `C(v) = {u ∈ N(v) | u ≠ r ∧ t_u = v}`
(the tree `T` of the proof of Lemma 3.3 only uses the edges `{v, t_v}` for `v ≠ r`).

## Main results

* `lemma_3_3` (repaired protocol) and `lemma_3_3_literal` (the general form for the literal protocol);
  `lemma_3_3_false`: the literal Lemma 3.3 fails (`K₂`, `t_r = r`, a hash index with `h_i(A) = 0`).
* `soundness`: for both versions, on a connected non-symmetric graph every prover is accepted with
  probability `≤ 2(n² − 1)/p < 1/3` when `p ≥ 10 n³`.
* `completeness`: an honest prover is accepted with probability `1` (repaired protocol; for the
  literal one, if some vertex moved by a non-trivial automorphism is not adjacent to all others).
* `theorem_3_4`: the repaired Protocol 1 decides `Sym` on connected graphs;
  `theorem_3_4_literal_false`: the literal Protocol 1 rejects the complete graph `K_n` (`n ≥ 2`, a
  YES-instance) with probability `> 2/3`, for every prover.
* `theorem_1_1`: `Sym ∈ dMAM[O(log n)]`.
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs.Protocol1

variable {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}

/-- First prover message: `(r, ρ_v, t_v, d_v)`. -/
abbrev M₁ (V : Type*) [Fintype V] := V × V × V × Fin (Fintype.card V)
/-- Second prover message: `(i, a_v, b_v)`. -/
abbrev M₂ (p : ℕ) := ZMod p × ZMod p × ZMod p
/-- Everything a node can read about one node. -/
abbrev Msg (V : Type*) [Fintype V] (p : ℕ) := M₁ V × ZMod p × M₂ p

section Accessors
variable (m : Msg V p)
/-- claimed root `r` -/
def root : V := m.1.1
/-- claimed image `ρ_v` -/
def rho : V := m.1.2.1
/-- claimed parent `t_v` -/
def par : V := m.1.2.2.1
/-- claimed depth `d_v` -/
def dep : ℕ := m.1.2.2.2
/-- own challenge `i_v` -/
def chal : ZMod p := m.2.1
/-- broadcast hash index `i` -/
def idx : ZMod p := m.2.2.1
/-- claimed hash value `a_v` -/
def ha : ZMod p := m.2.2.2.1
/-- claimed hash value `b_v` -/
def hb : ZMod p := m.2.2.2.2
end Accessors

/-- `h_s([w, S])`, computable by a node that knows `w`, `S` and the seed. -/
noncomputable def rowHash (s : ZMod p) (w : V) (S : Finset V) : ZMod p :=
  polyHash s (rowMat (ZMod p) w S)

/-- The verification procedure of node `v`, given its neighbourhood `nb = N(v)` and the messages
`x u` of the nodes `u ∈ N(v)` (values outside `N(v)` are never read). -/
def verify (excl : Bool) (v : V) (nb : Finset V) (x : V → Msg V p) : Prop :=
  (∀ u ∈ nb, root (x u) = root (x v) ∧ idx (x u) = idx (x v)) ∧
  (v ≠ root (x v) → par (x v) ∈ nb ∧ dep (x (par (x v))) + 1 = dep (x v)) ∧
  (v = root (x v) → dep (x v) = 0) ∧
  ha (x v) = rowHash (idx (x v)) v nb +
    ∑ u ∈ nb.filter (fun u => par (x u) = v ∧ (excl = true → u ≠ root (x v))), ha (x u) ∧
  hb (x v) = rowHash (idx (x v)) (rho (x v)) (nb.image fun u => rho (x u)) +
    ∑ u ∈ nb.filter (fun u => par (x u) = v ∧ (excl = true → u ≠ root (x v))), hb (x u) ∧
  (v = root (x v) → ha (x v) = hb (x v) ∧ rho (x v) ≠ v ∧ idx (x v) = chal (x v))

/-- `verify` only reads the messages of `N(v)`. -/
theorem verify_congr (excl : Bool) (v : V) (nb : Finset V) (hv : v ∈ nb) (x y : V → Msg V p)
    (hxy : ∀ u ∈ nb, x u = y u) : verify excl v nb x ↔ verify excl v nb y := by
  have hvv := hxy v hv
  have hf : nb.filter (fun u => par (x u) = v ∧ (excl = true → u ≠ root (y v))) =
      nb.filter (fun u => par (y u) = v ∧ (excl = true → u ≠ root (y v))) :=
    Finset.filter_congr fun u hu => by rw [hxy u hu]
  have hsa : ∀ f : Msg V p → ZMod p,
      ∑ u ∈ nb.filter (fun u => par (y u) = v ∧ (excl = true → u ≠ root (y v))), f (x u) =
      ∑ u ∈ nb.filter (fun u => par (y u) = v ∧ (excl = true → u ≠ root (y v))), f (y u) :=
    fun f => Finset.sum_congr rfl fun u hu => by rw [hxy u (Finset.mem_filter.1 hu).1]
  have himg : nb.image (fun u => rho (x u)) = nb.image (fun u => rho (y u)) :=
    Finset.image_congr fun u hu => by simp only [hxy u hu]
  have hall : (∀ u ∈ nb, root (x u) = root (y v) ∧ idx (x u) = idx (y v)) ↔
      (∀ u ∈ nb, root (y u) = root (y v) ∧ idx (y u) = idx (y v)) := by
    constructor <;> intro h u hu <;> [rw [← hxy u hu]; rw [hxy u hu]] <;> exact h u hu
  unfold verify
  rw [hvv, hf, hsa ha, hsa hb, himg, hall]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, fun h => ?_, h3, h4, h5, h6⟩
    obtain ⟨h21, h22⟩ := h2 h
    exact ⟨h21, by rwa [← hxy _ h21]⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, fun h => ?_, h3, h4, h5, h6⟩
    obtain ⟨h21, h22⟩ := h2 h
    exact ⟨h21, by rwa [hxy _ h21]⟩

variable [Nonempty V]

/-- A default message (only used for positions outside the view, which are never read). -/
noncomputable def dflt : Msg V p :=
  ((Classical.arbitrary V, Classical.arbitrary V, Classical.arbitrary V, ⟨0, Fintype.card_pos⟩),
    0, 0, 0, 0)

/-- **Protocol 1** (`excl = false`: literal; `excl = true`: root excluded from `C(v)`). -/
noncomputable def protocol (p : ℕ) (excl : Bool) : MAMProtocol V (M₁ V) (ZMod p) (M₂ p) where
  out v w := verify excl v (viewNbhd w) fun u => (w u).getD dflt

theorem out_mask (excl : Bool) (G : SimpleGraph V) (v : V) (x : V → Msg V p) :
    (protocol p excl).out v (mask G v x) ↔ verify excl v (cnbhd G v) x := by
  show verify excl v (viewNbhd (mask G v x)) _ ↔ _
  rw [viewNbhd_mask]
  exact verify_congr excl v _ (self_mem_cnbhd v) _ _ fun u hu => by
    rw [mask_apply_of_mem x hu]; rfl

/-! ### What acceptance implies (the summation argument) -/

/-- The global message vector seen by the nodes. -/
def glob (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) (c : V → ZMod p) : V → Msg V p :=
  fun u => (P.first u, c u, P.second c u)

/-- The root claimed to the reference node, and the claimed map `ρ` (both fixed by the first
message). -/
noncomputable def root₀ (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) : V :=
  (P.first (Classical.arbitrary V)).1

/-- The map `ρ` the prover committed to in the first round. -/
def rhoMap (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) : V → V := fun u => (P.first u).2.1

omit [Nonempty V] in
theorem sum_rowHash_adj (G : SimpleGraph V) (s : ZMod p) :
    ∑ v, rowHash s v (cnbhd G v) = polyHash s (adjSum (ZMod p) G) := by
  simp [rowHash, adjSum, map_sum]

omit [Nonempty V] in
theorem sum_rowHash_perm (G : SimpleGraph V) (ρ : V → V) (s : ZMod p) :
    ∑ v, rowHash s (ρ v) ((cnbhd G v).image ρ) = polyHash s (permSum (ZMod p) G ρ) := by
  simp [rowHash, permSum, map_sum]

/-- The structure of an accepting run: all nodes agree on the root `r = root₀ P` and on the index
`i = c r`, `ρ r ≠ r`, the per-node checks hold with `C(v) = children`, and the root values. -/
structure AcceptData (excl : Bool) (G : SimpleGraph V) (P : MAMProver V (M₁ V) (ZMod p) (M₂ p))
    (c : V → ZMod p) : Prop where
  root_eq : ∀ u, root (glob P c u) = root₀ P
  idx_eq : ∀ u, idx (glob P c u) = c (root₀ P)
  rho_ne : rhoMap P (root₀ P) ≠ root₀ P
  par_mem : ∀ v, v ≠ root₀ P → par (glob P c v) ∈ cnbhd G v
  checkA : ∀ v, ha (glob P c v) = rowHash (c (root₀ P)) v (cnbhd G v) +
    ∑ u ∈ children (cnbhd G) (fun u => par (glob P c u)) (root₀ P) excl v, ha (glob P c u)
  checkB : ∀ v, hb (glob P c v) = rowHash (c (root₀ P)) (rhoMap P v) ((cnbhd G v).image (rhoMap P)) +
    ∑ u ∈ children (cnbhd G) (fun u => par (glob P c u)) (root₀ P) excl v, hb (glob P c u)
  root_ab : ha (glob P c (root₀ P)) = hb (glob P c (root₀ P))

theorem acceptData {excl : Bool} {G : SimpleGraph V} (hG : G.Connected)
    {P : MAMProver V (M₁ V) (ZMod p) (M₂ p)} {c : V → ZMod p}
    (hacc : (protocol p excl).Accepts G P c) : AcceptData excl G P c := by
  have hv : ∀ v, verify excl v (cnbhd G v) (glob P c) := fun v => (out_mask excl G v _).1 (hacc v)
  -- broadcast values are constant
  have hroot : ∀ u v, root (glob P c u) = root (glob P c v) :=
    eq_of_connected hG _ fun u v huv =>
      ((hv u).1 v (mem_cnbhd.2 (Or.inr huv))).1.symm
  have hidx : ∀ u v, idx (glob P c u) = idx (glob P c v) :=
    eq_of_connected hG _ fun u v huv =>
      ((hv u).1 v (mem_cnbhd.2 (Or.inr huv))).2.symm
  set r := root₀ P with hr
  have hr' : ∀ u, root (glob P c u) = r := fun u => hroot u (Classical.arbitrary V)
  have hrr : r = root (glob P c r) := (hr' r).symm
  obtain ⟨hab, hρ, hi⟩ := (hv r).2.2.2.2.2 hrr
  have hidx' : ∀ u, idx (glob P c u) = c r := fun u => (hidx u r).trans hi
  have hch : ∀ v, (cnbhd G v).filter
      (fun u => par (glob P c u) = v ∧ (excl = true → u ≠ root (glob P c v))) =
      children (cnbhd G) (fun u => par (glob P c u)) r excl v := by
    intro v; simp only [children, hr' v]
  refine ⟨hr', hidx', hρ, fun v hvr => ((hv v).2.1 (by rw [hr' v]; exact hvr)).1, fun v => ?_,
    fun v => ?_, hab⟩
  · have := (hv v).2.2.2.1
    rwa [hidx' v, hch v] at this
  · have := (hv v).2.2.2.2.1
    rw [hidx' v, hch v] at this
    exact this

/-- **Lemma 3.3** (repaired protocol, root excluded from `C(v)`): if all nodes accept, then
`a_r = h_i(∑_v [v, N(v)])` and `b_r = h_i(∑_v [ρ(v), ρ(N(v))])`. -/
theorem lemma_3_3 {G : SimpleGraph V} (hG : G.Connected) {P : MAMProver V (M₁ V) (ZMod p) (M₂ p)}
    {c : V → ZMod p} (hacc : (protocol p true).Accepts G P c) :
    ha (glob P c (root₀ P)) = polyHash (c (root₀ P)) (adjSum (ZMod p) G) ∧
    hb (glob P c (root₀ P)) = polyHash (c (root₀ P)) (permSum (ZMod p) G (rhoMap P)) := by
  have D := acceptData hG hacc
  constructor
  · rw [← sum_rowHash_adj]
    exact treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem true _ _ D.checkA
      (Or.inl rfl)
  · rw [← sum_rowHash_perm]
    exact treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem true _ _ D.checkB
      (Or.inl rfl)

/-- What survives of Lemma 3.3 for the literal protocol: either the conclusion of Lemma 3.3 holds,
or the root is counted as a child of `t_r` and then both hash sums vanish. -/
theorem lemma_3_3_literal {G : SimpleGraph V} (hG : G.Connected)
    {P : MAMProver V (M₁ V) (ZMod p) (M₂ p)} {c : V → ZMod p}
    (hacc : (protocol p false).Accepts G P c) :
    (ha (glob P c (root₀ P)) = polyHash (c (root₀ P)) (adjSum (ZMod p) G) ∧
      hb (glob P c (root₀ P)) = polyHash (c (root₀ P)) (permSum (ZMod p) G (rhoMap P))) ∨
    (par (glob P c (root₀ P)) ∈ cnbhd G (root₀ P) ∧
      polyHash (c (root₀ P)) (adjSum (ZMod p) G) = 0 ∧
      polyHash (c (root₀ P)) (permSum (ZMod p) G (rhoMap P)) = 0) := by
  have D := acceptData hG hacc
  by_cases ht : par (glob P c (root₀ P)) ∈ cnbhd G (root₀ P)
  · right
    refine ⟨ht, ?_, ?_⟩
    · rw [← sum_rowHash_adj]
      exact treeSum_eq_zero (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem _ _ D.checkA ht
    · rw [← sum_rowHash_perm]
      exact treeSum_eq_zero (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem _ _ D.checkB ht
  · left
    constructor
    · rw [← sum_rowHash_adj]
      exact treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem false _ _
        D.checkA (Or.inr ht)
    · rw [← sum_rowHash_perm]
      exact treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem false _ _
        D.checkB (Or.inr ht)

/-- Acceptance (either version) implies a hash collision at the root's index. -/
theorem accept_imp_collision {excl : Bool} {G : SimpleGraph V} (hG : G.Connected)
    {P : MAMProver V (M₁ V) (ZMod p) (M₂ p)} {c : V → ZMod p}
    (hacc : (protocol p excl).Accepts G P c) :
    rhoMap P (root₀ P) ≠ root₀ P ∧
      (polyHash (c (root₀ P)) (adjSum (ZMod p) G) =
          polyHash (c (root₀ P)) (permSum (ZMod p) G (rhoMap P)) ∨
        polyHash (c (root₀ P)) (adjSum (ZMod p) G) =
          polyHash (c (root₀ P)) (0 : V × V → ZMod p)) := by
  have D := acceptData hG hacc
  refine ⟨D.rho_ne, ?_⟩
  rw [map_zero]
  by_cases ht : excl = false ∧ par (glob P c (root₀ P)) ∈ cnbhd G (root₀ P)
  · right
    obtain ⟨he, ht⟩ := ht
    subst he
    rw [← sum_rowHash_adj]
    exact treeSum_eq_zero (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem _ _ D.checkA ht
  · left
    have hr : excl = true ∨ par (glob P c (root₀ P)) ∉ cnbhd G (root₀ P) := by
      by_contra h
      push Not at h
      exact ht ⟨by simpa using h.1, h.2⟩
    rw [← sum_rowHash_adj, ← sum_rowHash_perm,
      ← treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem excl _ _ D.checkA hr,
      ← treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem excl _ _ D.checkB hr]
    exact D.root_ab

/-! ### The same argument for an arbitrary accepting message vector (used for Protocol 2) -/

/-- The root claimed to the reference node. -/
noncomputable def xroot (x : V → Msg V p) : V := root (x (Classical.arbitrary V))

/-- If every node passes `verify` on a connected graph, then (with `r` the common root, `i` the root's
own challenge, and `ρ u = ρ_u`) we have `ρ r ≠ r`, `i` is the common index, and either the root
hash values are the full hash sums, or the root is counted as a child and `h_i(∑_v [v, N(v)]) = 0`. -/
theorem collision_of_verify {excl : Bool} {G : SimpleGraph V} (hG : G.Connected)
    {x : V → Msg V p} (hv : ∀ v, verify excl v (cnbhd G v) x) :
    rho (x (xroot x)) ≠ xroot x ∧
      (polyHash (chal (x (xroot x))) (adjSum (ZMod p) G) =
          polyHash (chal (x (xroot x))) (permSum (ZMod p) G fun u => rho (x u)) ∨
        polyHash (chal (x (xroot x))) (adjSum (ZMod p) G) =
          polyHash (chal (x (xroot x))) (0 : V × V → ZMod p)) := by
  have hroot : ∀ u v, root (x u) = root (x v) :=
    eq_of_connected hG _ fun u v huv => ((hv u).1 v (mem_cnbhd.2 (Or.inr huv))).1.symm
  have hidx : ∀ u v, idx (x u) = idx (x v) :=
    eq_of_connected hG _ fun u v huv => ((hv u).1 v (mem_cnbhd.2 (Or.inr huv))).2.symm
  set r := xroot x with hr
  have hr' : ∀ u, root (x u) = r := fun u => hroot u (Classical.arbitrary V)
  obtain ⟨hab, hρ, hi⟩ := (hv r).2.2.2.2.2 (hr' r).symm
  have hidx' : ∀ u, idx (x u) = chal (x r) := fun u => (hidx u r).trans hi
  have hch : ∀ v, (cnbhd G v).filter
      (fun u => par (x u) = v ∧ (excl = true → u ≠ root (x v))) =
      children (cnbhd G) (fun u => par (x u)) r excl v := by
    intro v; simp only [children, hr' v]
  have hpm : ∀ v, v ≠ r → par (x v) ∈ cnbhd G v :=
    fun v hvr => ((hv v).2.1 (by rw [hr' v]; exact hvr)).1
  have hA : ∀ v, ha (x v) = rowHash (chal (x r)) v (cnbhd G v) +
      ∑ u ∈ children (cnbhd G) (fun u => par (x u)) r excl v, ha (x u) := by
    intro v; have := (hv v).2.2.2.1; rwa [hidx' v, hch v] at this
  have hB : ∀ v, hb (x v) = rowHash (chal (x r)) (rho (x v))
      ((cnbhd G v).image fun u => rho (x u)) +
      ∑ u ∈ children (cnbhd G) (fun u => par (x u)) r excl v, hb (x u) := by
    intro v; have := (hv v).2.2.2.2.1; rwa [hidx' v, hch v] at this
  refine ⟨hρ, ?_⟩
  rw [map_zero]
  by_cases ht : excl = false ∧ par (x r) ∈ cnbhd G r
  · right
    obtain ⟨he, ht⟩ := ht
    subst he
    rw [← sum_rowHash_adj]
    exact treeSum_eq_zero (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ hpm _ _ hA ht
  · left
    have hr2 : excl = true ∨ par (x r) ∉ cnbhd G r := by
      by_contra h
      push Not at h
      exact ht ⟨by simpa using h.1, h.2⟩
    rw [← sum_rowHash_adj, ← sum_rowHash_perm,
      ← treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ hpm excl _ _ hA hr2,
      ← treeSum_root_eq (cnbhd G) (fun _ _ => mem_cnbhd_comm) _ _ hpm excl _ _ hB hr2]
    exact hab

/-! ### Soundness -/

/-- **Soundness** of Protocol 1 (both versions): on a connected graph without non-trivial
automorphism, every prover makes all nodes accept with probability at most `2(n² - 1)/p`. -/
theorem soundness_bound [Fact p.Prime] (excl : Bool) {G : SimpleGraph V} (hG : G.Connected)
    (hS : ¬ Sym G) (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) :
    (protocol p excl).accProb G P ≤ 2 * ((Fintype.card V ^ 2 - 1 : ℕ) : ℝ) / p := by
  classical
  set r := root₀ P
  set ρ := rhoMap P
  set A := adjSum (ZMod p) G
  set B := permSum (ZMod p) G ρ
  let E : ZMod p → Prop := fun s =>
    ρ r ≠ r ∧ (polyHash s A = polyHash s B ∨ polyHash s A = polyHash s (0 : V × V → ZMod p))
  have hsub : ∀ c, (protocol p excl).Accepts G P c → E (c r) := fun c h =>
    accept_imp_collision hG h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (protocol p excl).accProb G P ≤ uprob fun c : V → ZMod p => E (c r) := uprob_mono hsub
    _ = uprob E := uprob_coord r E
    _ ≤ 2 * ((Fintype.card V ^ 2 - 1 : ℕ) : ℝ) / p := by
      rw [uprob_eq_card_filter, ZMod.card]
      rw [div_le_div_iff_of_pos_right hp0]
      by_cases hρ : ρ r = r
      · have : univ.filter E = ∅ := by
          ext s; simp [E, hρ]
        rw [this]; simp
      · have hne : ρ ≠ id := fun h => hρ (by rw [h]; rfl)
        have hAB : A ≠ B := adjSum_ne_permSum hS hne
        have hA0 : A ≠ 0 := adjSum_ne_zero
        have h1 := card_collision_le (p := p) hAB
        have h2 := card_collision_le (p := p) hA0
        have hcard : Fintype.card (V × V) = Fintype.card V ^ 2 := by
          rw [Fintype.card_prod, sq]
        rw [hcard] at h1 h2
        have hsplit : univ.filter E ⊆ (univ.filter fun s : ZMod p => polyHash s A = polyHash s B) ∪
            (univ.filter fun s : ZMod p => polyHash s A = polyHash s (0 : V × V → ZMod p)) := by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, E] at hs
          rcases hs.2 with h | h <;> simp [h]
        have := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
        have h3 : #(univ.filter E) ≤ 2 * (Fintype.card V ^ 2 - 1) := by omega
        exact_mod_cast h3

theorem soundness [Fact p.Prime] (excl : Bool) (hp : 10 * Fintype.card V ^ 3 ≤ p)
    {G : SimpleGraph V} (hG : G.Connected) (hS : ¬ Sym G)
    (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) :
    (protocol p excl).accProb G P < 1 / 3 := by
  refine (soundness_bound excl hG hS P).trans_lt ?_
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_lt_div_iff₀ hp0 (by norm_num)]
  have h1 : (Fintype.card V ^ 2 - 1 : ℕ) ≤ Fintype.card V ^ 2 := Nat.sub_le _ _
  have h2 : Fintype.card V ^ 2 ≤ Fintype.card V ^ 3 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have h3 : 2 * (Fintype.card V ^ 2 - 1 : ℕ) * 3 < 1 * p := by
    have : 0 < Fintype.card V ^ 3 := by positivity
    omega
  exact_mod_cast h3

/-! ### Completeness -/

omit [DecidableEq V] [Nonempty V] in
/-- In a connected graph, distances are `< n`. -/
theorem dist_lt_card {G : SimpleGraph V} (hG : G.Connected) (u v : V) :
    G.dist u v < Fintype.card V := by
  obtain ⟨q, hq, hlen⟩ := hG.exists_path_of_dist u v
  rw [← hlen]
  exact hq.length_lt

omit [Fintype V] [DecidableEq V] [Nonempty V] in
/-- BFS parents: every `v ≠ r` has a neighbour one step closer to `r`. -/
theorem exists_parent {G : SimpleGraph V} (hG : G.Connected) {v r : V} (hv : v ≠ r) :
    ∃ u, G.Adj v u ∧ G.dist u r + 1 = G.dist v r := by
  obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist v r
  cases q with
  | nil => exact absurd rfl hv
  | @cons _ u _ h q =>
    refine ⟨u, h, ?_⟩
    have h1 : G.dist u r ≤ q.length := SimpleGraph.dist_le q
    have h2 : G.dist v r ≤ G.dist v u + G.dist u r := hG.dist_triangle
    rw [SimpleGraph.dist_eq_one_iff_adj.2 h] at h2
    simp only [SimpleGraph.Walk.length_cons] at hq
    omega

/-- The honest parent pointers (`t_r = tr`). -/
noncomputable def honestPar {G : SimpleGraph V} (hG : G.Connected) (r tr : V) (v : V) : V :=
  if h : v = r then tr else Classical.choose (exists_parent hG h)

omit [Fintype V] [Nonempty V] in
theorem honestPar_spec {G : SimpleGraph V} (hG : G.Connected) {r tr v : V} (h : v ≠ r) :
    G.Adj v (honestPar hG r tr v) ∧ G.dist (honestPar hG r tr v) r + 1 = G.dist v r := by
  simp only [honestPar, h, dite_false]
  exact Classical.choose_spec (exists_parent hG h)

/-- The honest first message: `(r, ρ v, t_v, dist(v, r))`. -/
noncomputable def honestFirst {G : SimpleGraph V} (hG : G.Connected) (ρ : V → V) (r tr : V)
    (v : V) : M₁ V :=
  (r, ρ v, honestPar hG r tr v, ⟨G.dist v r, dist_lt_card hG v r⟩)

omit [Nonempty V] in
theorem honest_children_dep {G : SimpleGraph V} (hG : G.Connected) {r tr : V} {excl : Bool}
    (htr : excl = true ∨ tr ∉ cnbhd G r) (v : V) :
    ∀ u ∈ children (cnbhd G) (honestPar hG r tr) r excl v, G.dist u r = G.dist v r + 1 := by
  intro u hu
  simp only [children, Finset.mem_filter] at hu
  obtain ⟨hun, hpar, hex⟩ := hu
  by_cases hur : u = r
  · exfalso
    subst hur
    have : honestPar hG u tr u = tr := by simp [honestPar]
    rw [this] at hpar
    subst hpar
    rcases htr with h | h
    · exact hex h rfl
    · exact h (mem_cnbhd_comm.1 hun)
  · have := (honestPar_spec hG (tr := tr) hur).2
    rw [hpar] at this
    omega

omit [Nonempty V] in
/-- The honest prover's hash values for seed `s`: solutions of the tree-sum checks. -/
theorem exists_honest_hashes {G : SimpleGraph V} (hG : G.Connected) {r tr : V} {excl : Bool}
    (htr : excl = true ∨ tr ∉ cnbhd G r) (c : V → ZMod p) :
    ∃ a : V → ZMod p, ∀ v,
      a v = c v + ∑ u ∈ children (cnbhd G) (honestPar hG r tr) r excl v, a u :=
  exists_treeSol _ (fun v => G.dist v r) (Fintype.card V) (fun v => dist_lt_card hG v r)
    (honest_children_dep hG htr) c

/-- The honest prover (given a non-trivial automorphism `ρ`, a vertex `r` it moves, and the root's
parent pointer `tr`). -/
noncomputable def honest {G : SimpleGraph V} (hG : G.Connected) (ρ : V → V) {r tr : V} {excl : Bool}
    (htr : excl = true ∨ tr ∉ cnbhd G r) : MAMProver V (M₁ V) (ZMod p) (M₂ p) where
  first := honestFirst hG ρ r tr
  second c v :=
    (c r,
      Classical.choose (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) v (cnbhd G v)) v,
      Classical.choose (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) (ρ v) ((cnbhd G v).image ρ)) v)

omit [Nonempty V] in
/-- The honest prover passes every node's verification, for every challenge vector. -/
theorem honest_verify {G : SimpleGraph V} (hG : G.Connected) {ρ : V → V} (hρ : IsAut G ρ)
    {r tr : V} (hr : ρ r ≠ r) {excl : Bool} (htr : excl = true ∨ tr ∉ cnbhd G r)
    (c : V → ZMod p) (v : V) : verify excl v (cnbhd G v) (glob (honest (p := p) hG ρ htr) c) := by
    set x := glob (honest (p := p) hG ρ htr) c
    have hroot : ∀ u, root (x u) = r := fun u => rfl
    have hidx : ∀ u, idx (x u) = c r := fun u => rfl
    have hrho : ∀ u, rho (x u) = ρ u := fun u => rfl
    have hpar : ∀ u, par (x u) = honestPar hG r tr u := fun u => rfl
    have hdep : ∀ u, dep (x u) = G.dist u r := fun u => rfl
    have hchal : ∀ u, chal (x u) = c u := fun u => rfl
    have hspecA := Classical.choose_spec (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) v (cnbhd G v))
    have hspecB := Classical.choose_spec (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) (ρ v) ((cnbhd G v).image ρ))
    have hha : ∀ u, ha (x u) = Classical.choose (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) v (cnbhd G v)) u := fun u => rfl
    have hhb : ∀ u, hb (x u) = Classical.choose (exists_honest_hashes (p := p) hG htr
        fun v => rowHash (c r) (ρ v) ((cnbhd G v).image ρ)) u := fun u => rfl
    have hch : (cnbhd G v).filter (fun u => par (x u) = v ∧ (excl = true → u ≠ root (x v))) =
        children (cnbhd G) (honestPar hG r tr) r excl v := by
      simp only [children, hpar, hroot]
    have himg : (cnbhd G v).image (fun u => rho (x u)) = (cnbhd G v).image ρ := by
      simp only [hrho]
    have hnb : ∀ u v : V, u ∈ cnbhd G v ↔ v ∈ cnbhd G u := fun _ _ => mem_cnbhd_comm
    have hpm : ∀ v, v ≠ r → honestPar hG r tr v ∈ cnbhd G v := fun v hv =>
      mem_cnbhd.2 (Or.inr (honestPar_spec hG hv).1)
    refine ⟨fun u _ => ⟨rfl, rfl⟩, fun hv => ?_, fun hv => ?_, ?_, ?_, fun hv => ?_⟩
    · rw [hroot] at hv
      refine ⟨by rw [hpar]; exact hpm v hv, ?_⟩
      rw [hdep, hdep, hpar]
      exact (honestPar_spec hG hv).2
    · rw [hroot] at hv; subst hv; rw [hdep]; simp
    · rw [hch, hidx, hha]
      exact hspecA v
    · rw [hch, hidx, hrho, himg, hhb]
      exact hspecB v
    · rw [hroot] at hv
      subst hv
      refine ⟨?_, by rw [hrho]; exact hr, by rw [hidx, hchal]⟩
      have htr' : excl = true ∨ honestPar hG v tr v ∉ cnbhd G v := by
        simpa [honestPar] using htr
      rw [hha, hhb,
        treeSum_root_eq (cnbhd G) hnb _ _ hpm excl _ _ hspecA htr',
        treeSum_root_eq (cnbhd G) hnb _ _ hpm excl _ _ hspecB htr',
        sum_rowHash_adj, sum_rowHash_perm, permSum_eq_adjSum hρ]

/-- **Completeness** of Protocol 1: if `ρ` is an automorphism moving `r`, and either the root is
excluded from `C(v)` or the root's pointer `tr` lies outside `N(r)`, the honest prover is accepted
with probability `1`. -/
theorem completeness_one [NeZero p] {G : SimpleGraph V} (hG : G.Connected) {ρ : V → V}
    (hρ : IsAut G ρ) {r tr : V} (hr : ρ r ≠ r) {excl : Bool} (htr : excl = true ∨ tr ∉ cnbhd G r) :
    (protocol p excl).accProb G (honest (p := p) hG ρ htr) = 1 := by
  have hall : ∀ c, (protocol p excl).Accepts G (honest (p := p) hG ρ htr) c := fun c v =>
    (out_mask excl G v _).2 (honest_verify hG hρ hr htr c v)
  unfold MAMProtocol.accProb
  rw [show (protocol p excl).Accepts G (honest (p := p) hG ρ htr) = fun _ => True from
    funext fun c => propext ⟨fun _ => trivial, fun _ => hall c⟩]
  simp [uprob_true, NeZero.ne p]

/-! ### Theorem 3.4 and Theorem 1.1 -/

/-- **Theorem 3.4** (repaired Protocol 1): with `p ≥ 10 n³` prime, Protocol 1 decides `Sym` on
connected graphs (completeness with probability `1`, soundness error `< 1/3`). -/
theorem theorem_3_4 [Fact p.Prime] (hp : 10 * Fintype.card V ^ 3 ≤ p) :
    (protocol (V := V) p true).Decides (fun G => G.Connected) Sym := by
  intro G hG
  refine ⟨fun ⟨ρ, hρ, hne⟩ => ?_, fun hS P => soundness true hp hG hS P⟩
  have : ∃ r, ρ r ≠ r := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨r, hr⟩ := this
  exact ⟨honest (p := p) hG ρ (r := r) (tr := r) (Or.inl rfl), by
    rw [completeness_one hG hρ hr]; norm_num⟩

omit [Nonempty V] in
/-- The complete graph on at least two vertices is symmetric. -/
theorem sym_top (h2 : 2 ≤ Fintype.card V) : Sym (⊤ : SimpleGraph V) := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  refine ⟨Equiv.swap a b, ⟨(Equiv.swap a b).bijective, fun u v => ?_⟩, fun h => hab ?_⟩
  · simp
  · have := congrFun h a
    simpa using this.symm

/-- **Theorem 3.1.1 as literally stated fails**: with the paper's `C(v) = {u ∈ N(v) | t_u = v}`, on the
complete graph every prover is accepted with probability at most `(n² - 1)/p`, although `K_n`
(`n ≥ 2`) is symmetric: the root's pointer `t_r` necessarily lies in `N(r) = V`, so the root is
counted as a child and the checks force `h_i(∑_v [v, N(v)]) = 0`. -/
theorem accProb_top_literal_le [Fact p.Prime] (P : MAMProver V (M₁ V) (ZMod p) (M₂ p)) :
    (protocol p false).accProb ⊤ P ≤ ((Fintype.card V ^ 2 - 1 : ℕ) : ℝ) / p := by
  classical
  set r := root₀ P
  let E : ZMod p → Prop := fun s =>
    polyHash s (adjSum (ZMod p) (⊤ : SimpleGraph V)) = polyHash s (0 : V × V → ZMod p)
  have hsub : ∀ c, (protocol p false).Accepts ⊤ P c → E (c r) := by
    intro c h
    have D := acceptData SimpleGraph.connected_top h
    have hmem : par (glob P c r) ∈ cnbhd (⊤ : SimpleGraph V) r := by
      rw [mem_cnbhd]
      by_cases h' : par (glob P c r) = r
      · exact Or.inl h'
      · exact Or.inr (by simpa [eq_comm] using h')
    have := treeSum_eq_zero (cnbhd ⊤) (fun _ _ => mem_cnbhd_comm) _ _ D.par_mem _ _ D.checkA hmem
    rw [sum_rowHash_adj] at this
    simp only [E, map_zero]
    exact this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (protocol p false).accProb ⊤ P ≤ uprob fun c : V → ZMod p => E (c r) := uprob_mono hsub
    _ = uprob E := uprob_coord r E
    _ ≤ ((Fintype.card V ^ 2 - 1 : ℕ) : ℝ) / p := by
      rw [uprob_eq_card_filter, ZMod.card, div_le_div_iff_of_pos_right hp0]
      have h1 := card_collision_le (p := p)
        (adjSum_ne_zero (R := ZMod p) (G := (⊤ : SimpleGraph V)))
      rw [Fintype.card_prod, ← sq] at h1
      exact_mod_cast h1

/-- **Theorem 3.4 fails for the literal Protocol 1**: for `n ≥ 2` and `p ≥ 10 n³`, the literal
protocol does not decide `Sym` on connected graphs (it rejects `K_n` with probability `> 2/3`). -/
theorem theorem_3_4_literal_false [Fact p.Prime] (hn : 2 ≤ Fintype.card V)
    (hp : 10 * Fintype.card V ^ 3 ≤ p) :
    ¬ (protocol (V := V) p false).Decides (fun G => G.Connected) Sym := by
  intro hdec
  obtain ⟨P, hP⟩ := (hdec ⊤ SimpleGraph.connected_top).1 (sym_top hn)
  have h1 := accProb_top_literal_le P
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h2 : ((Fintype.card V ^ 2 - 1 : ℕ) : ℝ) / p ≤ 2 / 3 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]
    have : (Fintype.card V ^ 2 - 1 : ℕ) * 3 ≤ 2 * p := by
      have h3 : Fintype.card V ^ 2 ≤ Fintype.card V ^ 3 :=
        Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    exact_mod_cast this
  linarith

/-- **Theorem 1.1**: `Sym ∈ dMAM[O(log n)]` — every node exchanges at most `90 (log₂ n + 1)` bits with
the prover (three alphabets of at most `2^{30 (log₂ n + 1)}` symbols each). -/
theorem theorem_1_1 :
    InDMAM (fun _ _ _ G => Sym G) (fun n => 30 * (Nat.log 2 n + 1)) := by
  intro V _ _ _
  set n := Fintype.card V with hn
  have hn1 : 1 ≤ n := Fintype.card_pos
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (10 * n ^ 3) (by positivity)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨M₁ V, ZMod p, M₂ p, inferInstance, inferInstance, inferInstance, protocol p true,
    ?_, ?_, ?_, theorem_3_4 hlt.le⟩
  all_goals
    beta_reduce
    set L := Nat.log 2 n + 1
    have hL : n < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
    have hL1 : 1 ≤ L := by omega
    have hp' : p ≤ 2 ^ (8 * L) := by
      have h1 : n ^ 3 ≤ (2 ^ L) ^ 3 := Nat.pow_le_pow_left hL.le 3
      have h2 : (2 : ℕ) ^ 5 ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc p ≤ 2 * (10 * n ^ 3) := hle
        _ ≤ 2 ^ 5 * (2 ^ L) ^ 3 := by omega
        _ ≤ 2 ^ (5 * L) * (2 ^ L) ^ 3 := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (8 * L) := by rw [← pow_mul, ← pow_add]; ring_nf
  · simp only [M₁, Fintype.card_prod, Fintype.card_fin]
    have h1 : n * (n * (n * n)) ≤ 2 ^ L * (2 ^ L * (2 ^ L * 2 ^ L)) := by
      gcongr
    calc n * (n * (n * n)) ≤ 2 ^ L * (2 ^ L * (2 ^ L * 2 ^ L)) := h1
      _ = 2 ^ (4 * L) := by rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (30 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [ZMod.card]
    exact hp'.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · simp only [M₂, Fintype.card_prod, ZMod.card]
    calc p * (p * p) ≤ 2 ^ (8 * L) * (2 ^ (8 * L) * 2 ^ (8 * L)) := by gcongr
      _ = 2 ^ (24 * L) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (30 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Podc.InteractiveDistributedProofs.Protocol1
