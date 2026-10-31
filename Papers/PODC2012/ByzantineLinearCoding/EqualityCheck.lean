import Mathlib
import Cslib.Probability.Finite.Uniform

/-!
# The Equality Check algorithm of NAB (Liang–Vaidya, PODC 2012), Algorithm 1

Model of one execution of Algorithm 1 (Step 2.1 of the `k`-th instance of NAB) on the graph
`G_k`:

* the nodes are a finite type `V`; `z a b : ℕ` is the capacity of the directed link `(a, b)` of `G_k`
  (`0` = no link). A *coded symbol* (`Sym z`) is one unit of capacity of one link;
* every node `i` holds `X i : Fin ρ → F`, its `L`-bit Phase-1 value cut into `ρ` symbols of the
  field `F` (in the paper `F = GF(2^{L/ρ})`);
* the coding matrices `C_e` are one function `c : Sym z × Fin ρ → F` (`c (s, p)` = entry `p` of the
  column of `C_e` that produces the coded symbol `s`);
* a fault-free sender `a` sends `code c s (X a) = Σ_p X a p · c (s, p)` on every coded symbol `s` of
  its outgoing links; a faulty sender sends anything (`Y s`). A fault-free receiver `b` checks
  `Y s = code c s (X b)` on every coded symbol of its incoming links (step 2 of Algorithm 1).

`Correct` is the paper's property (EC): whenever no fault-free node detects a mismatch, all
fault-free nodes hold the same value. Faulty sets are those allowed in the `k`-th instance: at most
`f` nodes, containing every node already removed from `V_k`, and containing a node of every pair
found in dispute so far (dispute control never puts two fault-free nodes in dispute).
-/

namespace Podc.ByzantineLinearCoding

open Finset Matrix

variable {V : Type*} [DecidableEq V]

/-- Coded symbols of the network with capacities `z`: one per unit of capacity of a directed link.
-/
abbrev Sym (z : V → V → ℕ) := Σ e : V × V, Fin (z e.1 e.2)

/-- Sender of a coded symbol. -/
abbrev Sym.tail {z : V → V → ℕ} (s : Sym z) : V := s.1.1

/-- Receiver of a coded symbol. -/
abbrev Sym.head {z : V → V → ℕ} (s : Sym z) : V := s.1.2

/-- The coding matrices `{C_e | e ∈ E_k}` of Algorithm 1, as one function of (coded symbol,
row index). -/
abbrev Coding (z : V → V → ℕ) (ρ : ℕ) (R : Type*) := Sym z × Fin ρ → R

/-- The coded symbol `s` computed from the vector `x = X_i`: the corresponding entry of
`Y_e = X_i C_e`. -/
def code {R : Type*} [CommRing R] {z : V → V → ℕ} {ρ : ℕ} (c : Coding z ρ R) (s : Sym z)
    (x : Fin ρ → R) : R :=
  ∑ p, x p * c (s, p)

/-- Property (EC) of Section 3.1: the coding `c` is *correct* if, for every admissible set `B` of
faulty nodes, every Phase-1 outcome `X` and every behaviour of the faulty senders (`Y`), the
following holds: if no fault-free node detects a mismatch, then all fault-free nodes hold
identical values. (This is the contrapositive of the paper's phrasing.) -/
def Correct {F : Type*} [Field F] (z : V → V → ℕ) (Vk : Finset V) (disp : V → V → Prop) (f : ℕ)
    {ρ : ℕ} (c : Coding z ρ F) : Prop :=
  ∀ B : Finset V, #B ≤ f → (∀ v, v ∉ Vk → v ∈ B) → (∀ a b, disp a b → a ∈ B ∨ b ∈ B) →
    ∀ (X : V → Fin ρ → F) (Y : Sym z → F),
      (∀ s : Sym z, s.tail ∉ B → Y s = code c s (X s.tail)) →
      (∀ s : Sym z, s.head ∉ B → Y s = code c s (X s.head)) →
      ∀ i, i ∉ B → ∀ j, j ∉ B → X i = X j

/-- The set `Ω_k` of Section 3: node sets of size `m = n - f` of `G_k` containing no pair found in
dispute so far (the subgraphs `H` are the induced subgraphs on these sets). -/
noncomputable def Omega (Vk : Finset V) (disp : V → V → Prop) (m : ℕ) : Finset (Finset V) :=
  by classical exact (Vk.powersetCard m).filter fun H => ∀ a ∈ H, ∀ b ∈ H, ¬ disp a b

omit [DecidableEq V] in
theorem mem_Omega {Vk : Finset V} {disp : V → V → Prop} {m : ℕ} {H : Finset V} :
    H ∈ Omega Vk disp m ↔ (H ⊆ Vk ∧ #H = m) ∧ ∀ a ∈ H, ∀ b ∈ H, ¬ disp a b := by
  classical
  unfold Omega
  rw [Finset.mem_filter, Finset.mem_powersetCard]

/-- `ρ` edge-disjoint unit-capacity spanning trees of the undirected graph `H̄` (Appendix C.1).

The nodes of `H` are enumerated as `node 0, …, node w` (`node (last w)` plays the role of the
paper's node `n - f`). Tree `q` consists of the `w` coded symbols `sym (r, q)`, `r < w`, whose
links, with directions forgotten, connect all of `H`; different trees use different coded symbols
(`sym_inj`), i.e. together they respect the link capacities. By the Nash-Williams–Tutte theorem
(cited as [16] in the paper), such a packing exists for every `H ∈ Ω_k` as soon as `ρ ≤ U_k / 2`. -/
structure TreePacking (z : V → V → ℕ) (H : Finset V) (ρ : ℕ) where
  /-- Number of non-root nodes, `|H| - 1`. -/
  w : ℕ
  /-- Enumeration of the nodes of `H`. -/
  node : Fin (w + 1) ↪ V
  mem_iff : ∀ v, v ∈ H ↔ ∃ i, node i = v
  /-- The coded symbol used by edge `r` of tree `q`. -/
  sym : Fin w × Fin ρ → Sym z
  sym_inj : Function.Injective sym
  tail_mem : ∀ x, (sym x).tail ∈ H
  head_mem : ∀ x, (sym x).head ∈ H
  /-- Every tree is spanning: its undirected edges connect the root to every node of `H`. -/
  connected : ∀ q : Fin ρ, ∀ v ∈ H, Relation.ReflTransGen
    (fun a b => ∃ r, ((sym (r, q)).tail = a ∧ (sym (r, q)).head = b) ∨
      ((sym (r, q)).tail = b ∧ (sym (r, q)).head = a)) (node (Fin.last w)) v

/-- The determinant of a matrix of polynomials of total degree `≤ 1` has total degree at most its
size. -/
theorem totalDegree_det_le {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι (MvPolynomial σ R)) (h : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun π _ => ?_)
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (π i) i).totalDegree ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => h _ _
    _ = Fintype.card ι := by simp

namespace TreePacking

variable {z : V → V → ℕ} {H : Finset V} {ρ : ℕ} (P : TreePacking z H ρ)

/-- The root of the packing (the paper's node `n - f`). -/
def root : V := P.node (Fin.last P.w)

omit [DecidableEq V] in
theorem card_eq : #H = P.w + 1 := by
  have : H = univ.map P.node := by
    ext v; simp [P.mem_iff]
  have h2 : #H = #(univ.map P.node) := congrArg _ this
  rw [h2, card_map, card_univ, Fintype.card_fin]

/-- Incidence coefficient of the coded symbol `s` at non-root node `i`: `+1` at its sender, `-1` at
its receiver (the matrices `B_e` / `A_q` of Appendix C). -/
def inc {R : Type*} [Ring R] (s : Sym z) (i : Fin P.w) : R :=
  (if s.tail = P.node i.castSucc then 1 else 0) - (if s.head = P.node i.castSucc then 1 else 0)

/-- The square matrix `M̃_H` of Appendix C.1 (rows: (non-root node `i`, coordinate `p`); columns:
(edge `r`, tree `q`)): `M̃_H = [A_q S_{q,p}]`. -/
def M {R : Type*} [CommRing R] (c : Coding z ρ R) : Matrix (Fin P.w × Fin ρ) (Fin P.w × Fin ρ) R :=
  fun ip rq => P.inc (P.sym rq) ip.1 * c (P.sym rq, ip.2)

/-- The adjacency matrix `A_q` of tree `q` (Appendix C.1). -/
def A {R : Type*} [Ring R] (q : Fin ρ) : Matrix (Fin P.w) (Fin P.w) R :=
  fun i r => P.inc (P.sym (r, q)) i

/-- Extension of a vector on non-root nodes by `0` at the root (and outside `H`). -/
def ext {R : Type*} [Ring R] (D : Fin P.w → R) (v : V) : R :=
  ∑ i, D i * (if v = P.node i.castSucc then 1 else 0)

theorem ext_node_castSucc {R : Type*} [Ring R] (D : Fin P.w → R) (i : Fin P.w) :
    P.ext D (P.node i.castSucc) = D i := by
  unfold ext
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : P.node i.castSucc ≠ P.node j.castSucc := fun h =>
      hj (Fin.castSucc_injective _ (P.node.injective h)).symm
    simp [this]
  · simp

theorem ext_root {R : Type*} [Ring R] (D : Fin P.w → R) : P.ext D P.root = 0 := by
  unfold ext root
  refine Finset.sum_eq_zero fun i _ => ?_
  have : P.node (Fin.last P.w) ≠ P.node i.castSucc := fun h =>
    (Fin.castSucc_lt_last i).ne' (P.node.injective h)
  simp [this]

theorem sum_mul_inc {R : Type*} [CommRing R] (D : Fin P.w → R) (s : Sym z) :
    ∑ i, D i * P.inc s i = P.ext D s.tail - P.ext D s.head := by
  simp only [inc, ext, mul_sub, Finset.sum_sub_distrib]

/-- **Appendix C.3.** The adjacency matrix of a spanning tree is invertible (over any field).
(The paper's argument for this is incomplete; we prove it from connectivity.) -/
theorem det_A_ne_zero {F : Type*} [Field F] (q : Fin ρ) : (P.A q : Matrix _ _ F).det ≠ 0 := by
  intro hdet
  have hinj : ¬ Function.Injective (P.A q : Matrix _ _ F).vecMul := by
    rw [Matrix.vecMul_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hdet]
    exact not_isUnit_zero
  apply hinj
  -- injectivity of `D ↦ D A_q` via `D A_q = 0 → D = 0`
  have key : ∀ D : Fin P.w → F, Matrix.vecMul D (P.A q) = 0 → D = 0 := by
    intro D hD
    have hedge : ∀ r, P.ext D (P.sym (r, q)).tail = P.ext D (P.sym (r, q)).head := by
      intro r
      have := congrFun hD r
      simp only [Matrix.vecMul, dotProduct, A, Pi.zero_apply] at this
      rw [P.sum_mul_inc] at this
      exact sub_eq_zero.mp this
    have hreach : ∀ v, Relation.ReflTransGen
        (fun a b => ∃ r, ((P.sym (r, q)).tail = a ∧ (P.sym (r, q)).head = b) ∨
          ((P.sym (r, q)).tail = b ∧ (P.sym (r, q)).head = a)) (P.node (Fin.last P.w)) v →
        P.ext D v = 0 := by
      intro v hv
      induction hv with
      | refl => exact P.ext_root D
      | tail _ hab ih =>
        obtain ⟨r, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hab
        · rw [← h2, ← hedge r, h1, ih]
        · rw [← h1, hedge r, h2, ih]
    have hall : ∀ v ∈ H, P.ext D v = 0 := fun v hv => hreach v (P.connected q v hv)
    funext i
    rw [← P.ext_node_castSucc D i]
    exact hall _ ((P.mem_iff _).2 ⟨_, rfl⟩)
  intro D₁ D₂ h
  have := key (D₁ - D₂) (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr h)
  exact sub_eq_zero.mp this

/-- Extending the differences `D_i = X_i - X_{root}` by `0` at the root gives `X_v - X_root` on all
of `H`. -/
theorem ext_sub_root {R : Type*} [Ring R] (g : V → R) {v : V} (hv : v ∈ H) :
    P.ext (fun i => g (P.node i.castSucc) - g P.root) v = g v - g P.root := by
  obtain ⟨j, rfl⟩ := (P.mem_iff v).1 hv
  induction j using Fin.lastCases with
  | last => rw [show P.node (Fin.last P.w) = P.root from rfl, P.ext_root, sub_self]
  | cast i => rw [P.ext_node_castSucc]

/-- **Appendix C.1, reduction to `M_H`.** If `M̃_H` is invertible, then whenever all checks of
Algorithm 1 on the coded symbols of the trees pass between the nodes of `H` (honest sender and
honest receiver agree on every coded symbol), all nodes of `H` hold the same value. -/
theorem eq_root_of_det_ne_zero {F : Type*} [Field F] {c : Coding z ρ F} (hc : (P.M c).det ≠ 0)
    (X : V → Fin ρ → F)
    (hX : ∀ x, code c (P.sym x) (X (P.sym x).tail) = code c (P.sym x) (X (P.sym x).head)) :
    ∀ v ∈ H, X v = X P.root := by
  have hinj : Function.Injective (P.M c).vecMul := by
    rw [Matrix.vecMul_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    exact hc.isUnit
  set D : Fin P.w × Fin ρ → F := fun ip => X (P.node ip.1.castSucc) ip.2 - X P.root ip.2
  have hD : Matrix.vecMul D (P.M c) = Matrix.vecMul 0 (P.M c) := by
    rw [Matrix.zero_vecMul]
    funext rq
    set s := P.sym rq
    have hs := hX rq
    simp only [Matrix.vecMul, dotProduct, M, Pi.zero_apply]
    calc ∑ ip : Fin P.w × Fin ρ, D ip * (P.inc s ip.1 * c (s, ip.2))
        = ∑ p, c (s, p) * ∑ i, (fun i => X (P.node i.castSucc) p - X P.root p) i * P.inc s i := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by simp [D]; ring
      _ = ∑ p, c (s, p) * ((X s.tail p - X P.root p) - (X s.head p - X P.root p)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [P.sum_mul_inc, P.ext_sub_root (fun v => X v p) (P.tail_mem rq),
            P.ext_sub_root (fun v => X v p) (P.head_mem rq)]
      _ = code c s (X s.tail) - code c s (X s.head) := by
          simp only [code, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ = 0 := sub_eq_zero.mpr hs
  have h0 := hinj hD
  intro v hv
  obtain ⟨j, rfl⟩ := (P.mem_iff v).1 hv
  induction j using Fin.lastCases with
  | last => rfl
  | cast i =>
    funext p
    have := congrFun h0 (i, p)
    simpa [D, sub_eq_zero] using this

/-- The special coding used to show that `det M̃_H` is not the zero polynomial: the coded symbol of
edge `r` of tree `q` carries exactly the `q`-th coordinate. -/
noncomputable def specialCoding {F : Type*} [Field F] : Coding z ρ F := fun sp =>
  by classical exact if h : ∃ x, P.sym x = sp.1 then (if sp.2 = h.choose.2 then 1 else 0) else 0

theorem M_specialCoding {F : Type*} [Field F] :
    P.M (P.specialCoding (F := F)) = Matrix.blockDiagonal fun q => P.A q := by
  ext ⟨i, p⟩ ⟨r, q⟩
  have h : ∃ x, P.sym x = P.sym (r, q) := ⟨_, rfl⟩
  have hch : h.choose = (r, q) := P.sym_inj h.choose_spec
  simp only [M, specialCoding, Matrix.blockDiagonal_apply, A]
  rw [dite_eq_left_of_eq_true (eq_true h), hch]
  split_ifs <;> simp_all

/-- `det M̃_H` is not identically zero: at the special coding it is `∏_q det A_q ≠ 0`. -/
theorem det_M_specialCoding_ne_zero {F : Type*} [Field F] :
    (P.M (P.specialCoding (F := F))).det ≠ 0 := by
  rw [M_specialCoding, Matrix.det_blockDiagonal]
  exact Finset.prod_ne_zero_iff.mpr fun q _ => P.det_A_ne_zero q

/-- `M̃_H` with the coding coefficients as formal variables. -/
noncomputable def Mpoly (F : Type*) [Field F] :
    Matrix (Fin P.w × Fin ρ) (Fin P.w × Fin ρ) (MvPolynomial (Sym z × Fin ρ) F) :=
  P.M fun v => MvPolynomial.X v

theorem eval_det_Mpoly {F : Type*} [Field F] (c : Coding z ρ F) :
    MvPolynomial.eval c (P.Mpoly F).det = (P.M c).det := by
  rw [RingHom.map_det]
  congr 1
  ext ip rq
  simp [Mpoly, M, inc, apply_ite (MvPolynomial.eval c)]

theorem totalDegree_det_Mpoly_le {F : Type*} [Field F] :
    (P.Mpoly F).det.totalDegree ≤ P.w * ρ := by
  have h := totalDegree_det_le (P.Mpoly F) fun ip rq => by
    have : P.inc (R := MvPolynomial (Sym z × Fin ρ) F) (P.sym rq) ip.1 =
        MvPolynomial.C (P.inc (P.sym rq) ip.1) := by
      simp only [inc, map_sub, apply_ite MvPolynomial.C, map_one, map_zero]
    simp only [Mpoly, M, this]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  simpa using h

end TreePacking

end Podc.ByzantineLinearCoding
