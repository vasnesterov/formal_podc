import Papers.PODC2011.CompactPolicyRouting.Tree
import Papers.PODC2011.CompactPolicyRouting.Product
import Papers.PODC2011.CompactPolicyRouting.NoStretch

/-!
# Compressibility characterizations (Theorems 4.9, 4.11, Lemma 4.12) and the shortest-widest-path application

* `theorem_4_9`: a selective monotone algebra needs no more local memory than tree routing. Routing over a tree
  with `O(log n)` bits ([74] Fraigniaud–Gavoille) is a hypothesis (`TreeRoutingScheme`); with it `A` is compressible
  (`theorem_4_9_compressible`).
* `lemma_4_12`: if `A` has a delimited strictly monotone subalgebra containing a finite weight, then
  `M_S(n) ≤ M_A(n)` for the shortest-path algebra `S` (`powEmbedding`: `n ↦ wⁿ` embeds `S` into `A`), hence
  `A` is incompressible given Proposition 4.8 (Fraigniaud–Gavoille: `S` is incompressible), which is a hypothesis.
* `theorem_4_11`: delimited + strictly monotone (with a finite weight) ⇒ incompressible (given Proposition 4.8).
* `shortestWidest_no_compact_stretch`: Theorem 4.17 applies to shortest-widest-path routing (Section 4.4.2).
-/

namespace Podc.CompactPolicyRouting

open SimpleGraph RoutingAlgebra Filter OrdSemigroup

universe u

variable {W : Type u} [LinearOrder W]

/-! ### Theorem 4.9 -/

/-- The cited tree-routing result [74], as a hypothesis: on every graph `G` and every spanning tree `T ≤ G`, some
routing function routes every packet along the tree path, with labels below `n ^ c` and local memory `≤ f n`. -/
def TreeRoutingScheme (mem : MemoryMeasure) (c : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V) (T : SimpleGraph V) (hT : T ≤ G), T.IsTree →
    ∃ R : RoutingFunction G, R.LabelsBounded c (Nat.card V) ∧
      (∀ (s t : V) (p : T.Walk s t), p.IsPath → R.Generates (R.label t) (p.mapLe hT)) ∧
      ∀ u, mem (R.route u) ≤ f (Nat.card V)

/-- Theorem 4.9 of [paper] (memory form): if `A` is selective and monotone, then `M_A(n) ≤ f(n)` whenever trees
can be routed with `f(n)` bits (`TreeRoutingScheme`). The proof uses Lemma 4.10. -/
theorem theorem_4_9 {A : RoutingAlgebra W} (hM : A.IsMonotone) (hS : A.IsSelective)
    {mem : MemoryMeasure} {c : ℕ} {f : ℕ → ℕ} (htree : TreeRoutingScheme mem c f) (n : ℕ) :
    memReq A mem c n ≤ f n := by
  refine memReq_le fun V _ hV G hG wt => ?_
  obtain ⟨T, hTG, hT, hpref⟩ := exists_preferred_spanningTree hM hS hG wt
  obtain ⟨R, hlab, hgen, hmem⟩ := htree V G T hTG hT
  refine iInf₂_le_of_le R ⟨fun s t _ _ => ?_, hV ▸ hlab⟩ ?_
  · obtain ⟨p, hp⟩ := (hT.existsUnique_path s t).exists
    exact ⟨p.mapLe hTG, hpref s t p hp, hgen s t p hp⟩
  · exact iSup_le fun u => by rw [← hV]; exact_mod_cast hmem u

/-- Theorem 4.9 of [paper]: selective monotone algebras are compressible, given `O(log n)`-bit tree routing. -/
theorem theorem_4_9_compressible {A : RoutingAlgebra W} (hM : A.IsMonotone) (hS : A.IsSelective)
    {mem : MemoryMeasure} {c : ℕ} {f : ℕ → ℕ} (htree : TreeRoutingScheme mem c f)
    (hf : ∃ K, ∀ n, f n ≤ K * (Nat.log 2 n + 1)) : Compressible (memReq A mem c) := by
  rintro ⟨C, hC, hev⟩
  obtain ⟨K, hK⟩ := hf
  obtain ⟨n, hn, hlog⟩ := (hev.and (eventually_log_le (C * K))).exists
  have h1 : (n : ℕ∞) ≤ C * (f n : ℕ) := hn.trans (by gcongr; exact theorem_4_9 hM hS htree n)
  have h2 : n ≤ C * f n := by exact_mod_cast h1
  have h3 : C * f n ≤ C * (K * (Nat.log 2 n + 1)) := Nat.mul_le_mul_left C (hK n)
  have : C * (K * (Nat.log 2 n + 1)) = C * K * (Nat.log 2 n + 1) := by ring
  omega

/-! ### Non-vacuity: destination-based routing along a spanning tree exists in the model -/

/-- Local port numbering `1, …, δ(u)` of the neighbours of `u`. -/
noncomputable def stdPort {V : Type} (G : SimpleGraph V) [∀ u, Finite (G.neighborSet u)] (u v : V) : ℕ :=
  open Classical in
  if h : G.Adj u v then (Finite.equivFin (G.neighborSet u) ⟨v, h⟩ : ℕ) + 1 else 0

/-- Destination-based routing along a spanning tree `T ≤ G` (headers = destination labels) is a routing function
of the model of Section 4.2 with `log n`-bit labels; it generates exactly the tree paths. Hence
`TreeRoutingScheme mem 1 f` holds as soon as these routing functions have memory `≤ f n` (e.g. `mem = 0`, `f = 0`):
the hypothesis of `theorem_4_9` is consistent. -/
theorem exists_treeRouting {V : Type} [Finite V] (G : SimpleGraph V) (T : SimpleGraph V) (hT : T ≤ G)
    (hTt : T.IsTree) : ∃ R : RoutingFunction G, R.LabelsBounded 1 (Nat.card V) ∧
      ∀ (s t : V) (p : T.Walk s t), p.IsPath → R.Generates (R.label t) (p.mapLe hT) := by
  classical
  let e := Finite.equivFin V
  -- the next hop from `u` towards `t` on the unique tree path
  let path : (u t : V) → T.Walk u t := fun u t => (hTt.existsUnique_path u t).exists.choose
  have hpath : ∀ u t, (path u t).IsPath := fun u t => (hTt.existsUnique_path u t).exists.choose_spec
  have huniq : ∀ u t (q : T.Walk u t), q.IsPath → q = path u t := fun u t q hq =>
    (hTt.existsUnique_path u t).unique hq (hpath u t)
  let R : RoutingFunction G :=
    { label := fun v => e v
      label_injective := fun a b h => e.injective (Fin.ext h)
      port := stdPort G
      port_injOn := by
        intro u a ha b hb h
        simp only [stdPort, dif_pos (show G.Adj u a from ha), dif_pos (show G.Adj u b from hb),
          add_left_inj, Fin.val_inj] at h
        exact congrArg Subtype.val ((Finite.equivFin _).injective h)
      port_mem := by
        intro u v h
        simp only [stdPort, dif_pos h, Set.mem_Icc]
        refine ⟨by omega, ?_⟩
        have := (Finite.equivFin (G.neighborSet u) ⟨v, h⟩).isLt
        have h2 : Nat.card (G.neighborSet u) = (G.neighborSet u).ncard := Nat.card_coe_set_eq _
        omega
      route := fun u h => if hh : h < Nat.card V then (h, stdPort G u (path u (e.symm ⟨h, hh⟩)).snd)
        else (h, 0) }
  refine ⟨R, fun v => by simp [R], fun s t p hp => ?_⟩
  induction p with
  | nil => trivial
  | @cons a x t hax q ih =>
    have hq : q.IsPath := hp.of_cons
    have hsnd : (path a t).snd = x := by rw [← huniq a t _ hp]; simp
    simp only [Walk.mapLe, Walk.map_cons, RoutingFunction.generates_cons]
    have hlt : (e t : ℕ) < Nat.card V := (e t).isLt
    refine ⟨?_, ?_⟩
    · simp only [R, dif_pos hlt, Fin.eta]
      have key : ∀ y, y = t → stdPort G a (path a y).snd = stdPort G a x := by
        rintro y rfl; rw [hsnd]
      exact key _ (e.symm_apply_apply t)
    · simp only [R, dif_pos hlt]
      exact ih hq

/-- `TreeRoutingScheme` is satisfiable (for the trivial memory measure), so `theorem_4_9` is not vacuous. -/
theorem treeRoutingScheme_zero : TreeRoutingScheme (fun _ => 0) 1 (fun _ => 0) := by
  intro V _ G T hT hTt
  obtain ⟨R, hl, hg⟩ := exists_treeRouting G T hT hTt
  exact ⟨R, hl, hg, fun _ => le_rfl⟩

/-! ### Lemma 4.12 and Theorem 4.11 -/

theorem spow_lt_succ {A : RoutingAlgebra W} {S : Set W} (hclosed : ∀ a ∈ S, ∀ b ∈ S, A.op a b ∈ S)
    (hSM : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → a < A.op b a) {w : W} (hw : w ∈ S) (hfin : ∀ j, A.spow w j ≠ A.phi)
    (j : ℕ) : A.spow w j < A.spow w (j + 1) := by
  have hmem : ∀ j, A.spow w j ∈ S := by
    intro j; induction j with
    | zero => exact hw
    | succ j ih => exact hclosed _ ih _ hw
  show A.spow w j < A.op (A.spow w j) w
  rw [A.op_comm]; exact hSM _ (hmem j) _ hw (hfin j)

/-- The embedding `n ↦ wⁿ` of the shortest-path algebra `S = (ℤ⁺, ∞, +, ≤)` into `A`, for a finite weight `w` of a
delimited strictly monotone subalgebra (proof of Lemma 4.12). -/
def powEmbedding {A : RoutingAlgebra W} {S : Set W} (hclosed : ∀ a ∈ S, ∀ b ∈ S, A.op a b ∈ S)
    (hD : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → b ≠ A.phi → A.op a b ≠ A.phi)
    (hSM : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → a < A.op b a) {w : W} (hw : w ∈ S) (hwφ : w ≠ A.phi) :
    AlgEmbedding shortestPath A :=
  have hmem : ∀ j, A.spow w j ∈ S := by
    intro j; induction j with
    | zero => exact hw
    | succ j ih => exact hclosed _ ih _ hw
  have hfin : ∀ j, A.spow w j ≠ A.phi := by
    intro j; induction j with
    | zero => exact hwφ
    | succ j ih => exact hD _ (hmem j) _ hw ih hwφ
  have hmono : StrictMono (A.spow w) := strictMono_nat_of_lt_succ (spow_lt_succ hclosed hSM hw hfin)
  { toFun := fun x => WithTop.recTopCoe A.phi (fun n : ℕ+ => A.spow w ((n : ℕ) - 1)) x
    strictMono := by
      intro x y hxy
      induction x using WithTop.recTopCoe with
      | top => exact absurd hxy (not_lt.2 le_top)
      | coe a =>
        induction y using WithTop.recTopCoe with
        | top => exact A.lt_phi (hfin _)
        | coe b =>
          have : (a : ℕ) < b := by exact_mod_cast WithTop.coe_lt_coe.1 hxy
          exact hmono (by have := a.pos; omega)
    map_op := by
      intro x y
      induction x using WithTop.recTopCoe with
      | top => simp [shortestPath, A.phi_op]
      | coe a =>
        induction y using WithTop.recTopCoe with
        | top => simp [shortestPath, A.op_phi]
        | coe b =>
          simp only [shortestPath, withTop_op_coe, WithTop.recTopCoe_coe]
          rw [← spow_add]
          congr 1
          show ((a + b : ℕ+) : ℕ) - 1 = _
          rw [PNat.add_coe]; have := a.pos; have := b.pos; omega
    map_phi := rfl }

/-- Lemma 4.12 of [paper] (memory form): if `A` contains a delimited strictly monotone subalgebra `S` with a finite
weight, then routing in `A` needs at least as much local memory as shortest-path routing: `M_S(n) ≤ M_A(n)`. -/
theorem lemma_4_12_memReq {A : RoutingAlgebra W} {S : Set W} (hclosed : ∀ a ∈ S, ∀ b ∈ S, A.op a b ∈ S)
    (hD : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → b ≠ A.phi → A.op a b ≠ A.phi)
    (hSM : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → a < A.op b a) (hne : ∃ w ∈ S, w ≠ A.phi)
    (mem : MemoryMeasure) (c n : ℕ) : memReq shortestPath mem c n ≤ memReq A mem c n := by
  obtain ⟨w, hw, hwφ⟩ := hne
  exact (powEmbedding hclosed hD hSM hw hwφ).memReq_le_memReq mem c n

/-- Lemma 4.12 of [paper]: a delimited strictly monotone subalgebra (with a finite weight) makes `A`
incompressible, given Proposition 4.8 (the shortest-path algebra is incompressible, Fraigniaud–Gavoille). -/
theorem lemma_4_12 {A : RoutingAlgebra W} {S : Set W} (hclosed : ∀ a ∈ S, ∀ b ∈ S, A.op a b ∈ S)
    (hD : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → b ≠ A.phi → A.op a b ≠ A.phi)
    (hSM : ∀ a ∈ S, ∀ b ∈ S, a ≠ A.phi → a < A.op b a) (hne : ∃ w ∈ S, w ≠ A.phi)
    {mem : MemoryMeasure} {c : ℕ} (prop_4_8 : Incompressible (memReq shortestPath mem c)) :
    Incompressible (memReq A mem c) :=
  prop_4_8.mono fun n => lemma_4_12_memReq hclosed hD hSM hne mem c n

/-- Theorem 4.11 of [paper]: a delimited strictly monotone algebra (with a finite weight) is incompressible, given
Proposition 4.8. -/
theorem theorem_4_11 {A : RoutingAlgebra W} (hD : A.IsDelimited) (hSM : A.IsStrictlyMonotone)
    (hne : ∃ w : W, w ≠ A.phi) {mem : MemoryMeasure} {c : ℕ}
    (prop_4_8 : Incompressible (memReq shortestPath mem c)) : Incompressible (memReq A mem c) :=
  lemma_4_12 (S := Set.univ) (fun _ _ _ _ => trivial) (fun a _ b _ => hD a b)
    (fun a _ b _ => hSM a b) (by obtain ⟨w, hw⟩ := hne; exact ⟨w, trivial, hw⟩) prop_4_8

/-- The degenerate algebra `({φ}, φ, ⊕, ⪯)` is delimited and (vacuously) strictly monotone, but every routing
function implements it (there are no traversable paths), so it needs no routing memory: the finite weight in
`theorem_4_11` cannot be dropped. -/
theorem trivial_algebra (A : RoutingAlgebra Unit) :
    A.IsDelimited ∧ A.IsStrictlyMonotone ∧
      ∀ (V : Type) (G : SimpleGraph V) (wt : Sym2 V → Unit) (R : RoutingFunction G), Implements A wt R := by
  refine ⟨fun a b ha => absurd (Subsingleton.elim a A.phi) ha, fun a b ha =>
    absurd (Subsingleton.elim a A.phi) ha, fun V G wt R s t _ ⟨p, _, hp⟩ => ?_⟩
  exfalso
  rcases Ext.cases (weight A wt p) with h | ⟨a, h⟩
  · cases p with
    | nil => exact absurd (rfl : s = s) ‹s ≠ s›
    | cons h' q => rw [weight_cons] at h; exact emb_mul_ne_one _ _ h
  · exact hp (by rw [h, Subsingleton.elim a A.phi])

/-- Consistency of the Proposition 4.8 hypothesis of `lemma_4_12` / `theorem_4_11`: for the measure that
assigns `⊤` to every local function (allowed, since a code length may be infinite) every algebra is
incompressible. This only shows that the hypothesis is satisfiable; the content of Lemma 4.12 is
`lemma_4_12_memReq`. -/
theorem incompressible_memReq_top {W' : Type} [LinearOrder W'] [Inhabited W'] (A : RoutingAlgebra W') (c : ℕ) :
    Incompressible (memReq A (fun _ => ⊤) c) := by
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h := le_memReq (A := A) (mem := fun _ => ⊤) (c := c) (n := n) (V := Fin n) (by simp)
    (⊤ : SimpleGraph (Fin n)) (SimpleGraph.connected_top_iff.2 ⟨⟨0, hn⟩⟩) (fun _ => default)
  have : minMem (⊤ : SimpleGraph (Fin n)) (fun _ => ⊤)
      (fun R => Implements A (fun _ => default) R ∧ R.LabelsBounded c n) = ⊤ := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simp [minMem, RoutingFunction.maxMem]
  rw [this, top_le_iff] at h
  rw [h]; simp

/-! ### Shortest-widest path (Section 4.4.2) -/

/-- Section 4.4.2 of [paper]: shortest-widest-path routing admits no compact stretch-`k` routing scheme for any
`k ≥ 1` (Theorem 4.17 with `wᵢ = (i, (2k)^{i-1})`). -/
theorem shortestWidest_no_compact_stretch {k : ℕ} (hk : 1 ≤ k) {mem : MemoryMeasure}
    (hmem : CodeLength mem) (c : ℕ) : Incompressible (memReqStretch shortestWidest mem c k) :=
  theorem_4_17 (A := shortestWidest) shortestWidest_props.2.1 hk
    (fun p => by obtain ⟨w, -, hw⟩ := shortestWidest_condition_4_2 k hk p; exact ⟨w, hw⟩) hmem c

/-! ### Table 4.2, "Local memory" column (given the cited results) -/

/-- Table 4.2: widest-path routing is compressible (Theorem 4.9), given `O(log n)`-bit tree routing. -/
theorem widestPath_compressible {mem : MemoryMeasure} {c : ℕ} {f : ℕ → ℕ}
    (htree : TreeRoutingScheme mem c f) (hf : ∃ K, ∀ n, f n ≤ K * (Nat.log 2 n + 1)) :
    Compressible (memReq widestPath mem c) :=
  theorem_4_9_compressible widestPath_props.2.2.2.1 widestPath_props.2.1 htree hf

/-- Table 4.2: shortest-widest-path routing is incompressible (Theorem 4.11), given Proposition 4.8. -/
theorem shortestWidest_incompressible {mem : MemoryMeasure} {c : ℕ}
    (prop_4_8 : Incompressible (memReq shortestPath mem c)) :
    Incompressible (memReq shortestWidest mem c) :=
  theorem_4_11 shortestWidest_props.1 shortestWidest_props.2.2.1 
    ⟨((toLex (OrderDual.toDual (1 : ℕ+), (1 : ℕ+)) : Lex (ℕ+ᵒᵈ × ℕ+)) : WithTop _), WithTop.coe_ne_top⟩
    prop_4_8

end Podc.CompactPolicyRouting
