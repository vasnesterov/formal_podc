import Papers.PODC2011.CompactPolicyRouting.Paths

/-!
# Policy routing functions and local memory (Section 4.2, Definition 4.5)

A *policy routing function* on a graph `G` (after Fraigniaud–Gavoille) consists of
* injective node labels `L_V : V → ℕ` (the address of a node, bounded by `n ^ c`, i.e. `c log n` bits),
* local port labels `L_E(u, ·)`: a bijection from the neighbours of `u` onto `{1, …, δ(u)}`,
* local routing functions `R_u : ℕ → ℕ × ℕ`, mapping a header `h` to a new header and an outgoing port.

A packet for `t` starts with header `L_V(t)` at `s`; `Generates R h p` says that the walk `p` is the one produced
by the successive application of the local routing functions. `R` *implements* `A` on `(G, wt)` if for every pair
`s ≠ t` joined by a traversable path the generated walk is a preferred path.

The memory needed to store a local routing function is measured by an arbitrary function
`mem : (ℕ → ℕ × ℕ) → ℕ∞` (e.g. the length of the shortest description with respect to a fixed decoder, `⊤` for
functions without a finite description); the paper says "the minimum number of bits needed to encode `R_u`" without
fixing the encoding. The value `⊤` is needed: there are uncountably many functions `ℕ → ℕ × ℕ`, so no `ℕ`-valued
measure can have fewer than `2^b` functions of size `< b` (see `not_codeLength_of_ne_top`). All statements below hold for every `mem`;
where a counting argument needs that few functions have short codes we assume `CodeLength mem`.

`memReq A mem c n` is Definition 4.5: the maximum over connected weighted graphs on `n` nodes of the minimum
over routing functions implementing `A` of the maximum local memory.
-/

namespace Podc.CompactPolicyRouting

open SimpleGraph RoutingAlgebra Filter

universe u

/-- A policy routing function on `G` (Section 4.2.1). -/
structure RoutingFunction {V : Type} (G : SimpleGraph V) where
  /-- Node labels (addresses). -/
  label : V → ℕ
  label_injective : Function.Injective label
  /-- `port u v` is the local label at `u` of the edge `uv`. -/
  port : V → V → ℕ
  port_injOn : ∀ u, Set.InjOn (port u) (G.neighborSet u)
  port_mem : ∀ u v, G.Adj u v → port u v ∈ Set.Icc 1 (G.neighborSet u).ncard
  /-- The local routing function `R_u : header ↦ (new header, outgoing port)`. -/
  route : V → ℕ → ℕ × ℕ

namespace RoutingFunction

variable {V : Type} {G : SimpleGraph V} (R : RoutingFunction G)

/-- `R.Generates h p`: starting at the first node of `p` with header `h`, the successive application of the local
routing functions forwards the packet along `p` (and `p` ends at the destination). -/
def Generates : {u t : V} → ℕ → G.Walk u t → Prop
  | _, _, _, .nil => True
  | u, _, h, .cons (v := x) _ p => (R.route u h).2 = R.port u x ∧ Generates (R.route u h).1 p

@[simp] theorem generates_nil {u : V} (h : ℕ) : R.Generates h (Walk.nil : G.Walk u u) := trivial

@[simp] theorem generates_cons {u x t : V} (h : ℕ) (hadj : G.Adj u x) (p : G.Walk x t) :
    R.Generates h (Walk.cons hadj p) ↔ (R.route u h).2 = R.port u x ∧ R.Generates (R.route u h).1 p :=
  Iff.rfl

/-- The generated walk is unique (ports are injective and routing is deterministic). -/
theorem generates_unique {u t : V} {h : ℕ} {p q : G.Walk u t} (hp : R.Generates h p)
    (hq : R.Generates h q) (hpp : p.IsPath) (hqp : q.IsPath) : p = q := by
  induction p generalizing h with
  | nil => exact (Walk.isPath_iff_eq_nil.1 hqp).symm
  | @cons a x t hax p ih =>
    cases q with
    | nil => exact absurd hpp (by simp at hpp ⊢)
    | @cons _ y _ hay q =>
      have hxy : x = y := R.port_injOn a hax hay (hp.1.symm.trans hq.1)
      subst hxy
      rw [ih hp.2 hq.2 hpp.of_cons hqp.of_cons]

end RoutingFunction

variable {W : Type u} [LinearOrder W]

/-- A traversable `s – t` path exists (a path of weight `≠ φ`). -/
def Traversable (A : RoutingAlgebra W) {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W) (s t : V) :
    Prop :=
  ∃ p : G.Walk s t, p.IsPath ∧ weight A wt p ≠ A.emb A.phi

/-- `R` implements `A` on `(G, wt)`: for every `s ≠ t` joined by a traversable path, the walk generated from `s`
with initial header `L_V(t)` is a preferred `s – t` path. -/
def Implements (A : RoutingAlgebra W) {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W)
    (R : RoutingFunction G) : Prop :=
  ∀ s t, s ≠ t → Traversable A (G := G) wt s t →
    ∃ p : G.Walk s t, IsPreferred A wt p ∧ R.Generates (R.label t) p

/-- A measure of the number of bits needed to store a local routing function. -/
abbrev MemoryMeasure := (ℕ → ℕ × ℕ) → ℕ∞

/-- The maximum local memory `max_u M(R, u)` of a routing function. -/
noncomputable def RoutingFunction.maxMem {V : Type} {G : SimpleGraph V} (mem : MemoryMeasure)
    (R : RoutingFunction G) : ℕ∞ :=
  ⨆ u, mem (R.route u)

/-- The labels of `R` fit in `c log n` bits (`L_V(v) < n ^ c`). -/
def RoutingFunction.LabelsBounded {V : Type} {G : SimpleGraph V} (R : RoutingFunction G) (c n : ℕ) :
    Prop :=
  ∀ v, R.label v < n ^ c

/-- The minimum over routing functions with `P` of the maximum local memory. -/
noncomputable def minMem {V : Type} (G : SimpleGraph V) (mem : MemoryMeasure)
    (P : RoutingFunction G → Prop) : ℕ∞ :=
  ⨅ (R : RoutingFunction G) (_ : P R), R.maxMem mem

/-- Definition 4.5: `M_A(n) = max_{G ∈ 𝒢_n} min_{R implementing A on G} max_{u} M_A(R, u)`, the maximum ranging over
connected graphs on `n` nodes *and their edge weights*, and with node labels of `c log n` bits. -/
noncomputable def memReq (A : RoutingAlgebra W) (mem : MemoryMeasure) (c n : ℕ) : ℕ∞ :=
  ⨆ (V : Type) (_ : Finite V) (_ : Nat.card V = n) (G : SimpleGraph V) (_ : G.Connected)
    (wt : Sym2 V → W), minMem G mem (fun R => Implements A wt R ∧ R.LabelsBounded c n)

/-- `A` is incompressible if `M_A(n) = Ω(n)`. -/
def Incompressible (f : ℕ → ℕ∞) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (n : ℕ∞) ≤ C * f n

/-- `A` is compressible if it is not incompressible. -/
def Compressible (f : ℕ → ℕ∞) : Prop := ¬ Incompressible f

theorem Incompressible.mono {f g : ℕ → ℕ∞} (hf : Incompressible f) (hfg : ∀ n, f n ≤ g n) :
    Incompressible g := by
  obtain ⟨C, hC, h⟩ := hf
  exact ⟨C, hC, h.mono fun n hn => hn.trans (by gcongr; exact hfg n)⟩

theorem minMem_mono {V : Type} {G : SimpleGraph V} {mem : MemoryMeasure}
    {P Q : RoutingFunction G → Prop} (h : ∀ R, Q R → P R) : minMem G mem P ≤ minMem G mem Q :=
  le_iInf₂ fun R hR => iInf₂_le R (h R hR)

theorem le_memReq {A : RoutingAlgebra W} {mem : MemoryMeasure} {c n : ℕ} {V : Type} [Finite V]
    (hV : Nat.card V = n) (G : SimpleGraph V) (hG : G.Connected) (wt : Sym2 V → W) :
    minMem G mem (fun R => Implements A wt R ∧ R.LabelsBounded c n) ≤ memReq A mem c n :=
  le_iSup_of_le V <| le_iSup_of_le inferInstance <| le_iSup_of_le hV <| le_iSup_of_le G <|
    le_iSup_of_le hG <| le_iSup_of_le wt le_rfl

theorem memReq_le {A : RoutingAlgebra W} {mem : MemoryMeasure} {c n : ℕ} {b : ℕ∞}
    (h : ∀ (V : Type) [Finite V], Nat.card V = n → ∀ G : SimpleGraph V, G.Connected →
      ∀ wt : Sym2 V → W, minMem G mem (fun R => Implements A wt R ∧ R.LabelsBounded c n) ≤ b) :
    memReq A mem c n ≤ b :=
  iSup_le fun V => iSup_le fun _ => iSup_le fun hV => iSup_le fun G => iSup_le fun hG =>
    iSup_le fun wt => h V hV G hG wt

/-! ### Algebra embeddings preserve preferred paths (the reduction of Lemma 4.12) -/

section Embedding

variable {W' : Type*} [LinearOrder W'] {A : RoutingAlgebra W} {B : RoutingAlgebra W'}

/-- An embedding of routing algebras: an order embedding that is a semigroup homomorphism and maps `φ` to `φ`. -/
structure AlgEmbedding (B : RoutingAlgebra W') (A : RoutingAlgebra W) where
  toFun : W' → W
  strictMono : StrictMono toFun
  map_op : ∀ a b, toFun (B.op a b) = A.op (toFun a) (toFun b)
  map_phi : toFun B.phi = A.phi

namespace AlgEmbedding

variable (f : AlgEmbedding B A)

/-- The induced map on extended weights. -/
def ext (x : B.Ext) : A.Ext := WithBot.map f.toFun x

@[simp] theorem ext_emb (a : W') : f.ext (B.emb a) = A.emb (f.toFun a) := rfl

@[simp] theorem ext_one : f.ext 1 = 1 := rfl

theorem ext_mul (x y : B.Ext) : f.ext (x * y) = f.ext x * f.ext y := by
  rcases Ext.cases x with rfl | ⟨a, rfl⟩
  · simp
  rcases Ext.cases y with rfl | ⟨b, rfl⟩
  · simp
  · rw [emb_mul_emb, ext_emb, ext_emb, ext_emb, emb_mul_emb, f.map_op]

theorem ext_strictMono : StrictMono f.ext := f.strictMono.withBot_map

theorem ext_le_ext {x y : B.Ext} : f.ext x ≤ f.ext y ↔ x ≤ y := f.ext_strictMono.le_iff_le

theorem ext_injective : Function.Injective f.ext := f.ext_strictMono.injective

theorem weight_comp {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W') {s t : V} (p : G.Walk s t) :
    weight A (f.toFun ∘ wt) p = f.ext (weight B wt p) := by
  induction p with
  | nil => rfl
  | cons h p ih => rw [weight_cons, weight_cons, ih, ext_mul, ext_emb]; rfl

theorem isPreferred_comp_iff {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W') {s t : V}
    (p : G.Walk s t) : IsPreferred A (f.toFun ∘ wt) p ↔ IsPreferred B wt p := by
  simp only [IsPreferred, weight_comp, ext_le_ext]

theorem traversable_comp_iff {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W') {s t : V} :
    Traversable A (G := G) (f.toFun ∘ wt) s t ↔ Traversable B (G := G) wt s t := by
  simp only [Traversable, weight_comp]
  refine exists_congr fun p => and_congr_right fun _ => not_congr ?_
  rw [← f.map_phi, ← ext_emb, f.ext_injective.eq_iff]

theorem implements_comp_iff {V : Type} {G : SimpleGraph V} (wt : Sym2 V → W') (R : RoutingFunction G) :
    Implements A (f.toFun ∘ wt) R ↔ Implements B wt R := by
  simp only [Implements, traversable_comp_iff, isPreferred_comp_iff]

/-- The reduction behind Lemma 4.12: if `B` embeds into `A`, then routing in `A` needs at least as much local
memory as routing in `B` (`M_B(n) ≤ M_A(n)` for every memory measure). -/
theorem memReq_le_memReq (f : AlgEmbedding B A) (mem : MemoryMeasure) (c n : ℕ) : memReq B mem c n ≤ memReq A mem c n := by
  refine memReq_le fun V _ hV G hG wt => ?_
  refine le_trans ?_ (le_memReq hV G hG (f.toFun ∘ wt))
  exact minMem_mono fun R hR => ⟨(f.implements_comp_iff wt R).1 hR.1, hR.2⟩

end AlgEmbedding

end Embedding

end Podc.CompactPolicyRouting
