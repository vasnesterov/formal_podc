import Mathlib
import Cslib.Computability.Distributed.Local.Locality
import Podc.Foundations.Combinatorics.HypergraphRamsey
import Papers.PODC2024.LocalAdvice.OrderInvarianceAux

/-!
# Order-invariance with advice (Theorem 5 of Balliu et al., *Distributed Computation with Local Advice*)

Model (LOCAL with identifiers and advice):

* identifiers are natural numbers; an instance `I : Inst In` is a finite node set `I.Vs ⊆ ℕ`,
  a graph `I.G` on `ℕ` whose edges lie inside `I.Vs`, and node inputs `I.inp` from a finite
  alphabet `In`;
* `β` bits of advice per node are a function `ℕ → (Fin β → Bool)`;
* a `T`-round algorithm that knows the number of nodes `n` is a family
  `A : ℕ → SimpleGraph ℕ → (ℕ → In × (Fin β → Bool)) → ℕ → Out` with each `A n` being
  `T`-local (CSLib `Cslib.Local.IsLocal T`);
* a problem is a predicate `Valid I out` on instances and output labellings.
-/

namespace Podc.LocalAdvice.OrderInvariance

open Cslib.Local

/-- An instance of a graph problem in the LOCAL model: a finite set of identifiers `Vs`, a graph on
`ℕ` whose edges lie inside `Vs`, and node inputs. -/
structure Inst (In : Type*) where
  /-- The nodes (= their identifiers). -/
  Vs : Finset ℕ
  /-- The communication graph. -/
  G : SimpleGraph ℕ
  /-- Edges join nodes of the instance. -/
  edge_mem : ∀ ⦃u v⦄, G.Adj u v → u ∈ Vs
  /-- Node inputs. -/
  inp : ℕ → In

variable {In Out : Type*}

/-- `e` embeds the instance `I` into `J` as a union of connected components: it is injective on the
nodes of `I`, maps them to nodes of `J`, preserves and reflects adjacency and inputs, and no edge
of `J` leaves the image. -/
structure IsComponentEmbedding (e : ℕ → ℕ) (I J : Inst In) : Prop where
  injOn : Set.InjOn e I.Vs
  mapsTo : ∀ v ∈ I.Vs, e v ∈ J.Vs
  adj_iff : ∀ u ∈ I.Vs, ∀ v ∈ I.Vs, (I.G.Adj u v ↔ J.G.Adj (e u) (e v))
  closed : ∀ u ∈ I.Vs, ∀ w, J.G.Adj (e u) w → ∃ v ∈ I.Vs, e v = w
  inp_eq : ∀ v ∈ I.Vs, J.inp (e v) = I.inp v

/-- A problem is *component-wise defined*: a valid solution on `J` restricts to a valid solution
on every (union of) connected component(s) of `J` isomorphic to `I` (the outputs outside the nodes
of `I` are irrelevant). -/
def ComponentWise (Valid : Inst In → (ℕ → Out) → Prop) : Prop :=
  ∀ (I J : Inst In) (e : ℕ → ℕ), IsComponentEmbedding e I J → ∀ out out' : ℕ → Out,
    Valid J out → (∀ v ∈ I.Vs, out' v = out (e v)) → Valid I out'

/-- `J` is a disjoint union of `m` copies of `I`. -/
def IsUnionOfCopies (I J : Inst In) : Prop :=
  ∃ (m : ℕ) (e : Fin m → ℕ → ℕ), (∀ k, IsComponentEmbedding (e k) I J) ∧
    (∀ k l, k ≠ l → ∀ u ∈ I.Vs, ∀ v ∈ I.Vs, e k u ≠ e l v) ∧
    ∀ w ∈ J.Vs, ∃ k, ∃ v ∈ I.Vs, e k v = w

/-- An algorithm (without knowledge of `n`) is *order-invariant*: its output does not change when
the identifiers are renumbered by an order-preserving map. -/
def OrderInvariant {L : Type*} (A : SimpleGraph ℕ → (ℕ → L) → ℕ → Out) : Prop :=
  ∀ (e : ℕ ↪o ℕ) (G : SimpleGraph ℕ) (x x' : ℕ → L), (∀ u, x' (e u) = x u) →
    ∀ v, A (G.map e.toEmbedding) x' (e v) = A G x v

/-! ### Proof of Theorem 5 -/

open SimpleGraph

section Proof

/-- A component embedding is a local isomorphism of the graphs. -/
lemma IsComponentEmbedding.isLocalIso {e : ℕ → ℕ} {I J : Inst In} (h : IsComponentEmbedding e I J) :
    IsLocalIso I.G J.G e I.Vs where
  injOn := h.injOn
  closedG := fun _ _ _ hab => I.edge_mem hab.symm
  closedH := h.closed
  adj_iff := fun a ha b hb => (h.adj_iff a ha b hb).symm

/-- Every instance embeds into itself. -/
lemma isComponentEmbedding_id (I : Inst In) : IsComponentEmbedding id I I where
  injOn := Function.injective_id.injOn
  mapsTo := fun _ h => h
  adj_iff := fun _ _ _ _ => Iff.rfl
  closed := fun _ _ w h => ⟨w, I.edge_mem h.symm, rfl⟩
  inp_eq := fun _ _ => rfl

/-! #### Disjoint unions of copies -/

/-- `m` copies of `I` on the node set `W`, placed by the bijection `σ`. -/
noncomputable def copies (I : Inst In) (W : Finset ℕ) {m : ℕ} (σ : Fin m × I.Vs ≃ W) :
    Inst In where
  Vs := W
  G :=
    { Adj := fun a b => ∃ ha : a ∈ W, ∃ hb : b ∈ W, (σ.symm ⟨a, ha⟩).1 = (σ.symm ⟨b, hb⟩).1 ∧
        I.G.Adj (σ.symm ⟨a, ha⟩).2 (σ.symm ⟨b, hb⟩).2
      symm := ⟨fun _ _ ⟨ha, hb, h1, h2⟩ => ⟨hb, ha, h1.symm, h2.symm⟩⟩
      loopless := ⟨fun _ ⟨_, _, _, h⟩ => h.ne rfl⟩ }
  edge_mem := fun _ _ ⟨ha, _⟩ => ha
  inp := fun a => if ha : a ∈ W then I.inp (σ.symm ⟨a, ha⟩).2 else I.inp 0

/-- The `k`-th copy map (injective on all of `ℕ`). -/
noncomputable def copy (I : Inst In) (W : Finset ℕ) {m : ℕ} (σ : Fin m × I.Vs ≃ W) (k : Fin m)
    (u : ℕ) : ℕ :=
  if hu : u ∈ I.Vs then σ (k, ⟨u, hu⟩) else W.sup id + 1 + u

section
variable (I : Inst In) (W : Finset ℕ) {m : ℕ} (σ : Fin m × I.Vs ≃ W)

lemma copy_of_mem (k : Fin m) {u : ℕ} (hu : u ∈ I.Vs) : copy I W σ k u = σ (k, ⟨u, hu⟩) := by
  simp [copy, hu]

lemma copy_injective (k : Fin m) : Function.Injective (copy I W σ k) := by
  have hle : ∀ p, (σ p : ℕ) ≤ W.sup id := fun p => Finset.le_sup (f := id) (σ p).2
  intro u u' h
  by_cases hu : u ∈ I.Vs <;> by_cases hu' : u' ∈ I.Vs <;>
    simp only [copy, hu, hu', dite_true, dite_false] at h
  · have := σ.injective (Subtype.ext h)
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
    exact this.2
  · have := hle (k, ⟨u, hu⟩); omega
  · have := hle (k, ⟨u', hu'⟩); omega
  · omega

lemma isComponentEmbedding_copy (k : Fin m) : IsComponentEmbedding (copy I W σ k) I (copies I W σ) where
  injOn := (copy_injective I W σ k).injOn
  mapsTo := fun v hv => by rw [copy_of_mem I W σ k hv]; exact (σ _).2
  adj_iff := by
    intro u hu v hv
    simp only [copies, copy_of_mem I W σ k hu, copy_of_mem I W σ k hv, Subtype.coe_eta,
      Equiv.symm_apply_apply, Finset.coe_mem, exists_true_left, true_and]
  closed := by
    intro u hu w ⟨ha, hb, h1, h2⟩
    refine ⟨(σ.symm ⟨w, hb⟩).2, (σ.symm ⟨w, hb⟩).2.2, ?_⟩
    simp only [copy_of_mem I W σ k hu, Subtype.coe_eta, Equiv.symm_apply_apply] at h1
    rw [copy_of_mem I W σ k (σ.symm ⟨w, hb⟩).2.2, h1]
    simp
  inp_eq := by
    intro v hv
    simp [copies, copy_of_mem I W σ k hv]

lemma isUnionOfCopies_copies : IsUnionOfCopies I (copies I W σ) := by
  refine ⟨m, copy I W σ, isComponentEmbedding_copy I W σ, ?_, ?_⟩
  · intro k l hkl u hu v hv h
    rw [copy_of_mem I W σ k hu, copy_of_mem I W σ l hv] at h
    have := σ.injective (Subtype.ext h)
    simp only [Prod.mk.injEq] at this
    exact hkl this.1
  · intro w hw
    refine ⟨(σ.symm ⟨w, hw⟩).1, (σ.symm ⟨w, hw⟩).2, (σ.symm ⟨w, hw⟩).2.2, ?_⟩
    rw [copy_of_mem I W σ _ (σ.symm ⟨w, hw⟩).2.2]
    simp

end

/-! #### The order-invariant algorithm -/

open Classical in
/-- A finite set as a `Finset` (`∅` for infinite sets). -/
noncomputable def toFin (B : Set ℕ) : Finset ℕ := if h : B.Finite then h.toFinset else ∅

lemma toFin_coe (F : Finset ℕ) : toFin (F : Set ℕ) = F := by
  simp [toFin, F.finite_toSet]

lemma toFin_image (e : ℕ ↪o ℕ) (B : Set ℕ) : toFin (e '' B) = (toFin B).map e.toEmbedding := by
  by_cases hB : B.Finite
  · have hB' : (e '' B).Finite := hB.image _
    ext a
    simp [toFin, hB, hB']
  · have hB' : ¬ (e '' B).Finite := fun h => hB (h.of_finite_image e.injective.injOn)
    simp [toFin, hB, hB']

/-- The order-invariant algorithm: evaluate `Fs` on the structure of the radius-`T` view. -/
noncomputable def algA' {L : Type*} (s T : ℕ) [NeZero s] (Fs : Struct s L → Out) :
    SimpleGraph ℕ → (ℕ → L) → ℕ → Out :=
  fun G x v => Fs (mkStruct s (toFin (G.closedBall v (T : ℕ∞))) (loc G v T) (mask G v T x) v)

variable {L : Type*} {s T : ℕ} [NeZero s] (Fs : Struct s L → Out)

lemma algA'_isLocal : IsLocal T (algA' s T Fs) := by
  intro G x G' x' v hv
  simp only [algA', hv.1.closedBall_eq le_rfl, hv.loc_eq, hv.mask_eq]

lemma algA'_orderInvariant : OrderInvariant (algA' s T Fs) := by
  intro e G x x' hx v
  have hM := isLocalIso_map G e.toEmbedding
  have hd : ∀ a b, (G.map e.toEmbedding).edist (e a) (e b) = G.edist a b :=
    fun a b => hM.edist_eq trivial trivial
  have hball : (G.map e.toEmbedding).closedBall (e v) (T : ℕ∞) = e '' G.closedBall v T := by
    ext w
    simp only [mem_closedBall', Set.mem_image]
    constructor
    · intro hw
      obtain ⟨u, -, rfl⟩ := hM.exists_of_edist_ne_top (a := v) trivial
        (edist_ne_top_of_le_natCast hw)
      exact ⟨u, by rw [← hd v u]; exact hw, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rwa [hd]
  have hmask : ∀ a, mask (G.map e.toEmbedding) (e v) T x' (e a) = mask G v T x a := by
    intro a
    simp only [mask, hd, hx]
  simp only [algA', hball, toFin_image]
  congr 1
  apply mkStruct_map s e
  · intro a _ b _
    simp only [loc, hd]
    exact and_congr_left' (map_adj_apply (f := e.toEmbedding))
  · exact fun a _ => hmask a
  · exact hmask v

/-- The key step: the view of the copy of `v` in `H` is the realization of the structure of the
view of `v` in `I`. -/
lemma viewEq_real (T : ℕ) {I H : Inst In} {E : ℕ ↪ ℕ}
    (hE : IsComponentEmbedding E I H) {v : ℕ} (hv : v ∈ I.Vs) {F : Finset ℕ}
    (hF : (F : Set ℕ) = I.G.closedBall v T) (hFs : F.card ≤ s) {φ : Fin s → ℕ}
    (hφ : ∀ i : Fin s, i.val < F.card → φ i = E (enumF F i)) (hφinj : Function.Injective φ)
    {x xH : ℕ → L} (hx : ∀ u ∈ I.Vs, xH (E u) = x u) :
    ViewEq T (realGraph (mkStruct s F (loc I.G v T) (mask I.G v T x) v) φ)
      (realLab (mkStruct s F (loc I.G v T) (mask I.G v T x) v) φ) H.G xH (E v) := by
  have hJ := hE.isLocalIso
  have hmemF : ∀ u, u ∈ F ↔ I.G.edist v u ≤ T := fun u => by
    rw [← Finset.mem_coe, hF, mem_closedBall']
  have hLg : ∀ a b, (loc I.G v T).Adj a b → a ∈ F := by
    rintro a b ⟨hab, ha | hb⟩
    · exact (hmemF a).2 ha.le
    · rw [hmemF]
      calc I.G.edist v a ≤ I.G.edist v b + 1 := edist_le_add_one_of_adj hab.symm
        _ ≤ T := Order.add_one_le_of_lt hb
  rw [realGraph_mkStruct hFs hLg E hφ]
  refine ViewEq.symm ⟨?_, ?_⟩
  · intro y hy z
    obtain ⟨u, hu, rfl⟩ := hJ.exists_of_edist_ne_top hv (ne_top_of_lt hy)
    rw [hJ.edist_eq hv hu] at hy
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := hJ.closedH u hu z hz
      rw [map_adj_apply]
      exact ⟨(hJ.adj_iff u hu w hw).1 hz, Or.inl hy⟩
    · intro hz
      obtain ⟨u', w, ⟨hadj, -⟩, hu', rfl⟩ := (map_adj E _ _ _).1 hz
      rw [E.injective hu'] at hadj
      exact (hJ.adj_iff u hu w (hJ.closedG u hu w hadj)).2 hadj
  · intro a ha
    obtain ⟨u, hu, rfl⟩ := hJ.exists_of_edist_ne_top hv (edist_ne_top_of_le_natCast ha)
    rw [hJ.edist_eq hv hu] at ha
    rw [realLab_mkStruct hFs E hφinj hφ ((hmemF u).2 ha), mask_of_le ha, hx u hu]

end Proof

/-- **Theorem 5** of [Balliu et al., arXiv:2405.04519]. Fix `Δ`, `T` and `β`. Let `Valid` be a
component-wise defined problem with finite input and output alphabets, and let `Fam` be a family of
instances of maximum degree `≤ Δ` closed under disjoint unions of copies. Suppose that a `T`-round
algorithm `A` (which may know the number of nodes `n`) solves the problem with `β` bits of advice
on all instances of `Fam` whose identifier set is admissible, where every set `{1, …, N}` is
admissible (e.g. "identifiers in `{1, …, poly(n)}`"). Then an *order-invariant* `T`-round algorithm
`A'`, which does not even need to know `n`, solves the problem with `β` bits of advice on all
instances of `Fam`, with arbitrary identifiers. -/
theorem theorem_5 [Fintype In] [Fintype Out]
    (Δ T β : ℕ) (Valid : Inst In → (ℕ → Out) → Prop) (hcw : ComponentWise Valid)
    (Fam : Inst In → Prop) (hFam : ∀ I J, Fam I → IsUnionOfCopies I J → Fam J)
    (hdeg : ∀ I, Fam I → ∀ v, (I.G.neighborSet v).ncard ≤ Δ)
    (Adm : Finset ℕ → Prop) (hAdm : ∀ N, Adm (Finset.Icc 1 N))
    (A : ℕ → SimpleGraph ℕ → (ℕ → In × (Fin β → Bool)) → ℕ → Out)
    (hA : ∀ n, IsLocal T (A n))
    (hsolve : ∀ I, Fam I → Adm I.Vs → ∃ adv : ℕ → Fin β → Bool,
      Valid I (A I.Vs.card I.G (fun u => (I.inp u, adv u)))) :
    ∃ A' : SimpleGraph ℕ → (ℕ → In × (Fin β → Bool)) → ℕ → Out,
      IsLocal T A' ∧ OrderInvariant A' ∧
      ∀ I, Fam I → ∃ adv : ℕ → Fin β → Bool, Valid I (A' I.G (fun u => (I.inp u, adv u))) := by
  classical
  set s := (Δ + 1) ^ T with hs
  have : NeZero s := ⟨by positivity⟩
  -- Colour an `s`-set `Z` by the behaviour of `A N` on all structures realized on `Z`.
  let colour : ℕ → Finset ℕ → (Struct s (In × (Fin β → Bool)) → Out) := fun N Z =>
    if h : Z.card = s then fun S => A N (realGraph S (Z.orderEmbOfFin h))
      (realLab S (Z.orderEmbOfFin h)) (Z.orderEmbOfFin h S.2.2)
    else fun S => A N ⊥ (fun _ => S.2.1 S.2.2) 0
  have hR : ∀ M, ∃ R, ∀ (c : Finset ℕ → (Struct s (In × (Fin β → Bool)) → Out))
      (S : Finset ℕ), R ≤ S.card → ∃ Y ⊆ S, Y.card = M ∧ ∃ i, ∀ Z ⊆ Y, Z.card = s → c Z = i :=
    fun M => by
      obtain ⟨R, hR⟩ := Cslib.exists_homogeneous_finite s M (Struct s (In × (Fin β → Bool)) → Out)
      exact ⟨R, fun c S hS => hR c S hS⟩
  choose R hR using hR
  -- Ramsey on `{1, …, (R M + M)!}` for every `M`.
  have hY : ∀ M, ∃ Y ⊆ Finset.Icc 1 (R M + M).factorial, Y.card = M ∧
      ∃ t, ∀ Z ⊆ Y, Z.card = s → colour (R M + M).factorial Z = t := fun M =>
    hR M _ _ (by rw [Nat.card_Icc]; have := Nat.self_le_factorial (R M + M); omega)
  choose Y hYsub hYcard t ht using hY
  -- Pigeonhole: one behaviour `Fs` occurs for infinitely many `M`.
  obtain ⟨Fs, hinf⟩ := Finite.exists_infinite_fiber t
  refine ⟨algA' s T Fs, algA'_isLocal Fs, algA'_orderInvariant Fs, ?_⟩
  intro I hI
  by_cases hn : I.Vs.card = 0
  · have hVs : I.Vs = ∅ := Finset.card_eq_zero.1 hn
    obtain ⟨adv, hadv⟩ := hsolve I hI (by rw [hVs]; simpa using hAdm 0)
    refine ⟨adv, hcw I I id (isComponentEmbedding_id I) _ _ hadv ?_⟩
    intro v hv; rw [hVs] at hv; simp at hv
  set n := I.Vs.card with hn_def
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨M, hMt, hMgt⟩ := (Set.infinite_coe_iff.1 hinf).exists_gt (n + s)
  have hMt : t M = Fs := hMt
  set N := (R M + M).factorial with hN
  have hnN : n ∣ N := Nat.dvd_factorial hn0 (by omega)
  set m := N / n with hm
  have hmn : m * n = N := Nat.div_mul_cancel hnN
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hmn; have := Nat.factorial_pos (R M + M); omega
    · exact h
  -- The first copy of `I` goes order-preservingly onto the `n` smallest elements of `Y M`.
  let y := (Y M).orderEmbOfFin (hYcard M)
  let rank : I.Vs ≃o Fin n := (I.Vs.orderIsoOfFin rfl).symm
  let pos : I.Vs → Fin M := fun u => Fin.castLE (by omega) (rank u)
  let k0 : Fin m := ⟨0, hm0⟩
  obtain ⟨σ, hσ⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (α := Fin m × I.Vs)
    (t := Finset.Icc 1 N) (s := {p | p.1 = k0}) (f := fun p => y (pos p.2))
    (by simp [Nat.card_Icc, hmn, n])
    (fun p _ => hYsub M (Finset.orderEmbOfFin_mem _ _ _))
    (fun p hp q hq h => Prod.ext (hp.trans hq.symm)
      (rank.injective (Fin.castLE_injective _ (y.injective h))))
  let H := copies I (Finset.Icc 1 N) σ
  let E : ℕ ↪ ℕ := ⟨copy I (Finset.Icc 1 N) σ k0, copy_injective I _ σ k0⟩
  have hEce : IsComponentEmbedding E I H := isComponentEmbedding_copy I _ σ k0
  have hEval : ∀ u (hu : u ∈ I.Vs), E u = y (pos ⟨u, hu⟩) := fun u hu => by
    show copy I _ σ k0 u = _
    rw [copy_of_mem I _ σ k0 hu, hσ _ rfl]
  obtain ⟨advH, hvalid⟩ := hsolve H (hFam I H hI (isUnionOfCopies_copies I _ σ)) (hAdm N)
  have hHcard : H.Vs.card = N := by simp [H, copies, Nat.card_Icc]
  rw [hHcard] at hvalid
  refine ⟨fun u => advH (E u), hcw I H E hEce _ _ hvalid ?_⟩
  intro v hv
  -- The radius-`T` ball of `v`.
  have hfin : ∀ w, (I.G.neighborSet w).Finite := fun w =>
    I.Vs.finite_toSet.subset fun z hz => I.edge_mem (I.G.adj_symm hz)
  obtain ⟨F, hF, hFs⟩ := exists_closedBall_card_le hfin (hdeg I hI) T v
  have hFV : ∀ u ∈ F, u ∈ I.Vs := by
    intro u hu
    rw [← Finset.mem_coe, hF, mem_closedBall'] at hu
    obtain ⟨b, hb, rfl⟩ := (isComponentEmbedding_id I).isLocalIso.exists_of_edist_ne_top hv
      (edist_ne_top_of_le_natCast hu)
    exact hb
  -- The `s`-subset of `Y M`: the copy of the ball, padded by elements beyond the first copy.
  let g : Fin s → ℕ := fun i =>
    if hi : i.val < F.card then E (enumF F i) else y ⟨n + i, by omega⟩
  have hg : ∀ i : Fin s, i.val < F.card → g i = E (enumF F i) := fun i hi => by simp [g, hi]
  have hgmono : StrictMono g := by
    intro i j hij
    by_cases hj : j.val < F.card
    · have hi : i.val < F.card := lt_trans hij hj
      rw [hg i hi, hg j hj, hEval _ (hFV _ (enumF_mem hi)), hEval _ (hFV _ (enumF_mem hj))]
      apply y.strictMono
      rw [Fin.lt_def]
      simp only [pos, Fin.val_castLE]
      rw [← Fin.lt_def, rank.lt_iff_lt, Subtype.mk_lt_mk]
      exact (enumF_lt_iff hi hj).2 hij
    · by_cases hi : i.val < F.card
      · rw [hg i hi, hEval _ (hFV _ (enumF_mem hi))]
        simp only [g, hj, dite_false]
        apply y.strictMono
        rw [Fin.lt_def]
        simp only [pos, Fin.val_castLE]
        have := (rank ⟨_, hFV _ (enumF_mem hi)⟩).isLt
        omega
      · simp only [g, hi, hj, dite_false]
        apply y.strictMono
        rw [Fin.lt_def]
        simp only
        have : i.val < j.val := hij
        omega
  have hgY : ∀ i, g i ∈ Y M := by
    intro i
    by_cases hi : i.val < F.card
    · rw [hg i hi, hEval _ (hFV _ (enumF_mem hi))]; exact Finset.orderEmbOfFin_mem _ _ _
    · simp only [g, hi, dite_false]; exact Finset.orderEmbOfFin_mem _ _ _
  let X := Finset.univ.image g
  have hXcard : X.card = s := by
    rw [Finset.card_image_of_injective _ hgmono.injective]; simp
  have hXY : X ⊆ Y M := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact hgY i
  have hXg : ⇑(X.orderEmbOfFin hXcard) = g :=
    (Finset.orderEmbOfFin_unique hXcard (fun i => Finset.mem_image_of_mem g (Finset.mem_univ i))
      hgmono).symm
  have hcol := ht M X hXY hXcard
  -- The chain of equalities.
  set S := mkStruct s F (loc I.G v T) (mask I.G v T (fun u => (I.inp u, advH (E u)))) v with hS
  have h1 : algA' s T Fs I.G (fun u => (I.inp u, advH (E u))) v = Fs S := by
    simp only [algA', ← hF, toFin_coe, hS]
  have h2 : Fs S = A N (realGraph S g) (realLab S g) (g S.2.2) := by
    rw [← hMt, ← hcol]
    simp only [colour, hXcard, dite_true, hXg]
    rfl
  have h3 : g S.2.2 = E v :=
    centre_mkStruct hFs E hg (by rw [← Finset.mem_coe, hF]; exact mem_closedBall_self)
  rw [h1, h2, h3]
  exact hA N _ _ _ _ _ (viewEq_real T hEce hv hF hFs hg hgmono.injective
    (fun u hu => Prod.ext (hEce.inp_eq u hu) rfl))

end Podc.LocalAdvice.OrderInvariance
