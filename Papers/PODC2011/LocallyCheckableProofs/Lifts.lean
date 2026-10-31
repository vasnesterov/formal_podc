import Papers.PODC2011.LocallyCheckableProofs.Universal

/-!
# Theorem 7.1: properties closed under lifts and port-numbering verifiers (Section 7.1)

* `IsCovering ϕ H G`: `ϕ` maps `V(H)` onto `V(G)` and, for every node `v` of `H`, maps the
  neighbours of `v` bijectively onto the neighbours of `ϕ v` (so it is a homomorphism). `H` is a
  *lift* of `G` (`IsLift H G`); `P` is *closed under lifts* in `F` (`ClosedUnderLifts F P`) if
  `G ∈ F ∩ P` implies `H ∈ P` for every lift `H ∈ F` of `G`.
* **Port-numbering verifiers.** We model a PN verifier conservatively by `IsPN A`: the output of
  `v` is a function of its own proof label and of the *multiset* of the proof labels of its
  neighbours only (no identifiers, no port numbers; the degree is the size of the multiset).
  Every such verifier is implementable by a one-round PN algorithm, so positive results with
  this class are at least as strong as with PN algorithms. It has local horizon `1`
  (`IsPN.isLocal`), hence `AdmitsPNLCP F P s → AdmitsLCP F P s`.
* `IsPN.fooled`: a PN verifier is fooled by lifts, `A(H, P ∘ ϕ, v) = A(G, P, ϕ v)`; hence every
  property admitting PN-checkable proofs (of any size) is closed under lifts
  (`closedUnderLifts_of_admitsPNLCP`, the remark before Theorem 7.1).
* `theorem_7_1` (**Theorem 7.1**): on connected unlabelled graphs (any identifiers), a property
  closed under lifts admits PN-checkable proofs of size `24 n²`; `theorem_7_1_idBound`: the same on
  the family of connected unlabelled graphs with identifiers in `[1, n^c]`, `c ≥ 1`.
  `closedUnderLifts_iff_admitsPNLCP`: the resulting characterisation.

The scheme is stated once for any graph description `dec : K → Inst Unit` with an injective bit
encoding (`admitsPNLCP_of_codes`; reused for trees in `TreeUpper.lean`). The proof label of `v` is
a pair `(description of a graph G, ϕ(v))`. The honest proof uses the
canonical copy `canon H` of `H` with identifiers `1, …, n` (enumerating `V(H)` by
`Finset.toList`) and `ϕ(v)` the new identifier of `v`. Node `v` checks: `G ∈ F ∩ P`; `ϕ(v) ∈ V(G)`;
all neighbours hold the same code; the multiset of the neighbours' `ϕ`-values is exactly the set
of neighbours of `ϕ(v)` in `G` (equivalent to the paper's two checks
`deg_H v = deg_G ϕ(v)` and `{ϕ(u) : u ~ v} = N_G(ϕ v)`).
-/

namespace Podc.LocallyCheckableProofs.Lifts

open SimpleGraph Finset Cslib.BitEncoding Universal

/-! ### Covering maps and lifts -/

/-- `ϕ : V(H) → V(G)` is a covering map: onto, and for every node `v` of `H` a bijection from the
neighbours of `v` onto the neighbours of `ϕ v`. -/
structure IsCovering (ϕ : ℕ → ℕ) (H G : Inst Unit) : Prop where
  mapsTo : Set.MapsTo ϕ H.V G.V
  surjOn : Set.SurjOn ϕ H.V G.V
  bijOn_nbrs : ∀ v ∈ H.V, Set.BijOn ϕ (H.G.neighborSet v) (G.G.neighborSet (ϕ v))

/-- `H` is a lift of `G`. -/
def IsLift (H G : Inst Unit) : Prop := ∃ ϕ, IsCovering ϕ H G

/-- `P` is closed under lifts within the family `F`. -/
def ClosedUnderLifts (F P : Set (Inst Unit)) : Prop :=
  ∀ G ∈ F, G ∈ P → ∀ H ∈ F, IsLift H G → H ∈ P

/-- The family of connected unlabelled graphs (arbitrary identifiers). -/
def ConnPlain : Set (Inst Unit) := {I | I.Conn ∧ I.Plain}

variable {ϕ : ℕ → ℕ} {H G : Inst Unit}

lemma IsCovering.adj (h : IsCovering ϕ H G) {u v : ℕ} (huv : H.G.Adj u v) :
    G.G.Adj (ϕ u) (ϕ v) :=
  (h.bijOn_nbrs u (H.sub huv)).mapsTo huv

/-- A covering map is a homomorphism. -/
def IsCovering.hom (h : IsCovering ϕ H G) : H.G →g G.G := ⟨ϕ, h.adj⟩

/-- The image of a connected graph under a covering map is connected. -/
lemma IsCovering.conn (h : IsCovering ϕ H G) (hH : H.Conn) : G.Conn := by
  obtain ⟨v₀, hv₀⟩ := hH.1
  refine ⟨⟨ϕ v₀, h.mapsTo hv₀⟩, fun x hx y hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := h.surjOn hx
  obtain ⟨w, hw, rfl⟩ := h.surjOn hy
  exact (hH.2 u hu w hw).map h.hom

/-- Two mutually inverse homomorphisms between the node sets are covering maps. -/
lemma IsCovering.of_inverse {ψ : ℕ → ℕ} (hϕ : ∀ u v, H.G.Adj u v → G.G.Adj (ϕ u) (ϕ v))
    (hψ : ∀ u v, G.G.Adj u v → H.G.Adj (ψ u) (ψ v)) (hϕV : Set.MapsTo ϕ H.V G.V)
    (hψV : Set.MapsTo ψ G.V H.V) (hψϕ : ∀ v ∈ H.V, ψ (ϕ v) = v)
    (hϕψ : ∀ x ∈ G.V, ϕ (ψ x) = x) : IsCovering ϕ H G where
  mapsTo := hϕV
  surjOn := fun x hx => ⟨ψ x, hψV hx, hϕψ x hx⟩
  bijOn_nbrs := fun v hv => by
    refine ⟨fun u hu => hϕ v u hu, fun u hu u' hu' huu' => ?_, fun y hy => ?_⟩
    · rw [← hψϕ u (H.sub' hu), ← hψϕ u' (H.sub' hu'), huu']
    · refine ⟨ψ y, ?_, hϕψ y (G.sub' hy)⟩
      have := hψ _ _ hy
      rwa [hψϕ v hv] at this

/-! ### Port-numbering verifiers -/

/-- The neighbours of `v`, as a `Finset`. -/
noncomputable def nbrs {L : Type*} (I : Inst L) (v : ℕ) : Finset ℕ := by
  classical exact I.V.filter (I.G.Adj v)

lemma mem_nbrs {L : Type*} {I : Inst L} {v u : ℕ} : u ∈ nbrs I v ↔ I.G.Adj v u := by
  classical
  simp only [nbrs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨I.sub' h, h⟩⟩

lemma coe_nbrs {L : Type*} (I : Inst L) (v : ℕ) : (nbrs I v : Set ℕ) = I.G.neighborSet v := by
  ext u; simp [mem_nbrs]

/-- **Port-numbering verifiers** (conservative model): the output of `v` depends only on its own
proof label and on the multiset of the proof labels of its neighbours. -/
def IsPN {L Λ : Type*} (A : Inst L → (ℕ → Λ) → ℕ → Bool) : Prop :=
  ∃ f : Λ → Multiset Λ → Bool, ∀ I P v, A I P v = f (P v) ((nbrs I v).val.map P)

/-- A PN verifier has local horizon `1`. -/
lemma IsPN.isLocal {L Λ : Type*} {A : Inst L → (ℕ → Λ) → ℕ → Bool} (hA : IsPN A) :
    IsLocal 1 A := by
  obtain ⟨f, hf⟩ := hA
  intro I P I' P' v h
  have hn : nbrs I v = nbrs I' v := by
    ext u; simp only [mem_nbrs]; exact viewEq_one_adj h u
  rw [hf, hf, ← hn, viewEq_one_prf h (Or.inl rfl)]
  congr 1
  exact Multiset.map_congr rfl fun u hu =>
    viewEq_one_prf h (Or.inr (mem_nbrs.1 hu))

/-- Locally checkable proofs verifiable by a PN verifier (Definition 2.2 with a PN verifier). -/
def AdmitsPNLCP {L : Type*} (F P : Set (Inst L)) (s : ℕ → ℕ) : Prop :=
  ∃ A : Verifier L, IsPN A ∧
    (∀ I ∈ F, I ∈ P → ∃ Pf : Proof, SizeLE I Pf (s I.n) ∧ AllAccept A I Pf) ∧
    (∀ I ∈ F, I ∉ P → ∀ Pf : Proof, ∃ v ∈ I.V, A I Pf v = false)

lemma AdmitsPNLCP.admitsLCP {L : Type*} {F P : Set (Inst L)} {s : ℕ → ℕ}
    (h : AdmitsPNLCP F P s) : AdmitsLCP F P s :=
  let ⟨A, hA, hc, hs⟩ := h
  ⟨1, A, hA.isLocal, hc, hs⟩

/-- PN schemes with labels in any type with an injective bit encoding. -/
lemma admitsPNLCP_of_enc {L Λ : Type*} [Nonempty Λ] {enc : Λ → List Bool}
    (henc : Function.Injective enc) {F P : Set (Inst L)} {s : ℕ → ℕ}
    (A : Inst L → (ℕ → Λ) → ℕ → Bool) (hA : IsPN A)
    (hc : ∀ I ∈ F, I ∈ P → ∃ Q : ℕ → Λ, (∀ v ∈ I.V, (enc (Q v)).length ≤ s I.n) ∧
      ∀ v ∈ I.V, A I Q v = true)
    (hs : ∀ I ∈ F, I ∉ P → ∀ Q : ℕ → Λ, ∃ v ∈ I.V, A I Q v = false) :
    AdmitsPNLCP F P s := by
  classical
  obtain ⟨f, hf⟩ := hA
  let dec : List Bool → Λ := Function.invFun enc
  have hdec : ∀ x, dec (enc x) = x := Function.leftInverse_invFun henc
  have hA' : ∀ I (Pf : Proof) v, f (dec (Pf v)) (((nbrs I v).val.map Pf).map dec) =
      A I (dec ∘ Pf) v := fun I Pf v => by rw [hf, Multiset.map_map]; rfl
  refine ⟨fun I Pf v => f (dec (Pf v)) (((nbrs I v).val.map Pf).map dec),
    ⟨fun w M => f (dec w) (M.map dec), fun _ _ _ => rfl⟩, fun I hI hIP => ?_,
    fun I hI hIP Pf => ?_⟩
  · obtain ⟨Q, hQ, hacc⟩ := hc I hI hIP
    refine ⟨enc ∘ Q, fun v hv => hQ v hv, fun v hv => ?_⟩
    have : dec ∘ (enc ∘ Q) = Q := funext fun x => hdec (Q x)
    simp only [hA', this]
    exact hacc v hv
  · simpa only [hA'] using hs I hI hIP (dec ∘ Pf)

/-- A covering map maps the neighbourhood multiset of `v` onto that of `ϕ v`. -/
lemma IsCovering.map_nbrs (h : IsCovering ϕ H G) {v : ℕ} (hv : v ∈ H.V) :
    (nbrs H v).val.map ϕ = (nbrs G (ϕ v)).val := by
  classical
  have hb := h.bijOn_nbrs v hv
  rw [← coe_nbrs, ← coe_nbrs] at hb
  rw [← Finset.image_val_of_injOn hb.injOn]
  congr 1
  ext y
  simp only [Finset.mem_image]
  exact ⟨fun ⟨u, hu, hy⟩ => hy ▸ hb.mapsTo hu, fun hy => hb.surjOn hy⟩

/-- A PN verifier is fooled by lifts (Section 7.1): `A(H, P ∘ ϕ, v) = A(G, P, ϕ(v))`. -/
theorem IsPN.fooled {Λ : Type*} {A : Inst Unit → (ℕ → Λ) → ℕ → Bool} (hA : IsPN A)
    (h : IsCovering ϕ H G) (P : ℕ → Λ) {v : ℕ} (hv : v ∈ H.V) :
    A H (P ∘ ϕ) v = A G P (ϕ v) := by
  obtain ⟨f, hf⟩ := hA
  rw [hf, hf, ← Multiset.map_map, h.map_nbrs hv]
  rfl

/-- Section 7.1: "any property that can be locally checked using a PN verifier must be closed
under lifts" (for our one-round PN verifiers, with proofs of any size). -/
theorem closedUnderLifts_of_admitsPNLCP {F P : Set (Inst Unit)} {s : ℕ → ℕ}
    (h : AdmitsPNLCP F P s) : ClosedUnderLifts F P := by
  obtain ⟨A, hA, hc, hs⟩ := h
  intro G hG hGP H hH ⟨ϕ, hϕ⟩
  by_contra hHP
  obtain ⟨Pf, -, hacc⟩ := hc G hG hGP
  obtain ⟨v, hv, hrej⟩ := hs H hH hHP (Pf ∘ ϕ)
  rw [hA.fooled hϕ Pf hv, hacc _ (hϕ.mapsTo hv)] at hrej
  exact Bool.noConfusion hrej

/-! ### The scheme of Theorem 7.1, for any graph description -/

section Generic

variable {K : Type*} (dec : K → Inst Unit)

/-- Proof labels: a graph description (with an injective bit encoding `encK`) and a
distinguished node. -/
def encLabel (encK : K → List Bool) (q : K × ℕ) : List Bool := encList [encK q.1, Nat.bits q.2]

lemma encLabel_injective {encK : K → List Bool} (henc : Function.Injective encK) :
    Function.Injective (encLabel encK) := by
  rintro ⟨c, x⟩ ⟨c', x'⟩ h
  have h' := congrArg decList h
  simp only [encLabel, decList_encList, List.cons.injEq, and_true] at h'
  rw [henc h'.1, bits_injective h'.2]

/-- The check of the PN verifier at a node with label `own = (k, x)` whose neighbours hold the
labels `M`: the described graph `G = dec k` is in `F ∩ P`, `x ∈ V(G)`, all neighbours hold the same
description, and the multiset of their distinguished nodes is exactly the set of neighbours of `x`
in `G`. -/
def PNCheck (F P : Set (Inst Unit)) (own : K × ℕ) (M : Multiset (K × ℕ)) : Prop :=
  dec own.1 ∈ F ∧ dec own.1 ∈ P ∧ own.2 ∈ (dec own.1).V ∧ (∀ m ∈ M, m.1 = own.1) ∧
    M.map Prod.snd = (nbrs (dec own.1) own.2).val

/-- The PN verifier of Theorem 7.1. -/
noncomputable def pnVerifier (F P : Set (Inst Unit)) : Inst Unit → (ℕ → K × ℕ) → ℕ → Bool :=
  fun I Q v => by classical exact decide (PNCheck dec F P (Q v) ((nbrs I v).val.map Q))

lemma pnVerifier_isPN (F P : Set (Inst Unit)) : IsPN (pnVerifier dec F P) :=
  ⟨fun own M => by classical exact decide (PNCheck dec F P own M), fun _ _ _ => rfl⟩

/-- A multiset equation `s.map ϕ = t` between neighbourhoods gives a bijection. -/
lemma bijOn_of_map_eq {s t : Finset ℕ} (h : s.val.map ϕ = t.val) :
    Set.BijOn ϕ (s : Set ℕ) (t : Set ℕ) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · rw [Finset.mem_coe, ← Finset.mem_val, ← h]
    exact Multiset.mem_map_of_mem ϕ hx
  · have hnd : (s.val.map ϕ).Nodup := h ▸ t.nodup
    exact (Multiset.nodup_map_iff_inj_on s.nodup).1 hnd x hx y hy hxy
  · rw [Finset.mem_coe, ← Finset.mem_val, ← h, Multiset.mem_map] at hy
    exact hy

variable {dec} in
/-- **Soundness of the scheme**: if all nodes of a connected instance `H` accept, `H` is a lift of
the graph `G ∈ F ∩ P` described by the common label. (Surjectivity of `ϕ` uses that `G ∈ F` is
connected and `H` is nonempty.) -/
lemma exists_lift_of_pnCheck {F P : Set (Inst Unit)} (hF : ∀ G ∈ F, G.Conn) {H : Inst Unit}
    (hH : H.Conn) {Q : ℕ → K × ℕ}
    (hacc : ∀ v ∈ H.V, PNCheck dec F P (Q v) ((nbrs H v).val.map Q)) :
    ∃ G ∈ F, G ∈ P ∧ IsLift H G := by
  obtain ⟨v₀, hv₀⟩ := hH.1
  have hconst : ∀ v ∈ H.V, (Q v).1 = (Q v₀).1 := fun v hv =>
    const_of_conn (Q := fun x => (Q x).1) hH (fun v hv u hu => (hacc v hv).2.2.2.1 (Q u)
      (Multiset.mem_map_of_mem Q (mem_nbrs.2 hu))) hv₀ hv
  set G := dec (Q v₀).1 with hGdef
  let ϕ : ℕ → ℕ := fun x => (Q x).2
  have hmap : ∀ v ∈ H.V, (nbrs H v).val.map ϕ = (nbrs G (ϕ v)).val := fun v hv => by
    have := (hacc v hv).2.2.2.2
    rw [Multiset.map_map, hconst v hv] at this
    exact this
  have hbij : ∀ v ∈ H.V, Set.BijOn ϕ (H.G.neighborSet v) (G.G.neighborSet (ϕ v)) :=
    fun v hv => by rw [← coe_nbrs, ← coe_nbrs]; exact bijOn_of_map_eq (hmap v hv)
  have hmapsTo : Set.MapsTo ϕ H.V G.V := fun v hv => by
    have := (hacc v hv).2.2.1
    rw [hconst v hv] at this
    exact this
  have hGc : G.Conn := hF G (hacc v₀ hv₀).1
  refine ⟨G, (hacc v₀ hv₀).1, (hacc v₀ hv₀).2.1, ϕ, hmapsTo, fun x hx => ?_, hbij⟩
  exact mem_of_reachable (S := ϕ '' (H.V : Set ℕ))
    (fun y z ⟨v, hv, hvy⟩ hyz => by
      subst hvy
      obtain ⟨u, hu, rfl⟩ := (hbij v hv).surjOn hyz
      exact ⟨u, H.sub' hu, rfl⟩)
    (hGc.2 _ (hmapsTo hv₀) x hx) ⟨v₀, hv₀, rfl⟩

/-- **The scheme of Theorem 7.1** for any graph description `dec : K → Inst Unit` with an
injective bit encoding: if `P` is closed under lifts in a family `F` of connected graphs, and every
`I ∈ F` has a description `k` with `dec k ∈ F` a lift of `I` and a covering map `ϕ : I → dec k`
such that the labels `(k, ϕ v)` have at most `s n` bits, then `P` admits PN-checkable proofs of
size `s`. -/
theorem admitsPNLCP_of_codes [Nonempty K] {encK : K → List Bool}
    (henc : Function.Injective encK) {F P : Set (Inst Unit)} (hF : ∀ I ∈ F, I.Conn)
    (hP : ClosedUnderLifts F P) (s : ℕ → ℕ)
    (honest : ∀ I ∈ F, ∃ (k : K) (ϕ : ℕ → ℕ), dec k ∈ F ∧ IsLift (dec k) I ∧
      IsCovering ϕ I (dec k) ∧ ∀ v ∈ I.V, (encLabel encK (k, ϕ v)).length ≤ s I.n) :
    AdmitsPNLCP F P s := by
  classical
  refine admitsPNLCP_of_enc (encLabel_injective henc) (pnVerifier dec F P)
    (pnVerifier_isPN dec F P) ?_ ?_
  · -- completeness: the honest proof `(k, ϕ v)`
    intro H hH hHP
    obtain ⟨k, e, hkF, hlift, hcov, hsize⟩ := honest H hH
    have hkP : dec k ∈ P := hP H hH hHP _ hkF hlift
    refine ⟨fun v => (k, e v), hsize, fun v hv => ?_⟩
    simp only [pnVerifier, decide_eq_true_eq]
    refine ⟨hkF, hkP, hcov.mapsTo hv, fun m hm => ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Multiset.mem_map.1 hm
      rfl
    · rw [Multiset.map_map]
      exact hcov.map_nbrs hv
  · -- soundness
    intro H hH hHP Q
    by_contra hcon
    push Not at hcon
    have hacc : ∀ v ∈ H.V, PNCheck dec F P (Q v) ((nbrs H v).val.map Q) := fun v hv => by
      simpa [pnVerifier] using hcon v hv
    obtain ⟨G, hG, hGP, hlift⟩ := exists_lift_of_pnCheck hF (hF H hH) hacc
    exact hHP (hP G hG hGP H hH hlift)

end Generic

/-- The canonical copy of `I`: identifiers `1, …, n`, in the order of `I.V.toList`. -/
noncomputable def canonCode (I : Inst Unit) : Code :=
  ⟨List.range' 1 I.V.toList.length, mat I.G I.V.toList⟩

/-- The canonical copy of `I` as an instance. -/
noncomputable def canon (I : Inst Unit) : Inst Unit := (canonCode I).toInst

/-- The covering map between two relabellings of the same adjacency matrix. -/
lemma isCovering_relabel {l s : List ℕ} (a : List Bool) (hl : l.Nodup) (hs : s.Nodup)
    (hlen : l.length = s.length) :
    IsCovering (fun x => s.getD (l.idxOf x) 0) (⟨l, a⟩ : Code).toInst (⟨s, a⟩ : Code).toInst :=
  IsCovering.of_inverse (ψ := fun x => l.getD (s.idxOf x) 0)
    (fun _ _ h => relabel_adj a hl hs hlen h) (fun _ _ h => relabel_adj a hs hl hlen.symm h)
    (fun _ hx => List.mem_toFinset.2 (relabel_mem hlen (List.mem_toFinset.1 hx)))
    (fun _ hx => List.mem_toFinset.2 (relabel_mem hlen.symm (List.mem_toFinset.1 hx)))
    (fun _ hx => relabel_relabel hlen (List.mem_toFinset.1 hx) hs)
    (fun _ hx => relabel_relabel hlen.symm (List.mem_toFinset.1 hx) hl)

lemma code_toList (I : Inst Unit) (hI : I.Plain) :
    (⟨I.V.toList, mat I.G I.V.toList⟩ : Code).toInst = I :=
  toInst_mat I hI _ fun _ => Finset.mem_toList

/-- `canon I` is a lift of `I` (an isomorphic copy) … -/
lemma isCovering_canon_to (I : Inst Unit) (hI : I.Plain) :
    IsCovering (fun x => I.V.toList.getD ((canonCode I).ids.idxOf x) 0) (canon I) I := by
  have := isCovering_relabel (l := (canonCode I).ids) (mat I.G I.V.toList) List.nodup_range'
    I.V.nodup_toList List.length_range'
  rwa [code_toList I hI] at this

/-- … and `I` is a lift of `canon I`. -/
lemma isCovering_canon_from (I : Inst Unit) (hI : I.Plain) :
    IsCovering (fun x => (canonCode I).ids.getD (I.V.toList.idxOf x) 0) I (canon I) := by
  have := isCovering_relabel (s := (canonCode I).ids) (mat I.G I.V.toList) I.V.nodup_toList
    List.nodup_range' List.length_range'.symm
  rwa [code_toList I hI] at this

lemma mem_canonCode_ids {I : Inst Unit} {x : ℕ} (hx : x ∈ (canonCode I).ids) : 1 ≤ x ∧ x ≤ I.n := by
  simp only [canonCode, List.mem_range', Finset.length_toList] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨by omega, by unfold Inst.n; omega⟩

lemma canon_n (I : Inst Unit) : (canon I).n = I.n := by
  simp [canon, canonCode, Inst.n, List.toFinset_card_of_nodup List.nodup_range']

/-- **Theorem 7.1** of [GS16], for any family `F` of connected unlabelled graphs that contains the
canonical copies of its members: a property closed under lifts admits locally checkable proofs of
size `24 n²` (i.e. `O(n²)`) verifiable by a (one-round) port-numbering verifier. -/
theorem theorem_7_1_of {F P : Set (Inst Unit)} (hF : ∀ I ∈ F, I.Conn ∧ I.Plain)
    (hcanon : ∀ I ∈ F, canon I ∈ F) (hP : ClosedUnderLifts F P) :
    AdmitsPNLCP F P (fun n => 24 * n ^ 2) := by
  refine admitsPNLCP_of_codes Code.toInst encCode_injective (fun I hI => (hF I hI).1) hP _
    fun H hH => ⟨canonCode H, _, hcanon H hH, ⟨_, isCovering_canon_to H (hF H hH).2⟩,
      isCovering_canon_from H (hF H hH).2, fun v hv => ?_⟩
  have hcov := isCovering_canon_from H (hF H hH).2
  have hn : 1 ≤ H.n := Finset.card_pos.2 (hF H hH).1.1
  have hlen : (canonCode H).ids.length = H.n := by
    simp [canonCode, Inst.n]
  have hmx : (canonCode H).mx.length = H.n * H.n := by
    simp [canonCode, Inst.n]
  have h1 := length_encCode_le (canonCode H) H.n (fun x hx =>
    (size_le_self x).trans (mem_canonCode_ids hx).2)
  have hev := (mem_canonCode_ids (List.mem_toFinset.1 (hcov.mapsTo hv))).2
  have h2 : (Nat.bits ((canonCode H).ids.getD (H.V.toList.idxOf v) 0)).length ≤ H.n := by
    rw [Nat.size_eq_bits_len]; exact (size_le_self _).trans hev
  rw [hlen, hmx] at h1
  simp only [encLabel, length_encList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  nlinarith

/-- **Theorem 7.1** of [GS16]: on connected (unlabelled) graphs, every property closed under lifts
admits locally checkable proofs of size `O(n²)` (explicitly `24 n²`) that can be verified by a
port-numbering verifier. -/
theorem theorem_7_1 (P : Set (Inst Unit)) (hP : ClosedUnderLifts ConnPlain P) :
    AdmitsPNLCP ConnPlain P (fun n => 24 * n ^ 2) :=
  theorem_7_1_of (fun _ h => h) (fun I hI =>
    ⟨(isCovering_canon_from I hI.2).conn hI.1, Code.toInst_plain _⟩) hP

/-- **Theorem 7.1** of [GS16] on the family of connected unlabelled graphs with identifiers in
`[1, n^c]` (`c ≥ 1`). -/
theorem theorem_7_1_idBound (c : ℕ) (hc : 1 ≤ c) (P : Set (Inst Unit))
    (hP : ClosedUnderLifts (ConnPlainId c) P) :
    AdmitsPNLCP (ConnPlainId c) P (fun n => 24 * n ^ 2) := by
  refine theorem_7_1_of (fun _ h => ⟨h.1, h.2.1⟩) (fun I hI => ⟨
    (isCovering_canon_from I hI.2.1).conn hI.1, Code.toInst_plain _, fun x hx => ?_⟩) hP
  have hx' := mem_canonCode_ids (List.mem_toFinset.1 hx)
  rw [canon_n]
  refine ⟨hx'.1, hx'.2.trans ?_⟩
  calc I.n = I.n ^ 1 := (pow_one _).symm
    _ ≤ I.n ^ c := Nat.pow_le_pow_right (Finset.card_pos.2 hI.1.1) hc

/-- Section 7.1: on connected unlabelled graphs, a property admits PN-checkable proofs (of some
size) iff it is closed under lifts. -/
theorem closedUnderLifts_iff_admitsPNLCP (P : Set (Inst Unit)) :
    ClosedUnderLifts ConnPlain P ↔ ∃ s, AdmitsPNLCP ConnPlain P s :=
  ⟨fun h => ⟨_, theorem_7_1 P h⟩, fun ⟨_, h⟩ => closedUnderLifts_of_admitsPNLCP h⟩

end Podc.LocallyCheckableProofs.Lifts
