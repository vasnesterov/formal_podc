import Mathlib

/-!
# Locally checkable proofs: the model (Section 2 of Göös–Suomela)

M. Göös, J. Suomela. *Locally Checkable Proofs in Distributed Computing.* Theory of Computing 12(19),
2016 (journal version of the PODC 2011 paper *Locally Checkable Proofs*).

* `Inst L`: a (labelled) graph instance. Nodes **are** their identifiers: the node set is a
  `Finset ℕ` and the graph lives on `ℕ` (edges only between nodes). An instance carries node labels
  `lab : ℕ → L` (the paper's "colors, labels") and a set of marked edges `S ≤ G` (edge labels in
  `{0,1}`, used for graph problems such as spanning trees and matchings, Section 2.3). For graph
  properties of unlabelled graphs take `L = Unit` and `S = ⊥` (`Inst.Plain`).
* A *proof* is a function `ℕ → List Bool` (only its values on the nodes matter).
* `ball I v r`: the nodes within distance `r` of `v` (the paper's `V[v,r]`).
* `ViewEq r I P I' P' v`: `v` has the same radius-`r` view in `(I,P)` and `(I',P')`: the same ball,
  the same induced edges and marked edges on it (`G[v,r]`), the same labels and proof labels on it
  (`P[v,r]`).
* `IsLocal r A`: the verifier `A` has local horizon `r`, i.e. its output at `v` depends only on the
  radius-`r` view of `v`. This is equivalent to the paper's `A(G,P,v) = A(G[v,r],P[v,r],v)`.
* `AdmitsLCP F P s` (Definition 2.2): `P` admits locally checkable proofs of size `s` on the family
  `F`, i.e. `P ∈ LCP(s)`. `AdmitsWeakLCP` is the weak proof labelling scheme of Section 2.3 for
  graph problems (we may choose the solution); it is implied by `AdmitsLCP` (`AdmitsLCP.weak`).
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

/-- A labelled graph instance whose nodes are their identifiers. -/
@[ext]
structure Inst (L : Type*) where
  /-- The nodes (= identifiers). -/
  V : Finset ℕ
  /-- The graph. -/
  G : SimpleGraph ℕ
  /-- Edges only join nodes. -/
  sub : ∀ ⦃u v⦄, G.Adj u v → u ∈ V
  /-- Marked edges (edge labels `1`), e.g. a claimed solution of a graph problem. -/
  S : SimpleGraph ℕ
  S_le : S ≤ G
  /-- Node labels (auxiliary local input). -/
  lab : ℕ → L

/-- A proof: a bit string for every node. -/
abbrev Proof := ℕ → List Bool

/-- A verifier: `A I P v` is the output of node `v`. -/
abbrev Verifier (L : Type*) := Inst L → Proof → ℕ → Bool

namespace Inst

variable {L : Type*}

/-- The number of nodes `n(G)`. -/
def n (I : Inst L) : ℕ := I.V.card

lemma sub' (I : Inst L) {u v : ℕ} (h : I.G.Adj u v) : v ∈ I.V := I.sub h.symm

/-- An unlabelled instance: no marked edges (and, for `L = Unit`, no labels). -/
def Plain (I : Inst L) : Prop := I.S = ⊥

/-- The instance is connected (and nonempty). -/
def Conn (I : Inst L) : Prop := I.V.Nonempty ∧ ∀ u ∈ I.V, ∀ v ∈ I.V, I.G.Reachable u v

/-- Identifiers are in `{1, …, n^c}` (the paper: `V(G) ⊆ {1, …, poly(n(G))}`). -/
def IdBound (c : ℕ) (I : Inst L) : Prop := ∀ v ∈ I.V, 1 ≤ v ∧ v ≤ I.n ^ c

/-- Same underlying graph (possibly different labels / solutions). -/
def SameGraph (I J : Inst L) : Prop := I.V = J.V ∧ I.G = J.G

end Inst

variable {L : Type*}

/-- The ball `V[v,r]`: nodes joined to `v` by a walk of length `≤ r`. -/
def ball (I : Inst L) (v : ℕ) (r : ℕ) : Set ℕ := {u | ∃ p : I.G.Walk v u, p.length ≤ r}

lemma mem_ball_self (I : Inst L) (v r : ℕ) : v ∈ ball I v r := ⟨Walk.nil, by simp⟩

/-- `v` has the same radius-`r` view in `(I, P)` and in `(I', P')`. Proof labels may be of any
type `Λ` (bit strings `List Bool` in the paper's definition). -/
structure ViewEq {Λ : Type*} (r : ℕ) (I : Inst L) (P : ℕ → Λ) (I' : Inst L) (P' : ℕ → Λ) (v : ℕ) :
    Prop where
  ball_eq : ball I v r = ball I' v r
  adj : ∀ x ∈ ball I v r, ∀ y ∈ ball I v r, (I.G.Adj x y ↔ I'.G.Adj x y)
  sadj : ∀ x ∈ ball I v r, ∀ y ∈ ball I v r, (I.S.Adj x y ↔ I'.S.Adj x y)
  mem : ∀ x ∈ ball I v r, (x ∈ I.V ↔ x ∈ I'.V)
  lab : ∀ x ∈ ball I v r, I.lab x = I'.lab x
  prf : ∀ x ∈ ball I v r, P x = P' x

/-- A verifier with local horizon `r` (its output at `v` only depends on the radius-`r` view). -/
def IsLocal {Λ : Type*} (r : ℕ) (A : Inst L → (ℕ → Λ) → ℕ → Bool) : Prop :=
  ∀ I P I' P' v, ViewEq r I P I' P' v → A I P v = A I' P' v

/-- The proof has size at most `k` on the nodes of `I`. -/
def SizeLE (I : Inst L) (P : Proof) (k : ℕ) : Prop := ∀ v ∈ I.V, (P v).length ≤ k

/-- All nodes accept. -/
def AllAccept (A : Verifier L) (I : Inst L) (P : Proof) : Prop := ∀ v ∈ I.V, A I P v = true

/-- **Definition 2.2.** `P` admits locally checkable proofs of size `s` on the family `F`
(`P ∈ LCP(s)`): a local verifier such that every yes-instance has a proof of size `≤ s(n)` accepted
by all nodes (completeness), and every no-instance of `F` rejects every proof at some node
(soundness). For a graph problem (labelled instances) this is a *strong* proof labelling scheme. -/
def AdmitsLCP (F P : Set (Inst L)) (s : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (A : Verifier L), IsLocal r A ∧
    (∀ I ∈ F, I ∈ P → ∃ Pf : Proof, SizeLE I Pf (s I.n) ∧ AllAccept A I Pf) ∧
    (∀ I ∈ F, I ∉ P → ∀ Pf : Proof, ∃ v ∈ I.V, A I Pf v = false)

/-- Weak proof labelling scheme (Section 2.3): for every graph of `F` that has some correct
solution, *some* correct solution (labelling of the same graph) has an accepted proof of size
`≤ s(n)`; incorrect labellings are rejected. -/
def AdmitsWeakLCP (F P : Set (Inst L)) (s : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (A : Verifier L), IsLocal r A ∧
    (∀ I ∈ F, (∃ J ∈ F, J ∈ P ∧ I.SameGraph J) →
      ∃ J ∈ F, J ∈ P ∧ I.SameGraph J ∧ ∃ Pf : Proof, SizeLE J Pf (s J.n) ∧ AllAccept A J Pf) ∧
    (∀ I ∈ F, I ∉ P → ∀ Pf : Proof, ∃ v ∈ I.V, A I Pf v = false)

/-- A strong scheme is a weak scheme. -/
lemma AdmitsLCP.weak {F P : Set (Inst L)} {s : ℕ → ℕ} (h : AdmitsLCP F P s) :
    AdmitsWeakLCP F P s := by
  obtain ⟨r, A, hA, hc, hs⟩ := h
  refine ⟨r, A, hA, fun I hI ⟨J, hJF, hJP, _⟩ => ?_, hs⟩
  by_cases hIP : I ∈ P
  · exact ⟨I, hI, hIP, ⟨rfl, rfl⟩, hc I hI hIP⟩
  · obtain ⟨Pf, hPf, hacc⟩ := hc J hJF hJP
    exact ⟨J, hJF, hJP, ‹I.SameGraph J›, Pf, hPf, hacc⟩

/-- Monotonicity in the proof size. -/
lemma AdmitsLCP.mono {F P : Set (Inst L)} {s t : ℕ → ℕ} (h : AdmitsLCP F P s)
    (hst : ∀ n, s n ≤ t n) : AdmitsLCP F P t := by
  obtain ⟨r, A, hA, hc, hs⟩ := h
  refine ⟨r, A, hA, fun I hI hIP => ?_, hs⟩
  obtain ⟨Pf, hPf, hacc⟩ := hc I hI hIP
  exact ⟨Pf, fun v hv => (hPf v hv).trans (hst _), hacc⟩

/-- `LogLCP`: proofs of size `O(log n)`. -/
def LogLCP (F P : Set (Inst L)) : Prop :=
  ∃ C : ℕ, AdmitsLCP F P (fun n => C * (Nat.log 2 n + 1))

/-! ### Basic facts about balls and views -/

/-- Every node of a short walk from `v` is in the ball. -/
lemma mem_ball_of_walk (I : Inst L) {v u : ℕ} (p : I.G.Walk v u) {r : ℕ} (hp : p.length ≤ r) :
    u ∈ ball I v r := ⟨p, hp⟩

/-- `ViewEq` is symmetric. -/
lemma ViewEq.symm {Λ : Type*} {r : ℕ} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ} (h : ViewEq r I P I' P' v) :
    ViewEq r I' P' I P v := by
  have hb := h.ball_eq
  refine ⟨hb.symm, fun x hx y hy => ?_, fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩ <;> rw [← hb] at * <;> simp only [h.adj, h.sadj, h.mem, h.lab, h.prf, *]

/-- **Neighbourhood criterion for equal views.** If every node of the `r`-ball of `v` in `I` has
the same neighbours and the same marked neighbours in `I'`, and labels, proofs and node membership
agree on that ball, then `v` has the same `r`-view in both. -/
lemma viewEq_of_nbrs {Λ : Type*} {r : ℕ} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (hadj : ∀ x ∈ ball I v r, ∀ y, I.G.Adj x y ↔ I'.G.Adj x y)
    (hsadj : ∀ x ∈ ball I v r, ∀ y, I.S.Adj x y ↔ I'.S.Adj x y)
    (hmem : ∀ x ∈ ball I v r, (x ∈ I.V ↔ x ∈ I'.V))
    (hlab : ∀ x ∈ ball I v r, I.lab x = I'.lab x)
    (hprf : ∀ x ∈ ball I v r, P x = P' x) : ViewEq r I P I' P' v := by
  -- short walks *to* `v` in `I` are walks in `I'`, and conversely
  have to' : ∀ k u (p : I.G.Walk u v), p.length = k → k ≤ r →
      ∃ q : I'.G.Walk u v, q.length = k := by
    intro k
    induction k with
    | zero =>
      intro u p hp _
      cases p with
      | nil => exact ⟨Walk.nil, rfl⟩
      | cons _ _ => simp at hp
    | succ k ih =>
      intro u p hp hk
      cases p with
      | nil => simp at hp
      | @cons _ w _ h q =>
        have hu : u ∈ ball I v r := ⟨(Walk.cons h q).reverse, by simp at hp ⊢; omega⟩
        obtain ⟨q', hq'⟩ := ih w q (by simp at hp; omega) (by omega)
        exact ⟨Walk.cons ((hadj u hu w).1 h) q', by simp [hq']⟩
  have from' : ∀ k u (p : I'.G.Walk u v), p.length = k → k ≤ r →
      ∃ q : I.G.Walk u v, q.length = k := by
    intro k
    induction k with
    | zero =>
      intro u p hp _
      cases p with
      | nil => exact ⟨Walk.nil, rfl⟩
      | cons _ _ => simp at hp
    | succ k ih =>
      intro u p hp hk
      cases p with
      | nil => simp at hp
      | @cons _ w _ h q =>
        obtain ⟨q', hq'⟩ := ih w q (by simp at hp; omega) (by omega)
        have hw : w ∈ ball I v r := ⟨q'.reverse, by simp; omega⟩
        have : I.G.Adj w u := (hadj w hw u).2 h.symm
        exact ⟨Walk.cons this.symm q', by simp [hq']⟩
  have hb : ball I v r = ball I' v r := by
    ext u
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := to' _ u p.reverse rfl (by simpa using hp)
      exact ⟨q.reverse, by simp [hq, hp]⟩
    · rintro ⟨p, hp⟩
      obtain ⟨q, hq⟩ := from' _ u p.reverse rfl (by simpa using hp)
      exact ⟨q.reverse, by simp [hq, hp]⟩
  exact ⟨hb, fun x hx y _ => hadj x hx y, fun x hx y _ => hsadj x hx y, hmem, hlab, hprf⟩

/-! ### Bit strings and encodings -/

/-- The bit strings of length `≤ s`. -/
def bitStrings (s : ℕ) : Finset (List Bool) :=
  (Finset.range (s + 1)).biUnion fun k => (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

lemma mem_bitStrings {s : ℕ} {w : List Bool} : w ∈ bitStrings s ↔ w.length ≤ s := by
  simp only [bitStrings, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨k, hk, f, rfl⟩; simp; omega
  · intro h; exact ⟨w.length, by omega, fun i => w.get i, List.ofFn_get w⟩

lemma card_bitStrings_le (s : ℕ) : (bitStrings s).card ≤ 2 ^ (s + 1) := by
  calc (bitStrings s).card
      ≤ ∑ k ∈ Finset.range (s + 1), ((Finset.univ : Finset (Fin k → Bool)).image List.ofFn).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (s + 1), 2 ^ k := by
        gcongr with k
        refine Finset.card_image_le.trans ?_
        simp
    _ ≤ 2 ^ (s + 1) := by
        rw [Nat.geomSum_eq (le_refl 2)]
        simp

/-- `P` admits locally checkable proofs of size `s` with proof labels in an arbitrary type `Λ`,
whose size is measured through the encoding `enc : Λ → List Bool`. -/
def AdmitsLCPEnc {Λ : Type*} (enc : Λ → List Bool) (F P : Set (Inst L)) (s : ℕ → ℕ) : Prop :=
  ∃ (r : ℕ) (A : Inst L → (ℕ → Λ) → ℕ → Bool), IsLocal r A ∧
    (∀ I ∈ F, I ∈ P → ∃ Q : ℕ → Λ, (∀ v ∈ I.V, (enc (Q v)).length ≤ s I.n) ∧
      ∀ v ∈ I.V, A I Q v = true) ∧
    (∀ I ∈ F, I ∉ P → ∀ Q : ℕ → Λ, ∃ v ∈ I.V, A I Q v = false)

/-- Proof labels of any type with an injective bit encoding: the verifier decodes. -/
lemma AdmitsLCPEnc.admitsLCP {Λ : Type*} [Nonempty Λ] {enc : Λ → List Bool}
    (henc : Function.Injective enc) {F P : Set (Inst L)} {s : ℕ → ℕ}
    (h : AdmitsLCPEnc enc F P s) : AdmitsLCP F P s := by
  classical
  obtain ⟨r, A, hA, hc, hs⟩ := h
  let dec : List Bool → Λ := Function.invFun enc
  have hdec : ∀ x, dec (enc x) = x := Function.leftInverse_invFun henc
  refine ⟨r, fun I Pf v => A I (dec ∘ Pf) v, fun I P I' P' v hv => ?_, fun I hI hIP => ?_,
    fun I hI hIP Pf => hs I hI hIP (dec ∘ Pf)⟩
  · exact hA I _ I' _ v ⟨hv.ball_eq, hv.adj, hv.sadj, hv.mem, hv.lab,
      fun x hx => by simp [hv.prf x hx]⟩
  · obtain ⟨Q, hQ, hacc⟩ := hc I hI hIP
    refine ⟨enc ∘ Q, fun v hv => hQ v hv, fun v hv => ?_⟩
    have : dec ∘ (enc ∘ Q) = Q := funext fun x => hdec (Q x)
    simp only [this]
    exact hacc v hv

end Podc.LocallyCheckableProofs
