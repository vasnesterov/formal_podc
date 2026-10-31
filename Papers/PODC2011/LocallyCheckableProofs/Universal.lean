import Papers.PODC2011.LocallyCheckableProofs.Basic
import Cslib.Foundations.Data.List.BitEncoding

/-!
# The universal `O(n²)` upper bound (Section 6 of Göös–Suomela)

"In connected graphs, any property of unlabeled graphs admits locally checkable proofs of size
`O(n²)`. We can encode the structure of `G` and the unique node identifiers in `O(n²)` bits; the
nodes can verify that their neighbors agree on the structure of `G` and that their local
neighborhoods match those in `G`. Finally, the nodes can solve the problem by brute force."

* `Code = List ℕ × List Bool`: a *graph code*, a list of identifiers `l` and a (row-major,
  `|l| × |l|`) adjacency matrix `a`. *Every* code decodes to an unlabelled instance
  `Code.toInst` (node set `l`, `x ~ y` iff `x ≠ y` and one of the two matrix entries is set).
* `mat G s`: the adjacency matrix of `G` w.r.t. the identifier list `s`; for an
  enumeration `s` of the nodes, `(⟨s, mat I.G s⟩ : Code).toInst = I` (`toInst_mat`).
* `encCode`: an injective bit encoding of codes (CSLib's self-delimiting `encList`, identifiers in
  binary, `Nat.bits`), with `|encCode (s, mat G s)| ≤ (4c + 10) n²` when the `n` identifiers are
  in `[1, n^c]`.
* `universal_upper` (**Section 6**): for every `c` and **every** property `P` of unlabelled
  instances (not even closure under isomorphism is needed, the identifiers being visible),
  `P` admits locally checkable proofs of size `(4c + 10) n²` on the family of connected
  unlabelled graphs with identifiers in `[1, n^c]`. The verifier has local horizon `1`.

The relabelling lemmas (`relabel_adj`, …) are used for Theorem 7.1 in `Lifts.lean`.
-/

namespace Podc.LocallyCheckableProofs.Universal

open SimpleGraph Finset Cslib.BitEncoding

/-! ### Graph codes -/

/-- A graph code: a list of identifiers and a row-major `|l| × |l|` adjacency matrix. -/
@[ext]
structure Code where
  /-- The identifiers. -/
  ids : List ℕ
  /-- The adjacency matrix, row-major. -/
  mx : List Bool
deriving Inhabited

/-- The (symmetrised) matrix entry `(i, j)` of a code. -/
def Code.M (c : Code) (i j : ℕ) : Prop :=
  c.mx.getD (i * c.ids.length + j) false = true ∨ c.mx.getD (j * c.ids.length + i) false = true

lemma Code.M_symm {c : Code} {i j : ℕ} (h : c.M i j) : c.M j i := Or.symm h

/-- Adjacency in the graph described by a code. -/
def Code.Adj (c : Code) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ i j, c.ids[i]? = some x ∧ c.ids[j]? = some y ∧ c.M i j

/-- The graph described by a code. -/
def Code.graph (c : Code) : SimpleGraph ℕ where
  Adj := c.Adj
  symm := ⟨fun _ _ ⟨h, i, j, hi, hj, hm⟩ => ⟨h.symm, j, i, hj, hi, Code.M_symm hm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The unlabelled instance described by a code (every code describes one). -/
def Code.toInst (c : Code) : Inst Unit where
  V := c.ids.toFinset
  G := c.graph
  sub := by
    rintro u v ⟨-, i, j, hi, -, -⟩
    exact List.mem_toFinset.2 (List.mem_of_getElem? hi)
  S := ⊥
  S_le := bot_le
  lab := fun _ => ()

@[simp] lemma Code.toInst_V (c : Code) : c.toInst.V = c.ids.toFinset := rfl
@[simp] lemma Code.toInst_G (c : Code) : c.toInst.G = c.graph := rfl
@[simp] lemma Code.graph_adj (c : Code) (x y : ℕ) : c.graph.Adj x y ↔ c.Adj x y := Iff.rfl

lemma Code.toInst_plain (c : Code) : c.toInst.Plain := rfl

/-- The adjacency matrix of `G` with respect to the identifier list `s`. -/
noncomputable def mat (G : SimpleGraph ℕ) (s : List ℕ) : List Bool := by
  classical
  exact List.ofFn fun t : Fin (s.length * s.length) =>
    decide (G.Adj (s.getD (t / s.length) 0) (s.getD (t % s.length) 0))

@[simp] lemma length_mat (G : SimpleGraph ℕ) (s : List ℕ) :
    (mat G s).length = s.length * s.length := by
  simp [mat]

lemma mat_getD (G : SimpleGraph ℕ) (s : List ℕ) {i j : ℕ} (hi : i < s.length) (hj : j < s.length) :
    (mat G s).getD (i * s.length + j) false = true ↔ G.Adj (s.getD i 0) (s.getD j 0) := by
  classical
  have hlt : i * s.length + j < s.length * s.length := by nlinarith
  have hdiv : (i * s.length + j) / s.length = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, zero_add]
  have hmod : (i * s.length + j) % s.length = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [mat, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_eq_left]
  simp [hdiv, hmod]

/-- Matrix entries of `mat G s` in a code with an identifier list of the same length. -/
lemma M_mat (G : SimpleGraph ℕ) (s l : List ℕ) (hlen : l.length = s.length) {i j : ℕ}
    (hi : i < s.length) (hj : j < s.length) :
    (⟨l, mat G s⟩ : Code).M i j ↔ G.Adj (s.getD i 0) (s.getD j 0) := by
  simp only [Code.M, hlen]
  rw [mat_getD G s hi hj, mat_getD G s hj hi]
  exact ⟨fun h => h.elim id (fun h => h.symm), Or.inl⟩

/-- An enumeration of the nodes, with the adjacency matrix, encodes the instance. -/
lemma toInst_mat (I : Inst Unit) (hI : I.Plain) (s : List ℕ)
    (hsV : ∀ x, x ∈ s ↔ x ∈ I.V) : (⟨s, mat I.G s⟩ : Code).toInst = I := by
  ext x y
  · simp [hsV]
  · simp only [Code.toInst_G, Code.graph_adj, Code.Adj]
    constructor
    · rintro ⟨-, i, j, hi, hj, hm⟩
      obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.1 hi
      obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
      have := (M_mat I.G s s rfl hi' hj').1 hm
      simpa [List.getD_eq_getElem?_getD, hi', hj'] using this
    · intro h
      have hx : x ∈ s := (hsV x).2 (I.sub h)
      have hy : y ∈ s := (hsV y).2 (I.sub' h)
      refine ⟨h.ne, s.idxOf x, s.idxOf y, ?_, ?_, ?_⟩
      · simp [List.idxOf_lt_length_iff.2 hx]
      · simp [List.idxOf_lt_length_iff.2 hy]
      · rw [M_mat I.G s s rfl (List.idxOf_lt_length_iff.2 hx) (List.idxOf_lt_length_iff.2 hy)]
        simpa [List.getD_eq_getElem?_getD, List.idxOf_lt_length_iff.2 hx,
          List.idxOf_lt_length_iff.2 hy] using h
  · simp only [Code.toInst]; rw [hI]

/-! ### Relabelling (used for Theorem 7.1) -/

/-- In a duplicate-free list, the position of `l[i]` is `i`. -/
lemma idxOf_of_getElem? {l : List ℕ} (hl : l.Nodup) {i x : ℕ} (h : l[i]? = some x) :
    l.idxOf x = i := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact hl.idxOf_getElem i hi

/-- Moving from the identifier list `l` to `s` (same length, both duplicate-free, same matrix)
preserves adjacency: `l[i] ↦ s[i]` is a homomorphism. -/
lemma relabel_adj {l s : List ℕ} (a : List Bool) (hl : l.Nodup) (hs : s.Nodup)
    (hlen : l.length = s.length) {x y : ℕ} (h : (⟨l, a⟩ : Code).Adj x y) :
    (⟨s, a⟩ : Code).Adj (s.getD (l.idxOf x) 0) (s.getD (l.idxOf y) 0) := by
  obtain ⟨hne, i, j, hi, hj, hm⟩ := h
  rw [idxOf_of_getElem? hl hi, idxOf_of_getElem? hl hj]
  have hi' : i < s.length := hlen ▸ (List.getElem?_eq_some_iff.1 hi).1
  have hj' : j < s.length := hlen ▸ (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨?_, i, j, by simp [hi'], by simp [hj'], by simpa [Code.M, hlen] using hm⟩
  intro heq
  have : i = j := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi',
      List.getElem?_eq_getElem hj', Option.getD_some] at heq
    exact (hs.getElem_inj_iff).1 heq
  subst this
  exact hne (Option.some_injective _ (hi.symm.trans hj))

lemma relabel_mem {l s : List ℕ} (hlen : l.length = s.length) {x : ℕ} (hx : x ∈ l) :
    s.getD (l.idxOf x) 0 ∈ s := by
  have : l.idxOf x < s.length := hlen ▸ List.idxOf_lt_length_iff.2 hx
  simp [List.getD_eq_getElem?_getD, this]

lemma relabel_relabel {l s : List ℕ} (hlen : l.length = s.length) {x : ℕ}
    (hx : x ∈ l) (hs : s.Nodup) : l.getD (s.idxOf (s.getD (l.idxOf x) 0)) 0 = x := by
  have h1 : l.idxOf x < s.length := hlen ▸ List.idxOf_lt_length_iff.2 hx
  have h2 : s[l.idxOf x]? = some (s.getD (l.idxOf x) 0) := by
    simp [List.getD_eq_getElem?_getD, h1]
  rw [idxOf_of_getElem? hs h2]
  simp [List.getD_eq_getElem?_getD, List.idxOf_lt_length_iff.2 hx]

/-! ### Bit encoding of codes -/

lemma bits_injective : Function.Injective Nat.bits := by
  intro n m h
  have : Nat.digits 2 n = Nat.digits 2 m := by rw [Nat.digits_two_eq_bits, h, Nat.digits_two_eq_bits]
  exact Nat.digits_inj_iff.1 this

/-- Bit encoding of a code: the identifiers in binary, then the matrix. -/
def encCode (c : Code) : List Bool := encList [encList (c.ids.map Nat.bits), c.mx]

lemma encCode_injective : Function.Injective encCode := by
  rintro ⟨l, a⟩ ⟨l', a'⟩ h
  have h' := congrArg decList h
  simp only [encCode, decList_encList, List.cons.injEq, and_true] at h'
  obtain ⟨h1, rfl⟩ := h'
  have := congrArg decList h1
  simp only [decList_encList] at this
  rw [List.map_injective_iff.2 bits_injective this]

lemma length_encCode_le (c : Code) (p : ℕ) (hp : ∀ x ∈ c.ids, x.size ≤ p) :
    (encCode c).length ≤ 2 * (c.ids.length * (2 * p + 1)) + 1 + (2 * c.mx.length + 1) := by
  have h := length_encList_le (c.ids.map Nat.bits) p (by
    simp only [List.mem_map]
    rintro s ⟨x, hx, rfl⟩
    rw [Nat.size_eq_bits_len]; exact hp x hx)
  simp only [List.length_map] at h
  rw [encCode, length_encList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

lemma size_le_of_le_pow {m n c : ℕ} (h : m ≤ n ^ c) : m.size ≤ c * n + 1 := by
  apply Nat.size_le.2
  calc m ≤ n ^ c := h
    _ ≤ (2 ^ n) ^ c := Nat.pow_le_pow_left Nat.lt_two_pow_self.le c
    _ = 2 ^ (c * n) := by rw [← pow_mul, mul_comm]
    _ < 2 ^ (c * n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma size_le_self (m : ℕ) : m.size ≤ m := Nat.size_le.2 Nat.lt_two_pow_self

/-! ### Connectivity helpers -/

/-- A set closed under adjacency contains everything reachable from its members. -/
lemma mem_of_reachable {G : SimpleGraph ℕ} {S : Set ℕ} (hS : ∀ x y, x ∈ S → G.Adj x y → y ∈ S)
    {u v : ℕ} (h : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (hS _ _ hu h)

/-- A function that agrees across every edge is constant on a connected instance. -/
lemma const_of_conn {L Λ : Type*} {I : Inst L} (hI : I.Conn) {Q : ℕ → Λ}
    (hQ : ∀ v ∈ I.V, ∀ u, I.G.Adj v u → Q u = Q v) {u v : ℕ} (hu : u ∈ I.V) (hv : v ∈ I.V) :
    Q v = Q u :=
  (mem_of_reachable (S := {x | x ∈ I.V ∧ Q x = Q u})
    (fun x y ⟨hx, hxu⟩ hxy => ⟨I.sub' hxy, (hQ x hx y hxy).trans hxu⟩)
    (hI.2 u hu v hv) ⟨hu, rfl⟩).2

/-- Radius-1 views see the neighbours of the centre. -/
lemma viewEq_one_adj {L Λ : Type*} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (h : ViewEq 1 I P I' P' v) (u : ℕ) : I.G.Adj v u ↔ I'.G.Adj v u := by
  have hv := mem_ball_self I v 1
  constructor
  · intro hu
    exact (h.adj v hv u (mem_ball_of_walk I (Walk.cons hu Walk.nil) (by simp))).1 hu
  · intro hu
    have hu' : u ∈ ball I v 1 := h.ball_eq ▸ mem_ball_of_walk I' (Walk.cons hu Walk.nil) (by simp)
    exact (h.adj v hv u hu').2 hu

lemma viewEq_one_prf {L Λ : Type*} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (h : ViewEq 1 I P I' P' v) {u : ℕ} (hu : u = v ∨ I.G.Adj v u) : P u = P' u := by
  rcases hu with rfl | hu
  · exact h.prf _ (mem_ball_self I u 1)
  · exact h.prf u (mem_ball_of_walk I (Walk.cons hu Walk.nil) (by simp))

/-! ### The universal scheme -/

/-- The family of connected unlabelled graphs with identifiers in `[1, n^c]`. -/
def ConnPlainId (c : ℕ) : Set (Inst Unit) := {I | I.Conn ∧ I.Plain ∧ I.IdBound c}

/-- The check performed by node `v` of the universal scheme: its code describes a graph of `F ∩ P`
containing `v`; all neighbours hold the same code; the neighbours of `v` are its neighbours in the
code. -/
def UnivCheck (F P : Set (Inst Unit)) (I : Inst Unit) (Q : ℕ → Code) (v : ℕ) : Prop :=
  (Q v).toInst ∈ F ∧ (Q v).toInst ∈ P ∧ v ∈ (Q v).ids ∧ (∀ u, I.G.Adj v u → Q u = Q v) ∧
    ∀ u, I.G.Adj v u ↔ (Q v).Adj v u

/-- The universal verifier (local horizon 1). -/
noncomputable def univVerifier (F P : Set (Inst Unit)) : Inst Unit → (ℕ → Code) → ℕ → Bool :=
  fun I Q v => by classical exact decide (UnivCheck F P I Q v)

lemma univVerifier_isLocal (F P : Set (Inst Unit)) : IsLocal 1 (univVerifier F P) := by
  intro I Q I' Q' v h
  have hv : Q v = Q' v := viewEq_one_prf h (Or.inl rfl)
  have hiff : UnivCheck F P I Q v ↔ UnivCheck F P I' Q' v := by
    unfold UnivCheck
    rw [hv]
    refine and_congr_right' (and_congr_right' (and_congr_right' (and_congr ?_ ?_)))
    · refine forall_congr' fun u => ?_
      rw [viewEq_one_adj h u]
      exact imp_congr_right fun hu => by
        rw [viewEq_one_prf h (Or.inr ((viewEq_one_adj h u).2 hu))]
    · exact forall_congr' fun u => by rw [viewEq_one_adj h u]
  unfold univVerifier
  exact decide_eq_decide.2 hiff

/-- **Soundness of the universal scheme**: if all nodes of a connected unlabelled instance accept,
the common code describes exactly that instance. -/
lemma eq_of_univCheck {F P : Set (Inst Unit)} (hF : ∀ G ∈ F, G.Conn) {I : Inst Unit}
    (hI : I.Conn) (hIp : I.Plain) {Q : ℕ → Code} (h : ∀ v ∈ I.V, UnivCheck F P I Q v)
    {v₀ : ℕ} (hv₀ : v₀ ∈ I.V) : (Q v₀).toInst = I := by
  have hconst : ∀ v ∈ I.V, Q v = Q v₀ := fun v hv =>
    const_of_conn hI (fun v hv => (h v hv).2.2.2.1) hv₀ hv
  set G := (Q v₀).toInst with hGdef
  have hGc : G.Conn := hF G (h v₀ hv₀).1
  have hnbr : ∀ v ∈ I.V, ∀ u, I.G.Adj v u ↔ G.G.Adj v u := fun v hv u => by
    have := (h v hv).2.2.2.2 u; rwa [hconst v hv] at this
  have hVsub : ∀ v ∈ I.V, v ∈ G.V := fun v hv => by
    have := (h v hv).2.2.1; rw [hconst v hv] at this; simpa [hGdef] using this
  have hVeq : ∀ x, x ∈ G.V ↔ x ∈ I.V := fun x => ⟨fun hx =>
    mem_of_reachable (S := {y | y ∈ I.V})
      (fun y z hy hyz => I.sub' ((hnbr y hy z).2 hyz)) (hGc.2 v₀ (hVsub v₀ hv₀) x hx) hv₀,
    hVsub x⟩
  ext x y
  · exact hVeq x
  · by_cases hx : x ∈ I.V
    · exact (hnbr x hx y).symm
    · exact ⟨fun h' => absurd ((hVeq x).1 (G.sub h')) hx, fun h' => absurd (I.sub h') hx⟩
  · rw [hIp]; rfl

/-- **Section 6** (first paragraph) of [GS16]: in connected unlabelled graphs whose identifiers
lie in `[1, n^c]`, *every* property admits locally checkable proofs of size
`O(n²)`, explicitly `(4c + 10) n²`: the proof is the whole graph (identifiers and adjacency
matrix), the verifier has local horizon `1`. -/
theorem universal_upper (c : ℕ) (P : Set (Inst Unit)) :
    AdmitsLCP (ConnPlainId c) P (fun n => (4 * c + 10) * n ^ 2) := by
  classical
  refine AdmitsLCPEnc.admitsLCP encCode_injective
    ⟨1, univVerifier (ConnPlainId c) P, univVerifier_isLocal _ _, ?_, ?_⟩
  · -- completeness: every node gets the code of the whole instance
    rintro I hI hIP
    set s := I.V.toList
    have hsV : ∀ x, x ∈ s ↔ x ∈ I.V := fun x => Finset.mem_toList
    have hcode : (⟨s, mat I.G s⟩ : Code).toInst = I := toInst_mat I hI.2.1 s hsV
    refine ⟨fun _ => (⟨s, mat I.G s⟩ : Code), fun v _ => ?_, fun v hv => ?_⟩
    · have hn : 1 ≤ I.n := Finset.card_pos.2 hI.1.1
      have hlen : s.length = I.n := Finset.length_toList _
      have h := length_encCode_le (⟨s, mat I.G s⟩ : Code) (c * I.n + 1) (fun x hx =>
        size_le_of_le_pow (hI.2.2 x ((hsV x).1 hx)).2)
      simp only [length_mat, hlen] at h
      refine h.trans ?_
      nlinarith
    · unfold univVerifier
      refine decide_eq_true ⟨by rw [hcode]; exact hI, by rw [hcode]; exact hIP, (hsV v).2 hv,
        fun _ _ => rfl, fun u => ?_⟩
      have := congrArg (fun J : Inst Unit => J.G.Adj v u) hcode
      simp only [Code.toInst_G, Code.graph_adj] at this
      rw [this]
  · -- soundness
    rintro I hI hIP Q
    by_contra hcon
    push Not at hcon
    have hacc : ∀ v ∈ I.V, UnivCheck (ConnPlainId c) P I Q v := fun v hv => by
      have := hcon v hv
      unfold univVerifier at this
      simpa using this
    obtain ⟨v₀, hv₀⟩ := hI.1.1
    have heq := eq_of_univCheck (fun G hG => hG.1) hI.1 hI.2.1 hacc hv₀
    exact hIP (heq ▸ (hacc v₀ hv₀).2.1)

end Podc.LocallyCheckableProofs.Universal
