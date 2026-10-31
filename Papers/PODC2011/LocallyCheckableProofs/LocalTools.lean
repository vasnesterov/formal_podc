import Papers.PODC2011.LocallyCheckableProofs.Basic
import Cslib.Foundations.Data.List.BitEncoding

/-!
# Tools for upper bounds: radius-one verifiers, monotonicity of views, number encodings

* `Nbr1Eq`: the data a radius-1 verifier at `v` may read (own membership, label and proof; the
  neighbours of `v`, which of these edges are marked, and their labels and proofs).
  `ViewEq.nbr1Eq`: equal views of radius `R ≥ 1` give `Nbr1Eq`; `isLocal_of_nbr1Eq`: a verifier
  determined by this data is local with horizon `1`.
* `ViewEq.restrict_radius` / `IsLocal.of_le_radius`: a view of radius `R` determines the view of
  any radius `r ≤ R`, hence local verifiers with horizon `r` have horizon `R`.
* `natCode` (binary, `Nat.size x` bits), `natsCode` (self-delimiting tuples, CSLib
  `Cslib.BitEncoding.encList`) and `admitsLCP_of_nats`: a scheme whose proof labels are lists of
  at most `m` numbers bounded by `n^k` has proofs of size `m (2k + 3) (⌊log₂ n⌋ + 1)`.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

variable {L : Type*}

/-! ### Balls -/

lemma mem_ball_of_adj (I : Inst L) {v u : ℕ} (h : I.G.Adj v u) {R : ℕ} (hR : 1 ≤ R) :
    u ∈ ball I v R := ⟨Walk.cons h Walk.nil, by simpa using hR⟩

lemma ball_mono (I : Inst L) (v : ℕ) {r R : ℕ} (h : r ≤ R) : ball I v r ⊆ ball I v R :=
  fun _ ⟨p, hp⟩ => ⟨p, hp.trans h⟩

lemma mem_ball_zero {I : Inst L} {v u : ℕ} : u ∈ ball I v 0 ↔ u = v := by
  constructor
  · rintro ⟨p, hp⟩
    exact (Walk.eq_of_length_eq_zero (p := p) (by omega)).symm
  · rintro rfl; exact mem_ball_self I u 0

lemma mem_ball_succ {I : Inst L} {v u k : ℕ} :
    u ∈ ball I v (k + 1) ↔ u ∈ ball I v k ∨ ∃ y ∈ ball I v k, I.G.Adj y u := by
  constructor
  · rintro ⟨p, hp⟩
    by_cases hk : p.length ≤ k
    · exact Or.inl ⟨p, hk⟩
    · right
      cases hq : p.reverse with
      | nil => rw [← Walk.length_reverse, hq] at hk; simp at hk
      | @cons _ y _ h q =>
        refine ⟨y, ⟨q.reverse, ?_⟩, h.symm⟩
        have := congrArg Walk.length hq
        simp at this; simp; omega
  · rintro (h | ⟨y, ⟨p, hp⟩, h⟩)
    · exact ball_mono I v (by omega) h
    · exact ⟨p.concat h, by simp; omega⟩

/-- Every node of a walk starting in `V` lies in `V`. -/
lemma Inst.support_subset {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) {a b : ℕ}
    (p : H.Walk a b) (ha : a ∈ I.V) : ∀ x ∈ p.support, x ∈ I.V := by
  induction p with
  | nil => simpa using ha
  | cons h q ih =>
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih (I.sub' (hH h)) x hx

/-! ### Radius-one views -/

/-- The radius-one data of `v` agree in `(I, P)` and `(I', P')`. -/
structure Nbr1Eq {Λ : Type*} (I : Inst L) (P : ℕ → Λ) (I' : Inst L) (P' : ℕ → Λ) (v : ℕ) :
    Prop where
  adj : ∀ u, I.G.Adj v u ↔ I'.G.Adj v u
  sadj : ∀ u, I.S.Adj v u ↔ I'.S.Adj v u
  prf : ∀ u, I.G.Adj v u → P u = P' u
  lab : ∀ u, I.G.Adj v u → I.lab u = I'.lab u
  prf_self : P v = P' v
  lab_self : I.lab v = I'.lab v
  mem : v ∈ I.V ↔ v ∈ I'.V

lemma ViewEq.nbr1Eq {Λ : Type*} {R : ℕ} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (h : ViewEq R I P I' P' v) (hR : 1 ≤ R) : Nbr1Eq I P I' P' v := by
  have hv := mem_ball_self I v R
  have adj : ∀ u, I.G.Adj v u ↔ I'.G.Adj v u := by
    intro u
    constructor
    · intro hu; exact (h.adj v hv u (mem_ball_of_adj I hu hR)).1 hu
    · intro hu
      have : u ∈ ball I v R := h.ball_eq ▸ mem_ball_of_adj I' hu hR
      exact (h.adj v hv u this).2 hu
  refine ⟨adj, fun u => ?_, fun u hu => h.prf u (mem_ball_of_adj I hu hR),
    fun u hu => h.lab u (mem_ball_of_adj I hu hR), h.prf v hv, h.lab v hv, h.mem v hv⟩
  constructor
  · intro hu; exact (h.sadj v hv u (mem_ball_of_adj I (I.S_le hu) hR)).1 hu
  · intro hu
    have hu' : I.G.Adj v u := (adj u).2 (I'.S_le hu)
    exact (h.sadj v hv u (mem_ball_of_adj I hu' hR)).2 hu

/-- The neighbourhood of `v` as a finset. -/
noncomputable def Inst.nbrs (I : Inst L) (v : ℕ) : Finset ℕ := by
  classical exact I.V.filter (I.G.Adj v)

lemma Inst.mem_nbrs {I : Inst L} {v u : ℕ} : u ∈ I.nbrs v ↔ I.G.Adj v u := by
  classical
  simp only [Inst.nbrs, Finset.mem_filter, and_iff_right_iff_imp]
  exact fun h => I.sub' h

lemma Nbr1Eq.nbrs {Λ : Type*} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (h : Nbr1Eq I P I' P' v) : I.nbrs v = I'.nbrs v := by
  ext u; simp [Inst.mem_nbrs, h.adj]

/-- A verifier whose output is determined by the radius-one data is local (any horizon `≥ 1`). -/
lemma isLocal_of_nbr1Eq {Λ : Type*} {A : Inst L → (ℕ → Λ) → ℕ → Bool}
    (hA : ∀ I P I' P' v, Nbr1Eq I P I' P' v → A I P v = A I' P' v) {R : ℕ} (hR : 1 ≤ R) :
    IsLocal R A :=
  fun I P I' P' v h => hA I P I' P' v (h.nbr1Eq hR)

/-! ### Restricting the radius of a view -/

-- CSLib candidate (with the model)
/-- A view of radius `R` determines the view of radius `r ≤ R`. -/
lemma ViewEq.restrict_radius {Λ : Type*} {R r : ℕ} {I I' : Inst L} {P P' : ℕ → Λ} {v : ℕ}
    (h : ViewEq R I P I' P' v) (hr : r ≤ R) : ViewEq r I P I' P' v := by
  have key : ∀ k ≤ R, ∀ x, x ∈ ball I v k ↔ x ∈ ball I' v k := by
    intro k
    induction k with
    | zero => intro _ x; simp [mem_ball_zero]
    | succ k ih =>
      intro hk x
      have ih := ih (by omega)
      rw [mem_ball_succ, mem_ball_succ]
      constructor
      · rintro (hx | ⟨y, hy, hxy⟩)
        · exact Or.inl ((ih x).1 hx)
        · refine Or.inr ⟨y, (ih y).1 hy, ?_⟩
          have hx : x ∈ ball I v R := ball_mono I v hk (mem_ball_succ.2 (Or.inr ⟨y, hy, hxy⟩))
          exact (h.adj y (ball_mono I v (by omega) hy) x hx).1 hxy
      · rintro (hx | ⟨y, hy, hxy⟩)
        · exact Or.inl ((ih x).2 hx)
        · refine Or.inr ⟨y, (ih y).2 hy, ?_⟩
          have hx : x ∈ ball I v R := h.ball_eq ▸
            ball_mono I' v hk (mem_ball_succ.2 (Or.inr ⟨y, hy, hxy⟩))
          exact (h.adj y (ball_mono I v (by omega) ((ih y).2 hy)) x hx).2 hxy
  have hsub := ball_mono I v hr
  exact ⟨Set.ext (key r hr), fun x hx y hy => h.adj x (hsub hx) y (hsub hy),
    fun x hx y hy => h.sadj x (hsub hx) y (hsub hy), fun x hx => h.mem x (hsub hx),
    fun x hx => h.lab x (hsub hx), fun x hx => h.prf x (hsub hx)⟩

/-- A verifier with horizon `r` has every horizon `R ≥ r`. -/
lemma IsLocal.of_le_radius {Λ : Type*} {r R : ℕ} {A : Inst L → (ℕ → Λ) → ℕ → Bool}
    (h : IsLocal r A) (hr : r ≤ R) : IsLocal R A :=
  fun I P I' P' v hv => h I P I' P' v (hv.restrict_radius hr)

/-! ### Encoding numbers -/

-- CSLib candidate
/-- The binary representation of `x` (least significant bit first), `Nat.size x` bits. -/
def natCode (x : ℕ) : List Bool := List.ofFn fun i : Fin x.size => x.testBit i

@[simp] lemma length_natCode (x : ℕ) : (natCode x).length = x.size := by simp [natCode]

lemma natCode_injective : Function.Injective natCode := by
  intro x y h
  have hs : x.size = y.size := by simpa using congrArg List.length h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < x.size
  · have hi' : i < y.size := hs ▸ hi
    have := congrArg (fun l => l[i]?) h
    simpa [natCode, List.getElem?_ofFn, hi, hi'] using this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self x)
        (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self y)
        (Nat.pow_le_pow_right (by omega) (by omega)))]

-- CSLib candidate
/-- A list of numbers as a self-delimiting bit string. -/
def natsCode (l : List ℕ) : List Bool := Cslib.BitEncoding.encList (l.map natCode)

lemma natsCode_injective : Function.Injective natsCode := by
  intro l l' h
  have := congrArg Cslib.BitEncoding.decList h
  simp only [natsCode, Cslib.BitEncoding.decList_encList] at this
  exact List.map_injective_iff.2 natCode_injective this

lemma length_natsCode_le (l : List ℕ) (p : ℕ) (h : ∀ x ∈ l, x < 2 ^ p) :
    (natsCode l).length ≤ l.length * (2 * p + 1) := by
  have := Cslib.BitEncoding.length_encList_le (l.map natCode) p (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro s x hx rfl
    simpa [Nat.size_le] using h x hx)
  simpa [natsCode] using this

lemma lt_two_pow_of_le_pow {x n k : ℕ} (h : x ≤ n ^ k) :
    x < 2 ^ ((k + 1) * (Nat.log 2 n + 1)) := by
  have hn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h1 : n ^ k ≤ 2 ^ ((Nat.log 2 n + 1) * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hn.le k
  have h2 : 2 ^ ((Nat.log 2 n + 1) * k) < 2 ^ ((k + 1) * (Nat.log 2 n + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

/-- Proof labels that are lists of at most `m` numbers `≤ n^k` give an `O(log n)` scheme. -/
lemma admitsLCP_of_nats {F P : Set (Inst L)} (m k r : ℕ) (A : Inst L → (ℕ → List ℕ) → ℕ → Bool)
    (hA : IsLocal r A)
    (hc : ∀ I ∈ F, I ∈ P → ∃ Q : ℕ → List ℕ,
      (∀ v ∈ I.V, (Q v).length ≤ m ∧ ∀ x ∈ Q v, x ≤ I.n ^ k) ∧ ∀ v ∈ I.V, A I Q v = true)
    (hs : ∀ I ∈ F, I ∉ P → ∀ Q : ℕ → List ℕ, ∃ v ∈ I.V, A I Q v = false) :
    AdmitsLCP F P (fun n => m * (2 * k + 3) * (Nat.log 2 n + 1)) := by
  refine AdmitsLCPEnc.admitsLCP natsCode_injective ⟨r, A, hA, fun I hI hIP => ?_, hs⟩
  obtain ⟨Q, hQ, hacc⟩ := hc I hI hIP
  refine ⟨Q, fun v hv => ?_, hacc⟩
  obtain ⟨hlen, hx⟩ := hQ v hv
  refine (length_natsCode_le (Q v) _ fun x hx' => lt_two_pow_of_le_pow (hx x hx')).trans ?_
  have : 2 * ((k + 1) * (Nat.log 2 I.n + 1)) + 1 ≤ (2 * k + 3) * (Nat.log 2 I.n + 1) := by
    nlinarith
  calc (Q v).length * (2 * ((k + 1) * (Nat.log 2 I.n + 1)) + 1)
      ≤ m * ((2 * k + 3) * (Nat.log 2 I.n + 1)) := Nat.mul_le_mul hlen this
    _ = _ := by ring

lemma logLCP_of_nats {F P : Set (Inst L)} (m k r : ℕ) (A : Inst L → (ℕ → List ℕ) → ℕ → Bool)
    (hA : IsLocal r A)
    (hc : ∀ I ∈ F, I ∈ P → ∃ Q : ℕ → List ℕ,
      (∀ v ∈ I.V, (Q v).length ≤ m ∧ ∀ x ∈ Q v, x ≤ I.n ^ k) ∧ ∀ v ∈ I.V, A I Q v = true)
    (hs : ∀ I ∈ F, I ∉ P → ∀ Q : ℕ → List ℕ, ∃ v ∈ I.V, A I Q v = false) : LogLCP F P :=
  ⟨m * (2 * k + 3), admitsLCP_of_nats m k r A hA hc hs⟩

/-- **Radius-one schemes with numeric labels.** A radius-one check `Chk` on proof labels that are
lists of at most `m` numbers bounded by `n^k` gives an `O(log n)` scheme. -/
lemma logLCP_of_check {F P : Set (Inst L)} (m k : ℕ) (Chk : Inst L → (ℕ → List ℕ) → ℕ → Prop)
    (hloc : ∀ I Q I' Q' v, Nbr1Eq I Q I' Q' v → (Chk I Q v ↔ Chk I' Q' v))
    (hc : ∀ I ∈ F, I ∈ P → ∃ Q : ℕ → List ℕ,
      (∀ v ∈ I.V, (Q v).length ≤ m ∧ ∀ x ∈ Q v, x ≤ I.n ^ k) ∧ ∀ v ∈ I.V, Chk I Q v)
    (hs : ∀ I ∈ F, ∀ Q : ℕ → List ℕ, (∀ v ∈ I.V, Chk I Q v) → I ∈ P) : LogLCP F P := by
  classical
  refine logLCP_of_nats m k 1 (fun I Q v => decide (Chk I Q v))
    (isLocal_of_nbr1Eq (fun I Q I' Q' v h => by simp only [decide_eq_decide]; exact hloc _ _ _ _ _ h)
      le_rfl) (fun I hI hIP => ?_) (fun I hI hIP Q => ?_)
  · obtain ⟨Q, hQ, hacc⟩ := hc I hI hIP
    exact ⟨Q, hQ, fun v hv => by simpa using hacc v hv⟩
  · by_contra hall
    push Not at hall
    exact hIP (hs I hI Q fun v hv => by simpa using hall v hv)

/-- `LogLCP` only depends on the property inside the family. -/
lemma logLCP_congr {F P P' : Set (Inst L)} (h : ∀ I ∈ F, (I ∈ P ↔ I ∈ P')) (hP : LogLCP F P) :
    LogLCP F P' := by
  obtain ⟨C, r, A, hA, hc, hs⟩ := hP
  exact ⟨C, r, A, hA, fun I hI hIP => hc I hI ((h I hI).2 hIP),
    fun I hI hIP => hs I hI (fun h' => hIP ((h I hI).1 h'))⟩

/-- Field `i` of a numeric proof label. -/
def natField (i : ℕ) (Q : ℕ → List ℕ) : ℕ → ℕ := fun u => (Q u).getD i 0

lemma Nbr1Eq.field {I I' : Inst L} {Q Q' : ℕ → List ℕ} {v : ℕ} (h : Nbr1Eq I Q I' Q' v)
    (i : ℕ) : (∀ u, I.G.Adj v u → natField i Q u = natField i Q' u) ∧
      natField i Q v = natField i Q' v :=
  ⟨fun u hu => by simp [LocallyCheckableProofs.natField, h.prf u hu],
    by simp [LocallyCheckableProofs.natField, h.prf_self]⟩

/-- Identifiers and numbers `≤ n` are `≤ n^(c+1)` (with identifiers in `[1, n^c]`). -/
lemma le_pow_succ_of_idBound {I : Inst L} {c v x : ℕ} (hb : I.IdBound c) (hv : v ∈ I.V)
    (hx : x ∈ I.V ∨ x ≤ I.n) : x ≤ I.n ^ (c + 1) := by
  have hn : 1 ≤ I.n := Finset.card_pos.2 ⟨v, hv⟩
  rcases hx with hx | hx
  · exact (hb x hx).2.trans (Nat.pow_le_pow_right hn (Nat.le_succ c))
  · exact hx.trans (Nat.le_self_pow (by omega) _)

end Podc.LocallyCheckableProofs
