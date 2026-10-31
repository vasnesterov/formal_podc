import Papers.PODC2011.LocallyCheckableProofs.Theorem51Edges
import Papers.PODC2011.LocallyCheckableProofs.LogLCP
import Papers.PODC2011.LocallyCheckableProofs.Coloring
import Papers.PODC2011.LocallyCheckableProofs.CoLCP0
import Papers.PODC2011.LocallyCheckableProofs.Symmetric
import Papers.PODC2011.LocallyCheckableProofs.FPFTrees
import Papers.PODC2011.LocallyCheckableProofs.TreeUpper

/-!
# Tightness results and the whole development

This module imports every file of the formalization.

* `Θ(log n)` (Theorem 5.1 together with Section 5.1):

On the family of connected unlabelled graphs with identifiers in `{1, …, n^c}` (`c ≥ 2`), the local
proof complexity of an odd number of nodes, of non-bipartiteness and of leader election is
`Θ(log n)`: they are in `LogLCP` (Section 5.1), and no scheme of size `o(log n)` exists
(Theorem 5.1). Spanning-tree verification likewise (`spanningTree_theta`).
* `Θ(n²)` for symmetric graphs (`symmetric_theta`: Theorem 6.1 + the universal `O(n²)` scheme of §6).
* `Θ(n)` for trees with a fixed-point-free symmetry (`fpfTree_theta`: Theorem 6.3 + the `O(n)` tree
  scheme of §6.2).
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset Filter Asymptotics

variable {L : Type*}

/-- Shrinking the family keeps a scheme. -/
lemma AdmitsLCP.anti {F F' P : Set (Inst L)} {s : ℕ → ℕ} (h : AdmitsLCP F P s) (hF : F' ⊆ F) :
    AdmitsLCP F' P s := by
  obtain ⟨r, A, hA, hc, hs⟩ := h
  exact ⟨r, A, hA, fun I hI => hc I (hF hI), fun I hI => hs I (hF hI)⟩

lemma LogLCP.anti {F F' P : Set (Inst L)} (h : LogLCP F P) (hF : F' ⊆ F) : LogLCP F' P := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, hC.anti hF⟩

/-- Connected unlabelled graphs with identifiers in `{1, …, n^c}`. -/
def plainConnFamily (c : ℕ) : Set (Inst L) := {I | I.Conn ∧ I.IdBound c ∧ I.Plain}

lemma cycle_conn {I : Inst L} (h : I.IsCycle) : I.Conn := by
  obtain ⟨l, hl, h3, hV, hG⟩ := h
  have hadj : ∀ (i : ℕ) (hi : i + 1 < l.length), I.G.Adj l[i] l[i + 1] := by
    intro i hi
    rw [hG, cycGraph, fromRel_adj]
    refine ⟨fun he => ?_, Or.inl ⟨i, by omega, rfl, ?_⟩⟩
    · have := (List.Nodup.getElem_inj_iff hl).1 he; omega
    · simp only [Nat.mod_eq_of_lt hi]
  have hreach : ∀ (i : ℕ) (hi : i < l.length), I.G.Reachable (l[0]'(by omega)) l[i] := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih => intro hi; exact (ih (by omega)).trans (hadj i hi).reachable
  refine ⟨⟨l[0]'(by omega), by simp [hV, List.getElem_mem]⟩, fun u hu v hv => ?_⟩
  rw [hV, List.mem_toFinset] at hu hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  exact (hreach i hi).symm.trans (hreach j hj)

lemma idBound_mono {I : Inst L} {c d : ℕ} (h : I.IdBound c) (hcd : c ≤ d) : I.IdBound d := by
  intro v hv
  refine ⟨(h v hv).1, (h v hv).2.trans (Nat.pow_le_pow_right ?_ hcd)⟩
  have : 0 < I.n := Finset.card_pos.2 ⟨v, hv⟩
  omega

lemma plainConnFamily_plainCycle {c : ℕ} (hc : 2 ≤ c) :
    PlainCycleFamily (plainConnFamily (L := L) c) :=
  ⟨fun _ hI => hI.2.2, fun _ hcyc hid hpl => ⟨cycle_conn hcyc, idBound_mono hid hc, hpl⟩⟩

lemma plainConnFamily_sub (c : ℕ) : plainConnFamily (L := L) c ⊆ connIdFamily c :=
  fun _ hI => ⟨hI.1, hI.2.1⟩

/-- **Non-bipartiteness is `Θ(log n)`** (Table 1; Section 5.1 and Theorem 5.1). -/
theorem nonBipartite_theta {c : ℕ} (hc : 2 ≤ c) :
    LogLCP (plainConnFamily c) (NonBipartite (L := Unit)) ∧
      ∀ s : ℕ → ℕ, AdmitsLCP (plainConnFamily c) (NonBipartite (L := Unit)) s →
        ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) :=
  ⟨(nonBipartite_logLCP c).anti (plainConnFamily_sub c), fun _ h =>
    (theorem_5_1_nonBipartite (plainConnFamily_plainCycle hc) h.weak).2⟩

/-- **An odd number of nodes is `Θ(log n)`** on connected graphs (Section 5.1, Theorem 5.1). -/
theorem oddNodes_theta {c : ℕ} (hc : 2 ≤ c) :
    LogLCP (plainConnFamily c) (OddNodes (L := Unit)) ∧
      ∀ s : ℕ → ℕ, AdmitsLCP (plainConnFamily c) (OddNodes (L := Unit)) s →
        ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) :=
  ⟨(oddNodes_logLCP c).anti (plainConnFamily_sub c), fun _ h =>
    (theorem_5_1_oddNodes (plainConnFamily_plainCycle hc) h.weak).2⟩

lemma leaderElection_eq : (LeaderElection : Set (Inst Bool)) = LeaderElected := by
  ext I
  simp only [LeaderElection, LeaderElected, Set.mem_setOf_eq, Finset.card_eq_one]
  constructor
  · rintro ⟨r, hr⟩
    have hrm : r ∈ I.V.filter fun v => I.lab v = true := by rw [hr]; simp
    refine ⟨r, (Finset.mem_filter.1 hrm).1, fun v hv => ⟨fun hl => ?_, fun he => he ▸ (Finset.mem_filter.1 hrm).2⟩⟩
    have : v ∈ I.V.filter fun v => I.lab v = true := Finset.mem_filter.2 ⟨hv, hl⟩
    rw [hr] at this; simpa using this
  · rintro ⟨r, hr, h⟩
    refine ⟨r, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hl⟩; exact (h v hv).1 hl
    · rintro rfl; exact ⟨hr, (h _ hr).2 rfl⟩

/-- **Leader election is `Θ(log n)`** on connected graphs (Table 2; Section 5.1, Theorem 5.1),
for weak and strong schemes alike. -/
theorem leaderElection_theta {c : ℕ} (hc : 2 ≤ c) :
    LogLCP (plainConnFamily c) LeaderElection ∧
      ∀ s : ℕ → ℕ, AdmitsWeakLCP (plainConnFamily c) LeaderElection s →
        ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) :=
  ⟨leaderElection_eq ▸ (leaderElection_logLCP c).anti (plainConnFamily_sub c), fun _ h =>
    (theorem_5_1_leader (plainConnFamily_plainCycle hc) h).2⟩

/-! ### Spanning trees -/

lemma AdmitsLCP.congr {F P P' : Set (Inst L)} {s : ℕ → ℕ} (h : AdmitsLCP F P s)
    (hPP : ∀ I ∈ F, I ∈ P ↔ I ∈ P') : AdmitsLCP F P' s := by
  obtain ⟨r, A, hA, hc, hs⟩ := h
  exact ⟨r, A, hA, fun I hI hP => hc I hI ((hPP I hI).2 hP),
    fun I hI hP => hs I hI fun h' => hP ((hPP I hI).1 h')⟩

lemma support_subset_V (I : Inst L) {u v : ℕ} (w : I.S.Walk u v) (hu : u ∈ I.V) :
    ∀ x ∈ w.support, x ∈ (I.V : Set ℕ) := by
  induction w with
  | nil => intro x hx; simp at hx; subst hx; exact hu
  | @cons a b _ h p ih =>
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih (I.sub' (I.S_le h)) x hx

/-- The two formulations of "the marked edges form a spanning tree" agree on nonempty instances. -/
lemma spanningTree_iff (I : Inst L) (hne : I.V.Nonempty) :
    I ∈ SpanningTree ↔ I ∈ MarkedSpanningTree := by
  simp only [SpanningTree, MarkedSpanningTree, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hconn, hacyc⟩
    refine ⟨fun u c hc => ?_, fun u hu v hv => ?_⟩
    · cases c with
      | nil => exact hc.ne_nil rfl
      | cons h p =>
        have hu : u ∈ I.V := I.sub (I.S_le h)
        have hs := support_subset_V I (Walk.cons h p) hu
        have hmap := Walk.map_induce (Walk.cons h p) hs
        have : (Walk.induce (I.V : Set ℕ) (Walk.cons h p) hs).IsCycle := by
          rw [← Walk.map_isCycle_iff_of_injective (f := (Embedding.induce (G := I.S) (I.V : Set ℕ)).toHom)
            (Embedding.induce (G := I.S) (I.V : Set ℕ)).injective, hmap]
          exact hc
        exact hacyc _ this
    · have := hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩
      simpa using this.map (Embedding.induce (G := I.S) (I.V : Set ℕ)).toHom
  · rintro ⟨hacyc, hreach⟩
    refine ⟨?_, hacyc.induce _⟩
    haveI : Nonempty (I.V : Set ℕ) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩
    obtain ⟨w⟩ := hreach u hu v hv
    exact ⟨w.induce (I.V : Set ℕ) (support_subset_V I w hu)⟩

lemma cycleFamily_connId {c : ℕ} (hc : 2 ≤ c) : CycleFamily (connIdFamily (L := L) c) :=
  fun _ hcyc hid => ⟨cycle_conn hcyc, idBound_mono hid hc⟩

/-- **Spanning tree verification is `Θ(log n)`** on connected graphs (Table 2; Section 5.1 and
Theorem 5.1), for weak and strong schemes alike. -/
theorem spanningTree_theta {c : ℕ} (hc : 2 ≤ c) :
    LogLCP (connIdFamily c) (SpanningTree (L := Unit)) ∧
      ∀ s : ℕ → ℕ, AdmitsWeakLCP (connIdFamily c) (SpanningTree (L := Unit)) s →
        ¬ (fun n => (s n : ℝ)) =o[atTop] (fun n => Real.log n) := by
  refine ⟨?_, fun _ h => (theorem_5_1_spanningTree (cycleFamily_connId hc) h).2⟩
  obtain ⟨C, hC⟩ := spanningTree_logLCP (L := Unit) c
  exact ⟨C, hC.congr fun I hI => (spanningTree_iff I hI.1.1).symm⟩

/-! ### `Θ(n²)` and `Θ(n)` -/

/-- **Symmetric graphs need `Θ(n²)`-bit proofs** (Table 1, Theorem 6.1 and the universal `O(n²)`
scheme of Section 6), on connected unlabelled graphs with identifiers in `{1, …, n^c}`, `c ≥ 1`. -/
theorem symmetric_theta {c : ℕ} (hc : 1 ≤ c) :
    AdmitsLCP (Universal.ConnPlainId c) {I | IsSymmetric I} (fun n => (4 * c + 10) * n ^ 2) ∧
      ∀ s : ℕ → ℕ, AdmitsLCP (Universal.ConnPlainId c) {I | IsSymmetric I} s →
        ∃ c' : ℝ, 0 < c' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c' * (n : ℝ) ^ 2 ≤ s n :=
  ⟨Universal.universal_upper c _, fun _ h => symmetric_lcp_lower_bound _
    (fun I hpl hconn hid => show I.Conn ∧ I.Plain ∧ I.IdBound c from
      ⟨hconn, hpl, idBound_mono hid hc⟩) h⟩

lemma hasFPFSym_closedUnderIso (F : Set (Inst Unit)) :
    Trees.ClosedUnderIso F {I | HasFPFSym I} := by
  rintro G - ⟨φ, hφ⟩ H - ⟨ϕ, hϕ⟩
  let e : (H.V : Set ℕ) ≃ (G.V : Set ℕ) := hϕ.bijOn.equiv
  let iso : H.G.induce (H.V : Set ℕ) ≃g G.G.induce (G.V : Set ℕ) :=
    { toEquiv := e
      map_rel_iff' := fun {a b} => by
        simp only [induce_adj]
        exact (hϕ.adj_iff a a.2 b b.2).symm }
  refine ⟨(iso.trans φ).trans iso.symm, fun v hv => ?_⟩
  apply hφ (iso v)
  have := congrArg iso hv
  simpa using this

/-- **Trees with a fixed-point-free symmetry need `Θ(n)`-bit proofs** (Table 1, Theorem 6.3 and
the `O(n)` scheme of Section 6.2), on trees with identifiers in `{1, …, n^c}`, `c ≥ 1`; the lower
bound holds for all large even `n` (odd trees have no fixed-point-free automorphism). -/
theorem fpfTree_theta {c : ℕ} (hc : 1 ≤ c) :
    AdmitsLCP {I | I ∈ Trees.TreeFam ∧ I.IdBound c} {I | HasFPFSym I} (fun n => 8 * n) ∧
      ∀ s : ℕ → ℕ, AdmitsLCP {I | I ∈ Trees.TreeFam ∧ I.IdBound c} {I | HasFPFSym I} s →
        ∃ c' : ℝ, 0 < c' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c' * n ≤ s n :=
  ⟨Trees.tree_upper_idBound c hc _ (hasFPFSym_closedUnderIso _), fun _ h =>
    fpf_tree_lcp_lower_bound _ (fun I hpl hconn hacyc hid =>
      show (I.Conn ∧ I.Plain ∧ I.G.IsAcyclic) ∧ I.IdBound c from
        ⟨⟨hconn, hpl, hacyc⟩, idBound_mono hid hc⟩) h⟩

end Podc.LocallyCheckableProofs
