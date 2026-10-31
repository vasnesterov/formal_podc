import Papers.PODC2011.LocallyCheckableProofs.SpanningTree

/-!
# Complementing in LCP(0) (Section 7.3)

On connected graphs (with identifiers in `{1, …, n^c}`), if `P ∈ LCP(0)` then its complement
`F \ P` is in LogLCP: the proof is a spanning tree rooted at a node `a` that rejects the input
under the LCP(0) verifier `A` with the empty proof `ε`; the root checks `A(G, ε, a) = 0`.

Locality: the new verifier at `v` runs the tree check (radius 1) and, if `v` claims to be the root,
simulates `A` on the *empty* proof, i.e. it ignores the actual proof labels inside its radius-`r`
ball; this is a function of the radius-`max(r,1)` view (`ViewEq.restrict_radius`). Soundness uses
that on a yes-instance of `P` the accepted proof of size `0` *is* the empty proof inside every
ball around a node (`apply_eq_emptyProof`).
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph

variable {L : Type*}

/-- The empty proof `ε`. -/
def emptyProof : Proof := fun _ => []

lemma ball_subset_V {I : Inst L} {v r : ℕ} (hv : v ∈ I.V) : ∀ x ∈ ball I v r, x ∈ I.V :=
  fun x ⟨p, _⟩ => Inst.support_subset le_rfl p hv x p.end_mem_support

/-- A proof of size `0` looks like the empty proof to every node. -/
lemma apply_eq_emptyProof {A : Verifier L} {r : ℕ} (hA : IsLocal r A) {I : Inst L} {Pf : Proof}
    (hPf : SizeLE I Pf 0) {v : ℕ} (hv : v ∈ I.V) : A I Pf v = A I emptyProof v :=
  hA I Pf I emptyProof v (viewEq_of_nbrs (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    fun x hx => List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (hPf x (ball_subset_V hv x hx))))

/-- **Section 7.3 of [GS16]** (`coLCP(0) ⊆ LogLCP` on connected graphs; unnumbered in the paper).
Let `F` be the family of connected graphs with identifiers in `{1, …, n^c}`. If `P` admits
locally checkable proofs of size `0` on `F`, then its complement `F \ P` admits locally checkable
proofs of size `O(log n)`. -/
theorem coLCP0_logLCP (c : ℕ) {P : Set (Inst L)} (hP : AdmitsLCP (connIdFamily c) P (fun _ => 0)) :
    LogLCP (connIdFamily c) (connIdFamily c \ P) := by
  classical
  obtain ⟨r₀, A, hA, hcomp, hsound⟩ := hP
  let Chk : Inst L → (ℕ → List ℕ) → ℕ → Prop := fun I Q v =>
    TreeOK I.G I.G (natField 0 Q) (natField 1 Q) (natField 2 Q) v ∧
      (v = natField 0 Q v → A I emptyProof v = false)
  refine logLCP_of_nats 3 (c + 1) (max r₀ 1) (fun I Q v => decide (Chk I Q v))
    (fun I Q I' Q' v hv => ?_) (fun I hI hIP => ?_) (fun I hI hIP Q => ?_)
  · have h1 := hv.nbr1Eq (le_max_right _ _)
    have hv' := hv.restrict_radius (le_max_left r₀ 1)
    have hA' : A I emptyProof v = A I' emptyProof v :=
      hA _ _ _ _ v ⟨hv'.ball_eq, hv'.adj, hv'.sadj, hv'.mem, hv'.lab, fun _ _ => rfl⟩
    simp only [Chk, decide_eq_decide]
    rw [hA', (h1.field 0).2]
    exact and_congr (h1.treeOK h1.adj le_rfl 0 1 2) Iff.rfl
  · obtain ⟨hc, hb⟩ := hI
    obtain ⟨a, ha, hrej⟩ := hsound I ⟨hc, hb⟩ hIP.2 emptyProof
    obtain ⟨par, hpar⟩ := treeOK_complete le_rfl fun v hv => hc.2 v hv a ha
    refine ⟨fun v => [a, I.G.dist v a, par v], fun v hv => ⟨by simp, ?_⟩,
      fun v hv => decide_eq_true ⟨(hpar v hv).1, fun hva => ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      · exact le_pow_succ_of_idBound hb hv (Or.inl ha)
      · exact le_pow_succ_of_idBound hb hv (Or.inr (hpar v hv).2.1.le)
      · exact le_pow_succ_of_idBound hb hv (Or.inl (hpar v hv).2.2)
    · have : v = a := hva
      subst this; exact hrej
  · have hIP' : I ∈ P := by by_contra h; exact hIP ⟨hI, h⟩
    obtain ⟨Pf, hPf, hacc⟩ := hcomp I hI hIP'
    by_contra hall
    push Not at hall
    have acc : ∀ v ∈ I.V, Chk I Q v := fun v hv => by simpa using hall v hv
    obtain ⟨a, ha, hrt, -⟩ := treeOK_sound hI.1 le_rfl fun v hv => (acc v hv).1
    have h1 := (acc a ha).2 (hrt a ha).symm
    have h2 := hacc a ha
    rw [apply_eq_emptyProof hA hPf ha, h1] at h2
    exact Bool.false_ne_true h2

end Podc.LocallyCheckableProofs
