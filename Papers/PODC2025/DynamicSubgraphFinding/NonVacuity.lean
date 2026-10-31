import Papers.PODC2025.DynamicSubgraphFinding.Model

/-!
# Non-vacuity of the model

With unbounded bandwidth (every node sends its whole neighbourhood, `n` bits), `MemDetect(K_s)`
and `Detect(K_s)` are solvable in one round in every insertion-only dynamic network: a node lies in
an `s`-clique iff its closed neighbourhood contains one, and in one round it learns all edges
between its neighbours. So the `Solves` hypotheses of Theorems 1.3 and 1.6 are not vacuous; the
lower bounds are genuinely about bandwidth.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

variable {V : Type}

/-- The full-neighbourhood algorithm: state = (own identifier, current output). -/
noncomputable def fullNbrAlg (s : ℕ) : Algorithm V (Set V) Bool where
  State := V × Bool
  init P0 G0 v := (v, decide (P0 v ∧ ∃ Q : Finset V, (SimpleGraph.fromRel G0).IsNClique s Q ∧ v ∈ Q))
  send _ _ x _ := match x with
    | some N => N
    | none => ∅
  recv _ st x inbox := (st.1, match x with
    | none => false
    | some N => decide (∃ Q : Finset V, Q.card = s ∧ st.1 ∈ Q ∧ (∀ y ∈ Q, y ≠ st.1 → y ∈ N) ∧
        ∀ y ∈ Q, ∀ z ∈ Q, y ≠ z → y ≠ st.1 → z ≠ st.1 → ∃ S, inbox y = some S ∧ z ∈ S))
  out st := st.2

lemma fullNbrAlg_fst (s : ℕ) (D : InsNet V) (r : ℕ) (v : V) :
    ((fullNbrAlg s).state D r v).1 = v := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Algorithm.state_succ]; exact ih

lemma fromRel_eq (D : InsNet V) : SimpleGraph.fromRel (D.adj 0) = D.graph 0 := by
  ext u v
  simp only [SimpleGraph.fromRel_adj, InsNet.graph]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact D.symm _ _ _ h
  · intro h
    exact ⟨fun e => D.irrefl 0 v (e ▸ h), Or.inl h⟩

/-- The full-neighbourhood algorithm solves `MemDetect(K_s)` in one round, in every
insertion-only dynamic network. -/
theorem fullNbrAlg_memDetect (s : ℕ) (hs : 1 ≤ s) (D : InsNet V) (r : ℕ) :
    MemDetectOK s (fullNbrAlg s) D r := by
  intro v hv
  unfold Algorithm.output
  cases r with
  | zero =>
    simp only [Algorithm.state, fullNbrAlg, fromRel_eq, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  | succ r =>
    rw [Algorithm.state_succ]
    have hfst := fullNbrAlg_fst s D r v
    have hloc : D.loc (r + 1) v = some {u | D.adj (r + 1) u v} := by
      simp only [InsNet.loc, if_pos hv]
    rw [hloc]
    change decide (∃ Q : Finset V, Q.card = s ∧ ((fullNbrAlg s).state D r v).1 ∈ Q ∧ _) = true ↔ _
    rw [hfst, decide_eq_true_iff]
    constructor
    · rintro ⟨Q, hcard, hvQ, hN, hadj⟩
      refine ⟨Q, ⟨fun y hy z hz hyz => ?_, hcard⟩, hvQ⟩
      show D.adj (r + 1) y z
      by_cases hyv : y = v
      · subst hyv; exact D.symm _ _ _ (hN z hz (Ne.symm hyz))
      by_cases hzv : z = v
      · subst hzv; exact hN y hy hyv
      obtain ⟨S, hS, hzS⟩ := hadj y hy z hz hyz hyv hzv
      unfold Algorithm.inbox at hS
      split_ifs at hS with h
      have hpy : D.pres (r + 1) y := D.pres_of_adj _ _ _ h
      simp only [InsNet.loc, if_pos hpy, Option.some.injEq] at hS
      rw [← hS] at hzS
      exact D.symm _ _ _ hzS
    · rintro ⟨Q, hQ, hvQ⟩
      refine ⟨Q, hQ.card_eq, hvQ, fun y hy hyv => ?_, fun y hy z hz hyz hyv hzv => ?_⟩
      · exact D.symm _ _ _ (hQ.isClique hvQ hy (Ne.symm hyv))
      · have hyv' : D.adj (r + 1) y v := hQ.isClique hy hvQ hyv
        refine ⟨{u | D.adj (r + 1) u y}, ?_, D.symm _ _ _ (hQ.isClique hy hz hyz)⟩
        unfold Algorithm.inbox
        have hpy : D.pres (r + 1) y := D.pres_of_adj _ _ _ hyv'
        simp only [if_pos hyv', InsNet.loc, if_pos hpy]
        rfl

/-- Hence `MemDetect(K_s)` is solvable (with large messages) in both models. -/
theorem memDetect_solvable (s : ℕ) (hs : 1 ≤ s) (Model : InsNet V → Prop) (Δ : ℕ) :
    Solves (fullNbrAlg s) Model Δ (MemDetectOK s) :=
  fun D _ _ r => fullNbrAlg_memDetect s hs D r

/-- And so is `Detect(K_s)`. -/
theorem detect_solvable (s : ℕ) (hs : 2 ≤ s) (Model : InsNet V → Prop) (Δ : ℕ) :
    Solves (fullNbrAlg s) Model Δ (DetectOK s) := by
  intro D _ _ r
  have h := fullNbrAlg_memDetect s (by omega) D r
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨v, hv⟩ : Q.Nonempty := Finset.card_pos.mp (by rw [hQ.card_eq]; omega)
    have hp : D.pres r v := by
      have hcard := hQ.card_eq
      obtain ⟨w, hw, hwv⟩ : ∃ w ∈ Q, w ≠ v := by
        by_contra hc
        push_neg at hc
        have : Q ⊆ {v} := fun w hw => Finset.mem_singleton.mpr (hc w hw)
        have := Finset.card_le_card this
        simp at this
        omega
      exact D.pres_of_adj _ _ _ (hQ.isClique hv hw (Ne.symm hwv))
    exact ⟨v, hp, (h v hp).2 ⟨Q, hQ, hv⟩⟩
  · rintro ⟨v, hp, hv⟩
    obtain ⟨Q, hQ, -⟩ := (h v hp).1 hv
    exact ⟨Q, hQ⟩

end Podc.DynamicSubgraphFinding
