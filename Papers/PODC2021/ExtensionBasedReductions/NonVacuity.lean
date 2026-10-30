import Papers.PODC2021.ExtensionBasedReductions.Main

/-!
# Non-vacuity checks

* `hasAugEBProof_of_spec_empty`: augmented extension-based proofs exist (for a task without valid
  outputs, the trivial prover wins at once), so `HasAugEBProof` is not vacuous.
* `idProt_solves`, `isReduction_self`: the hypotheses of `theorem1` are satisfiable: every task
  reduces to itself through the identity tasks, solved by the one-round IS protocol "output your
  input", and the identity task `R₂` is solvable without communication.
* `waitFree_of_isIS`: IS protocols in normal form are wait-free.
* `not_hasProof_of_solves`, `not_hasAugEBProof_of_solves`: soundness of the game; a task solvable
  in the NIS model has no (augmented) extension-based impossibility proof.
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P X Y : Type} [DecidableEq P] [Fintype P]

/-- IS protocols (in normal form) are wait-free. -/
lemma waitFree_of_isIS [Inhabited Y] {δ : Protocol P X Y} {t : ℕ} (hIS : IsIS δ t) (ht : 0 < t) : WaitFree δ := by
  rintro x ⟨f, hf⟩
  have hk := hf (Fintype.card P * (2 * t) + 1)
  have hR : Reach δ (exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)) :=
    (reach_initC x).run hk
  have h1 := measure_exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)
  have h0 : totalDepth (initC x : Config P X) = 0 := by simp [totalDepth, initC, St.depth]
  have h2 : totalDepth (exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)) ≤
      Fintype.card P * (2 * t) := by
    unfold totalDepth
    calc _ ≤ ∑ _j : P, 2 * t := Finset.sum_le_sum fun j _ => by
          by_cases hj : (decided δ (exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)
            j)).isSome
          · exact (hR.depth_fin hIS ht hj).le
          · exact (hR.depth_unfin hIS ht (by simpa using hj)).le
      _ = Fintype.card P * (2 * t) := by simp
  simp at h1; omega

/-- The identity task on the input vectors `I`. -/
def idTask (I : Set (P → X)) : Task P X X := ⟨I, fun x => {x}⟩

/-- The one-round protocol "output your input". -/
def idProt : Protocol P X X := fun s => if s.rounds = 1 then some s.input else none

lemma idProt_isIS : IsIS (idProt : Protocol P X X) 1 := fun s v => by
  simp only [idProt]; split_ifs with h <;> simp [h]

lemma idProt_solves [Inhabited X] (I : Set (P → X)) : Solves (idProt : Protocol P X X) (idTask I) := by
  refine ⟨waitFree_of_isIS idProt_isIS one_pos, fun x _ α hα hfin => ⟨x, rfl, fun q => ?_⟩⟩
  have hq := hfin q
  unfold Active at hq
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hq
  have hs : (exec (initC x) α q).IsScan := by
    cases h : exec (initC x) α q <;> simp_all [St.IsScan]
  unfold outs
  cases h : exec (initC x) α q with
  | init i z => rw [h] at hs; exact absurd hs id
  | upd s => rw [h] at hs; exact absurd hs id
  | scan s v =>
    rw [h] at hy
    simp only [decided_scan, idProt] at hy ⊢
    split_ifs at hy ⊢ with hr
    have := input_exec (initC x) α q
    rw [h] at this; simp only [St.input, initC] at this ⊢; rw [this]

/-- Every task reduces to itself (`R₁`, `R₂` identity tasks). -/
lemma isReduction_self {Y : Type} [Inhabited X] [Inhabited Y] (T : Task P X Y) :
    IsReduction T T (idTask T.inputs) (idTask Set.univ) where
  solv1 := ⟨idProt, idProt_solves _⟩
  solv2 := ⟨idProt, idProt_solves _⟩
  sub := fun x _ z ⟨w, ⟨y, hy, hw⟩, hz⟩ => by
    simp only [idTask, Set.mem_singleton_iff] at hy hz; subst hy; subst hz; exact hw
  wf_in := fun _ h => h
  wf1 := fun x hx u hu => by simp only [idTask, Set.mem_singleton_iff] at hu; subst hu; exact hx
  wf2 := fun _ _ _ _ => Set.mem_univ _

lemma locallySolvable_id {Y : Type} : LocallySolvable (idTask (Set.univ : Set (P → Y)))
    (fun _ w => w) := fun _ _ => rfl

/-- `theorem1` applies to the trivial self-reduction (so its hypotheses are satisfiable). -/
example {Y : Type} [Inhabited X] [Inhabited Y] [Finite X] [Finite Y] (T : Task P X Y)
    (h : HasAugEBProof T) : HasAugEBProof T :=
  theorem1 (isReduction_self T) locallySolvable_id h

/-- A task without valid outputs has an augmented extension-based impossibility proof: the trivial
prover (which only asks the empty assignment query) wins, as it has reached an initial
configuration whose input vector is an input vector of the task. -/
theorem hasAugEBProof_of_spec_empty [Inhabited X] {T : Task P X Y} {x0 : P → X}
    (hx0 : x0 ∈ T.inputs) (hT : ∀ x, T.spec x = ∅) : HasAugEBProof T := by
  refine ⟨fun h => .oracle (initC default) (∅, fun _ => none), fun δ pl hc hv => ?_⟩
  have hst : ∀ k, states pl k = GState.start := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => show (states pl k).next (pl k).1 = _; rw [hc k, ih]; rfl
  refine ⟨fun k => ?_, Or.inl ⟨0, initC x0, Or.inl ⟨x0, (reinit_initC _ _).symm⟩, ?_⟩⟩
  · rw [hc k, hst k]
    exact ⟨Or.inl ⟨default, (reinit_initC _ _).symm⟩, fun q hq => by simp at hq⟩
  · have hin : inputs (initC x0 : Config P X) = x0 := rfl
    refine ⟨by rw [hin]; exact hx0, fun ⟨y, hy, _⟩ => ?_⟩
    rw [hin, hT] at hy; exact hy

/-- **Soundness of the game** (sanity check of the definitions): a task that is solvable in the NIS
model has no (augmented) extension-based impossibility proof. Hence `HasAugEBProof S`, the conclusion
of `theorem1`, is a genuine impossibility statement. (Finite input type, as in the paper.) -/
theorem not_hasProof_of_solves {Y Q O : Type} [Inhabited X] [Finite X]
    {spec : OracleSpec P X Y Q O} (htot : spec.Total) {T : Task P X Y} {δ : Protocol P X Y}
    (hs : Solves δ T) : ¬ HasProof spec T := by
  rintro ⟨σ, hσ⟩
  obtain ⟨pl, hc, hv, -⟩ := exists_extension htot σ δ
    (fun _ => (.endPhase (initC default), .ack)) 0 (by simp) (by simp)
  obtain ⟨hl, hwin⟩ := hσ δ pl hc hv
  obtain ⟨N, hN⟩ := ISConv.exists_bound_of_waitFree hs.1
  have hbd : ∀ C, Reach δ C → totalDepth C ≤ N := by
    rintro C ⟨x, α, hα, rfl⟩
    have h0 : totalDepth (initC x : Config P X) = 0 := by simp [totalDepth, initC, St.depth]
    rw [measure_exec, h0]; simpa using hN x α hα
  rcases hwin with ⟨k, C, hC, hvi⟩ | hinf | ⟨K, hK⟩
  · -- (W1) a correct protocol never reaches a violation
    obtain ⟨x, α, hα, rfl⟩ := (ginv_states hl k).reach hC
    obtain ⟨β, hβ, hfin⟩ := hs.1.exists_final ((reach_initC x).run hα)
    have hin : inputs (exec (initC x) α) = x := funext fun j => by
      simp [inputs, input_exec, initC, St.input]
    rw [Violates, hin] at hvi
    obtain ⟨y, hy, hyo⟩ := hs.2 x hvi.1 (α ++ β) ((isSched_append _ _ _).2 ⟨hα, hβ⟩)
      (by rw [exec_append]; exact hfin)
    refine hvi.2 ⟨y, hy, fun q z hq => ?_⟩
    have hq' := hyo q
    rw [outs] at hq
    rw [exec_append, outs, exec_of_terminated hβ (by rw [hq]; simp), hq] at hq'
    exact (Option.some.inj hq').symm
  · -- (W2) phase ends strictly increase the depth of the base, which is bounded
    obtain ⟨K', -, hK'⟩ := eventually_not_of_bounded (fun k => totalDepth (states pl k).base) 0 N
      (fun k => IsEnd (pl k).1)
      (fun k _ => by
        show _ ≤ totalDepth ((states pl k).next (pl k).1).base
        have hlk := hl k
        cases hm : (pl k).1 with
        | query C q => exact le_rfl
        | oracle C o => exact le_rfl
        | endPhase C =>
          rw [hm] at hlk
          exact (measure_lt_of_mem_resp (ginv_states hl k) hlk).le)
      (fun k _ ⟨C, hm⟩ => by
        show _ < totalDepth ((states pl k).next (pl k).1).base
        have hlk := hl k
        rw [hm] at hlk ⊢
        exact measure_lt_of_mem_resp (ginv_states hl k) hlk)
      (fun k _ => hbd _ (ginv_states hl k).1)
    obtain ⟨k, hk, hE⟩ := hinf K'
    exact hK' k hk hE
  · -- (W3) an infinite chain of queries is an infinite schedule
    have hch : ∀ i, ∃ C q, (pl (K + i)).1 = .query C q ∧ i ≤ totalDepth C := by
      intro i
      induction i with
      | zero =>
        obtain ⟨C, q, -, h1, -⟩ := hK K le_rfl
        exact ⟨C, q, h1, Nat.zero_le _⟩
      | succ i ih =>
        obtain ⟨C, q, h1, h2⟩ := ih
        obtain ⟨C', q0, q', h3, h4⟩ := hK (K + i) (by omega)
        rw [h1] at h3
        obtain ⟨rfl, rfl⟩ := Move.query.inj h3
        refine ⟨step C q, q', by rw [← add_assoc]; exact h4, ?_⟩
        rw [measure_step]; omega
    obtain ⟨C, q, h1, h2⟩ := hch (N + 1)
    have hlk := hl (K + (N + 1))
    rw [h1] at hlk
    have := hbd C ((ginv_states hl _).reach hlk.1)
    omega

/-- In particular there is no augmented extension-based proof for a task solvable in the NIS model. -/
theorem not_hasAugEBProof_of_solves {Y : Type} [Inhabited X] [Finite X] {T : Task P X Y}
    {δ : Protocol P X Y} (hs : Solves δ T) : ¬ HasAugEBProof T :=
  not_hasProof_of_solves assignSpec_total hs

end Podc.ExtensionBasedReductions
