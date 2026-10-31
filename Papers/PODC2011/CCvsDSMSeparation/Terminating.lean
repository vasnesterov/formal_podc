import Papers.PODC2011.CCvsDSMSeparation.Trace

/-!
# The paper's notion of termination (Section 2)

An *infinite history* is a sequence of events all of whose finite prefixes are executions. It is
*fair* if every participating process takes infinitely many steps or eventually terminates (stays
idle forever; stopping in the middle of a call would be a crash). An algorithm is *terminating*
if in every fair infinite history (with at most one call to `Signal()`) every call completes
after finitely many steps of its process. (Finite fair histories end with all participants
terminated, so all their calls are complete.)

`Terminating.soloTerminating`: this implies the solo form `SoloTerminating` used in the lower
bound proof.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

/-- The first `n` events of an infinite history. -/
def pre (h : ℕ → Ev N V Val) (n : ℕ) : List (Ev N V Val) := (List.range n).map h

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- An infinite history of `A`. -/
def InfExec (h : ℕ → Ev N V Val) : Prop := ∀ n, A.Valid (pre h n)

/-- Fairness (Section 2): every participant takes infinitely many steps or terminates. -/
def Fair (h : ℕ → Ev N V Val) : Prop :=
  ∀ p, (∃ n, (h n).p = p) →
    (∀ n, ∃ m ≥ n, (h m).p = p) ∨ ∃ n, (∀ m ≥ n, (h m).p ≠ p) ∧ A.Idle (pre h n) p

/-- **Terminating** (Section 2): in every fair history without crashes (and with at most one call
to `Signal()`), each call to a procedure completes after finitely many steps. -/
def Terminating : Prop :=
  ∀ h : ℕ → Ev N V Val, A.InfExec h → (∀ n, signals (pre h n) ≤ 1) → A.Fair h →
    ∀ n o, (h n).op = .inv o → ∃ m > n, (h m).p = (h n).p ∧ ∃ b, (h m).op = .ret b

/-! ### From the paper's termination to solo termination -/

lemma lstep_busy_cases {p : Fin N} {c : LState S} {s' : S} {o : Proc} {op : Op V Val}
    (h : A.lstep p c op = some (s', some o)) :
    (op = .inv o ∧ c.2 = none) ∨ (op.isAccess = true ∧ c.2 = some o) := by
  rcases c with ⟨s, _ | o'⟩
  · cases op with
    | inv o' =>
      simp only [lstep, Option.some.injEq, Prod.mk.injEq] at h
      left; exact ⟨by rw [h.2], rfl⟩
    | _ => simp [lstep] at h
  · right
    simp only [lstep] at h
    rcases hact : A.act p s with ⟨v, k⟩ | ⟨v, x, s''⟩ | ⟨b, s''⟩ <;> cases op <;>
      simp [hact] at h <;> simp_all [Op.isAccess]

/-- A busy process is in the middle of a call it invoked and has not returned from. -/
lemma busy_decomp {τ : List (Ev N V Val)} {p : Fin N} {o : Proc} (hv : A.Valid τ)
    (hb : A.Busy τ p o) :
    ∃ τ₁ τ₂, τ = τ₁ ++ ⟨p, .inv o⟩ :: τ₂ ∧ ∀ e ∈ τ₂, e.p = p → e.op.isAccess = true := by
  induction τ using List.reverseRecOn with
  | nil => obtain ⟨s, hs⟩ := hb; simp [state] at hs
  | append_singleton τ e ih =>
    have hv' := Valid.of_append A hv
    by_cases hep : e.p = p
    · subst hep
      obtain ⟨s, hs⟩ := hb
      rw [state_snoc_self] at hs
      rcases hc : A.state τ e.p with _ | c
      · simp [hc] at hs
      rw [hc, Option.bind_some] at hs
      rcases A.lstep_busy_cases hs with ⟨hop, -⟩ | ⟨hop, hc2⟩
      · rcases e with ⟨p, op⟩; simp only at hop; subst hop
        exact ⟨τ, [], by simp, by simp⟩
      · obtain ⟨τ₁, τ₂, h1, h2⟩ := ih hv' ⟨c.1, by rw [hc, ← hc2]⟩
        refine ⟨τ₁, τ₂ ++ [e], by simp [h1], fun e' he' _ => ?_⟩
        rcases List.mem_append.1 he' with he' | he'
        · exact h2 e' he' (by assumption)
        · simp at he'; subst he'; exact hop
    · obtain ⟨τ₁, τ₂, h1, h2⟩ := ih hv' (A.busy_of_proj_eq hb (proj_snoc_ne _ _ hep).symm)
      refine ⟨τ₁, τ₂ ++ [e], by simp [h1], fun e' he' hp => ?_⟩
      rcases List.mem_append.1 he' with he' | he'
      · exact h2 e' he' hp
      · simp at he'; subst he'; exact absurd hp hep

/-- The next step of a process in local state `s` (the value of a read is the current value). -/
noncomputable def nextEvOf (p : Fin N) (s : S) (ρ : List (Ev N V Val)) : Ev N V Val :=
  match A.act p s with
  | .read v _ => ⟨p, .read v (A.memVal ρ v)⟩
  | .write v x _ => ⟨p, .write v x⟩
  | .ret b _ => ⟨p, .ret b⟩

/-- The next step of a busy process. -/
noncomputable def nextEv (p : Fin N) (ρ : List (Ev N V Val)) : Ev N V Val :=
  match A.state ρ p with
  | some (s, _) => A.nextEvOf p s ρ
  | none => ⟨p, .ret false⟩

lemma nextEv_eq {ρ : List (Ev N V Val)} {p : Fin N} {s : S} {st : Option Proc}
    (h : A.state ρ p = some (s, st)) : A.nextEv p ρ = A.nextEvOf p s ρ := by
  simp [nextEv, h]

lemma nextEv_p (ρ : List (Ev N V Val)) (p : Fin N) : (A.nextEv p ρ).p = p := by
  unfold nextEv; split
  · unfold nextEvOf; split <;> rfl
  · rfl

lemma nextEv_stepOK {ρ : List (Ev N V Val)} {p : Fin N} {o : Proc} (hb : A.Busy ρ p o) :
    A.StepOK ρ (A.nextEv p ρ) := by
  obtain ⟨s, hs⟩ := hb
  rw [A.nextEv_eq hs]
  have hl : ∀ op : Op V Val, (A.lstep p (s, some o) op).isSome →
      (A.lrun p (proj ρ p ++ [op])).isSome := by
    intro op h
    rw [lrun_snoc]
    change ((A.state ρ p).bind fun c => A.lstep p c op).isSome
    rw [hs]; exact h
  unfold nextEvOf
  rcases hact : A.act p s with ⟨v, k⟩ | ⟨v, x, s'⟩ | ⟨b, s'⟩
  · exact ⟨hl _ (by simp [lstep, hact]), fun v' x' h => by cases h; rfl⟩
  · exact ⟨hl _ (by simp [lstep, hact]), fun v' x' h => by cases h⟩
  · exact ⟨hl _ (by simp [lstep, hact]), fun v' x' h => by cases h⟩

/-- `Terminating` implies `SoloTerminating`. -/
theorem Terminating.soloTerminating (hT : A.Terminating) : A.SoloTerminating := by
  classical
  intro τ p o hv hsig hidle hbusy
  by_contra hno
  push Not at hno
  -- the solo run of `p` never returns
  let run : ℕ → List (Ev N V Val) := fun k => Nat.rec τ (fun _ ρ => ρ ++ [A.nextEv p ρ]) k
  have run_succ : ∀ k, run (k + 1) = run k ++ [A.nextEv p (run k)] := fun _ => rfl
  have hrun : ∀ k, ∃ σ, run k = τ ++ σ ∧ (∀ e ∈ σ, e.p = p ∧ e.op.isAccess = true) ∧
      A.Valid (run k) ∧ A.Busy (run k) p o := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp [run], by simp, hv, hbusy⟩
    | succ k ih =>
      obtain ⟨σ, hσ, hσp, hvk, hbk⟩ := ih
      have hs := A.nextEv_stepOK hbk
      have hvk' : A.Valid (run k ++ [A.nextEv p (run k)]) := (A.valid_snoc _ _).2 ⟨hvk, hs⟩
      have hep : (A.nextEv p (run k)).p = p := A.nextEv_p _ _
      -- the next step is not a return
      have hacc : (A.nextEv p (run k)).op.isAccess = true := by
        rcases he : A.nextEv p (run k) with ⟨q, op⟩
        rw [he] at hep; simp only at hep; subst hep
        cases op with
        | ret b =>
          exfalso
          refine hno σ b hσp ?_
          rw [← hσ, ← he]; exact hvk'
        | inv o' =>
          exfalso
          obtain ⟨s₁, hs₁⟩ := hbk
          rw [A.nextEv_eq hs₁] at he
          unfold nextEvOf at he
          split at he <;> simp at he
        | _ => rfl
      refine ⟨σ ++ [A.nextEv p (run k)], by rw [run_succ, hσ]; simp, ?_, hvk', ?_⟩
      · intro e he; rcases List.mem_append.1 he with he | he
        · exact hσp e he
        · simp at he; subst he; exact ⟨hep, hacc⟩
      · rw [run_succ]
        have := A.busy_append_access hbk (σ := [A.nextEv p (run k)]) hvk' (by simp [hep, hacc])
        simpa using this
  -- the infinite history
  let h : ℕ → Ev N V Val := fun n =>
    if hn : n < τ.length then τ[n] else A.nextEv p (run (n - τ.length))
  have hlen : ∀ k, (run k).length = τ.length + k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [run_succ, List.length_append, ih]; simp; omega
  have hpre : ∀ k, pre h (τ.length + k) = run k := by
    intro k
    induction k with
    | zero =>
      apply List.ext_getElem (by simp [pre, run])
      intro i h1 h2
      simp only [pre, List.getElem_map, List.getElem_range]
      simp only [pre, List.length_map, List.length_range] at h1
      have hi : i < τ.length := by omega
      simp only [h, hi, dite_true]; rfl
    | succ k ih =>
      rw [show τ.length + (k + 1) = (τ.length + k) + 1 by omega, pre, List.range_succ,
        List.map_append, ← pre, ih, run_succ]
      simp [h]
  have hpre_le : ∀ n, n ≤ τ.length → pre h n = τ.take n := by
    intro n hn
    apply List.ext_getElem (by simp [pre]; omega)
    intro i h1 h2
    simp only [pre, List.length_map, List.length_range] at h1
    simp [pre, h, List.getElem_take, show i < τ.length by omega]
  have hvalid : A.InfExec h := by
    intro n
    by_cases hn : n ≤ τ.length
    · rw [hpre_le n hn]; exact Valid.of_prefix A hv (List.take_prefix _ _)
    · obtain ⟨k, rfl⟩ : ∃ k, n = τ.length + k := ⟨n - τ.length, by omega⟩
      rw [hpre k]; obtain ⟨-, -, -, hvk, -⟩ := hrun k; exact hvk
  have hsigs : ∀ n, signals (pre h n) ≤ 1 := by
    intro n
    by_cases hn : n ≤ τ.length
    · rw [hpre_le n hn]
      exact (List.Sublist.countP_le (List.take_prefix n τ).sublist).trans hsig
    · obtain ⟨k, rfl⟩ : ∃ k, n = τ.length + k := ⟨n - τ.length, by omega⟩
      rw [hpre k]
      obtain ⟨σ, hσ, hσp, -⟩ := hrun k
      rw [hσ, signals_append, signals_eq_zero (fun e he => Op.isSigInv_eq_false_of_isAccess
        (hσp e he).2)]
      exact hsig
  have hhp : ∀ m, τ.length ≤ m → (h m).p = p ∧ (h m).op.isAccess = true := by
    intro m hm
    have : h m = A.nextEv p (run (m - τ.length)) := by simp [h, show ¬ m < τ.length by omega]
    obtain ⟨σ, hσ, hσp, -⟩ := hrun (m - τ.length + 1)
    have hmem : A.nextEv p (run (m - τ.length)) ∈ σ := by
      have := hσ ▸ (run_succ (m - τ.length))
      obtain ⟨σ', hσ', -⟩ := hrun (m - τ.length)
      rw [hσ', List.append_assoc] at this
      have := List.append_cancel_left this
      rw [this, hσ']; simp
    rw [this]; exact hσp _ hmem
  have hfair : A.Fair h := by
    intro q _
    by_cases hqp : q = p
    · left; intro n; exact ⟨max n τ.length, le_max_left _ _, hqp ▸ (hhp _ (le_max_right _ _)).1⟩
    · right
      refine ⟨τ.length, fun m hm heq => hqp (heq ▸ (hhp m hm).1), ?_⟩
      rw [show τ.length = τ.length + 0 by rfl, hpre 0]
      exact hidle q hqp
  -- `p`'s pending call never returns
  obtain ⟨τ₁, τ₂, hτ, hτ₂⟩ := A.busy_decomp hv hbusy
  have hn₀ : τ₁.length < τ.length := by rw [hτ]; simp
  have hh₀ : h τ₁.length = ⟨p, .inv o⟩ := by simp [h, hτ]
  obtain ⟨m, hm, hmp, b, hmb⟩ := hT h hvalid hsigs hfair τ₁.length o (by rw [hh₀])
  rw [hh₀] at hmp
  by_cases hmτ : m < τ.length
  · have hm' : h m = τ[m] := by simp [h, hmτ]
    have hmem : τ[m] ∈ τ₂ := by
      have : τ[m] = τ₂[m - τ₁.length - 1]'(by
        have : τ.length = τ₁.length + 1 + τ₂.length := by rw [hτ]; simp; omega
        omega) := by
        simp only [hτ]
        rw [List.getElem_append_right (by omega)]
        rw [List.getElem_cons]
        split
        · omega
        · congr 1
      rw [this]; exact List.getElem_mem _
    have := hτ₂ _ hmem (by rw [← hm']; exact hmp)
    rw [← hm', hmb] at this; simp [Op.isAccess] at this
  · have := (hhp m (by omega)).2
    rw [hmb] at this; simp [Op.isAccess] at this

end Algorithm

end Podc.CCvsDSMSeparation
