import Papers.PODC2015.ABADetection.Defs

/-!
# Common constructions of the lower-bound proofs

* `exists_round`: from a configuration where all processes outside `ps` (including the writer)
  are idle, let `ps` finish their pending operations solo, then let the writer `w0` run one
  round `ws` solo; the result is quiescent (paper, Lemmas 1 and 3: the schedules `γᵢ`).
* `clean_of_split`, `dirty_of_split`: the clean and dirty executions built in the proofs of
  Lemmas 1 and 3 are `p`-clean, respectively `p`-dirty.
* `chain_extends`: executions of a chain extend each other.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ABADetection

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L} {w0 : P} {rd : P → A.Op} {ws : List A.Op}

omit [DecidableEq ι] in
lemma mem_opsOf_of_inv_mem {α : List (Label P A)} {q : P} {o : A.Op} (h : Label.inv q o ∈ α) :
    o ∈ opsOf α q := by
  simp only [opsOf, List.mem_filterMap]
  exact ⟨_, h, by simp [Label.invOf]⟩

lemma runFrom_of_run_append {α β : List (Label P A)} {C D : Config A B P L}
    (h : I.run (α ++ β) = some C) (hα : I.run α = some D) : I.runFrom D β = some C := by
  rw [Impl.run_append_of_eq I hα] at h; exact h

omit [DecidableEq ι] in
lemma Std.append {α β : List (Label P A)} (h : Std w0 rd ws α) (h' : ∀ q o, Label.inv q o ∈ β →
    (q = w0 ∧ o ∈ ws) ∨ (q ≠ w0 ∧ o = rd q)) : Std w0 rd ws (α ++ β) := by
  intro q o hm
  rcases List.mem_append.1 hm with hm | hm
  · exact h q o hm
  · exact h' q o hm

omit [DecidableEq ι] in
lemma not_inv_mem_of_opsOf {β : List (Label P A)} (h : ∀ q, opsOf β q = []) (q : P) (o : A.Op) :
    Label.inv q o ∉ β := fun hm => by
  have := mem_opsOf_of_inv_mem hm; rw [h q] at this; simp at this

-- CSLib candidate: SharedMemory/Solo.lean (finish pending ops, then a solo round)
/-- **One round** (paper, Lemma 1: the schedule `γᵢ`): the processes of `ps` finish their pending
operations solo, then the writer runs its round `ws` solo. -/
theorem exists_round (hof : I.ObstructionFree) (hws : ∀ o ∈ ws, I.allowed w0 o) (ps : List P)
    (hw0 : w0 ∉ ps) {α : List (Label P A)} {D : Config A B P L} (hα : I.run α = some D)
    (hstd : Std w0 rd ws α) (hidle : ∀ q, q ∉ ps → D.pend q = none) :
    ∃ γ Q', I.runFrom D γ = some Q' ∧ Q'.Quiescent ∧ (∀ ℓ ∈ γ, ℓ.proc ∈ w0 :: ps) ∧
      Std w0 rd ws (α ++ γ) ∧ (∀ q, q ≠ w0 → opsOf γ q = []) ∧ opsOf γ w0 = ws ∧
      (respsOf γ w0).length = ws.length := by
  obtain ⟨γ₁, F, hγ₁, hops₁, hr₁, hfin₁, hoth₁⟩ :=
    Impl.exists_finish (I := I) (E := fun _ => True) (hof.obstructionFreeOn _)
      (fun _ _ _ _ => trivial) ps hα trivial
  have hαF : I.run (α ++ γ₁) = some F := by rw [Impl.run_append_of_eq I hα, hr₁]
  have hFw : F.pend w0 = none := by rw [(hoth₁ w0 hw0).2]; exact hidle w0 hw0
  obtain ⟨Q', h1, h2, h3, h4, h5⟩ := I.soloOps_spec hof w0 ws hws hαF hFw
  refine ⟨γ₁ ++ I.soloOps w0 F ws, Q', by rw [Impl.runFrom_append_of_eq I hr₁, h1], ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = w0
    · subst hq; exact h2
    · rw [(I.runFrom_other h1 (fun ℓ hℓ => by rw [h3 ℓ hℓ]; exact Ne.symm hq)).2]
      by_cases hqs : q ∈ ps
      · exact hfin₁ q hqs
      · rw [(hoth₁ q hqs).2]; exact hidle q hqs
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · exact List.mem_cons_of_mem _ (hγ₁ ℓ h)
    · rw [h3 ℓ h]; exact List.mem_cons_self
  · rw [← List.append_assoc]
    refine (hstd.append fun q o hm => absurd hm (not_inv_mem_of_opsOf hops₁ q o)).append ?_
    intro q o hm
    have hq : q = w0 := h3 _ hm
    subst hq
    exact Or.inl ⟨rfl, by rw [← h4]; exact mem_opsOf_of_inv_mem hm⟩
  · intro q hq
    rw [opsOf_append, hops₁ q, opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [h3 ℓ hℓ]; exact Ne.symm hq)]
    rfl
  · rw [opsOf_append, hops₁ w0, h4]; rfl
  · rw [respsOf_append, List.length_append, h5,
      respsOf_eq_nil_of_proc_ne (fun ℓ hℓ h => hw0 (by rw [← h]; exact hγ₁ ℓ hℓ))]
    simp

/-- The executions built in Lemmas 1 and 3 are **clean**: `p` is invoked after the prefix `pre`
(at whose end the writer is idle), and nothing afterwards invokes or involves the writer. -/
lemma clean_of_split {p : P} (hp : p ≠ w0) {pre rest : List (Label P A)} {C₀ C : Config A B P L}
    (hpre : I.run pre = some C₀) (hw : C₀.pend w0 = none)
    (hrun : I.run (pre ++ .inv p (rd p) :: rest) = some C) (hpC : C.pend p = none)
    (hrest : ∀ ℓ ∈ rest, ℓ.proc ≠ w0) (hinv : opsOf rest p = []) :
    Clean w0 rd p (pre ++ .inv p (rd p) :: rest) := by
  refine ⟨(opsOf pre p).length, ?_, ?_, ?_⟩
  · simp [opOf, hinv]
  · have := I.run_idle_counts hrun hpC
    simp only [Completed, ← this]
    simp [hinv]
  · intro k' hk'
    have hw' : opsOf (.inv p (rd p) :: rest) w0 = [] :=
      opsOf_eq_nil_of_proc_ne fun ℓ hℓ => by
        rcases List.mem_cons.1 hℓ with rfl | h
        · exact hp
        · exact hrest ℓ h
    have hinvpre : Invoked pre (w0, k') := by
      simpa [Invoked, hw'] using hk'
    refine ⟨pre, _, rfl, ?_, by simp [Invoked]⟩
    have := I.run_idle_counts hpre hw
    simp only [Completed, Invoked] at hinvpre ⊢
    omega

/-- The executions built in Lemmas 1 and 3 are **dirty**: after `E₁` (at whose end `p` and the
writer are idle) the writer runs a complete round `ws` in `γ`, and `p` does not take steps. -/
lemma dirty_of_split {p : P} {E₁ γ τ : List (Label P A)} {D : Config A B P L}
    (hE₁ : I.run E₁ = some D) (hpD : D.pend p = none) (hwD : D.pend w0 = none)
    (hγ : opsOf γ w0 = ws) (hγr : (respsOf γ w0).length = ws.length)
    (hnp : ∀ ℓ ∈ γ ++ τ, ℓ.proc ≠ p) :
    Dirty w0 ws p (E₁ ++ γ ++ τ) := by
  have hw := I.run_idle_counts hE₁ hwD
  refine ⟨(opsOf E₁ w0).length, fun m hm => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · simp only [opOf, List.append_assoc, opsOf_append, hγ]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hm, List.getElem?_eq_getElem hm]
  · simp only [Completed, List.append_assoc, respsOf_append, List.length_append]
    omega
  · have hp0 : opsOf (γ ++ τ) p = [] := opsOf_eq_nil_of_proc_ne hnp
    have hp := I.run_idle_counts hE₁ hpD
    rw [List.append_assoc] at hk ⊢
    refine ⟨E₁, γ ++ τ, rfl, ?_, by simp [Invoked]⟩
    simp only [Invoked, opsOf_append, hp0, List.append_nil] at hk
    simp only [Completed]; omega

-- CSLib candidate: SharedMemory/History.lean
omit [DecidableEq P] [DecidableEq ι] in
/-- Executions of a chain extend each other. -/
lemma chain_extends {S : Set P} (f : ℕ → List (Label P A))
    (hf : ∀ i, ∃ δ, f (i + 1) = f i ++ δ ∧ ∀ ℓ ∈ δ, ℓ.proc ∈ S) :
    ∀ i j, i ≤ j → ∃ δ, f j = f i ++ δ ∧ ∀ ℓ ∈ δ, ℓ.proc ∈ S := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ j _ ih =>
    obtain ⟨δ, h1, h2⟩ := ih
    obtain ⟨δ', h1', h2'⟩ := hf j
    refine ⟨δ ++ δ', by rw [h1', h1, List.append_assoc], fun ℓ hℓ => ?_⟩
    rcases List.mem_append.1 hℓ with h | h
    · exact h2 ℓ h
    · exact h2' ℓ h

end Cslib.SharedMemory.ABADetection
