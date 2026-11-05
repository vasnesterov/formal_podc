import Papers.PODC2012.LeaderElectionSpaceLB.Erasure

-- CSLib candidate: nondeterministic read/write shared memory + covering toolkit

/-!
# Covering tools and Claim 5.3

* `blockWrite`: processes covering distinct registers each take their (write) step;
* `runAll`: a finite set of processes runs to completion, one after the other (from
  nondeterministic solo-termination);
* `seesIn_of_visible`: in an `S`-only execution starting where only processes of `S` are visible,
  processes see only processes of `S`;
* `exists_prefix_cover`: the longest prefix without a write to `S` ends with a process covering
  a register of `S`;
* `claim_5_3`: Claim 5.3 of the paper.
-/

namespace Podc.LeaderElectionSpaceLB

set_option linter.unusedSectionVars false

open Classical

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg]

namespace Alg

variable (A : Alg P Reg V L)

lemma covers_unique {C : Config P Reg V L} {p : P} {r r' : Reg} (h : A.Covers C p r)
    (h' : A.Covers C p r') : r = r' := by
  obtain ⟨v, hv⟩ := h; obtain ⟨v', hv'⟩ := h'
  rw [hv] at hv'; cases hv'; rfl

lemma not_finished_of_covers {C : Config P Reg V L} {p : P} {r : Reg} (h : A.Covers C p r) :
    ¬ A.Finished C p := by
  rintro ⟨b, hb⟩; obtain ⟨v, hv⟩ := h; rw [hv] at hb; cases hb

lemma covers_run_of_not_mem {C : Config P Reg V L} {es : List (P × L)} {p : P} {r : Reg}
    (h : A.Covers C p r) (hp : ∀ e ∈ es, e.1 ≠ p) : A.Covers (A.run C es) p r := by
  unfold Covers; rw [A.run_loc_of_not_mem C es p hp]; exact h

lemma writesIn_mono {C : Config P Reg V L} {es : List (P × L)} {S T : Set Reg} (hST : S ⊆ T)
    (h : A.WritesIn C es S) : A.WritesIn C es T := by
  induction es generalizing C with
  | nil => exact h
  | cons e es ih =>
    rcases h with ⟨r, v, h1, h2⟩ | h
    · exact Or.inl ⟨r, v, h1, hST h2⟩
    · exact Or.inr (ih h)

lemma seesIn_mem {C : Config P Reg V L} {es : List (P × L)} {p q : P} (h : A.SeesIn C es p q) :
    ∃ e ∈ es, e.1 = p := by
  induction es generalizing C with
  | nil => exact absurd h id
  | cons e es ih =>
    rcases h with ⟨h, -⟩ | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', h'⟩ := ih h; exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-- **Block write**: if, in a reachable configuration, process `W r` covers `r` for each `r` of
a duplicate-free list `Rs`, then these processes can each take one step (writing `r`). Afterwards
`W r` is the last writer of every `r ∈ Rs`, and the other registers are unchanged; nobody sees
anybody during these steps. -/
theorem blockWrite (hST : A.SoloTerminating) :
    ∀ (Rs : List Reg) (C : Config P Reg V L) (W : Reg → P), A.Reachable C → Rs.Nodup →
      (∀ r ∈ Rs, A.Covers C (W r) r) →
      ∃ σ, A.Valid C σ ∧ (∀ e ∈ σ, ∃ r ∈ Rs, e.1 = W r) ∧
        (∀ r ∈ Rs, (A.run C σ).wr r = some (W r)) ∧
        (∀ r ∉ Rs, (A.run C σ).val r = C.val r ∧ (A.run C σ).wr r = C.wr r) ∧
        ∀ p q, ¬ A.SeesIn C σ p q := by
  intro Rs
  induction Rs with
  | nil =>
    intro C W _ _ _
    exact ⟨[], trivial, by simp, by simp, fun _ _ => ⟨rfl, rfl⟩, fun _ _ h => h⟩
  | cons r Rs ih =>
    intro C W hC hnd hcov
    rw [List.nodup_cons] at hnd
    have hcr := hcov r List.mem_cons_self
    obtain ⟨l, hl⟩ := A.exists_enabled hST hC (A.not_finished_of_covers hcr)
    set e : P × L := (W r, l)
    obtain ⟨v, hv⟩ := hcr
    have hwr := A.apply_mem_of_write C e hv
    have hC1 : A.Reachable (A.apply C e) := A.reachable_apply hC hl
    have hcov1 : ∀ r' ∈ Rs, A.Covers (A.apply C e) (W r') r' := by
      intro r' hr'
      have hne : W r' ≠ e.1 := by
        intro h
        have h1 := hcov r' (List.mem_cons_of_mem _ hr')
        rw [h] at h1
        have := A.covers_unique ⟨v, hv⟩ h1
        exact hnd.1 (this ▸ hr')
      unfold Covers; rw [A.apply_loc_of_ne C e hne]
      exact hcov r' (List.mem_cons_of_mem _ hr')
    obtain ⟨σ, hvσ, hmem, hin, hout, hsees⟩ := ih (A.apply C e) W hC1 hnd.2 hcov1
    refine ⟨e :: σ, ⟨hl, hvσ⟩, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact ⟨r, List.mem_cons_self, rfl⟩
      · obtain ⟨r', hr', h⟩ := hmem e' he'
        exact ⟨r', List.mem_cons_of_mem _ hr', h⟩
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · simp only [run_cons]
        rw [(hout r' hnd.1).2, hwr.2]; simp [e]
      · simp only [run_cons]; exact hin r' hr'
    · intro r' hr'
      rw [List.mem_cons, not_or] at hr'
      simp only [run_cons]
      rw [(hout r' hr'.2).1, (hout r' hr'.2).2, hwr.1, hwr.2,
        Function.update_of_ne hr'.1, Function.update_of_ne hr'.1]
      exact ⟨rfl, rfl⟩
    · intro p q h
      rcases h with ⟨-, r', hr', -⟩ | h
      · rw [hv] at hr'; cases hr'
      · exact hsees p q h

/-- **Run to completion**: in a reachable configuration, the processes of a list can run to
completion one after the other (solo runs, from nondeterministic solo-termination). -/
theorem runAll (hST : A.SoloTerminating) :
    ∀ (ps : List P) (C : Config P Reg V L), A.Reachable C →
      ∃ τ, A.Valid C τ ∧ (∀ e ∈ τ, e.1 ∈ ps) ∧ ∀ p ∈ ps, A.Finished (A.run C τ) p := by
  intro ps
  induction ps with
  | nil => intro C _; exact ⟨[], trivial, by simp, by simp⟩
  | cons p ps ih =>
    intro C hC
    obtain ⟨ρ, hρp, hvρ, hfin⟩ := hST C hC p
    obtain ⟨τ, hvτ, hmem, hfin'⟩ := ih _ (A.reachable_run hC hvρ)
    refine ⟨ρ ++ τ, (A.valid_append _ _ _).2 ⟨hvρ, hvτ⟩, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · rw [hρp e he]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem e he)
    · intro q hq
      rw [A.run_append]
      rcases List.mem_cons.1 hq with rfl | hq
      · exact (A.finished_run hvτ hfin).1
      · exact hfin' q hq

/-- In an `S`-only execution that starts in a configuration where only processes of `S` are
visible, every process that sees somebody is in `S` and sees only processes of `S`. -/
theorem seesIn_of_visible (S : Set P) :
    ∀ (es : List (P × L)) (C : Config P Reg V L), (∀ r p, C.wr r = some p → p ∈ S) →
      (∀ e ∈ es, e.1 ∈ S) → ∀ p q, A.SeesIn C es p q → p ∈ S ∧ q ∈ S := by
  intro es
  induction es with
  | nil => intro C _ _ p q h; exact absurd h id
  | cons e es ih =>
    intro C hvis honly p q h
    have he : e.1 ∈ S := honly e List.mem_cons_self
    rcases h with ⟨rfl, r, -, hr⟩ | h
    · exact ⟨he, hvis r q hr⟩
    · refine ih (A.apply C e) ?_ (fun e' he' => honly e' (List.mem_cons_of_mem _ he')) p q h
      intro r p' hr
      by_cases hw : ∃ v, A.act (C.loc e.1) = .write r v
      · obtain ⟨v, hv⟩ := hw
        rw [(A.apply_mem_of_write C e hv).2] at hr
        simp at hr; rw [← hr]; exact he
      · push Not at hw
        rw [(A.apply_mem_other C e r hw).2] at hr
        exact hvis r p' hr

/-- **Longest prefix without a write to `S`**: if some step of `β` writes a register of `S`,
then `β = β₁ ++ β₂` where no step of `β₁` writes `S`, and at the end of `β₁` the next process
of `β` covers a register of `S`. -/
theorem exists_prefix_cover (S : Set Reg) :
    ∀ (β : List (P × L)) (C : Config P Reg V L), A.WritesIn C β S →
      ∃ β₁ β₂, β = β₁ ++ β₂ ∧ ¬ A.WritesIn C β₁ S ∧
        ∃ e ∈ β, ∃ r ∈ S, A.Covers (A.run C β₁) e.1 r := by
  intro β
  induction β with
  | nil => intro C h; exact absurd h id
  | cons e β ih =>
    intro C h
    rcases h with ⟨r, v, h1, h2⟩ | h
    · exact ⟨[], e :: β, rfl, id, e, List.mem_cons_self, r, h2, v, h1⟩
    · by_cases h0 : ∃ r v, A.act (C.loc e.1) = .write r v ∧ r ∈ S
      · obtain ⟨r, v, h1, h2⟩ := h0
        exact ⟨[], e :: β, rfl, id, e, List.mem_cons_self, r, h2, v, h1⟩
      · obtain ⟨β₁, β₂, rfl, hno, e', he', r, hr, hc⟩ := ih _ h
        refine ⟨e :: β₁, β₂, rfl, ?_, e', List.mem_cons_of_mem _ he', r, hr, hc⟩
        rintro (h' | h')
        · exact h0 h'
        · exact hno h'

/-- **Claim 5.3.** Let `E` be an execution from an initial configuration, `R` a nonempty finite
set of registers and `R'` a finite set of registers such that at the end `C` of `E` no process
is visible on a register outside `R`. Let `Q` be closed w.r.t. `≡_E`. Suppose that in `C` every
register of `R ∪ R'` is covered by a process outside `Q` and every register of `R` is covered by
a process of `Q`. Then there is a `Q`-only execution `β` from `C` during which some process
writes a register outside `R ∪ R'`, and no process of `Q` sees a process outside `Q`.

(The paper does not require `R ≠ ∅`; for `R = ∅` and `Q = ∅` the statement fails, but the
paper only applies it with `R ≠ ∅`. The paper's assumption `R' ∩ R = ∅` is not needed.) -/
theorem claim_5_3 [Fintype P] (hLE : A.IsLeaderElection) (hST : A.SoloTerminating)
    {C₀ : Config P Reg V L} (h0 : A.IsInit C₀) {es : List (P × L)} (hv : A.Valid C₀ es)
    (R R' : Finset Reg) (hR : R.Nonempty)
    (hvis : ∀ r ∉ R, (A.run C₀ es).wr r = none)
    (Q : Set P) (hQ : A.Closed C₀ es Q)
    (hQbar : ∀ r ∈ R ∪ R', ∃ p ∉ Q, A.Covers (A.run C₀ es) p r)
    (hQcov : ∀ r ∈ R, ∃ q ∈ Q, A.Covers (A.run C₀ es) q r) :
    ∃ β : List (P × L), (∀ e ∈ β, e.1 ∈ Q) ∧ A.Valid (A.run C₀ es) β ∧
      A.WritesIn (A.run C₀ es) β {r | r ∉ R ∪ R'} ∧
      ∀ p q, A.SeesIn (A.run C₀ es) β p q → p ∈ Q → q ∈ Q := by
  set C := A.run C₀ es with hCdef
  have hC : A.Reachable C := ⟨C₀, es, h0, hv, rfl⟩
  have hQ' := (A.closed_iff _ _ _).1 hQ
  obtain ⟨r0, hr0⟩ := hR
  obtain ⟨q0, hq0Q, -⟩ := hQcov r0 hr0
  obtain ⟨p0, hp0Q, -⟩ := hQbar r0 (Finset.mem_union_left _ hr0)
  -- the writers `q_i ∈ Q`
  have hW : ∀ r, ∃ q, r ∈ R → q ∈ Q ∧ A.Covers C q r := fun r =>
    if h : r ∈ R then (let ⟨q, hq, hc⟩ := hQcov r h; ⟨q, fun _ => ⟨hq, hc⟩⟩)
    else ⟨q0, fun h' => absurd h' h⟩
  choose W hW using hW
  obtain ⟨σ, hvσ, hmemσ, hinσ, houtσ, hseesσ⟩ :=
    A.blockWrite hST R.toList C W hC (Finset.nodup_toList R)
      (fun r hr => (hW r (Finset.mem_toList.1 hr)).2)
  set C1 := A.run C σ
  have hC1 : A.Reachable C1 := A.reachable_run hC hvσ
  have hvis1 : ∀ r p, C1.wr r = some p → p ∈ Q := by
    intro r p hp
    by_cases hr : r ∈ R
    · rw [hinσ r (Finset.mem_toList.2 hr)] at hp; cases hp; exact (hW r hr).1
    · rw [(houtσ r (by simpa using hr)).2, hvis r hr] at hp; cases hp
  -- run all of `Q` to completion
  obtain ⟨τ, hvτ, hmemτ, hfinτ⟩ :=
    A.runAll hST (Finset.univ.filter (· ∈ Q)).toList C1 hC1
  have hτQ : ∀ e ∈ τ, e.1 ∈ Q := fun e he => by simpa using hmemτ e he
  have hσQ : ∀ e ∈ σ, e.1 ∈ Q := fun e he => by
    obtain ⟨r, hr, h⟩ := hmemσ e he
    rw [h]; exact (hW r (Finset.mem_toList.1 hr)).1
  set β := σ ++ τ
  have hβQ : ∀ e ∈ β, e.1 ∈ Q := fun e he => by
    rcases List.mem_append.1 he with he | he
    · exact hσQ e he
    · exact hτQ e he
  have hvβ : A.Valid C β := (A.valid_append _ _ _).2 ⟨hvσ, hvτ⟩
  have hseesβ : ∀ p q, A.SeesIn C β p q → p ∈ Q → q ∈ Q := by
    intro p q h _
    rcases (A.seesIn_append _ _ _ p q).1 h with h | h
    · exact absurd h (hseesσ p q)
    · exact (A.seesIn_of_visible Q τ C1 hvis1 hτQ p q h).2
  refine ⟨β, hβQ, hvβ, ?_, hseesβ⟩
  -- suppose, for a contradiction, that `Q` writes only to `R ∪ R'`
  by_contra hno
  set C' := A.run C β
  have hC' : A.Reachable C' := A.reachable_run hC hvβ
  have hCC' : C' = A.run C1 τ := A.run_append _ _ _
  have hfinQ : ∀ p ∈ Q, A.Finished C' p := fun p hp => by
    rw [hCC']; exact hfinτ p (by simpa using hp)
  have hout' : ∀ r ∉ R ∪ R', C'.wr r = none := by
    intro r hr
    have : ¬ A.WritesIn C β {r} := fun h => hno (A.writesIn_mono (by simpa using hr) h)
    rw [(A.run_mem_of_not_writesIn C β r this).2]
    exact hvis r (fun h => hr (Finset.mem_union_left _ h))
  -- the writers `p_j ∉ Q`, still covering
  have hW' : ∀ r, ∃ p, r ∈ R ∪ R' → p ∉ Q ∧ A.Covers C' p r := fun r =>
    if h : r ∈ R ∪ R' then
      (let ⟨p, hp, hc⟩ := hQbar r h
       ⟨p, fun _ => ⟨hp, A.covers_run_of_not_mem hc (fun e he h' => hp (h' ▸ hβQ e he))⟩⟩)
    else ⟨p0, fun h' => absurd h' h⟩
  choose W' hW' using hW'
  obtain ⟨σ2, hvσ2, hmemσ2, hinσ2, houtσ2, hseesσ2⟩ :=
    A.blockWrite hST (R ∪ R').toList C' W' hC' (Finset.nodup_toList _)
      (fun r hr => (hW' r (Finset.mem_toList.1 hr)).2)
  set C2 := A.run C' σ2
  have hC2 : A.Reachable C2 := A.reachable_run hC' hvσ2
  have hvis2 : ∀ r p, C2.wr r = some p → p ∈ (Qᶜ : Set P) := by
    intro r p hp
    by_cases hr : r ∈ R ∪ R'
    · rw [hinσ2 r (Finset.mem_toList.2 hr)] at hp; cases hp; exact (hW' r hr).1
    · rw [(houtσ2 r (by simpa using hr)).2, hout' r hr] at hp; cases hp
  obtain ⟨τ2, hvτ2, hmemτ2, hfinτ2⟩ :=
    A.runAll hST (Finset.univ.filter (· ∉ Q)).toList C2 hC2
  have hτ2Q : ∀ e ∈ τ2, e.1 ∈ (Qᶜ : Set P) := fun e he => by simpa using hmemτ2 e he
  have hσ2Q : ∀ e ∈ σ2, e.1 ∉ Q := fun e he => by
    obtain ⟨r, hr, h⟩ := hmemσ2 e he
    rw [h]; exact (hW' r (Finset.mem_toList.1 hr)).1
  -- the whole execution
  set all := es ++ β ++ σ2 ++ τ2
  have hvall : A.Valid C₀ all := by
    simp only [all, A.valid_append]
    refine ⟨⟨⟨hv, hvβ⟩, by simpa [A.run_append] using hvσ2⟩, ?_⟩
    simpa [A.run_append] using hvτ2
  have hrunall : A.run C₀ all = A.run C2 τ2 := by simp [all, A.run_append, C2, C', C]
  have hsees_all : ∀ p q, A.SeesIn C₀ all p q → (p ∈ Q ↔ q ∈ Q) := by
    intro p q h
    simp only [all, A.seesIn_append, A.run_append] at h
    rcases h with ((h | h) | h) | h
    · exact hQ' p q h
    · have hp : p ∈ Q := by
        obtain ⟨e, he, rfl⟩ := A.seesIn_mem h; exact hβQ e he
      exact ⟨fun _ => hseesβ p q h hp, fun _ => hp⟩
    · exact absurd h (hseesσ2 p q)
    · have := A.seesIn_of_visible Qᶜ τ2 C2 hvis2 hτ2Q p q (by simpa [C2, C', C] using h)
      exact ⟨fun h' => absurd h' this.1, fun h' => absurd h' this.2⟩
  have hfinall : ∀ p, A.Finished (A.run C₀ all) p := by
    intro p
    rw [hrunall]
    by_cases hp : p ∈ Q
    · have hv' : A.Valid C' (σ2 ++ τ2) := (A.valid_append _ _ _).2 ⟨hvσ2, hvτ2⟩
      have := (A.finished_run hv' (hfinQ p hp)).1
      rwa [A.run_append] at this
    · exact hfinτ2 p (by simpa using hp)
  obtain ⟨⟨w1, hw1Q, hw1⟩, -⟩ := A.claim_5_2 hLE h0 hvall Q ⟨q0, hq0Q⟩
    (fun p q h hp => (hsees_all p q h).1 hp) (fun p _ => hfinall p)
  obtain ⟨⟨w2, hw2Q, hw2⟩, -⟩ := A.claim_5_2 hLE h0 hvall (Qᶜ : Set P) ⟨p0, hp0Q⟩
    (fun p q h hp => fun hq => hp ((hsees_all p q h).2 hq)) (fun p _ => hfinall p)
  have := (hLE C₀ all h0 hvall Set.univ (fun _ _ => trivial)).1 w1 trivial w2 trivial hw1 hw2
  exact hw2Q (this ▸ hw1Q)

end Alg

end Podc.LeaderElectionSpaceLB
