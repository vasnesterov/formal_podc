import Papers.PODC2011.RulesOfThumb.Valency

/-!
# The act-and-tell model and the FLP-style extension lemma (Appendix F)

Appendix F.6 converts the simultaneous activations of Section 3 into sequential events: `e_j`
(node `j` computes its reaction, invisible to the others) and `W` (all computed reactions are
revealed: one time step). A state of this *act-and-tell* model is a history together with the set
`P` of nodes that have already reacted in the current time step. We model `e_j` by `some j` and
`W` by `none`; `W` is only enabled when `P` is nonempty, so every time step activates a nonempty
set, as Section 3 requires.

The colour of a state is `F.lims h P` (`Valency.lean`). The main result, `exists_bivalent_after`,
is the FLP-style extension lemma (the content of Lemmas F.8 and F.12): in a convergent system with
self-independent `k`-recall reaction functions, from every bivalent state and for every event `e`
some extension that avoids `e` and then performs `e` reaches a bivalent state. The proof does not
need stationarity: both paths through each "diamond" of Fig. 3 take the same number of time
steps, as Appendix F.7 observes.

`exists_segment` packages two applications into a statement about schedules: from a bivalent
history, for every node `i`, some finite schedule segment that activates `i` leads to a bivalent
history.
-/

-- CSLib candidate (with the rest of the adaptive-heuristics model of this folder).
namespace Podc.RulesOfThumb

open Filter Relation

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

namespace System

variable (F : System A)

/-- One event of the act-and-tell model: `some j` adds `j` to the pending set, `none` reveals the
pending reactions (one time step of the dynamics). -/
inductive ATStep : Option ι → Hist A × Finset ι → Hist A × Finset ι → Prop
  | add (j : ι) (h : Hist A) (P : Finset ι) : ATStep (some j) (h, P) (h, insert j P)
  | fire (h : Hist A) (P : Finset ι) (hP : P.Nonempty) : ATStep none (h, P) (F.step h P, ∅)

/-- An event different from `e`. -/
def Avoid (e : Option ι) (s s' : Hist A × Finset ι) : Prop := ∃ e', e' ≠ e ∧ F.ATStep e' s s'

/-- The colour of an act-and-tell state. -/
def col (s : Hist A × Finset ι) : Set (Profile A) := F.lims s.1 s.2

/-- A bivalent state: at least two different colours. -/
def Biv (s : Hist A × Finset ι) : Prop := ¬ (F.col s).Subsingleton

variable {F}

lemma col_anti {e : Option ι} {s s' : Hist A × Finset ι} (hs : F.ATStep e s s') :
    F.col s' ⊆ F.col s := by
  cases hs with
  | add j h P => exact lims_anti (Finset.subset_insert _ _)
  | fire h P hP => exact lims_step_subset hP

/-- Adding a set `S` of nodes, none of which is `e`, to the pending set. -/
lemma avoid_addAll {e : Option ι} (S : Finset ι) (hS : ∀ j ∈ S, some j ≠ e)
    (u : Hist A × Finset ι) : ReflTransGen (F.Avoid e) u (u.1, u.2 ∪ S) := by
  induction S using Finset.induction_on with
  | empty => simpa using ReflTransGen.refl
  | insert j S hj ih =>
    refine (ih fun l hl => hS l (Finset.mem_insert_of_mem hl)).tail ?_
    rw [Finset.union_insert]
    exact ⟨some j, hS j (Finset.mem_insert_self _ _), ATStep.add _ _ _⟩

lemma othersEq_step_insert (F : System A) (g : Hist A) (P : Finset ι) (i : ι) :
    OthersEq i (F.step g (insert i P)) (F.step g P) := by
  unfold OthersEq
  rw [step_toList, step_toList]
  refine List.Forall₂.cons (fun l hl => ?_) ?_
  · have : l ∈ insert i P ↔ l ∈ P := by simp [hl]
    simp only [step, this]
  · exact List.forall₂_same.mpr fun _ _ _ _ => rfl

variable [Fintype ι] [Nonempty ι]

/-- **The extension lemma.** In a convergent system with self-independent `k`-recall reaction
functions, from a bivalent act-and-tell state, for every event `e`, some extension avoiding `e`
followed by `e` reaches a bivalent state (Lemmas F.8 and F.12 of the paper). -/
theorem exists_bivalent_after {k : ℕ} (hk : 1 ≤ k) (hrec : ∀ i, F.HasRecall i k)
    (hsi : F.SelfIndependent) (hconv : F.Convergent) (e : Option ι)
    {s : Hist A × Finset ι} (hs : F.Biv s) :
    ∃ s₁ s₂, ReflTransGen (F.Avoid e) s s₁ ∧ F.ATStep e s₁ s₂ ∧ F.Biv s₂ := by
  by_contra H
  push Not at H
  simp only [Biv, not_not] at H
  obtain ⟨c, hc, d, hd, hcd⟩ : ∃ c ∈ F.col s, ∃ d ∈ F.col s, c ≠ d := by
    simpa [Biv, Set.Subsingleton] using hs
  obtain ⟨h, P⟩ := s
  cases e with
  | some i =>
    -- the colour of `e_i(u)` is the same for all `u` reachable while avoiding `e_i`
    let E : Hist A × Finset ι → Hist A × Finset ι := fun u => (u.1, insert i u.2)
    have hE : ∀ u, F.ATStep (some i) u (E u) := fun u => ATStep.add _ _ _
    have inv : ∀ u, ReflTransGen (F.Avoid (some i)) (h, P) u → F.col (E u) = F.col (E (h, P)) := by
      intro u hu
      induction hu with
      | refl => rfl
      | @tail u v huv hv ih =>
        rw [← ih]
        refine subsingleton_eq_of_inter (H _ _ (huv.tail hv) (hE v)) (H _ _ huv (hE u)) ?_
        obtain ⟨e', he', hstep⟩ := hv
        cases hstep with
        | add j g Q =>
          have hj : j ≠ i := fun h => he' (by rw [h])
          obtain ⟨x, hx⟩ := lims_nonempty hconv g (insert i (insert j Q))
          refine ⟨x, hx, ?_⟩
          have : F.ATStep (some j) (E (g, Q)) (g, insert i (insert j Q)) := by
            rw [Finset.insert_comm]; exact ATStep.add _ _ _
          exact col_anti this hx
        | fire g Q hQ =>
          obtain ⟨x, hx1, hx2⟩ :=
            lims_inter_nonempty' hk hrec hsi hconv (othersEq_step_insert F g Q i)
          refine ⟨x, ?_, ?_⟩
          · simpa [E, col] using hx2
          · exact lims_step_subset (Finset.insert_nonempty _ _) hx1
    -- every colour of `s` shows up as a colour of some `e_i(u)`
    have hit : ∀ a ∈ F.col (h, P), ∃ u, ReflTransGen (F.Avoid (some i)) (h, P) u ∧
        a ∈ F.col (E u) := by
      rintro a ⟨σ, hσ, hfair, hP, hconvσ⟩
      have hex : ∃ m, i ∈ σ (h.time + 1 + m) := by
        obtain ⟨t, ht, hi⟩ := ((hfair i).and_eventually (eventually_gt_atTop h.time)).exists
        exact ⟨t - (h.time + 1), by rwa [show h.time + 1 + (t - (h.time + 1)) = t by omega]⟩
      classical
      let m₀ := Nat.find hex
      have reach : ∀ m ≤ m₀, ∃ Q ⊆ σ ((F.run h σ m).time + 1),
          ReflTransGen (F.Avoid (some i)) (h, P) (F.run h σ m, Q) := by
        intro m hm
        induction m with
        | zero => exact ⟨P, hP, ReflTransGen.refl⟩
        | succ m ih =>
          obtain ⟨Q, hQ, hr⟩ := ih (by omega)
          have hi : i ∉ σ ((F.run h σ m).time + 1) := by
            have := Nat.find_min hex (show m < m₀ by omega)
            simpa [add_assoc, add_comm 1 m] using this
          refine ⟨∅, Finset.empty_subset _, ?_⟩
          have h1 := avoid_addAll (F := F) (e := some i) (σ ((F.run h σ m).time + 1))
            (fun j hj h' => hi (by simp only [Option.some.injEq] at h'; exact h' ▸ hj))
            (F.run h σ m, Q)
          simp only [Finset.union_eq_right.mpr hQ] at h1
          refine (hr.trans h1).tail ⟨none, by simp, ?_⟩
          rw [run_succ]
          exact ATStep.fire _ _ (hσ _)
      obtain ⟨Q, hQ, hr⟩ := reach m₀ le_rfl
      set g := F.run h σ m₀
      set S := σ (g.time + 1)
      have hiS : i ∈ S := by
        have := Nat.find_spec hex
        simp only [S, g, run_time]
        rwa [add_assoc, add_comm 1] at this
      refine ⟨(g, Q ∪ S.erase i), hr.trans (avoid_addAll _ (fun j hj h' => ?_) _), ?_⟩
      · simp only [Option.some.injEq] at h'
        exact (Finset.notMem_erase j S) (h' ▸ hj)
      · have : insert i (Q ∪ S.erase i) = S := by
          ext x
          by_cases hx : x = i
          · simp [hx, hiS]
          · simp only [Finset.mem_insert, hx, false_or, Finset.mem_union, Finset.mem_erase,
              ne_eq, not_false_eq_true, true_and]
            exact ⟨fun h => h.elim (fun h => hQ h) id, Or.inr⟩
        show a ∈ F.lims g (insert i (Q ∪ S.erase i))
        rw [this]
        exact mem_lims_run hσ hfair hconvσ m₀ le_rfl
    obtain ⟨u, hu, hcu⟩ := hit c hc
    obtain ⟨w, hw, hdw⟩ := hit d hd
    rw [inv u hu] at hcu
    rw [inv w hw] at hdw
    exact hcd (H _ _ ReflTransGen.refl (hE _) hcu hdw)
  | none =>
    -- states reachable without `W` only have more pending nodes
    have hreach : ∀ Q, P ⊆ Q → ReflTransGen (F.Avoid none) (h, P) (h, Q) := by
      intro Q hQ
      have := avoid_addAll (F := F) (e := none) Q (fun _ _ => by simp) (h, P)
      simpa [Finset.union_eq_right.mpr hQ] using this
    let C : Finset ι → Set (Profile A) := fun Q => F.lims (F.step h Q) ∅
    have hsub : ∀ Q, P ⊆ Q → Q.Nonempty → (C Q).Subsingleton := fun Q hPQ hQ =>
      H _ _ (hreach Q hPQ) (ATStep.fire _ _ hQ)
    have hins : ∀ Q, P ⊆ Q → Q.Nonempty → ∀ j, C (insert j Q) = C Q := by
      intro Q hPQ hQ j
      refine subsingleton_eq_of_inter (hsub _ (hPQ.trans (Finset.subset_insert _ _))
        (Finset.insert_nonempty _ _)) (hsub Q hPQ hQ) ?_
      exact lims_inter_nonempty hk hrec hsi hconv (othersEq_step_insert F h Q j)
    have hunion : ∀ Q, P ⊆ Q → Q.Nonempty → ∀ R : Finset ι, C (Q ∪ R) = C Q := by
      intro Q hPQ hQ R
      induction R using Finset.induction_on with
      | empty => simp
      | insert j R _ ih =>
        rw [Finset.union_insert, hins _ (hPQ.trans Finset.subset_union_left)
          (hQ.mono Finset.subset_union_left), ih]
    have hit : ∀ a ∈ F.col (h, P), ∃ Q, P ⊆ Q ∧ Q.Nonempty ∧ a ∈ C Q := by
      rintro a ⟨σ, hσ, hfair, hP, hconvσ⟩
      exact ⟨_, hP, hσ _, mem_lims_run hσ hfair hconvσ 1 (Finset.empty_subset _)⟩
    obtain ⟨Q₁, hP₁, hn₁, hc₁⟩ := hit c hc
    obtain ⟨Q₂, hP₂, hn₂, hd₂⟩ := hit d hd
    have e₁ := hunion Q₁ hP₁ hn₁ Q₂
    have e₂ := hunion Q₂ hP₂ hn₂ Q₁
    rw [Finset.union_comm] at e₂
    rw [← e₁, e₂] at hc₁
    exact hcd (hsub Q₂ hP₂ hn₂ hc₁ hd₂)

end System

end Podc.RulesOfThumb
