import Papers.PODC2011.RulesOfThumb.Bivalence

/-!
# Concatenating schedule segments into a fair schedule

`exists_fair_of_segments`: if from every history in a set `S`, for every node `i`, some finite
schedule segment activating `i` leads back into `S` (and has an extra property `X`), then some fair
schedule visits `S` infinitely often, each visit followed by such a segment. This is the
iteration step of Theorem F.9 ("iteratively apply the fair-extension lemma").
-/

-- CSLib candidate (with the rest of the adaptive-heuristics model of this folder).
namespace Podc.RulesOfThumb

open Filter

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι] [Fintype ι] [Nonempty ι]

/-- An enumeration of the nodes that visits every node infinitely often. -/
noncomputable def cyc (ι : Type u) [Fintype ι] [Nonempty ι] (n : ℕ) : ι :=
  (Fintype.equivFin ι).symm ⟨n % Fintype.card ι, Nat.mod_lt _ Fintype.card_pos⟩

omit [DecidableEq ι] in
lemma exists_cyc_eq (i : ι) (N : ℕ) : ∃ n, N ≤ n ∧ cyc ι n = i := by
  have hc := Fintype.card_pos (α := ι)
  refine ⟨(Fintype.equivFin ι i).1 + Fintype.card ι * N, by nlinarith, ?_⟩
  have : ((Fintype.equivFin ι i).1 + Fintype.card ι * N) % Fintype.card ι =
      (Fintype.equivFin ι i).1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Fintype.equivFin ι i).2]
  simp only [cyc, this]
  simp

namespace System

variable {F : System A}

theorem exists_fair_of_segments (S : Hist A → Prop) (X : Hist A → (ℕ → Finset ι) → ℕ → Prop)
    {h₀ : Hist A} (h₀S : S h₀)
    (seg : ∀ h, S h → ∀ i, ∃ τ m, IsSegment h τ m ∧ (∃ t, h.time < t ∧ t ≤ h.time + m ∧ i ∈ τ t) ∧
      S (F.run h τ m) ∧ X h τ m) :
    ∃ σ, IsSchedule σ ∧ Fair σ ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ τ m, S (F.run h₀ σ n) ∧
      X (F.run h₀ σ n) τ m ∧ ∀ j ≤ m, F.run h₀ σ (n + j) = F.run (F.run h₀ σ n) τ j := by
  choose τf mf hseg hin hS hX using seg
  let H : ℕ → {h // S h} := fun n => Nat.rec ⟨h₀, h₀S⟩
    (fun n x => ⟨F.run x.1 (τf x.1 x.2 (cyc ι n)) (mf x.1 x.2 (cyc ι n)), hS _ _ _⟩) n
  set τn : ℕ → ℕ → Finset ι := fun n => τf (H n).1 (H n).2 (cyc ι n)
  set mn : ℕ → ℕ := fun n => mf (H n).1 (H n).2 (cyc ι n)
  have H_succ : ∀ n, (H (n + 1)).1 = F.run (H n).1 (τn n) (mn n) := fun n => rfl
  set T : ℕ → ℕ := fun n => (H n).1.time
  have T_succ : ∀ n, T (n + 1) = T n + mn n := fun n => by simp only [T, H_succ, run_time]
  have mn_pos : ∀ n, 1 ≤ mn n := fun n => by
    obtain ⟨t, h1, h2, -⟩ := hin (H n).1 (H n).2 (cyc ι n)
    simp only [mn]; omega
  have T_mono : StrictMono T := strictMono_nat_of_lt_succ fun n => by
    rw [T_succ]; linarith [mn_pos n]
  have T_ge : ∀ n, T 0 + n ≤ T n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [T_succ]; linarith [mn_pos n]
  have uniq : ∀ n n' t, T n < t → t ≤ T (n + 1) → T n' < t → t ≤ T (n' + 1) → n = n' := by
    intro n n' t h1 h2 h3 h4
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := T_mono.monotone (show n + 1 ≤ n' by omega); omega
    · have := T_mono.monotone (show n' + 1 ≤ n by omega); omega
  classical
  let σ : ℕ → Finset ι := fun t =>
    if h : ∃ n, T n < t ∧ t ≤ T (n + 1) then τn (Nat.find h) t else Finset.univ
  have hσ : ∀ n t, T n < t → t ≤ T (n + 1) → σ t = τn n t := by
    intro n t h1 h2
    have hex : ∃ n, T n < t ∧ t ≤ T (n + 1) := ⟨n, h1, h2⟩
    have := Nat.find_spec hex
    simp only [σ, hex, dif_pos]
    rw [uniq _ _ t this.1 this.2 h1 h2]
  have hrun : ∀ n, F.run h₀ σ (T n - T 0) = (H n).1 := by
    intro n
    induction n with
    | zero => simp; rfl
    | succ n ih =>
      rw [show T (n + 1) - T 0 = (T n - T 0) + mn n by rw [T_succ]; have := T_ge n; omega,
        F.run_add, ih, H_succ]
      refine F.run_congr fun t h1 h2 => hσ n t h1 ?_
      rw [T_succ]; exact h2
  have hseg' : ∀ n, ∀ j ≤ mn n, F.run h₀ σ ((T n - T 0) + j) = F.run (H n).1 (τn n) j := by
    intro n j hj
    rw [F.run_add, hrun]
    refine F.run_congr fun t h1 h2 => hσ n t h1 ?_
    rw [T_succ]; exact h2.trans (by simp only [T]; omega)
  refine ⟨σ, fun t => ?_, fun i => ?_, fun N => ?_⟩
  · by_cases hex : ∃ n, T n < t ∧ t ≤ T (n + 1)
    · obtain ⟨n, h1, h2⟩ := hex
      rw [hσ n t h1 h2]
      exact hseg (H n).1 (H n).2 (cyc ι n) t h1 (by rw [← T_succ]; exact h2)
    · simp only [σ, hex, dif_neg, not_false_eq_true, Finset.univ_nonempty]
  · rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hni⟩ := exists_cyc_eq i N
    obtain ⟨t, h1, h2, hit⟩ := hin (H n).1 (H n).2 (cyc ι n)
    refine ⟨t, ?_, ?_⟩
    · have := T_ge n; simp only [T] at this; omega
    · rw [hσ n t h1 (by rw [T_succ]; exact h2)]
      simpa [τn, hni] using hit
  · refine ⟨T N - T 0, by have := T_ge N; omega, τn N, mn N, ?_, ?_, fun j hj => ?_⟩
    · rw [hrun]; exact (H N).2
    · rw [hrun]; exact hX _ _ _
    · rw [hseg' N j hj, hrun]

end System

end Podc.RulesOfThumb
