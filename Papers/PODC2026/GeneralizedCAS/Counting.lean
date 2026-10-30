import Papers.PODC2026.GeneralizedCAS.Periods

/-!
# Algorithm 1: counting rises (Proposition B.2.13, Lemma B.2.14)

* `Trace.card_RE_le`: every operation rises at most 3 times in an execution. Between two rises it
  must re-enter `A` while done, and its owner writes it into `A` at most twice while it is done
  (`Inv2.wd_le`). This is the content of Proposition B.2.13.
* `OpStart.it_le`: an operation completes at most `15 |S(o)| + 5` iterations of its loop
  (Lemma B.2.14): its non-initial periods have pairwise disjoint time windows, each containing a
  rise of an operation of `S(o)` (Lemma B.2.12).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

/-- Rises minus falls of a sequence of propositions telescope. -/
theorem card_rise_le (f : ℕ → Prop) [DecidablePred f] (N : ℕ) :
    ((Finset.range N).filter (fun m => ¬ f m ∧ f (m + 1))).card ≤
      ((Finset.range N).filter (fun m => f m ∧ ¬ f (m + 1))).card + 1 := by
  suffices ((Finset.range N).filter (fun m => ¬ f m ∧ f (m + 1))).card + (if f 0 then 1 else 0) =
      ((Finset.range N).filter (fun m => f m ∧ ¬ f (m + 1))).card + (if f N then 1 else 0) by
    split_ifs at this <;> omega
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases h1 : f N <;> by_cases h2 : f (N + 1) <;> simp [h1, h2] at ih ⊢ <;> omega

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable {cellInit : ℕ → CellVal T.Resp}

namespace Trace

variable (tr : Trace T P cellInit)

/-- A *fall* of `Q τ` at time `m`. -/
def FE (τ m : ℕ) : Prop := m < tr.N ∧ tr.Q τ m ∧ ¬ tr.Q τ (m + 1)

/-- At a fall, the owner of `τ` writes `τ` into `A` while `τ` is done, which increments `wd τ`. -/
theorem wd_of_FE {τ m : ℕ} (h : tr.FE τ m) : (tr.G (m + 1)).wd τ = (tr.G m).wd τ + 1 := by
  obtain ⟨hm, ⟨hd, hA⟩, hQ⟩ := h
  have hd' := tr.done_mono (Nat.le_succ m) hm hd
  have hA' : (tr.C (m + 1)).M.A.time = τ := by
    by_contra hc; exact hQ ⟨hd', hc⟩
  have hch : (tr.C (m + 1)).M.A ≠ (tr.C m).M.A := fun e => hA (by rw [← e]; exact hA')
  obtain ⟨q, hl, hAq, hcase⟩ := tr.A_change hm hch
  have ht : ((tr.C m).loc q).t = τ := by rw [← hA', hAq]; rfl
  rw [tr.stepG m hm, hl]
  rcases hcase with ⟨hpc, -⟩ | ⟨hpc, -⟩ <;> simp [augStep, hpc, ht, hd]

theorem wd_mono {τ n m : ℕ} (hnm : n ≤ m) (hm : m ≤ tr.N) : (tr.G n).wd τ ≤ (tr.G m).wd τ := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    rw [tr.stepG m (by omega)]
    rcases wd_step (C := tr.C m) (G := tr.G m) (ℓ := tr.lbl m) τ with h | ⟨-, -, -, -, -, h⟩ <;>
      rw [h] <;> have := ih (by omega) <;> omega

open Classical in
theorem card_FE_le (τ : ℕ) {n : ℕ} (hn : n ≤ tr.N) :
    ((Finset.range n).filter (fun m => tr.FE τ m)).card ≤ (tr.G n).wd τ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hf
    · rw [Finset.card_insert_of_notMem (by simp)]
      rw [tr.wd_of_FE hf]; have := ih (by omega); omega
    · exact (ih (by omega)).trans (tr.wd_mono (Nat.le_succ n) hn)

open Classical in
/-- **Proposition B.2.13** (in the form used for counting): an operation rises at most three
times. -/
theorem card_RE_le (τ : ℕ) : ((Finset.range tr.N).filter (fun m => tr.RE τ m)).card ≤ 3 := by
  have h1 := card_rise_le (tr.Q τ) tr.N
  have h2 := tr.card_FE_le τ (le_refl tr.N)
  have h3 := (tr.inv2 (le_refl tr.N)).wd_le τ
  have e1 : (Finset.range tr.N).filter (fun m => tr.RE τ m) =
      (Finset.range tr.N).filter (fun m => ¬ tr.Q τ m ∧ tr.Q τ (m + 1)) :=
    Finset.filter_congr (fun m hm => by
      simp only [Finset.mem_range] at hm; simp only [Trace.RE, hm, true_and])
  have e2 : (Finset.range tr.N).filter (fun m => tr.FE τ m) =
      (Finset.range tr.N).filter (fun m => tr.Q τ m ∧ ¬ tr.Q τ (m + 1)) :=
    Finset.filter_congr (fun m hm => by
      simp only [Finset.mem_range] at hm; simp only [Trace.FE, hm, true_and])
  rw [e1]; rw [e2] at h2; omega

end Trace


namespace OpStart

variable {tr : Trace T P cellInit} {p : P} {n3 : ℕ} (h : OpStart tr p n3)

open Classical in
/-- The rises of operations of `S(o)`. -/
noncomputable def rises : Finset (ℕ × ℕ) :=
  h.SO.biUnion fun τ => ((Finset.range tr.N).filter (fun m => tr.RE τ m)).image fun m => (τ, m)

include h

theorem card_rises : h.rises.card ≤ 3 * h.SO.card := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ τ ∈ h.SO, (((Finset.range tr.N).filter (fun m => tr.RE τ m)).image fun m => (τ, m)).card
      ≤ ∑ τ ∈ h.SO, 3 := Finset.sum_le_sum fun τ _ => Finset.card_image_le.trans (tr.card_RE_le τ)
    _ = 3 * h.SO.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem mem_rises {τ m : ℕ} (hτ : τ ∈ h.SO) (hre : tr.RE τ m) : (τ, m) ∈ h.rises := by
  classical
  simp only [OpStart.rises, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, Prod.mk.injEq]
  exact ⟨τ, hτ, m, ⟨hre.1, hre⟩, rfl, rfl⟩

theorem periods {m : ℕ} (hm : h.InOp m) (R : ℕ) (hR : 5 * R + 1 ≤ (tr.G m).it p) :
    ∃ E, h.IsEnd (5 * R) E ∧ R ≤ (h.rises.filter (fun x => x.2 ≤ E)).card := by
  classical
  induction R with
  | zero =>
    obtain ⟨E, -, hE⟩ := h.end_exists hm (i := 0) (by omega)
    exact ⟨E, hE, Nat.zero_le _⟩
  | succ R ih =>
    obtain ⟨E₀, hE₀, hc⟩ := ih (by omega)
    have ex : ∀ j, j ≤ 5 → ∃ E, h.IsEnd (5 * R + j) E := fun j hj => by
      obtain ⟨E, -, hE⟩ := h.end_exists hm (i := 5 * R + j) (by omega); exact ⟨E, hE⟩
    obtain ⟨E₁, h1⟩ := ex 1 (by omega)
    obtain ⟨E₂, h2⟩ := ex 2 (by omega)
    obtain ⟨E₃, h3⟩ := ex 3 (by omega)
    obtain ⟨E₄, h4⟩ := ex 4 (by omega)
    obtain ⟨E₅, h5⟩ := ex 5 (by omega)
    obtain ⟨τ, hτ, m', hm1, hm2, hre⟩ := h.useful hE₀ h1 h2 h3 h4 h5
    refine ⟨E₅, by rw [show 5 * (R + 1) = 5 * R + 5 by ring]; exact h5, ?_⟩
    have hlt := h.start_gt hE₀ h1
    have hsub : insert (τ, m') (h.rises.filter (fun x => x.2 ≤ E₀)) ⊆
        h.rises.filter (fun x => x.2 ≤ E₅) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter] at hx ⊢
      rcases hx with rfl | ⟨hx1, hx2⟩
      · exact ⟨h.mem_rises hτ hre, hm2⟩
      · exact ⟨hx1, by have := h.end_lt hE₀ h5 (by omega); omega⟩
    have hnot : (τ, m') ∉ h.rises.filter (fun x => x.2 ≤ E₀) := by
      simp only [Finset.mem_filter, not_and, not_le]; intro _; omega
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at this
    omega

/-- **Lemma B.2.14**: an operation completes at most `15 |S(o)| + 5` iterations of its loop. -/
theorem it_le {m : ℕ} (hm : h.InOp m) : (tr.G m).it p ≤ 15 * h.SO.card + 5 := by
  classical
  by_contra hc
  obtain ⟨E, -, hcard⟩ := h.periods hm (3 * h.SO.card + 1) (by omega)
  have := (Finset.card_filter_le h.rises (fun x => x.2 ≤ E)).trans h.card_rises
  omega

end OpStart

end Podc.GeneralizedCAS
