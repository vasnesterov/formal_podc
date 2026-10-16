import Papers.PODC2019.CommComplexityBA.NoSetupModel

/-!
# The two-copy system behind the proof of Theorem 13

Node `S` runs together with two copies of all other nodes: copy 1 (tapes `τ1`, inputs `x1`) and
copy 2 (tapes `τ2`, inputs `x2`). `S` (tape `τS`, input `xS`) sends its messages to both copies and
hears both. A copy can be *truncated*: once more than `C` of its nodes (other than `S`) have spoken,
its messages are no longer delivered to `S`.

* the worlds `W_{h,b}` and `W_{c,b}` of the paper are this system with copy 1 = real execution
  (sender input `b`), copy 2 = simulated execution (sender input `1-b`), copy 2 truncated;
* `tcRun_swap`: the system is symmetric under exchanging the two copies;
* `tcRun_eq_untrunc`: as long as no truncated copy has more than `C` speakers, truncation does not
  matter.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA.NoSetup

variable {P I M T : Type*} [DecidableEq P]

/-- Parameters of the two-copy system. -/
structure TCParams (P I T : Type*) where
  τS : T
  xS : I
  τ1 : P → T
  τ2 : P → T
  x1 : P → I
  x2 : P → I
  t1 : Bool
  t2 : Bool

/-- State of the two-copy system: `S`'s history, the copies' histories (entries at `S` are
meaningless) and the sets of speakers (other than `S`) so far. -/
structure TCState (P M : Type*) where
  hS : MHistory P M
  h1 : P → MHistory P M
  h2 : P → MHistory P M
  sp1 : Finset P
  sp2 : Finset P

def TCParams.swap (c : TCParams P I T) : TCParams P I T :=
  ⟨c.τS, c.xS, c.τ2, c.τ1, c.x2, c.x1, c.t2, c.t1⟩

/-- The untruncated version of the parameters. -/
def TCParams.untrunc (c : TCParams P I T) : TCParams P I T := { c with t1 := false, t2 := false }

def TCState.swap (st : TCState P M) : TCState P M := ⟨st.hS, st.h2, st.h1, st.sp2, st.sp1⟩

variable [Fintype P]

/-- Speakers other than `S` in a traffic matrix. -/
noncomputable def speakersOf (S : P) (tr : Traffic P M) : Finset P := by
  classical exact Finset.univ.filter fun j => j ≠ S ∧ ∃ q, tr j q ≠ 0

lemma mem_speakersOf {S : P} {tr : Traffic P M} {j : P} :
    j ∈ speakersOf S tr ↔ j ≠ S ∧ ∃ q, tr j q ≠ 0 := by
  classical
  unfold speakersOf; simp

lemma speakersOf_congr {S : P} {tr tr' : Traffic P M} (h : ∀ j, j ≠ S → tr j = tr' j) :
    speakersOf S tr = speakersOf S tr' := by
  ext j; simp only [mem_speakersOf]
  constructor <;> rintro ⟨hj, q, hq⟩ <;> exact ⟨hj, q, by simpa [h j hj] using hq⟩

namespace Protocol

variable (π : Protocol P I M T) (S : P) (C : ℕ)

/-- Traffic of one copy (with `S` playing its part, using `hS`). -/
def copyTraffic (τS : T) (xS : I) (τ : P → T) (x : P → I) (hS : MHistory P M)
    (h : P → MHistory P M) : Traffic P M :=
  π.sent (Function.update x S xS) (Function.update τ S τS) (Function.update h S hS)

/-- One round of the two-copy system. -/
noncomputable def tcStep (c : TCParams P I T) (st : TCState P M) : TCState P M := by
  classical exact
  let tr1 := π.copyTraffic S c.τS c.xS c.τ1 c.x1 st.hS st.h1
  let tr2 := π.copyTraffic S c.τS c.xS c.τ2 c.x2 st.hS st.h2
  let sp1 := st.sp1 ∪ speakersOf S tr1
  let sp2 := st.sp2 ∪ speakersOf S tr2
  ⟨st.hS ++ [fun j => (if c.t1 = true → sp1.card ≤ C then tr1 j S else 0) +
      (if c.t2 = true → sp2.card ≤ C then tr2 j S else 0)],
    fun q => st.h1 q ++ [fun j => tr1 j q], fun q => st.h2 q ++ [fun j => tr2 j q], sp1, sp2⟩

/-- The two-copy system after `r` rounds. -/
noncomputable def tcRun (c : TCParams P I T) : ℕ → TCState P M
  | 0 => ⟨[], fun _ => [], fun _ => [], ∅, ∅⟩
  | r + 1 => π.tcStep S C c (tcRun c r)

lemma tcRun_succ (c : TCParams P I T) (r : ℕ) :
    π.tcRun S C c (r + 1) = π.tcStep S C c (π.tcRun S C c r) := rfl

lemma tcRun_sp1_succ (c : TCParams P I T) (r : ℕ) :
    (π.tcRun S C c (r + 1)).sp1 = (π.tcRun S C c r).sp1 ∪
      speakersOf S (π.copyTraffic S c.τS c.xS c.τ1 c.x1 (π.tcRun S C c r).hS (π.tcRun S C c r).h1) :=
  rfl

lemma tcRun_sp2_succ (c : TCParams P I T) (r : ℕ) :
    (π.tcRun S C c (r + 1)).sp2 = (π.tcRun S C c r).sp2 ∪
      speakersOf S (π.copyTraffic S c.τS c.xS c.τ2 c.x2 (π.tcRun S C c r).hS (π.tcRun S C c r).h2) :=
  rfl

/-- **Symmetry**: exchanging the two copies. -/
lemma tcRun_swap (c : TCParams P I T) (r : ℕ) :
    π.tcRun S C c.swap r = (π.tcRun S C c r).swap := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [tcRun_succ, ih, tcRun_succ]
    simp only [tcStep, TCState.swap, TCParams.swap, TCState.mk.injEq, true_and, and_true]
    congr 2; funext j; exact add_comm _ _

/-- Speaker sets only grow. -/
lemma tcRun_sp1_mono (c : TCParams P I T) {r r' : ℕ} (h : r ≤ r') :
    (π.tcRun S C c r).sp1 ⊆ (π.tcRun S C c r').sp1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [tcRun_sp1_succ]; exact Finset.subset_union_left)

lemma tcRun_sp2_mono (c : TCParams P I T) {r r' : ℕ} (h : r ≤ r') :
    (π.tcRun S C c r).sp2 ⊆ (π.tcRun S C c r').sp2 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [tcRun_sp2_succ]; exact Finset.subset_union_left)

/-- **Truncation is invisible** as long as the truncated copies have at most `C` speakers in the
untruncated system. -/
lemma tcRun_eq_untrunc (c : TCParams P I T) (R : ℕ)
    (h : ∀ r < R, (c.t1 = true → (π.tcRun S C c.untrunc (r + 1)).sp1.card ≤ C) ∧
      (c.t2 = true → (π.tcRun S C c.untrunc (r + 1)).sp2.card ≤ C)) :
    ∀ r ≤ R, π.tcRun S C c r = π.tcRun S C c.untrunc r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    have ih := ih (by omega)
    obtain ⟨h1, h2⟩ := h r (by omega)
    rw [tcRun_succ, tcRun_succ, ← ih]
    rw [tcRun_succ, ← ih] at h1 h2
    simp only [tcStep, TCParams.untrunc] at h1 h2 ⊢
    congr 3
    funext j
    congr 1
    · by_cases ht : c.t1 = true
      · rw [if_pos (fun _ => h1 ht)]; simp
      · simp [ht]
    · by_cases ht : c.t2 = true
      · rw [if_pos (fun _ => h2 ht)]; simp
      · simp [ht]

/-- Changing a copy's tape at `S` does not matter. -/
lemma tcRun_update_τ1 (c : TCParams P I T) (a : T) :
    π.tcRun S C { c with τ1 := Function.update c.τ1 S a } = π.tcRun S C c := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [tcRun_succ, ih, tcRun_succ]
    simp only [tcStep, copyTraffic, Function.update_idem]
    congr

lemma tcRun_update_τ2 (c : TCParams P I T) (a : T) :
    π.tcRun S C { c with τ2 := Function.update c.τ2 S a } = π.tcRun S C c := by
  funext r
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [tcRun_succ, ih, tcRun_succ]
    simp only [tcStep, copyTraffic, Function.update_idem]
    congr

end Protocol

end CommComplexityBA.NoSetup
