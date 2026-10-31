import Papers.PODC2019.FastReadsRegisterSim.Defs
import Papers.PODC2019.FastReadsRegisterSim.Kraft

/-!
# Solo runs of one process on binary registers and the decision tree of a read

A process is given by its program `act : L → Action (register V v₀) (BinRegs ι) L`. Running it
*solo* from local state `l` on memory `M` is a deterministic sequence of pairs
`lrun act n (l, M)` (local state, memory). This file develops the combinatorics behind
Lemmas 3.3 and 3.4 of the paper, abstractly:

* `rr act s N` — the list of `(register, value)` pairs read in the first `N` steps;
* **lockstep** (`lockstep`): two solo runs from the same local state on memories `M`, `M'` stay in
  the same local state as long as their reads return the same values, and they first differ at a
  read of a register that the process has not accessed before (`diverge`);
* `SeqReads` — hypotheses describing the first read of a reader after a solo write of `v`
  (memory `M v`) for every `v`: the solo read returns, and it returns `v`. Its read-response
  strings `s v` are a prefix-free family (`prefixFree`), hence `|V| ≤ 2^(max |s v|)`
  (Theorem 3.1) and, if every read reads at most `m = log₂ |V|` registers, the strings are exactly
  all binary strings of length `m` (`complete`, Lemma 3.3) and each read accesses a register for
  the first time (`fresh`, Lemma 3.4).
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι L : Type} [DecidableEq ι]

/-- Memories of binary registers. -/
abbrev Mem (ι : Type) := (i : ι) → (BinRegs ι i).State

section Machine

variable (act : L → Action (register V v₀) (BinRegs ι) L)

/-- One solo step (identity once the process returns). -/
def lstep (s : L × Mem ι) : L × Mem ι :=
  match act s.1 with
  | .access i o k => (k ((BinRegs ι i).δ (s.2 i) o).2,
      Function.update s.2 i ((BinRegs ι i).δ (s.2 i) o).1)
  | .ret _ _ => s

/-- `n` solo steps. -/
def lrun (n : ℕ) (s : L × Mem ι) : L × Mem ι := (lstep act)^[n] s

/-- The process is about to return. -/
def IsRet (s : L × Mem ι) : Prop := ∃ u l, act s.1 = .ret u l

/-- The process is about to access register `i`. -/
def Acc (s : L × Mem ι) (i : ι) : Prop := ∃ o k, act s.1 = .access i o k

/-- The process is about to read register `i`. -/
def RdAt (s : L × Mem ι) (i : ι) : Prop := ∃ k, act s.1 = .access i .read k

/-- The read performed by the next step, with the value it returns. -/
def rd (s : L × Mem ι) : Option (ι × Bool) :=
  match act s.1 with
  | .access i .read _ => some (i, s.2 i)
  | _ => none

/-- Registers read, with the values returned, in the first `N` steps from `s`. -/
def rr (s : L × Mem ι) : ℕ → List (ι × Bool)
  | 0 => []
  | n + 1 => rr s n ++ (rd act (lrun act n s)).toList

variable {act}

@[simp] lemma lrun_zero (s : L × Mem ι) : lrun act 0 s = s := rfl

lemma lrun_succ (n : ℕ) (s : L × Mem ι) : lrun act (n + 1) s = lstep act (lrun act n s) :=
  Function.iterate_succ_apply' _ _ _

lemma lstep_of_isRet {s : L × Mem ι} (h : IsRet act s) : lstep act s = s := by
  obtain ⟨u, l, h⟩ := h
  simp [lstep, h]

lemma lrun_of_isRet {s : L × Mem ι} (h : IsRet act s) (n : ℕ) : lrun act n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lrun_succ, ih, lstep_of_isRet h]

lemma lrun_add (a b : ℕ) (s : L × Mem ι) : lrun act (a + b) s = lrun act b (lrun act a s) := by
  simp only [lrun, add_comm a b, Function.iterate_add_apply]

lemma rd_eq_some {s : L × Mem ι} {i : ι} {b : Bool} :
    rd act s = some (i, b) ↔ RdAt act s i ∧ s.2 i = b := by
  unfold rd RdAt
  split
  · rename_i j k hact
    simp only [Option.some.injEq, Prod.mk.injEq, hact]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨k, rfl⟩, rfl⟩
    · rintro ⟨⟨k', hk'⟩, rfl⟩
      simp only [Action.access.injEq] at hk'
      obtain ⟨rfl, -⟩ := hk'
      exact ⟨rfl, rfl⟩
  · rename_i hne
    simp only [reduceCtorEq, false_iff, not_and]
    rintro ⟨k, hk⟩
    exact absurd hk (hne i k)

lemma rd_isSome_iff {s : L × Mem ι} : (rd act s).isSome ↔ ∃ i, RdAt act s i := by
  constructor
  · intro h
    obtain ⟨⟨i, b⟩, hb⟩ := Option.isSome_iff_exists.1 h
    exact ⟨i, (rd_eq_some.1 hb).1⟩
  · rintro ⟨i, hi⟩
    exact Option.isSome_iff_exists.2 ⟨(i, s.2 i), rd_eq_some.2 ⟨hi, rfl⟩⟩

lemma rd_eq_none_of_isRet {s : L × Mem ι} (h : IsRet act s) : rd act s = none := by
  obtain ⟨u, l, h⟩ := h; simp [rd, h]

lemma acc_of_rdAt {s : L × Mem ι} {i : ι} (h : RdAt act s i) : Acc act s i := by
  obtain ⟨k, hk⟩ := h; exact ⟨_, k, hk⟩

lemma not_isRet_of_acc {s : L × Mem ι} {i : ι} (h : Acc act s i) : ¬ IsRet act s := by
  obtain ⟨o, k, hk⟩ := h; rintro ⟨u, l, h'⟩; rw [hk] at h'; cases h'

lemma acc_unique {s : L × Mem ι} {i j : ι} (hi : Acc act s i) (hj : Acc act s j) : i = j := by
  obtain ⟨o, k, hk⟩ := hi; obtain ⟨o', k', hk'⟩ := hj
  rw [hk] at hk'; simp only [Action.access.injEq] at hk'; exact hk'.1

lemma isRet_or_acc (s : L × Mem ι) : IsRet act s ∨ ∃ i, Acc act s i := by
  rcases h : act s.1 with ⟨i, o, k⟩ | ⟨u, l⟩
  · exact Or.inr ⟨i, o, k, h⟩
  · exact Or.inl ⟨u, l, h⟩

/-- The memory changes only at accessed registers. -/
lemma lstep_mem_of_not_acc {s : L × Mem ι} {i : ι} (h : ¬ Acc act s i) :
    (lstep act s).2 i = s.2 i := by
  unfold lstep
  split
  · rename_i j o k hact
    have hij : i ≠ j := fun hij => h ⟨o, k, hij ▸ hact⟩
    simp [Function.update_of_ne hij]
  · rfl

/-- A read does not change the memory. -/
lemma lstep_of_rdAt {s : L × Mem ι} {i : ι} {k} (h : act s.1 = .access i .read k) :
    lstep act s = (k (s.2 i), s.2) := by
  simp only [lstep, h]
  ext j
  · rfl
  · by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]

/-! ### Read lists -/

lemma rr_succ (s : L × Mem ι) (n : ℕ) :
    rr act s (n + 1) = rr act s n ++ (rd act (lrun act n s)).toList := rfl

lemma rr_mono (s : L × Mem ι) {n N : ℕ} (h : n ≤ N) : ∃ t, rr act s N = rr act s n ++ t := by
  induction N, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ N _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t ++ (rd act (lrun act N s)).toList, by rw [rr_succ, ht, List.append_assoc]⟩

lemma rr_of_rd (s : L × Mem ι) {n N : ℕ} (h : n < N) {e : ι × Bool}
    (he : rd act (lrun act n s) = some e) : ∃ t, rr act s N = rr act s n ++ e :: t := by
  obtain ⟨t, ht⟩ := rr_mono (act := act) s (show n + 1 ≤ N by omega)
  refine ⟨t, ?_⟩
  rw [ht, rr_succ, he]; simp

lemma length_rr_lt (s : L × Mem ι) {n N : ℕ} (h : n < N) (he : (rd act (lrun act n s)).isSome) :
    (rr act s n).length < (rr act s N).length := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 he
  obtain ⟨t, ht⟩ := rr_of_rd s h he
  rw [ht]; simp

lemma length_rr_le_succ (s : L × Mem ι) (n : ℕ) :
    (rr act s (n + 1)).length ≤ (rr act s n).length + 1 := by
  rw [rr_succ]; cases rd act (lrun act n s) <;> simp

/-- Each read index `< |rr N|` is attained by some step `< N`. -/
lemma exists_step_of_lt_length (s : L × Mem ι) {N j : ℕ} (h : j < (rr act s N).length) :
    ∃ n < N, (rr act s n).length = j ∧ (rd act (lrun act n s)).isSome := by
  induction N with
  | zero => simp [rr] at h
  | succ N ih =>
    by_cases hj : j < (rr act s N).length
    · obtain ⟨n, hn, h1, h2⟩ := ih hj
      exact ⟨n, by omega, h1, h2⟩
    · refine ⟨N, by omega, ?_, ?_⟩
      · have := length_rr_le_succ (act := act) s N; omega
      · rw [rr_succ] at h
        cases hrd : rd act (lrun act N s)
        · rw [hrd] at h; simp at h; omega
        · rfl

/-- Two read steps with the same read index are the same step. -/
lemma step_eq_of_length_rr_eq (s : L × Mem ι) {n n' : ℕ}
    (hn : (rd act (lrun act n s)).isSome) (hn' : (rd act (lrun act n' s)).isSome)
    (h : (rr act s n).length = (rr act s n').length) : n = n' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := length_rr_lt s hlt hn; omega
  · have := length_rr_lt s hlt hn'; omega

lemma getElem?_rr (s : L × Mem ι) {n N : ℕ} (h : n < N) {e : ι × Bool}
    (he : rd act (lrun act n s) = some e) : (rr act s N)[(rr act s n).length]? = some e := by
  obtain ⟨t, ht⟩ := rr_of_rd s h he
  rw [ht]; simp

/-- Every entry of the read list comes from a read step. -/
lemma mem_rr (s : L × Mem ι) {N : ℕ} {e : ι × Bool} (h : e ∈ rr act s N) :
    ∃ n < N, rd act (lrun act n s) = some e := by
  induction N with
  | zero => simp [rr] at h
  | succ N ih =>
    rw [rr_succ, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨n, hn, h⟩ := ih h; exact ⟨n, by omega, h⟩
    · exact ⟨N, by omega, by simpa using h⟩

/-! ### Lockstep -/

variable (act) in
/-- Lockstep invariant for the solo runs from `(l, M)` and `(l, M')` after `n` steps: same local
state; every register has the same value in both runs or still has its initial value in both
runs and has not been accessed. -/
def LS (l : L) (M M' : Mem ι) (n : ℕ) : Prop :=
  (lrun act n (l, M)).1 = (lrun act n (l, M')).1 ∧
  ∀ i, (lrun act n (l, M)).2 i = (lrun act n (l, M')).2 i ∨
    ((lrun act n (l, M)).2 i = M i ∧ (lrun act n (l, M')).2 i = M' i ∧
      ∀ n' < n, ¬ Acc act (lrun act n' (l, M)) i)

/-- **Lockstep.** If the reads of the two runs return the same values in the first `n` steps,
the lockstep invariant holds after `n` steps. -/
lemma lockstep (l : L) (M M' : Mem ι) (n : ℕ)
    (hag : ∀ n' < n, rd act (lrun act n' (l, M)) = rd act (lrun act n' (l, M'))) :
    LS act l M M' n := by
  induction n with
  | zero => exact ⟨rfl, fun i => Or.inr ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  | succ n ih =>
    obtain ⟨hst, hmem⟩ := ih (fun n' h => hag n' (by omega))
    have hrd := hag n (by omega)
    set X := lrun act n (l, M) with hX
    set Y := lrun act n (l, M') with hY
    have hX1 : lrun act (n + 1) (l, M) = lstep act X := lrun_succ _ _
    have hY1 : lrun act (n + 1) (l, M') = lstep act Y := lrun_succ _ _
    unfold LS; rw [hX1, hY1]
    -- old accesses extend by the current step
    have hacc : ∀ i, ¬ Acc act X i → (∀ n' < n, ¬ Acc act (lrun act n' (l, M)) i) →
        ∀ n' < n + 1, ¬ Acc act (lrun act n' (l, M)) i := by
      intro i h1 h2 n' hn'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn' with h | h
      · exact h2 n' h
      · subst h; exact h1
    rcases hact : act X.1 with ⟨i, o, k⟩ | ⟨u, l'⟩
    · have hactY : act Y.1 = .access i o k := by rw [← hst]; exact hact
      cases o with
      | read =>
        have hXi : X.2 i = Y.2 i := by
          have h1 : rd act X = some (i, X.2 i) := rd_eq_some.2 ⟨⟨k, hact⟩, rfl⟩
          have h2 : rd act Y = some (i, Y.2 i) := rd_eq_some.2 ⟨⟨k, hactY⟩, rfl⟩
          rw [h1, h2] at hrd; simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hrd
          exact hrd
        rw [lstep_of_rdAt hact, lstep_of_rdAt hactY]
        refine ⟨by simp only; rw [hXi], fun j => ?_⟩
        by_cases hji : j = i
        · subst hji; exact Or.inl hXi
        · rcases hmem j with h | ⟨h1, h2, h3⟩
          · exact Or.inl h
          · refine Or.inr ⟨h1, h2, hacc j (fun hA => hji (acc_unique hA ⟨_, k, hact⟩)) h3⟩
      | write b =>
        simp only [lstep, hact, hactY]
        refine ⟨trivial, fun j => ?_⟩
        by_cases hji : j = i
        · subst hji; left; simp
        · simp only [Function.update_of_ne hji]
          rcases hmem j with h | ⟨h1, h2, h3⟩
          · exact Or.inl h
          · exact Or.inr ⟨h1, h2, hacc j (fun hA => hji (acc_unique hA ⟨_, k, hact⟩)) h3⟩
    · have hactY : act Y.1 = .ret u l' := by rw [← hst]; exact hact
      rw [lstep_of_isRet ⟨u, l', hact⟩, lstep_of_isRet ⟨u, l', hactY⟩]
      refine ⟨hst, fun j => ?_⟩
      rcases hmem j with h | ⟨h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, hacc j (fun hA => not_isRet_of_acc hA ⟨u, l', hact⟩) h3⟩

/-- At the first step where the reads of two lockstep runs differ, both read a register that has
not been accessed before; the values read are the initial values. -/
lemma diverge {l : L} {M M' : Mem ι} {n : ℕ} (hls : LS act l M M' n)
    (hne : rd act (lrun act n (l, M)) ≠ rd act (lrun act n (l, M'))) :
    ∃ i, RdAt act (lrun act n (l, M)) i ∧ RdAt act (lrun act n (l, M')) i ∧
      (lrun act n (l, M)).2 i = M i ∧ (lrun act n (l, M')).2 i = M' i ∧ M i ≠ M' i ∧
      ∀ n' < n, ¬ Acc act (lrun act n' (l, M)) i := by
  obtain ⟨hst, hmem⟩ := hls
  have hiff : ∀ i, RdAt act (lrun act n (l, M)) i ↔ RdAt act (lrun act n (l, M')) i := by
    intro i; simp only [RdAt, hst]
  have hrdX : rd act (lrun act n (l, M)) ≠ none := by
    intro h
    apply hne; rw [h]; symm
    rw [← Option.not_isSome_iff_eq_none, rd_isSome_iff] at h ⊢
    rintro ⟨i, hi⟩; exact h ⟨i, (hiff i).2 hi⟩
  obtain ⟨⟨i, b⟩, hb⟩ := Option.ne_none_iff_exists'.1 hrdX
  obtain ⟨⟨k, hk⟩, hbi⟩ := rd_eq_some.1 hb
  have hkY : act (lrun act n (l, M')).1 = .access i .read k := by rw [← hst]; exact hk
  have hb' : rd act (lrun act n (l, M')) = some (i, (lrun act n (l, M')).2 i) :=
    rd_eq_some.2 ⟨⟨k, hkY⟩, rfl⟩
  rcases hmem i with h | ⟨h1, h2, h3⟩
  · exfalso; apply hne; rw [hb, hb', ← hbi, h]
  · refine ⟨i, ⟨k, hk⟩, ⟨k, hkY⟩, h1, h2, ?_, h3⟩
    intro hMM
    apply hne; rw [hb, hb', ← hbi, h1, h2, hMM]

lemma rr_congr {l : L} {M M' : Mem ι} {N : ℕ}
    (hag : ∀ n < N, rd act (lrun act n (l, M)) = rd act (lrun act n (l, M'))) :
    rr act (l, M) N = rr act (l, M') N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [rr_succ, rr_succ, ih (fun n h => hag n (by omega)), hag N (by omega)]

/-- Either the reads of two runs agree for `N` steps, or there is a first step where they
differ. -/
lemma agree_or_diverge (l : L) (M M' : Mem ι) (N : ℕ) :
    (∀ n < N, rd act (lrun act n (l, M)) = rd act (lrun act n (l, M'))) ∨
    ∃ d < N, (∀ n < d, rd act (lrun act n (l, M)) = rd act (lrun act n (l, M'))) ∧
      rd act (lrun act d (l, M)) ≠ rd act (lrun act d (l, M')) := by
  classical
  by_cases h : ∃ n, n < N ∧ rd act (lrun act n (l, M)) ≠ rd act (lrun act n (l, M'))
  · right
    refine ⟨Nat.find h, (Nat.find_spec h).1, fun n hn => ?_, (Nat.find_spec h).2⟩
    by_contra hne
    exact Nat.find_min h hn ⟨lt_trans hn (Nat.find_spec h).1, hne⟩
  · left
    intro n hn
    by_contra hne
    exact h ⟨n, hn, hne⟩

end Machine

/-! ## The first read after a solo write of each value -/

section Seq

variable {act : L → Action (register V v₀) (BinRegs ι) L} {l₀ : L} {M : V → Mem ι}

variable (act l₀ M) in
/-- Hypotheses on the solo runs of a reader from local state `l₀` on the memories `M v`
(paper: the execution `σ_v`, a write of `v` followed by a read): every run returns, and it returns
`v`. -/
structure SeqReads : Prop where
  term : ∀ v, ∃ n, IsRet act (lrun act n (l₀, M v))
  correct : ∀ v n u l, act (lrun act n (l₀, M v)).1 = .ret u l → u = v

namespace SeqReads

variable (h : SeqReads act l₀ M)

/-- The step at which the read returns. -/
noncomputable def R (v : V) : ℕ := by classical exact Nat.find (h.term v)

lemma isRet_R (v : V) : IsRet act (lrun act (h.R v) (l₀, M v)) := by
  classical
  unfold R; convert Nat.find_spec (h.term v)

lemma not_isRet_of_lt {v : V} {n : ℕ} (hn : n < h.R v) : ¬ IsRet act (lrun act n (l₀, M v)) := by
  classical
  unfold R at hn; convert Nat.find_min (h.term v) hn

lemma R_eq_of {v : V} {T : ℕ} (hT : IsRet act (lrun act T (l₀, M v)))
    (hmin : ∀ j < T, ¬ IsRet act (lrun act j (l₀, M v))) : h.R v = T := by
  classical
  unfold R
  rw [Nat.find_eq_iff]
  exact ⟨hT, hmin⟩

/-- The read-response string of the read (paper: the root-to-leaf path of `v` in the decision
tree `T_i`). -/
noncomputable def str (v : V) : List Bool := (rr act (l₀, M v) (h.R v)).map Prod.snd

/-- Runs whose reads agree up to the earlier return time return the same value. -/
lemma eq_of_agree {v v' : V}
    (hag : ∀ n < min (h.R v) (h.R v'),
      rd act (lrun act n (l₀, M v)) = rd act (lrun act n (l₀, M v'))) : v = v' := by
  obtain ⟨hst, -⟩ := lockstep l₀ (M v) (M v') _ hag
  rcases min_choice (h.R v) (h.R v') with hm | hm <;> rw [hm] at hst
  · obtain ⟨u, l, hu⟩ := h.isRet_R v
    have hu' : act (lrun act (h.R v) (l₀, M v')).1 = .ret u l := by rw [← hst]; exact hu
    exact (h.correct v _ u l hu).symm.trans (h.correct v' _ u l hu')
  · obtain ⟨u, l, hu⟩ := h.isRet_R v'
    have hu' : act (lrun act (h.R v') (l₀, M v)).1 = .ret u l := by rw [hst]; exact hu
    exact (h.correct v _ u l hu').symm.trans (h.correct v' _ u l hu)

lemma str_getElem? {v : V} {n : ℕ} (hn : n < h.R v) {e : ι × Bool}
    (he : rd act (lrun act n (l₀, M v)) = some e) :
    (h.str v)[(rr act (l₀, M v) n).length]? = some e.2 := by
  simp [str, getElem?_rr _ hn he]

lemma str_getElem?_of_lt {v : V} {n k : ℕ} (hn : n ≤ h.R v)
    (hk : k < (rr act (l₀, M v) n).length) :
    (h.str v)[k]? = ((rr act (l₀, M v) n).map Prod.snd)[k]? := by
  obtain ⟨t, ht⟩ := rr_mono (act := act) (l₀, M v) hn
  simp only [str, ht, List.map_append]
  rw [List.getElem?_append_left (by simpa using hk)]

/-- The first difference of two runs of different values occurs before both return. -/
lemma exists_diverge {v v' : V} (hne : v ≠ v') :
    ∃ d < min (h.R v) (h.R v'),
      (∀ n < d, rd act (lrun act n (l₀, M v)) = rd act (lrun act n (l₀, M v'))) ∧
      rd act (lrun act d (l₀, M v)) ≠ rd act (lrun act d (l₀, M v')) := by
  rcases agree_or_diverge (act := act) l₀ (M v) (M v') (min (h.R v) (h.R v')) with hag | hd
  · exact absurd (h.eq_of_agree hag) hne
  · exact hd

/-- Data at the first difference of the runs of `v ≠ v'`: the read index `j` (common to both
runs), the register `i` and the two (different) values. -/
lemma diverge_data {v v' : V} (hne : v ≠ v') :
    ∃ d i, d < h.R v ∧ d < h.R v' ∧
      (∀ n < d, rd act (lrun act n (l₀, M v)) = rd act (lrun act n (l₀, M v'))) ∧
      RdAt act (lrun act d (l₀, M v')) i ∧
      (rr act (l₀, M v) d) = (rr act (l₀, M v') d) ∧
      RdAt act (lrun act d (l₀, M v)) i ∧
      (∀ n' < d, ¬ Acc act (lrun act n' (l₀, M v)) i) ∧
      (lrun act d (l₀, M v)).2 i = M v i ∧ (lrun act d (l₀, M v')).2 i = M v' i ∧
      M v i ≠ M v' i ∧
      (h.str v)[(rr act (l₀, M v) d).length]? = some (M v i) ∧
      (h.str v')[(rr act (l₀, M v) d).length]? = some (M v' i) := by
  obtain ⟨d, hd, hag, hdiff⟩ := h.exists_diverge hne
  have hls := lockstep l₀ (M v) (M v') d hag
  obtain ⟨i, hi, hi', h1, h2, h3, h4⟩ := diverge hls hdiff
  have hrr := rr_congr hag
  refine ⟨d, i, by omega, by omega, hag, hi', hrr, hi, h4, h1, h2, h3, ?_, ?_⟩
  · have := h.str_getElem? (v := v) (by omega : d < h.R v) (rd_eq_some.2 ⟨hi, h1⟩)
    simpa using this
  · have := h.str_getElem? (v := v') (by omega : d < h.R v') (rd_eq_some.2 ⟨hi', h2⟩)
    rw [hrr]; simpa using this

/-- The read-response strings form a prefix-free family. -/
lemma prefixFree (v v' : V) (hp : h.str v <+: h.str v') : v = v' := by
  by_contra hne
  obtain ⟨d, i, -, -, -, -, -, -, -, -, -, h3, h5, h6⟩ := h.diverge_data hne
  obtain ⟨t, ht⟩ := hp
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.1 h5).1, h5] at h6
  exact h3 (Option.some.inj h6)

variable [Fintype V]

/-- **Theorem 3.1 (combinatorial core).** Some read reads at least `log₂ |V|` registers. -/
lemma exists_card_le_two_pow : ∃ v, Fintype.card V ≤ 2 ^ (h.str v).length := by
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ (fun v => (h.str v).length)
    ⟨v₀, Finset.mem_univ _⟩
  exact ⟨v, card_le_two_pow_of_prefixFree h.prefixFree _ (fun v' => hv v' (Finset.mem_univ _))⟩

variable {m : ℕ} (hcard : Fintype.card V = 2 ^ m) (hlen : ∀ v, (h.str v).length ≤ m)

include hcard hlen

/-- **Lemma 3.3.** If every read reads at most `m = log₂ |V|` registers, the read-response
strings are exactly the binary strings of length `m`, each for exactly one value. -/
lemma complete : (∀ v, (h.str v).length = m) ∧ ∀ u : List Bool, u.length = m → ∃ v, h.str v = u :=
  complete_of_prefixFree h.prefixFree m hlen hcard

/-- **Flipping one read.** For a read at step `n` of the run of `v` there is a value `v'` whose
run agrees with the run of `v` before step `n` and reads the same register at step `n`, which
holds different values in `M v` and `M v'`; the register was not accessed before step `n`. -/
lemma flip {v : V} {n : ℕ} (hn : n < h.R v) {i : ι} (hi : RdAt act (lrun act n (l₀, M v)) i) :
    ∃ v', v' ≠ v ∧ n < h.R v' ∧
      (∀ n' < n, rd act (lrun act n' (l₀, M v)) = rd act (lrun act n' (l₀, M v'))) ∧
      RdAt act (lrun act n (l₀, M v')) i ∧ (∀ n' < n, ¬ Acc act (lrun act n' (l₀, M v)) i) ∧
      (lrun act n (l₀, M v)).2 i = M v i ∧ (lrun act n (l₀, M v')).2 i = M v' i ∧
      M v i ≠ M v' i := by
  obtain ⟨hl, hsurj⟩ := h.complete hcard hlen
  set b : Bool := (lrun act n (l₀, M v)).2 i with hb
  set j := (rr act (l₀, M v) n).length with hj
  have hsj : (h.str v)[j]? = some b := by
    have := h.str_getElem? hn (rd_eq_some.2 ⟨hi, rfl⟩); simpa using this
  have hjm : j < m := by
    have := (List.getElem?_eq_some_iff.1 hsj).1; rw [hl v] at this; exact this
  set u : List Bool := (h.str v).take j ++ [!b] ++ List.replicate (m - j - 1) false with hu
  have hulen : u.length = m := by
    simp only [hu, List.length_append, List.length_take, hl v, List.length_singleton,
      List.length_replicate]; omega
  obtain ⟨v', hv'⟩ := hsurj u hulen
  have huj : u[j]? = some (!b) := by
    rw [hu, List.append_assoc, List.getElem?_append_right (by simp [hl v])]
    simp [hl v, show min j m = j by omega]
  have hutake : ∀ k < j, u[k]? = (h.str v)[k]? := by
    intro k hk
    rw [hu, List.append_assoc, List.getElem?_append_left (by simp [hl v]; omega)]
    simp [hk]
  have hne : v ≠ v' := by
    rintro rfl; rw [hv', huj] at hsj; simp at hsj
  obtain ⟨d, i', hdv, hdv', hag, hi'', hrr, hi', hfr, h1, h2, h3, h5, h6⟩ := h.diverge_data hne
  set j' := (rr act (l₀, M v) d).length with hj'
  -- the divergence happens at read index `j`
  have hjj : j' = j := by
    rcases lt_trichotomy j' j with hlt | heq | hgt
    · exfalso
      have := hutake j' hlt
      rw [← hv', h6, h5] at this
      exact h3 (Option.some.inj this).symm
    · exact heq
    · exfalso
      have e1 := h.str_getElem?_of_lt (v := v) (n := d) (by omega) hgt
      have e2 := h.str_getElem?_of_lt (v := v') (n := d) (by omega) (by rw [← hrr]; exact hgt)
      rw [← hrr, ← e1, hsj, hv', huj] at e2
      simp at e2
  have hdn : d = n :=
    step_eq_of_length_rr_eq _ (rd_isSome_iff.2 ⟨i', hi'⟩) (rd_isSome_iff.2 ⟨i, hi⟩) (by omega)
  subst hdn
  have hii : i' = i := acc_unique (acc_of_rdAt hi') (acc_of_rdAt hi)
  subst hii
  exact ⟨v', hne.symm, hdv', hag, hi'', hfr, h1, h2, h3⟩

/-- **Lemma 3.4.** Every read of the first read accesses a register that the reader has not
accessed before (in particular no register is read twice), and it returns the value of that
register at the start of the read. -/
lemma fresh {v : V} {n : ℕ} (hn : n < h.R v) {i : ι} (hi : RdAt act (lrun act n (l₀, M v)) i) :
    (∀ n' < n, ¬ Acc act (lrun act n' (l₀, M v)) i) ∧ (lrun act n (l₀, M v)).2 i = M v i := by
  obtain ⟨v', -, -, -, -, h1, h2, -, -⟩ := h.flip hcard hlen hn hi
  exact ⟨h1, h2⟩

/-- The registers read by the read of `v` are pairwise distinct. -/
lemma nodup_regs (v : V) : ((rr act (l₀, M v) (h.R v)).map Prod.fst).Nodup := by
  have : ∀ N ≤ h.R v, ((rr act (l₀, M v) N).map Prod.fst).Nodup := by
    intro N hN
    induction N with
    | zero => simp [rr]
    | succ N ih =>
      rw [rr_succ, List.map_append, List.nodup_append]
      refine ⟨ih (by omega), ?_, ?_⟩
      · cases rd act (lrun act N (l₀, M v)) <;> simp
      · intro a ha b hb hab
        subst hab
        cases hrd : rd act (lrun act N (l₀, M v)) with
        | none => rw [hrd] at hb; simp at hb
        | some e =>
          rw [hrd] at hb; simp only [Option.toList_some, List.map_cons, List.map_nil,
            List.mem_singleton] at hb
          obtain ⟨⟨k, b'⟩, he, rfl⟩ := List.mem_map.1 ha
          obtain ⟨n', hn', hrd'⟩ := mem_rr _ he
          have hN' : RdAt act (lrun act N (l₀, M v)) k := by
            obtain ⟨e1, e2⟩ := e; simp only at hb; subst hb; exact (rd_eq_some.1 hrd).1
          exact (h.fresh hcard hlen (by omega) hN').1 n' hn' (acc_of_rdAt (rd_eq_some.1 hrd').1)
  exact this _ le_rfl

/-- **Theorem 3.2 (combinatorial core).** If every read reads at most `m = log₂ |V|` registers,
then for every memory `M₀` there is a value `v` such that `M v` differs from `M₀` on at least
`m` registers (paper: the rightmost root-to-leaf path, generalized to arbitrary `M₀`). -/
lemma exists_far (M₀ : Mem ι) :
    ∃ v, ∃ rs : List ι, rs.Nodup ∧ rs.length = m ∧ ∀ i ∈ rs, M v i ≠ M₀ i := by
  obtain ⟨hl, -⟩ := h.complete hcard hlen
  -- induction on the number of reads that already see a non-initial value
  have key : ∀ j ≤ m, ∃ v, ∀ n < h.R v, ∀ i, RdAt act (lrun act n (l₀, M v)) i →
      (rr act (l₀, M v) n).length < j → M v i ≠ M₀ i := by
    intro j hj
    induction j with
    | zero => exact ⟨v₀, fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ j ih =>
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨n, hn, hnj, hrdn⟩ := exists_step_of_lt_length (act := act) (l₀, M v)
        (N := h.R v) (j := j) (by have := hl v; simp only [str, List.length_map] at this; omega)
      obtain ⟨i, hi⟩ := rd_isSome_iff.1 hrdn
      by_cases hMi : M v i = M₀ i
      · obtain ⟨v', -, hnv', hag, hi', -, h1, h2, h3⟩ := h.flip hcard hlen hn hi
        refine ⟨v', fun n' hn' i' hi'' hlt => ?_⟩
        rcases lt_trichotomy n' n with hlt' | heq | hgt
        · -- before the flipped read: same read as in the run of `v`
          have hrdv : rd act (lrun act n' (l₀, M v)) = some (i', (lrun act n' (l₀, M v')).2 i') := by
            rw [hag n' hlt']; exact rd_eq_some.2 ⟨hi'', rfl⟩
          have hiv := (rd_eq_some.1 hrdv).1
          have hlen' : (rr act (l₀, M v) n').length < j := by
            have := length_rr_lt (act := act) (l₀, M v) hlt' (by rw [hrdv]; rfl); omega
          have e1 := (h.fresh hcard hlen (by omega) hiv).2
          have e2 := (h.fresh hcard hlen hn' hi'').2
          have e3 := (rd_eq_some.1 hrdv).2
          rw [← e2, ← e3, e1]
          exact hv n' (by omega) i' hiv hlen'
        · subst heq
          have : i' = i := acc_unique (acc_of_rdAt hi'') (acc_of_rdAt hi')
          subst this
          rw [← hMi]; exact fun e => h3 e.symm
        · exfalso
          have h1 := length_rr_lt (act := act) (l₀, M v') hgt (rd_isSome_iff.2 ⟨i, hi'⟩)
          have h2 : rr act (l₀, M v) n = rr act (l₀, M v') n := rr_congr hag
          have h2' := congrArg List.length h2
          omega
      · refine ⟨v, fun n' hn' i' hi' hlt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
        · exact hv n' hn' i' hi' hlt
        · have : n' = n := step_eq_of_length_rr_eq _ (rd_isSome_iff.2 ⟨i', hi'⟩) hrdn (by omega)
          subst this
          rw [acc_unique (acc_of_rdAt hi') (acc_of_rdAt hi)]; exact hMi
  obtain ⟨v, hv⟩ := key m le_rfl
  refine ⟨v, (rr act (l₀, M v) (h.R v)).map Prod.fst, h.nodup_regs hcard hlen v, ?_, ?_⟩
  · have := hl v; simpa [str] using this
  · intro i hi
    obtain ⟨⟨i', b⟩, he, rfl⟩ := List.mem_map.1 hi
    obtain ⟨n, hn, hrd⟩ := mem_rr _ he
    refine hv n hn _ (rd_eq_some.1 hrd).1 ?_
    have := length_rr_lt (act := act) (l₀, M v) hn (by rw [hrd]; rfl)
    have h2 := hl v; simp only [str, List.length_map] at h2; omega

end SeqReads

end Seq

end Podc.FastReadsRegisterSim
