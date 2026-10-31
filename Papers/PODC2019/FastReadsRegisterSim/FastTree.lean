import Papers.PODC2019.FastReadsRegisterSim.ReadTree

/-!
# The decision tree of a read that takes exactly `log₂ k` steps

If, in addition to `SeqReads`, every first read takes at most `m = log₂ |V|` *steps*, then every
step of the first read is a read of a fresh register (the read is invisible), and the read is
described by a complete binary decision tree of depth `m` (paper: Lemmas 3.3, 3.4 and the remark
that the first read is invisible):

* `node act l₀ u` — the local state after the reads returned the bits `u`;
* for `|u| < m` the next step is a read (`node_read`); for `|u| = m` the read returns `val u`
  (`node_ret`), and `val` is a bijection from the strings of length `m` to `V`
  (`str_val`, `val_str`);
* `path act l₀ M j` — the bits read in the first `j` steps when every read sees memory `M`.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι L : Type} [DecidableEq ι]

section Defs

variable (act : L → Action (register V v₀) (BinRegs ι) L) (l₀ : L)

/-- The local state after a read returns `b` (identity at a return). -/
def tstep (l : L) (b : Bool) : L :=
  match act l with
  | .access _ _ k => k b
  | .ret _ _ => l

/-- The local state after the reads returned the bits `u`. -/
def node (u : List Bool) : L := u.foldl (tstep act) l₀

/-- The register read at a local state (if any), as a predicate. -/
def RdN (l : L) (i : ι) : Prop := ∃ k, act l = .access i .read k

/-- The value seen by the next step at memory `M` (`false` if it does not access a register). -/
def bit (M : Mem ι) (l : L) : Bool :=
  match act l with
  | .access i _ _ => M i
  | .ret _ _ => false

/-- The bits read in the first `j` steps at constant memory `M`. -/
def path (M : Mem ι) : ℕ → List Bool
  | 0 => []
  | j + 1 => path M j ++ [bit act M (node act l₀ (path M j))]

/-- The value returned at a leaf. -/
def val (u : List Bool) : V :=
  match act (node act l₀ u) with
  | .ret v _ => v
  | .access _ _ _ => v₀

variable {act l₀}

@[simp] lemma node_nil : node act l₀ [] = l₀ := rfl

lemma node_append (u : List Bool) (b : Bool) :
    node act l₀ (u ++ [b]) = tstep act (node act l₀ u) b := by
  simp [node, List.foldl_append]

@[simp] lemma length_path (M : Mem ι) (j : ℕ) : (path act l₀ M j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [path, ih]

lemma path_prefix (M : Mem ι) {j j' : ℕ} (h : j ≤ j') :
    path act l₀ M j <+: path act l₀ M j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j' _ ih => exact ih.trans (List.prefix_append _ _)

lemma path_take (M : Mem ι) {j j' : ℕ} (h : j ≤ j') :
    (path act l₀ M j').take j = path act l₀ M j := by
  obtain ⟨t, ht⟩ := path_prefix (act := act) (l₀ := l₀) M h
  rw [← ht]; simp

lemma rdN_unique {l : L} {i j : ι} (hi : RdN act l i) (hj : RdN act l j) : i = j := by
  obtain ⟨k, hk⟩ := hi; obtain ⟨k', hk'⟩ := hj
  rw [hk] at hk'; simp only [Action.access.injEq] at hk'; exact hk'.1

lemma bit_of_rdN {M : Mem ι} {l : L} {i : ι} (h : RdN act l i) : bit act M l = M i := by
  obtain ⟨k, hk⟩ := h; simp [bit, hk]

lemma tstep_of_rdN {l : L} {i : ι} {k} (h : act l = .access i .read k) (b : Bool) :
    tstep act l b = k b := by simp [tstep, h]

/-- Two memories that agree on every register read along `path M` have the same path. -/
lemma path_congr {M M' : Mem ι} (j : ℕ)
    (h : ∀ j' < j, ∀ i, RdN act (node act l₀ (path act l₀ M j')) i → M i = M' i)
    (hrd : ∀ j' < j, ∃ i, RdN act (node act l₀ (path act l₀ M j')) i) :
    path act l₀ M' j = path act l₀ M j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have ih' := ih (fun j' hj' => h j' (by omega)) (fun j' hj' => hrd j' (by omega))
    obtain ⟨i, hi⟩ := hrd j (by omega)
    simp only [path, ih', bit_of_rdN hi, h j (by omega) i hi]

/-- The bit at position `j` of a path is the value of the register read at depth `j`. -/
lemma path_getElem {m : ℕ} (M' : Mem ι) {j : ℕ} (hj : j < m) {i : ι}
    (hi : RdN act (node act l₀ (path act l₀ M' j)) i) :
    (path act l₀ M' m)[j]? = some (M' i) := by
  calc (path act l₀ M' m)[j]? = ((path act l₀ M' m).take (j + 1))[j]? := by
        rw [List.getElem?_take]; simp
    _ = (path act l₀ M' (j + 1))[j]? := by rw [path_take M' (by omega)]
    _ = some (M' i) := by simp [path, bit_of_rdN hi]

end Defs

/-! ## From `SeqReads` with a step bound to the decision tree -/

section Fast

variable {act : L → Action (register V v₀) (BinRegs ι) L} {l₀ : L} {M : V → Mem ι}

lemma length_rr_le (s : L × Mem ι) (N : ℕ) : (rr act s N).length ≤ N := by
  induction N with
  | zero => simp [rr]
  | succ N ih => have := length_rr_le_succ (act := act) s N; omega

lemma rd_isSome_of_length_rr (s : L × Mem ι) {N : ℕ} (heq : (rr act s N).length = N) :
    ∀ n < N, (rd act (lrun act n s)).isSome := by
  induction N with
  | zero => intro n hn; omega
  | succ N ih =>
    intro n hn
    have h1 := length_rr_le (act := act) s N
    rw [rr_succ, List.length_append] at heq
    cases hrd : rd act (lrun act N s) with
    | none => rw [hrd] at heq; simp at heq; omega
    | some e =>
      rw [hrd] at heq; simp at heq
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · exact ih (by omega) n hn
      · rw [hrd]; rfl

variable (h : SeqReads act l₀ M) [Fintype V] {m : ℕ} (hcard : Fintype.card V = 2 ^ m)
  (hR : ∀ v, h.R v ≤ m)

include hcard hR

lemma str_length_le (v : V) : (h.str v).length ≤ m := by
  have := length_rr_le (act := act) (l₀, M v) (h.R v)
  simp only [SeqReads.str, List.length_map]; have := hR v; omega

/-- With at most `m` steps, the first read takes exactly `m` steps. -/
lemma R_eq_m (v : V) : h.R v = m := by
  have hl := (h.complete hcard (str_length_le h hcard hR)).1 v
  have := length_rr_le (act := act) (l₀, M v) (h.R v)
  simp only [SeqReads.str, List.length_map] at hl
  have := hR v; omega

/-- Every step of the first read is a read (the first read is invisible). -/
lemma all_reads (v : V) : ∀ n < m, (rd act (lrun act n (l₀, M v))).isSome := by
  have hl := (h.complete hcard (str_length_le h hcard hR)).1 v
  simp only [SeqReads.str, List.length_map, R_eq_m h hcard hR] at hl
  exact rd_isSome_of_length_rr _ hl

lemma length_rr_eq (v : V) {n : ℕ} (hn : n ≤ m) : (rr act (l₀, M v) n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rr_succ, List.length_append, ih (by omega)]
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (all_reads h hcard hR v n (by omega))
    simp [he]

/-- During the first read the memory does not change. -/
lemma mem_const (v : V) {n : ℕ} (hn : n ≤ m) : (lrun act n (l₀, M v)).2 = M v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨i, k, hk⟩ : ∃ i k, act (lrun act n (l₀, M v)).1 = .access i .read k := by
      obtain ⟨i, ⟨k, hk⟩⟩ := rd_isSome_iff.1 (all_reads h hcard hR v n (by omega))
      exact ⟨i, k, hk⟩
    rw [lrun_succ, lstep_of_rdAt hk, ih (by omega)]

/-- The local state after `n` steps of the first read of `v` is the node of the first `n` bits
of its string. -/
lemma lrun_fst (v : V) {n : ℕ} (hn : n ≤ m) :
    (lrun act n (l₀, M v)).1 = node act l₀ ((h.str v).take n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨i, k, hk⟩ : ∃ i k, act (lrun act n (l₀, M v)).1 = .access i .read k := by
      obtain ⟨i, ⟨k, hk⟩⟩ := rd_isSome_iff.1 (all_reads h hcard hR v n (by omega))
      exact ⟨i, k, hk⟩
    have hrn : n < h.R v := by rw [R_eq_m h hcard hR]; omega
    have hs := h.str_getElem? hrn (rd_eq_some.2 ⟨⟨k, hk⟩, rfl⟩)
    rw [length_rr_eq h hcard hR v (by omega)] at hs
    rw [List.take_add_one, hs, Option.toList_some, node_append, ← ih (by omega), lrun_succ,
      lstep_of_rdAt hk, tstep_of_rdN hk]

/-- Inner nodes of the tree are reads. -/
lemma node_read {u : List Bool} (hu : u.length < m) :
    ∃ i k, act (node act l₀ u) = .access i .read k ∧ ∀ b, k b = node act l₀ (u ++ [b]) := by
  obtain ⟨-, hsurj⟩ := h.complete hcard (str_length_le h hcard hR)
  obtain ⟨v, hv⟩ := hsurj (u ++ List.replicate (m - u.length) false) (by simp; omega)
  have hst := lrun_fst h hcard hR v (n := u.length) (by omega)
  rw [hv, List.take_left' rfl] at hst
  obtain ⟨i, ⟨k, hk⟩⟩ := rd_isSome_iff.1 (all_reads h hcard hR v u.length hu)
  rw [hst] at hk
  exact ⟨i, k, hk, fun b => by rw [node_append, tstep_of_rdN hk]⟩

/-- Leaves of the tree return the value whose string they are. -/
lemma node_ret {u : List Bool} (hu : u.length = m) :
    ∃ l, act (node act l₀ u) = .ret (val act l₀ u) l ∧ h.str (val act l₀ u) = u := by
  obtain ⟨-, hsurj⟩ := h.complete hcard (str_length_le h hcard hR)
  obtain ⟨v, hv⟩ := hsurj u hu
  have hst := lrun_fst h hcard hR v (n := m) le_rfl
  have hlen := (h.complete hcard (str_length_le h hcard hR)).1 v
  rw [List.take_of_length_le (by omega), hv] at hst
  obtain ⟨u', l, hul⟩ := R_eq_m h hcard hR v ▸ h.isRet_R v
  have huv := h.correct v _ u' l hul
  rw [hst] at hul
  subst huv
  have : val act l₀ u = u' := by simp [val, hul]
  rw [this]
  exact ⟨l, hul, hv⟩

lemma val_str (v : V) : val act l₀ (h.str v) = v := by
  have hl := (h.complete hcard (str_length_le h hcard hR)).1 v
  obtain ⟨l, -, hs⟩ := node_ret h hcard hR hl
  exact h.prefixFree _ _ (by rw [hs])

lemma str_val {u : List Bool} (hu : u.length = m) : h.str (val act l₀ u) = u := by
  obtain ⟨l, _, hs⟩ := node_ret h hcard hR hu
  exact hs

lemma val_injective {u u' : List Bool} (hu : u.length = m) (hu' : u'.length = m)
    (heq : val act l₀ u = val act l₀ u') : u = u' := by
  rw [← str_val h hcard hR hu, ← str_val h hcard hR hu', heq]

/-- Along a path, every node of depth `< m` reads some register. -/
lemma path_rd (M' : Mem ι) {j : ℕ} (hj : j < m) :
    ∃ i, RdN act (node act l₀ (path act l₀ M' j)) i := by
  obtain ⟨i, k, hk, -⟩ := node_read h hcard hR (u := path act l₀ M' j) (by simp; omega)
  exact ⟨i, k, hk⟩

end Fast

end Podc.FastReadsRegisterSim
