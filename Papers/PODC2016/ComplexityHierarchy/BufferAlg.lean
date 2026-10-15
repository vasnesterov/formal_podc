import Papers.PODC2016.ComplexityHierarchy.BufferLB
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# A history object from a single ℓ-buffer (Lemma 6.1 of Ellen–Gelashvili–Shavit–Zhu, PODC 2016)

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 6.1.

A *history object* supports `append x` and `get-history`, which returns the sequence of all
values appended so far. Lemma 6.1: a single `ℓ`-buffer simulates a history object with at most
`ℓ` appending processes and any number of readers.

**Algorithm.** Each value written to the buffer is a pair `(h, x)` of a history `h` and an
appended value `x`.

* `append x`: perform `get-history` to obtain `h`, then `ℓ-buffer-write (h, x)`
  (linearization point: the write).
* `get-history`: `ℓ-buffer-read` gives `a₁, …, a_ℓ` (`a_ℓ` most recent, `aᵢ = (hᵢ, xᵢ)`);
  if the buffer holds fewer than `ℓ` entries return their `xᵢ`; otherwise let `h` be the longest
  `hᵢ`; if `x₁ ∈ h` return the prefix of `h` before `x₁` followed by `x₁, …, x_ℓ`, else return
  `h, x₁, …, x_ℓ` (linearization point: the read).

The paper assumes w.l.o.g. that no value is appended twice, "achieved by having a process include
its process identifier and a sequence number". We implement this: internally every appended value
is tagged `(p, c, x)` (`p` the appender, `c` its number of previous appends); `get-history`
strips the tags.

Helper definitions live in the namespace `HistBuf`.

## Main results

* `recon_correct`: the combinatorial heart of the proof — if the writes so far satisfy the
  invariant `GoodW` (each recorded history is a prefix of the earlier writes, a process's later
  append read after its earlier write, at most `ℓ` appenders, distinct tags), then the
  reconstruction of the buffer content is exactly the sequence of all writes.
* `lemma_6_1`: the implementation `histImpl ℓ S` (appenders restricted to `S`, `|S| ≤ ℓ`) is
  linearizable (CSLib's `Impl.Linearizable`).

## Notes on the proof

The paper argues by induction on the number `k` of writes before a read, applying the induction
hypothesis to the `get-history` operations inside the `ℓ` appends whose entries are in the buffer.
We instead keep a ghost list `W` of all writes and prove the step invariant `HistBuf.Inv`: the
history stored by every write is the prefix of `W` read by its append (`GoodW.pre`); then
`recon_correct` (the paper's case analysis, including the "Figure 1" case where the longest
history does not contain `x₁`) shows that every read reconstructs all of `W`. The key
combinatorial step: if the longest stored history `h_m` had fewer than `k - ℓ` entries, the `ℓ`
appends in the buffer would be pairwise concurrent, hence by `ℓ` distinct processes, hence by all
appenders; the owner of write number `|h_m|` (before the window) is one of them, so its later
append read after that write, contradicting the maximality of `h_m`.

Model checking (exhaustive, all interleavings; `ℓ ≤ 4`, up to `ℓ` appenders with up to 6 appends
each) confirms the lemma, and finds that the bound on appenders is tight for this algorithm: with
`ℓ + 1` appenders a reader can miss an append (e.g. `ℓ = 1`: `p` and `q` both read `⊥`, `q` writes
`([], b)`, then `p` writes `([], a)`; a reader then reconstructs `[a]` instead of `[b, a]`).

## Deviations from the paper

* Values are tagged internally with `(process, sequence number)` (the paper's w.l.o.g.).
* The buffer content is a list (most recent first) of length `≤ ℓ` instead of a vector padded with
  `⊥`; the initial content is empty.
* The tie-breaking among equally long histories is "first in the buffer" (the paper leaves it
  open; all candidates are equal anyway).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

/-! ### The history object -/

/-- Operations of a history object over values `X`. -/
inductive HOp (X : Type) where
  /-- `append (x)`. -/
  | append (x : X)
  /-- `get-history ()`. -/
  | get

/-- The history object: the state is the sequence of appended values; `get` returns it, `append`
returns nothing (`[]`). -/
abbrev historySpec (X : Type) : ObjSpec where
  State := List X
  Op := HOp X
  Resp := List X
  init := []
  δ s o := match o with
    | .append x => (s ++ [x], [])
    | .get => (s, s)

namespace HistBuf

/-! ### Reconstruction -/

section Recon

variable {T : Type}

/-- The longest list in a list of lists (the first one among equally long ones). -/
def longest : List (List T) → List T
  | [] => []
  | h :: hs => if (longest hs).length ≤ h.length then h else longest hs

lemma longest_mem {hs : List (List T)} (h : hs ≠ []) : longest hs ∈ hs := by
  induction hs with
  | nil => exact absurd rfl h
  | cons h₀ hs ih =>
    unfold longest
    split_ifs
    · simp
    · rcases hs with _ | ⟨h₁, hs⟩
      · simp_all [longest]
      · exact List.mem_cons_of_mem _ (ih (by simp))

lemma length_le_longest {hs : List (List T)} {h : List T} (hh : h ∈ hs) :
    h.length ≤ (longest hs).length := by
  induction hs with
  | nil => simp at hh
  | cons h₀ hs ih =>
    unfold longest
    rcases List.mem_cons.1 hh with rfl | hh
    · split_ifs <;> omega
    · have := ih hh; split_ifs <;> omega

variable [DecidableEq T]

/-- The reconstruction of `get-history` from the content `b` of the buffer (most recent entry
first, as in `bufferSpec`). In the paper's notation `b = [a_ℓ, …, a₁]`, `aᵢ = (hᵢ, xᵢ)`. -/
def recon (ℓ : ℕ) (b : List (List T × T)) : List T :=
  match b.reverse with
  | [] => []
  | (_, x₁) :: _ =>
    if b.length < ℓ then (b.map Prod.snd).reverse
    else
      let h := longest (b.map Prod.fst)
      if x₁ ∈ h then h.takeWhile (· ≠ x₁) ++ (b.map Prod.snd).reverse
      else h ++ (b.map Prod.snd).reverse

end Recon

/-! ### Correctness of the reconstruction -/

section Core

variable {T P : Type} [DecidableEq T]

/-- The invariant on the sequence `W` of all `ℓ-buffer-write`s performed so far (in order; entry
`(h, x)` with `h` the history obtained by the append's `get-history` and `x` the tagged value);
`own x` is the process that appended `x`, `S` the set of appenders. -/
structure GoodW (S : Finset P) (own : T → P) (W : List (List T × T)) : Prop where
  /-- The history recorded by the `j`-th write is a prefix of the values written before it. -/
  pre : ∀ j (hj : j < W.length), W[j].1 <+: (W.take j).map Prod.snd
  /-- Program order: if the `j`-th and `j'`-th writes (`j < j'`) are by the same process, then the
  `get-history` of the `j'`-th append read after the `j`-th write, i.e. its history contains it. -/
  order : ∀ j j' (hjj : j < j') (hj' : j' < W.length), own (W[j]'(by omega)).2 = own W[j'].2 →
    j < W[j'].1.length
  /-- All appenders are in `S`. -/
  mem : ∀ e ∈ W, own e.2 ∈ S
  /-- Appended (tagged) values are distinct. -/
  nodup : (W.map Prod.snd).Nodup

lemma takeWhile_take_nodup {l : List T} (hl : l.Nodup) {s r : ℕ} (hsr : s < r)
    (hr : r ≤ l.length) :
    (l.take r).takeWhile (· ≠ l[s]'(by omega)) = l.take s := by
  have hsplit : l.take r = l.take s ++ l[s]'(by omega) :: (l.take r).drop (s + 1) := by
    conv_lhs => rw [← List.take_append_drop s (l.take r)]
    rw [List.take_take, min_eq_left hsr.le]
    congr 1
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp
  rw [hsplit, List.takeWhile_append_of_pos]
  · simp
  · intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    rintro rfl
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
    simp only [List.length_take] at hi
    rw [List.getElem_take] at hia
    have := (List.Nodup.getElem_inj_iff hl).1 hia
    omega

/-- **Correctness of the reconstruction** (the induction in the proof of Lemma 6.1): if the
writes satisfy `GoodW` with at most `ℓ` appenders, `get-history` applied to the buffer content
(the last `ℓ` writes, most recent first) returns the sequence of all written values. -/
theorem recon_correct {S : Finset P} {own : T → P} {W : List (List T × T)} {ℓ : ℕ}
    (hW : GoodW S own W) (hS : S.card ≤ ℓ) :
    recon ℓ (W.reverse.take ℓ) = W.map Prod.snd := by
  classical
  rcases Nat.lt_or_ge W.length ℓ with hlt | hge
  · -- fewer than `ℓ` writes: the buffer holds all of them
    rw [List.take_of_length_le (by simp; omega)]
    unfold recon
    rw [List.reverse_reverse]
    rcases W with _ | ⟨⟨h₀, x₀⟩, W'⟩
    · rfl
    · simp only [List.length_reverse]
      simp only [hlt, ↓reduceIte]
      simp [List.map_reverse]
  · rcases eq_or_ne W [] with rfl | hne
    · simp [recon]
    set n := W.length with hn
    set s := n - ℓ with hs
    have hℓ : 1 ≤ ℓ := by
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil W hne
      have := Finset.card_pos.2 ⟨_, hW.mem e he⟩
      omega
    have hsn : s < n := by omega
    have hb : W.reverse.take ℓ = (W.drop s).reverse := by
      rw [List.take_reverse]
    have hdrop : W.drop s = W[s] :: W.drop (s + 1) := List.drop_eq_getElem_cons hsn
    rw [hb]
    unfold recon
    rw [List.reverse_reverse, hdrop]
    simp only [List.length_reverse, List.length_cons, List.length_drop]
    simp only [show ¬ (W.length - (s + 1) + 1 < ℓ) by omega, ↓reduceIte]
    rw [← hdrop]
    -- the longest recorded history
    set h := longest (((W.drop s).reverse).map Prod.fst) with hh
    have hmem : h ∈ ((W.drop s).reverse).map Prod.fst :=
      longest_mem (by simp [List.drop_eq_nil_iff]; omega)
    have hle : ∀ j (hj : j < n), s ≤ j → (W[j].1).length ≤ h.length := by
      intro j hj hsj
      apply length_le_longest
      simp only [List.map_reverse, List.mem_reverse, List.mem_map]
      refine ⟨W[j], ?_, rfl⟩
      rw [List.mem_iff_getElem]
      exact ⟨j - s, by simp; omega, by simp; congr 1; omega⟩
    obtain ⟨m, hm, hsm, hhm⟩ : ∃ m, ∃ hm : m < n, s ≤ m ∧ W[m].1 = h := by
      simp only [List.map_reverse, List.mem_reverse, List.mem_map] at hmem
      obtain ⟨e, he, heh⟩ := hmem
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      simp only [List.length_drop] at hi
      exact ⟨s + i, by omega, by omega, by simpa using heh⟩
    have hpre := hW.pre m hm
    rw [hhm] at hpre
    have hhlen : h.length ≤ m := by
      have := hpre.length_le; simp at this; omega
    have htake : h = (W.map Prod.snd).take h.length := by
      rw [List.prefix_iff_eq_take.1 hpre, List.map_take, List.take_take]
      simp [List.length_take]
    -- key claim: the longest history contains all writes before the window
    have hkey : s ≤ h.length := by
      by_contra hcon
      push Not at hcon
      have hwin : ∀ j (hj : j < n), s ≤ j → (W[j].1).length < s :=
        fun j hj hsj => lt_of_le_of_lt (hle j hj hsj) hcon
      set l := (W.drop s).map (fun e => own e.2) with hl
      have hlnd : l.Nodup := by
        rw [List.Nodup, List.pairwise_iff_getElem]
        intro i j hi hj hij heq
        simp only [hl, List.length_map, List.length_drop] at hi hj
        simp only [hl, List.getElem_map, List.getElem_drop] at heq
        have := hW.order (s + i) (s + j) (by omega) (by omega) heq
        have := hwin (s + j) (by omega) (by omega)
        omega
      have hlS : l.toFinset = S := by
        apply Finset.eq_of_subset_of_card_le
        · intro q hq
          simp only [hl, List.mem_toFinset, List.mem_map] at hq
          obtain ⟨e, he, rfl⟩ := hq
          exact hW.mem e (List.mem_of_mem_drop he)
        · rw [List.toFinset_card_of_nodup hlnd]; simp [hl]; omega
      have hr : h.length < n := by omega
      have hq : own (W[h.length]).2 ∈ l.toFinset := by
        rw [hlS]; exact hW.mem _ (List.getElem_mem _)
      simp only [hl, List.mem_toFinset, List.mem_map] at hq
      obtain ⟨e, he, heq⟩ := hq
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      simp only [List.length_drop, List.getElem_drop] at hi heq
      have h1 := hW.order h.length (s + i) (by omega) (by omega) heq.symm
      have h2 := hle (s + i) (by omega) (by omega)
      omega
    have hsuffix : (((W.drop s).reverse).map Prod.snd).reverse = (W.map Prod.snd).drop s := by
      simp [List.map_reverse, List.map_drop]
    have hx : W[s].2 = (W.map Prod.snd)[s]'(by simp; omega) := by simp
    rw [hsuffix, hx]
    have hnd := hW.nodup
    split_ifs with hin
    · rw [htake, takeWhile_take_nodup hnd ?_ (by simp; omega)]
      · exact List.take_append_drop _ _
      · rcases Nat.lt_or_ge s h.length with h' | h'
        · exact h'
        · exfalso
          rw [htake] at hin
          obtain ⟨i, hi, hia⟩ := List.getElem_of_mem hin
          simp only [List.length_take] at hi
          rw [List.getElem_take] at hia
          have := (List.Nodup.getElem_inj_iff hnd).1 hia
          omega
    · have hseq : h.length = s := by
        by_contra hne'
        apply hin
        rw [htake]
        exact List.mem_iff_getElem.2 ⟨s, by simp; omega, by simp⟩
      rw [htake, hseq]
      exact List.take_append_drop _ _

/-- Extending the write sequence by a write `(h, t)` of process `own t ∈ S` whose history `h` is
a prefix of the earlier writes containing all earlier writes of the same process. -/
lemma GoodW.append {S : Finset P} {own : T → P} {W : List (List T × T)} (hW : GoodW S own W)
    {h : List T} {t : T} (hpre : h <+: W.map Prod.snd)
    (hord : ∀ j (hj : j < W.length), own W[j].2 = own t → j < h.length) (hS : own t ∈ S)
    (ht : t ∉ W.map Prod.snd) : GoodW S own (W ++ [(h, t)]) where
  pre j hj := by
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j W.length with hj' | hj'
    · rw [List.getElem_append_left hj', List.take_append_of_le_length hj'.le]
      exact hW.pre j hj'
    · have : j = W.length := by omega
      subst this
      simpa using hpre
  order j j' hjj hj' heq := by
    simp only [List.length_append, List.length_singleton] at hj'
    rw [List.getElem_append_left (by omega)] at heq
    rcases Nat.lt_or_ge j' W.length with hj'' | hj''
    · rw [List.getElem_append_left hj''] at heq ⊢
      exact hW.order j j' hjj hj'' heq
    · have : j' = W.length := by omega
      subst this
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at heq ⊢
      exact hord j (by omega) heq
  mem e he := by
    rcases List.mem_append.1 he with he | he
    · exact hW.mem e he
    · simp only [List.mem_singleton] at he; subst he; exact hS
  nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hW.nodup, by simp, ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    rintro a ha b rfl rfl; exact ht ha

end Core

/-! ### The implementation -/

section Impl

variable {P X : Type}

/-- Internally appended values are tagged `(p, c, x)`: appender `p`, its number `c` of previous
appends, and the value `x` (the paper's w.l.o.g. "no value is appended twice"). -/
abbrev Tag (P X : Type) := P × ℕ × X

/-- Values written to the buffer: a history and a (tagged) appended value. -/
abbrev Entry (P X : Type) := List (Tag P X) × Tag P X

/-- The base objects: a single `ℓ`-buffer holding `Entry`s. -/
abbrev HB (ℓ : ℕ) (P X : Type) : Unit → ObjSpec := fun _ => bufferSpec ℓ (Entry P X)

/-- Program counter of a process. -/
inductive HPc (P X : Type) where
  /-- No pending operation. -/
  | idle
  /-- `get-history`: about to `ℓ-buffer-read`. -/
  | get
  /-- `append x`: about to `ℓ-buffer-read` (its internal `get-history`). -/
  | app (x : X)
  /-- `append x`: about to `ℓ-buffer-write (h, x)`. -/
  | wr (x : X) (h : List (Tag P X))
  /-- About to return `r`. -/
  | done (r : List X)

/-- Local state: the number of completed appends (for tagging) and the program counter. -/
structure HLoc (P X : Type) where
  /-- Number of appends performed so far. -/
  cnt : ℕ
  /-- Program counter. -/
  pc : HPc P X

variable [DecidableEq P] [DecidableEq X]

/-- **The algorithm of Lemma 6.1**: a history object from one `ℓ`-buffer; only processes in `S`
may append. -/
def histImpl (ℓ : ℕ) (S : Finset P) : Impl (historySpec X) (HB ℓ P X) P (HLoc P X) where
  memInit _ := []
  locInit _ := ⟨0, .idle⟩
  invoke _ l o := match o with
    | .append x => ⟨l.cnt, .app x⟩
    | .get => ⟨l.cnt, .get⟩
  act p l := match l with
    | ⟨c, .idle⟩ => .ret [] ⟨c, .idle⟩
    | ⟨c, .get⟩ => .access () .read (fun b => ⟨c, .done ((recon ℓ b).map (·.2.2))⟩)
    | ⟨c, .app x⟩ => .access () .read (fun b => ⟨c, .wr x (recon ℓ b)⟩)
    | ⟨c, .wr x h⟩ => .access () (.write (h, (p, c, x))) (fun _ => ⟨c + 1, .done []⟩)
    | ⟨c, .done r⟩ => .ret r ⟨c, .idle⟩
  allowed p o := match o with
    | .append _ => p ∈ S
    | .get => True

/-- The current operation instance of `p` (its first not yet returned one). -/
abbrev cur (α : List (Label P (historySpec X))) (p : P) : OpId P := (p, (respsOf α p).length)

/-- The per-process part of the invariant, by program counter. -/
def ProcOK (S : Finset P) (α : List (Label P (historySpec X))) (L : List (OpId P × HOp X))
    (W : List (Entry P X)) (p : P) : HPc P X → Option (HOp X) → Prop
  | .idle, pd => pd = none
  | .get, pd => pd ≠ none ∧ cur α p ∉ L.map Prod.fst ∧ opOf α (cur α p) = some .get
  | .app x, pd => pd ≠ none ∧ cur α p ∉ L.map Prod.fst ∧ opOf α (cur α p) = some (.append x) ∧
      p ∈ S
  | .wr x h, pd => pd ≠ none ∧ cur α p ∉ L.map Prod.fst ∧ opOf α (cur α p) = some (.append x) ∧
      p ∈ S ∧ h <+: W.map Prod.snd ∧ ∀ j (hj : j < W.length), W[j].2.1 = p → j < h.length
  | .done r, pd => pd ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (cur α p, o) :: L₂ ∧
      ((historySpec X).δ ((historySpec X).runOps [] (L₁.map Prod.snd)) o).2 = r

/-- The invariant of `histImpl` (`W`: all buffer writes so far, a ghost variable). -/
structure Inv (ℓ : ℕ) (S : Finset P) (α : List (Label P (historySpec X)))
    (C : Config (historySpec X) (HB ℓ P X) P (HLoc P X)) (L : List (OpId P × HOp X))
    (W : List (Entry P X)) : Prop where
  lin : IsLinearization α L
  good : GoodW S Prod.fst W
  mem : C.mem () = W.reverse.take ℓ
  state : linState (A := historySpec X) L = W.map (fun e => e.2.2.2)
  cnt : ∀ e ∈ W, e.2.2.1 < (C.loc e.2.1).cnt
  proc : ∀ p, ProcOK S α L W p (C.loc p).pc (C.pend p)

lemma invoked_of_opOf {α : List (Label P (historySpec X))} {x : OpId P} {o : HOp X}
    (h : opOf α x = some o) : Invoked α x := by
  simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma ProcOK.mono {S : Finset P} {α α' : List (Label P (historySpec X))}
    {L L₀ : List (OpId P × HOp X)} {W W₀ : List (Entry P X)} {q : P} {c : HPc P X}
    {pd : Option (HOp X)}
    (hresp : respsOf α' q = respsOf α q)
    (hop : ∀ x, Invoked α x → opOf α' x = opOf α x)
    (hL₀ : cur α q ∉ L₀.map Prod.fst)
    (hW₀ : ∀ e ∈ W₀, e.2.1 ≠ q)
    (h : ProcOK S α L W q c pd) : ProcOK S α' (L ++ L₀) (W ++ W₀) q c pd := by
  have hcur : cur α' q = cur α q := by simp [cur, hresp]
  cases c with
  | idle => exact h
  | get =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, ?_, ?_⟩
    · rw [hcur, List.map_append, List.mem_append, not_or]; exact ⟨h2, hL₀⟩
    · rw [hcur, hop _ (invoked_of_opOf h3), h3]
  | app x =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [hcur, List.map_append, List.mem_append, not_or]; exact ⟨h2, hL₀⟩
    · rw [hcur, hop _ (invoked_of_opOf h3), h3]
  | wr x hh =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, ?_, ?_, h4, ?_, ?_⟩
    · rw [hcur, List.map_append, List.mem_append, not_or]; exact ⟨h2, hL₀⟩
    · rw [hcur, hop _ (invoked_of_opOf h3), h3]
    · rw [List.map_append]; exact h5.trans (List.prefix_append _ _)
    · intro j hj hjq
      rcases Nat.lt_or_ge j W.length with hj' | hj'
      · rw [List.getElem_append_left hj'] at hjq; exact h6 j hj' hjq
      · exfalso
        rw [List.getElem_append_right hj'] at hjq
        exact hW₀ _ (List.getElem_mem _) hjq
  | done r =>
    obtain ⟨h1, L₁, L₂, o, hs, hr⟩ := h
    exact ⟨h1, L₁, L₂ ++ L₀, o, by rw [hcur, hs]; simp, hr⟩

lemma ProcOK.idle_of_none {S : Finset P} {α : List (Label P (historySpec X))}
    {L : List (OpId P × HOp X)} {W : List (Entry P X)} {p : P} {c : HPc P X}
    (h : ProcOK S α L W p c none) : c = .idle := by
  cases c <;> simp_all [ProcOK]

end Impl

/-! ### Preservation of the invariant -/

section Proof

variable {P X : Type} [DecidableEq P] [DecidableEq X] {ℓ : ℕ} {S : Finset P}
  {α : List (Label P (historySpec X))} {C₀ C : Config (historySpec X) (HB ℓ P X) P (HLoc P X)}
  {L : List (OpId P × HOp X)} {W : List (Entry P X)}

lemma inv_init : Inv ℓ S ([] : List (Label P (historySpec X))) (histImpl ℓ S).initCfg [] [] where
  lin := ⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
    fun a b hab hb => by simp at hb, trivial⟩
  good := ⟨fun j hj => by simp at hj, fun j j' _ hj' => by simp at hj', by simp, by simp⟩
  mem := by simp [Impl.initCfg, histImpl]
  state := rfl
  cnt := by simp
  proc p := rfl

lemma inv_step_inv (hI : Inv ℓ S α C₀ L W) (hrun : (histImpl ℓ S).run α = some C₀) {p : P}
    {o : HOp X} (h : (histImpl ℓ S).step C₀ (.inv p o) = some C) :
    Inv ℓ S (α ++ [.inv p o]) C L W := by
  obtain ⟨h0, hall, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hlen : (opsOf α p).length = (respsOf α p).length := by
    rcases (histImpl ℓ S).run_counts hrun p with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h0 h1
  have hcnt : ∀ q, (C.loc q).cnt = (C₀.loc q).cnt := by
    intro q
    by_cases hq : q = p
    · subst hq; rw [hloc, Function.update_self]; cases o <;> rfl
    · rw [hloc, Function.update_of_ne hq]
  have hresp : ∀ q, respsOf (α ++ [.inv p o]) q = respsOf α q := by intro q; simp
  have hnL : cur α p ∉ L.map Prod.fst := by
    intro hm
    have := hI.lin.mem_invoked hm
    simp [Invoked] at this; omega
  have hop : opOf (α ++ [.inv p o]) (cur α p) = some o := by
    simp [opOf, opsOf_append, ← hlen]
  refine ⟨hI.lin.append_inv p o, hI.good, by rw [hmem]; exact hI.mem, hI.state,
    fun e he => by rw [hcnt]; exact hI.cnt e he, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq
    have hcur : cur (α ++ [.inv q o]) q = cur α q := by simp [cur, hresp]
    rw [hpend, hloc, Function.update_self, Function.update_self]
    cases o with
    | append x =>
      exact ⟨by simp, by rw [hcur]; exact hnL, by rw [hcur]; exact hop, hall⟩
    | get => exact ⟨by simp, by rw [hcur]; exact hnL, by rw [hcur]; exact hop⟩
  · obtain ⟨h1, h2⟩ := Impl.step_other h (q := q) (Ne.symm hq)
    rw [h1, h2]
    have := (hI.proc q).mono (α' := α ++ [.inv p o]) (L₀ := []) (W₀ := []) (hresp q)
      (fun _ hx => opOf_append_of_invoked hx) (by simp) (by simp)
    rwa [List.append_nil, List.append_nil] at this

lemma inv_step_ret (hI : Inv ℓ S α C₀ L W) {p : P} {r : List X}
    (h : (histImpl ℓ S).step C₀ (.ret p r) = some C) :
    Inv ℓ S (α ++ [.ret p r]) C L W := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hp := hI.proc p
  rcases hl : C₀.loc p with ⟨c, pc⟩
  rw [hl] at hp hact
  cases pc with
  | idle => exact absurd hp h0
  | get => simp [histImpl] at hact
  | app x => simp [histImpl] at hact
  | wr x hh => simp [histImpl] at hact
  | done r' =>
    simp only [histImpl, Action.ret.injEq] at hact
    obtain ⟨hrr, rfl⟩ := hact
    subst hrr
    obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hp
    have hcnt : ∀ q, (C.loc q).cnt = (C₀.loc q).cnt := by
      intro q
      by_cases hq : q = p
      · subst hq; rw [hloc, Function.update_self, hl]
      · rw [hloc, Function.update_of_ne hq]
    refine ⟨hI.lin.append_ret L₁ L₂ o hs hr, hI.good, by rw [hmem]; exact hI.mem, hI.state,
      fun e he => by rw [hcnt]; exact hI.cnt e he, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq
      rw [hpend, hloc, Function.update_self, Function.update_self]
      rfl
    · obtain ⟨h1, h2⟩ := Impl.step_other h (q := q) (Ne.symm hq)
      rw [h1, h2]
      have := (hI.proc q).mono (α' := α ++ [.ret p r']) (L₀ := []) (W₀ := [])
        (by simp [respsOf_append, Ne.symm hq]) (fun _ hx => opOf_append_of_invoked hx)
        (by simp) (by simp)
      rwa [List.append_nil, List.append_nil] at this

lemma inv_step_tau (hS : S.card ≤ ℓ) (hI : Inv ℓ S α C₀ L W) {p : P}
    (h : (histImpl ℓ S).step C₀ (.tau p) = some C) :
    ∃ L' W', Inv ℓ S (α ++ [.tau p]) C L' W' := by
  obtain ⟨h0, hpend, i, o', k, hact, hmem, hloc⟩ := Impl.step_tau h
  cases i
  have hp := hI.proc p
  have hresp : ∀ q, respsOf (α ++ [.tau p]) q = respsOf α q := by intro q; simp
  have hcurp : cur (α ++ [.tau p]) p = cur α p := by simp [cur, hresp]
  have hnc : ¬ Completed α (cur α p) := by simp [Completed]
  have hrec : recon ℓ (C₀.mem ()) = W.map Prod.snd := by
    rw [hI.mem]; exact recon_correct hI.good hS
  rcases hl : C₀.loc p with ⟨c, pc⟩
  rw [hl] at hp hact
  have hother : ∀ q, q ≠ p → C.loc q = C₀.loc q ∧ C.pend q = C₀.pend q :=
    fun q hq => Impl.step_other h (q := q) (Ne.symm hq)
  cases pc with
  | idle => exact absurd hp h0
  | done r' => simp [histImpl] at hact
  | get =>
    simp only [histImpl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o' = .read := (eq_of_heq h1).symm
    subst ho
    have hk := (eq_of_heq h2).symm
    subst hk
    obtain ⟨hp1, hp2, hp3⟩ := hp
    refine ⟨L ++ [(cur α p, .get)], W, (hI.lin.push hp3 hp2 hnc).append_tau p, hI.good, ?_, ?_,
      ?_, ?_⟩
    · rw [hmem, Function.update_self]; exact hI.mem
    · rw [← hI.state]; simp [linState, ObjSpec.runOps]
    · intro e he
      have := hI.cnt e he
      by_cases hq : e.2.1 = p
      · rw [hq, hloc, Function.update_self]; rw [hq, hl] at this; exact this
      · rw [(hother _ hq).1]; exact this
    · intro q
      by_cases hq : q = p
      · subst hq
        rw [hpend, hloc, Function.update_self]
        refine ⟨h0, L, [], .get, by rw [hcurp], ?_⟩
        simp only [historySpec]
        have := hI.state
        simp only [linState] at this
        rw [this, hrec, List.map_map]
        rfl
      · rw [(hother q hq).1, (hother q hq).2]
        have := (hI.proc q).mono (α' := α ++ [.tau p]) (L₀ := [(cur α p, .get)]) (W₀ := [])
          (hresp q) (fun _ hx => opOf_append_of_invoked hx)
          (by simp [cur, hq]) (by simp)
        rwa [List.append_nil] at this
  | app x =>
    simp only [histImpl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o' = .read := (eq_of_heq h1).symm
    subst ho
    have hk := (eq_of_heq h2).symm
    subst hk
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    refine ⟨L, W, hI.lin.append_tau p, hI.good, ?_, hI.state, ?_, ?_⟩
    · rw [hmem, Function.update_self]; exact hI.mem
    · intro e he
      have := hI.cnt e he
      by_cases hq : e.2.1 = p
      · rw [hq, hloc, Function.update_self]; rw [hq, hl] at this; exact this
      · rw [(hother _ hq).1]; exact this
    · intro q
      by_cases hq : q = p
      · subst hq
        rw [hpend, hloc, Function.update_self]
        dsimp only
        rw [hrec]
        refine ⟨h0, by rw [hcurp]; exact hp2, by rw [hcurp,
          opOf_append_of_invoked (invoked_of_opOf hp3)]; exact hp3, hp4, List.prefix_refl _, ?_⟩
        intro j hj _; simpa using hj
      · rw [(hother q hq).1, (hother q hq).2]
        have := (hI.proc q).mono (α' := α ++ [.tau p]) (L₀ := []) (W₀ := [])
          (hresp q) (fun _ hx => opOf_append_of_invoked hx) (by simp) (by simp)
        rwa [List.append_nil, List.append_nil] at this
  | wr x hh =>
    simp only [histImpl, Action.access.injEq, true_and] at hact
    obtain ⟨h1, h2⟩ := hact
    have ho : o' = .write (hh, (p, c, x)) := (eq_of_heq h1).symm
    subst ho
    have hk := (eq_of_heq h2).symm
    subst hk
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hp
    set e : Entry P X := (hh, (p, c, x)) with he
    have hnotin : (p, c, x) ∉ W.map Prod.snd := by
      intro hm
      obtain ⟨e', he', hee⟩ := List.mem_map.1 hm
      have := hI.cnt e' he'
      rw [hee, hl] at this
      exact lt_irrefl _ this
    refine ⟨L ++ [(cur α p, .append x)], W ++ [e], (hI.lin.push hp3 hp2 hnc).append_tau p,
      hI.good.append hp5 hp6 hp4 hnotin, ?_, ?_, ?_, ?_⟩
    · rw [hmem, Function.update_self, hI.mem]
      simp only [bufWrite, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact take_append_take [e] W.reverse ℓ
    · have := hI.state
      simp only [linState] at this ⊢
      rw [List.map_append, ObjSpec.runOps_append, this, List.map_append]
      simp [e, ObjSpec.runOps]
    · intro e' he'
      have hcp : (C.loc p).cnt = c + 1 := by rw [hloc, Function.update_self]
      rcases List.mem_append.1 he' with he' | he'
      · by_cases hq : e'.2.1 = p
        · rw [hq, hcp]
          have := hI.cnt e' he'
          rw [hq, hl] at this
          dsimp only at this
          omega
        · rw [(hother _ hq).1]; exact hI.cnt e' he'
      · simp only [List.mem_singleton] at he'
        rw [he', he]
        dsimp only
        rw [hcp]; omega
    · intro q
      by_cases hq : q = p
      · subst hq
        rw [hpend, hloc, Function.update_self]
        exact ⟨h0, L, [], .append x, by rw [hcurp], rfl⟩
      · rw [(hother q hq).1, (hother q hq).2]
        exact (hI.proc q).mono (α' := α ++ [.tau p]) (L₀ := [(cur α p, .append x)]) (W₀ := [e])
          (hresp q) (fun _ hx => opOf_append_of_invoked hx)
          (by simp [cur, hq]) (by simp [e, Ne.symm hq])

theorem inv_of_run (hS : S.card ≤ ℓ) {α : List (Label P (historySpec X))}
    {C : Config (historySpec X) (HB ℓ P X) P (HLoc P X)}
    (h : (histImpl ℓ S).run α = some C) : ∃ L W, Inv ℓ S α C L W := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom, Option.some.injEq] at h; subst h
    exact ⟨[], [], inv_init⟩
  | append_singleton α lab ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (histImpl ℓ S).runFrom (histImpl ℓ S).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨L, W, hI⟩ := ih hα
      cases lab with
      | inv p o => exact ⟨L, W, inv_step_inv hI hα h⟩
      | tau p => exact inv_step_tau hS hI h
      | ret p r => exact ⟨L, W, inv_step_ret hI h⟩


end Proof

end HistBuf

section Main

open HistBuf

variable {P X : Type} [DecidableEq P] [DecidableEq X]

/-- **Lemma 6.1** of [EGSZ16]: a single `ℓ`-buffer simulates a history object on which at most
`ℓ` different processes (those in `S`, `|S| ≤ ℓ`) perform `append` and any number of processes
perform `get-history`: the implementation `histImpl ℓ S` is linearizable. (The linearization
points are the paper's: the `ℓ-buffer-write` of an `append`, the `ℓ-buffer-read` of a
`get-history`; see `Inv`.) -/
theorem lemma_6_1 (ℓ : ℕ) (S : Finset P) (hS : S.card ≤ ℓ) :
    (histImpl (X := X) ℓ S).Linearizable := by
  have : ∀ α : List (Label P (historySpec X)), ∃ L, (histImpl ℓ S).Valid α →
      IsLinearization α L := by
    intro α
    cases hα : (histImpl ℓ S).run α with
    | none => exact ⟨[], fun ⟨C, hC⟩ => by rw [hα] at hC; cases hC⟩
    | some C =>
      obtain ⟨L, W, hI⟩ := inv_of_run hS hα
      exact ⟨L, fun _ => hI.lin⟩
  choose f hf using this
  exact ⟨f, fun α hα => hf α hα⟩

end Main

end Cslib.SharedMemory.ComplexityHierarchy
