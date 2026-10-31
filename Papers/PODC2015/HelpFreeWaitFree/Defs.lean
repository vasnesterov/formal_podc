import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Indist
import Mathlib

/-!
# Help: decided-before order and help-freedom (Section 4.4 of [CPT15])

[CPT15]: K. Censor-Hillel, E. Petrank, S. Timnat. *Help!* PODC 2015. Numbering follows the full
version, Chapter 4 of S. Timnat's PhD thesis (Technion, 2015).

We work in CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`): an implementation
`I : Impl A B P L` of the type `A` from base objects `B`, its finite executions (label lists
`h` with `I.Valid h`) form the paper's set of histories `H`, and operation instances are
`OpId P = P × ℕ` (`(p, k)` is the `k`-th operation of `p`; this names future operations too).

* `Prec S a b` — `a ≺ b` in the sequential history `S`: `a` occurs in `S` and `b` does not occur
  before it (it occurs later or not at all). Operations missing from a linearization are
  treated as coming after all others; this is the reading used by the paper's own proofs
  (Claim 4.8.1 and Claim 4.5.2), see `differencies.md`.
* `DecidedBefore I f h a b` — Definition 4.4.2: no extension `s` of `h` has `b ≺ a` in `f s`.
* `HelpFreeWith I f` — Definition 4.4.3: a pair becomes decided only at a step of the earlier
  operation by its owner; `HelpFree I` — some linearization function is help-free.
* `OwnerOnlyWith I f` / `WeaklyHelpFree I` — the weaker requirement that the deciding step is
  taken by the *owner* of the operation (not necessarily inside that operation). The
  impossibility results are proved for this weaker notion, hence are stronger than the paper's.

General facts: monotonicity and transitivity of the decided-before order, Observation 4.4.4,
the backward-propagation principle of help-freedom ("steps of other processes cannot decide
`a` before anything") and Claim 4.4.5.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-! ### Order in a sequential history -/

section Prec

variable [DecidableEq P]

/-- Position of the instance `a` in the sequential history `S` (`S.length` if absent). -/
def pos (S : List (OpId P × A.Op)) (a : OpId P) : ℕ := (S.map Prod.fst).idxOf a

/-- `a ≺ b` in the sequential history `S`: `a` occurs in `S`, and `b` either does not occur or
occurs after `a`. -/
def Prec (S : List (OpId P × A.Op)) (a b : OpId P) : Prop :=
  a ∈ S.map Prod.fst ∧ (b ∉ S.map Prod.fst ∨ pos S a < pos S b)

lemma pos_le_length (S : List (OpId P × A.Op)) (a : OpId P) : pos S a ≤ S.length := by
  simpa [pos] using List.idxOf_le_length (a := a) (l := S.map Prod.fst)

lemma pos_lt_length_iff {S : List (OpId P × A.Op)} {a : OpId P} :
    pos S a < S.length ↔ a ∈ S.map Prod.fst := by
  simpa [pos] using (List.idxOf_lt_length_iff (a := a) (l := S.map Prod.fst))

lemma pos_eq_length_iff {S : List (OpId P × A.Op)} {a : OpId P} :
    pos S a = S.length ↔ a ∉ S.map Prod.fst := by
  simpa [pos] using (List.idxOf_eq_length_iff (a := a) (l := S.map Prod.fst))

/-- `a ≺ b` iff `a` has a smaller position (absent instances sit at position `S.length`). -/
lemma prec_iff_pos_lt {S : List (OpId P × A.Op)} {a b : OpId P} :
    Prec S a b ↔ pos S a < pos S b := by
  constructor
  · rintro ⟨ha, hb | hb⟩
    · rw [pos_eq_length_iff.2 hb]; exact pos_lt_length_iff.2 ha
    · exact hb
  · intro h
    have ha : a ∈ S.map Prod.fst :=
      pos_lt_length_iff.1 (lt_of_lt_of_le h (pos_le_length S b))
    exact ⟨ha, Or.inr h⟩

lemma not_prec_iff {S : List (OpId P × A.Op)} {a b : OpId P} :
    ¬ Prec S b a ↔ pos S a ≤ pos S b := by
  rw [prec_iff_pos_lt]; omega

end Prec

/-! ### Decided-before order and help-freedom -/

variable [DecidableEq P] {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
variable (I : Impl A B P L)

/-- **Definition 4.4.2** (decided operations order). For the linearization function `f`,
the operation `a` is *decided before* `b` in the history `h` if no extension `s` of `h` (in the
set of finite histories of `I`) has `b ≺ a` in `f (h ++ s)`. -/
def DecidedBefore (f : List (Label P A) → List (OpId P × A.Op)) (h : List (Label P A))
    (a b : OpId P) : Prop :=
  ∀ s, I.Valid (h ++ s) → ¬ Prec (f (h ++ s)) b a

/-- **Definition 4.4.3** (help-free implementation), for a fixed linearization function `f`:
whenever a single step `γ` after `h` makes `a` decided before `b`, the step `γ` is a step of the
operation `a` taken by its owner. (A step of process `p` after `h` belongs to `p`'s current
operation instance `curOp h p`: the pending one, or the one an invocation starts.) -/
def HelpFreeWith (f : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  ∀ h γ a b, I.Valid (h ++ [γ]) → DecidedBefore I f (h ++ [γ]) a b →
    ¬ DecidedBefore I f h a b → curOp h γ.proc = a

/-- **Definition 4.4.3**: the implementation is help-free if some linearization function is
help-free over its set of (finite) histories. -/
def HelpFree : Prop := ∃ f, I.IsLinFun f ∧ HelpFreeWith I f

/-- Weaker than `HelpFreeWith`: a step that makes `a` decided before `b` is taken by the owner
of `a` (possibly while executing another operation). -/
def OwnerOnlyWith (f : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  ∀ h γ a b, I.Valid (h ++ [γ]) → DecidedBefore I f (h ++ [γ]) a b →
    ¬ DecidedBefore I f h a b → γ.proc = a.1

/-- Weak help-freedom: some linearization function satisfies `OwnerOnlyWith`. Help-freedom
implies it (`HelpFree.weaklyHelpFree`), so impossibility results for weakly help-free
implementations are stronger than for help-free ones. -/
def WeaklyHelpFree : Prop := ∃ f, I.IsLinFun f ∧ OwnerOnlyWith I f

variable {I}

lemma HelpFreeWith.ownerOnlyWith {f : List (Label P A) → List (OpId P × A.Op)}
    (hf : HelpFreeWith I f) : OwnerOnlyWith I f := by
  intro h γ a b hv h1 h2
  rw [← hf h γ a b hv h1 h2]

lemma HelpFree.weaklyHelpFree (h : HelpFree I) : WeaklyHelpFree I := by
  obtain ⟨f, hf, hh⟩ := h; exact ⟨f, hf, hh.ownerOnlyWith⟩

section Basic

variable {f : List (Label P A) → List (OpId P × A.Op)}

lemma decidedBefore_iff {h : List (Label P A)} {a b : OpId P} :
    DecidedBefore I f h a b ↔ ∀ s, I.Valid (h ++ s) → pos (f (h ++ s)) a ≤ pos (f (h ++ s)) b := by
  simp only [DecidedBefore, not_prec_iff]

/-- Decisions persist along extensions. -/
lemma DecidedBefore.append {h : List (Label P A)} {a b : OpId P}
    (hd : DecidedBefore I f h a b) (t : List (Label P A)) : DecidedBefore I f (h ++ t) a b := by
  intro s hs
  have := hd (t ++ s) (by simpa using hs)
  simpa using this

lemma decidedBefore_refl (h : List (Label P A)) (a : OpId P) : DecidedBefore I f h a a := by
  intro s _; rw [not_prec_iff]

/-- The decided-before order is transitive. -/
lemma DecidedBefore.trans {h : List (Label P A)} {a b c : OpId P}
    (h1 : DecidedBefore I f h a b) (h2 : DecidedBefore I f h b c) : DecidedBefore I f h a c := by
  rw [decidedBefore_iff] at *
  intro s hs; exact (h1 s hs).trans (h2 s hs)

/-- If `a` is decided before `b` and `b` is linearized in `f (h ++ s)`, then so is `a`, and `a`
comes first. -/
lemma DecidedBefore.mem {h s : List (Label P A)} {a b : OpId P} (hd : DecidedBefore I f h a b)
    (hs : I.Valid (h ++ s)) (hb : b ∈ (f (h ++ s)).map Prod.fst) :
    a ∈ (f (h ++ s)).map Prod.fst ∧ pos (f (h ++ s)) a ≤ pos (f (h ++ s)) b := by
  have hle := (decidedBefore_iff.1 hd) s hs
  refine ⟨pos_lt_length_iff.1 (lt_of_le_of_lt hle (pos_lt_length_iff.2 hb)), hle⟩

/-- An instance occurring in a linearization of `α` has been invoked in `α`. -/
lemma invoked_of_mem_lin {α : List (Label P A)} {S : List (OpId P × A.Op)}
    (hS : IsLinearization α S) {a : OpId P} (ha : a ∈ S.map Prod.fst) : Invoked α a := by
  obtain ⟨⟨a', o⟩, hy, rfl⟩ := List.mem_map.1 ha
  exact Invoked.of_opOf_eq_some (hS.op_eq _ hy)

lemma idxOf_lt_of_pair_sublist {α : Type} [DecidableEq α] {a b : α} :
    ∀ {l : List α}, List.Sublist [a, b] l → l.Nodup → l.idxOf a < l.idxOf b
  | [], h, _ => by simp at h
  | x :: l, h, hnd => by
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.1 h with h' | ⟨r, hr, h'⟩
    · have ha : a ≠ x := fun e => hnd.1 (e ▸ h'.subset (by simp))
      have hb : b ≠ x := fun e => hnd.1 (e ▸ h'.subset (by simp))
      rw [List.idxOf_cons_ne _ (Ne.symm ha), List.idxOf_cons_ne _ (Ne.symm hb)]
      exact Nat.succ_lt_succ (idxOf_lt_of_pair_sublist h' hnd.2)
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hb : b ∈ l := h'.subset (by simp)
      have hne : b ≠ a := fun e => hnd.1 (e ▸ hb)
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hne)]
      exact Nat.succ_pos _

/-- In a linearization, `a` precedes `b` if `a` returned before `b` was invoked. -/
lemma pos_lt_of_precedes {α : List (Label P A)} {S : List (OpId P × A.Op)}
    (hS : IsLinearization α S) {a b : OpId P} (hab : Precedes α a b)
    (hb : b ∈ S.map Prod.fst) : pos S a < pos S b :=
  idxOf_lt_of_pair_sublist (hS.realtime a b hab hb) hS.nodup

/-- **Observation 4.4.4 (1)**: an operation completed in `h` is decided before every operation
not yet invoked in `h`. -/
lemma decidedBefore_of_completed (hf : I.IsLinFun f) {h : List (Label P A)} {a b : OpId P}
    (ha : Completed h a) (hb : ¬ Invoked h b) : DecidedBefore I f h a b := by
  rw [decidedBefore_iff]
  intro s hs
  by_cases hbm : b ∈ (f (h ++ s)).map Prod.fst
  · exact (pos_lt_of_precedes (hf _ hs) ⟨h, s, rfl, ha, hb⟩ hbm).le
  · rw [pos_eq_length_iff.2 hbm]; exact pos_le_length _ _

/-- **Observation 4.4.4 (2)**, engine: if some extension `h ++ s` completes `b` while `a` is still
not invoked, then `a` is not decided before `b` in `h`. -/
lemma not_decidedBefore_of_extension (hf : I.IsLinFun f) {h s : List (Label P A)}
    {a b : OpId P} (hs : I.Valid (h ++ s)) (hb : Completed (h ++ s) b)
    (ha : ¬ Invoked (h ++ s) a) : ¬ DecidedBefore I f h a b := by
  intro hd
  have hbm := (hf _ hs).complete b hb
  exact ha (invoked_of_mem_lin (hf _ hs) (hd.mem hs hbm).1)

/-- **Help-freedom, backward form.** Steps of processes other than the owner of `a` cannot
decide `a` before anything: if `a` is decided before `b` after a fragment `s` without steps of
`a`'s owner, it was already decided before `s`. -/
lemma OwnerOnlyWith.decidedBefore_of_append (hh : OwnerOnlyWith I f)
    {h : List (Label P A)} {a b : OpId P} :
    ∀ {s : List (Label P A)}, I.Valid (h ++ s) → (∀ γ ∈ s, γ.proc ≠ a.1) →
      DecidedBefore I f (h ++ s) a b → DecidedBefore I f h a b := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro _ _ hd; simpa using hd
  | append_singleton s γ ih =>
    intro hv hp hd
    have hv' : I.Valid (h ++ s) := I.valid_of_prefix hv ⟨[γ], by simp⟩
    apply ih hv' (fun γ' hγ' => hp γ' (by simp [hγ']))
    by_contra hn
    have := hh (h ++ s) γ a b (by simpa using hv) (by simpa using hd) hn
    exact hp γ (by simp) this

end Basic

end Podc.HelpFreeWaitFree
