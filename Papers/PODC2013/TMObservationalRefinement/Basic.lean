import Mathlib

/-!
# Histories of a transactional system (Section 3)

Attiya, Gotsman, Hans, Rinetzky. *A Programming Language Perspective on Transactional Memory
Consistency.* PODC 2013.

* `IKind O M`, `IAct T O M`: interface actions (Definition 1); `(t, k)` is action `k` by thread `t`.
* `WellFormedLit`: Definition 2 exactly as printed; `WellFormed`: Definition 2 with the evidently
  intended extra requirement that `txcommit` actions occur inside transactions (as in the journal
  version, JACM 2017, Definition 3.2(vi)).
* `WellFormed` is characterized by a per-thread automaton (`wellFormed_iff_run`).
* `Complete` (Definition 3), `IsTS` (history sets).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

/-- The kind of an interface action (Definition 1), without its thread. -/
inductive IKind (O M : Type) where
  | txbegin
  | txcommit
  | call (o : O) (f : M) (n : ℤ)
  | ok
  | committed
  | aborted
  | ret (n : ℤ) (o : O) (f : M)
  deriving DecidableEq

/-- An interface action `(t, k)` (Definition 1). -/
abbrev IAct (T O M : Type) := T × IKind O M

variable {T O M : Type}

namespace IKind

/-- Request actions. -/
def isReq : IKind O M → Bool
  | txbegin | txcommit | call .. => true
  | _ => false

/-- `Corr a b`: `b` is a response corresponding to the request `a` (Definition 1). -/
def Corr : IKind O M → IKind O M → Prop
  | txbegin, ok => True
  | txcommit, committed => True
  | txcommit, aborted => True
  | call o f _, ret _ o' f' => o' = o ∧ f' = f
  | call .., aborted => True
  | _, _ => False

/-- `committed` or `aborted`. -/
def isEnd : IKind O M → Bool
  | committed | aborted => true
  | _ => false

/-- `txbegin`, `committed` or `aborted` (the actions delimiting transactions). -/
def isBound : IKind O M → Bool
  | txbegin | committed | aborted => true
  | _ => false

/-- `txbegin`, `txcommit`, `committed` or `aborted`. -/
def isCtl : IKind O M → Bool
  | txbegin | txcommit | committed | aborted => true
  | _ => false

/-- `txbegin`. -/
def isTxbegin : IKind O M → Bool
  | txbegin => true
  | _ => false

/-- `txcommit`. -/
def isTxcommit : IKind O M → Bool
  | txcommit => true
  | _ => false

/-- `call` or `ret`. -/
def isCallRet : IKind O M → Bool
  | call .. | ret .. => true
  | _ => false

end IKind

open IKind

/-- Projection `H|t` of a history onto the actions of thread `t`, as a list of kinds. -/
def proj [DecidableEq T] (t : T) (H : List (IAct T O M)) : List (IKind O M) :=
  (H.filter (fun a => a.1 = t)).map Prod.snd

/-! ### Definition 2 (well-formed histories), per thread -/

/-- First bullet: alternating requests and corresponding responses, starting with a request. -/
def ReqResp : List (IKind O M) → Prop
  | [] => True
  | [a] => a.isReq = true
  | a :: b :: l => a.isReq = true ∧ Corr a b ∧ ReqResp l

/-- Second bullet: `txbegin` alternates with `committed`/`aborted`, starting with `txbegin`
(applied to the projection onto these three kinds of actions). -/
def TxAlt : List (IKind O M) → Prop
  | [] => True
  | [a] => a = txbegin
  | a :: b :: l => a = txbegin ∧ b.isEnd = true ∧ TxAlt l

/-- `InTx l`: `l = l₁ txbegin l₂` where `l₂` contains no `txbegin`, `txcommit`, `committed` or
`aborted` action. -/
def InTx (l : List (IKind O M)) : Prop :=
  ∃ l₁ l₂, l = l₁ ++ txbegin :: l₂ ∧ ∀ b ∈ l₂, b.isCtl = false

/-- Third bullet, for actions satisfying `p`: every such action is preceded by an open
transaction (`InTx`). The paper states it for `call`/`ret`. -/
def InsideFor (p : IKind O M → Bool) (l : List (IKind O M)) : Prop :=
  ∀ l₁ a l₂, l = l₁ ++ a :: l₂ → p a = true → InTx l₁

/-- Definition 2 for a single thread, exactly as printed. -/
def WFThreadLit (l : List (IKind O M)) : Prop :=
  ReqResp l ∧ TxAlt (l.filter isBound) ∧ InsideFor isCallRet l

/-- Definition 2 for a single thread, with `txcommit` also required to occur inside a transaction. -/
def WFThread (l : List (IKind O M)) : Prop :=
  WFThreadLit l ∧ InsideFor isTxcommit l

/-- **Definition 2, as printed.** -/
def WellFormedLit [DecidableEq T] (H : List (IAct T O M)) : Prop :=
  ∀ t, WFThreadLit (proj t H)

/-- **Definition 2, repaired**: additionally `txcommit` occurs only inside transactions. -/
def WellFormed [DecidableEq T] (H : List (IAct T O M)) : Prop :=
  ∀ t, WFThread (proj t H)

/-- **Definition 3.** A history is complete if every `txbegin` of `t` is followed by a
`committed`/`aborted` action of `t`. -/
def Complete (H : List (IAct T O M)) : Prop :=
  ∀ H₁ t H₂, H = H₁ ++ (t, txbegin) :: H₂ → (t, committed) ∈ H₂ ∨ (t, aborted) ∈ H₂

/-! ### The per-thread automaton -/

/-- States of a thread's interaction with the transactional system. -/
inductive TState (O M : Type) where
  | idle
  | beginP
  | inTx
  | callP (o : O) (f : M)
  | commitP
  deriving DecidableEq

namespace TState

open Classical in
/-- One step of the per-thread automaton. -/
noncomputable def step : TState O M → IKind O M → Option (TState O M)
  | idle, txbegin => some beginP
  | beginP, ok => some inTx
  | inTx, call o f _ => some (callP o f)
  | inTx, txcommit => some commitP
  | callP o f, ret _ o' f' => if o' = o ∧ f' = f then some inTx else none
  | callP _ _, aborted => some idle
  | commitP, committed => some idle
  | commitP, aborted => some idle
  | _, _ => none

/-- Run of the automaton. -/
noncomputable def run (q : TState O M) (l : List (IKind O M)) : Option (TState O M) :=
  l.foldlM step q

@[simp] lemma run_nil (q : TState O M) : run q [] = some q := rfl

@[simp] lemma run_cons (q : TState O M) (a : IKind O M) (l : List (IKind O M)) :
    run q (a :: l) = (step q a).bind (fun q' => run q' l) := by
  simp [run, List.foldlM_cons]

lemma run_append (q : TState O M) (l l' : List (IKind O M)) :
    run q (l ++ l') = (run q l).bind (fun q' => run q' l') := by
  simp [run, List.foldlM_append]

lemma run_concat (q : TState O M) (l : List (IKind O M)) (a : IKind O M) :
    run q (l ++ [a]) = (run q l).bind (fun q' => step q' a) := by
  rw [run_append]; congr; funext q'; simp

/-- Requests are accepted in `idle`/`inTx`. -/
def neutral : TState O M → Bool
  | idle | inTx => true
  | _ => false

/-- Inside a transaction (between `txbegin` and `committed`/`aborted`). -/
def inside : TState O M → Bool
  | idle => false
  | _ => true

/-- Open transaction that has not yet requested to commit. -/
def opn : TState O M → Bool
  | beginP | inTx | callP .. => true
  | _ => false

end TState

open TState

/-! ### Auxiliary list lemmas -/

/-- `ReqResp` of a snoc. -/
lemma reqResp_concat : ∀ (l : List (IKind O M)) (a : IKind O M),
    ReqResp (l ++ [a]) ↔ ReqResp l ∧ (Even l.length → a.isReq = true) ∧
      (∀ l' x, l = l' ++ [x] → Odd l.length → Corr x a)
  | [], a => by simp [ReqResp]
  | [x], a => by
    simp only [List.cons_append, List.nil_append, ReqResp, List.length_singleton]
    constructor
    · rintro ⟨h1, h2, -⟩
      refine ⟨h1, fun he => absurd he (by decide), ?_⟩
      intro l' y hl _
      have : l' = [] ∧ y = x := by
        rcases l' with _ | ⟨z, l'⟩
        · simp at hl; exact ⟨rfl, hl.symm⟩
        · simp at hl
      obtain ⟨rfl, rfl⟩ := this; exact h2
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3 [] x rfl (by decide), trivial⟩
  | x :: y :: l, a => by
    simp only [List.cons_append, ReqResp, List.length_cons]
    rw [reqResp_concat l a]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨⟨h1, h2, h3⟩, fun he => h4 (by simpa [Nat.even_add_one] using he), ?_⟩
      intro l' z hl ho
      rcases l' with _ | ⟨w, l'⟩
      · simp at hl
      rcases l' with _ | ⟨w', l'⟩
      · simp at hl; obtain ⟨-, -, rfl⟩ := hl; exact absurd ho (by simp [Nat.odd_iff])
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl, rfl⟩ := hl
      exact h5 l' z rfl (by simpa [Nat.odd_add_one] using ho)
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
      refine ⟨h1, h2, h3, fun he => h4 (by simpa [Nat.even_add_one] using he), ?_⟩
      intro l' z hl ho
      exact h5 (x :: y :: l') z (by simp [hl]) (by simpa [Nat.odd_add_one] using ho)

/-- `TxAlt` of a snoc. -/
lemma txAlt_concat : ∀ (l : List (IKind O M)) (a : IKind O M),
    TxAlt (l ++ [a]) ↔ TxAlt l ∧ (Even l.length → a = txbegin) ∧ (Odd l.length → a.isEnd = true)
  | [], a => by simp [TxAlt]
  | [x], a => by simp [TxAlt]
  | x :: y :: l, a => by
    simp only [List.cons_append, TxAlt, List.length_cons]
    rw [txAlt_concat l a]
    simp only [Nat.even_add_one, Nat.odd_add_one, not_not, Nat.not_even_iff_odd,
      Nat.not_odd_iff_even]
    tauto

lemma inTx_concat (l : List (IKind O M)) (a : IKind O M) :
    InTx (l ++ [a]) ↔ a = txbegin ∨ (InTx l ∧ a.isCtl = false) := by
  constructor
  · rintro ⟨l₁, l₂, h, h2⟩
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', b, rfl⟩
    · simp at h; exact Or.inl h.2
    · have h' : l ++ [a] = (l₁ ++ txbegin :: l₂') ++ [b] := by simp [h]
      rw [List.append_singleton_inj] at h'
      obtain ⟨rfl, hb⟩ := h'
      subst hb
      exact Or.inr ⟨⟨l₁, l₂', rfl, fun c hc => h2 c (by simp [hc])⟩, h2 _ (by simp)⟩
  · rintro (rfl | ⟨⟨l₁, l₂, rfl, h2⟩, ha⟩)
    · exact ⟨l, [], rfl, by simp⟩
    · refine ⟨l₁, l₂ ++ [a], by simp, ?_⟩
      intro b hb; simp at hb; rcases hb with hb | rfl
      · exact h2 b hb
      · exact ha

lemma not_inTx_nil : ¬ InTx ([] : List (IKind O M)) := by
  rintro ⟨l₁, l₂, h, -⟩; simp at h

lemma insideFor_concat (p : IKind O M → Bool) (l : List (IKind O M)) (a : IKind O M) :
    InsideFor p (l ++ [a]) ↔ InsideFor p l ∧ (p a = true → InTx l) := by
  constructor
  · intro h
    refine ⟨fun l₁ b l₂ hl hb => h l₁ b (l₂ ++ [a]) (by simp [hl]) hb, fun ha => h l a [] rfl ha⟩
  · rintro ⟨h1, h2⟩ l₁ b l₂ hl hb
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', c, rfl⟩
    · rw [List.append_singleton_inj] at hl
      obtain ⟨rfl, hb'⟩ := hl; subst hb'; exact h2 hb
    · have : l ++ [a] = (l₁ ++ b :: l₂') ++ [c] := by simp [hl]
      rw [List.append_singleton_inj] at this
      obtain ⟨rfl, -⟩ := this
      exact h1 l₁ b l₂' rfl hb

/-! ### The automaton characterizes `WFThread` -/

/-- Invariants of a run from `idle`. -/
structure RunInv (l : List (IKind O M)) (q : TState O M) : Prop where
  neutral_iff : q.neutral = true ↔ Even l.length
  last_beginP : q = beginP → ∃ l', l = l' ++ [txbegin]
  last_callP : ∀ o f, q = callP o f → ∃ l' n, l = l' ++ [call o f n]
  last_commitP : q = commitP → ∃ l', l = l' ++ [txcommit]
  inside_iff : q.inside = true ↔ Odd (l.filter isBound).length
  opn_iff : q.opn = true ↔ InTx l

lemma runInv_nil : RunInv ([] : List (IKind O M)) idle where
  neutral_iff := by simp [neutral]
  last_beginP := by simp
  last_callP := by simp
  last_commitP := by simp
  inside_iff := by simp [inside]
  opn_iff := by simp [opn, not_inTx_nil]

lemma step_eq_some {q q' : TState O M} {a : IKind O M} :
    step q a = some q' ↔
      (q = idle ∧ a = txbegin ∧ q' = beginP) ∨ (q = beginP ∧ a = ok ∧ q' = inTx) ∨
      (∃ o f n, q = inTx ∧ a = call o f n ∧ q' = callP o f) ∨
      (q = inTx ∧ a = txcommit ∧ q' = commitP) ∨
      (∃ o f n, q = callP o f ∧ a = ret n o f ∧ q' = inTx) ∨
      (∃ o f, q = callP o f ∧ a = aborted ∧ q' = idle) ∨
      (q = commitP ∧ (a = committed ∨ a = aborted) ∧ q' = idle) := by
  constructor
  · intro h
    cases q <;> cases a <;> simp [step] at h <;> (try split_ifs at h) <;> simp_all
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, rfl | rfl, rfl⟩) <;> simp [step]

lemma runInv_step {l : List (IKind O M)} {q q' : TState O M} {a : IKind O M}
    (h : RunInv l q) (hs : step q a = some q') : RunInv (l ++ [a]) q' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha, rfl⟩ <;>
  [skip; skip; skip; skip; skip; skip; rcases ha with rfl | rfl] <;>
  constructor <;>
  simp_all [neutral, inside, opn, isBound, isCtl, inTx_concat, List.filter_append, List.filter_cons,
    Nat.even_add_one, Nat.odd_add_one]

lemma runInv_of_run : ∀ (l : List (IKind O M)) (q : TState O M), run idle l = some q → RunInv l q := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro q h; simp at h; subst h; exact runInv_nil
  | append_singleton l a ih =>
    intro q h
    rw [run_concat] at h
    obtain ⟨q₀, h₀, hs⟩ := Option.bind_eq_some_iff.mp h
    exact runInv_step (ih q₀ h₀) hs

/-- **Characterization of (repaired) Definition 2 by the per-thread automaton.** -/
lemma step_isSome_of {l : List (IKind O M)} {q : TState O M} {a : IKind O M}
    (I : RunInv l q) (hw : WFThread (l ++ [a])) : (step q a).isSome := by
  obtain ⟨⟨hr, ht, hc⟩, hx⟩ := hw
  rw [reqResp_concat] at hr
  obtain ⟨-, hr1, hr2⟩ := hr
  have hc1 := ((insideFor_concat _ _ _).mp hc).2
  have hx1 := ((insideFor_concat _ _ _).mp hx).2
  rw [List.filter_append] at ht
  cases q with
  | idle =>
    have hreq := hr1 (I.neutral_iff.mp rfl)
    have hno : ¬ InTx l := fun h => by simpa [opn] using I.opn_iff.mpr h
    cases a <;> simp_all [isReq, step, isCallRet, isTxcommit]
  | inTx =>
    have hreq := hr1 (I.neutral_iff.mp rfl)
    have hodd : Odd (l.filter isBound).length := I.inside_iff.mp rfl
    cases a <;> simp_all [isReq, step]
    simp only [List.filter, isBound] at ht
    rw [txAlt_concat] at ht
    simpa [isEnd] using ht.2.2 hodd
  | beginP =>
    obtain ⟨l', rfl⟩ := I.last_beginP rfl
    have ho : Odd (l' ++ [txbegin]).length := by
      rw [← Nat.not_even_iff_odd, ← I.neutral_iff]; simp [neutral]
    have := hr2 l' txbegin rfl ho
    cases a <;> simp_all [Corr, step]
  | callP o f =>
    obtain ⟨l', n, rfl⟩ := I.last_callP o f rfl
    have ho : Odd (l' ++ [call o f n]).length := by
      rw [← Nat.not_even_iff_odd, ← I.neutral_iff]; simp [neutral]
    have := hr2 l' _ rfl ho
    cases a <;> simp_all [Corr, step]
  | commitP =>
    obtain ⟨l', rfl⟩ := I.last_commitP rfl
    have ho : Odd (l' ++ [txcommit]).length := by
      rw [← Nat.not_even_iff_odd, ← I.neutral_iff]; simp [neutral]
    have := hr2 l' _ rfl ho
    cases a <;> simp_all [Corr, step]

lemma wfThread_concat_of_step {l : List (IKind O M)} {q q' : TState O M} {a : IKind O M}
    (I : RunInv l q) (hw : WFThread l) (hs : step q a = some q') : WFThread (l ++ [a]) := by
  obtain ⟨⟨hr, ht, hc⟩, hx⟩ := hw
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [reqResp_concat]
    refine ⟨hr, fun he => ?_, fun l' x hl ho => ?_⟩
    · have := I.neutral_iff.mpr he
      rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha, rfl⟩ <;>
        simp_all [neutral, isReq]
    · subst hl
      have hn : q.neutral = false := by
        by_contra hc; simp at hc; exact (Nat.not_even_iff_odd.mpr ho) (I.neutral_iff.mp hc)
      rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · simp [neutral] at hn
      · obtain ⟨l'', hl''⟩ := I.last_beginP rfl
        rw [List.append_singleton_inj] at hl''; obtain ⟨-, rfl⟩ := hl''; simp [Corr]
      · simp [neutral] at hn
      · simp [neutral] at hn
      · obtain ⟨l'', n', hl''⟩ := I.last_callP o f rfl
        rw [List.append_singleton_inj] at hl''; obtain ⟨-, rfl⟩ := hl''; simp [Corr]
      · obtain ⟨l'', n', hl''⟩ := I.last_callP o f rfl
        rw [List.append_singleton_inj] at hl''; obtain ⟨-, rfl⟩ := hl''; simp [Corr]
      · obtain ⟨l'', hl''⟩ := I.last_commitP rfl
        rw [List.append_singleton_inj] at hl''; obtain ⟨-, rfl⟩ := hl''
        rcases ha with rfl | rfl <;> simp [Corr]
  · have hi := I.inside_iff
    rw [List.filter_append]
    by_cases hb : a.isBound
    · simp only [List.filter, hb]
      rw [txAlt_concat]
      refine ⟨ht, fun he => ?_, fun ho => ?_⟩
      · have : q.inside = false := by
          by_contra hc; simp at hc; exact (Nat.not_odd_iff_even.mpr he) (hi.mp hc)
        rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha, rfl⟩ <;>
          simp_all [inside, isBound]
      · have := hi.mpr ho
        rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha, rfl⟩ <;>
          simp_all [inside, isBound, isEnd]
        rcases ha with rfl | rfl <;> rfl
    · simpa [List.filter, hb] using ht
  · rw [insideFor_concat]
    refine ⟨hc, fun ha => ?_⟩
    rw [← I.opn_iff]
    rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha', rfl⟩ <;>
      simp_all [isCallRet, opn]
    rcases ha' with rfl | rfl <;> simp_all [isCallRet]
  · rw [insideFor_concat]
    refine ⟨hx, fun ha => ?_⟩
    rw [← I.opn_iff]
    rcases step_eq_some.mp hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, ha', rfl⟩ <;>
      simp_all [isTxcommit, opn]
    rcases ha' with rfl | rfl <;> simp_all [isTxcommit]

/-- **Characterization of (repaired) Definition 2 by the per-thread automaton.** -/
theorem wfThread_iff_run (l : List (IKind O M)) : WFThread l ↔ (run idle l).isSome := by
  induction l using List.reverseRecOn with
  | nil => simp [WFThread, WFThreadLit, ReqResp, TxAlt, InsideFor]
  | append_singleton l a ih =>
    rw [run_concat]
    constructor
    · intro hw
      have hl : WFThread l := by
        obtain ⟨⟨hr, ht, hc⟩, hx⟩ := hw
        refine ⟨⟨((reqResp_concat _ _).mp hr).1, ?_, ((insideFor_concat _ _ _).mp hc).1⟩,
          ((insideFor_concat _ _ _).mp hx).1⟩
        rw [List.filter_append] at ht
        by_cases hb : a.isBound
        · simp only [List.filter, hb] at ht; exact ((txAlt_concat _ _).mp ht).1
        · simpa [List.filter, hb] using ht
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (ih.mp hl)
      rw [hq]
      exact step_isSome_of (runInv_of_run l q hq) hw
    · intro h
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨q, hq, hs⟩ := Option.bind_eq_some_iff.mp hq'
      exact wfThread_concat_of_step (runInv_of_run l q hq) (ih.mpr (by simp [hq])) hs

/-- The repaired well-formedness of a history, via the automaton. -/
theorem wellFormed_iff_run [DecidableEq T] (H : List (IAct T O M)) :
    WellFormed H ↔ ∀ t, (run idle (proj t H)).isSome :=
  forall_congr' fun t => wfThread_iff_run _

lemma WellFormed.toLit [DecidableEq T] {H : List (IAct T O M)} (h : WellFormed H) :
    WellFormedLit H := fun t => (h t).1

end Podc.TMObservationalRefinement
