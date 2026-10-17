import Papers.PODC2026.EarlyStabilizingCounting.Basic
import Podc.Agreement.PhaseKing

/-!
# Communication-efficient King Consensus (Section 6.1: Lemmas 6.2, 6.4, Theorem 6.5)

One instance of each of the three fixed-round algorithms of [LL26, Section 6.1]:

* Algorithm 2, *weak graded agreement* (Definition 6.1, Lemma 6.2), 2 rounds;
* Algorithm 3, *graded king consensus* (Definition 6.3, Lemma 6.4), 4 rounds;
* Algorithm 4, *King Consensus with improved bit complexity* (Theorem 6.5), 8 rounds:
  Algorithm 3, a "runGC" round, Algorithm 2 with `s_v := [received runGC from ℓ_v ≠ ⊥]`, and
  a final round in which the leader sends its value.

## Model

Synchronous rounds on the node set `Fin n`, faulty set `F` with `3 |F| < n`; values are natural
numbers. Unlike the state-broadcast form of `KingConsensus.lean`, in every round a correct node `u`
computes, from its local state (inputs and all vectors received so far), a message
`m u w : Option Msg` *for every receiver `w`*; `none` means that nothing is sent. A correct
receiver `v` sees a vector `r v : Fin n → Option Msg` with `r v u = m u v` for correct `u`
(`Consistent`), and arbitrary entries for faulty `u` (faulty nodes may send anything, including
`nack`/`runGC` where a value is expected, or nothing). "Received `k` times `x`" counts distinct
senders. An execution (`WGARun`, `GKCRun`, `KC8Run`) is the inputs of all nodes together with the
received vectors of all rounds, subject to consistency for every round; the outputs of correct
nodes are explicit functions of their inputs and received vectors.

Messages are `Msg.val x` (a value), `Msg.nack` (Algorithm 2, line 3) and `Msg.runGC`
(Algorithm 4, line 2). "Break ties arbitrarily" (Algorithm 2 line 5, Algorithm 3 line 8) is
resolved by taking the value of the smallest sender whose value was received more than `t` times
(`bigVal`). In Algorithm 2 "messages different from `x_v`" are received messages (not `⊥`) other
than `val x_v`; a `nack` counts as different. In Algorithm 4 line 8, "received `z_{ℓ_v}` from
`ℓ_v`" means receiving a value message from `ℓ_v`.

## Main results

* `wga_silent`, `WGARun.spec` — Lemma 6.2 (`WGASpec` = Definition 6.1).
* `GKCRun.spec`, `GKCRun.sparse` — Lemma 6.4 (`GKCSpec` = Definition 6.3, communication).
* `KC8Run.spec`, `KC8Run.sparse`, `KC8Run.card_sent_le` — Theorem 6.5 (`KCSpec` = Definition 2.6,
  communication: under the hypothesis of the theorem every message of a correct node in each of
  the 8 rounds is sent by `ℓ`, to `ℓ`, or to a faulty node, hence at most `n (|F| + 2)` messages
  per round).

No error was found: all claims of Section 6.1 hold as stated (the paper's proof of weak graded
agreement even takes a detour through a node `u₀` that is not needed).
-/

set_option linter.unusedSectionVars false

namespace EarlyStabilizingCounting

namespace KC8

open Finset

/-- Messages of Section 6.1: a value, a `NACK` (Algorithm 2), or `runGC` (Algorithm 4). -/
inductive Msg where
  | val (a : ℕ)
  | nack
  | runGC
  deriving DecidableEq

variable {n : ℕ}

/-! ### Executions, consistency, and sparse communication -/

/-- The received vectors `r v` (receiver `v`, sender `u`) of the correct receivers agree with the
messages `m u v` of the correct senders. -/
def Consistent (F : Finset (Fin n)) (r m : Fin n → Fin n → Option Msg) : Prop :=
  ∀ v u, v ∉ F → u ∉ F → r v u = m u v

theorem Consistent.agree {F : Finset (Fin n)} {r m : Fin n → Fin n → Option Msg}
    (h : Consistent F r m) {v : Fin n} (hv : v ∉ F) : Agree F (r v) (fun u => m u v) :=
  fun u hu => h v u hv hu

/-- Communication pattern of Lemma 6.4 / Theorem 6.5: every message `m u w ≠ ⊥` of a correct node
`u` is sent by the leader `ℓ`, or to the leader `ℓ`, or to a faulty node. -/
def Sparse (F : Finset (Fin n)) (ℓ : Option (Fin n)) (m : Fin n → Fin n → Option Msg) : Prop :=
  ∀ u w, u ∉ F → m u w ≠ none → ℓ = some u ∨ ℓ = some w ∨ w ∈ F

/-- The (sender, receiver) pairs of the messages sent by correct nodes in a round. -/
def sent (F : Finset (Fin n)) (m : Fin n → Fin n → Option Msg) : Finset (Fin n × Fin n) :=
  univ.filter fun p => p.1 ∉ F ∧ m p.1 p.2 ≠ none

/-- A sparse round has at most `n (|F| + 2)` messages sent by correct nodes. -/
theorem Sparse.card_sent_le {F : Finset (Fin n)} {ℓ : Option (Fin n)}
    {m : Fin n → Fin n → Option Msg} (h : Sparse F ℓ m) : (sent F m).card ≤ n * (F.card + 2) := by
  have hsub : sent F m ⊆ (univ ×ˢ F) ∪ ((univ.filter fun p : Fin n × Fin n => ℓ = some p.1) ∪
      (univ.filter fun p : Fin n × Fin n => ℓ = some p.2)) := by
    intro p hp
    simp only [sent, mem_filter, mem_univ, true_and] at hp
    simp only [mem_union, mem_product, mem_univ, true_and, mem_filter]
    rcases h p.1 p.2 hp.1 hp.2 with h1 | h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl h1
  have h1 : (univ.filter fun p : Fin n × Fin n => ℓ = some p.1).card ≤ n := by
    rcases ℓ with _ | a
    · simp
    · calc _ ≤ ({a} ×ˢ (univ : Finset (Fin n))).card := card_le_card fun p hp => by
            simp only [mem_filter, mem_univ, true_and, Option.some.injEq] at hp
            simp [hp]
        _ = n := by simp
  have h2 : (univ.filter fun p : Fin n × Fin n => ℓ = some p.2).card ≤ n := by
    rcases ℓ with _ | a
    · simp
    · calc _ ≤ ((univ : Finset (Fin n)) ×ˢ {a}).card := card_le_card fun p hp => by
            simp only [mem_filter, mem_univ, true_and, Option.some.injEq] at hp
            simp [hp]
        _ = n := by simp
  have h3 : ((univ : Finset (Fin n)) ×ˢ F).card = n * F.card := by simp [card_product]
  have h4 := card_le_card hsub
  have h5 := card_union_le ((univ : Finset (Fin n)) ×ˢ F) ((univ.filter fun p : Fin n × Fin n => ℓ = some p.1) ∪
      (univ.filter fun p : Fin n × Fin n => ℓ = some p.2))
  have h6 := card_union_le (univ.filter fun p : Fin n × Fin n => ℓ = some p.1)
      (univ.filter fun p : Fin n × Fin n => ℓ = some p.2)
  have h7 : n * (F.card + 2) = n * F.card + n + n := by ring
  omega

/-! ### Counting received messages -/

/-- Number of senders whose received entry satisfies `P`. -/
def pcnt {α : Type*} (s : Fin n → α) (P : α → Prop) [DecidablePred P] : ℕ :=
  (univ.filter fun w => P (s w)).card

theorem pcnt_ge {α : Type*} {F : Finset (Fin n)} {r m : Fin n → α} (h : Agree F r m)
    (P : α → Prop) [DecidablePred P] (A : Finset (Fin n)) (hA : ∀ u ∈ A, u ∉ F ∧ P (m u)) :
    A.card ≤ pcnt r P :=
  card_le_card fun u hu => by
    simp only [mem_filter, mem_univ, true_and]
    rw [h u (hA u hu).1]; exact (hA u hu).2

theorem pcnt_le_add {α : Type*} {F : Finset (Fin n)} {r m : Fin n → α} (h : Agree F r m)
    (P : α → Prop) [DecidablePred P] (A : Finset (Fin n)) (hA : ∀ u, u ∉ F → P (m u) → u ∈ A) :
    pcnt r P ≤ A.card + F.card := by
  refine (card_le_card fun u hu => ?_).trans (card_union_le A F)
  simp only [mem_filter, mem_univ, true_and] at hu
  rw [mem_union]
  by_cases huF : u ∈ F
  · exact Or.inr huF
  · rw [h u huF] at hu; exact Or.inl (hA u huF hu)

theorem pcnt_le_of {α : Type*} {F : Finset (Fin n)} {r m : Fin n → α} (h : Agree F r m)
    (P : α → Prop) [DecidablePred P] (hm : ∀ u, u ∉ F → ¬ P (m u)) : pcnt r P ≤ F.card := by
  have := pcnt_le_add h P ∅ fun u hu hP => absurd hP (hm u hu)
  simpa using this

theorem cnt_ge {α : Type*} [DecidableEq α] {F : Finset (Fin n)} {r m : Fin n → α}
    (h : Agree F r m) (a : α) (A : Finset (Fin n)) (hA : ∀ u ∈ A, u ∉ F ∧ m u = a) :
    A.card ≤ cnt r a :=
  pcnt_ge h (· = a) A hA

theorem cnt_le_add {α : Type*} [DecidableEq α] {F : Finset (Fin n)} {r m : Fin n → α}
    (h : Agree F r m) (a : α) (A : Finset (Fin n)) (hA : ∀ u, u ∉ F → m u = a → u ∈ A) :
    cnt r a ≤ A.card + F.card :=
  pcnt_le_add h (· = a) A hA

theorem cnt_le_of {α : Type*} [DecidableEq α] {F : Finset (Fin n)} {r m : Fin n → α}
    (h : Agree F r m) (a : α) (hm : ∀ u, u ∉ F → m u ≠ a) : cnt r a ≤ F.card :=
  pcnt_le_of h (· = a) hm

/-- Number of received messages different from `val x` (`⊥` is not a message; `nack` and
`runGC` are different from `val x`). -/
def diffCnt (r : Fin n → Option Msg) (x : ℕ) : ℕ :=
  pcnt r fun o => o ≠ none ∧ o ≠ some (.val x)

theorem diffCnt_le_of {F : Finset (Fin n)} {r m : Fin n → Option Msg} (h : Agree F r m) (c : ℕ)
    (hm : ∀ u, u ∉ F → m u = none ∨ m u = some (.val c)) : diffCnt r c ≤ F.card :=
  pcnt_le_of h _ fun u hu hP => by
    rcases hm u hu with h' | h' <;> simp_all

/-- Candidate of sender `w` for "received more than `t` times `a`": `a` if `w` sent `val a` and
`val a` was received at least `t + 1` times. -/
def bigSel (r : Fin n → Option Msg) (w : Fin n) : Option ℕ :=
  match r w with
  | some (.val a) => if res n + 1 ≤ cnt r (some (.val a)) then some a else none
  | _ => none

/-- A value received more than `t` times, ties broken by the smallest sender (`none` if there is
no such value). -/
def bigVal (r : Fin n → Option Msg) : Option ℕ := (List.finRange n).findSome? (bigSel r)

theorem bigSel_eq_some {r : Fin n → Option Msg} {w : Fin n} {a : ℕ} (h : bigSel r w = some a) :
    r w = some (.val a) ∧ res n + 1 ≤ cnt r (some (.val a)) := by
  unfold bigSel at h
  split at h
  next b hb =>
    split_ifs at h with h1
    cases h
    exact ⟨hb, h1⟩
  next => simp at h

theorem bigVal_cases {r : Fin n → Option Msg} {a : ℕ}
    (hlow : ∀ b, b ≠ a → cnt r (some (.val b)) ≤ res n) :
    bigVal r = none ∨ bigVal r = some a := by
  rcases h : bigVal r with _ | b
  · exact Or.inl rfl
  · right
    obtain ⟨w, -, hw⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨-, hc⟩ := bigSel_eq_some hw
    by_contra hne
    have := hlow b (fun e => hne (by rw [e]))
    omega

theorem bigVal_eq {r : Fin n → Option Msg} {a : ℕ}
    (hlow : ∀ b, b ≠ a → cnt r (some (.val b)) ≤ res n)
    (hy : res n + 1 ≤ cnt r (some (.val a))) : bigVal r = some a := by
  rcases bigVal_cases hlow with h | h
  · exfalso
    rw [bigVal, List.findSome?_eq_none_iff] at h
    obtain ⟨w, hw⟩ : ∃ w, r w = some (.val a) := by
      have : 0 < cnt r (some (.val a)) := by omega
      obtain ⟨w, -, hw⟩ := exists_mem_of_countEq_pos this
      exact ⟨w, hw⟩
    have := h w (List.mem_finRange w)
    simp [bigSel, hw, hy] at this
  · exact h

/-- If no value other than `a` is received more than `t` times, and either the default is `a` or
`a` is received more than `t` times, the selected value is `a`. -/
theorem bigVal_getD {r : Fin n → Option Msg} {a x : ℕ}
    (hlow : ∀ b, b ≠ a → cnt r (some (.val b)) ≤ res n)
    (h : x = a ∨ res n + 1 ≤ cnt r (some (.val a))) : (bigVal r).getD x = a := by
  rcases h with rfl | hy
  · rcases bigVal_cases hlow with h | h <;> simp [h]
  · rw [bigVal_eq hlow hy]; rfl

/-! ### Algorithm 2: weak graded agreement (Definition 6.1, Lemma 6.2) -/

/-- Algorithm 2, line 1 (first round): send `x_v` to all nodes iff `s_v = 1`. -/
def wga1 (x : ℕ) (s : Bool) : Option Msg := if s then some (.val x) else none

/-- Algorithm 2, lines 2–3 (second round), from the first-round vector `r1`. -/
def wga2 (x : ℕ) (s : Bool) (r1 : Fin n → Option Msg) : Option Msg :=
  if s then (if diffCnt r1 x ≤ res n then some (.val x) else some .nack) else none

/-- Algorithm 2, lines 4–6: output `(y_v, g_v)` from the second-round vector `r2`. -/
def wgaOut (x : ℕ) (r2 : Fin n → Option Msg) : ℕ × Bool :=
  if diffCnt r2 x ≤ res n then (x, true) else ((bigVal r2).getD x, false)

/-- An execution of Algorithm 2: inputs `(x_v, s_v)` and the received vectors of both rounds. -/
structure WGARun (F : Finset (Fin n)) where
  /-- value inputs -/
  x : Fin n → ℕ
  /-- participation bits -/
  s : Fin n → Bool
  /-- first-round receptions (`r1 v u`: what `v` received from `u`) -/
  r1 : Fin n → Fin n → Option Msg
  /-- second-round receptions -/
  r2 : Fin n → Fin n → Option Msg
  h1 : Consistent F r1 fun u _ => wga1 (x u) (s u)
  h2 : Consistent F r2 fun u _ => wga2 (x u) (s u) (r1 u)

/-- Output value of Algorithm 2. -/
def WGARun.y {F : Finset (Fin n)} (E : WGARun F) (v : Fin n) : ℕ := (wgaOut (E.x v) (E.r2 v)).1

/-- Output grade of Algorithm 2. -/
def WGARun.g {F : Finset (Fin n)} (E : WGARun F) (v : Fin n) : Bool :=
  (wgaOut (E.x v) (E.r2 v)).2

/-- Definition 6.1 (Weak Graded Agreement), for the inputs and outputs of the correct nodes. -/
structure WGASpec (F : Finset (Fin n)) (x : Fin n → ℕ) (s : Fin n → Bool) (y : Fin n → ℕ)
    (g : Fin n → Bool) : Prop where
  /-- Validity: equal correct inputs `x` give output `(x, 1)` at every correct node. -/
  validity : ∀ c, (∀ v, v ∉ F → x v = c) → ∀ v, v ∉ F → y v = c ∧ g v = true
  /-- Weak graded agreement: if all correct `s_v = 1` and a correct `w` has grade 1, all correct
  nodes output `y_w`. -/
  weak_agreement : (∀ v, v ∉ F → s v = true) → ∀ w, w ∉ F → g w = true →
    ∀ v, v ∉ F → y v = y w

/-- Lemma 6.2 (communication): a node with `s_v = 0` sends no message in either round. -/
theorem wga_silent (x : ℕ) (r1 : Fin n → Option Msg) :
    wga1 x false = none ∧ wga2 x false r1 = none := by
  simp [wga1, wga2]

theorem wgaOut_g {x : ℕ} {r : Fin n → Option Msg} :
    (wgaOut x r).2 = true ↔ diffCnt r x ≤ res n := by
  unfold wgaOut; split_ifs with h <;> simp [h]

/-- Lemma 6.2 (correctness of Algorithm 2): validity and weak graded agreement. -/
theorem WGARun.spec {F : Finset (Fin n)} (E : WGARun F) (hF : 3 * F.card < n) :
    WGASpec F E.x E.s E.y E.g := by
  have ht := card_le_res hF
  have hn : 3 * res n < n := by unfold res; omega
  refine ⟨fun c hc v hv => ?_, fun hs w hw hg v hv => ?_⟩
  · -- validity
    have h1 : ∀ u, u ∉ F → diffCnt (E.r1 u) c ≤ res n := fun u hu =>
      (diffCnt_le_of (E.h1.agree hu) c fun w hw => by
        cases h : E.s w <;> simp [wga1, hc w hw]).trans ht
    have h2 : ∀ u, u ∉ F → wga2 (E.x u) (E.s u) (E.r1 u) = none ∨
        wga2 (E.x u) (E.s u) (E.r1 u) = some (.val c) := fun u hu => by
      rw [hc u hu]; cases h : E.s u <;> simp [wga2, h1 u hu]
    have h3 : diffCnt (E.r2 v) (E.x v) ≤ res n := by
      rw [hc v hv]; exact (diffCnt_le_of (E.h2.agree hv) c h2).trans ht
    rw [hc v hv] at h3
    simp [WGARun.y, WGARun.g, wgaOut, h3, hc v hv]
  · -- weak graded agreement
    have hgw : diffCnt (E.r2 w) (E.x w) ≤ res n := wgaOut_g.mp hg
    have hyw : E.y w = E.x w := by simp only [WGARun.y, wgaOut, hgw, ite_true]
    set a := E.x w with ha
    have hm2 : ∀ u, u ∉ F → wga2 (E.x u) (E.s u) (E.r1 u) =
        if diffCnt (E.r1 u) (E.x u) ≤ res n then some (.val (E.x u)) else some .nack :=
      fun u hu => by simp [wga2, hs u hu]
    -- `A`: correct nodes sending `val a` in the second round
    set C := univ.filter fun u : Fin n => u ∉ F with hC
    set A := C.filter fun u => diffCnt (E.r1 u) (E.x u) ≤ res n ∧ E.x u = a with hA
    set D := C.filter fun u => ¬ (diffCnt (E.r1 u) (E.x u) ≤ res n ∧ E.x u = a) with hD
    have hAD : A.card + D.card = n - F.card := by
      rw [hA, hD, card_filter_add_card_filter_not, hC, card_correct]
    have hDle : D.card ≤ res n := by
      refine (pcnt_ge (E.h2.agree hw) _ D fun u hu => ?_).trans hgw
      simp only [hD, hC, mem_filter, mem_univ, true_and] at hu
      refine ⟨hu.1, ?_⟩
      simp only [hm2 u hu.1]
      split_ifs with h
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, Msg.val.injEq,
          true_and]
        exact fun e => hu.2 ⟨h, e⟩
      · simp
    have hAbig : res n + 1 ≤ A.card := by omega
    have hAmem : ∀ u ∈ A, u ∉ F ∧ diffCnt (E.r1 u) (E.x u) ≤ res n ∧ E.x u = a := by
      intro u hu
      simpa only [hA, hC, mem_filter, mem_univ, true_and] using hu
    -- correct nodes with a different value send `nack`
    have hok : ∀ v, v ∉ F → diffCnt (E.r1 v) (E.x v) ≤ res n → E.x v = a := by
      intro v hv hle
      by_contra hne
      have : A.card ≤ diffCnt (E.r1 v) (E.x v) := pcnt_ge (E.h1.agree hv) _ A fun u hu => by
        obtain ⟨hu1, -, hu3⟩ := hAmem u hu
        refine ⟨hu1, ?_⟩
        simp only [wga1, hs u hu1, hu3, ite_true]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, Msg.val.injEq,
          true_and]
        exact fun e => hne e.symm
      omega
    have hmsg : ∀ u, u ∉ F → wga2 (E.x u) (E.s u) (E.r1 u) = some (.val a) ∨
        wga2 (E.x u) (E.s u) (E.r1 u) = some .nack := fun u hu => by
      rw [hm2 u hu]
      split_ifs with h
      · exact Or.inl (by rw [hok u hu h])
      · exact Or.inr rfl
    have hlow : ∀ b, b ≠ a → cnt (E.r2 v) (some (.val b)) ≤ res n := fun b hb =>
      (cnt_le_of (E.h2.agree hv) _ fun u hu => by
        rcases hmsg u hu with h | h <;> simp [h, Ne.symm hb]).trans ht
    have hAge : ∀ v, v ∉ F → A.card ≤ cnt (E.r2 v) (some (.val a)) := fun v hv =>
      cnt_ge (E.h2.agree hv) _ A fun u hu => by
        obtain ⟨hu1, hu2, hu3⟩ := hAmem u hu
        refine ⟨hu1, ?_⟩
        show wga2 (E.x u) (E.s u) (E.r1 u) = some (.val a)
        rw [hm2 u hu1, ite_eq_left hu2, hu3]
    have hyv : E.y v = a := by
      simp only [WGARun.y, wgaOut]
      split_ifs with h
      · by_contra hne
        have : A.card ≤ diffCnt (E.r2 v) (E.x v) := pcnt_ge (E.h2.agree hv) _ A fun u hu => by
          obtain ⟨hu1, hu2, hu3⟩ := hAmem u hu
          refine ⟨hu1, ?_⟩
          show wga2 (E.x u) (E.s u) (E.r1 u) ≠ none ∧ wga2 (E.x u) (E.s u) (E.r1 u) ≠ some _
          rw [hm2 u hu1, ite_eq_left hu2, hu3]
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, Msg.val.injEq,
            true_and]
          exact fun e => hne e.symm
        omega
      · exact bigVal_getD hlow (Or.inr ((hAbig.trans (hAge v hv))))
    rw [hyv, hyw]

/-! ### Algorithm 3: graded king consensus (Definition 6.3, Lemma 6.4) -/

/-- Algorithm 3, line 1 (first round): send `x_v` to `ℓ_v` (if `ℓ_v ≠ ⊥`); `w` is the receiver. -/
def gkc1 (x : ℕ) (l : Option (Fin n)) (w : Fin n) : Option Msg :=
  if l = some w then some (.val x) else none

/-- Algorithm 3, lines 2–5: the grade of node `u`: `u` is its own leader and received `x_u` at
least `n - t` times in the first round. -/
def gkcGrade (u : Fin n) (x : ℕ) (l : Option (Fin n)) (r1 : Fin n → Option Msg) : Bool :=
  decide (l = some u ∧ n - res n ≤ cnt r1 (some (.val x)))

/-- Algorithm 3, line 3 (second round): a leader with grade 1 sends `x_v` to all nodes. -/
def gkc2 (u : Fin n) (x : ℕ) (l : Option (Fin n)) (r1 : Fin n → Option Msg) (_w : Fin n) :
    Option Msg :=
  if gkcGrade u x l r1 then some (.val x) else none

/-- Algorithm 3, line 6: the value `x_{ℓ_v} ≠ x_v` received from `ℓ_v ≠ ⊥` in the second round,
if any. -/
def gkcAdv (x : ℕ) (l : Option (Fin n)) (r2 : Fin n → Option Msg) : Option ℕ :=
  match l with
  | none => none
  | some ℓ =>
    match r2 ℓ with
    | some (.val b) => if b = x then none else some b
    | _ => none

/-- Algorithm 3, line 6 (third round): forward the leader's differing value to all nodes. -/
def gkc3 (x : ℕ) (l : Option (Fin n)) (r2 : Fin n → Option Msg) (_w : Fin n) : Option Msg :=
  (gkcAdv x l r2).map .val

/-- Algorithm 3, line 7 (fourth round): answer `x_v` to every `w` from which `x_v` was received
in the third round. -/
def gkc4 (x : ℕ) (r3 : Fin n → Option Msg) (w : Fin n) : Option Msg :=
  if r3 w = some (.val x) then some (.val x) else none

/-- Algorithm 3, line 8: the output value, from the fourth-round vector. -/
def gkcVal (x : ℕ) (r4 : Fin n → Option Msg) : ℕ := (bigVal r4).getD x

/-- An execution of Algorithm 3: inputs `(x_v, ℓ_v)` and the received vectors of the 4 rounds. -/
structure GKCRun (F : Finset (Fin n)) where
  /-- value inputs -/
  x : Fin n → ℕ
  /-- leader inputs (`none` = `⊥`) -/
  l : Fin n → Option (Fin n)
  /-- receptions of round 1 -/
  r1 : Fin n → Fin n → Option Msg
  /-- receptions of round 2 -/
  r2 : Fin n → Fin n → Option Msg
  /-- receptions of round 3 -/
  r3 : Fin n → Fin n → Option Msg
  /-- receptions of round 4 -/
  r4 : Fin n → Fin n → Option Msg
  h1 : Consistent F r1 fun u => gkc1 (x u) (l u)
  h2 : Consistent F r2 fun u => gkc2 u (x u) (l u) (r1 u)
  h3 : Consistent F r3 fun u => gkc3 (x u) (l u) (r2 u)
  h4 : Consistent F r4 fun u => gkc4 (x u) (r3 u)

namespace GKCRun

variable {F : Finset (Fin n)} (E : GKCRun F)

/-- Output value `y_v` of Algorithm 3. -/
def y (v : Fin n) : ℕ := gkcVal (E.x v) (E.r4 v)

/-- Output grade `g_v` of Algorithm 3. -/
def g (v : Fin n) : Bool := gkcGrade v (E.x v) (E.l v) (E.r1 v)

/-- Messages of correct nodes in round 1 (sender, receiver). -/
def m1 : Fin n → Fin n → Option Msg := fun u => gkc1 (E.x u) (E.l u)
/-- Messages of correct nodes in round 2. -/
def m2 : Fin n → Fin n → Option Msg := fun u => gkc2 u (E.x u) (E.l u) (E.r1 u)
/-- Messages of correct nodes in round 3. -/
def m3 : Fin n → Fin n → Option Msg := fun u => gkc3 (E.x u) (E.l u) (E.r2 u)
/-- Messages of correct nodes in round 4. -/
def m4 : Fin n → Fin n → Option Msg := fun u => gkc4 (E.x u) (E.r3 u)

end GKCRun

/-- Definition 6.3 (Graded King Consensus), for the inputs and outputs of the correct nodes. -/
structure GKCSpec (F : Finset (Fin n)) (x : Fin n → ℕ) (l : Fin n → Option (Fin n))
    (y : Fin n → ℕ) (g : Fin n → Bool) : Prop where
  /-- Validity: equal correct inputs `x` give output value `x` at every correct node. -/
  validity : ∀ c, (∀ v, v ∉ F → x v = c) → ∀ v, v ∉ F → y v = c
  /-- King validity: equal correct inputs `(x, ℓ)` with `ℓ` correct give `g_ℓ = 1`. -/
  king_validity : ∀ c ℓ, ℓ ∉ F → (∀ v, v ∉ F → x v = c ∧ l v = some ℓ) → g ℓ = true
  /-- Graded king agreement: if all correct nodes have the same correct leader `ℓ` and `g_ℓ = 1`,
  every correct node outputs `y_ℓ`. -/
  graded_king_agreement : ∀ ℓ, ℓ ∉ F → (∀ v, v ∉ F → l v = some ℓ) → g ℓ = true →
    ∀ v, v ∉ F → y v = y ℓ

/-- Lemma 6.4 (correctness of Algorithm 3): validity, king validity, graded king agreement. -/
theorem GKCRun.spec {F : Finset (Fin n)} (E : GKCRun F) (hF : 3 * F.card < n) :
    GKCSpec F E.x E.l E.y E.g := by
  have ht := card_le_res hF
  have hn : 3 * res n < n := by unfold res; omega
  refine ⟨fun c hc v hv => ?_, fun c ℓ hℓ hall => ?_, fun ℓ hℓ hall hg v hv => ?_⟩
  · -- validity
    have hlow : ∀ b, b ≠ c → cnt (E.r4 v) (some (.val b)) ≤ res n := fun b hb =>
      (cnt_le_of (E.h4.agree hv) _ fun u hu => by
        simp only [gkc4, hc u hu]
        split_ifs <;> simp [Ne.symm hb]).trans ht
    exact bigVal_getD hlow (Or.inl (hc v hv))
  · -- king validity
    simp only [GKCRun.g, gkcGrade, decide_eq_true_eq]
    refine ⟨(hall ℓ hℓ).2, ?_⟩
    rw [(hall ℓ hℓ).1]
    exact cnt_all hF (E.h1.agree hℓ) fun u hu => by simp [gkc1, hall u hu]
  · -- graded king agreement
    have hg' : E.l ℓ = some ℓ ∧ n - res n ≤ cnt (E.r1 ℓ) (some (.val (E.x ℓ))) := by
      simpa [GKCRun.g, gkcGrade] using hg
    have hg2 : gkcGrade ℓ (E.x ℓ) (E.l ℓ) (E.r1 ℓ) = true := hg
    have hr2 : ∀ v, v ∉ F → E.r2 v ℓ = some (.val (E.x ℓ)) := fun v hv => by
      rw [E.h2 v ℓ hv hℓ]; simp [gkc2, hg2]
    set a := E.x ℓ with ha
    set G := univ.filter fun u : Fin n => u ∉ F ∧ E.x u = a with hG
    have hGbig : n - res n ≤ G.card + F.card :=
      hg'.2.trans (cnt_le_add (E.h1.agree hℓ) _ G fun u hu hP => by
        simp [gkc1, hall u hu] at hP
        simp [hG, hu, hP])
    have hGt : res n + 1 ≤ G.card := by omega
    have hadv : ∀ v, v ∉ F → gkcAdv (E.x v) (E.l v) (E.r2 v) =
        if a = E.x v then none else some a := fun v hv => by
      rw [hall v hv]; simp only [gkcAdv, hr2 v hv]
    have hm4 : ∀ v w, v ∉ F → w ∉ F → gkc4 (E.x w) (E.r3 w) v =
        if E.x v ≠ a ∧ E.x w = a then some (.val a) else none := fun v w hv hw => by
      simp only [gkc4]
      rw [E.h3 w v hw hv]
      simp only [gkc3, hadv v hv]
      by_cases h1 : a = E.x v
      · simp [h1]
      · by_cases h2 : E.x w = a
        · simp [h1, h2, Ne.symm h1]
        · simp [h1, h2, Ne.symm h2]
    have hya : ∀ v, v ∉ F → E.y v = a := fun v hv => by
      have hlow : ∀ b, b ≠ a → cnt (E.r4 v) (some (.val b)) ≤ res n := fun b hb =>
        (cnt_le_of (E.h4.agree hv) _ fun u hu => by
          simp only [hm4 v u hv hu]
          split_ifs <;> simp [Ne.symm hb]).trans ht
      refine bigVal_getD hlow ?_
      by_cases h : E.x v = a
      · exact Or.inl h
      · refine Or.inr (hGt.trans (cnt_ge (E.h4.agree hv) _ G fun u hu => ?_))
        simp only [hG, mem_filter, mem_univ, true_and] at hu
        refine ⟨hu.1, ?_⟩
        show gkc4 (E.x u) (E.r3 u) v = _
        rw [hm4 v u hv hu.1]
        simp [h, hu.2]
    rw [hya v hv, hya ℓ hℓ]

/-- Lemma 6.4 (communication of Algorithm 3): if all correct nodes have the same input `(x, ℓ)`
with `ℓ = ⊥` or `ℓ` correct, then in each of the 4 rounds every message of a correct node is sent
by `ℓ`, to `ℓ`, or to a faulty node. -/
theorem GKCRun.sparse {F : Finset (Fin n)} (E : GKCRun F) (c : ℕ) (ℓo : Option (Fin n))
    (hall : ∀ v, v ∉ F → E.x v = c ∧ E.l v = ℓo) (hℓ : ∀ ℓ, ℓo = some ℓ → ℓ ∉ F) :
    Sparse F ℓo E.m1 ∧ Sparse F ℓo E.m2 ∧ Sparse F ℓo E.m3 ∧ Sparse F ℓo E.m4 := by
  have hadv : ∀ u, u ∉ F → gkcAdv (E.x u) (E.l u) (E.r2 u) = none := fun u hu => by
    rw [(hall u hu).2]
    rcases ℓo with _ | ℓ
    · rfl
    · have hℓF := hℓ ℓ rfl
      simp only [gkcAdv]
      rw [E.h2 u ℓ hu hℓF]
      simp only [gkc2]
      split_ifs
      · simp [(hall ℓ hℓF).1, (hall u hu).1]
      · rfl
  refine ⟨fun u w hu hne => ?_, fun u w hu hne => ?_, fun u w hu hne => ?_,
    fun u w hu hne => ?_⟩
  · right; left
    by_contra hcon
    apply hne
    simp only [GKCRun.m1, gkc1]
    rw [ite_eq_right]
    rw [(hall u hu).2]; exact hcon
  · left
    by_contra hcon
    apply hne
    have hg : gkcGrade u (E.x u) (E.l u) (E.r1 u) = false := by
      simp only [gkcGrade, decide_eq_false_iff_not, not_and]
      intro h1
      exact absurd ((hall u hu).2.symm.trans h1) hcon
    simp [GKCRun.m2, gkc2, hg]
  · exact absurd (by simp [GKCRun.m3, gkc3, hadv u hu]) hne
  · right; right
    by_contra hwF
    apply hne
    simp only [GKCRun.m4, gkc4]
    rw [E.h3 u w hu hwF]
    simp [gkc3, hadv w hwF]

/-! ### Algorithm 4: King Consensus in 8 rounds (Theorem 6.5) -/

/-- Algorithm 4, line 2 (fifth round): a leader with graded-king-consensus grade `h = 0` sends
`runGC` to all nodes. -/
def kc5 (u : Fin n) (l : Option (Fin n)) (h : Bool) (_w : Fin n) : Option Msg :=
  if l = some u ∧ h = false then some .runGC else none

/-- Algorithm 4, line 3: the participation bit `s_v` of weak graded agreement: received `runGC`
from `ℓ_v ≠ ⊥` in the fifth round. -/
def kcS (l : Option (Fin n)) (r5 : Fin n → Option Msg) : Bool :=
  match l with
  | none => false
  | some ℓ => decide (r5 ℓ = some .runGC)

/-- Algorithm 4, line 6 (eighth round): the leader sends its value `z_v` to all nodes. -/
def kc8 (u : Fin n) (l : Option (Fin n)) (z : ℕ) (_w : Fin n) : Option Msg :=
  if l = some u then some (.val z) else none

/-- Algorithm 4, lines 7–9: the output, from `ℓ_v`, the weak graded agreement output `(z_v, g_v)`
and the eighth-round vector. -/
def kc8Out (l : Option (Fin n)) (z : ℕ) (g : Bool) (r8 : Fin n → Option Msg) : Option ℕ :=
  match l with
  | none => none
  | some ℓ =>
    if g then some z else
      match r8 ℓ with
      | some (.val a) => some a
      | _ => some z

/-- An execution of Algorithm 4: an execution of Algorithm 3 (rounds 1–4) followed by the
receptions of rounds 5–8. -/
structure KC8Run (F : Finset (Fin n)) extends GKCRun F where
  /-- receptions of round 5 (`runGC`) -/
  r5 : Fin n → Fin n → Option Msg
  /-- receptions of round 6 (first round of Algorithm 2) -/
  r6 : Fin n → Fin n → Option Msg
  /-- receptions of round 7 (second round of Algorithm 2) -/
  r7 : Fin n → Fin n → Option Msg
  /-- receptions of round 8 (leader's value) -/
  r8 : Fin n → Fin n → Option Msg
  h5 : Consistent F r5 fun u => kc5 u (l u) (gkcGrade u (x u) (l u) (r1 u))
  h6 : Consistent F r6 fun u _ => wga1 (gkcVal (x u) (r4 u)) (kcS (l u) (r5 u))
  h7 : Consistent F r7 fun u _ => wga2 (gkcVal (x u) (r4 u)) (kcS (l u) (r5 u)) (r6 u)
  h8 : Consistent F r8 fun u => kc8 u (l u) (wgaOut (gkcVal (x u) (r4 u)) (r7 u)).1

namespace KC8Run

variable {F : Finset (Fin n)} (E : KC8Run F)

/-- Output value `k_v` of graded king consensus (Algorithm 4, line 1). -/
def k (u : Fin n) : ℕ := E.toGKCRun.y u

/-- Output grade `h_v` of graded king consensus (Algorithm 4, line 1). -/
def h (u : Fin n) : Bool := E.toGKCRun.g u

/-- Participation bit `s_v` (Algorithm 4, lines 3–5). -/
def s (u : Fin n) : Bool := kcS (E.l u) (E.r5 u)

/-- The embedded execution of Algorithm 2 (rounds 6–7) with inputs `(k_v, s_v)`. -/
def wga : WGARun F := ⟨E.k, E.s, E.r6, E.r7, E.h6, E.h7⟩

/-- Output value `z_v` of weak graded agreement. -/
def z (u : Fin n) : ℕ := E.wga.y u

/-- Output grade `g_v` of weak graded agreement. -/
def g (u : Fin n) : Bool := E.wga.g u

/-- Output `y_v` of Algorithm 4. -/
def y (u : Fin n) : Option ℕ := kc8Out (E.l u) (E.z u) (E.g u) (E.r8 u)

/-- Messages of correct nodes in round 5. -/
def m5 : Fin n → Fin n → Option Msg := fun u => kc5 u (E.l u) (E.h u)
/-- Messages of correct nodes in round 6. -/
def m6 : Fin n → Fin n → Option Msg := fun u _ => wga1 (E.k u) (E.s u)
/-- Messages of correct nodes in round 7. -/
def m7 : Fin n → Fin n → Option Msg := fun u _ => wga2 (E.k u) (E.s u) (E.r6 u)
/-- Messages of correct nodes in round 8. -/
def m8 : Fin n → Fin n → Option Msg := fun u => kc8 u (E.l u) (E.z u)

end KC8Run

/-- Theorem 6.5 (correctness of Algorithm 4): one instance solves King Consensus
(Definition 2.6). -/
theorem KC8Run.spec {F : Finset (Fin n)} (E : KC8Run F) (hF : 3 * F.card < n) :
    KCSpec F E.x E.l E.y := by
  have hG := E.toGKCRun.spec hF
  have hW := E.wga.spec hF
  refine ⟨fun c hc v hv => ?_, fun hnone v hv => ?_, fun ℓ hℓ hlead => ?_⟩
  · -- validity
    have hk : ∀ u, u ∉ F → E.k u = c := hG.validity c hc
    obtain ⟨hz, hg⟩ := hW.validity c hk v hv
    have hz' : E.z v = c := hz
    have hg' : E.g v = true := hg
    simp only [KC8Run.y, kc8Out]
    cases E.l v <;> simp [hz', hg']
  · -- default
    simp [KC8Run.y, kc8Out, hnone v hv]
  · -- king agreement
    have hr8 : ∀ v, v ∉ F → E.r8 v ℓ = some (.val (E.z ℓ)) := fun v hv => by
      rw [E.h8 v ℓ hv hℓ]
      simp only [kc8, hlead ℓ hℓ, ite_true]
      rfl
    have hy : ∀ v, v ∉ F → E.y v = some (if E.g v then E.z v else E.z ℓ) := fun v hv => by
      simp only [KC8Run.y, kc8Out, hlead v hv]
      cases E.g v <;> simp [hr8 v hv]
    have hagree : ∀ v, v ∉ F → E.g v = true → E.z v = E.z ℓ := by
      cases hgℓ : E.h ℓ
      · -- `h_ℓ = 0`: the leader sends `runGC`, all correct nodes run weak graded agreement
        have hgℓ' : gkcGrade ℓ (E.x ℓ) (E.l ℓ) (E.r1 ℓ) = false := hgℓ
        have hs : ∀ v, v ∉ F → E.wga.s v = true := fun v hv => by
          change kcS (E.l v) (E.r5 v) = true
          simp only [hlead v hv, kcS, decide_eq_true_eq]
          rw [E.h5 v ℓ hv hℓ]
          have hlℓ := hlead ℓ hℓ
          rw [hlℓ] at hgℓ'
          simp [kc5, hlℓ, hgℓ']
        exact fun v hv hgv => (hW.weak_agreement hs v hv hgv ℓ hℓ).symm
      · -- `h_ℓ = 1`: graded king agreement, then validity of weak graded agreement
        have hk : ∀ v, v ∉ F → E.k v = E.k ℓ := hG.graded_king_agreement ℓ hℓ hlead hgℓ
        exact fun v hv _ => (hW.validity _ hk v hv).1.trans (hW.validity _ hk ℓ hℓ).1.symm
    have hyℓ : E.y ℓ = some (E.z ℓ) := by rw [hy ℓ hℓ, ite_self]
    refine ⟨by simp [hyℓ], fun v hv => hyℓ ▸ ?_⟩
    -- the king step (line 8, `Cslib.Byzantine.kingPhase_agreement`)
    exact Cslib.Byzantine.kingPhase_agreement (H := (F : Set (Fin n))ᶜ) (val := E.z)
      (strong := fun v => E.g v = true) (out := E.y) (keep := some) (adopt := some)
      (fun w hw hg => (hagree w hw hg).symm) (fun w hw hg => by rw [hy w hw, ite_eq_left hg])
      (fun w hw hg => by rw [hy w hw, ite_eq_right hg]) (fun _ _ _ => rfl) v hv

/-- Theorem 6.5 (communication of Algorithm 4): if all correct nodes have the same input `(x, ℓ)`
with `ℓ = ⊥` or `ℓ` correct, then in each of the 8 rounds every message of a correct node is sent
by `ℓ`, to `ℓ`, or to a faulty node. -/
theorem KC8Run.sparse {F : Finset (Fin n)} (E : KC8Run F) (hF : 3 * F.card < n) (c : ℕ)
    (ℓo : Option (Fin n)) (hall : ∀ v, v ∉ F → E.x v = c ∧ E.l v = ℓo)
    (hℓ : ∀ ℓ, ℓo = some ℓ → ℓ ∉ F) :
    Sparse F ℓo E.m1 ∧ Sparse F ℓo E.m2 ∧ Sparse F ℓo E.m3 ∧ Sparse F ℓo E.m4 ∧
      Sparse F ℓo E.m5 ∧ Sparse F ℓo E.m6 ∧ Sparse F ℓo E.m7 ∧ Sparse F ℓo E.m8 := by
  obtain ⟨s1, s2, s3, s4⟩ := E.toGKCRun.sparse c ℓo hall hℓ
  -- nobody runs weak graded agreement: `ℓ` has grade 1 by king validity
  have hs : ∀ u, u ∉ F → E.s u = false := fun u hu => by
    simp only [KC8Run.s, (hall u hu).2]
    rcases ℓo with _ | ℓ
    · rfl
    · have hℓF := hℓ ℓ rfl
      have hg : gkcGrade ℓ (E.x ℓ) (E.l ℓ) (E.r1 ℓ) = true :=
        (E.toGKCRun.spec hF).king_validity c ℓ hℓF fun v hv =>
          ⟨(hall v hv).1, (hall v hv).2⟩
      simp only [kcS, decide_eq_false_iff_not]
      rw [E.h5 u ℓ hu hℓF]
      simp [kc5, hg]
  refine ⟨s1, s2, s3, s4, fun u w hu hne => ?_, fun u w hu hne => ?_, fun u w hu hne => ?_,
    fun u w hu hne => ?_⟩
  · left
    by_contra hcon
    apply hne
    simp only [KC8Run.m5, kc5]
    rw [ite_eq_right]
    rintro ⟨h1, -⟩
    exact hcon ((hall u hu).2.symm.trans h1)
  · exact absurd (by simp [KC8Run.m6, wga1, hs u hu]) hne
  · exact absurd (by simp [KC8Run.m7, wga2, hs u hu]) hne
  · left
    by_contra hcon
    apply hne
    simp only [KC8Run.m8, kc8]
    rw [ite_eq_right]
    exact fun h1 => hcon ((hall u hu).2.symm.trans h1)

/-- Theorem 6.5 (message complexity): under the hypothesis of `KC8Run.sparse`, correct nodes send
at most `8 n (|F| + 2)` messages, i.e. `O(n (f + 1))` messages of `O(log |V|)` bits. -/
theorem KC8Run.card_sent_le {F : Finset (Fin n)} (E : KC8Run F) (hF : 3 * F.card < n) (c : ℕ)
    (ℓo : Option (Fin n)) (hall : ∀ v, v ∉ F → E.x v = c ∧ E.l v = ℓo)
    (hℓ : ∀ ℓ, ℓo = some ℓ → ℓ ∉ F) :
    (sent F E.m1).card + (sent F E.m2).card + (sent F E.m3).card + (sent F E.m4).card +
      (sent F E.m5).card + (sent F E.m6).card + (sent F E.m7).card + (sent F E.m8).card ≤
      8 * (n * (F.card + 2)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := E.sparse hF c ℓo hall hℓ
  have := s1.card_sent_le; have := s2.card_sent_le; have := s3.card_sent_le
  have := s4.card_sent_le; have := s5.card_sent_le; have := s6.card_sent_le
  have := s7.card_sent_le; have := s8.card_sent_le
  generalize n * (F.card + 2) = N at *
  omega

end KC8

end EarlyStabilizingCounting
