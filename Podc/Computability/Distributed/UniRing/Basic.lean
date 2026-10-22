/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/UniRing/Basic.lean
import Mathlib

/-!
# Asynchronous unidirectional rings of deterministic processors

`n` processors `Fin n` are arranged on a directed ring: processor `i` sends to `i + 1` and receives
from `i - 1` over a reliable FIFO link. Processors are deterministic and event driven: the behaviour
of a processor is a function of the list of messages it has received so far (its *history*); its
randomness, if any, is a parameter of the processor. Concretely a processor (`Proc`) gives

* `sent h`: all messages it has sent after processing the history `h` (`sent []` are the messages sent
  at initialization). Sending is incremental: `sent h` is a prefix of `sent (h ++ [m])`;
* `out h`: `some o` if, after processing `h`, it terminates with output `o`. A terminated processor
  receives no further messages.

A configuration (`Config`) is the vector of processed histories. A step (`Step`) delivers the next
pending message on one link to a non-terminated receiver. An oblivious schedule is a sequence of
processors `σ : ℕ → Fin n`; at time `t` the next pending message of `σ t` (if any) is delivered
(`run`). It is fair (`Fair`) if every processor is scheduled infinitely often (every fair
asynchronous execution is obtained this way: insert no-op steps).

Since every processor has a single incoming link, the system is confluent (it is a Kahn network):
**the schedule has no influence on what is computed.** We prove that every fair run eventually
dominates every reachable configuration (`exists_le_run`), so a processor terminates with output `o`
in some fair run iff in every fair run iff in some reachable configuration (`terminates_iff`), and its
output is unique (`Terminates.unique`).

To prove reachability of an explicitly given candidate final configuration `X` we provide
`exists_reach_le_of_consistent`: if `X` is *consistent* (every history is a prefix of what its
predecessor sends, and no processor terminates strictly before the end of its history), then some
reachable `c ≤ X` is *stuck below `X`*: each processor either has its whole history `X i` or has
processed everything its predecessor sent. A counting argument specific to the protocol then shows
`c = X`.

## Main definitions

* `Proc`, `Config`, `Proc.sent_mono`, `inbox`, `Enabled`, `deliver`, `Step`, `Reach`, `run`, `Fair`
* `Terminates P i o`: processor `i` terminates with output `o`

## Main statements

* `Reach.inv`: reachable histories are prefixes of the inbox and never extend past termination
* `exists_le_run`: a fair run eventually dominates any reachable configuration
* `terminates_iff`, `Terminates.unique`
* `reach_update`: a processor can always be fed messages already sent to it
* `exists_reach_le_of_consistent`
-/

namespace Cslib.UniRing

/-- A deterministic event-driven processor of a unidirectional ring, with messages `M` and outputs
`O`. `sent h` are all messages sent after processing the received history `h`; `out h = some o`
means that after processing `h` it terminates with output `o`. -/
structure Proc (M O : Type*) where
  /-- All messages sent after processing the history `h` (`sent []`: sent at initialization). -/
  sent : List M → List M
  /-- Sending is incremental. -/
  sent_snoc : ∀ h m, sent h <+: sent (h ++ [m])
  /-- `out h = some o`: having processed `h`, the processor terminates with output `o`. -/
  out : List M → Option O

variable {n : ℕ} {M O : Type*}

namespace Proc

theorem sent_mono (p : Proc M O) {h h' : List M} (hh : h <+: h') : p.sent h <+: p.sent h' := by
  obtain ⟨t, rfl⟩ := hh
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t m ih =>
    rw [← List.append_assoc]; exact ih.trans (p.sent_snoc _ m)

end Proc

/-- A configuration: the history processed by every processor. -/
abbrev Config (n : ℕ) (M : Type*) := Fin n → List M

/-- Componentwise prefix order on configurations. -/
def Le (c c' : Config n M) : Prop := ∀ i, c i <+: c' i

theorem Le.refl (c : Config n M) : Le c c := fun _ => List.prefix_refl _

theorem Le.trans {c c' c'' : Config n M} (h : Le c c') (h' : Le c' c'') : Le c c'' :=
  fun i => (h i).trans (h' i)

variable [NeZero n] (P : Fin n → Proc M O)

/-- The messages sent so far to `i` (by its predecessor `i - 1`). -/
def inbox (c : Config n M) (i : Fin n) : List M := (P (i - 1)).sent (c (i - 1))

/-- Processor `i` can receive a message: it has not terminated and a message is pending. -/
def Enabled (c : Config n M) (i : Fin n) : Prop :=
  (P i).out (c i) = none ∧ (c i).length < (inbox P c i).length

/-- Deliver the next pending message to `i` (a no-op if `i` is not enabled). -/
def deliver (c : Config n M) (i : Fin n) : Config n M :=
  if (P i).out (c i) = none then
    Function.update c i (c i ++ ((inbox P c i).drop (c i).length).take 1)
  else c

/-- One asynchronous step. -/
def Step (c c' : Config n M) : Prop := ∃ i, Enabled P c i ∧ c' = deliver P c i

/-- The initial configuration. -/
def init : Config n M := fun _ => []

/-- Reachable configurations. -/
def Reach (c : Config n M) : Prop := Relation.ReflTransGen (Step P) init c

/-- The run under the oblivious schedule `σ`. -/
def run (σ : ℕ → Fin n) : ℕ → Config n M
  | 0 => init
  | t + 1 => deliver P (run σ t) (σ t)

/-- A schedule is fair if every processor is scheduled infinitely often. -/
def Fair (σ : ℕ → Fin n) : Prop := ∀ i N, ∃ t, N ≤ t ∧ σ t = i

/-- Processor `i` terminates with output `o` (in some, equivalently every, fair run:
`terminates_iff`). -/
def Terminates (i : Fin n) (o : O) : Prop := ∃ c, Reach P c ∧ (P i).out (c i) = some o

/-- The invariant of reachable configurations. -/
def Inv (c : Config n M) : Prop :=
  ∀ i, c i <+: inbox P c i ∧ ∀ p x, p ++ [x] <+: c i → (P i).out p = none

variable {P}

theorem inbox_mono {c c' : Config n M} (h : Le c c') (i : Fin n) :
    inbox P c i <+: inbox P c' i :=
  (P (i - 1)).sent_mono (h _)

theorem deliver_of_enabled {c : Config n M} {i : Fin n} (h : Enabled P c i) :
    ∃ x, (inbox P c i)[(c i).length]? = some x ∧
      deliver P c i = Function.update c i (c i ++ [x]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨(inbox P c i)[(c i).length], by simp [h2], ?_⟩
  simp only [deliver, h1, ite_true]
  rw [List.drop_eq_getElem_cons h2, List.take_succ_cons, List.take_zero]

theorem deliver_of_not_enabled {c : Config n M} {i : Fin n} (h : ¬ Enabled P c i) :
    deliver P c i = c := by
  unfold deliver
  split_ifs with h1
  · have : (inbox P c i).length ≤ (c i).length := by
      by_contra h2; exact h ⟨h1, by omega⟩
    rw [List.drop_eq_nil_of_le this]
    simp
  · rfl

theorem le_deliver (c : Config n M) (i : Fin n) : Le c (deliver P c i) := by
  intro j
  unfold deliver
  split_ifs
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  · exact List.prefix_refl _

theorem deliver_ne (c : Config n M) {i j : Fin n} (h : j ≠ i) : deliver P c i j = c j := by
  unfold deliver; split_ifs <;> simp [h]

theorem inv_init : Inv P (init : Config n M) := by
  intro i
  refine ⟨by simp [init], fun p x h => ?_⟩
  simp [init] at h

theorem prefix_snoc_of_getElem? {l L : List M} {x : M} (h : l <+: L)
    (hx : L[l.length]? = some x) : l ++ [x] <+: L := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hx
  | cons y t =>
    simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hx
    subst hx
    exact ⟨t, by simp⟩

theorem Inv.deliver {c : Config n M} (hc : Inv P c) (i : Fin n) : Inv P (deliver P c i) := by
  by_cases he : Enabled P c i
  · obtain ⟨x, hx, hd⟩ := deliver_of_enabled he
    have hle : Le c (UniRing.deliver P c i) := le_deliver c i
    intro j
    rcases eq_or_ne j i with rfl | hj
    · rw [hd, Function.update_self]
      refine ⟨?_, fun p y hp => ?_⟩
      · exact (prefix_snoc_of_getElem? (hc j).1 hx).trans (by rw [← hd]; exact inbox_mono hle j)
      · rcases List.prefix_concat_iff.mp hp with h | h
        · obtain ⟨rfl, -⟩ := List.append_inj' h rfl
          exact he.1
        · exact (hc j).2 p y h
    · rw [deliver_ne c hj]
      exact ⟨(hc j).1.trans (inbox_mono hle j), (hc j).2⟩
  · rw [deliver_of_not_enabled he]; exact hc

theorem Step.le {c c' : Config n M} (h : Step P c c') : Le c c' := by
  obtain ⟨i, -, rfl⟩ := h; exact le_deliver c i

theorem Reach.inv {c : Config n M} (h : Reach P c) : Inv P c := by
  induction h with
  | refl => exact inv_init
  | tail _ hs ih => obtain ⟨i, -, rfl⟩ := hs; exact ih.deliver i

theorem Reach.deliver {c : Config n M} (h : Reach P c) (i : Fin n) : Reach P (deliver P c i) := by
  by_cases he : Enabled P c i
  · exact h.tail ⟨i, he, rfl⟩
  · rw [deliver_of_not_enabled he]; exact h

theorem reach_run (σ : ℕ → Fin n) (t : ℕ) : Reach P (run P σ t) := by
  induction t with
  | zero => exact Relation.ReflTransGen.refl
  | succ t ih => exact ih.deliver (σ t)

theorem run_le_succ (σ : ℕ → Fin n) (t : ℕ) : Le (run P σ t) (run P σ (t + 1)) :=
  le_deliver _ _

theorem run_mono (σ : ℕ → Fin n) {t t' : ℕ} (h : t ≤ t') : Le (run P σ t) (run P σ t') := by
  induction h with
  | refl => exact Le.refl _
  | step _ ih => exact ih.trans (run_le_succ σ _)

/-- An enabled processor stays enabled while its own history does not change. -/
theorem Enabled.mono {c c' : Config n M} {i : Fin n} (h : Enabled P c i) (hle : Le c c')
    (hi : c' i = c i) : Enabled P c' i :=
  ⟨hi ▸ h.1, hi ▸ lt_of_lt_of_le h.2 (inbox_mono hle i).length_le⟩

theorem getElem?_of_prefix {l L : List M} {k : ℕ} {x : M} (h : l <+: L) (hx : l[k]? = some x) :
    L[k]? = some x := by
  obtain ⟨t, rfl⟩ := h
  have hk : k < l.length := by
    by_contra hk; rw [List.getElem?_eq_none (by omega)] at hx; simp at hx
  rw [List.getElem?_append_left hk, hx]

theorem run_succ_of_ne (σ : ℕ → Fin n) {t : ℕ} {i : Fin n} (h : σ t ≠ i) :
    run P σ (t + 1) i = run P σ t i :=
  deliver_ne _ (Ne.symm h)

/-- **Fair runs dominate reachable configurations.** Every fair run eventually dominates (in the
prefix order) any reachable configuration: the ring is confluent. -/
theorem exists_le_run {σ : ℕ → Fin n} (hσ : Fair σ) {g : Config n M} (hg : Reach P g) :
    ∃ T, Le g (run P σ T) := by
  induction hg with
  | refl => exact ⟨0, fun i => by simp [run, init]⟩
  | tail _ hs ih =>
    rename_i c c' _
    obtain ⟨T, hT⟩ := ih
    obtain ⟨i, he, rfl⟩ := hs
    obtain ⟨x, hx, hd⟩ := deliver_of_enabled he
    -- `x` is also the next message in any later run configuration dominating `c`
    have key : ∀ r : Config n M, Inv P r → Le c r → (c i).length < (r i).length →
        c i ++ [x] <+: r i := by
      intro r hr hcr hlen
      have h1 : c i ++ [x] <+: inbox P r i :=
        prefix_snoc_of_getElem? ((hcr i).trans (hr i).1) (getElem?_of_prefix (inbox_mono hcr i) hx)
      exact List.prefix_of_prefix_length_le h1 (hr i).1 (by simp; omega)
    have upd : ∀ r : Config n M, Le c r → c i ++ [x] <+: r i → Le (deliver P c i) r := by
      intro r hcr hi j
      rw [hd]
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self]; exact hi
      · rw [Function.update_of_ne hj]; exact hcr j
    by_cases hlong : (c i).length < (run P σ T i).length
    · exact ⟨T, upd _ hT (key _ (reach_run σ T).inv hT hlong)⟩
    · have hri : run P σ T i = c i :=
        ((hT i).eq_of_length (le_antisymm (hT i).length_le (by omega))).symm
      classical
      have hex : ∃ t, T ≤ t ∧ σ t = i := hσ i T
      set t0 := Nat.find hex with ht0
      have hspec := Nat.find_spec hex
      have hmin : ∀ t, T ≤ t → t < t0 → σ t ≠ i := fun t h1 h2 h3 =>
        Nat.find_min hex h2 ⟨h1, h3⟩
      have hstay : ∀ t, T ≤ t → t ≤ t0 → run P σ t i = c i := by
        intro t h1 h2
        induction t, h1 using Nat.le_induction with
        | base => exact hri
        | succ t ht ih =>
          rw [run_succ_of_ne σ (hmin t ht (by omega))]; exact ih (by omega)
      have hct0 : Le c (run P σ t0) := hT.trans (run_mono σ hspec.1)
      have he0 : Enabled P (run P σ t0) i := he.mono hct0 (hstay t0 hspec.1 le_rfl)
      have hle1 : Le (run P σ t0) (run P σ (t0 + 1)) := run_le_succ σ t0
      refine ⟨t0 + 1, upd _ (hct0.trans hle1) (key _ (reach_run σ _).inv (hct0.trans hle1) ?_)⟩
      obtain ⟨y, -, hy⟩ := deliver_of_enabled he0
      have hrun : run P σ (t0 + 1) = deliver P (run P σ t0) i := by
        show deliver P (run P σ t0) (σ t0) = _
        rw [hspec.2]
      rw [hrun, hy, Function.update_self, List.length_append, hstay t0 hspec.1 le_rfl]
      simp

/-- A terminated processor's history does not grow. -/
theorem eq_of_le_of_out {c r : Config n M} (hr : Inv P r) (hcr : Le c r) {i : Fin n} {o : O}
    (ho : (P i).out (c i) = some o) : r i = c i := by
  by_contra hne
  have hlt : (c i).length < (r i).length := by
    rcases lt_or_eq_of_le (hcr i).length_le with h | h
    · exact h
    · exact absurd ((hcr i).eq_of_length h).symm hne
  obtain ⟨t, ht⟩ := hcr i
  cases t with
  | nil => simp at ht; exact hne ht.symm
  | cons y t =>
    have := (hr i).2 (c i) y ⟨t, by rw [← ht]; simp⟩
    rw [ho] at this; exact absurd this (by simp)

/-- **Schedule independence of termination.** In a fair run, processor `i` terminates with
output `o` iff it does so in some reachable configuration. -/
theorem terminates_iff {σ : ℕ → Fin n} (hσ : Fair σ) {i : Fin n} {o : O} :
    (∃ t, (P i).out (run P σ t i) = some o) ↔ Terminates P i o := by
  constructor
  · rintro ⟨t, ht⟩; exact ⟨_, reach_run σ t, ht⟩
  · rintro ⟨c, hc, ho⟩
    obtain ⟨T, hT⟩ := exists_le_run hσ hc
    exact ⟨T, by rw [eq_of_le_of_out (reach_run σ T).inv hT ho]; exact ho⟩

/-- The round-robin schedule. -/
def roundRobin (n : ℕ) [NeZero n] (t : ℕ) : Fin n := ⟨t % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem fair_roundRobin : Fair (roundRobin n) := by
  intro i N
  refine ⟨N * n + i, by nlinarith [NeZero.pos n], ?_⟩
  ext; simp [roundRobin, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

/-- Finitely many reachable configurations have a common reachable upper bound. -/
theorem exists_reach_ge {ι : Type*} [Finite ι] (g : ι → Config n M) (hg : ∀ j, Reach P (g j)) :
    ∃ c, Reach P c ∧ ∀ j, Le (g j) c := by
  have := fun j => exists_le_run (P := P) fair_roundRobin (hg j)
  choose T hT using this
  cases nonempty_fintype ι
  refine ⟨run P (roundRobin n) (Finset.univ.sup T), reach_run _ _, fun j => (hT j).trans
    (run_mono _ (Finset.le_sup (Finset.mem_univ j)))⟩

/-- The output of a processor is unique. -/
theorem Terminates.unique {i : Fin n} {o o' : O} (h : Terminates P i o) (h' : Terminates P i o') :
    o = o' := by
  obtain ⟨c, hc, ho⟩ := h
  obtain ⟨c', hc', ho'⟩ := h'
  obtain ⟨r, hr, hle⟩ := exists_reach_ge (P := P) ![c, c'] (by intro j; fin_cases j <;> assumption)
  have h1 := eq_of_le_of_out hr.inv (hle 0) ho
  have h2 := eq_of_le_of_out hr.inv (hle 1) ho'
  simp at h1 h2
  rw [← h1, h2] at ho; rw [ho] at ho'; exact Option.some_injective _ ho'

/-- **Pumping.** A processor can be fed any messages already sent to it, as long as it does not
terminate before. -/
theorem reach_update {c : Config n M} (hc : Reach P c) {j : Fin n} {h : List M}
    (hpre : h <+: inbox P c j) (hcj : c j <+: h)
    (hout : ∀ p x, p ++ [x] <+: h → (P j).out p = none) :
    Reach P (Function.update c j h) := by
  obtain ⟨t, rfl⟩ := hcj
  induction t generalizing c with
  | nil => simpa using hc
  | cons x t ih =>
    have hlen : (c j).length < (inbox P c j).length := by
      have := hpre.length_le; simp at this; omega
    have he : Enabled P c j := ⟨hout (c j) x ⟨t, by simp⟩, hlen⟩
    obtain ⟨y, hy, hd⟩ := deliver_of_enabled he
    have hxy : y = x := by
      have := getElem?_of_prefix hpre (show (c j ++ x :: t)[(c j).length]? = some x by simp)
      rw [hy] at this; exact Option.some_injective _ this
    subst hxy
    have hc' := hc.deliver j
    rw [hd] at hc'
    have key := ih hc' (by
        rw [Function.update_self]; simp
        exact hpre.trans (by rw [← hd]; exact inbox_mono (le_deliver c j) j)) (by
        rw [Function.update_self]; simpa using hout)
    simpa using key

/-- **Candidate final configurations.** If `X` is consistent (each history is a prefix of what the
predecessor sends in `X`, and no processor terminates strictly inside its history), then some
reachable configuration below `X` is *stuck below `X`*: every processor has either its full history
`X i` or has processed everything sent to it. -/
theorem exists_reach_le_of_consistent (X : Config n M) (hX : ∀ i, X i <+: inbox P X i)
    (hXo : ∀ i p x, p ++ [x] <+: X i → (P i).out p = none) :
    ∃ c, Reach P c ∧ Le c X ∧ ∀ i, c i = X i ∨ (inbox P c i).length ≤ (c i).length := by
  suffices H : ∀ m (c : Config n M), Reach P c → Le c X →
      ∑ i, ((X i).length - (c i).length) = m →
      ∃ c, Reach P c ∧ Le c X ∧ ∀ i, c i = X i ∨ (inbox P c i).length ≤ (c i).length from
    H _ init Relation.ReflTransGen.refl (fun i => by simp [init]) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c hc hcX hm
  by_cases hall : ∀ i, c i = X i ∨ (inbox P c i).length ≤ (c i).length
  · exact ⟨c, hc, hcX, hall⟩
  push Not at hall
  obtain ⟨i, hne, hlt⟩ := hall
  have hlen : (c i).length < (X i).length :=
    lt_of_le_of_ne (hcX i).length_le (fun h => hne ((hcX i).eq_of_length h))
  obtain ⟨z, hz⟩ : ∃ z, (X i)[(c i).length]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have he : Enabled P c i := ⟨hXo i (c i) z (prefix_snoc_of_getElem? (hcX i) hz), hlt⟩
  obtain ⟨x, hx, hd⟩ := deliver_of_enabled he
  have hxz : x = z := by
    have h1 := getElem?_of_prefix (inbox_mono hcX i) hx
    have h2 := getElem?_of_prefix (hX i) hz
    rw [h1] at h2; exact Option.some_injective _ h2
  subst hxz
  have hc'X : Le (deliver P c i) X := by
    intro j; rw [hd]
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]; exact prefix_snoc_of_getElem? (hcX j) hz
    · rw [Function.update_of_ne hj]; exact hcX j
  refine ih _ ?_ _ (hc.deliver i) hc'X rfl
  rw [← hm]
  apply Finset.sum_lt_sum
  · intro j _
    have := (le_deliver (P := P) c i j).length_le; omega
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hd, Function.update_self]; simp; omega

end Cslib.UniRing
