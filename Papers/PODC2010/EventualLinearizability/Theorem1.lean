import Papers.PODC2010.EventualLinearizability.Nonblocking
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Theorem 1, nonblocking part: a counterexample

Theorem 1 of the paper claims that Eventual Linearizability ("weakly consistent and
`t`-linearizable") is nonblocking, "directly" from Lemma 3 (weak consistency is nonblocking)
and Lemma 4 (`t`-linearizability is nonblocking). The two lemmas choose the response of the
pending operation differently, and the choices can be incompatible.

Counterexample (`theorem1_nonblocking_false`). One swap register (`read`, `swap v` writes `v`
and returns the old value), initially `0`, three processes, `t = 3` (global time = position of
the event):

```
1  p1: inv swap(1)              (i1, pending forever)
2  p0: inv read                 (o')
3  p0: res 1
4  p0: inv swap(2)              (o, pending)
5  p2: inv read                 (r2)
6  p2: res 2
7  p2: inv read                 (r3)
8  p2: res 1
```

`H` is weakly consistent and `3`-linearizable (`o', o, r2, i1, r3`). But `o` cannot respond:

* `t`-linearizability forces `o` to return `0`: `r2` (late) reads `2`, so the last swap before
  it is `o`; `r3` (late, after `r2`) reads `1`, so `i1` comes after `r2`; hence no swap
  precedes `o`.
* weak consistency forces `o` to return `1`: `τ(p0, o')` must end with `o'` returning `1`, so
  it contains `i1`; by (iii) `τ(p0, o)` contains `i1` before `o`, and `i1` is the only other
  swap.
-/

namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

/-! ### Concrete histories: decidable reformulations -/

section General

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

omit [DecidableEq P] [DecidableEq X] in
lemma IdSeq.mem_ids {L : IdSeq P X Op Res} {a : OpId P X} :
    a ∈ L.ids ↔ ∃ e, (a, e) ∈ L := by
  simp [IdSeq.ids]

/-- Real-time precedence is decidable: it suffices to look at prefixes. -/
lemma precedes_iff_take {H : History P X Op Res} {a b : OpId P X} :
    Precedes H a b ↔ ∃ n ∈ List.range (H.length + 1), Completed (H.take n) a ∧
      ¬ Invoked (H.take n) b := by
  constructor
  · rintro ⟨β, γ, rfl, h1, h2⟩
    refine ⟨β.length, by simp; omega, ?_⟩
    simpa using And.intro h1 h2
  · rintro ⟨n, -, h1, h2⟩
    exact ⟨H.take n, H.drop n, (List.take_append_drop _ _).symm, h1, h2⟩

instance (H : History P X Op Res) (a b : OpId P X) : Decidable (Precedes H a b) :=
  decidable_of_iff _ precedes_iff_take.symm

end General

/-! ### The swap register -/

/-- Operations of a swap register. -/
inductive SwapOp
  | read
  | swap (v : ℕ)
  deriving DecidableEq

/-- Transition function of a swap register (state = value; `swap v` returns the old value). -/
def swapδ : ℕ → SwapOp → ℕ × ℕ
  | v, .read => (v, v)
  | v, .swap w => (w, v)

/-- The sequential specification: one swap register, initially `0`. -/
def swapSpec : SeqSpec (Fin 3) Unit SwapOp ℕ := fun _ => detSpec 0 swapδ

abbrev Ev := Event (Fin 3) Unit SwapOp ℕ

/-- The history of the counterexample. -/
def H₀ : History (Fin 3) Unit SwapOp ℕ :=
  [.inv 1 () (.swap 1), .inv 0 () .read, .res 0 () 1, .inv 0 () (.swap 2),
   .inv 2 () .read, .res 2 () 2, .inv 2 () .read, .res 2 () 1]

/-- The extension of `H₀` by the response `r` of the pending `swap(2)` of `p0`. -/
def H₁ (r : ℕ) : History (Fin 3) Unit SwapOp ℕ := H₀ ++ [.res 0 () r]

/-- Operation identities. -/
def i1 : OpId (Fin 3) Unit := ⟨1, (), 0⟩
def o' : OpId (Fin 3) Unit := ⟨0, (), 0⟩
def o : OpId (Fin 3) Unit := ⟨0, (), 1⟩
def r2 : OpId (Fin 3) Unit := ⟨2, (), 0⟩
def r3 : OpId (Fin 3) Unit := ⟨2, (), 1⟩

/-- All operations of `H₀`. -/
def U : List (OpId (Fin 3) Unit) := [i1, o', o, r2, r3]

/-- The late operations: invoked after time `t = 3`. -/
def late : Set (OpId (Fin 3) Unit) := after (tInv H₀) 3

lemma length_opsOf_H₀ (p : Fin 3) (x : Unit) : (opsOf H₀ p x).length ≤ 8 :=
  (List.length_filterMap_le _ _).trans (by decide)

lemma length_ressOf_H₀ (p : Fin 3) (x : Unit) : (ressOf H₀ p x).length ≤ 8 :=
  (List.length_filterMap_le _ _).trans (by decide)

lemma invoked_H₀ {a : OpId (Fin 3) Unit} : Invoked H₀ a ↔ a ∈ U := by
  rcases a with ⟨p, x, k⟩
  by_cases hk : k < 9
  · have : ∀ p : Fin 3, ∀ k < 9, (Invoked H₀ ⟨p, (), k⟩ ↔ ⟨p, (), k⟩ ∈ U) := by decide
    exact this p k hk
  · have h1 := length_opsOf_H₀ p x
    have h2 : (⟨p, x, k⟩ : OpId (Fin 3) Unit) ∉ U := by
      intro h
      simp only [U, i1, o', o, r2, r3, List.mem_cons, OpId.mk.injEq, List.not_mem_nil,
        or_false] at h
      rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> omega
    simp only [Invoked, h2, iff_false]; omega

lemma completed_H₀ {a : OpId (Fin 3) Unit} : Completed H₀ a ↔ a ∈ [o', r2, r3] := by
  rcases a with ⟨p, x, k⟩
  by_cases hk : k < 9
  · have : ∀ p : Fin 3, ∀ k < 9, (Completed H₀ ⟨p, (), k⟩ ↔ ⟨p, (), k⟩ ∈ [o', r2, r3]) := by
      decide
    exact this p k hk
  · have h1 := length_ressOf_H₀ p x
    have h2 : (⟨p, x, k⟩ : OpId (Fin 3) Unit) ∉ [o', r2, r3] := by
      intro h
      simp only [o', r2, r3, List.mem_cons, OpId.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> omega
    simp only [Completed, h2, iff_false]; omega

/-- `tInv` of an invoked operation, computed from prefixes. -/
lemma tInv_eq {H : History (Fin 3) Unit SwapOp ℕ} {a : OpId (Fin 3) Unit} {n : ℕ}
    (h1 : Invoked (H.take (n + 1)) a) (h2 : ¬ Invoked (H.take n) a) : tInv H a = n + 1 := by
  rw [invoked_take_iff] at h1 h2
  have := not_and.1 h2 h1.1
  omega

lemma late_iff {a : OpId (Fin 3) Unit} (ha : a ∈ U) : a ∈ late ↔ a ∈ [o, r2, r3] := by
  simp only [U, List.mem_cons, List.not_mem_nil, or_false] at ha
  simp only [late, after, Set.mem_ofPred_eq]
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · rw [tInv_eq (n := 0) (by decide) (by decide)]; decide
  · rw [tInv_eq (n := 1) (by decide) (by decide)]; decide
  · rw [tInv_eq (n := 3) (by decide) (by decide)]; decide
  · rw [tInv_eq (n := 4) (by decide) (by decide)]; decide
  · rw [tInv_eq (n := 6) (by decide) (by decide)]; decide

/-- Legality for the swap register is the run of the transition function. -/
lemma legal_swap_iff {M : List (OpRec (Fin 3) Unit SwapOp ℕ)} :
    Legal swapSpec (seqHist M) ↔ runOK swapδ 0 M := by
  rw [legal_seqHist_iff]
  constructor
  · intro h; have := h (); rw [swapSpec, seqHist_mem_detSpec] at this
    simpa using this
  · intro h x; rw [swapSpec, seqHist_mem_detSpec]; simpa using h

/-- Decidability of the run of the swap register. -/
def decRunOK : (q : ℕ) → (M : List (OpRec (Fin 3) Unit SwapOp ℕ)) → Decidable (runOK swapδ q M)
  | _, [] => isTrue trivial
  | q, e :: M =>
    have := decRunOK (swapδ q e.o).1 M
    decidable_of_iff _ (runOK_cons swapδ q e M).symm

instance (q : ℕ) (M : List (OpRec (Fin 3) Unit SwapOp ℕ)) : Decidable (runOK swapδ q M) :=
  decRunOK q M

/-- The operation of an identity in `H₀`. -/
def opU (a : OpId (Fin 3) Unit) : SwapOp := (opOf H₀ a).getD .read

/-- The unique legal sequential history with the given order of identities. -/
def fillWith (f : OpId (Fin 3) Unit → SwapOp) :
    ℕ → List (OpId (Fin 3) Unit) → IdSeq (Fin 3) Unit SwapOp ℕ
  | _, [] => []
  | q, a :: π => (a, ⟨a.p, (), f a, (swapδ q (f a)).2⟩) :: fillWith f (swapδ q (f a)).1 π

/-- `fillWith` for the operations of `H₀`. -/
abbrev fillL : ℕ → List (OpId (Fin 3) Unit) → IdSeq (Fin 3) Unit SwapOp ℕ := fillWith opU

lemma eq_fillWith {f : OpId (Fin 3) Unit → SwapOp} {L : IdSeq (Fin 3) Unit SwapOp ℕ} {q : ℕ}
    (hof : ∀ ae ∈ L, ae.2.p = ae.1.p ∧ ae.2.o = f ae.1) (hrun : runOK swapδ q L.recs) :
    L = fillWith f q L.ids := by
  induction L generalizing q with
  | nil => rfl
  | cons ae L ih =>
    obtain ⟨a, ⟨p, x, op, r⟩⟩ := ae
    obtain ⟨hp, ho⟩ := hof _ List.mem_cons_self
    simp only at hp ho
    simp only [IdSeq.recs, List.map_cons, runOK_cons] at hrun
    obtain ⟨hr, hrun⟩ := hrun
    subst hp ho hr
    simp only [IdSeq.ids, List.map_cons, fillWith]
    congr 1
    exact ih (fun ae hae => hof ae (List.mem_cons_of_mem _ hae)) hrun

/-- A legal sequential history of operations of `H₀` (or of its extensions `H₁ r`). -/
lemma eq_fillL_of_isSeqOf {H : History (Fin 3) Unit SwapOp ℕ}
    (hop : ∀ a, opOf H a = opOf H₀ a) {L : IdSeq (Fin 3) Unit SwapOp ℕ}
    (hL : IsSeqOf swapSpec H L) : L = fillL 0 L.ids ∧ L.ids ⊆ U := by
  have hof : ∀ ae ∈ L, ae.2.p = ae.1.p ∧ ae.2.o = opU ae.1 ∧ ae.1 ∈ U := by
    intro ae hae
    obtain ⟨h1, -, h3⟩ := hL.ofHist ae hae
    rw [hop] at h3
    exact ⟨h1, by simp [opU, h3], invoked_H₀.1 (Invoked.of_opOf h3)⟩
  refine ⟨eq_fillWith (fun ae hae => ⟨(hof ae hae).1, (hof ae hae).2.1⟩)
    (legal_swap_iff.1 hL.legal), ?_⟩
  intro a ha
  obtain ⟨ae, hae, rfl⟩ := List.mem_map.1 ha
  exact (hof ae hae).2.2

lemma mem_sublists_permutations {π V : List (OpId (Fin 3) Unit)} (hnd : π.Nodup)
    (hU : π ⊆ V) : π ∈ V.sublists.flatMap List.permutations' := by
  obtain ⟨s, hs, hsU⟩ := List.subperm_of_subset hnd hU
  simp only [List.mem_flatMap, List.mem_sublists, List.mem_permutations']
  exact ⟨s, hsU, hs.symm⟩

/-! ### The decidable core facts -/

/-- The result of an identity in a list of entries. -/
def resIn (L : IdSeq (Fin 3) Unit SwapOp ℕ) (a : OpId (Fin 3) Unit) : Option ℕ :=
  (L.find? (fun ae => ae.1 = a)).map (·.2.r)

set_option maxRecDepth 100000 in
/-- `t`-linearization side: in every order of the five operations that respects `<_{H,3}` and
gives `r2` the result `2` and `r3` the result `1`, `o` returns `0`. -/
lemma tlin_core : ∀ π ∈ U.permutations',
    [o', o].Sublist π → [o', r2].Sublist π → [o', r3].Sublist π → [r2, r3].Sublist π →
    resIn (fillL 0 π) r2 = some 2 → resIn (fillL 0 π) r3 = some 1 →
    resIn (fillL 0 π) o = some 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Weak-consistency side: a legal sequential history ending with `o'` returning `1`
contains `i1`; one ending with `o` and containing `i1` gives `o` the result `1`. -/
lemma wc_core : ∀ π ∈ U.sublists.flatMap List.permutations',
    ((fillL 0 π).getLast?.map (fun ae => (ae.1, ae.2.r)) = some (o', 1) → i1 ∈ π) ∧
    ((fillL 0 π).getLast?.all fun ae => decide (ae.1 = o → i1 ∈ π → ae.2.r = 1)) := by
  decide +kernel

lemma resIn_of_mem {L : IdSeq (Fin 3) Unit SwapOp ℕ} (hnd : L.ids.Nodup) {a : OpId (Fin 3) Unit}
    {e : OpRec (Fin 3) Unit SwapOp ℕ} (h : (a, e) ∈ L) : resIn L a = some e.r := by
  induction L with
  | nil => simp at h
  | cons bf L ih =>
    obtain ⟨b, f⟩ := bf
    simp only [IdSeq.ids, List.map_cons, List.nodup_cons] at hnd
    by_cases hb : b = a
    · subst hb
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [resIn]
      · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hnd.1
    · rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; exact absurd h.1.symm hb
      · have := ih hnd.2 h
        simpa [resIn, hb] using this

/-! ### The history `H₀` is weakly consistent and `3`-linearizable -/

lemma wellFormed_H₀ : WellFormed H₀ := by
  intro p
  fin_cases p
  · exact ⟨[⟨0, (), .read, 1⟩], Or.inr ⟨0, (), .swap 2, by decide⟩⟩
  · exact ⟨[], Or.inr ⟨1, (), .swap 1, by decide⟩⟩
  · exact ⟨[⟨2, (), .read, 2⟩, ⟨2, (), .read, 1⟩], Or.inl (by decide)⟩

lemma pendingInv_H₀ : restrictP H₀ 0 = seqHist [⟨0, (), .read, 1⟩] ++ [.inv 0 () (.swap 2)] := by
  decide

lemma forall_completed {Q : OpId (Fin 3) Unit → Prop} (h : ∀ b ∈ [o', r2, r3], Q b) :
    ∀ b, Completed H₀ b → Q b := fun b hb => h b (completed_H₀.1 hb)

/-- The sequential histories `τ(i, o)` witnessing weak consistency of `H₀`. -/
def τ₀ (a : OpId (Fin 3) Unit) : IdSeq (Fin 3) Unit SwapOp ℕ :=
  if a = o' then [(i1, ⟨1, (), .swap 1, 0⟩), (o', ⟨0, (), .read, 1⟩)]
  else if a = r2 then [(o, ⟨0, (), .swap 2, 0⟩), (r2, ⟨2, (), .read, 2⟩)]
  else if a = r3 then [(o, ⟨0, (), .swap 2, 0⟩), (r2, ⟨2, (), .read, 2⟩),
    (i1, ⟨1, (), .swap 1, 2⟩), (r3, ⟨2, (), .read, 1⟩)]
  else []

lemma weaklyConsistent_H₀ : WeaklyConsistent swapSpec H₀ := by
  refine ⟨τ₀, forall_completed ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨⟨⟨by decide, by decide, legal_swap_iff.2 (by decide)⟩, ?_, by decide, ?_⟩,
    ⟨⟨by decide, by decide, legal_swap_iff.2 (by decide)⟩, ?_, by decide, ?_⟩,
    ⟨⟨by decide, by decide, legal_swap_iff.2 (by decide)⟩, ?_, by decide, ?_⟩⟩
  all_goals first
    | exact ⟨_, rfl, by decide⟩
    | exact fun b hbp hb => by
        have := completed_H₀.1 hb.completed
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl <;> revert hbp hb <;> decide

/-- The `3`-linearization `o', o, r2, i1, r3` of `H₀`. -/
def L₀ : IdSeq (Fin 3) Unit SwapOp ℕ :=
  [(o', ⟨0, (), .read, 0⟩), (o, ⟨0, (), .swap 2, 0⟩), (r2, ⟨2, (), .read, 2⟩),
   (i1, ⟨1, (), .swap 1, 2⟩), (r3, ⟨2, (), .read, 1⟩)]

lemma late_of_mem {a : OpId (Fin 3) Unit} (ha : a ∈ U) (hl : a ∈ late) : a ∈ [o, r2, r3] :=
  (late_iff ha).1 hl

lemma hH₀inv {a : OpId (Fin 3) Unit} (h : Completed H₀ a) : Invoked H₀ a :=
  wellFormed_H₀.invoked_of_completed h

lemma tLinearizable_H₀ : TLinearizable swapSpec H₀ late := by
  refine ⟨L₀, ⟨⟨⟨by decide, by decide, legal_swap_iff.2 (by decide)⟩, ?_, ?_⟩, ?_⟩⟩
  · intro a ha
    exact (by decide : ∀ a ∈ U, a ∈ L₀.ids) a (invoked_H₀.1 ha)
  · rintro a b ⟨hbl, hbi, hab⟩
    have hb := late_of_mem (invoked_H₀.1 hbi) hbl
    have ha := completed_H₀.1 hab.completed
    exact (by decide : ∀ a ∈ [o', r2, r3], ∀ b ∈ [o, r2, r3], Precedes H₀ a b →
      [a, b].Sublist L₀.ids) a ha b hb hab
  · intro a e hae hal hac
    have ha := completed_H₀.1 hac
    have hb := late_of_mem (invoked_H₀.1 (hH₀inv hac)) hal
    exact (by decide : ∀ ae ∈ L₀, ae.1 ∈ [o', r2, r3] → ae.1 ∈ [o, r2, r3] →
      resOf H₀ ae.1 = some ae.2.r) (a, e) hae ha hb

/-! ### The pending `swap(2)` cannot respond -/

lemma o_eq : o = ⟨0, (), cnt [(⟨0, (), .read, 1⟩ : OpRec (Fin 3) Unit SwapOp ℕ)] 0 ()⟩ := by
  decide

/-- In every extension `H₀ · res(r)`, `t`-linearizability forces `r = 0`. -/
lemma tlin_forces (r : ℕ) (h : TLinearizable swapSpec (H₀ ++ [.res 0 () r]) late) : r = 0 := by
  obtain ⟨L, hL⟩ := h
  have E := pendingExt wellFormed_H₀ pendingInv_H₀ r
  rw [← o_eq] at E
  obtain ⟨hfill, hsub⟩ := eq_fillL_of_isSeqOf E.opOf_eq hL.toIsSeqOf
  have hperm : L.ids ∈ U.permutations' := by
    rw [List.mem_permutations', List.perm_ext_iff_of_nodup hL.nodup (by decide)]
    intro a
    exact ⟨fun ha => hsub ha,
      fun ha => hL.all a ((E.invoked_iff a).2 (invoked_H₀.2 ha))⟩
  have hU : ∀ a ∈ U, Invoked (H₀ ++ [.res 0 () r]) a :=
    fun a ha => (E.invoked_iff a).2 (invoked_H₀.2 ha)
  have hlate : ∀ a ∈ [o, r2, r3], a ∈ late := fun a ha => by
    have haU : a ∈ U := (by decide : ∀ a ∈ [o, r2, r3], a ∈ U) a ha
    exact (late_iff haU).2 ha
  have hord : ∀ a b, b ∈ [o, r2, r3] → Precedes H₀ a b → [a, b].Sublist L.ids :=
    fun a b hb hab => hL.order a b ⟨hlate b hb,
      hU b ((by decide : ∀ b ∈ [o, r2, r3], b ∈ U) b hb), hab.mono⟩
  have hres : ∀ a e, (a, e) ∈ L → a ∈ [r2, r3] → resIn L a = resOf H₀ a := by
    intro a e hae ha
    have ha' : a ∈ [o, r2, r3] := (by decide : ∀ a ∈ [r2, r3], a ∈ [o, r2, r3]) a ha
    have hc : Completed H₀ a :=
      completed_H₀.2 ((by decide : ∀ a ∈ [r2, r3], a ∈ [o', r2, r3]) a ha)
    rw [resIn_of_mem hL.nodup hae, ← E.resOf_eq a hc]
    exact (hL.results a e hae (hlate a ha') ((E.completed_iff a).2 (Or.inl hc))).symm
  have hmem : ∀ a ∈ U, ∃ e, (a, e) ∈ L := fun a ha => IdSeq.mem_ids.1 (hL.all a (hU a ha))
  obtain ⟨e2, he2⟩ := hmem r2 (by decide)
  obtain ⟨e3, he3⟩ := hmem r3 (by decide)
  obtain ⟨eo, heo⟩ := hmem o (by decide)
  have key := tlin_core L.ids hperm (hord _ _ (by decide) (by decide))
    (hord _ _ (by decide) (by decide)) (hord _ _ (by decide) (by decide))
    (hord _ _ (by decide) (by decide))
    (by rw [← hfill, hres r2 e2 he2 (by decide)]; decide)
    (by rw [← hfill, hres r3 e3 he3 (by decide)]; decide)
  rw [← hfill, resIn_of_mem hL.nodup heo] at key
  have := hL.results o eo heo (hlate o (by decide)) ((E.completed_iff o).2 (Or.inr rfl))
  rw [E.resOf_a] at this
  simp only [Option.some.injEq] at key this
  omega

/-- In every extension `H₀ · res(r)`, weak consistency forces `r = 1`. -/
lemma wc_forces (r : ℕ) (h : WeaklyConsistent swapSpec (H₀ ++ [.res 0 () r])) : r = 1 := by
  obtain ⟨τ, hτ⟩ := h
  have E := pendingExt wellFormed_H₀ pendingInv_H₀ r
  rw [← o_eq] at E
  have hco' : Completed (H₀ ++ [.res 0 () r]) o' :=
    (E.completed_iff o').2 (Or.inl (completed_H₀.2 (by decide)))
  have hco : Completed (H₀ ++ [.res 0 () r]) o := (E.completed_iff o).2 (Or.inr rfl)
  obtain ⟨hs1, ⟨e1, hl1, hr1⟩, -, -⟩ := hτ o' hco'
  obtain ⟨hs2, ⟨e2, hl2, hr2⟩, -, hiii⟩ := hτ o hco
  obtain ⟨hf1, hsub1⟩ := eq_fillL_of_isSeqOf E.opOf_eq hs1
  obtain ⟨hf2, hsub2⟩ := eq_fillL_of_isSeqOf E.opOf_eq hs2
  -- `τ(o')` contains `i1`
  have hi1 : i1 ∈ (τ o').ids := by
    refine (wc_core _ (mem_sublists_permutations hs1.nodup hsub1)).1 ?_
    rw [← hf1, hl1]
    rw [E.resOf_eq o' (completed_H₀.2 (by decide))] at hr1
    have : e1.r = 1 := by
      have h0 : resOf H₀ o' = some 1 := by decide
      rw [h0] at hr1; exact (Option.some.inj hr1).symm
    simp [this]
  -- hence `τ(o)` contains `i1`
  have hprec : Precedes (H₀ ++ [.res 0 () r]) o' o := (show Precedes H₀ o' o by decide).mono
  have hi1' := hiii o' rfl hprec i1 hi1
  have := (wc_core _ (mem_sublists_permutations hs2.nodup hsub2)).2
  rw [← hf2, hl2] at this
  simp only [Option.all_some, decide_eq_true_eq] at this
  rw [E.resOf_a] at hr2
  rw [Option.some.inj hr2]; exact this trivial hi1'

/-- **Theorem 1 (nonblocking part) is false.** The history `H₀` is well-formed, weakly
consistent and `3`-linearizable (`late` = the operations invoked after time `3`, the time
being the position of the event), and `p0` has a pending invocation of the total operation
`swap(2)`; but no response to it keeps the history both weakly consistent and
`3`-linearizable. Lemmas 3 and 4 each provide a response (`1` and `0` respectively), but not
the same one. -/
theorem theorem1_nonblocking_false :
    WellFormed H₀ ∧ WeaklyConsistent swapSpec H₀ ∧ TLinearizable swapSpec H₀ late ∧
      PendingInv H₀ 0 () (.swap 2) ∧ Total swapSpec 0 () (.swap 2) ∧
      ∀ r, ¬ (WeaklyConsistent swapSpec (H₀ ++ [.res 0 () r]) ∧
        TLinearizable swapSpec (H₀ ++ [.res 0 () r]) late) :=
  ⟨wellFormed_H₀, weaklyConsistent_H₀, tLinearizable_H₀, ⟨_, pendingInv_H₀⟩,
    detSpec_total _ _ _ _ _, fun r h => by
      have h1 := tlin_forces r h.2
      have h2 := wc_forces r h.1
      omega⟩

/-- The nonblocking property claimed in Theorem 1, in the form of Lemmas 3 and 4
(Herlihy–Wing nonblocking: a pending invocation of a total operation can always be given a
response, for the same `t`), does not hold for "weakly consistent and `t`-linearizable". -/
theorem not_eventuallyLinearizable_nonblocking :
    ¬ ∀ (H : History (Fin 3) Unit SwapOp ℕ) (A : Set (OpId (Fin 3) Unit)) (p : Fin 3) (x : Unit)
        (op : SwapOp), WellFormed H → WeaklyConsistent swapSpec H → TLinearizable swapSpec H A →
        PendingInv H p x op → Total swapSpec p x op →
        ∃ r, WeaklyConsistent swapSpec (H ++ [.res p x r]) ∧
          TLinearizable swapSpec (H ++ [.res p x r]) A := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := theorem1_nonblocking_false
  obtain ⟨r, hr⟩ := h H₀ late 0 () (.swap 2) h1 h2 h3 h4 h5
  exact h6 r hr

end Podc.EventualLinearizability
