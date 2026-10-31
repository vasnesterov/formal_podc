import Papers.PODC2019.BayouRevisited.Theorem5

/-!
# Main results: Theorem 5 and Corollary 1

Kokociński, Kobus, Wojciechowski, *On Mixing Eventual and Strong Consistency: Bayou Revisited*,
PODC 2019 (full version: *Acute Cloud Types*, arXiv:1905.11762v2), Section 6.

An implementation `I` of an ACT specification `S` *avoids temporary operation reordering* in the
sense of Theorem 5 if
* in every stable run its history extends to one abstract execution satisfying
  `BEC(weak, F) ∧ SinOrd(strong) ∧ BEC(strong, F)`, and
* in every asynchronous or stable run its history satisfies `BEC(weak, F)`.

Theorem 5: for `F_seq` (with both operations allowed at both levels) no ACT implementation (an
implementation obeying invisible reads, input-driven processing and op-driven messages) with
`n ≥ 2` replicas does so.
-/

namespace Podc.BayouRevisited

open Impl

/-- The guarantee ruled out by Theorem 5: `SinOrd(strong) ∧ BEC(strong, F)` in stable runs
(together with `BEC(weak, F)` for the same abstract execution) and `BEC(weak, F)` in both
asynchronous and stable runs. -/
def NoReordering {n : ℕ} {Op Val : Type} (S : ACTSpec Op Val) (I : Impl n Op Val) : Prop :=
  (∀ r, I.IsStableRun S r → (I.history r).Satisfies
      fun A => A.BEC .weak S.F ∧ A.SinOrd .strong ∧ A.BEC .strong S.F) ∧
  (∀ r, I.IsAsyncRun S r ∨ I.IsStableRun S r →
      (I.history r).Satisfies fun A => A.BEC .weak S.F)

/-- **Theorem 5** of [Kokociński–Kobus–Wojciechowski, PODC 2019], for the specification
`(F_seq, lvlmap_seq)` over any alphabet with two distinct letters: no ACT implementation with
`n ≥ 2` replicas satisfies `SinOrd(strong) ∧ BEC(strong, F_seq)` in stable runs and
`BEC(weak, F_seq)` in asynchronous and stable runs. -/
theorem theorem5_seq {α : Type} [Nontrivial α] {n : ℕ} (hn : 2 ≤ n)
    (I : Impl n (SeqOp α) (SeqVal α)) (hI : I.IsACT (seqSpec α)) :
    ¬ NoReordering (seqSpec α) I := by
  intro hyp
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
  have hyp' : I.T5Hyp := hyp
  rcases claim1 hI hyp' hpq hxy with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact main_contra hI hyp' hpq hxy m hm
  · exact main_contra hI hyp' (Ne.symm hpq) (Ne.symm hxy) m hm

/-- **Theorem 5** of [Kokociński–Kobus–Wojciechowski, PODC 2019], as stated: there exists an ACT
specification `(F, lvlmap)` for which no implementation (with any number `n ≥ 2` of replicas)
satisfies `SinOrd(strong) ∧ BEC(strong, F)` in stable runs and `BEC(weak, F)` in both
asynchronous and stable runs. The witness is `(F_seq, lvlmap_seq)` over the alphabet
`$ = {a, …, z}`. -/
theorem theorem5 : ∃ (Op Val : Type) (S : ACTSpec Op Val),
    ∀ n, 2 ≤ n → ∀ I : Impl n Op Val, I.IsACT S → ¬ NoReordering S I :=
  ⟨SeqOp (Fin 26), SeqVal (Fin 26), seqSpec (Fin 26), fun _ hn I hI => theorem5_seq hn I hI⟩

/-- **Corollary 1** of [Kokociński–Kobus–Wojciechowski, PODC 2019]: there is no generic
implementation that, for every ACT specification `(F, lvlmap)`, satisfies
`SinOrd(strong) ∧ BEC(strong, F)` in stable runs and `BEC(weak, F)` in asynchronous and stable
runs. -/
theorem corollary1 (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ (Op Val : Type) (S : ACTSpec Op Val), ∃ I : Impl n Op Val, I.IsACT S ∧ NoReordering S I := by
  intro h
  obtain ⟨Op, Val, S, hS⟩ := theorem5
  obtain ⟨I, hI, hN⟩ := h Op Val S
  exact hS n hn I hI hN

/-! ### Non-vacuity: the implementation restrictions are satisfiable -/

/-- A trivial implementation: one state, every invocation is answered immediately with a fixed
value `v`, no messages, no internal events. -/
def trivialImpl (n : ℕ) {Op Val : Type} (v : Val) : Impl n Op Val where
  State := Unit
  Msg := Unit
  IntEv := Empty
  init _ := ()
  ext _ c _ x := match x with
    | .invoke _ _ => ((), ⟨[(c, v)], [], []⟩)
    | _ => ((), ⟨[], [], []⟩)
  enabled _ _ _ := False
  int _ _ σ _ := (σ, ⟨[], [], []⟩)

lemma trivialImpl_noCasts {n : ℕ} {Op Val : Type} (v : Val) (i : Fin n)
    (ℓ : List (trivialImpl n (Op := Op) v).Input) :
    ∀ e ∈ (trivialImpl n (Op := Op) v).leffs i ℓ, e.rbCast = [] ∧ e.tobCast = [] := by
  induction ℓ using List.reverseRecOn with
  | nil => simp
  | append_singleton ℓ x ih =>
    intro e he
    rw [leffs_concat] at he
    rcases List.mem_append.1 he with he | he
    · exact ih e he
    · rw [List.mem_singleton.1 he]
      cases x with
      | inv op l => exact ⟨rfl, rfl⟩
      | rb j k m => exact ⟨rfl, rfl⟩
      | tob j k m => exact ⟨rfl, rfl⟩
      | int ι => exact ⟨rfl, rfl⟩

/-- The restrictions of `IsACT` are satisfiable (for every specification). -/
theorem isACT_trivialImpl {n : ℕ} {Op Val : Type} (S : ACTSpec Op Val) (v : Val) :
    (trivialImpl n (Op := Op) v).IsACT S where
  invisible_reads P _ i op _ _ := by
    refine ⟨rfl, ?_⟩
    simp [stepAt, step, trivialImpl]
  input_driven P _ i f := ⟨0, fun h => h⟩
  op_driven P _ i c e he hc := by
    have := trivialImpl_noCasts v i _ e (List.mem_of_getElem? he)
    simp [this.1, this.2] at hc

end Podc.BayouRevisited
