import Papers.PODC2010.ModularConsensus.Basic
import Podc.Computability.Distributed.SharedMemory.SeqCompose

/-!
# Operational composition of deciding objects (Procedure Composition of Aspnes, PODC 2010)

`Cslib.SharedMemory.Impl.seqComp X Y deciderCont` is Procedure Composition run on actual
shared-memory implementations `X`, `Y` of deciding objects (disjoint base objects): run `X`; on
`(commit, v)` return it, on `(adopt, v)` continue with `Y` on input `v` and return its output.

* `seqComp_mem_seq`: the inputs and outputs of every valid one-shot execution of the composite
  are an input/output pair of the relational composition `DX ⨾ DY` of the behaviours that `X`
  and `Y` are proved to have (`Impl.Solves`). Hence Lemmas 1 and 3 and Theorem 4 (safety) of
  `Basic.lean` apply to the operational composition: `seqComp_solves_validity`,
  `seqComp_solves_weakConsensus`.
* Termination (Lemma 2) and step complexity are `Cslib.SharedMemory.Impl.seqComp_waitFree` and
  `Cslib.SharedMemory.Impl.seqComp_tauSteps_le` (deterministic, potential-based).
-/

namespace Podc.ModularConsensus

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P]
  {ιX ιY : Type} [DecidableEq ιX] [DecidableEq ιY] {BX : ιX → ObjSpec} {BY : ιY → ObjSpec}
  {LX LY : Type}

/-- The continuation map of Procedure Composition: a commit is returned, an adopted value is fed
to the second object. -/
def deciderCont : Decision × V → Option V
  | (.commit, _) => none
  | (.adopt, v) => some v

omit [DecidableEq P] in
@[simp] lemma deciderCont_commit (v : V) : deciderCont (.commit, v) = none := rfl

omit [DecidableEq P] in
@[simp] lemma deciderCont_adopt (v : V) : deciderCont (.adopt, v) = some v := rfl

omit [DecidableEq P] in
lemma deciderCont_eq_some {o : Decision × V} {v : V} (h : deciderCont o = some v) :
    o = (.adopt, v) := by
  obtain ⟨_ | _, w⟩ := o
  · simp only [deciderCont_adopt, Option.some.injEq] at h; rw [h]
  · simp at h

/-- **Operational Procedure Composition refines `DObj.seq`.** If the implementations `X` and `Y`
of deciding objects have behaviours `DX` and `DY` (every one-shot execution has an input/output
pair in `DX`, resp. `DY`), then every valid one-shot execution of `X.seqComp Y deciderCont` has
its input/output pair in `DX ⨾ DY`. -/
theorem seqComp_mem_seq [Inhabited V] {DX DY : DObj P V}
    (X : Impl (taskObj V (Decision × V)) BX P LX) (Y : Impl (taskObj V (Decision × V)) BY P LY)
    (hX : X.Solves ⟨V, Decision × V, DX⟩) (hY : Y.Solves ⟨V, Decision × V, DY⟩)
    (hall : ∀ p v, Y.allowed p v)
    {α : List (Label P (taskObj V (Decision × V)))} (hα : (X.seqComp Y deciderCont).Valid α)
    (h1 : OneShot α) : DObj.seq DX DY (inputs α) (outputs α) := by
  obtain ⟨outX, inpY, outY, hx, hy, hlink, hwf, hout⟩ :=
    Impl.seqComp_solves X Y deciderCont hX hY (fun p _ m _ => hall p m) hα h1
  have hlink' : ∀ p v, inpY p = some v → outX p = some (.adopt, v) := fun p v hp => by
    obtain ⟨o, ho, hc⟩ := hlink p v hp
    rw [ho, deciderCont_eq_some hc]
  refine ⟨outX, inpY, outY, hx, hy, hlink', fun p => (hout p).trans ?_⟩
  rcases hpx : outX p with _ | ⟨_ | _, v⟩
  · have hY0 : outY p = none := by
      by_contra hne
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hwf p hne)
      rw [hlink' p v hv] at hpx; cases hpx
    simp [seqOutput, DObj.seqOut, hY0]; rfl
  · simp [seqOutput, DObj.seqOut]; rfl
  · simp [seqOutput, DObj.seqOut]; rfl

/-- **Lemma 1, operationally.** If `X` and `Y` satisfy validity, so does
`X.seqComp Y deciderCont`. -/
theorem seqComp_solves_validity [Inhabited V]
    (X : Impl (taskObj V (Decision × V)) BX P LX) (Y : Impl (taskObj V (Decision × V)) BY P LY)
    (hX : X.Solves ⟨V, Decision × V, Validity⟩) (hY : Y.Solves ⟨V, Decision × V, Validity⟩)
    (hall : ∀ p v, Y.allowed p v) :
    (X.seqComp Y deciderCont).Solves ⟨V, Decision × V, Validity⟩ := fun _ hα h1 =>
  DObj.validity_seq (X := (Validity : DObj P V)) (Y := Validity) (fun _ _ h => h)
    (fun _ _ h => h) _ _
    (seqComp_mem_seq X Y hX hY hall hα h1)

/-- **Theorem 4 (safety), operationally.** If `X` and `Y` are weak consensus objects (validity
and coherence), so is `X.seqComp Y deciderCont` (Lemmas 1 and 3). -/
theorem seqComp_solves_weakConsensus [Inhabited V]
    (X : Impl (taskObj V (Decision × V)) BX P LX) (Y : Impl (taskObj V (Decision × V)) BY P LY)
    (hX : X.Solves ⟨V, Decision × V, fun inp out => Validity inp out ∧ Coherence out⟩)
    (hY : Y.Solves ⟨V, Decision × V, fun inp out => Validity inp out ∧ Coherence out⟩)
    (hall : ∀ p v, Y.allowed p v) :
    (X.seqComp Y deciderCont).Solves
      ⟨V, Decision × V, fun inp out => Validity inp out ∧ Coherence out⟩ := fun _ hα h1 => by
  let W : DObj P V := fun inp out => Validity inp out ∧ Coherence out
  have hW : W.IsWeakConsensus := ⟨fun _ _ h => h.1, fun _ _ h => h.2⟩
  have hw := DObj.isWeakConsensus_seq hW hW
  have hm := seqComp_mem_seq X Y hX hY hall hα h1
  exact ⟨hw.1 _ _ hm, hw.2 _ _ hm⟩

end Podc.ModularConsensus
