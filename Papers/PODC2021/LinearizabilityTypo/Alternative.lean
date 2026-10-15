import Mathlib
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Nonblocking

/-!
# Section 6 of Sela–Herlihy–Petrank: the alternative interpretation of operations

Definition 6.1 also counts pending invocations as operations. A pending operation never ends,
so in `<_H` it can only appear on the right: `a <_H b` iff `a` completed before `b` was invoked
(`b` completed or pending). With this interpretation and the original L2 (`<_H ⊆ <_S`) we get
`LinearizableAlt`.

* `LinearizableAlt.linearizable`: this definition is at least as strong as the amended
  Definition 4.1 (Section 8, Figure 6).
* `Hs_linearizable`, `Hs_not_linearizableAlt`: it is strictly stronger, i.e. too strong. The
  stack history `H_s` of Figure 5 is linearizable by Definition 4.1 (hence by Definition 2.2) but
  not under the alternative interpretation.
-/

namespace Podc2021.LinearizabilityTypo.Sec6

open Cslib.SharedMemory.HerlihyWing

set_option linter.unusedSectionVars false

/-- Linearizability with the original L2 and operations as in Definition 6.1. -/
def LinearizableAlt {P X Op Res : Type} [DecidableEq P] [DecidableEq X]
    (spec : SeqSpec P X Op Res) (H : History P X Op Res) : Prop :=
  WellFormed H ∧ ∃ H', IsExtension H H' ∧ ∃ S, Legal spec S ∧ Equiv (complete H') S ∧
    ∀ a b, Precedes H a b → Invoked H b → RT S a b

/-- Section 8: the alternative interpretation implies amended linearizability. -/
theorem LinearizableAlt.linearizable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]
    {spec : SeqSpec P X Op Res} {H : History P X Op Res} (h : LinearizableAlt spec H) :
    Linearizable spec H := by
  obtain ⟨hH, H', hext, S, hleg, hEq, hL2⟩ := h
  refine ⟨hH, H', hext, S, hleg, hEq, fun a b hab => hL2 a b ?_ ?_⟩
  · obtain ⟨R, rfl, hR, hwf⟩ := hext
    have hbc : Completed (H ++ R) b := completed_complete.1 hab.2
    have hp := (hwf.precedes_complete_iff hbc).1 hab.1
    have hbi : Invoked H b := by
      have := hwf.invoked_of_completed hbc
      simpa [Invoked, opsOf_eq_nil_of_isRes hR] using this
    exact hp.of_append_of_invoked hbi
  · obtain ⟨R, rfl, hR, hwf⟩ := hext
    have hbc : Completed (H ++ R) b := completed_complete.1 hab.2
    have := hwf.invoked_of_completed hbc
    simpa [Invoked, opsOf_eq_nil_of_isRes hR] using this

/-! ### The stack history `H_s` (Figure 5) -/

/-- Processes. -/
inductive SProc | A | B
  deriving DecidableEq

/-- Stack operations. -/
inductive SOp | push (v : ℕ) | pop
  deriving DecidableEq

/-- Stack responses. -/
inductive SRes | ok | val (v : ℕ)
  deriving DecidableEq

open SProc SOp SRes

/-- Legal runs of a stack whose `pop` on the empty stack does not return (it waits for a push):
such a `pop` has no legal response. -/
def stackOK {P X : Type} : List ℕ → List (OpRec P X SOp SRes) → Prop
  | _, [] => True
  | st, e :: M =>
    match e.o with
    | .push v => e.r = .ok ∧ stackOK (v :: st) M
    | .pop =>
      match st with
      | [] => False
      | v :: st' => e.r = .val v ∧ stackOK st' M

/-- Sequential specification of the (partial) stack, initially empty. -/
def stackSpec {P X : Type} [DecidableEq P] [DecidableEq X] : SeqSpec P X SOp SRes :=
  fun _ => {s | ∃ M, s = seqHist M ∧ stackOK [] M}

/-- `isPop`. -/
def isPop {P X : Type} (e : OpRec P X SOp SRes) : Bool :=
  match e.o with
  | .pop => true
  | .push _ => false

lemma stackOK_count {P X : Type} :
    ∀ (st : List ℕ) (M : List (OpRec P X SOp SRes)), stackOK st M →
      M.countP isPop ≤ M.countP (fun e => !isPop e) + st.length
  | _, [], _ => by simp
  | st, e :: M, h => by
    rcases he : e.o with v | _
    · have hp : isPop e = false := by simp [isPop, he]
      have h' : e.r = .ok ∧ stackOK (v :: st) M := by
        unfold stackOK at h; rw [he] at h; exact h
      have := stackOK_count _ M h'.2
      rw [List.countP_cons, List.countP_cons]
      simp only [hp, Bool.not_false]
      simp only [List.length_cons] at this
      simp; omega
    · have hp : isPop e = true := by simp [isPop, he]
      rcases st with _ | ⟨v, st'⟩
      · unfold stackOK at h; rw [he] at h; exact h.elim
      · have h' : e.r = .val v ∧ stackOK st' M := by
          unfold stackOK at h; rw [he] at h; exact h
        have := stackOK_count _ M h'.2
        rw [List.countP_cons, List.countP_cons]
        simp only [hp, Bool.not_true]
        simp; omega

/-- `H_s` (Figure 5): `A` pushes 1; then `B` pops 1, and then invokes a second `pop`, which
cannot complete (the stack is empty). -/
def Hs : History SProc Unit SOp SRes :=
  [.inv A () (push 1), .res A () ok, .inv B () pop, .res B () (val 1), .inv B () pop]

lemma Hs_wellFormed : WellFormed Hs := by
  have : Hs = (((([] ++ [.inv A () (push 1)]) ++ [.res A () ok]) ++ [.inv B () pop]) ++
      [.res B () (val 1)]) ++ [.inv B () pop] := rfl
  rw [this]
  refine wellFormed_concat_inv.2 ⟨wellFormed_concat_res.2 ⟨wellFormed_concat_inv.2
    ⟨wellFormed_concat_res.2 ⟨wellFormed_concat_inv.2 ⟨wellFormed_nil, [], by decide⟩, [], push 1,
      by decide⟩, [], by decide⟩, [], pop, by decide⟩, [⟨B, (), pop, val 1⟩], by decide⟩

lemma Hs_opsA : opsOf Hs A () = [push 1] := by decide
lemma Hs_opsB : opsOf Hs B () = [pop, pop] := by decide
lemma Hs_ressA : ressOf Hs A () = [ok] := by decide
lemma Hs_ressB : ressOf Hs B () = [val 1] := by decide

lemma Hs_opOf {a : OpId SProc Unit} {o : SOp} (h : opOf Hs a = some o) :
    (a = ⟨A, (), 0⟩ ∧ o = push 1) ∨ (a = ⟨B, (), 0⟩ ∧ o = pop) ∨ (a = ⟨B, (), 1⟩ ∧ o = pop) := by
  rcases a with ⟨_ | _, ⟨⟩, k⟩ <;>
    rcases k with _ | _ | k <;> simp_all [opOf, Hs_opsA, Hs_opsB]

lemma Hs_completed {a : OpId SProc Unit} (h : Completed Hs a) :
    a = ⟨A, (), 0⟩ ∨ a = ⟨B, (), 0⟩ := by
  rcases a with ⟨_ | _, ⟨⟩, k⟩ <;>
    rcases k with _ | _ | k <;> simp_all [Completed, Hs_ressA, Hs_ressB]

lemma Hs_prec_A0_B0 : Precedes Hs ⟨A, (), 0⟩ ⟨B, (), 0⟩ :=
  ⟨[.inv A () (push 1), .res A () ok], [.inv B () pop, .res B () (val 1), .inv B () pop], rfl,
    by decide, by decide⟩

lemma Hs_prec_B0_B1 : Precedes Hs ⟨B, (), 0⟩ ⟨B, (), 1⟩ :=
  ⟨[.inv A () (push 1), .res A () ok, .inv B () pop, .res B () (val 1)], [.inv B () pop], rfl,
    by decide, by decide⟩

/-- The linearization of `H_s`: the push, then the first pop. -/
def Ms : List (OpRec SProc Unit SOp SRes) := [⟨A, (), push 1, ok⟩, ⟨B, (), pop, val 1⟩]

lemma idsOf_Ms : idsOf Ms = [⟨A, (), 0⟩, ⟨B, (), 0⟩] := by decide

/-- Section 6: `H_s` is linearizable by the amended Definition 4.1. -/
theorem Hs_linearizable : Linearizable stackSpec Hs := by
  refine linearizable_iff.2 ⟨Hs_wellFormed, Ms, IsLinA.mk' Hs_wellFormed ?_ ?_ ?_ ?_⟩
  · intro a e hae
    rw [idsOf_Ms] at hae
    simp only [Ms, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hae
    rcases hae with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, fun _ => by decide⟩
  · intro a ha
    rw [idsOf_Ms]
    rcases Hs_completed ha with rfl | rfl <;> simp
  · rw [legal_seqHist_iff]
    intro x
    exact ⟨_, rfl, by simp [Ms, stackOK]⟩
  · intro a b hab hb
    rw [idsOf_Ms] at hb ⊢
    have ha := Hs_completed hab.completed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (not_precedes_self Hs_wellFormed _)
    · simp
    · exact absurd hab (Hs_prec_A0_B0.not_precedes Hs_wellFormed)
    · exact absurd hab (not_precedes_self Hs_wellFormed _)

/-- `H_s` is also linearizable by the original Definition 2.2. -/
theorem Hs_linearizableHW : LinearizableHW stackSpec Hs := Hs_linearizable.linearizableHW

/-- Section 6: `H_s` is **not** linearizable under the alternative interpretation (original L2,
pending invocations counted as operations): the first pop precedes the pending second pop, which
would therefore have to be completed in `S`, but no stack history with one push can have two
pops. -/
theorem Hs_not_linearizableAlt : ¬ LinearizableAlt stackSpec Hs := by
  rintro ⟨hH, H', hext, S, hleg, hEq, hL2⟩
  have hwf' : WellFormed H' := by obtain ⟨R, -, -, hwf⟩ := hext; exact hwf
  obtain ⟨M, rfl⟩ := eq_seqHist_of_equiv_complete hwf' hEq hleg.1
  obtain ⟨hrecs, hcomp, -, -⟩ := lin_of_extension hext hEq
  have hB1 : (⟨B, (), 1⟩ : OpId SProc Unit) ∈ idsOf M :=
    rt_seqHist.1 (hL2 _ _ Hs_prec_B0_B1 (by decide)) |>.subset (by simp)
  have hB0 : (⟨B, (), 0⟩ : OpId SProc Unit) ∈ idsOf M := hcomp _ (by decide)
  have hlegal : stackOK [] M := by
    obtain ⟨M', h1, h2⟩ := (legal_seqHist_iff _ M).1 hleg ()
    have : M.filter (·.x = ()) = M := List.filter_eq_self.2 (by simp)
    rw [this] at h1
    rwa [seqHist_injective h1]
  have hcnt := stackOK_count [] M hlegal
  set Z := (idsOf M).zip M with hZ
  have hZnd : Z.Nodup := List.Nodup.of_map Prod.fst (by
    rw [hZ, List.map_fst_zip (by simp)]; exact nodup_idsOf M)
  have hMZ : Z.map Prod.snd = M := List.map_snd_zip (by simp)
  -- two pops
  obtain ⟨e0, he0⟩ := exists_mem_zip_idsOf hB0
  obtain ⟨e1, he1⟩ := exists_mem_zip_idsOf hB1
  have hpop0 : isPop e0 = true := by
    have := (hrecs _ _ he0).1
    rcases Hs_opOf this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;> simp_all [isPop]
  have hpop1 : isPop e1 = true := by
    have := (hrecs _ _ he1).1
    rcases Hs_opOf this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all [isPop]
  have hpops : 2 ≤ M.countP isPop := by
    rw [← hMZ, List.countP_map, List.countP_eq_length_filter]
    have hsub : [((⟨B, (), 0⟩ : OpId SProc Unit), e0), (⟨B, (), 1⟩, e1)].Subperm
        (Z.filter (fun u => isPop u.2)) := by
      apply List.subperm_of_subset (by simp)
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact List.mem_filter.2 ⟨he0, hpop0⟩
      · exact List.mem_filter.2 ⟨he1, hpop1⟩
    simpa [Function.comp_def] using hsub.length_le
  -- at most one push
  have hpushes : M.countP (fun e => !isPop e) ≤ 1 := by
    rw [← hMZ, List.countP_map, List.countP_eq_length_filter]
    have hsub : ((Z.filter (fun u => !isPop u.2)).map Prod.fst).Subperm
        [(⟨A, (), 0⟩ : OpId SProc Unit)] := by
      apply List.subperm_of_subset ((hZnd.filter _).map_on ?_)
      · intro a ha
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
        obtain ⟨hu, hpush⟩ := List.mem_filter.1 hu
        have := (hrecs _ _ hu).1
        rcases Hs_opOf this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · simp [h]
        all_goals simp [isPop, h] at hpush
      · intro u hu v hv huv
        have hu' := (List.mem_filter.1 hu).1
        have hv' := (List.mem_filter.1 hv).1
        rcases u with ⟨a, e⟩; rcases v with ⟨b, f⟩
        simp only at huv; subst huv
        rw [zip_unique (nodup_idsOf M) hu' hv']
    simpa [Function.comp_def] using hsub.length_le
  simp at hcnt
  omega

end Podc2021.LinearizabilityTypo.Sec6
