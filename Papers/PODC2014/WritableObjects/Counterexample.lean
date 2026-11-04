import Papers.PODC2014.WritableObjects.Lemma45
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The "not in use" requirement of the template is necessary

The proof of Lemma 4.5 in the paper never uses the template's requirement that the write-index
`f` of a `Write` is not in use (`Ptr ≠ f`) when the `Write` is invoked. It only uses condition
(C), ownership, and sequential writability, which it applies to the *sub-history* `Λ_ℓ` of the
operations with timestamp `ℓ` ("Subsequence `Λ_ℓ` is a history, and by (4.1), no
`A[i_ℓ].SWrite()` overlaps any other operation call on `A[i_ℓ]`. Therefore, there is a
linearization `S_ℓ` of `Λ_ℓ`", proof of Claim 4.7).

Here is a transcript (`cex`) of a register `WT` over `ℕ` (initially `0`) with three processes
that follows the template except for the "not in use" requirement, satisfies condition (C), in
which the history of each base object is linearizable, but whose high-level history is not
linearizable (`notInUse_necessary`):

* `p₀` writes `1` (index `0`, `Ptr := 0`), then starts `Write(2)` reusing index `0` while it is
  in use: `A[0].SWrite(2)` completes;
* `p₂` executes `Exec(read)`: `Ptr = 0`, reads `2` from `A[0]` and returns `2`;
* `p₁` executes `Write(3)` (index `1`, `Ptr := 1`) and returns;
* `p₀` writes `Ptr := 0` and returns from `Write(2)`;
* `p₂` executes `Exec(read)`: `Ptr = 0`, reads `2` and returns `2`.

The first read forces `Write(2)` before it, real time forces `Write(3)` after the first read and
before the second read, which then must return `3`. The sub-history `Λ_1` of the calls with
timestamp `1` (`A[0].SWrite(1)`, the first read returning `2`) has no overlapping `SWrite` but is
not linearizable, although the whole history of `A[0]` is: the inference quoted above fails
without the "not in use" requirement.
-/

namespace Podc.WritableObjects.Counterexample

open Cslib.SharedMemory List

/-- A read/write register over `ℕ`, initially `0`. -/
abbrev R : ObjSpec := register ℕ 0

/-- The register is writable (`Write(v)` returns `v`, as CSLib's register does). -/
def regW : Writable R := ⟨RWOp.write, id, fun _ _ => rfl⟩

/-- Index `0` is owned by `p₀`, index `1` by `p₁`. -/
def own : Fin 2 → Fin 3 := Fin.castSucc

/-- The transcript. -/
def cex : List (Ev (Fin 3) (Fin 2) R) :=
  [ .winv 0 1, .swinv 0 0 1, .aret 0 0 1, .ptr 0 0, .hret 0 1,
    .winv 0 2, .swinv 0 0 2, .aret 0 0 2,
    .einv 2 .read, .opinv 2 0 .read, .aret 2 0 2, .hret 2 2,
    .winv 1 3, .swinv 1 1 3, .aret 1 1 3, .ptr 1 1, .hret 1 3,
    .ptr 0 0, .hret 0 2,
    .einv 2 .read, .opinv 2 0 .read, .aret 2 0 2, .hret 2 2 ]

/-- Control states of the processes along `cex`. -/
def ctl : Fin 3 → ℕ → PSt (Fin 2) R
  | 0, t => (([.idle, .wBeg 1, .wSW 1 0, .wPtr 1 0, .wEnd 1, .idle, .wBeg 2, .wSW 2 0] :
      List (PSt (Fin 2) R)) ++ replicate 10 (PSt.wPtr 2 0 : PSt (Fin 2) R) ++ [(PSt.wEnd 2 : PSt (Fin 2) R)] ++
      replicate 5 (PSt.idle : PSt (Fin 2) R)).getD t .idle
  | 1, t => (replicate 13 (PSt.idle : PSt (Fin 2) R) ++ ([.wBeg 3, .wSW 3 1, .wPtr 3 1, .wEnd 3] :
      List (PSt (Fin 2) R)) ++ replicate 7 (PSt.idle : PSt (Fin 2) R)).getD t .idle
  | 2, t => (replicate 9 (PSt.idle : PSt (Fin 2) R) ++ ([.eBeg .read, .eOp 0, .eEnd 2] : List (PSt (Fin 2) R)) ++
      replicate 8 (PSt.idle : PSt (Fin 2) R) ++ ([.eBeg .read, .eOp 0, .eEnd 2, .idle] : List (PSt (Fin 2) R))).getD
      t .idle

lemma cex_ctrl : IsCtrl regW own cex ctl := by
  intro p
  refine ⟨by fin_cases p <;> rfl, fun t ht => ?_⟩
  simp only [cex, List.length_cons, List.length_nil] at ht
  fin_cases p <;> interval_cases t <;>
    simp [cex, ctl, Ev.proc, own] <;>
    first
    | exact PStep.winv _
    | exact PStep.einv _ (by intro v h; cases h)
    | exact PStep.swinv _ _ rfl
    | exact PStep.swret _ _ _
    | exact PStep.ptr _ _
    | exact PStep.wret (W := regW) _
    | exact PStep.opinv _ _
    | exact PStep.opret _ _
    | exact PStep.eret _

lemma cex_length : cex.length = 23 := rfl

lemma lt_of_cex {a : ℕ} {ev : Ev (Fin 3) (Fin 2) R} (h : cex[a]? = some ev) : a < 23 := by
  have := (getElem_of_getElem? h).1; rwa [cex_length] at this

/-- The transcript violates "not in use": `A[0].SWrite(2)` is invoked while `Ptr = 0`. -/
lemma cex_not_notInUse : ¬ NotInUse cex := fun h => h 6 0 0 2 rfl (by decide)

lemma cex_swinv0 {a : ℕ} {p : Fin 3} {v : ℕ} (ha : cex[a]? = some (.swinv p 0 v)) :
    (a = 1 ∧ p = 0 ∧ v = 1) ∨ (a = 6 ∧ p = 0 ∧ v = 2) := by
  have := lt_of_cex ha
  interval_cases a <;> simp [cex] at ha <;> omega

/-- Condition (C) holds (with `t*` just before the `Oper`). -/
lemma cex_condC : CondC cex := by
  intro e t q o o' i het he ht hq
  have htl := lt_of_cex ht
  interval_cases t <;> simp [cex] at ht
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    refine ⟨9, het, le_rfl, by decide, fun a p v ha => ?_⟩
    rcases cex_swinv0 ha with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨2, 1, by omega, by omega, rfl⟩
    · exact Or.inl ⟨7, 2, by omega, by omega, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    refine ⟨20, het, le_rfl, by decide, fun a p v ha => ?_⟩
    rcases cex_swinv0 ha with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨2, 1, by omega, by omega, rfl⟩
    · exact Or.inl ⟨7, 2, by omega, by omega, rfl⟩

section SeqExtend

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- Extending a linearization by an operation executed in isolation. -/
lemma seq_extend {α : List (Label P A)} {L : List (OpId P × A.Op)} (hL : IsLinearization α L)
    (p : P) (o : A.Op) (hcnt : (opsOf α p).length = (respsOf α p).length) :
    IsLinearization (α ++ [.inv p o] ++ [.ret p (A.δ (A.runOps A.init (L.map Prod.snd)) o).2])
      (L ++ [((p, (opsOf α p).length), o)]) := by
  have h1 := hL.append_inv p o
  have hx : opOf (α ++ [.inv p o]) (p, (opsOf α p).length) = some o := by
    simp [opOf, opsOf_append, opsOf]
  have hxL : (p, (opsOf α p).length) ∉ L.map Prod.fst := by
    intro hm
    have := hL.invoked_of_mem hm
    simp [Invoked] at this
  have hxc : ¬ Completed (α ++ [.inv p o]) (p, (opsOf α p).length) := by
    simp [Completed, respsOf_append, respsOf, hcnt]
  have h2 := h1.push hx hxL hxc
  refine h2.append_ret L [] o ?_ rfl
  simp [respsOf_append, respsOf, hcnt]

end SeqExtend

/-- Each base object behaves as a sequentially writable register: its history is even
linearizable (it is sequential). -/
lemma cex_seqWritable (i : Fin 2) : SeqWritable regW (lowH regW i cex) := by
  intro _
  fin_cases i
  · have h := seq_extend (seq_extend (seq_extend (seq_extend (isLinearization_nil (P := Fin 3)
      (A := R)) 0 (.write 1) rfl) 0 (.write 2) rfl) 2 .read rfl) 2 .read rfl
    exact ⟨_, by convert h using 1; rfl⟩
  · have h := seq_extend (isLinearization_nil (P := Fin 3) (A := R)) 1 (.write 3) rfl
    exact ⟨_, by convert h using 1; rfl⟩

/-- The register: the final state is the initial one or a written value. -/
lemma reg_runOps {q v : ℕ} {os : List (RWOp ℕ)} (h : R.runOps q os = v) :
    v = q ∨ RWOp.write v ∈ os := by
  induction os generalizing q with
  | nil => left; exact h.symm
  | cons o os ih =>
    rw [ObjSpec.runOps_cons] at h
    rcases ih h with h1 | h1
    · cases o with
      | read => left; exact h1
      | write w => right; simp only [register_write] at h1; rw [h1]; exact List.mem_cons_self
    · right; exact List.mem_cons_of_mem _ h1

/-- The response of a listed instance is given by the state reached before it. -/
lemma resp_of_split {h : List (Label (Fin 3) R)} {L L₁ L₂ : List (OpId (Fin 3) × R.Op)}
    (hL : IsLinearization h L) {x : OpId (Fin 3)} {o : R.Op} {r : ℕ}
    (hsplit : L = L₁ ++ (x, o) :: L₂) (hr : respOf h x = some r) :
    (R.δ (R.runOps R.init (L₁.map Prod.snd)) o).2 = r := by
  have := hL.seq
  rw [hsplit, seqOK_append] at this
  exact this.2.1 r hr

/-- The high-level history of `cex`. -/
def hc : List (Label (Fin 3) R) :=
  [.inv 0 (.write 1), .ret 0 1, .inv 0 (.write 2), .inv 2 .read, .ret 2 2, .inv 1 (.write 3),
    .ret 1 3, .ret 0 2, .inv 2 .read, .ret 2 2]

lemma highH_cex : highH regW cex = hc := rfl

lemma hc_ops0 : opsOf hc 0 = [.write 1, .write 2] := by decide
lemma hc_ops1 : opsOf hc 1 = [.write 3] := by decide
lemma hc_ops2 : opsOf hc 2 = [.read, .read] := by decide
lemma hc_resps2 : respsOf hc 2 = [2, 2] := by decide
lemma hc_resps1 : respsOf hc 1 = [3] := by decide

/-- **The "not in use" requirement is necessary** (and the inference in the proof of Claim 4.7
needs it): the transcript `cex` follows the template except for that requirement, satisfies
condition (C), each of its base objects is sequentially writable, yet its high-level history is
not linearizable. -/
theorem cex_not_linearizable : ¬ ∃ L, IsLinearization (highH regW cex) L := by
  rintro ⟨L, hL⟩
  rw [highH_cex] at hL
  have hnd := hL.nodup
  have hW2 : ∀ x, opOf hc x = some (.write 2) → x = (0, 1) := by
    rintro ⟨p, k⟩ hx
    have hp : p = 0 ∨ p = 1 ∨ p = 2 := by fin_cases p <;> simp
    rcases hp with rfl | rfl | rfl <;> simp only [opOf, hc_ops0, hc_ops1, hc_ops2] at hx <;>
      rcases k with _ | _ | k <;> simp at hx ⊢
  have hcE : Completed hc (2, 0) := by simp [Completed, hc_resps2]
  have hcE2 : Completed hc (2, 1) := by simp [Completed, hc_resps2]
  have hcW3 : Completed hc (1, 0) := by simp [Completed, hc_resps1]
  have hpE : Precedes hc (2, 0) (1, 0) :=
    ⟨hc.take 5, hc.drop 5, (List.take_append_drop 5 _).symm,
      by show 0 < (respsOf (hc.take 5) 2).length; decide,
      by show ¬ 0 < (opsOf (hc.take 5) 1).length; decide⟩
  have hpW3 : Precedes hc (1, 0) (2, 1) :=
    ⟨hc.take 7, hc.drop 7, (List.take_append_drop 7 _).symm,
      by show 0 < (respsOf (hc.take 7) 1).length; decide,
      by show ¬ 1 < (opsOf (hc.take 7) 2).length; decide⟩
  have hmE := hL.complete _ hcE
  have hmE2 := hL.complete _ hcE2
  have hmW3 := hL.complete _ hcW3
  have hEW3 := hL.realtime _ _ hpE hmW3
  have hW3E2 := hL.realtime _ _ hpW3 hmE2
  -- the first read returns `2`: `Write(2)` comes before it
  have hW2E : [((0 : Fin 3), 1), ((2 : Fin 3), 0)] <+ L.map Prod.fst := by
    obtain ⟨⟨x, o⟩, hxm, hx⟩ := List.mem_map.1 hmE
    simp only at hx; subst hx
    obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hxm
    have ho : o = .read := by
      have := hL.op_eq _ hxm
      simp only [opOf, hc_ops2] at this
      simpa using this.symm
    subst ho
    have hr := resp_of_split hL hsplit (r := 2) (by simp [respOf, hc_resps2])
    simp only [register_read] at hr
    rcases reg_runOps hr with h0 | hw
    · exact absurd h0 (by decide)
    obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hw
    have hzW := hW2 z.1 (by rw [hL.op_eq z (by rw [hsplit]; simp [hz]), hz2])
    rw [hsplit, List.map_append, List.map_cons]
    exact List.Sublist.append (List.singleton_sublist.2 (List.mem_map.2 ⟨z, hz, hzW⟩))
      (List.singleton_sublist.2 (by simp))
  -- the second read returns `2` although `Write(3)` precedes it: `Write(2)` comes after `Write(3)`
  have hW3W2 : [((1 : Fin 3), 0), ((0 : Fin 3), 1)] <+ L.map Prod.fst := by
    obtain ⟨⟨x, o⟩, hxm, hx⟩ := List.mem_map.1 hmE2
    simp only at hx; subst hx
    obtain ⟨M₁, M₂, hsplit⟩ := List.append_of_mem hxm
    have ho : o = .read := by
      have := hL.op_eq _ hxm
      simp only [opOf, hc_ops2] at this
      simpa using this.symm
    subst ho
    have hr := resp_of_split hL hsplit (r := 2) (by simp [respOf, hc_resps2])
    simp only [register_read] at hr
    have hW3in : ((1 : Fin 3), 0) ∈ M₁.map Prod.fst := by
      rw [hsplit, List.map_append, List.map_cons] at hW3E2 hnd
      exact mem_of_sublist_pair hnd hW3E2
    obtain ⟨⟨y, o3⟩, hym, hy⟩ := List.mem_map.1 hW3in
    simp only at hy; subst hy
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hym
    have ho3 : o3 = .write 3 := by
      have := hL.op_eq ((1, 0), o3) (by rw [hsplit, hAB]; simp)
      simp only [opOf, hc_ops1] at this
      simpa using this.symm
    subst ho3
    rw [hAB, List.map_append, List.map_cons, ObjSpec.runOps_append, ObjSpec.runOps_cons,
      register_write] at hr
    rcases reg_runOps hr with h0 | hw
    · exact absurd h0 (by decide)
    obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hw
    have hzW := hW2 z.1 (by rw [hL.op_eq z (by rw [hsplit, hAB]; simp [hz]), hz2])
    rw [hsplit, hAB]
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    refine List.Sublist.cons_cons _ ?_
    exact (List.singleton_sublist.2 (List.mem_map.2 ⟨z, hz, hzW⟩)).trans
      (List.sublist_append_left _ _)
  exact not_sublist_pair_both hnd (sublist_pair_trans hnd hW2E hEW3) hW3W2

/-- The sub-history `Λ_1` of `A[0]` (operations of the calls with timestamp `1`: `SWrite(1)` of
the first `Write` and the `Oper` of the first read) has no overlapping `SWrite` but is not
linearizable, although the whole history of `A[0]` is (`cex_seqWritable`): sequential
writability cannot be applied to `Λ_ℓ` as in the proof of Claim 4.7. -/
theorem lambda1_not_linearizable :
    ¬ ∃ L, IsLinearization ([.inv 0 (.write 1), .ret 0 1, .inv 2 .read, .ret 2 2] :
      List (Label (Fin 3) R)) L := by
  rintro ⟨L, hL⟩
  have hm := hL.complete (2, 0) (by show 0 < (respsOf _ 2).length; decide)
  obtain ⟨⟨x, o⟩, hxm, hx⟩ := List.mem_map.1 hm
  simp only at hx; subst hx
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hxm
  have ho : o = .read := by
    have := hL.op_eq _ hxm
    have h2 : opOf ([.inv 0 (.write 1), .ret 0 1, .inv 2 .read, .ret 2 2] :
      List (Label (Fin 3) R)) (2, 0) = some .read := by decide
    rw [h2] at this; exact (Option.some.inj this).symm
  subst ho
  have hr := resp_of_split hL hsplit (r := 2) (by decide)
  simp only [register_read] at hr
  rcases reg_runOps hr with h0 | hw
  · exact absurd h0 (by decide)
  obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hw
  have hop := hL.op_eq z (by rw [hsplit]; simp [hz])
  rw [hz2] at hop
  generalize z.1 = y at hop
  obtain ⟨p, k⟩ := y
  have h0 : opsOf ([.inv 0 (.write 1), .ret 0 1, .inv 2 .read, .ret 2 2] :
    List (Label (Fin 3) R)) 0 = [.write 1] := by decide
  have h1 : opsOf ([.inv 0 (.write 1), .ret 0 1, .inv 2 .read, .ret 2 2] :
    List (Label (Fin 3) R)) 1 = [] := by decide
  have h2 : opsOf ([.inv 0 (.write 1), .ret 0 1, .inv 2 .read, .ret 2 2] :
    List (Label (Fin 3) R)) 2 = [.read] := by decide
  have hp : p = 0 ∨ p = 1 ∨ p = 2 := by fin_cases p <;> simp
  rcases hp with rfl | rfl | rfl <;> simp only [opOf, h0, h1, h2] at hop <;>
    rcases k with _ | k <;> simp at hop

/-- Summary: dropping the "not in use" requirement from the template, Lemma 4.5 fails. -/
theorem notInUse_necessary : ∃ (α : List (Ev (Fin 3) (Fin 2) R)) (σ : Fin 3 → ℕ → PSt (Fin 2) R),
    IsCtrl regW own α σ ∧ ¬ NotInUse α ∧ CondC α ∧ (∀ i, SeqWritable regW (lowH regW i α)) ∧
      ¬ ∃ L, IsLinearization (highH regW α) L :=
  ⟨cex, ctl, cex_ctrl, cex_not_notInUse, cex_condC, cex_seqWritable, cex_not_linearizable⟩

end Podc.WritableObjects.Counterexample
