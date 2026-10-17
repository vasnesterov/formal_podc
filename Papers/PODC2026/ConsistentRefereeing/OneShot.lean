import Papers.PODC2026.ConsistentRefereeing.Defs
import Cslib.Computability.Distributed.SharedMemory.Covering
import Cslib.Computability.Distributed.SharedMemory.SWSRRegister
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Solo
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Nat.Descent
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Valency for the one-shot contest object

Infrastructure for Theorem 5 of [ACE26]: fix an implementation `I` of the one-shot contest
object `contestObj P` with referee `ref`.

* `Val I ref α` — the *valency* of an admissible execution `α`: the competitors `w` such that, in
  some admissible extension of `α`, the referee's `decide` returns `w` (paper: `α` is
  `v`-univalent if `Val α = {v}`, multivalent if it has two elements).
* `decide_some` — with linearizability, `decide` never returns `false` in admissible executions
  (the referee starts after a `compete` completed).
* `val_subsingleton` — **Claim 9**: with strong linearizability, once some `compete` has completed
  the execution is univalent. This is the only use of strong linearizability.
* `nxt` — the unique next label of a process in admissible executions (`nxt_eq`).
* `obstructionFreeOn` — lock-freedom on admissible executions gives obstruction-freedom on them,
  so pending operations can be finished by solo runs (`Impl.exists_finish`).
* `exists_common` — the *key lemma* of every case of the proof: two admissible executions whose
  final configurations agree on the memory, the referee and some competitor `k` (with the same
  invocation status) have a common value in their valencies (run `k` solo to completion, then
  the referee).
* `exists_critical` — **Claim 10**: there is a critical execution.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Referee

open Impl

variable {P ι L : Type} {B : ι → ObjSpec}

/-! ## Facts about the sequential specification -/

section Spec

lemma runOps_of_compete {c : P} {os : List (ContestOp P)} (h : .compete c ∈ os)
    (s : Option P) : ∃ w, (contestObj P).runOps s os = some w := by
  induction os generalizing s with
  | nil => simp at h
  | cons o os ih =>
    rcases List.mem_cons.1 h with rfl | h
    · rw [ObjSpec.runOps_cons]
      cases s with
      | none => exact ⟨c, runOps_some c os⟩
      | some w => exact ⟨w, runOps_some w os⟩
    · rw [ObjSpec.runOps_cons]; exact ih h _

lemma runOps_none_eq_some {w : P} {os : List (ContestOp P)}
    (h : (contestObj P).runOps none os = some w) : .compete w ∈ os := by
  induction os with
  | nil => simp [ObjSpec.runOps] at h
  | cons o os ih =>
    rw [ObjSpec.runOps_cons] at h
    cases o with
    | decide => exact List.mem_cons_of_mem _ (ih h)
    | compete i =>
      have : ((contestObj P).δ none (.compete i)).1 = some i := rfl
      rw [this, runOps_some] at h
      cases h; exact List.mem_cons_self

variable [DecidableEq P]

/-- After a state `some w`, the referee's `decide` returns `winner (some w)`. -/
lemma respIn_decide {x : OpId P} {w : P} {M : List (OpId P × ContestOp P)}
    (hM : ∀ y ∈ M, y.1 = x → y.2 = .decide) {r : ContestResp P}
    (h : (contestObj P).respIn (some w) M x = some r) : r = .winner (some w) := by
  induction M with
  | nil => simp [ObjSpec.respIn, linRespFrom] at h
  | cons y M ih =>
    obtain ⟨y, o⟩ := y
    by_cases hy : y = x
    · subst hy
      have := hM (y, o) (by simp) rfl; simp only at this; subst this
      simp only [ObjSpec.respIn, linRespFrom, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy] at h
      have hs : ((contestObj P).δ (some w) o).1 = some w := by cases o <;> rfl
      rw [hs] at h
      exact ih (fun y' hy' => hM y' (by simp [hy'])) h

end Spec

variable [DecidableEq P] [DecidableEq ι] (I : Impl (contestObj P) B P L) (ref : P)

/-! ## The referee never returns `false` -/

lemma opsOf_eq_split {α : List (Label P (contestObj P))} {p : P} {o : ContestOp P}
    (h : opsOf α p = [o]) : ∃ β γ, α = β ++ .inv p o :: γ ∧ opsOf β p = [] := by
  induction α with
  | nil => simp at h
  | cons ℓ α ih =>
    rw [opsOf_cons] at h
    cases hℓ : ℓ.invOf p with
    | none =>
      rw [hℓ] at h
      obtain ⟨β, γ, rfl, hβ⟩ := ih (by simpa using h)
      exact ⟨ℓ :: β, γ, rfl, by simp [opsOf_cons, hℓ, hβ]⟩
    | some o' =>
      rw [hℓ] at h
      simp only [Option.toList_some, List.singleton_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      cases ℓ with
      | inv q o'' =>
        simp only [Label.invOf_inv] at hℓ
        split_ifs at hℓ with hq
        · subst hq; cases hℓ; exact ⟨[], α, rfl, rfl⟩
      | ret q r => simp at hℓ
      | tau q => simp at hℓ

omit [DecidableEq ι] in
lemma Adm.opOf_eq {α : List (Label P (contestObj P))} (hA : Adm ref α) {x : OpId P}
    (hx : Invoked α x) : opOf α x = some (roleOp ref x.1) := by
  simp only [opOf]
  simp only [Invoked] at hx
  rw [List.getElem?_eq_getElem hx]
  exact congrArg some (hA.role _ _ (List.getElem_mem _))

omit [DecidableEq ι] in
lemma Adm.op_eq_of_mem {α : List (Label P (contestObj P))} (hA : Adm ref α)
    {Lin : List (OpId P × ContestOp P)} (hL : IsLinearization α Lin) {y : OpId P × ContestOp P}
    (hy : y ∈ Lin) : y.2 = roleOp ref y.1.1 := by
  have h1 := hL.op_eq y hy
  rw [hA.opOf_eq ref (Invoked.of_opOf_eq_some h1)] at h1
  exact (Option.some_inj.1 h1).symm

/-- In an admissible execution with a linearization, a response of the referee's `decide` is
`winner (some w)`: the referee starts after some `compete` completed, so `decide` is linearized
after it. -/
lemma decide_some {α : List (Label P (contestObj P))} (hV : I.Valid α) (hA : Adm ref α)
    {Lin : List (OpId P × ContestOp P)} (hL : IsLinearization α Lin) {r : ContestResp P}
    (hr : respOf α (ref, 0) = some r) :
    ∃ w, r = .winner (some w) ∧ w ≠ ref ∧ opsOf α w ≠ [] := by
  have hc' : Completed α (ref, 0) := Completed.of_respOf_eq_some hr
  have hinv := (Impl.Valid.wellFormed I hV).invoked_of_completed hc'
  -- the invocation of the referee
  have hops : opsOf α ref = [.decide] := by
    have h1 := hA.oneShot ref
    simp only [Invoked] at hinv
    obtain ⟨o, ho⟩ : ∃ o, opsOf α ref = [o] := by
      match h : opsOf α ref, h1, hinv with
      | [o], _, _ => exact ⟨o, rfl⟩
    have := hA.role ref o (by rw [ho]; simp)
    rw [ho, this]; simp [roleOp]
  obtain ⟨β, γ, hsplit, hβ⟩ := opsOf_eq_split hops
  obtain ⟨c, hcref, hc⟩ := hA.late β γ _ hsplit
  have hcomp : Completed β (c, 0) := by
    simp only [Completed]; exact List.length_pos_of_ne_nil hc
  have hprec : Precedes α (c, 0) (ref, 0) :=
    ⟨β, .inv ref .decide :: γ, hsplit, hcomp, by simp [Invoked, hβ]⟩
  have hrefL : (ref, 0) ∈ Lin.map Prod.fst := hL.complete _ hc'
  have hsub := hL.realtime _ _ hprec hrefL
  obtain ⟨r₁, r₂, hr12, hcmem, hrefsub⟩ := List.cons_sublist_iff.1 hsub
  obtain ⟨L₁, L₂, hLin, hL₁, hL₂⟩ := List.map_eq_append_iff.1 hr12
  have hrefL₂ : (ref, 0) ∈ L₂.map Prod.fst := by
    rw [hL₂]; exact List.singleton_sublist.1 hrefsub
  have hnd := hL.nodup
  rw [hLin, List.map_append] at hnd
  have hrefL₁ : (ref, 0) ∉ L₁.map Prod.fst := by
    intro h; exact List.disjoint_of_nodup_append hnd h hrefL₂
  -- the state after `L₁` is `some w`
  obtain ⟨y, hyL₁, hy⟩ := List.mem_map.1 (hL₁ ▸ hcmem)
  have hyop : y.2 = .compete c := by
    rw [hA.op_eq_of_mem ref hL (hLin ▸ List.mem_append_left _ hyL₁), hy]
    simp [roleOp, hcref]
  obtain ⟨w, hw⟩ := runOps_of_compete (c := c) (os := L₁.map Prod.snd)
    (List.mem_map.2 ⟨y, hyL₁, hyop⟩) (contestObj P).init
  have hres := hL.respIn_eq hr
  rw [hLin, ObjSpec.respIn_append_of_not_mem hrefL₁, hw] at hres
  refine ⟨w, respIn_decide (fun y' hy' hy'1 => ?_) hres, ?_⟩
  · rw [hA.op_eq_of_mem ref hL (hLin ▸ List.mem_append_right _ hy'), hy'1]
    simp [roleOp]
  · -- `w` invoked `compete`
    obtain ⟨z, hzL, hz⟩ := List.mem_map.1 (runOps_none_eq_some hw)
    have hzop := hA.op_eq_of_mem ref hL (hLin ▸ List.mem_append_left _ hzL)
    rw [hz] at hzop
    have hzw : z.1.1 = w ∧ w ≠ ref := by
      by_cases hh : z.1.1 = ref
      · simp [roleOp, hh] at hzop
      · simp only [roleOp, hh, ↓reduceIte, ContestOp.compete.injEq] at hzop
        exact ⟨hzop.symm, hzop ▸ hh⟩
    refine ⟨hzw.2, ?_⟩
    have := Invoked.of_opOf_eq_some (hL.op_eq z (hLin ▸ List.mem_append_left _ hzL))
    simp only [Invoked, hzw.1] at this
    exact List.ne_nil_of_length_pos (by omega)

/-! ## Valency -/

/-- The *valency* of an execution `α`: the competitors `w` such that the referee's `decide`
returns `w` in some admissible extension of `α`. -/
def Val (α : List (Label P (contestObj P))) : Set P :=
  {w | ∃ β, I.Valid (α ++ β) ∧ Adm ref (α ++ β) ∧
    respOf (α ++ β) (ref, 0) = some (.winner (some w))}

/-- `α` is *multivalent*. -/
def Multi (α : List (Label P (contestObj P))) : Prop :=
  ∃ w₁ w₂, w₁ ≠ w₂ ∧ w₁ ∈ Val I ref α ∧ w₂ ∈ Val I ref α

lemma val_mono {α β : List (Label P (contestObj P))} {w : P} (h : w ∈ Val I ref (α ++ β)) :
    w ∈ Val I ref α := by
  obtain ⟨γ, h1, h2, h3⟩ := h
  exact ⟨β ++ γ, by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- The outcome of every extension is determined by `h α` once a `compete` is linearized. -/
lemma val_cases {α : List (Label P (contestObj P))}
    (hV : I.Valid α) (hA : Adm ref α) {c : P} (hc : c ≠ ref) (hcomp : respsOf α c ≠ [])
    {h : List (Label P (contestObj P)) → List (OpId P × ContestOp P)}
    (hlin : ∀ α, I.Valid α → Adm ref α → IsLinearization α (h α))
    (hpre : ∀ α β, I.Valid β → Adm ref β → α <+: β → h α <+: h β)
    {w : P} (hw : w ∈ Val I ref α) :
    (contestObj P).respIn (contestObj P).init (h α) (ref, 0) = some (ContestResp.winner (some w)) ∨
      ((ref, 0) ∉ (h α).map Prod.fst ∧ linState (A := contestObj P) (h α) = some w) := by
  obtain ⟨β, hVβ, hAβ, hr⟩ := hw
  have hL := hlin _ hVβ hAβ
  have hres := hL.respIn_eq hr
  obtain ⟨M, hM⟩ := hpre α (α ++ β) hVβ hAβ (List.prefix_append _ _)
  rw [← hM] at hres hL
  by_cases hmem : (ref, 0) ∈ (h α).map Prod.fst
  · left; rwa [ObjSpec.respIn_append_of_mem hmem] at hres
  · right
    refine ⟨hmem, ?_⟩
    rw [ObjSpec.respIn_append_of_not_mem hmem] at hres
    -- `h α` contains the completed `compete` of `c`
    have hcα : Completed α (c, 0) := List.length_pos_of_ne_nil hcomp
    have hcL := (hlin α hV hA).complete _ hcα
    obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hcL
    have hyop : y.2 = .compete c := by
      rw [hA.op_eq_of_mem ref (hlin α hV hA) hy, hy1]; simp [roleOp, hc]
    obtain ⟨w₀, hw₀⟩ := runOps_of_compete (c := c) (os := (h α).map Prod.snd)
      (List.mem_map.2 ⟨y, hy, hyop⟩) (contestObj P).init
    rw [hw₀] at hres
    rw [show linState (A := contestObj P) (h α) = some w₀ from hw₀]
    have := respIn_decide (fun y' hy' hy'1 => by
      rw [hAβ.op_eq_of_mem ref hL (List.mem_append_right _ hy'), hy'1]; simp [roleOp]) hres
    simp only [ContestResp.winner.injEq, Option.some.injEq] at this
    rw [this]

/-- **Claim 9 of [ACE26].** With a strong linearization function, an admissible execution in
which some `compete` has completed is univalent. -/
theorem val_subsingleton (hsl : I.StrongLinOn (Adm ref)) {α : List (Label P (contestObj P))}
    (hV : I.Valid α) (hA : Adm ref α) {c : P} (hc : c ≠ ref) (hcomp : respsOf α c ≠ []) :
    (Val I ref α).Subsingleton := by
  obtain ⟨h, hlin, hpre⟩ := hsl
  intro w₁ hw₁ w₂ hw₂
  rcases val_cases I ref hV hA hc hcomp hlin hpre hw₁ with h1 | ⟨h1, h1'⟩ <;>
  rcases val_cases I ref hV hA hc hcomp hlin hpre hw₂ with h2 | ⟨h2, h2'⟩
  · rw [h1] at h2; simpa using h2
  · exact absurd (ObjSpec.mem_of_respIn_eq_some h1) h2
  · exact absurd (ObjSpec.mem_of_respIn_eq_some h2) h1
  · rw [h1'] at h2'; simpa using h2'

/-! ## Admissible extensions and next labels -/

omit [DecidableEq ι] in
lemma split_append_singleton {α β γ : List (Label P (contestObj P))} {ℓ x : Label P (contestObj P)}
    (h : α ++ [ℓ] = β ++ x :: γ) : (β = α ∧ x = ℓ ∧ γ = []) ∨ ∃ γ', α = β ++ x :: γ' := by
  rcases γ.eq_nil_or_concat with rfl | ⟨γ', y, rfl⟩
  · left
    obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
    simp only [List.cons.injEq] at h2
    exact ⟨h1.symm, h2.1.symm, rfl⟩
  · right
    have h' : α ++ [ℓ] = (β ++ x :: γ') ++ [y] := by simpa using h
    obtain ⟨h1, -⟩ := List.append_inj' h' rfl
    exact ⟨γ', h1⟩

omit [DecidableEq ι] in
/-- Appending labels without invocations preserves admissibility. -/
lemma Adm.append_noInv {α β : List (Label P (contestObj P))} (hA : Adm ref α)
    (hops : ∀ q, opsOf β q = []) : Adm ref (α ++ β) := by
  have hβ : ∀ o, (Label.inv ref o : Label P (contestObj P)) ∉ β := fun o h => by
    have : o ∈ opsOf β ref := by
      obtain ⟨β₁, β₂, rfl⟩ := List.append_of_mem h; simp [opsOf_append]
    simp [hops] at this
  refine ⟨fun p => by simpa [hops] using hA.oneShot p, fun p o ho => ?_, fun β' γ o h => ?_⟩
  · simp only [opsOf_append, hops, List.append_nil] at ho; exact hA.role p o ho
  · -- the invocation lies in `α`
    rcases List.append_eq_append_iff.1 h with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
    · -- `β = a' ++ inv ref o :: γ`
      exact absurd (by rw [h2]; simp) (hβ o)
    · rcases c' with _ | ⟨z, c'⟩
      · simp only [List.nil_append] at h2
        exact absurd (by rw [← h2]; simp) (hβ o)
      · simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact hA.late β' c' _ h1

omit [DecidableEq ι] in
/-- Appending the role invocation of a process that has not invoked yet. -/
lemma Adm.append_inv {α : List (Label P (contestObj P))} (hA : Adm ref α) {p : P}
    (hp : opsOf α p = []) (hlate : p = ref → ∃ c, c ≠ ref ∧ respsOf α c ≠ []) :
    Adm ref (α ++ [.inv p (roleOp ref p)]) := by
  refine ⟨fun q => ?_, fun q o ho => ?_, fun β γ o h => ?_⟩
  · by_cases hq : p = q
    · subst hq; simp [opsOf_append, hp]
    · simpa [opsOf_append, hq] using hA.oneShot q
  · simp only [opsOf_append, opsOf_cons, opsOf_nil, Label.invOf_inv, List.append_nil,
      List.mem_append] at ho
    rcases ho with ho | ho
    · exact hA.role q o ho
    · by_cases hq : p = q
      · subst hq; simp at ho; exact ho
      · simp [hq] at ho
  · rcases split_append_singleton h with ⟨rfl, hx, rfl⟩ | ⟨γ', hγ'⟩
    · cases hx; exact hlate rfl
    · exact hA.late β γ' o hγ'

/-- The next label of process `p` after the execution `α` ending in `C`: its role invocation if
it has not invoked yet, its next step if it is pending, none if it has returned. -/
noncomputable def nxt (α : List (Label P (contestObj P))) (C : Config (contestObj P) B P L)
    (p : P) : Option (Label P (contestObj P)) :=
  if opsOf α p = [] then some (.inv p (roleOp ref p))
  else if C.pend p = none then none else some (I.nextLabel C p)

omit [DecidableEq ι] in
lemma nxt_proc {α : List (Label P (contestObj P))} {C : Config (contestObj P) B P L} {p : P}
    {ℓ : Label P (contestObj P)} (h : nxt I ref α C p = some ℓ) : ℓ.proc = p := by
  unfold nxt at h
  split_ifs at h
  · cases h; rfl
  · cases h; exact I.nextLabel_proc C p

/-- In admissible executions, every label is the next label of its process. -/
lemma nxt_eq {α : List (Label P (contestObj P))} {C C' : Config (contestObj P) B P L}
    (hC : I.run α = some C) {ℓ : Label P (contestObj P)} (hA : Adm ref (α ++ [ℓ]))
    (hs : I.step C ℓ = some C') : nxt I ref α C ℓ.proc = some ℓ := by
  cases ℓ with
  | inv p o =>
    have h1 := hA.oneShot p
    have h2 := hA.role p o (by simp [opsOf_append])
    simp only [opsOf_append, opsOf_cons, opsOf_nil, Label.invOf_inv, ite_true, List.append_nil,
      List.length_append, Option.toList_some, List.length_singleton] at h1
    have h3 : opsOf α p = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [nxt, Label.proc, h3, h2]
  | tau p =>
    obtain ⟨h1, -, i, o, k, hact, -⟩ := step_tau hs
    simp only [nxt, Label.proc, Impl.opsOf_ne_nil_of_pend hC h1, h1, ite_false]
    simp [nextLabel, hact]
  | ret p r =>
    obtain ⟨h1, -, -, l, hact, -⟩ := step_ret hs
    simp only [nxt, Label.proc, Impl.opsOf_ne_nil_of_pend hC h1, h1, ite_false]
    simp [nextLabel, hact]

/-- Next labels are enabled and keep executions admissible (for the referee: once some
competitor completed). -/
lemma nxt_step (hallow : ∀ p, I.allowed p (roleOp ref p)) {α : List (Label P (contestObj P))}
    {C : Config (contestObj P) B P L} (hC : I.run α = some C) (hA : Adm ref α) {p : P}
    {ℓ : Label P (contestObj P)} (h : nxt I ref α C p = some ℓ)
    (hlate : p = ref → ∃ c, c ≠ ref ∧ respsOf α c ≠ []) :
    ∃ C', I.step C ℓ = some C' ∧ Adm ref (α ++ [ℓ]) := by
  unfold nxt at h
  split_ifs at h with h1 h2
  · cases h
    have hs : (I.step C (.inv p (roleOp ref p))).isSome := by
      simp [step, pend_none_of_opsOf_nil hC h1, hallow p]
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨C', hC', hA.append_inv ref h1 hlate⟩
  · cases h
    obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome C p h2)
    refine ⟨C', hC', hA.append_noInv ref fun q => ?_⟩
    simp [opsOf_cons, I.nextLabel_invOf C p q]

/-- The next label of a process is not affected by other processes' steps. -/
lemma nxt_other {α : List (Label P (contestObj P))} {C C' : Config (contestObj P) B P L}
    {ℓ : Label P (contestObj P)} (hs : I.step C ℓ = some C') {q : P} (hq : ℓ.proc ≠ q) :
    nxt I ref (α ++ [ℓ]) C' q = nxt I ref α C q := by
  have h1 : opsOf (α ++ [ℓ]) q = opsOf α q := by
    simp [opsOf_append, Label.invOf_eq_none_of_proc_ne hq]
  obtain ⟨hl, hp⟩ := step_other hs hq
  simp only [nxt, h1, hp, nextLabel, hl]

/-! ## Solo termination -/

/-- Lock-freedom on admissible executions gives obstruction-freedom on them (admissible
executions are closed under prefixes and internal steps). -/
theorem obstructionFreeOn (hlf : I.LockFreeOn (Adm ref)) : I.ObstructionFreeOn (Adm ref) :=
  hlf.obstructionFreeOn (fun _ _ h => h.of_append) fun _ _ h => h.append_noInv ref fun _ => by simp

/-! ## The key lemma -/

lemma respsOf_eq_nil_of_opsOf {α : List (Label P (contestObj P))}
    {C : Config (contestObj P) B P L} (hC : I.run α = some C) {p : P} (hp : opsOf α p = []) :
    respsOf α p = [] := by
  rcases I.run_counts hC p with ⟨-, h⟩ | ⟨-, h⟩
  · rw [hp] at h; exact List.eq_nil_of_length_eq_zero (by simpa using h.symm)
  · rw [hp] at h; simp at h

/-- Process `k` runs solo until it has no pending operation (`Impl.exists_finish` for one
process). -/
lemma solo_finish (hlf : I.LockFreeOn (Adm ref)) {α : List (Label P (contestObj P))}
    {C : Config (contestObj P) B P L} (hα : I.run α = some C) (hA : Adm ref α) (k : P) :
    ∃ β D, I.runFrom C β = some D ∧ D.pend k = none ∧ (∀ ℓ ∈ β, ℓ.proc = k) ∧
      ∀ q, opsOf β q = [] := by
  obtain ⟨β, D, hp, hops, hD, hk, -⟩ := I.exists_finish (obstructionFreeOn I ref hlf)
    (fun _ _ h => h.append_noInv ref) [k] hα hA
  exact ⟨β, D, hD, hk k (by simp), fun ℓ hℓ => by simpa using hp ℓ hℓ, hops⟩

/-- **Key lemma.** Two admissible executions, in which the referee has not invoked yet and
competitor `k` has invoked, whose final configurations agree on the memory, `k` and the referee,
have a common value in their valencies: run `k` solo to completion, then the referee. (The value
is a competitor that invoked `compete` in the first execution.) -/
theorem exists_common (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p))
    {α₁ α₂ : List (Label P (contestObj P))} {C₁ C₂ : Config (contestObj P) B P L}
    (h₁ : I.run α₁ = some C₁) (h₂ : I.run α₂ = some C₂) (hA₁ : Adm ref α₁) (hA₂ : Adm ref α₂)
    (href₁ : opsOf α₁ ref = []) (href₂ : opsOf α₂ ref = []) {k : P} (hk : k ≠ ref)
    (hk₁ : opsOf α₁ k ≠ []) (hk₂ : opsOf α₂ k ≠ []) (hag : Impl.AgreeOn {k, ref} C₁ C₂) :
    ∃ w, w ∈ Val I ref α₁ ∧ w ∈ Val I ref α₂ ∧ w ≠ ref ∧ opsOf α₁ w ≠ [] := by
  obtain ⟨hlinf, hlin, -⟩ := hsl
  -- `k` runs solo to completion
  obtain ⟨β, D₁, hD₁, hD₁k, hβp, hβops⟩ := solo_finish I ref hlf h₁ hA₁ k
  obtain ⟨D₂, hD₂, hagD⟩ := runFrom_agreeOn hag (fun ℓ hℓ => by simp [hβp ℓ hℓ]) hD₁
  have hr₁ : I.run (α₁ ++ β) = some D₁ := by rw [run_append_of_eq I h₁, hD₁]
  have hr₂ : I.run (α₂ ++ β) = some D₂ := by rw [run_append_of_eq I h₂, hD₂]
  have hAβ₁ := hA₁.append_noInv ref hβops
  have hAβ₂ := hA₂.append_noInv ref hβops
  have hopsβ : ∀ α' : List (Label P (contestObj P)), ∀ q, opsOf (α' ++ β) q = opsOf α' q :=
    fun α' q => by simp [opsOf_append, hβops q]
  have hD₂k : D₂.pend k = none := by rw [← hagD.pend k (by simp)]; exact hD₁k
  have hcomp₁ : respsOf (α₁ ++ β) k ≠ [] :=
    Impl.respsOf_ne_nil_of_idle hr₁ hD₁k (by rw [hopsβ]; exact hk₁)
  have hcomp₂ : respsOf (α₂ ++ β) k ≠ [] :=
    Impl.respsOf_ne_nil_of_idle hr₂ hD₂k (by rw [hopsβ]; exact hk₂)
  -- the referee invokes `decide`
  have hrr : roleOp ref ref = (.decide : ContestOp P) := by simp [roleOp]
  have hnx : nxt I ref (α₁ ++ β) D₁ ref = some (.inv ref .decide) := by
    simp [nxt, hopsβ, href₁, hrr]
  obtain ⟨E₁, hE₁, hAE₁⟩ := nxt_step I ref hallow hr₁ hAβ₁ hnx (fun _ => ⟨k, hk, hcomp₁⟩)
  obtain ⟨E₂, hE₂, hagE⟩ := step_agreeOn hagD (by simp [Label.proc]) hE₁
  have hAE₂ : Adm ref (α₂ ++ β ++ [.inv ref .decide]) := by
    rw [← hrr]; exact hAβ₂.append_inv ref (by rw [hopsβ]; exact href₂) (fun _ => ⟨k, hk, hcomp₂⟩)
  have hrE₁ : I.run (α₁ ++ β ++ [.inv ref .decide]) = some E₁ := by
    rw [run_append_of_eq I hr₁, runFrom_singleton, hE₁]
  have hrE₂ : I.run (α₂ ++ β ++ [.inv ref .decide]) = some E₂ := by
    rw [run_append_of_eq I hr₂, runFrom_singleton, hE₂]
  -- the referee runs solo to completion
  obtain ⟨γ, F₁, hF₁, hF₁r, hγp, hγops⟩ := solo_finish I ref hlf hrE₁ hAE₁ ref
  obtain ⟨F₂, hF₂, hagF⟩ := runFrom_agreeOn hagE (fun ℓ hℓ => by simp [hγp ℓ hℓ]) hF₁
  set δ : List (Label P (contestObj P)) := β ++ [.inv ref .decide] ++ γ with hδ
  have hrF₁ : I.run (α₁ ++ δ) = some F₁ := by
    rw [hδ, ← List.append_assoc, ← List.append_assoc, run_append_of_eq I hrE₁, hF₁]
  have hrF₂ : I.run (α₂ ++ δ) = some F₂ := by
    rw [hδ, ← List.append_assoc, ← List.append_assoc, run_append_of_eq I hrE₂, hF₂]
  have hAF₁ : Adm ref (α₁ ++ δ) := by
    rw [hδ, ← List.append_assoc, ← List.append_assoc]
    exact hAE₁.append_noInv ref hγops
  have hAF₂ : Adm ref (α₂ ++ δ) := by
    rw [hδ, ← List.append_assoc, ← List.append_assoc]
    exact hAE₂.append_noInv ref hγops
  -- the referee's responses come from `γ`
  have hresps : ∀ α' : List (Label P (contestObj P)), respsOf α' ref = [] →
      respsOf (α' ++ δ) ref = respsOf γ ref := by
    intro α' h'
    have hβr : respsOf β ref = [] :=
      respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hβp ℓ hℓ]; exact hk)
    simp [hδ, respsOf_append, h', hβr]
  have hres₁ := hresps α₁ (respsOf_eq_nil_of_opsOf I h₁ href₁)
  have hres₂ := hresps α₂ (respsOf_eq_nil_of_opsOf I h₂ href₂)
  have hops₁ : opsOf (α₁ ++ δ) ref ≠ [] := by simp [hδ, opsOf_append]
  have hdone := Impl.respsOf_ne_nil_of_idle hrF₁ hF₁r hops₁
  obtain ⟨r, hr⟩ : ∃ r, respOf (α₁ ++ δ) (ref, 0) = some r := by
    simp only [respOf]
    exact ⟨_, List.getElem?_eq_getElem (List.length_pos_of_ne_nil hdone)⟩
  have hr' : respOf (α₂ ++ δ) (ref, 0) = some r := by
    simp only [respOf] at hr ⊢; rw [hres₂, ← hres₁, hr]
  obtain ⟨w, rfl, hwref, hwops⟩ := decide_some I ref ⟨_, hrF₁⟩ hAF₁ (hlin _ ⟨_, hrF₁⟩ hAF₁) hr
  refine ⟨w, ⟨δ, ⟨_, hrF₁⟩, hAF₁, hr⟩, ⟨δ, ⟨_, hrF₂⟩, hAF₂, hr'⟩, hwref, ?_⟩
  -- `δ` invokes only for the referee
  have : opsOf δ w = [] := by
    simp [hδ, opsOf_append, hβops, hγops, Ne.symm hwref]
  rwa [opsOf_append, this, List.append_nil] at hwops

/-- The key lemma, when `k` has the same invocation status in both executions. -/
theorem exists_common_gen (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p))
    {α₁ α₂ : List (Label P (contestObj P))} {C₁ C₂ : Config (contestObj P) B P L}
    (h₁ : I.run α₁ = some C₁) (h₂ : I.run α₂ = some C₂) (hA₁ : Adm ref α₁) (hA₂ : Adm ref α₂)
    (href₁ : opsOf α₁ ref = []) (href₂ : opsOf α₂ ref = []) {k : P} (hk : k ≠ ref)
    (hk₁₂ : opsOf α₁ k = [] ↔ opsOf α₂ k = []) (hag : Impl.AgreeOn {k, ref} C₁ C₂) :
    ∃ w, w ∈ Val I ref α₁ ∧ w ∈ Val I ref α₂ ∧ w ≠ ref ∧ (w = k ∨ opsOf α₁ w ≠ []) := by
  by_cases hk₁ : opsOf α₁ k = []
  · have hk₂ := hk₁₂.1 hk₁
    have hrk : roleOp ref k = .compete k := by simp [roleOp, hk]
    have hnx : nxt I ref α₁ C₁ k = some (.inv k (roleOp ref k)) := by simp [nxt, hk₁]
    obtain ⟨D₁, hD₁, hAD₁⟩ := nxt_step I ref hallow h₁ hA₁ hnx (fun h => absurd h hk)
    obtain ⟨D₂, hD₂, hagD⟩ := step_agreeOn hag (by simp [Label.proc]) hD₁
    have hAD₂ := hA₂.append_inv ref hk₂ (fun h => absurd h hk)
    have hr₁ : I.run (α₁ ++ [.inv k (roleOp ref k)]) = some D₁ := by
      rw [run_append_of_eq I h₁, runFrom_singleton, hD₁]
    have hr₂ : I.run (α₂ ++ [.inv k (roleOp ref k)]) = some D₂ := by
      rw [run_append_of_eq I h₂, runFrom_singleton, hD₂]
    have hops : ∀ α' : List (Label P (contestObj P)), ∀ q,
        opsOf (α' ++ [.inv k (roleOp ref k)]) q = opsOf α' q ++ (if k = q then [roleOp ref k] else []) := by
      intro α' q; by_cases h : k = q <;> simp [opsOf_append, h]
    obtain ⟨w, hw₁, hw₂, hwr, hwo⟩ := exists_common I ref hlf hsl hallow hr₁ hr₂ hAD₁ hAD₂
      (by rw [hops, href₁]; simp [hk]) (by rw [hops, href₂]; simp [hk]) hk
      (by rw [hops]; simp) (by rw [hops]; simp) hagD
    refine ⟨w, val_mono I ref hw₁, val_mono I ref hw₂, hwr, ?_⟩
    rw [hops] at hwo
    by_cases hwk : k = w
    · exact Or.inl hwk.symm
    · right; simpa [hwk] using hwo
  · have hk₂ : opsOf α₂ k ≠ [] := fun h => hk₁ (hk₁₂.2 h)
    obtain ⟨w, hw₁, hw₂, hwr, hwo⟩ :=
      exists_common I ref hlf hsl hallow h₁ h₂ hA₁ hA₂ href₁ href₂ hk hk₁ hk₂ hag
    exact ⟨w, hw₁, hw₂, hwr, Or.inr hwo⟩

/-- The valency of an admissible execution with a pending or idle competitor is nonempty. -/
theorem val_nonempty (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p)) {α : List (Label P (contestObj P))}
    {C : Config (contestObj P) B P L} (h : I.run α = some C) (hA : Adm ref α)
    (href : opsOf α ref = []) {k : P} (hk : k ≠ ref) : (Val I ref α).Nonempty := by
  obtain ⟨w, hw, -⟩ := exists_common_gen I ref hlf hsl hallow h h hA hA href href hk Iff.rfl
    ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  exact ⟨w, hw⟩

/-- **Claim 7 of [ACE26].** Every competitor is in the valency of the empty execution. -/
theorem mem_val_nil (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p)) {c : P} (hc : c ≠ ref) : c ∈ Val I ref [] := by
  have hA : Adm ref ([] : List (Label P (contestObj P))) :=
    ⟨fun _ => by simp, fun _ _ h => by simp at h, fun β γ o h => by simp at h⟩
  obtain ⟨w, hw, -, -, hwc⟩ := exists_common_gen I ref hlf hsl hallow (run_nil I) (run_nil I)
    hA hA (by simp) (by simp) hc Iff.rfl ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  rcases hwc with rfl | h
  · exact hw
  · simp at h

/-! ## Counting invocations -/

lemma Adm.numInv_le [Fintype P] {α : List (Label P (contestObj P))} (hA : Adm ref α) :
    invCount α ≤ Fintype.card P := by
  rw [invCount_eq_sum]
  calc ∑ p, (opsOf α p).length ≤ ∑ _p : P, 1 := Finset.sum_le_sum fun p _ => hA.oneShot p
    _ = Fintype.card P := by simp

/-! ## The critical execution -/

/-- **Claim 10 of [ACE26].** There is a *critical* execution: admissible, the referee has not
invoked, multivalent, and every next step of a competitor leads to an execution that is not
multivalent. -/
theorem exists_critical [Fintype P] (hlf : I.LockFreeOn (Adm ref)) (hsl : I.StrongLinOn (Adm ref))
    (hallow : ∀ p, I.allowed p (roleOp ref p)) {c₁ c₂ : P} (h₁ : c₁ ≠ ref) (h₂ : c₂ ≠ ref)
    (h₁₂ : c₁ ≠ c₂) :
    ∃ α C, I.run α = some C ∧ Adm ref α ∧ opsOf α ref = [] ∧ Multi I ref α ∧
      ∀ c ℓ, c ≠ ref → nxt I ref α C c = some ℓ → ¬ Multi I ref (α ++ [ℓ]) := by
  by_contra H
  push Not at H
  let Good : List (Label P (contestObj P)) → Prop := fun α =>
    (∃ C, I.run α = some C) ∧ Adm ref α ∧ opsOf α ref = [] ∧ Multi I ref α
  have hnext : ∀ α : Subtype Good, ∃ ℓ : Label P (contestObj P), Good (α.1 ++ [ℓ]) := by
    rintro ⟨α, ⟨C, hC⟩, hA, hr, hM⟩
    obtain ⟨c, ℓ, hc, hnx, hM'⟩ := H α C hC hA hr hM
    obtain ⟨C', hC', hA'⟩ := nxt_step I ref hallow hC hA hnx (fun h => absurd h hc)
    have hp := nxt_proc I ref hnx
    refine ⟨ℓ, ⟨C', by rw [run_append_of_eq I hC, runFrom_singleton, hC']⟩, hA', ?_, hM'⟩
    rw [opsOf_append, hr, opsOf_cons, Label.invOf_eq_none_of_proc_ne (by rw [hp]; exact hc)]
    simp
  choose f hf using hnext
  have hA0 : Adm ref ([] : List (Label P (contestObj P))) :=
    ⟨fun _ => by simp, fun _ _ h => by simp at h, fun β γ o h => by simp at h⟩
  let s0 : Subtype Good := ⟨[], ⟨_, run_nil I⟩, hA0, by simp,
    ⟨c₁, c₂, h₁₂, mem_val_nil I ref hlf hsl hallow h₁, mem_val_nil I ref hlf hsl hallow h₂⟩⟩
  let seq : ℕ → Subtype Good := fun n => Nat.rec s0 (fun _ s => ⟨s.1 ++ [f s], hf s⟩) n
  let E : ℕ → List (Label P (contestObj P)) := fun n => (seq n).1
  have hEs : ∀ n, E (n + 1) = E n ++ [f (seq n)] := fun n => rfl
  have hElen : ∀ n, (E n).length = n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [hEs, List.length_append, ih]; rfl
  have hmono : ∀ n, E n <+: E (n + 1) := fun n => by rw [hEs]; exact List.prefix_append _ _
  have hlen : ∀ n, n ≤ (E n).length := fun n => by rw [hElen]
  obtain ⟨e, hlbl, -⟩ := I.exists_infExec_of_chain E hmono hlen (fun n => (seq n).2.1)
  have hlbls : ∀ t, e.pre t = E t := fun t => by
    rw [e.pre_eq_take (hlen t) (hlbl t), List.take_of_length_le (hElen t).le]
  have hadm : ∀ t, Adm ref (e.pre t) := fun t => by rw [hlbls]; exact (seq t).2.2.1
  -- infinitely many steps: at most `card P` invocations
  have hsteps : ∀ N, ∃ m ≥ N, (e.lbl m).IsStep := by
    intro N
    by_contra hno
    push Not at hno
    have hinv : ∀ m ≥ N, ∃ q o, e.lbl m = .inv q o := by
      intro m hm
      cases h : e.lbl m with
      | inv q o => exact ⟨q, o, rfl⟩
      | ret q r => exact absurd (by rw [h]; trivial) (hno m hm)
      | tau q => exact absurd (by rw [h]; trivial) (hno m hm)
    have hgrow : ∀ K, invCount (e.pre N) + K ≤ invCount (e.pre (N + K)) := by
      intro K; induction K with
      | zero => simp
      | succ K ih =>
        show invCount (e.pre N) + (K + 1) ≤ invCount (e.pre ((N + K) + 1))
        rw [InfExec.pre_succ]
        obtain ⟨q, o, hq⟩ := hinv (N + K) (by omega)
        simp only [invCount_append, hq, invCount_cons, invCount_nil, Label.isInv_inv, ite_true] at ih ⊢
        omega
    have := hgrow (Fintype.card P + 1)
    have hle := (hadm (N + (Fintype.card P + 1))).numInv_le ref
    omega
  obtain ⟨m, -, q, r, hr⟩ := hlf e hadm hsteps 0
  -- the response belongs to a competitor and makes the execution univalent
  have hfm : f (seq m) = .ret q r := by
    rw [← hr, hlbl (m + 1) m (by have := hElen (m + 1); omega)]
    simp [hEs, hElen]
  have hlast : E (m + 1) = E m ++ [.ret q r] := by rw [hEs, hfm]
  obtain ⟨⟨C, hC⟩, hA, href, hM⟩ := (seq (m + 1)).2
  have hqr : q ≠ ref := by
    intro hq; subst hq
    have := I.proc_ne_of_opsOf_eq_nil hC href (.ret q r) (by
      show _ ∈ E (m + 1); rw [hlast]; simp)
    exact this rfl
  have hcomp : respsOf (E (m + 1)) q ≠ [] := by rw [hlast]; simp [respsOf_append]
  obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ := hM
  exact hne (val_subsingleton I ref hsl ⟨C, hC⟩ hA hqr hcomp hw₁ hw₂)

end Referee

end Cslib.SharedMemory
