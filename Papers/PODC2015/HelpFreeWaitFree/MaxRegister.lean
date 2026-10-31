import Papers.PODC2015.HelpFreeWaitFree.LinPointHelpFree
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister

/-!
# A help-free wait-free max register from CAS (Figure 4.5 of [CPT15])

[CPT15]: K. Censor-Hillel, E. Petrank, S. Timnat. *Help!* PODC 2015 (full version: Chapter 4 of
S. Timnat's PhD thesis), Section 4.8.2, Figure 4.5:

```
void WriteMax(int key) {
  while (true) {
    int local = value;                 // linearization point if value ≥ key
    if (local ≥ key) return;
    if (cas(value, local, key)) return; // linearization point if the cas succeeds
} }
int ReadMax() { int result = value; return result; } // linearization point
```

## Model
CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`): any set `P` of processes,
deterministic programs, one atomic base object `value`, a compare-and-swap object over `ℕ`
initialized to `0` (CSLib's `casObject ℕ 0`, which supports `read` and `cas` returning a success
flag). The implemented object is CSLib's max register over `ℕ` (`maxRegObj`, initially `0`).
Values are natural numbers (the paper uses `int` with initial value `0`; negative keys are
irrelevant for a max register starting at `0`).

## Results
* `isLinFun_lin` — `lin`, the linearization function derived from the linearization points of
  Figure 4.5, is a linearization function (the implementation is linearizable).
* `linPointFun_lin` — every linearization point is a step of the operation itself.
* `waitFree` — the implementation is wait-free (potential `2 (key - value) + 2` for a
  `WriteMax(key)` about to read: every failed `cas` increases `value`).
* `helpFree` — help-freedom, via Claim 4.8.1 (`helpFree_of_linPointFun`).
* `maxRegister_helpFree_waitFree` — the main statement of Section 4.8.2.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree.MaxRegister

open Cslib.SharedMemory

/-- Program counters of Figure 4.5. -/
inductive Loc where
  /-- No pending operation. -/
  | idle
  /-- `WriteMax(v)` about to read `value` (line 3). -/
  | wRead (v : ℕ)
  /-- `WriteMax(v)` about to execute `cas(value, tmp, v)` (line 6). -/
  | wCas (v tmp : ℕ)
  /-- `WriteMax` about to return (line 5 or 7). -/
  | wDone
  /-- `ReadMax` about to read `value` (line 10). -/
  | rRead
  /-- `ReadMax` about to return `r` (line 11). -/
  | rDone (r : ℕ)

/-- The value carried by a response of the CAS object (`read` returns `inl v`). -/
def val : ℕ ⊕ Bool → ℕ
  | .inl x => x
  | .inr _ => 0

/-- The base objects: a single CAS object `value` over `ℕ`, initially `0`. -/
abbrev Base : Unit → ObjSpec := fun _ => casObject ℕ 0

/-- **Figure 4.5 of [CPT15]**: the max register `maxRegObj` from one CAS object. -/
def impl (P : Type) : Impl maxRegObj Base P Loc where
  memInit _ := 0
  locInit _ := .idle
  invoke _ _ o := match o with
    | .writeMax v => .wRead v
    | .readMax => .rRead
  act _ l := match l with
    | .idle => .ret 0 .idle
    | .wRead v => .access () .read (fun r => if v ≤ val r then .wDone else .wCas v (val r))
    | .wCas v tmp => .access () (.cas tmp v) (fun r => if r = .inr true then .wDone else .wRead v)
    | .wDone => .ret 0 .idle
    | .rRead => .access () .read (fun r => .rDone (val r))
    | .rDone r => .ret r .idle

/-- Configurations of the implementation. -/
abbrev Cfg (P : Type) := Config maxRegObj Base P Loc

variable {P : Type} [DecidableEq P]

/-! ### Steps -/

section Steps

variable {C C' : Cfg P} {p : P}

lemma step_tau_wRead {v : ℕ} (hp : C.pend p ≠ none) (hl : C.loc p = .wRead v)
    (h : (impl P).step C (.tau p) = some C') :
    C' = { C with
      loc := Function.update C.loc p (if v ≤ C.mem () then .wDone else .wCas v (C.mem ())) } := by
  have hact : (impl P).act p (C.loc p) =
      .access () .read (fun r => if v ≤ val r then .wDone else .wCas v (val r)) := by
    rw [hl]; rfl
  rw [Impl.step_tau_eq_some hp hact] at h
  obtain rfl := Option.some.inj h
  congr 1

lemma step_tau_wCas {v tmp : ℕ} (hp : C.pend p ≠ none) (hl : C.loc p = .wCas v tmp)
    (h : (impl P).step C (.tau p) = some C') :
    C' = { C with mem := fun _ => if C.mem () = tmp then v else C.mem (),
                  loc := Function.update C.loc p
                    (if C.mem () = tmp then .wDone else .wRead v) } := by
  have hact : (impl P).act p (C.loc p) =
      .access () (.cas tmp v) (fun r => if r = .inr true then .wDone else .wRead v) := by
    rw [hl]; rfl
  rw [Impl.step_tau_eq_some hp hact] at h
  obtain rfl := Option.some.inj h
  congr 1 <;> funext i
  · by_cases hi : i = p
    · subst hi; by_cases h1 : C.mem () = tmp <;> simp [h1]
    · simp [Function.update_of_ne hi]
  · cases i; by_cases h1 : C.mem () = tmp <;> simp [h1]

lemma step_tau_rRead (hp : C.pend p ≠ none) (hl : C.loc p = .rRead)
    (h : (impl P).step C (.tau p) = some C') :
    C' = { C with loc := Function.update C.loc p (.rDone (C.mem ())) } := by
  have hact : (impl P).act p (C.loc p) = .access () .read (fun r => .rDone (val r)) := by
    rw [hl]; rfl
  rw [Impl.step_tau_eq_some hp hact] at h
  obtain rfl := Option.some.inj h
  congr 1

lemma step_tau_false (hl : C.loc p = .idle ∨ C.loc p = .wDone ∨ ∃ r, C.loc p = .rDone r)
    (h : (impl P).step C (.tau p) = some C') : False := by
  obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
  rcases hl with hl | hl | ⟨r, hl⟩ <;> rw [hl] at hact <;> simp [impl] at hact

end Steps

/-! ### The linearization function derived from the linearization points -/

/-- The entry appended to the linearization by the step `γ` taken from configuration `C` after
the execution `h`: the read of `WriteMax(v)` that sees a value `≥ v`, the successful `cas` of a
`WriteMax`, and the read of `ReadMax` are linearization points. -/
def lpEntry (C : Cfg P) (h : List (Label P maxRegObj)) : Label P maxRegObj →
    Option (OpId P × MaxOp)
  | .tau p => match C.pend p, C.loc p with
    | some o, .wRead v => if v ≤ C.mem () then some (curOp h p, o) else none
    | some o, .wCas _ tmp => if C.mem () = tmp then some (curOp h p, o) else none
    | some o, .rRead => some (curOp h p, o)
    | _, _ => none
  | _ => none

/-- Auxiliary: `lin` on the reversed execution. -/
noncomputable def linRev : List (Label P maxRegObj) → List (OpId P × MaxOp)
  | [] => []
  | γ :: hr => match (impl P).run hr.reverse with
    | some C => linRev hr ++ (lpEntry C hr.reverse γ).toList
    | none => linRev hr

/-- The linearization function of Section 4.8.2: operations ordered by their linearization
points. -/
noncomputable def lin (h : List (Label P maxRegObj)) : List (OpId P × MaxOp) := linRev h.reverse

@[simp] lemma lin_nil : lin ([] : List (Label P maxRegObj)) = [] := rfl

lemma lin_concat {h : List (Label P maxRegObj)} {C : Cfg P} (hC : (impl P).run h = some C)
    (γ : Label P maxRegObj) : lin (h ++ [γ]) = lin h ++ (lpEntry C h γ).toList := by
  simp [lin, linRev, hC]

lemma lpEntry_spec (C : Cfg P) (h : List (Label P maxRegObj)) (γ : Label P maxRegObj) :
    lpEntry C h γ = none ∨ ∃ o, lpEntry C h γ = some (curOp h γ.proc, o) := by
  cases γ with
  | tau p =>
    simp only [lpEntry, Label.proc]
    rcases C.pend p with _ | o
    · simp
    · cases C.loc p <;> simp only [] <;> (try split_ifs) <;> simp
  | inv p o => simp [lpEntry]
  | ret p r => simp [lpEntry]

/-- Every linearization point of Figure 4.5 is a step of the operation itself. -/
theorem linPointFun_lin : LinPointFun (impl P) lin := by
  rintro h γ ⟨C', hv⟩
  rw [Impl.run_concat] at hv
  cases hC : (impl P).run h with
  | none => simp [hC] at hv
  | some C =>
    rw [lin_concat hC]
    rcases lpEntry_spec C h γ with he | ⟨o, he⟩
    · left; simp [he]
    · right; exact ⟨o, by simp [he]⟩

/-! ### The invariant -/

/-- The status of a process with local state `l`, pending operation `pd` and current instance
`x`, relative to the linearization `L` and the value `m` of `value`. -/
def Good (L : List (OpId P × MaxOp)) (m : ℕ) (x : OpId P) (pd : Option MaxOp) : Loc → Prop
  | .idle => pd = none
  | .wRead v => pd = some (.writeMax v) ∧ x ∉ L.map Prod.fst
  | .wCas v tmp => pd = some (.writeMax v) ∧ x ∉ L.map Prod.fst ∧ tmp < v ∧ tmp ≤ m
  | .wDone => ∃ v, pd = some (.writeMax v) ∧ x ∈ L.map Prod.fst
  | .rRead => pd = some .readMax ∧ x ∉ L.map Prod.fst
  | .rDone r => pd ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧
      (maxRegObj.δ (maxRegObj.runOps maxRegObj.init (L₁.map Prod.snd)) o).2 = r

/-- The invariant: `L` (to be `lin α`) is a linearization of `α`, `value` holds the state of the
max register after `L`, and every process is in a status consistent with its linearization
point. -/
structure InvL (α : List (Label P maxRegObj)) (C : Cfg P) (L : List (OpId P × MaxOp)) :
    Prop where
  isLin : IsLinearization α L
  mem : C.mem () = linState (A := maxRegObj) L
  good : ∀ p, Good L (C.mem ()) (curOp α p) (C.pend p) (C.loc p)

/-- The invariant for the linearization `lin α`. -/
abbrev Inv (α : List (Label P maxRegObj)) (C : Cfg P) : Prop := InvL α C (lin α)

lemma good_frame {L N : List (OpId P × MaxOp)} {m m' : ℕ} {x : OpId P} {pd : Option MaxOp}
    {l : Loc} (hN : x ∉ N.map Prod.fst) (hm : m ≤ m') (h : Good L m x pd l) :
    Good (L ++ N) m' x pd l := by
  cases l with
  | idle => exact h
  | wRead v =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h2, hN⟩⟩
  | wCas v tmp =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h2, hN⟩, h3,
      h4.trans hm⟩
  | wDone =>
    obtain ⟨v, h1, h2⟩ := h
    exact ⟨v, h1, by simp only [List.map_append, List.mem_append]; exact Or.inl h2⟩
  | rRead =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h2, hN⟩⟩
  | rDone r =>
    obtain ⟨h1, L₁, L₂, o, rfl, h2⟩ := h
    exact ⟨h1, L₁, L₂ ++ N, o, by simp, h2⟩

lemma good_frame' {L : List (OpId P × MaxOp)} {m m' : ℕ} {x : OpId P} {pd : Option MaxOp}
    {l : Loc} (hm : m ≤ m') (h : Good L m x pd l) : Good L m' x pd l := by
  simpa using good_frame (N := []) (by simp) hm h

lemma linState_concat (L : List (OpId P × MaxOp)) (x : OpId P) (o : MaxOp) :
    linState (L ++ [(x, o)]) = (maxRegObj.δ (linState L) o).1 := by
  simp [linState, ObjSpec.runOps]

lemma not_mem_single {x y : OpId P} {o : MaxOp} (h : x.1 ≠ y.1) :
    x ∉ ([(y, o)] : List (OpId P × MaxOp)).map Prod.fst := by
  simp only [List.map_cons, List.map_nil, List.mem_singleton]
  rintro rfl; exact h rfl

/-- The invariant is preserved by every step, and `value` never decreases. -/
theorem inv_step {α : List (Label P maxRegObj)} {C C' : Cfg P} {ℓ : Label P maxRegObj}
    (hα : (impl P).run α = some C) (hI : Inv α C) (h : (impl P).step C ℓ = some C') :
    Inv (α ++ [ℓ]) C' ∧ C.mem () ≤ C'.mem () := by
  show InvL (α ++ [ℓ]) C' (lin (α ++ [ℓ])) ∧ _
  rw [lin_concat hα]
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hx : curOp α p ∉ (lin α).map Prod.fst := fun hm =>
      (impl P).not_invoked_curOp_of_idle hα h0 (hI.isLin.mem_invoked hm)
    simp only [lpEntry, Option.toList_none, List.append_nil]
    refine ⟨⟨hI.isLin.append_inv p o, by rw [hmem]; exact hI.mem, fun q => ?_⟩, by rw [hmem]⟩
    rw [hmem, hpend, hloc, curOp_append_inv]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      cases o with
      | writeMax v => exact ⟨rfl, hx⟩
      | readMax => exact ⟨rfl, hx⟩
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]; exact hI.good q
  | tau p =>
    have h0 := (Impl.step_tau h).1
    have hgp := hI.good p
    set m := C.mem () with hm
    set x := curOp α p with hx
    have hfr : ∀ q, q ≠ p → ∀ o, curOp α q ∉ ([(x, o)] : List (OpId P × MaxOp)).map Prod.fst :=
      fun q hq o => not_mem_single (by simpa [x] using hq)
    cases hl : C.loc p with
    | wRead v =>
      rw [hl] at hgp
      obtain ⟨hpo, hxL⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (impl P).run_pend_curOp hα hpo
      obtain rfl := step_tau_wRead h0 hl h
      by_cases hvm : v ≤ m
      · have he : lpEntry C α (.tau p) = some (x, .writeMax v) := by
          simp [lpEntry, hpo, hl, ← hm, hvm, x]
        rw [he]
        refine ⟨⟨(hI.isLin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, le_rfl⟩
        · simp only [Option.toList_some, linState_concat, ← hI.mem, ← hm,
            max_eq_left hvm]
        · simp only [Option.toList_some, curOp_append_tau]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self, ← hm, hvm, ite_true]
            exact ⟨v, hpo, by simp [x]⟩
          · rw [Function.update_of_ne hq]
            exact good_frame (hfr q hq _) le_rfl (hI.good q)
      · have he : lpEntry C α (.tau p) = none := by simp [lpEntry, hpo, hl, ← hm, hvm]
        rw [he, Option.toList_none, List.append_nil]
        refine ⟨⟨hI.isLin.append_tau p, by simpa using hI.mem, fun q => ?_⟩, le_rfl⟩
        simp only [curOp_append_tau]
        by_cases hq : q = p
        · subst hq; simp only [Function.update_self, ← hm, hvm, ite_false]
          exact ⟨hpo, hxL, lt_of_not_ge hvm, le_rfl⟩
        · rw [Function.update_of_ne hq]; exact hI.good q
    | wCas v tmp =>
      rw [hl] at hgp
      obtain ⟨hpo, hxL, htv, htm⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (impl P).run_pend_curOp hα hpo
      obtain rfl := step_tau_wCas h0 hl h
      by_cases hmt : m = tmp
      · have he : lpEntry C α (.tau p) = some (x, .writeMax v) := by
          simp [lpEntry, hpo, hl, ← hm, hmt, x]
        rw [he]
        have hmv : m ≤ v := hmt ▸ htv.le
        refine ⟨⟨(hI.isLin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, ?_⟩
        · simp only [Option.toList_some, linState_concat, ← hI.mem, ← hm, hmt, ite_true,
            max_eq_right htv.le]
        · simp only [Option.toList_some, curOp_append_tau, ← hm, hmt, ite_true]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact ⟨v, hpo, by simp [x]⟩
          · rw [Function.update_of_ne hq]
            exact good_frame (hfr q hq _) hmv (hI.good q)
        · simp [← hm, hmt, htv.le]
      · have he : lpEntry C α (.tau p) = none := by simp [lpEntry, hpo, hl, ← hm, hmt]
        rw [he, Option.toList_none, List.append_nil]
        refine ⟨⟨hI.isLin.append_tau p, by simpa [← hm, hmt] using hI.mem, fun q => ?_⟩, ?_⟩
        · simp only [curOp_append_tau, ← hm, hmt, ite_false]
          by_cases hq : q = p
          · subst hq; simp only [Function.update_self]
            exact ⟨hpo, hxL⟩
          · rw [Function.update_of_ne hq]; exact hI.good q
        · simp [← hm, hmt]
    | rRead =>
      rw [hl] at hgp
      obtain ⟨hpo, hxL⟩ := hgp
      obtain ⟨-, hnc, hop⟩ := (impl P).run_pend_curOp hα hpo
      obtain rfl := step_tau_rRead h0 hl h
      have he : lpEntry C α (.tau p) = some (x, .readMax) := by
        simp [lpEntry, hpo, hl, x]
      rw [he]
      refine ⟨⟨(hI.isLin.push hop hxL hnc).append_tau p, ?_, fun q => ?_⟩, le_rfl⟩
      · simp only [Option.toList_some, linState_concat, ← hI.mem]
      · simp only [Option.toList_some, curOp_append_tau]
        by_cases hq : q = p
        · subst hq; simp only [Function.update_self]
          refine ⟨by simp [hpo], lin α, [], .readMax, rfl, ?_⟩
          exact hI.mem.symm
        · rw [Function.update_of_ne hq]
          exact good_frame (hfr q hq _) le_rfl (hI.good q)
    | idle => exact (step_tau_false (Or.inl hl) h).elim
    | wDone => exact (step_tau_false (Or.inr (Or.inl hl)) h).elim
    | rDone r => exact (step_tau_false (Or.inr (Or.inr ⟨r, hl⟩)) h).elim
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    simp only [lpEntry, Option.toList_none, List.append_nil]
    have hgp := hI.good p
    have hrest : ∀ q, q ≠ p → Good (lin α) (C'.mem ()) (curOp (α ++ [.ret p r]) q) (C'.pend q)
        (C'.loc q) := by
      intro q hq
      rw [hmem, hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq,
        curOp_append_ret_of_ne _ _ (Ne.symm hq)]
      exact hI.good q
    cases hl : C.loc p with
    | wDone =>
      rw [hl] at hgp hact
      simp only [impl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨v, hpo, hxL⟩ := hgp
      obtain ⟨y, hyL, hyx⟩ := List.mem_map.1 hxL
      obtain ⟨L₁, L₂, hs⟩ := List.append_of_mem hyL
      have hop := hI.isLin.op_eq y hyL
      rw [hyx, ((impl P).run_pend_curOp hα hpo).2.2] at hop
      have hs' : lin α = L₁ ++ ((p, (respsOf α p).length), .writeMax v) :: L₂ := by
        rw [hs]; obtain ⟨y1, y2⟩ := y
        simp only [Option.some.injEq] at hyx hop
        rw [hyx, hop]
      refine ⟨⟨hI.isLin.append_ret L₁ L₂ _ hs' (by simp), by rw [hmem]; exact hI.mem,
        fun q => ?_⟩, by rw [hmem]⟩
      by_cases hq : q = p
      · subst hq; rw [hpend, hloc]; simp [Good]
      · exact hrest q hq
    | rDone r' =>
      rw [hl] at hgp hact
      simp only [impl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hgp
      refine ⟨⟨hI.isLin.append_ret L₁ L₂ o hs hr, by rw [hmem]; exact hI.mem, fun q => ?_⟩,
        by rw [hmem]⟩
      by_cases hq : q = p
      · subst hq; rw [hpend, hloc]; simp [Good]
      · exact hrest q hq
    | idle => rw [hl] at hgp; exact absurd hgp h0
    | wRead v => rw [hl] at hact; simp [impl] at hact
    | wCas v tmp => rw [hl] at hact; simp [impl] at hact
    | rRead => rw [hl] at hact; simp [impl] at hact

/-- The invariant holds in every execution. -/
theorem inv_of_run {α : List (Label P maxRegObj)} {C : Cfg P} (h : (impl P).run α = some C) :
    Inv α C := by
  refine Impl.run_induction (Q := fun α C => Inv α C) ?_ ?_ h
  · exact ⟨isLinearization_nil, rfl, fun _ => rfl⟩
  · intro α C ℓ C' hα hI hs
    exact (inv_step hα hI hs).1

/-- **Linearizability** (Section 4.8.2 of [CPT15]): ordering the operations by their
linearization points gives a linearization of every execution. -/
theorem isLinFun_lin : (impl P).IsLinFun lin := fun _ ⟨_, hC⟩ => (inv_of_run hC).isLin

/-! ### Wait-freedom -/

/-- The potential of process `p`: a `WriteMax(v)` about to read has potential
`2 (v - value) + 2`, one about to `cas(value, tmp, v)` has `2 (v - tmp) + 1`. A failed `cas`
means `value > tmp`, so the potential drops at every step. -/
def pot (p : P) (C : Cfg P) : ℕ :=
  match C.loc p with
  | .wRead v => 2 * (v - C.mem ()) + 2
  | .wCas v tmp => 2 * (v - tmp) + 1
  | .rRead => 1
  | _ => 0

lemma pot_step {α : List (Label P maxRegObj)} {C C' : Cfg P} {ℓ : Label P maxRegObj} {p : P}
    (hα : (impl P).run α = some C) (hs : (impl P).step C ℓ = some C')
    (hp : C.pend p ≠ none) (hp' : C'.pend p ≠ none) :
    pot p C' ≤ pot p C ∧ (ℓ = .tau p → pot p C' < pot p C) := by
  have hI := inv_of_run hα
  have hle := (inv_step hα hI hs).2
  rcases (impl P).step_tau_or_other hs hp hp' with rfl | ⟨hq, hloc⟩
  · have hgp := hI.good p
    suffices pot p C' < pot p C from ⟨this.le, fun _ => this⟩
    cases hl : C.loc p with
    | wRead v =>
      obtain rfl := step_tau_wRead hp hl hs
      by_cases hvm : v ≤ C.mem () <;> simp [pot, hl, hvm]
    | wCas v tmp =>
      rw [hl] at hgp
      obtain ⟨-, -, htv, htm⟩ := hgp
      obtain rfl := step_tau_wCas hp hl hs
      by_cases hmt : C.mem () = tmp
      · simp [pot, hl, hmt]
      · simp only [pot, hl, Function.update_self, hmt, ite_false]
        have : tmp < C.mem () := lt_of_le_of_ne htm (Ne.symm hmt)
        omega
    | rRead =>
      obtain rfl := step_tau_rRead hp hl hs
      simp [pot, hl]
    | idle => exact (step_tau_false (Or.inl hl) hs).elim
    | wDone => exact (step_tau_false (Or.inr (Or.inl hl)) hs).elim
    | rDone r => exact (step_tau_false (Or.inr (Or.inr ⟨r, hl⟩)) hs).elim
  · refine ⟨?_, fun h => absurd (by rw [h]; rfl) hq⟩
    unfold pot
    rw [hloc]
    cases C.loc p with
    | wRead v =>
      dsimp only
      have : v - C'.mem () ≤ v - C.mem () := Nat.sub_le_sub_left hle v
      omega
    | _ => exact le_rfl

/-- **Wait-freedom** (Section 4.8.2 of [CPT15]): "each time the cas fails, the shared value
grows by at least one". -/
theorem waitFree : (impl P).WaitFree :=
  Impl.waitFreeOn_true_iff.1 <| (impl P).waitFreeOn_of_cfgPotential pot
    fun _ _ _ _ _ hα _ hs hp hp' => pot_step hα hs hp hp'

/-! ### Help-freedom -/

/-- **Section 4.8.2 of [CPT15]**: the max register of Figure 4.5 is help-free, by Claim 4.8.1
with the linearization points of the paper. -/
theorem helpFreeWith_lin : HelpFreeWith (impl P) lin :=
  helpFreeWith_of_linPointFun isLinFun_lin linPointFun_lin waitFree.obstructionFree
    fun _ => ⟨.readMax, trivial⟩

/-- **Section 4.8.2 of [CPT15]**: the max register of Figure 4.5 is help-free. -/
theorem helpFree : HelpFree (impl P) := ⟨lin, isLinFun_lin, helpFreeWith_lin⟩

/-- **Section 4.8.2 of [CPT15]** (main statement): Figure 4.5 is a linearizable, wait-free and
help-free implementation of a max register from a single CAS object, for any set of
processes. -/
theorem maxRegister_helpFree_waitFree :
    (impl P).Linearizable ∧ (impl P).WaitFree ∧ HelpFree (impl P) :=
  ⟨⟨lin, isLinFun_lin⟩, waitFree, helpFree⟩

end Podc.HelpFreeWaitFree.MaxRegister
