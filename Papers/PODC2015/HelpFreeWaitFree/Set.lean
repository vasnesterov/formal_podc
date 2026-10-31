import Papers.PODC2015.HelpFreeWaitFree.LinPointHelpFree
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# A help-free wait-free set (Figure 4.4 of [CPT15])

[CPT15]: K. Censor-Hillel, E. Petrank, S. Timnat. *Help!* PODC 2015 (full version: Chapter 4 of
S. Timnat's PhD thesis), Section 4.8.1, Figure 4.4:

```
bool insert(int key)   { bool result = cas(A[key],0,1); return result; }  // linearization point
bool delete(int key)   { bool result = cas(A[key],1,0); return result; }  // linearization point
bool contains(int key) { bool result = (A[key] == 1);   return result; }  // linearization point
```

## Model
CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`): any set `P` of processes, one
compare-and-swap bit `A[k]` per key `k : K` (CSLib's `casObject Bool false`, `true` = 1). The key
domain `K` is any type with decidable equality (the paper takes a finite domain; finiteness is
not needed). The implemented object is the set `setObj K` (initially empty): `insert k` adds `k`
and returns whether `k` was absent, `delete k` removes `k` and returns whether it was present,
`contains k` returns whether `k` is present.

## Results
* `isLinFun_lin` — the linearization function given by the paper's linearization points (the
  single `cas`/read of each operation) is a linearization function;
* `linPointFun_lin` — these are steps of the operations themselves;
* `waitFree` — every operation takes a single base-object access;
* `set_helpFree_waitFree` — linearizable, wait-free and help-free (via Claim 4.8.1).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree.SetImpl

open Cslib.SharedMemory

variable {K : Type} [DecidableEq K]

/-- Operations of the set type. -/
inductive SetOp (K : Type) where
  | insert (k : K)
  | delete (k : K)
  | contains (k : K)

/-- The set type over the key domain `K` (state: characteristic function, initially empty). -/
abbrev setObj (K : Type) [DecidableEq K] : ObjSpec where
  State := K → Bool
  Op := SetOp K
  Resp := Bool
  init := fun _ => false
  δ s
    | .insert k => (Function.update s k true, !s k)
    | .delete k => (Function.update s k false, s k)
    | .contains k => (s, s k)

/-- Program counters of Figure 4.4. -/
inductive Loc (K : Type) where
  | idle
  /-- about to execute the operation's single base-object access on `A[k]` -/
  | ins (k : K)
  | del (k : K)
  | con (k : K)
  /-- about to return `r` -/
  | done (r : Bool)

/-- The base objects: a CAS bit `A[k]` (initially `0 = false`) per key. -/
abbrev Base (K : Type) : K → ObjSpec := fun _ => casObject Bool false

/-- **Figure 4.4 of [CPT15]**: the set from one CAS bit per key. -/
def impl (K P : Type) [DecidableEq K] : Impl (setObj K) (Base K) P (Loc K) where
  memInit _ := false
  locInit _ := .idle
  invoke _ _ o := match o with
    | .insert k => .ins k
    | .delete k => .del k
    | .contains k => .con k
  act _ l := match l with
    | .idle => .ret false .idle
    | .ins k => .access k (.cas false true) (fun r => .done (decide (r = .inr true)))
    | .del k => .access k (.cas true false) (fun r => .done (decide (r = .inr true)))
    | .con k => .access k .read (fun r => .done (decide (r = .inl true)))
    | .done r => .ret r .idle

/-- Configurations of the implementation. -/
abbrev Cfg (K P : Type) [DecidableEq K] := Config (setObj K) (Base K) P (Loc K)

variable {P : Type} [DecidableEq P]

/-! ### Linearization points -/

/-- The entry appended by the step `γ` taken from `C` after `h`: every base-object access is the
linearization point of the operation it belongs to. -/
def lpEntry (C : Cfg K P) (h : List (Label P (setObj K))) : Label P (setObj K) →
    Option (OpId P × SetOp K)
  | .tau p => (C.pend p).map fun o => (curOp h p, o)
  | _ => none

/-- Auxiliary: `lin` on the reversed execution. -/
noncomputable def linRev : List (Label P (setObj K)) → List (OpId P × SetOp K)
  | [] => []
  | γ :: hr => match (impl K P).run hr.reverse with
    | some C => linRev hr ++ (lpEntry C hr.reverse γ).toList
    | none => linRev hr

/-- The linearization function of Section 4.8.1: operations ordered by their (single)
base-object access. -/
noncomputable def lin (h : List (Label P (setObj K))) : List (OpId P × SetOp K) :=
  linRev h.reverse

lemma lin_concat {h : List (Label P (setObj K))} {C : Cfg K P}
    (hC : (impl K P).run h = some C) (γ : Label P (setObj K)) :
    lin (h ++ [γ]) = lin h ++ (lpEntry C h γ).toList := by
  simp [lin, linRev, hC]

/-- Every linearization point of Figure 4.4 is a step of the operation itself. -/
theorem linPointFun_lin : LinPointFun (impl K P) lin := by
  rintro h γ ⟨C', hv⟩
  rw [Impl.run_concat] at hv
  cases hC : (impl K P).run h with
  | none => simp [hC] at hv
  | some C =>
    rw [lin_concat hC]
    cases γ with
    | tau p =>
      cases hp : C.pend p with
      | none => left; simp [lpEntry, hp]
      | some o => right; exact ⟨o, by simp [lpEntry, hp, Label.proc]⟩
    | inv p o => left; simp [lpEntry]
    | ret p r => left; simp [lpEntry]

/-! ### The invariant -/

/-- Status of a process with local state `l`, pending operation `pd`, current instance `x`,
relative to the linearization `L`. -/
def Good (L : List (OpId P × SetOp K)) (x : OpId P) (pd : Option (SetOp K)) : Loc K → Prop
  | .idle => pd = none
  | .ins k => pd = some (.insert k) ∧ x ∉ L.map Prod.fst
  | .del k => pd = some (.delete k) ∧ x ∉ L.map Prod.fst
  | .con k => pd = some (.contains k) ∧ x ∉ L.map Prod.fst
  | .done r => pd ≠ none ∧ ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧
      ((setObj K).δ ((setObj K).runOps (setObj K).init (L₁.map Prod.snd)) o).2 = r

/-- The invariant: `L` is a linearization of `α`, the bits hold the abstract set after `L`,
and every process is in a status consistent with its linearization point. -/
structure InvL (α : List (Label P (setObj K))) (C : Cfg K P) (L : List (OpId P × SetOp K)) :
    Prop where
  isLin : IsLinearization α L
  mem : ∀ k, C.mem k = linState (A := setObj K) L k
  good : ∀ p, Good L (curOp α p) (C.pend p) (C.loc p)

/-- The invariant for the linearization `lin α`. -/
abbrev Inv (α : List (Label P (setObj K))) (C : Cfg K P) : Prop := InvL α C (lin α)

lemma good_frame {L N : List (OpId P × SetOp K)} {x : OpId P} {pd : Option (SetOp K)}
    {l : Loc K} (hN : x ∉ N.map Prod.fst) (h : Good L x pd l) : Good (L ++ N) x pd l := by
  have hm : ∀ {L : List (OpId P × SetOp K)}, x ∉ L.map Prod.fst →
      x ∉ (L ++ N).map Prod.fst := fun h' => by
    simp only [List.map_append, List.mem_append, not_or]; exact ⟨h', hN⟩
  cases l with
  | idle => exact h
  | ins k => exact ⟨h.1, hm h.2⟩
  | del k => exact ⟨h.1, hm h.2⟩
  | con k => exact ⟨h.1, hm h.2⟩
  | done r =>
    obtain ⟨h1, L₁, L₂, o, rfl, h2⟩ := h
    exact ⟨h1, L₁, L₂ ++ N, o, by simp, h2⟩

/-- The invariant is preserved by every step. -/
theorem inv_step {α : List (Label P (setObj K))} {C C' : Cfg K P} {ℓ : Label P (setObj K)}
    (hα : (impl K P).run α = some C) (hI : Inv α C) (h : (impl K P).step C ℓ = some C') :
    Inv (α ++ [ℓ]) C' := by
  show InvL (α ++ [ℓ]) C' (lin (α ++ [ℓ]))
  rw [lin_concat hα]
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hx : curOp α p ∉ (lin α).map Prod.fst := fun hm =>
      (impl K P).not_invoked_curOp_of_idle hα h0 (hI.isLin.mem_invoked hm)
    simp only [lpEntry, Option.toList_none, List.append_nil]
    refine ⟨hI.isLin.append_inv p o, by rw [hmem]; exact hI.mem, fun q => ?_⟩
    rw [hpend, hloc, curOp_append_inv]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      cases o with
      | insert k => exact ⟨rfl, hx⟩
      | delete k => exact ⟨rfl, hx⟩
      | contains k => exact ⟨rfl, hx⟩
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]; exact hI.good q
  | tau p =>
    have h0 := (Impl.step_tau h).1
    obtain ⟨o, hpo⟩ := Option.ne_none_iff_exists'.1 h0
    obtain ⟨-, hnc, hop⟩ := (impl K P).run_pend_curOp hα hpo
    have hgp := hI.good p
    set x := curOp α p with hx
    have he : lpEntry C α (.tau p) = some (x, o) := by simp [lpEntry, hpo, x]
    rw [he, Option.toList_some]
    have hfr : ∀ q, q ≠ p → curOp α q ∉ ([(x, o)] : List (OpId P × SetOp K)).map Prod.fst := by
      intro q hq; simp only [List.map_cons, List.map_nil, List.mem_singleton]
      intro e; exact hq (congrArg Prod.fst e)
    -- the access step `access k bo (fun r => done (resp r))`
    have key : ∀ (k : K) (bo : CASOp Bool) (resp : Bool ⊕ Bool → Bool),
        (impl K P).act p (C.loc p) = .access k bo (fun r => .done (resp r)) →
        x ∉ (lin α).map Prod.fst →
        (∀ k', Function.update C.mem k ((casObject Bool false).δ (C.mem k) bo).1 k' =
          linState (A := setObj K) (lin α ++ [(x, o)]) k') →
        resp ((casObject Bool false).δ (C.mem k) bo).2 =
          ((setObj K).δ ((setObj K).runOps (setObj K).init ((lin α).map Prod.snd)) o).2 →
        InvL (α ++ [.tau p]) C' (lin α ++ [(x, o)]) := by
      intro k bo resp hact hxL hmem hresp
      rw [Impl.step_tau_eq_some h0 hact] at h
      obtain rfl := Option.some.inj h
      refine ⟨(hI.isLin.push hop hxL hnc).append_tau p, hmem, fun q => ?_⟩
      simp only [curOp_append_tau]
      by_cases hq : q = p
      · subst hq
        simp only [Function.update_self]
        exact ⟨by simp [hpo], lin α, [], o, rfl, hresp.symm⟩
      · rw [Function.update_of_ne hq]
        exact good_frame (hfr q hq) (hI.good q)
    have hst : ∀ k', linState (A := setObj K) (lin α ++ [(x, o)]) k' =
        ((setObj K).δ (linState (A := setObj K) (lin α)) o).1 k' := by
      intro k'; simp [linState, ObjSpec.runOps]
    have hmemI : ∀ k', C.mem k' = linState (A := setObj K) (lin α) k' := hI.mem
    have hlinS : (setObj K).runOps (setObj K).init ((lin α).map Prod.snd) =
        linState (A := setObj K) (lin α) := rfl
    cases hl : C.loc p with
    | ins k =>
      rw [hl] at hgp
      obtain ⟨hpo', hxL⟩ := hgp
      obtain rfl := Option.some.inj (hpo.symm.trans hpo')
      refine key k (.cas false true) _ (by rw [hl]; rfl) hxL (fun k' => ?_) ?_
      · rw [hst]
        by_cases hk : k' = k
        · subst hk; cases hb : C.mem k' <;> simp
        · simp [Function.update_of_ne hk, hmemI k']
      · rw [hlinS]; show _ = !(linState (A := setObj K) (lin α) k)
        rw [← hmemI k]; cases C.mem k <;> simp
    | del k =>
      rw [hl] at hgp
      obtain ⟨hpo', hxL⟩ := hgp
      obtain rfl := Option.some.inj (hpo.symm.trans hpo')
      refine key k (.cas true false) _ (by rw [hl]; rfl) hxL (fun k' => ?_) ?_
      · rw [hst]
        by_cases hk : k' = k
        · subst hk; cases hb : C.mem k' <;> simp
        · simp [Function.update_of_ne hk, hmemI k']
      · rw [hlinS]; show _ = linState (A := setObj K) (lin α) k
        rw [← hmemI k]; cases C.mem k <;> simp
    | con k =>
      rw [hl] at hgp
      obtain ⟨hpo', hxL⟩ := hgp
      obtain rfl := Option.some.inj (hpo.symm.trans hpo')
      refine key k .read _ (by rw [hl]; rfl) hxL (fun k' => ?_) ?_
      · rw [hst]
        by_cases hk : k' = k
        · subst hk; simp [hmemI k']
        · simp [Function.update_of_ne hk, hmemI k']
      · rw [hlinS]; show _ = linState (A := setObj K) (lin α) k
        rw [← hmemI k]; cases C.mem k <;> simp
    | idle =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      rw [hl] at hact; simp [impl] at hact
    | done r =>
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      rw [hl] at hact; simp [impl] at hact
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    simp only [lpEntry, Option.toList_none, List.append_nil]
    have hgp := hI.good p
    cases hl : C.loc p with
    | done r' =>
      rw [hl] at hgp hact
      simp only [impl, Action.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      obtain ⟨-, L₁, L₂, o, hs, hr⟩ := hgp
      refine ⟨hI.isLin.append_ret L₁ L₂ o hs hr, by rw [hmem]; exact hI.mem, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; rw [hpend, hloc]; simp [Good]
      · rw [hpend, hloc, Function.update_of_ne hq, Function.update_of_ne hq,
          curOp_append_ret_of_ne _ _ (Ne.symm hq)]
        exact hI.good q
    | idle => rw [hl] at hgp; exact absurd hgp h0
    | ins k => rw [hl] at hact; simp [impl] at hact
    | del k => rw [hl] at hact; simp [impl] at hact
    | con k => rw [hl] at hact; simp [impl] at hact

/-- The invariant holds in every execution. -/
theorem inv_of_run {α : List (Label P (setObj K))} {C : Cfg K P}
    (h : (impl K P).run α = some C) : Inv α C := by
  refine Impl.run_induction (Q := fun α C => Inv α C) ?_ ?_ h
  · exact ⟨isLinearization_nil, fun _ => rfl, fun _ => rfl⟩
  · intro α C ℓ C' hα hI hs
    exact inv_step hα hI hs

/-- **Linearizability** (Section 4.8.1 of [CPT15]). -/
theorem isLinFun_lin : (impl K P).IsLinFun lin := fun _ ⟨_, hC⟩ => (inv_of_run hC).isLin

/-- **Wait-freedom** (Section 4.8.1 of [CPT15]): every operation performs a single base-object
access. -/
theorem waitFree : (impl K P).WaitFree :=
  (impl K P).waitFree_of_potential
    (fun _ l => match l with | .ins _ | .del _ | .con _ => 1 | _ => 0)
    (fun p l i o k hact x => by cases l <;> simp [impl] at hact <;> obtain ⟨rfl, rfl, rfl⟩ := hact <;> simp)

/-- **Section 4.8.1 of [CPT15]**: the set of Figure 4.4 is linearizable, wait-free and help-free
(by Claim 4.8.1, `helpFree_of_linPointFun`), for any key domain and any set of processes. -/
theorem set_helpFree_waitFree [Inhabited K] :
    (impl K P).Linearizable ∧ (impl K P).WaitFree ∧ HelpFree (impl K P) :=
  ⟨⟨lin, isLinFun_lin⟩, waitFree,
    helpFree_of_linPointFun isLinFun_lin linPointFun_lin waitFree.obstructionFree
      fun _ => ⟨.contains default, trivial⟩⟩

end Podc.HelpFreeWaitFree.SetImpl
