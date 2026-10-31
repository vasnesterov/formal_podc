import Papers.PODC2022.BluntingAdversary.Moves

/-!
# Tail strong linearizability: simulation by the atomic object (Lemma 4.3, property (4))

For a deterministic implementation `I` of `A` that is tail strongly linearizable w.r.t. the
preamble mapping `Π`, every strong adversary against `P(O)` (with `O = implSem I Π`) is matched
by an adversary against `P(A)` (the atomic object), as far as executions are concerned all of
whose program random steps happen at prefixes that are complete w.r.t. `Π`:
`optSafe_le_prob_atom`.

## Proof

Golab–Higham–Woelfel style simulation. The O-configuration `s` is abstracted to a CSLib
configuration `K` (`TSLSim.Abs`); the execution of the object is recorded by its history `γ`
(`I.run γ = some K`). The atomic system lags behind: it is only synchronised at complete
prefixes (program random steps and termination). At such a prefix `α` with linearization
`L = f α`, the correspondence `TSLSim.QInv α s d L` says that the atomic configuration `d` has
executed exactly `L`: its memory is `linState L`, and every process is either *in sync*
(same client state; its pending operation is not in `L`) or *ahead* (its pending operation
is in `L` and the atomic client already continued with the response the specification gives it
in `L`).

The **segment lemma** `TSLSim.seg_main`: if `QInv β sβ d (f β)` at a complete prefix `β` and a
coin-free run of the O-system leads to a complete prefix `γ`, then the atomic system can
deterministically reach `d'` with `QInv γ s d' (f γ)`. Along the segment the atomic system
executes `L = f γ` greedily (`TSLSim.catchUp`), maintaining `QInv` relative to a prefix of `L`
and the maximality property `TSLSim.Max`; maximality and the real-time order of `L` show that
every operation returned by `O` has already been executed atomically, with the same response.

The main theorem follows from `MDP.opt_le_of_super`.
-/

-- CSLib candidate (generic infrastructure for randomized programs over shared objects)
namespace Podc.BluntingAdversary

open Cslib.SharedMemory
open scoped Classical

namespace TSLSim

variable {P : Type} [DecidableEq P] {A : ObjSpec} {C L : Type}
  {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}

/-! ## Abstraction of O-configurations and O-steps -/

/-- The O-configuration `s` corresponds to the CSLib configuration `K`. -/
structure Abs (Pr : Program P A C) (s : Cfg P C L (Mem Bs)) (K : Config A Bs P L) : Prop where
  loc : K.loc = s.lo
  mem : K.mem = s.mem
  pend : ∀ p, K.pend p = none ↔ s.busy p = false
  call : ∀ p o, K.pend p = some o → ∃ k, Pr.next p (s.cl p) = .call o k

/-- A deterministic step of the O-system, with the labels it adds to the object's history. -/
inductive OStep (Pr : Program P A C) (I : Impl A Bs P L) :
    Cfg P C L (Mem Bs) → Cfg P C L (Mem Bs) → List (Label P A) → Prop
  | tau (s : Cfg P C L (Mem Bs)) (p : P) (i : ι) (o : (Bs i).Op) (k : (Bs i).Resp → L) :
      s.busy p = true → I.act p (s.lo p) = .access i o k →
      OStep Pr I s { s with lo := Function.update s.lo p (k ((Bs i).δ (s.mem i) o).2),
                            mem := Function.update s.mem i ((Bs i).δ (s.mem i) o).1 } [.tau p]
  | ret (s : Cfg P C L (Mem Bs)) (p : P) (r : A.Resp) (l : L) (o : A.Op) (k : A.Resp → C) :
      s.busy p = true → I.act p (s.lo p) = .ret r l → Pr.next p (s.cl p) = .call o k →
      OStep Pr I s { s with cl := Function.update s.cl p (k r),
                            busy := Function.update s.busy p false,
                            lo := Function.update s.lo p l } [.ret p r]
  | loc (s : Cfg P C L (Mem Bs)) (p : P) (c : C) :
      s.busy p = false → Pr.next p (s.cl p) = .loc c →
      OStep Pr I s { s with cl := Function.update s.cl p c } []
  | inv (s : Cfg P C L (Mem Bs)) (p : P) (o : A.Op) (k : A.Resp → C) :
      s.busy p = false → Pr.next p (s.cl p) = .call o k →
      OStep Pr I s { s with busy := Function.update s.busy p true,
                            lo := Function.update s.lo p (I.invoke p (s.lo p) o) } [.inv p o]

variable {Pr : Program P A C} {I : Impl A Bs P L} {Pi : P → L → Prop}

/-- Every deterministic move of the O-system is an `OStep`. -/
lemma oStep_of_move {s s' : Cfg P C L (Mem Bs)} {q : P}
    (h : (sys Pr (implSem I Pi)).move s q = .det s') : ∃ ℓs, OStep Pr I s s' ℓs := by
  cases hb : s.busy q
  · cases hn : Pr.next q (s.cl q) with
    | loc c =>
      rw [move_loc Pr _ s q hb hn] at h; cases h; exact ⟨_, .loc s q c hb hn⟩
    | rnd m g => rw [move_rnd Pr _ s q hb hn] at h; cases h
    | call o k =>
      rw [move_call_inl Pr _ s q hb hn (l := I.invoke q (s.lo q) o) (m := s.mem) rfl] at h
      cases h; exact ⟨_, .inv s q o k hb hn⟩
    | done => rw [move_done Pr _ s q hb hn] at h; cases h
  · cases ha : I.act q (s.lo q) with
    | access i o k =>
      have : (implSem I Pi).act q (s.lo q) s.mem s.coins =
          .step (k ((Bs i).δ (s.mem i) o).2) (Function.update s.mem i ((Bs i).δ (s.mem i) o).1) := by
        simp [implSem, ha]
      rw [move_step Pr _ s q hb this] at h; cases h; exact ⟨_, .tau s q i o k hb ha⟩
    | ret r l =>
      have : (implSem I Pi).act q (s.lo q) s.mem s.coins = .ret r l := by simp [implSem, ha]
      cases hn : Pr.next q (s.cl q) with
      | call o k =>
        rw [move_ret Pr _ s q hb this hn] at h; cases h; exact ⟨_, .ret s q r l o k hb ha hn⟩
      | _ => simp [sys, sysMove, hb, this, hn] at h

lemma OStep.badCoin {s s' : Cfg P C L (Mem Bs)} {ℓs : List (Label P A)} (h : OStep Pr I s s' ℓs) :
    s'.badCoin = s.badCoin ∧ s'.coins = s.coins := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- An O-step is a step of the CSLib implementation (all operations allowed). -/
lemma OStep.run (hall : ∀ p o, I.allowed p o) {s s' : Cfg P C L (Mem Bs)}
    {ℓs : List (Label P A)} (h : OStep Pr I s s' ℓs) {K : Config A Bs P L} (hA : Abs Pr s K) :
    ∃ K', I.runFrom K ℓs = some K' ∧ Abs Pr s' K' := by
  cases h with
  | tau p i o k hb ha =>
    have hp : K.pend p ≠ none := fun h => by simp [(hA.pend p).1 h] at hb
    have ha' : I.act p (K.loc p) = .access i o k := by rw [hA.loc]; exact ha
    refine ⟨_, by rw [Impl.runFrom_singleton, Impl.step_tau_eq_some hp ha'], ?_⟩
    refine ⟨by simp [hA.loc, hA.mem], by simp [hA.mem], fun q => ?_, fun q o' h => ?_⟩
    · exact hA.pend q
    · exact hA.call q o' h
  | ret p r l o k hb ha hn =>
    have hp : K.pend p ≠ none := fun h => by simp [(hA.pend p).1 h] at hb
    have ha' : I.act p (K.loc p) = .ret r l := by rw [hA.loc]; exact ha
    refine ⟨_, by rw [Impl.runFrom_singleton, Impl.step_ret_eq_some hp ha'], ?_⟩
    refine ⟨by simp [hA.loc], hA.mem, fun q => ?_, fun q o' h => ?_⟩
    · by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, hA.pend q]
    · by_cases hq : q = p
      · subst hq; simp at h
      · simp only [Function.update_of_ne hq] at h ⊢; exact hA.call q o' h
  | loc p c hb hn =>
    refine ⟨K, rfl, hA.loc, hA.mem, hA.pend, fun q o' h => ?_⟩
    by_cases hq : q = p
    · subst hq; simp [(hA.pend q).2 hb] at h
    · simp only [Function.update_of_ne hq]; exact hA.call q o' h
  | inv p o k hb hn =>
    have hp : K.pend p = none := (hA.pend p).2 hb
    refine ⟨_, by rw [Impl.runFrom_singleton, Impl.step_inv_eq_some hp (hall p o)], ?_⟩
    refine ⟨by simp [hA.loc], hA.mem, fun q => ?_, fun q o' h => ?_⟩
    · by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, hA.pend q]
    · by_cases hq : q = p
      · subst hq; simp at h; subst h; exact ⟨k, hn⟩
      · simp only [Function.update_of_ne hq] at h ⊢; exact hA.call q o' h

/-! ## The correspondence with the atomic system -/

/-- Correspondence between the O-configuration `s` (object history `γ`) and the atomic
configuration `d` that has executed the sequential history `Lj`. -/
structure QInv (Pr : Program P A C) (γ : List (Label P A)) (s : Cfg P C L (Mem Bs))
    (d : Cfg P C Unit A.State) (Lj : List (OpId P × A.Op)) : Prop where
  mem : d.mem = linState Lj
  coins : d.coins = s.coins
  bad : d.badCoin = s.badCoin
  busy : ∀ p, d.busy p = false
  proc : ∀ p, (d.cl p = s.cl p ∧ (s.busy p = true → curOp γ p ∉ Lj.map Prod.fst)) ∨
    (s.busy p = true ∧ ∃ o k r, Pr.next p (s.cl p) = .call o k ∧
      A.respIn A.init Lj (curOp γ p) = some r ∧ d.cl p = k r)
  inv : ∀ y ∈ Lj.map Prod.fst, Invoked γ y
  compl : ∀ y, Completed γ y → y ∈ Lj.map Prod.fst

/-- Maximality of the greedy catch-up: the next entry of `L` after `Lj` has not been invoked. -/
def Max (L Lj : List (OpId P × A.Op)) (γ : List (Label P A)) : Prop :=
  ∀ y M, Lj ++ y :: M = L → ¬ Invoked γ y.1

/-- Atomic moves. -/
lemma atom_loc {d : Cfg P C Unit A.State} {p : P} {c : C} (hb : d.busy p = false)
    (h : Pr.next p (d.cl p) = .loc c) :
    (sys Pr (atomSem A)).DetReach d { d with cl := Function.update d.cl p c } :=
  .single p (move_loc Pr _ d p hb h)

lemma atom_call {d : Cfg P C Unit A.State} {p : P} {o : A.Op} {k : A.Resp → C}
    (hb : d.busy p = false) (h : Pr.next p (d.cl p) = .call o k) :
    (sys Pr (atomSem A)).DetReach d
      { d with cl := Function.update d.cl p (k (A.δ d.mem o).2),
               lo := Function.update d.lo p (), mem := (A.δ d.mem o).1 } :=
  .single p (move_call_inr Pr _ d p hb h rfl)

/-- A pending instance that is invoked but not completed is the current one of its process. -/
lemma eq_curOp_of_pending {γ : List (Label P A)} {K : Config A Bs P L} (hrun : I.run γ = some K)
    {y : OpId P} (hi : Invoked γ y) (hc : ¬ Completed γ y) :
    y = curOp γ y.1 ∧ K.pend y.1 ≠ none := by
  obtain ⟨p, n⟩ := y
  simp only [Invoked, Completed] at hi hc
  rcases I.run_counts hrun p with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · exact ⟨by simp only [curOp, Prod.mk.injEq, true_and]; omega, h1⟩

lemma not_mem_of_sublist_pair {X : Type} {x y : X} {A' B : List X} (h : [x, y].Sublist (A' ++ y :: B))
    (hx : x ∉ A') (hnd : y ∉ B) : False := by
  obtain ⟨l1, l2, he, h1, h2⟩ := sublist_pair_iff.1 h
  rcases List.append_eq_append_iff.1 he with ⟨a', rfl, he'⟩ | ⟨c', rfl, -⟩
  · cases a' with
    | nil => simp at h1; exact hx h1
    | cons z a' =>
      simp only [List.cons_append, List.cons.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact hnd (List.mem_append_right _ h2)
  · exact hx (List.mem_append_left _ h1)

section Step

variable {αf : List (Label P A)} {L' : List (OpId P × A.Op)}

/-- One O-step, simulated by the atomic system (which keeps the executed prefix `Lj`). -/
lemma qinv_step (hLin : IsLinearization αf L') {γ : List (Label P A)} {ℓs : List (Label P A)}
    (hpre : γ ++ ℓs <+: αf) {K : Config A Bs P L} (hrun : I.run γ = some K)
    {s s' : Cfg P C L (Mem Bs)} (hA : Abs Pr s K) {d : Cfg P C Unit A.State}
    {Lj : List (OpId P × A.Op)} (hQ : QInv Pr γ s d Lj) (hLj : Lj <+: L') (hmax : Max L' Lj γ)
    (hst : OStep Pr I s s' ℓs) :
    ∃ d', (sys Pr (atomSem A)).DetReach d d' ∧ QInv Pr (γ ++ ℓs) s' d' Lj := by
  cases hst with
  | tau p i o k hb ha =>
    refine ⟨d, .refl _, hQ.mem, hQ.coins, hQ.bad, hQ.busy, fun q => ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · simpa using hQ.proc q
    · exact (hQ.inv y hy).mono
    · exact hQ.compl y ((completed_append_of_not_ret (by simp) y).1 hy)
  | loc p c hb hn =>
    have hsync : d.cl p = s.cl p := by
      rcases hQ.proc p with h | h
      · exact h.1
      · simp [hb] at h
    refine ⟨_, atom_loc (hQ.busy p) (hsync ▸ hn), ?_⟩
    simp only [List.append_nil]
    refine ⟨hQ.mem, hQ.coins, hQ.bad, hQ.busy, fun q => ?_, hQ.inv, hQ.compl⟩
    by_cases hq : q = p
    · subst hq; left; simp [hb]
    · simpa [Function.update_of_ne hq] using hQ.proc q
  | inv p o k hb hn =>
    have hsync : d.cl p = s.cl p := by
      rcases hQ.proc p with h | h
      · exact h.1
      · simp [hb] at h
    have hnot : curOp γ p ∉ Lj.map Prod.fst := fun h =>
      I.not_invoked_curOp_of_idle hrun ((hA.pend p).2 hb) (hQ.inv _ h)
    refine ⟨d, .refl _, hQ.mem, hQ.coins, hQ.bad, hQ.busy, fun q => ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · by_cases hq : q = p
      · subst hq; left; simpa [hsync] using hnot
      · simpa [Function.update_of_ne hq] using hQ.proc q
    · exact (hQ.inv y hy).mono
    · exact hQ.compl y ((completed_append_of_not_ret (by simp) y).1 hy)
  | ret p r l o k hb ha hn =>
    obtain ⟨αr, hαr⟩ := hpre
    have hp : K.pend p ≠ none := fun h => by simp [(hA.pend p).1 h] at hb
    obtain ⟨o', hpo⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨hinvx, -, -⟩ := I.run_pend_curOp hrun hpo
    set x := curOp γ p with hx
    have hcx : Completed (γ ++ [.ret p r]) x := (completed_append_ret x).2 (Or.inr rfl)
    have hrx : respOf (γ ++ [.ret p r]) x = some r := by rw [respOf_append_ret]; simp [hx]
    have hrxf : respOf αf x = some r := by rw [← hαr]; exact respOf_append_of_eq_some hrx _
    obtain ⟨M, hM⟩ := hLj
    -- the returning instance has already been executed atomically
    have hxL : x ∈ Lj.map Prod.fst := by
      by_contra hxL
      have hxf : x ∈ L'.map Prod.fst :=
        hLin.complete x (Completed.of_respOf_eq_some hrxf)
      rw [← hM, List.map_append, List.mem_append] at hxf
      have hxM := hxf.resolve_left hxL
      cases M with
      | nil => simp at hxM
      | cons y M =>
        have hy := hmax y M hM
        have hne : y.1 ≠ x := fun h => hy (h ▸ hinvx)
        have hprec : Precedes αf x y.1 := by
          refine ⟨γ ++ [.ret p r], αr, hαr.symm, hcx, ?_⟩
          simpa [Invoked, opsOf_append_ret] using hy
        have hyL : y.1 ∈ L'.map Prod.fst := by rw [← hM]; simp
        have hsub := hLin.realtime x y.1 hprec hyL
        have hnd := hLin.nodup
        rw [← hM] at hsub hnd
        simp only [List.map_append, List.map_cons] at hsub hnd
        refine not_mem_of_sublist_pair hsub hxL ?_
        exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
    have hahead := hQ.proc p
    rcases hahead with ⟨-, h⟩ | ⟨-, o2, k2, r2, hn2, hr2, hd⟩
    · exact absurd hxL (h hb)
    rw [hn] at hn2
    cases hn2
    have hrL : A.respIn A.init L' x = some r := hLin.respIn_eq hrxf
    rw [← hM, ObjSpec.respIn_append_of_mem hxL, hr2] at hrL
    cases hrL
    refine ⟨d, .refl _, hQ.mem, hQ.coins, hQ.bad, hQ.busy, fun q => ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · by_cases hq : q = p
      · subst hq; left; simp [hd]
      · simpa [Function.update_of_ne hq, curOp_append_ret_of_ne _ _ (Ne.symm hq)] using hQ.proc q
    · exact (hQ.inv y hy).mono
    · rcases (completed_append_ret y).1 hy with h | h
      · exact hQ.compl y h
      · rw [h]; exact hxL

/-- One step of the greedy catch-up: the atomic system executes the next entry of `L'`, which
is pending in the O-execution. -/
lemma qinv_push (hLin : IsLinearization αf L') {γ : List (Label P A)} (hpre : γ <+: αf)
    {K : Config A Bs P L} (hrun : I.run γ = some K) {s : Cfg P C L (Mem Bs)} (hA : Abs Pr s K)
    {d : Cfg P C Unit A.State} {Lj M : List (OpId P × A.Op)} {y : OpId P × A.Op}
    (hQ : QInv Pr γ s d Lj) (hsplit : Lj ++ y :: M = L') (hy : Invoked γ y.1) :
    ∃ d', (sys Pr (atomSem A)).DetReach d d' ∧ QInv Pr γ s d' (Lj ++ [y]) := by
  obtain ⟨⟨p, n⟩, o⟩ := y
  have hnd := hLin.nodup
  rw [← hsplit] at hnd
  simp only [List.map_append, List.map_cons] at hnd
  have hyLj : (p, n) ∉ Lj.map Prod.fst := fun h =>
    (List.nodup_append.1 hnd).2.2 _ h _ (List.mem_cons_self) rfl
  have hyc : ¬ Completed γ (p, n) := fun h => hyLj (hQ.compl _ h)
  obtain ⟨hcur, hp⟩ := eq_curOp_of_pending hrun hy hyc
  simp only at hcur hp
  obtain ⟨o', hpo⟩ := Option.ne_none_iff_exists'.1 hp
  obtain ⟨k, hn⟩ := hA.call p o' hpo
  obtain ⟨-, -, hop⟩ := I.run_pend_curOp hrun hpo
  have hop' : opOf αf (p, n) = some o := hLin.op_eq ((p, n), o) (by rw [← hsplit]; simp)
  obtain ⟨αr, rfl⟩ := hpre
  rw [opOf_append_of_invoked hy, hcur, hop] at hop'
  cases hop'
  have hb : s.busy p = true := by
    by_contra h; exact hp ((hA.pend p).2 (by simpa using h))
  have hsync : d.cl p = s.cl p := by
    rcases hQ.proc p with h | ⟨-, o2, k2, r2, -, hr2, -⟩
    · exact h.1
    · exact absurd (ObjSpec.mem_of_respIn_eq_some hr2) (hcur ▸ hyLj)
  refine ⟨_, atom_call (hQ.busy p) (hsync ▸ hn), ?_⟩
  refine ⟨by simp [hQ.mem, linState_concat], hQ.coins, hQ.bad, hQ.busy, fun q => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · by_cases hq : q = p
    · subst hq
      right
      refine ⟨hb, _, k, _, hn, ?_, by simp [hQ.mem]; rfl⟩
      rw [← hcur, ObjSpec.respIn_concat_self hyLj]; rfl
    · simp only [Function.update_of_ne hq]
      have hne : curOp γ q ≠ (p, n) := fun h => hq (congrArg Prod.fst h)
      rcases hQ.proc q with ⟨h1, h2⟩ | ⟨h1, o2, k2, r2, h3, h4, h5⟩
      · left; refine ⟨h1, fun hb' => ?_⟩
        simpa [hne] using h2 hb'
      · right; refine ⟨h1, o2, k2, r2, h3, ?_, h5⟩
        rw [ObjSpec.respIn_append_of_mem (ObjSpec.mem_of_respIn_eq_some h4), h4]
  · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hQ.inv z hz
    · exact hy
  · simp [hQ.compl z hz]

end Step

section CatchUp

variable {αf : List (Label P A)} {L' : List (OpId P × A.Op)}

/-- **Greedy catch-up**: the atomic system executes the entries of `L'` as long as the next one
is pending in the O-execution. -/
lemma catchUp (hLin : IsLinearization αf L') {γ : List (Label P A)} (hpre : γ <+: αf)
    {K : Config A Bs P L} (hrun : I.run γ = some K) {s : Cfg P C L (Mem Bs)} (hA : Abs Pr s K) :
    ∀ n (d : Cfg P C Unit A.State) (Lj : List (OpId P × A.Op)), L'.length - Lj.length = n →
      Lj <+: L' → QInv Pr γ s d Lj →
      ∃ d' Lj', (sys Pr (atomSem A)).DetReach d d' ∧ QInv Pr γ s d' Lj' ∧ Lj' <+: L' ∧
        Max L' Lj' γ := by
  intro n
  induction n with
  | zero =>
    intro d Lj hn hLj hQ
    refine ⟨d, Lj, .refl _, hQ, hLj, fun y M hM => ?_⟩
    have := congrArg List.length hM
    simp at this; omega
  | succ n ih =>
    intro d Lj hn hLj hQ
    obtain ⟨M, hM⟩ := hLj
    cases M with
    | nil => simp at hM; subst hM; simp at hn
    | cons y M =>
      by_cases hy : Invoked γ y.1
      · obtain ⟨d1, h1, hQ1⟩ := qinv_push hLin hpre hrun hA hQ hM hy
        obtain ⟨d2, Lj2, h2, hQ2, hL2, hmax⟩ :=
          ih d1 (Lj ++ [y]) (by rw [← hM] at hn ⊢; simp at hn ⊢; omega) ⟨M, by simp [← hM]⟩ hQ1
        exact ⟨d2, Lj2, h1.trans h2, hQ2, hL2, hmax⟩
      · refine ⟨d, Lj, .refl _, hQ, ⟨_, hM⟩, fun y' M' hM' => ?_⟩
        rw [← hM] at hM'
        simp only [List.append_cancel_left_eq, List.cons.injEq] at hM'
        rw [hM'.1]; exact hy

end CatchUp

/-! ## Coin-free segments and the segment lemma -/

/-- A coin-free run of the O-system from `sβ` (object history `β`) to `s` (history `γ`). -/
inductive Seg (Pr : Program P A C) (I : Impl A Bs P L) (β : List (Label P A))
    (sβ : Cfg P C L (Mem Bs)) : List (Label P A) → Cfg P C L (Mem Bs) → Prop
  | refl : Seg Pr I β sβ β sβ
  | step {γ : List (Label P A)} {s s' : Cfg P C L (Mem Bs)} {ℓs : List (Label P A)} :
      Seg Pr I β sβ γ s → OStep Pr I s s' ℓs → Seg Pr I β sβ (γ ++ ℓs) s'

lemma Seg.prefix {β γ : List (Label P A)} {sβ s : Cfg P C L (Mem Bs)}
    (h : Seg Pr I β sβ γ s) : β <+: γ := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ _ ih => exact ih.trans (List.prefix_append _ _)

/-- **Segment lemma.** From a complete prefix `β` with `QInv β sβ d (f β)`, along a coin-free
O-run to a complete prefix `γ`, the atomic system can deterministically reach a configuration
`d'` with `QInv γ s d' (f γ)`. -/
lemma seg_main (hall : ∀ p o, I.allowed p o) {f : List (Label P A) → List (OpId P × A.Op)}
    (hf1 : ∀ α K, I.run α = some K → Complete Pi K → IsLinearization α (f α))
    (hf2 : ∀ α β K K', I.run α = some K → I.run β = some K' → Complete Pi K → Complete Pi K' →
      α <+: β → f α <+: f β)
    {β : List (Label P A)} {sβ : Cfg P C L (Mem Bs)} {Kβ : Config A Bs P L}
    {d : Cfg P C Unit A.State} (hβ : I.run β = some Kβ) (hcβ : Complete Pi Kβ)
    (hAβ : Abs Pr sβ Kβ) (hQ : QInv Pr β sβ d (f β))
    {γ : List (Label P A)} {s : Cfg P C L (Mem Bs)} {K : Config A Bs P L}
    (hseg : Seg Pr I β sβ γ s) (hrun : I.run γ = some K) (hc : Complete Pi K) :
    ∃ d', (sys Pr (atomSem A)).DetReach d d' ∧ QInv Pr γ s d' (f γ) := by
  have hLin := hf1 γ K hrun hc
  have key : ∀ γ' s', Seg Pr I β sβ γ' s' → γ' <+: γ → ∃ K', I.run γ' = some K' ∧
      Abs Pr s' K' ∧ ∃ d' Lj, (sys Pr (atomSem A)).DetReach d d' ∧ QInv Pr γ' s' d' Lj ∧
        Lj <+: f γ ∧ Max (f γ) Lj γ' := by
    intro γ' s' hs
    induction hs with
    | refl =>
      intro hp
      obtain ⟨d', Lj, h1, h2, h3, h4⟩ := catchUp hLin hp hβ hAβ _ d (f β) rfl
        (hf2 β γ Kβ K hβ hrun hcβ hc hp) hQ
      exact ⟨Kβ, hβ, hAβ, d', Lj, h1, h2, h3, h4⟩
    | @step γ1 s1 s2 ℓs hs hst ih =>
      intro hp
      obtain ⟨K1, hr1, hA1, d1, Lj1, h1, hQ1, hL1, hm1⟩ := ih ((List.prefix_append _ _).trans hp)
      obtain ⟨K2, hK2, hA2⟩ := hst.run hall hA1
      have hr2 : I.run (γ1 ++ ℓs) = some K2 := by rw [I.run_append_of_eq hr1]; exact hK2
      obtain ⟨d2, h2, hQ2⟩ := qinv_step hLin hp hr1 hA1 hQ1 hL1 hm1 hst
      obtain ⟨d3, Lj3, h3, hQ3, hL3, hm3⟩ := catchUp hLin hp hr2 hA2 _ d2 Lj1 rfl hL1 hQ2
      exact ⟨K2, hr2, hA2, d3, Lj3, h1.trans (h2.trans h3), hQ3, hL3, hm3⟩
  obtain ⟨K', -, -, d', Lj, h1, hQ', ⟨M, hM⟩, hm⟩ := key γ s hseg (List.prefix_refl _)
  cases M with
  | nil => simp only [List.append_nil] at hM; subst hM; exact ⟨d', h1, hQ'⟩
  | cons y M => exact absurd (hLin.mem_invoked (by rw [← hM]; simp)) (hm y M hM)

/-- Random moves of the O-system are program random steps of idle processes. -/
lemma oRand_of_move {s : Cfg P C L (Mem Bs)} {q : P} {m : ℕ} {g : Fin (m + 1) → Cfg P C L (Mem Bs)}
    (h : (sys Pr (implSem I Pi)).move s q = .rand m g) :
    s.busy q = false ∧ ∃ g' : Fin (m + 1) → C, Pr.next q (s.cl q) = .rnd m g' ∧
      g = fun i => { s with cl := Function.update s.cl q (g' i), coins := s.coins + 1,
                            badCoin := s.badCoin || decide (s.inPreamble (implSem I Pi)) } := by
  cases hb : s.busy q
  · cases hn : Pr.next q (s.cl q) with
    | rnd m' g' =>
      rw [move_rnd Pr _ s q hb hn] at h; cases h; exact ⟨rfl, g', rfl, rfl⟩
    | loc c => rw [move_loc Pr _ s q hb hn] at h; cases h
    | call o k =>
      rw [move_call_inl Pr _ s q hb hn (l := I.invoke q (s.lo q) o) (m := s.mem) rfl] at h; cases h
    | done => rw [move_done Pr _ s q hb hn] at h; cases h
  · cases ha : I.act q (s.lo q) with
    | access i o k =>
      have : (implSem I Pi).act q (s.lo q) s.mem s.coins =
          .step (k ((Bs i).δ (s.mem i) o).2) (Function.update s.mem i ((Bs i).δ (s.mem i) o).1) := by
        simp [implSem, ha]
      rw [move_step Pr _ s q hb this] at h; cases h
    | ret r l =>
      have : (implSem I Pi).act q (s.lo q) s.mem s.coins = .ret r l := by simp [implSem, ha]
      cases hn : Pr.next q (s.cl q) with
      | call o k => rw [move_ret Pr _ s q hb this hn] at h; cases h
      | _ => simp [sys, sysMove, hb, this, hn] at h

/-! ## The supersolution -/

/-- The supersolution relation: `x` bounds the safe value at `s`. Either a program random step
already happened at an incomplete prefix (`badCoin`; the safe payoff is `0`), or `s` was reached
by a coin-free run from a complete prefix `β` at which the atomic configuration `d` corresponds,
and `x` is the atomic value at `d`. -/
def Rel (Pr : Program P A C) (I : Impl A Bs P L) (Pi : P → L → Prop)
    (f : List (Label P A) → List (OpId P × A.Op)) (B : (P → C) → Prop)
    (s : Cfg P C L (Mem Bs)) (x : ℝ) : Prop :=
  (s.badCoin = true ∧ x = 0) ∨
  (s.badCoin = false ∧ ∃ (β : List (Label P A)) (sβ : Cfg P C L (Mem Bs)) (Kβ : Config A Bs P L)
    (d : Cfg P C Unit A.State) (γ : List (Label P A)) (K : Config A Bs P L),
    I.run β = some Kβ ∧ Complete Pi Kβ ∧ Abs Pr sβ Kβ ∧ QInv Pr β sβ d (f β) ∧
    Seg Pr I β sβ γ s ∧ I.run γ = some K ∧ Abs Pr s K ∧
    x = (sys Pr (atomSem A)).opt (payB B) d)

omit [DecidableEq P] in
lemma Abs.complete {s : Cfg P C L (Mem Bs)} {K : Config A Bs P L} (hA : Abs Pr s K)
    (h : ¬ s.inPreamble (implSem I Pi)) : Complete Pi K := by
  intro p hp hPi
  refine h ⟨p, ?_, by rw [hA.loc] at hPi; exact hPi⟩
  by_contra hb
  exact hp ((hA.pend p).2 (by simpa using hb))

end TSLSim

open TSLSim in
/-- **Lemma 4.3, property (4)** (simulation part of the paper's Lemma 4.3 / Theorem 4.4 setup):
for a tail strongly linearizable implementation `I` (w.r.t. the preamble mapping `Π`), the best
probability, over strong adversaries, that the program reaches an outcome in `B` with `I` *in an
execution all of whose program random steps happen at prefixes complete w.r.t. `Π`* is at most
the best probability of reaching `B` with the atomic object. -/
theorem optSafe_le_prob_atom {P : Type} [Fintype P] [Nonempty P] [DecidableEq P] {A : ObjSpec}
    {C L : Type} {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}
    (Pr : Program P A C) (I : Impl A Bs P L) (Pi : P → L → Prop)
    (hall : ∀ p o, I.allowed p o) (hTSL : TailStronglyLinearizable I Pi) (B : (P → C) → Prop) :
    (sys Pr (implSem I Pi)).opt (paySafe B) (initCfg Pr (implSem I Pi)) ≤
      prob Pr (atomSem A) B := by
  obtain ⟨-, f, hf1, hf2⟩ := hTSL
  have hp0 : ∀ d : Cfg P C Unit A.State, 0 ≤ payB B d := payB_nonneg B
  have hp1 : ∀ d : Cfg P C Unit A.State, payB B d ≤ 1 := payB_le_one B
  have hinit : Complete Pi (I.initCfg) := fun p h => absurd rfl h
  have hf0 : f [] = [] := by
    have hl := hf1 [] I.initCfg rfl hinit
    cases h : f [] with
    | nil => rfl
    | cons y L =>
      exfalso
      have := hl.op_eq y (by simp [h])
      simp [opOf] at this
  have hnn : ∀ s x, Rel Pr I Pi f B s x → 0 ≤ x := by
    rintro s x (⟨-, rfl⟩ | ⟨-, β, sβ, Kβ, d, γ, K, -, -, -, -, -, -, -, rfl⟩)
    · exact le_rfl
    · exact MDP.opt_nonneg hp0 d
  refine MDP.opt_le_of_super (Rel Pr I Pi f B) hnn ?_ ?_ ?_ (Or.inr ⟨rfl, [],
    initCfg Pr (implSem I Pi), I.initCfg, initCfg Pr (atomSem A), [], I.initCfg, rfl, hinit,
    ?_, ?_, .refl, rfl, ?_, rfl⟩)
  · -- terminal configurations
    rintro s x (⟨hb, rfl⟩ | ⟨hb, β, sβ, Kβ, d, γ, K, hβ, hcβ, hAβ, hQ, hseg, hrun, hA, rfl⟩) ht
    · simp [paySafe, hb]
    · have hinv : ∀ q, s.busy q = true → ∃ o κ, Pr.next q (s.cl q) = .call o κ := by
        intro q hq
        have hp : K.pend q ≠ none := fun h => by simp [(hA.pend q).1 h] at hq
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
        exact ⟨o, hA.call q o ho⟩
      have hall' := (terminal_iff Pr (implSem I Pi) hinv).1 ht
      have hc : Complete Pi K := fun p hp => absurd ((hA.pend p).2 (hall' p).1) hp
      obtain ⟨d', hD, hQ'⟩ := seg_main hall hf1 hf2 hβ hcβ hAβ hQ hseg hrun hc
      have hcl : d'.cl = s.cl := by
        funext q
        rcases hQ'.proc q with h | h
        · exact h.1
        · simp [(hall' q).1] at h
      have ht' : (sys Pr (atomSem A)).Terminal d' :=
        (terminal_iff Pr (atomSem A) (fun q hq => by simp [hQ'.busy q] at hq)).2
          fun q => ⟨hQ'.busy q, by rw [hcl]; exact (hall' q).2⟩
      calc paySafe B s ≤ payB B s := paySafe_le_payB B s
        _ = (sys Pr (atomSem A)).opt (payB B) d' := by
          rw [MDP.opt_of_terminal ht']; simp [payB, hcl]
        _ ≤ _ := MDP.opt_detReach hp0 hp1 hD
  · -- deterministic moves
    rintro s x q s' hR hm
    obtain ⟨ℓs, hst⟩ := oStep_of_move hm
    rcases hR with ⟨hb, rfl⟩ | ⟨hb, β, sβ, Kβ, d, γ, K, hβ, hcβ, hAβ, hQ, hseg, hrun, hA, rfl⟩
    · exact ⟨0, le_rfl, Or.inl ⟨hst.badCoin.1.trans hb, rfl⟩⟩
    · obtain ⟨K', hK', hA'⟩ := hst.run hall hA
      exact ⟨_, le_rfl, Or.inr ⟨hst.badCoin.1.trans hb, β, sβ, Kβ, d, γ ++ ℓs, K', hβ, hcβ, hAβ,
        hQ, hseg.step hst, by rw [I.run_append_of_eq hrun]; exact hK', hA', rfl⟩⟩
  · -- random moves
    rintro s x q m g hR hm
    obtain ⟨hbq, g', hn, rfl⟩ := oRand_of_move hm
    have hx := hnn s x hR
    rcases hR with ⟨hb, rfl⟩ | ⟨hb, β, sβ, Kβ, d, γ, K, hβ, hcβ, hAβ, hQ, hseg, hrun, hA, rfl⟩
    · exact ⟨fun _ => 0, by simp, fun i => Or.inl ⟨by simp [hb], rfl⟩⟩
    by_cases hpre : s.inPreamble (implSem I Pi)
    · exact ⟨fun _ => 0, by simpa using hx, fun i => Or.inl ⟨by simp [hpre], rfl⟩⟩
    have hc : Complete Pi K := hA.complete hpre
    obtain ⟨d', hD, hQ'⟩ := seg_main hall hf1 hf2 hβ hcβ hAβ hQ hseg hrun hc
    have hsync : d'.cl q = s.cl q := by
      rcases hQ'.proc q with h | h
      · exact h.1
      · simp [hbq] at h
    have hmv := move_rnd Pr (atomSem A) d' q (hQ'.busy q) (hsync ▸ hn)
    refine ⟨fun i => (sys Pr (atomSem A)).opt (payB B) _, (MDP.opt_rand hp0 hp1 hmv).trans
      (MDP.opt_detReach hp0 hp1 hD), fun i => Or.inr ⟨by simp [hb, hpre], γ, _, K, _, γ, K,
      hrun, hc, ?_, ?_, .refl, hrun, ?_, rfl⟩⟩
    · exact ⟨hA.loc, hA.mem, hA.pend, fun p o h => by
        have hpq : p ≠ q := fun e => by subst e; simp [(hA.pend p).2 hbq] at h
        simpa [Function.update_of_ne hpq] using hA.call p o h⟩
    · refine ⟨hQ'.mem, by simp [hQ'.coins], ?_, hQ'.busy, fun p => ?_, hQ'.inv, hQ'.compl⟩
      · simp only [hQ'.bad, hb, decide_eq_false hpre]; simp [Cfg.inPreamble, atomSem]
      · by_cases hpq : p = q
        · subst hpq; left; simp [hbq]
        · simpa [Function.update_of_ne hpq] using hQ'.proc p
    · exact ⟨hA.loc, hA.mem, hA.pend, fun p o h => by
        have hpq : p ≠ q := fun e => by subst e; simp [(hA.pend p).2 hbq] at h
        simpa [Function.update_of_ne hpq] using hA.call p o h⟩
  · -- initial abstraction
    exact ⟨rfl, rfl, fun p => by simp [Impl.initCfg, initCfg], fun p o h => by
      simp [Impl.initCfg] at h⟩
  · -- initial correspondence
    rw [hf0]
    exact ⟨rfl, rfl, rfl, fun _ => rfl, fun p => Or.inl ⟨rfl, by simp [initCfg]⟩, by simp,
      fun y h => by simp [Completed] at h⟩
  · exact ⟨rfl, rfl, fun p => by simp [Impl.initCfg, initCfg], fun p o h => by
      simp [Impl.initCfg] at h⟩

end Podc.BluntingAdversary
