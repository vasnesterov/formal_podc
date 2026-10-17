import Papers.PODC2026.ConsistentRefereeing.LongLivedBasic
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Objects.FetchAdd
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister
import Cslib.Computability.Distributed.SharedMemory.Objects.Snapshot
import Cslib.Computability.Distributed.SharedMemory.OneAccess
import Cslib.Computability.Distributed.SharedMemory.Task
import Cslib.Foundations.Data.Finset.SumUpdate

/-!
# Long-lived contest from counters, max registers and snapshots (Lemma 14 of [ACE26])

Possibility results complementing Theorems 25 and 30: wait-free strongly linearizable
long-lived contest implementations exist from an atomic readable fetch&increment (used as a
counter), from an atomic max register and from an atomic snapshot (Lemma 14 of [ACE26]). In
particular the hypotheses of Theorems 25 and 30 are not contradictory in themselves: the
restriction on the base objects is essential.

All three implementations are *single-access* (every operation applies one primitive), so we
use `OneAccess` (CSLib) with a deterministic refinement `ctObj P f` of the long-lived contest
(`decide` returns `f` of the vector of `compete` counts, `f` = sum or maximum) and transfer the
result to the nondeterministic specification `llSpec` (`IsNLinearization.of_ctObj`) and to the
object type `llObj P` (`implL`, a relabelling of the object type; `implL_nStronglyLinearizable`,
`implL_waitFree`).

The base objects are atomic (the paper allows strongly linearizable implementations of them,
which needs a composition theorem not available here).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Referee

open Impl

variable {P : Type} [DecidableEq P]

/-- A deterministic refinement of the long-lived contest object: the state counts the
`compete` operations of every process, `decide` returns `f` of the counts. -/
abbrev ctObj (P : Type) [DecidableEq P] (f : (P → ℕ) → ℕ) : ObjSpec where
  State := P → ℕ
  Op := ContestOp P
  Resp := LLResp
  init := fun _ => 0
  δ q
    | .compete i => (Function.update q i (q i + 1), .ok)
    | .decide => (q, .val (f q))

/-- If `f` bounds every count, the deterministic refinement refines `llSpec`. -/
lemma legal_of_ctObj {f : (P → ℕ) → ℕ} (hf : ∀ q c, q c ≤ f q) :
    ∀ (q : P → ℕ) (l : List (ContestOp P × LLResp)),
      (ctObj P f).toNSpec.Legal q l → (llSpec P).Legal q l := by
  intro q l h
  induction l generalizing q with
  | nil => trivial
  | cons y l ih =>
    obtain ⟨o, r⟩ := y
    obtain ⟨q', hs, hl⟩ := h
    refine ⟨q', ?_, ih q' hl⟩
    cases o with
    | compete i =>
      simp only [ObjSpec.toNSpec] at hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact ⟨rfl, rfl⟩
    | decide =>
      simp only [ObjSpec.toNSpec] at hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      exact ⟨⟨f q, rfl, hf q⟩, rfl⟩

lemma IsNLinearization.of_ctObj {f : (P → ℕ) → ℕ} (hf : ∀ q c, q c ≤ f q)
    {α : List (Label P (ctObj P f))} {L : List (OpId P × ContestOp P × LLResp)}
    (h : IsNLinearization (ctObj P f).toNSpec α L) :
    IsNLinearization (A := ctObj P f) (llSpec P) α L :=
  ⟨h.nodup, h.op_eq, h.resp_eq, h.complete, h.realtime, legal_of_ctObj hf _ _ h.legal⟩

/-! ### Relabelling the object type -/

section Retype

variable {f : (P → ℕ) → ℕ} {ι L : Type} {B : ι → ObjSpec} [DecidableEq ι]

/-- Labels of `ctObj` executions as labels of `llObj` executions. -/
def lblL : Label P (ctObj P f) → LLabel P
  | .inv p o => .inv p o
  | .ret p r => .ret p r
  | .tau p => .tau p

/-- The inverse of `lblL`. -/
def lblC : LLabel P → Label P (ctObj P f)
  | .inv p o => .inv p o
  | .ret p r => .ret p r
  | .tau p => .tau p

@[simp] lemma lblL_lblC (ℓ : LLabel P) : lblL (f := f) (lblC ℓ) = ℓ := by cases ℓ <;> rfl
@[simp] lemma lblC_lblL (ℓ : Label P (ctObj P f)) : lblC (lblL ℓ) = ℓ := by cases ℓ <;> rfl

@[simp] lemma map_lblL_lblC (α : List (LLabel P)) :
    (α.map (lblC (f := f))).map lblL = α := by simp [List.map_map, Function.comp_def]

@[simp] lemma map_lblC_lblL (α : List (Label P (ctObj P f))) :
    (α.map lblL).map lblC = α := by simp [List.map_map, Function.comp_def]

/-- Actions of `ctObj` implementations as actions of `llObj` implementations. -/
def actL : Action (ctObj P f) B L → Action (llObj P) B L
  | .access i o k => .access i o k
  | .ret r l => .ret r l

/-- An implementation of `ctObj P f` seen as an implementation of `llObj P`. -/
def implL (I : Impl (ctObj P f) B P L) : Impl (llObj P) B P L where
  memInit := I.memInit
  locInit := I.locInit
  invoke := I.invoke
  act p l := actL (I.act p l)
  allowed := I.allowed

/-- Configurations of `ctObj` implementations as configurations of `llObj` ones. -/
def cfgL (C : Config (ctObj P f) B P L) : Config (llObj P) B P L := ⟨C.loc, C.pend, C.mem⟩

lemma step_implL (I : Impl (ctObj P f) B P L) (C : Config (ctObj P f) B P L)
    (ℓ : Label P (ctObj P f)) :
    (implL I).step (cfgL C) (lblL ℓ) = (I.step C ℓ).map cfgL := by
  classical
  cases ℓ with
  | inv p o =>
    by_cases h : C.pend p = none ∧ I.allowed p o
    · simp [lblL, Impl.step, cfgL, implL, h]
    · simp [lblL, Impl.step, cfgL, implL, h]
  | tau p =>
    by_cases h : C.pend p = none
    · simp [lblL, Impl.step, cfgL, h]
    · cases ha : I.act p (C.loc p) <;> simp [lblL, Impl.step, cfgL, implL, h, ha, actL]
  | ret p r =>
    by_cases h : C.pend p = none
    · simp [lblL, Impl.step, cfgL, h]
    · cases ha : I.act p (C.loc p) with
      | access i o k => simp [lblL, Impl.step, cfgL, implL, h, ha, actL]
      | ret r' l =>
        by_cases hr : r = r'
        · simp [lblL, Impl.step, cfgL, implL, h, ha, actL, hr]
        · simp [lblL, Impl.step, cfgL, implL, h, ha, actL, hr]

lemma runFrom_implL (I : Impl (ctObj P f) B P L) (C : Config (ctObj P f) B P L)
    (α : List (Label P (ctObj P f))) :
    (implL I).runFrom (cfgL C) (α.map lblL) = (I.runFrom C α).map cfgL := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [List.map_cons, runFrom_cons, step_implL]
    cases I.step C ℓ with
    | none => rfl
    | some C' => simp [ih]

lemma run_implL (I : Impl (ctObj P f) B P L) (α : List (Label P (ctObj P f))) :
    (implL I).run (α.map lblL) = (I.run α).map cfgL :=
  runFrom_implL I I.initCfg α

lemma valid_implL_iff (I : Impl (ctObj P f) B P L) (α : List (Label P (ctObj P f))) :
    (implL I).Valid (α.map lblL) ↔ I.Valid α := by
  simp only [Impl.Valid, run_implL]
  constructor
  · rintro ⟨C, hC⟩
    cases h : I.run α with
    | none => simp [h] at hC
    | some C' => exact ⟨C', rfl⟩
  · rintro ⟨C, hC⟩; exact ⟨cfgL C, by simp [hC]⟩

lemma opsOf_map_lblL (α : List (Label P (ctObj P f))) (p : P) :
    opsOf (α.map lblL) p = opsOf α p := by
  simp only [opsOf, List.filterMap_map]
  congr 1; funext ℓ; cases ℓ <;> rfl

lemma respsOf_map_lblL (α : List (Label P (ctObj P f))) (p : P) :
    respsOf (α.map lblL) p = respsOf α p := by
  simp only [respsOf, List.filterMap_map]
  congr 1; funext ℓ; cases ℓ <;> rfl

lemma precedes_map_lblL (α : List (Label P (ctObj P f))) (a b : OpId P) :
    Precedes (α.map lblL) a b ↔ Precedes α a b := by
  constructor
  · rintro ⟨β, γ, h, h1, h2⟩
    refine ⟨β.map lblC, γ.map lblC, ?_, ?_, ?_⟩
    · rw [← List.map_append, ← h, map_lblC_lblL]
    · simp only [Completed] at h1 ⊢
      rw [← respsOf_map_lblL, map_lblL_lblC]; exact h1
    · simp only [Invoked] at h2 ⊢
      rw [← opsOf_map_lblL, map_lblL_lblC]; exact h2
  · rintro ⟨β, γ, h, h1, h2⟩
    refine ⟨β.map lblL, γ.map lblL, by rw [h, List.map_append], ?_, ?_⟩
    · simp only [Completed] at h1 ⊢; rw [respsOf_map_lblL]; exact h1
    · simp only [Invoked] at h2 ⊢; rw [opsOf_map_lblL]; exact h2

lemma isNLinearization_map_lblL (S : NSpec (ContestOp P) LLResp)
    (α : List (Label P (ctObj P f))) (Lin : List (OpId P × ContestOp P × LLResp)) :
    IsNLinearization (A := llObj P) S (α.map lblL) Lin ↔
      IsNLinearization (A := ctObj P f) S α Lin := by
  have hop : ∀ x, opOf (α.map lblL) x = opOf α x := fun x => by
    simp only [opOf, opsOf_map_lblL]
  have hresp : ∀ x, respOf (α.map lblL) x = respOf α x := fun x => by
    simp only [respOf, respsOf_map_lblL]
  have hcomp : ∀ x, Completed (α.map lblL) x ↔ Completed α x := fun x => by
    simp only [Completed, respsOf_map_lblL]
  constructor
  · intro h
    exact ⟨h.nodup, fun y hy => (hop _).symm.trans (h.op_eq y hy),
      fun y hy r hr => h.resp_eq y hy r ((hresp _).trans hr),
      fun a ha => h.complete a ((hcomp a).2 ha),
      fun a b hab hb => h.realtime a b ((precedes_map_lblL α a b).2 hab) hb, h.legal⟩
  · intro h
    exact ⟨h.nodup, fun y hy => (hop _).trans (h.op_eq y hy),
      fun y hy r hr => h.resp_eq y hy r ((hresp _).symm.trans hr),
      fun a ha => h.complete a ((hcomp a).1 ha),
      fun a b hab hb => h.realtime a b ((precedes_map_lblL α a b).1 hab) hb, h.legal⟩

/-- Strong linearizability transfers along the relabelling. -/
theorem implL_nStronglyLinearizable (I : Impl (ctObj P f) B P L)
    {S : NSpec (ContestOp P) LLResp} (h : I.NStronglyLinearizable S) :
    (implL I).NStronglyLinearizable S := by
  obtain ⟨g, hg, hpc⟩ := h
  refine ⟨fun α => g (α.map lblC), fun α hα => ?_, fun α β hβ hαβ => ?_⟩
  · have hv : I.Valid (α.map lblC) := by
      rw [← valid_implL_iff, map_lblL_lblC]; exact hα
    have := (isNLinearization_map_lblL S (α.map lblC) _).2 (hg _ hv)
    rwa [map_lblL_lblC] at this
  · have hv : I.Valid (β.map lblC) := by
      rw [← valid_implL_iff, map_lblL_lblC]; exact hβ
    exact hpc _ _ hv (hαβ.map _)

/-- Wait-freedom by a potential transfers along the relabelling. -/
theorem implL_waitFree (I : Impl (ctObj P f) B P L) (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) < μ p l) :
    (implL I).WaitFree := by
  refine (implL I).waitFree_of_potential μ (fun p l i o k h x => ?_)
  simp only [implL] at h
  cases ha : I.act p l with
  | access i' o' k' =>
    rw [ha] at h
    simp only [actL, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    rw [← eq_of_heq hk]
    exact hμ p l i' o' k' ha x
  | ret r l' => rw [ha] at h; simp [actL] at h

end Retype

/-- Strong linearizability w.r.t. the deterministic refinement gives strong linearizability
w.r.t. `llSpec`. -/
lemma nStronglyLinearizable_llSpec {f : (P → ℕ) → ℕ} (hf : ∀ q c, q c ≤ f q) {ι L : Type}
    {B : ι → ObjSpec} [DecidableEq ι] {I : Impl (ctObj P f) B P L}
    (h : I.StronglyLinearizable) : I.NStronglyLinearizable (llSpec P) := by
  obtain ⟨g, hg, hpc⟩ := h.nStronglyLinearizable
  exact ⟨g, fun α hα => IsNLinearization.of_ctObj hf (hg α hα), hpc⟩

/-- The potential of single-access implementations: `1` before the access, `0` otherwise. -/
def oaPot {A : ObjSpec} {D : Type} (_ : P) : OALoc D A → ℕ
  | .pend _ _ => 1
  | _ => 0

lemma oneAccess_potential {A : ObjSpec} {ι D : Type} {B : ι → ObjSpec}
    (S : OneAccess A B P D) (r₀ : A.Resp) :
    ∀ p l i o k, (S.impl r₀).act p l = .access i o k → ∀ x, oaPot p (k x) < oaPot p l := by
  intro p l i o k hact x
  cases l with
  | idle d => simp [OneAccess.impl] at hact
  | done d r => simp [OneAccess.impl] at hact
  | pend d o' =>
    simp only [OneAccess.impl, Action.access.injEq] at hact
    obtain ⟨rfl, -, hk⟩ := hact
    rw [← eq_of_heq hk]
    simp [oaPot]

variable [Fintype P]

lemma sup_update_succ (q : P → ℕ) (p : P) :
    Finset.univ.sup (Function.update q p (q p + 1)) = max (Finset.univ.sup q) (q p + 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro c _
    by_cases hc : c = p
    · subst hc; simp
    · rw [Function.update_of_ne hc]
      exact le_max_of_le_left (Finset.le_sup (Finset.mem_univ c))
  · apply max_le
    · apply Finset.sup_le
      intro c _
      by_cases hc : c = p
      · subst hc
        exact le_trans (Nat.le_succ _) (by
          have := Finset.le_sup (f := Function.update q c (q c + 1)) (Finset.mem_univ c)
          simpa using this)
      · have := Finset.le_sup (f := Function.update q p (q p + 1)) (Finset.mem_univ c)
        rwa [Function.update_of_ne hc] at this
    · have := Finset.le_sup (f := Function.update q p (q p + 1)) (Finset.mem_univ p)
      simpa using this

/-! ### Lemma 14: counter -/

/-- The long-lived contest from a counter (an atomic readable fetch&increment): `compete`
increments the counter, `decide` reads it. -/
def ctrScheme : OneAccess (ctObj P (fun q => ∑ c, q c)) (fun _ : Unit => rfaiObj) P Unit where
  memInit _ := 0
  dInit _ := ()
  obj _ _ _ := ()
  prim _ _ o := match o with
    | .compete _ => .fai
    | .decide => .read
  upd _ _ _ _ := ()
  out _ _ o r := match o with
    | .compete _ => .ok
    | .decide => .val r

lemma ctrScheme_sim : (ctrScheme (P := P)).Sim (fun m _ q => m () = ∑ c, q c) := by
  refine ⟨by simp [ctrScheme], ?_⟩
  intro m ds s p d o _ hab _
  cases o with
  | compete i =>
    refine ⟨?_, rfl⟩
    simp only [ctrScheme, Function.update_self]
    have := Fintype.sum_update_add s i (s i + 1)
    rw [hab]; omega
  | decide =>
    refine ⟨?_, ?_⟩
    · simp only [ctrScheme, Function.update_self]; exact hab
    · simp only [ctrScheme]; rw [hab]

/-- **Lemma 14 of [ACE26] (counter).** There is a wait-free strongly linearizable long-lived
contest implementation from a single atomic counter (readable fetch&increment). -/
theorem lemma14_counter (ref : P) :
    ∃ (L : Type) (I : Impl (llObj P) (fun _ : Unit => rfaiObj) P L),
      (∀ p, I.allowed p (roleOp ref p)) ∧ I.WaitFree ∧ I.NStronglyLinearizable (llSpec P) :=
  ⟨_, implL ((ctrScheme (P := P)).impl .ok), fun _ => trivial,
    implL_waitFree _ oaPot (oneAccess_potential _ _),
    implL_nStronglyLinearizable _ (nStronglyLinearizable_llSpec
      (fun _ c => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
      (ctrScheme.stronglyLinearizable ctrScheme_sim _))⟩

/-! ### Lemma 14: max register -/

/-- The long-lived contest from a max register: a competitor writes its number of `compete`
operations (kept locally) into the max register, `decide` reads it. -/
def maxScheme (ref : P) :
    OneAccess (ctObj P (fun q => Finset.univ.sup q)) (fun _ : Unit => maxRegObj) P ℕ where
  memInit _ := 0
  dInit _ := 0
  obj _ _ _ := ()
  prim _ d o := match o with
    | .compete _ => .writeMax (d + 1)
    | .decide => .readMax
  upd _ d o _ := match o with
    | .compete _ => d + 1
    | .decide => d
  out _ _ o r := match o with
    | .compete _ => .ok
    | .decide => .val r
  allowed p o := o = roleOp ref p

lemma maxScheme_sim (ref : P) :
    (maxScheme ref).Sim (fun m ds q => (∀ c, ds c = q c) ∧ m () = Finset.univ.sup q) := by
  refine ⟨⟨fun _ => rfl, (le_antisymm (Finset.sup_le fun _ _ => le_rfl) (Nat.zero_le _)).symm⟩,
    ?_⟩
  intro m ds s p d o hd hab hal
  obtain ⟨hds, hm⟩ := hab
  simp only [maxScheme, roleOp] at hal
  split_ifs at hal with hp
  · subst hal
    refine ⟨⟨fun c => ?_, ?_⟩, by simp [maxScheme, hm]⟩
    · by_cases hc : c = p
      · subst hc; simp [maxScheme, ← hd, hds]
      · simp [maxScheme, Function.update_of_ne hc, hds]
    · simp [maxScheme, hm]
  · subst hal
    refine ⟨⟨fun c => ?_, ?_⟩, ?_⟩
    · by_cases hc : c = p
      · subst hc; simp [maxScheme, ← hd, hds]
      · simp [maxScheme, Function.update_of_ne hc, hds]
    · simp only [maxScheme, Function.update_self]
      rw [sup_update_succ, hm, ← hd, hds]
    · rfl

/-- **Lemma 14 of [ACE26] (max register).** There is a wait-free strongly linearizable
long-lived contest implementation from a single atomic max register. -/
theorem lemma14_maxRegister (ref : P) :
    ∃ (L : Type) (I : Impl (llObj P) (fun _ : Unit => maxRegObj) P L),
      (∀ p, I.allowed p (roleOp ref p)) ∧ I.WaitFree ∧ I.NStronglyLinearizable (llSpec P) :=
  ⟨_, implL ((maxScheme ref).impl .ok), fun _ => rfl,
    implL_waitFree _ oaPot (oneAccess_potential _ _),
    implL_nStronglyLinearizable _ (nStronglyLinearizable_llSpec
      (fun _ c => Finset.le_sup (Finset.mem_univ c))
      ((maxScheme ref).stronglyLinearizable (maxScheme_sim ref) _))⟩

/-! ### Lemma 14: snapshot -/

/-- The long-lived contest from a single-writer snapshot: a competitor writes its number of
`compete` operations into its component, `decide` scans and returns the sum. -/
noncomputable def snapScheme (ref : P) :
    OneAccess (ctObj P (fun q => ∑ c, q c)) (fun _ : Unit => snapObj (Fintype.card P)) P ℕ where
  memInit _ := fun _ => 0
  dInit _ := 0
  obj _ _ _ := ()
  prim p d o := match o with
    | .compete _ => .update (Fintype.equivFin P p) (d + 1)
    | .decide => .scan
  upd _ d o _ := match o with
    | .compete _ => d + 1
    | .decide => d
  out _ _ o r := match o with
    | .compete _ => .ok
    | .decide => .val (∑ i, r i)
  allowed p o := o = roleOp ref p

lemma snapScheme_sim (ref : P) :
    (snapScheme ref).Sim (fun m ds q => (∀ c, ds c = q c) ∧
      ∀ c, m () (Fintype.equivFin P c) = q c) := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro m ds s p d o hd hab hal
  obtain ⟨hds, hm⟩ := hab
  simp only [snapScheme, roleOp] at hal
  split_ifs at hal with hp
  · subst hal
    refine ⟨⟨fun c => ?_, fun c => ?_⟩, ?_⟩
    · by_cases hc : c = p
      · subst hc; simp [snapScheme, ← hd, hds]
      · simp [snapScheme, Function.update_of_ne hc, hds]
    · simp [snapScheme, hm]
    · simp only [snapScheme]
      congr 1
      exact (Fintype.sum_equiv (Fintype.equivFin P) s _ (fun c => (hm c).symm)).symm
  · subst hal
    refine ⟨⟨fun c => ?_, fun c => ?_⟩, rfl⟩
    · by_cases hc : c = p
      · subst hc; simp [snapScheme, ← hd, hds]
      · simp [snapScheme, Function.update_of_ne hc, hds]
    · by_cases hc : c = p
      · subst hc; simp [snapScheme, ← hd, hds]
      · have : Fintype.equivFin P c ≠ Fintype.equivFin P p := fun h =>
          hc ((Fintype.equivFin P).injective h)
        simp [snapScheme, Function.update_of_ne this, Function.update_of_ne hc, hm]

/-- **Lemma 14 of [ACE26] (snapshot).** There is a wait-free strongly linearizable long-lived
contest implementation from a single atomic (single-writer) snapshot object. -/
theorem lemma14_snapshot (ref : P) :
    ∃ (L : Type) (I : Impl (llObj P) (fun _ : Unit => snapObj (Fintype.card P)) P L),
      (∀ p, I.allowed p (roleOp ref p)) ∧ I.WaitFree ∧ I.NStronglyLinearizable (llSpec P) :=
  ⟨_, implL ((snapScheme ref).impl .ok), fun _ => rfl,
    implL_waitFree _ oaPot (oneAccess_potential _ _),
    implL_nStronglyLinearizable _ (nStronglyLinearizable_llSpec
      (fun _ c => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
      ((snapScheme ref).stronglyLinearizable (snapScheme_sim ref) _))⟩

end Cslib.SharedMemory.Referee
