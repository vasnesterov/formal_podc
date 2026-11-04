import Papers.PODC2012.DAPUniversalConstruction.Theorem5
import Cslib.Computability.Distributed.SharedMemory.Atomic

/-!
# Non-vacuity of the hypotheses of Theorem 5

The trivial *atomic* implementation of the list (one base object holding the whole list, every
operation applied in one step; `Cslib.SharedMemory.atomicImpl`) is linearizable, wait-free, lets
every process invoke every operation, and satisfies the value-obliviousness assumption for
`Append` (every append accesses and non-trivially writes the single base object). So these
hypotheses of `theorem_5_list` are jointly satisfiable, and by Theorem 5 the atomic
implementation is not feebly disjoint-access parallel (`atomic_not_feeblyDAP`): `Search(0)` and
`Append` contend on the single base object even when their data sets are disjoint.
-/

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P]

/-- The atomic implementation of the list. -/
abbrev atomicList (P : Type) : Impl listSpec (fun _ : Unit => listSpec) P (AtomicLoc listSpec) :=
  atomicImpl listSpec true P

lemma atomicList_linearizable : (atomicList P).Linearizable :=
  (Atomic.perfectHI (A := listSpec) (r₀ := true) (P := P)).linearizable

lemma atomicList_waitFree : (atomicList P).WaitFree := Atomic.waitFree

/-- Every append accesses and writes the single base object. -/
lemma atomicList_seg_sets {C : Config listSpec (fun _ : Unit => listSpec) P (AtomicLoc listSpec)}
    (hC : (atomicList P).Reachable C) {r : P} (hr : C.pend r = none) (v : ℤ) :
    (atomicList P).accessed C ((atomicList P).soloOp r (.append v) C) = Set.univ ∧
      (atomicList P).written C ((atomicList P).soloOp r (.append v) C) = Set.univ := by
  have hOF := Impl.WaitFree.obstructionFree (atomicList P) atomicList_waitFree
  have hs := step_inv_eq_some (I := atomicList P) hr (o := .append v) trivial
  set C₁ : Config listSpec (fun _ : Unit => listSpec) P (AtomicLoc listSpec) :=
    ⟨Function.update C.loc r ((atomicList P).invoke r (C.loc r) (.append v)),
      Function.update C.pend r (some (LOp.append v)), C.mem⟩ with hC₁
  have hp₁ : C₁.pend r ≠ none := by simp [hC₁]
  have hact : (atomicList P).act r (C₁.loc r) = .access () (.append v) (fun x => .done x) := by
    simp [hC₁, atomicImpl]
  have hreach : (atomicList P).Reachable C₁ := by
    obtain ⟨α, hα⟩ := hC
    exact ⟨α ++ [.inv r (.append v)], by rw [run_append_of_eq _ hα, runFrom_singleton, hs]⟩
  have htime : (atomicList P).soloTime r C₁ ≠ 0 := by
    intro h0
    have := (atomicList P).soloTime_spec r C₁ (hOF C₁ r hreach hp₁)
    rw [h0] at this
    exact hp₁ this
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero htime
  have hop : (atomicList P).soloOp r (.append v) C =
      .inv r (.append v) :: (atomicList P).nextLabel C₁ r ::
        (atomicList P).soloLabels r ((atomicList P).soloStep r C₁) t := by
    simp only [soloOp, hs, ht, soloLabels_succ, ite_eq_right hp₁]
  have hnt : ¬ listSpec.ReadOnly (LOp.append v) := fun h => by
    have := h []; simp at this
  rw [hop, accessed_cons_of_step hs, written_cons_of_step hs,
    accessed_cons_of_step (step_nextLabel hp₁), written_cons_of_step (step_nextLabel hp₁)]
  refine ⟨Set.eq_univ_of_forall fun i => ?_, Set.eq_univ_of_forall fun i => ?_⟩
  · refine Or.inr (Or.inl ((stepAccess_nextLabel i).2 ⟨hp₁, _, _, hact⟩))
  · refine Or.inr (Or.inl ((stepWrite_nextLabel i).2 ⟨hp₁, _, _, hact, hnt⟩))

/-- The atomic implementation satisfies Assumption 3 for `Append`. -/
lemma atomicList_valueOblivious : ImplValueOblivious (atomicList P) LOp.append := by
  intro C r hC hq f g n
  have hOF := Impl.WaitFree.obstructionFree (atomicList P) atomicList_waitFree
  have key : ∀ (h : ℕ → ℤ) n, (atomicList P).Reachable (instCfg (atomicList P) C r LOp.append h n) ∧
      (instCfg (atomicList P) C r LOp.append h n).pend r = none := by
    intro h n
    induction n with
    | zero => exact ⟨hC, hq r⟩
    | succ n ih =>
      obtain ⟨⟨α, hα⟩, hp⟩ := ih
      obtain ⟨C', g1, g2, -⟩ := (atomicList P).soloOp_spec hOF r (.append (h n)) trivial hα hp
      have : instCfg (atomicList P) C r LOp.append h (n + 1) = C' := by
        simp only [instCfg, g1, Option.getD_some]
      rw [this]
      exact ⟨⟨_, by rw [run_append_of_eq _ hα, g1]⟩, g2⟩
  obtain ⟨hf1, hf2⟩ := key f n
  obtain ⟨hg1, hg2⟩ := key g n
  obtain ⟨a1, a2⟩ := atomicList_seg_sets hf1 hf2 (f n)
  obtain ⟨b1, b2⟩ := atomicList_seg_sets hg1 hg2 (g n)
  exact ⟨by simp only [instSeg, a1, b1], by simp only [instSeg, a2, b2]⟩

/-- The hypotheses of `theorem_5_list` other than feeble disjoint-access parallelism are
satisfiable; hence the atomic implementation of the list is not feebly disjoint-access parallel
(with at least two processes). -/
theorem atomic_not_feeblyDAP {p q : P} (hpq : p ≠ q) :
    ¬ FeeblyDAP (atomicList P) listDataSet := fun hdap =>
  theorem_5_list (atomicList P) hpq (fun _ _ => trivial) atomicList_linearizable hdap
    atomicList_valueOblivious atomicList_waitFree

/-! ### LL/SC with a trivial `LL`

CSLib's `llscObj` keeps the link set in the object's state, so its `LL` is not
`ObjSpec.ReadOnly`, whereas the paper calls `LL` trivial. LL/SC can equally be encoded with a
version number that the caller keeps locally: `LL` returns the value and the version (a
read-only primitive), `SC v ver` succeeds iff the version is still `ver` (no successful `SC`
since the caller's `LL`) and then increments it. With this encoding the trivial/non-trivial
classification of LL/SC primitives is the paper's, so `theorem_5_list` covers LL/SC-based
implementations with the paper's notion of contention. -/

/-- Primitives of a versioned LL/SC object. -/
inductive VLLOp (V : Type) where
  /-- `LL`: return the value and the current version. -/
  | ll
  /-- `SC(v)` by a process whose last `LL` returned version `ver`. -/
  | sc (v : V) (ver : ℕ)

/-- A versioned LL/SC object: the state is the value and the number of successful `SC`s. -/
abbrev versionedLLSC (V : Type) (v₀ : V) : ObjSpec where
  State := V × ℕ
  Op := VLLOp V
  Resp := V × ℕ × Bool
  init := (v₀, 0)
  δ s o := match o with
    | .ll => (s, (s.1, s.2, true))
    | .sc v ver => if ver = s.2 then ((v, s.2 + 1), (s.1, s.2, true)) else (s, (s.1, s.2, false))

/-- `LL` is trivial for the versioned LL/SC object. -/
example (V : Type) (v₀ : V) : (versionedLLSC V v₀).ReadOnly .ll := fun _ => rfl

/-- `SC` is non-trivial. -/
example (v₀ v : ℕ) (h : v ≠ v₀) : ¬ (versionedLLSC ℕ v₀).ReadOnly (.sc v 0) := fun hro => by
  have := hro (v₀, 0)
  simp_all

end Podc.DAPUniversalConstruction
