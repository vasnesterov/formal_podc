import Papers.PODC2024.MemSnap.Possibilities
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Theorem 7.3: MemSnap is a wait-free linearizable checkpointable object

* `P_nonempty` — `P ≠ ∅` is an invariant of Algorithm 2 (from the corrected Lemma 7.2).
* `theorem_7_3_linearizable` — Algorithm 1 is linearizable (with respect to the checkpointable
  object of Section 4), for every component type, every family of word primitives `W` (any
  read-modify-write primitives), every set of updaters and every initial state.
* `theorem_7_3_waitFree` — Algorithm 1 is wait-free.
* `theorem_7_3_steps` — every operation takes at most 9 accesses of shared memory (`O(1)` time):
  a `click` 2, an `observe` 9, an `update` 9.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

variable {W : ObjSpec} {K : Type} [DecidableEq K] {v₀ : K → W.State}
variable {P : Type} [DecidableEq P] {σ : P}

/-- `P ≠ ∅` is an invariant of the meta-configuration tracker (Algorithm 2). -/
theorem P_nonempty {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : G.PP.Nonempty := by
  obtain ⟨hsub, p, hp⟩ := lemma_7_2_fixed h
  exact ⟨p, hsub hp⟩

variable (W K v₀ σ) in
/-- **Theorem 7.3 of [MemSnap]** (linearizability): Algorithm 1 is a linearizable implementation
of the checkpointable object (an adaptive, RMWable, single-scanner snapshot object). -/
theorem theorem_7_3_linearizable : (memSnap W K v₀ σ).Linearizable :=
  Poss.linearizable_of_tracked fun α C hC => by
    obtain ⟨G, hG⟩ := exists_arun (σ := σ) hC
    obtain ⟨p, hp⟩ := P_nonempty hG
    exact ⟨p, tracked_of_mem_PP hG p hp⟩

/-- The potential used for wait-freedom: an upper bound on the remaining accesses. -/
def pot : Loc W K → ℕ
  | .idle => 0
  | .c1 => 2
  | .c1w _ => 1
  | .c2 => 0
  | .f9 _ _ k => (if k then 0 else 4) + 5
  | .f10 _ _ k _ => (if k then 0 else 4) + 4
  | .f11 _ _ k _ _ => (if k then 0 else 4) + 3
  | .f12 _ _ k _ _ _ => (if k then 0 else 4) + 2
  | .o4 _ => 1
  | .o5 _ => 0
  | .u7 _ _ => 1
  | .u8 _ => 0

lemma pot_fcont (i : K) (u : Option W.Op) : pot (fcont i u : Loc W K) = 1 := by
  cases u <;> rfl

lemma pot_decreases (l : Loc W K) {i : Obj K} {o : (base W K v₀ i).Op}
    {k : (base W K v₀ i).Resp → Loc W K} (h : act W K v₀ l = .access i o k) (x) :
    pot (k x) < pot l := by
  cases l <;> simp only [act, Action.access.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, h1, h2⟩ := h <;> (try subst h1) <;> (try subst h2) <;>
    (try cases x) <;> (try rename_i k2 _ _ _ _; cases k2) <;> (try rename_i k2 _ _ _; cases k2) <;>
    (try rename_i k2 _ _; cases k2) <;> (try rename_i k2 _; cases k2) <;>
    (try cases ‹Option W.Op›) <;> simp [pot, fcont] <;> (try split_ifs) <;> simp_all

variable (W K v₀ σ) in
/-- **Theorem 7.3 of [MemSnap]** (wait-freedom): Algorithm 1 is wait-free. -/
theorem theorem_7_3_waitFree : (memSnap W K v₀ σ).WaitFree :=
  (memSnap W K v₀ σ).waitFree_of_potential (fun _ l => pot l) (fun _ l _ _ _ h x => pot_decreases l h x)

/-- **Theorem 7.3 of [MemSnap]** (time complexity): after invoking an operation, a process
performs at most 9 accesses to shared memory before it returns (2 for a `click`). -/
theorem theorem_7_3_steps {α γ : List (CLabel W K v₀ P)} {p : P} {o : COp W K}
    (hv : (memSnap W K v₀ σ).Valid (α ++ .inv p o :: γ)) (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ 9 ∧ (o = .click → γ.countP (Label.isTauOf p) ≤ 2) := by
  obtain ⟨l, h⟩ := (memSnap W K v₀ σ).tauSteps_le_potential_invoke (fun _ l => pot l)
    (fun _ l _ _ _ h x => pot_decreases l h x) hv hret
  refine ⟨h.trans ?_, fun ho => h.trans ?_⟩
  · cases o <;> simp [memSnap, invoke, pot]
  · subst ho; simp [memSnap, invoke, pot]

end Podc.MemSnap
