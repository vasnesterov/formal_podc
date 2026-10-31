import Papers.PODC2019.FastReadsRegisterSim.Consistency
import Papers.PODC2019.FastReadsRegisterSim.ReadTree

/-!
# Consequences of atomicity used in Section 4, and small helpers

* `lastVal v₀ ws` — the value of a register after the writes `ws` (`v₀` if none);
* `lin_read`, `lin_reads` — in an atomic simulation, in an execution where `w` invoked the writes
  `ws` and every other process only reads, a read returns `lastVal` of a prefix of `ws` of length
  at least the number of writes preceding it; for two reads `x → y` the prefixes are ordered;
* `exists_flip` — first change of a Boolean sequence;
* `lrun_succ_mem_eq` — one step changes at most one register.
-/

set_option linter.unusedSectionVars false

namespace Podc.FastReadsRegisterSim

open Cslib.SharedMemory

variable {V : Type} {v₀ : V} {ι P L : Type} [DecidableEq P] [DecidableEq ι]

/-- The value of a register after the writes `ws`. -/
def lastVal (v₀ : V) (ws : List V) : V := ws.foldl (fun _ v => v) v₀

@[simp] lemma lastVal_nil : lastVal v₀ [] = v₀ := rfl

@[simp] lemma lastVal_append_singleton (ws : List V) (v : V) : lastVal v₀ (ws ++ [v]) = v := by
  simp [lastVal]

lemma runOps_writes (q : V) (ws : List V) :
    (register V v₀).runOps q (ws.map RWOp.write) = ws.foldl (fun _ v => v) q := by
  induction ws generalizing q with
  | nil => rfl
  | cons v ws ih => simp only [List.map_cons, List.foldl_cons]; exact ih v

section Lin

variable {I : Sim V v₀ ι P L} {w : P}

lemma singleWriter_of {α : List (Label P (register V v₀))}
    (hother : ∀ q, q ≠ w → ∀ o ∈ opsOf α q, o = .read) : SingleWriter v₀ α w := by
  intro y u hy
  by_contra hne
  have hmem : RWOp.write u ∈ opsOf α y.1 := List.mem_of_getElem? hy
  have := hother y.1 hne _ hmem
  cases this

/-- **One read in an atomic simulation.** -/
lemma lin_read (hatom : I.Atomic w) {α : List (Label P (register V v₀))} (hval : I.Valid α)
    {ws : List V} (hw : opsOf α w = ws.map .write)
    (hother : ∀ q, q ≠ w → ∀ o ∈ opsOf α q, o = .read) {x : OpId P} {vx : V}
    (hx : ReadReturns v₀ α x vx) (M₀ : ℕ) (hpre : ∀ j < M₀, Precedes α (w, j) x) :
    ∃ j, M₀ ≤ j ∧ j ≤ ws.length ∧ vx = lastVal v₀ (ws.take j) := by
  obtain ⟨Lin, hL⟩ := hatom α hval (singleWriter_of hother)
  have hα := hval.wellFormed
  have hro : ∀ y ∈ Lin, y.1.1 ≠ w → (register V v₀).ReadOnly y.2 := by
    intro y hy hne
    rw [hother _ hne _ (hL.op_mem hy)]; exact register_read_readOnly v₀
  obtain ⟨j, h1, h2, o, ho, hr⟩ := hL.resp_eq hα w hro hx.2 M₀ hpre
  rw [hx.1] at ho; cases ho
  refine ⟨j, h1, by simpa [hw] using h2, ?_⟩
  rw [hr, hw, ← List.map_take, register_read, runOps_writes]; rfl

/-- **Two reads `x → y` in an atomic simulation** (no new–old inversion). -/
lemma lin_reads (hatom : I.Atomic w) {α : List (Label P (register V v₀))} (hval : I.Valid α)
    {ws : List V} (hw : opsOf α w = ws.map .write)
    (hother : ∀ q, q ≠ w → ∀ o ∈ opsOf α q, o = .read) {x y : OpId P} {vx vy : V}
    (hx : ReadReturns v₀ α x vx) (hy : ReadReturns v₀ α y vy) (hxy : Precedes α x y)
    (M₀ : ℕ) (hpre : ∀ j < M₀, Precedes α (w, j) x) :
    ∃ j j', M₀ ≤ j ∧ j ≤ j' ∧ j' ≤ ws.length ∧ vx = lastVal v₀ (ws.take j) ∧
      vy = lastVal v₀ (ws.take j') := by
  obtain ⟨Lin, hL⟩ := hatom α hval (singleWriter_of hother)
  have hα := hval.wellFormed
  have hro : ∀ y ∈ Lin, y.1.1 ≠ w → (register V v₀).ReadOnly y.2 := by
    intro y hy hne
    rw [hother _ hne _ (hL.op_mem hy)]; exact register_read_readOnly v₀
  obtain ⟨j, j', h1, h2, h3, ⟨o, ho, hr⟩, ⟨o', ho', hr'⟩⟩ :=
    resp_reads hL hα w hro hx.2 hy.2 hxy M₀ hpre
  rw [hx.1] at ho; cases ho
  rw [hy.1] at ho'; cases ho'
  refine ⟨j, j', h1, h2, by simpa [hw] using h3, ?_, ?_⟩
  · rw [hr, hw, ← List.map_take, register_read, runOps_writes]; rfl
  · rw [hr', hw, ← List.map_take, register_read, runOps_writes]; rfl

end Lin

/-- First change of a Boolean sequence. -/
lemma exists_flip (f : ℕ → Bool) {N : ℕ} {b : Bool} (h0 : f 0 ≠ b) (hN : f N = b) :
    ∃ t < N, f (t + 1) = b ∧ ∀ t' ≤ t, f t' ≠ b := by
  classical
  rcases N with _ | N
  · exact absurd hN h0
  have hex : ∃ t, f (t + 1) = b := ⟨N, hN⟩
  refine ⟨Nat.find hex, Nat.lt_succ_of_le (Nat.find_min' hex hN), Nat.find_spec hex, ?_⟩
  · intro t' ht'
    rcases t' with _ | t'
    · exact h0
    · exact Nat.find_min hex (by omega)

/-- One local step changes at most one register. -/
lemma lstep_mem_eq_of_ne {act : L → Action (register V v₀) (BinRegs ι) L} {s : L × Mem ι}
    {i j : ι} (hij : i ≠ j) (hi : (lstep act s).2 i ≠ s.2 i) : (lstep act s).2 j = s.2 j := by
  by_contra hj
  have hacc : ∀ k, (lstep act s).2 k ≠ s.2 k → Acc act s k := by
    intro k hk; by_contra hna; exact hk (lstep_mem_of_not_acc hna)
  exact hij (acc_unique (hacc i hi) (hacc j hj))

end Podc.FastReadsRegisterSim
