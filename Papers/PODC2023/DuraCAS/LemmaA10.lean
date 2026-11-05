import Papers.PODC2023.DuraCAS.Refinement

/-!
# Lemma A.10.2 of the full version is false as stated; the corrected statement

Lemma A.10.2: "if `h.DetVal` is changed at any time `t` by the execution of line 15 by some
`FORWARD(h')`, then `X.hndl = h` and `h.pc ∈ {13, 14, 15}`."

`lemmaA10_2_counterexample`: process `0` installs at line 10 of an `ECSC` on `Z` (inside
`CAS(0, 1)`), crashes before its `FORWARD`, and restarts at line 22 of `RECOVER` (the per-process
discipline). Process `1` runs `CAS(0, 1)` on the same object: its `ECSC` is a hitchhiker, its
`FORWARD` reads the pending install of `h₀ = (0, crit)` and raises `h₀.DetVal` from `0` to `1` at
line 15 — while process `0` is not in lines 13–15 (it has no active DurEC call at all).

`detVal_help_pending` is the corrected statement used in the proof (it follows from `Inv`): a
successful `CAS` on `g.DetVal` at line 15 writes the sequence number `e` of the *pending* install
`(g, e)` of the object being forwarded.
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- **Lemma A.10.2, corrected.** In a reachable state, if the `CAS` of line 15 of a `FORWARD` of
process `p` (with `x = (g, e)` and `ŝ = d`) is about to succeed, then `(g, e)` is the pending
install of the object (`X = (g, e)` and `Y.seq < e`). -/
theorem detVal_help_pending {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) {p : P} {f : Frame P K V} {g : Hd P} {e d : ℕ}
    (hf : (s.ps p).fr = some f) (hpc : f.pc = .f15 g e d) (hc : d < e ∧ s.m.det g = d) :
    s.m.X f.o = (some g, e) ∧ (s.m.Y f.o).1 < e := by
  obtain ⟨a, -, hI⟩ := reach_inv h
  have h5 := ((hI.p p).fr f hf).stage
  simp only [StageOK, hpc] at h5
  rcases h5.2.1 with ⟨hx, hp⟩ | ⟨-, h⟩
  · refine ⟨hx, ?_⟩; unfold Pend at hp; rw [hx] at hp; exact hp
  · have := hI.g.lsDet g; omega

/-- **Lemma A.2.** In a reachable state, `Y.seq ≤ X.seq` for every DurEC object (an install
makes `X.seq > Y.seq`, the next move brings `Y.seq` up to `X.seq`). -/
theorem reach_Yseq_le_Xseq {init : K → V} {hv0 : Hd P → V × Bool} {s : St P K V}
    (h : Reach init hv0 s) (o : Obj K) : (s.m.Y o).1 ≤ (s.m.X o).2 := by
  obtain ⟨a, -, hI⟩ := reach_inv h
  exact hI.g.yx o

/-- Run a schedule (none if some label is not enabled). -/
def runSched (s : St P K V) : List (Lbl P K V) → Option (St P K V)
  | [] => some s
  | ℓ :: ls => if ℓ.En s then runSched (ℓ.apply s) ls else none

theorem reach_of_runSched {init : K → V} {hv0} {s s' : St P K V} (hs : Reach init hv0 s) :
    ∀ ls, runSched s ls = some s' → Reach init hv0 s' := by
  intro ls
  induction ls generalizing s with
  | nil => intro h; simp [runSched] at h; exact h ▸ hs
  | cons ℓ ls ih =>
    intro h
    simp only [runSched] at h
    split_ifs at h with hen
    exact ih (hs.tail ⟨ℓ, hen, rfl⟩) h

section Example

/-- The schedule: `p₀` runs `CAS(0, 1)` up to its install on `Z` and crashes; `p₁` runs
`CAS(0, 1)` up to line 15 of the `FORWARD` of its (hitchhiking) `ECSC`. -/
def a10Schedule : List (Lbl (Fin 2) Unit ℕ) :=
  [.invoke 0 () (.cas 0 1), .step 0, .step 0, .step 0, .step 0, .step 0, .step 0, .step 0,
   .step 0, .crash 0,
   .invoke 1 () (.cas 0 1), .step 1, .step 1, .step 1, .step 1, .step 1, .step 1, .step 1,
   .step 1, .step 1, .step 1]

theorem a10Schedule_spec :
    (runSched (initSt (fun _ => 0) (fun _ => (0, false))) a10Schedule).map
      (fun s => ((s.ps 1).fr.map Frame.pc, s.m.det (0, .crit), (s.ps 0).pc, (s.ps 0).fr.isSome,
        (pstep s 1).m.det (0, .crit))) =
      some (some (.f15 (0, .crit) 1 0), 0, .recv 0, false, 1) := by
  decide +kernel

theorem a10Schedule_X :
    (runSched (initSt (fun _ => 0) (fun _ => (0, false))) a10Schedule).map
      (fun s => s.m.X ((), .Z)) = some (some (0, .crit), 1) := by
  decide +kernel

/-- **Lemma A.10.2 is false as stated.** In a reachable state, the next step of process `1`
(line 15 of a `FORWARD` on `Z`, whose `X.hndl = h₀`) changes `h₀.DetVal` (`h₀ = (0, crit)`) from
`0` to `1`, while process `0` — the owner of `h₀` — has crashed and is at line 22 of `RECOVER`,
with no active DurEC call (so its `pc` is not in `{13, 14, 15}`). -/
theorem lemmaA10_2_counterexample :
    ∃ s : St (Fin 2) Unit ℕ, Reach (fun _ => 0) (fun _ => (0, false)) s ∧
      (s.ps 1).fr.map Frame.pc = some (.f15 (0, .crit) 1 0) ∧
      s.m.X ((), .Z) = (some (0, .crit), 1) ∧
      (s.ps 0).pc = .recv 0 ∧ (s.ps 0).fr = none ∧
      s.m.det (0, .crit) = 0 ∧ (pstep s 1).m.det (0, .crit) = 1 := by
  have h := a10Schedule_spec
  have hX := a10Schedule_X
  cases hr : runSched (initSt (fun _ => 0) (fun _ => (0, false))) a10Schedule with
  | none => rw [hr] at h; simp at h
  | some s =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [hr] at hX
    simp only [Option.map_some, Option.some.injEq] at hX
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    exact ⟨s, reach_of_runSched Relation.ReflTransGen.refl _ hr, h0, hX, h2,
      Option.not_isSome_iff_eq_none.1 (by simp [h3]), h1, h4⟩

end Example

end Podc.DuraCAS
