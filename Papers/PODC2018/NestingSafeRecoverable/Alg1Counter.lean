import Papers.PODC2018.NestingSafeRecoverable.Alg1
import Papers.PODC2018.NestingSafeRecoverable.Alg1Gen

/-!
# The initial value must not be written again

Lemma 2 needs that the written values also differ from the initial value `v₀` of the register.
Counterexample with two processes `p = false`, `q = true`, values `ℕ`, `v₀ = 0`:
`p` invokes `WRITE(1)`, writes `R ← 1` (line 4) and crashes; `q` reads `1`, writes `0` (= `v₀`)
and reads `0`; `p` recovers, reads `S_p = ⟨1, 0⟩` and `R = 0` (line 14), so it re-executes
`WRITE` and writes `1` again; `q` reads `1`. The single `WRITE(1)` would have to be linearized
both before `q`'s `WRITE(0)` and after it.
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL

/-- The schedule of the counterexample. -/
def badRun : List (Ev Bool (register ℕ 0)) :=
  [.inv false (.write 1), .step false, .step false, .step false, .crash false,
   .inv true .read, .step true, .step true,
   .inv true (.write 0), .step true, .step true, .step true, .step true, .step true,
   .inv true .read, .step true, .step true,
   .step false, .step false, .step false, .step false, .step false, .step false, .step false,
   .inv true .read, .step true, .step true]

lemma badRun_hist : N ((alg1 Bool ℕ 0).init.run badRun).hist =
    [.inv false (.write 1), .inv true .read, .ret true 1, .inv true (.write 0), .ret true 0,
     .inv true .read, .ret true 0, .inv true .read, .ret true 1] := by
  simp [badRun, Alg.Cfg.run, Alg.Cfg.ev, Alg.init, act1, wval]; rfl

/-- The history of `badRun`. -/
abbrev badHist : List (Label Bool (register ℕ 0)) :=
  [.inv false (.write 1), .inv true .read, .ret true 1, .inv true (.write 0), .ret true 0,
   .inv true .read, .ret true 0, .inv true .read, .ret true 1]

lemma opOf_badHist {x : OpId Bool} {v : ℕ} (h : opOf badHist x = some (.write v)) :
    (x = (false, 0) ∧ v = 1) ∨ (x = (true, 1) ∧ v = 0) := by
  obtain ⟨b, n⟩ := x
  have hf : opsOf badHist false = [.write 1] := rfl
  have ht : opsOf badHist true = [.read, .write 0, .read, .read] := rfl
  cases b <;> simp only [opOf, hf, ht] at h
  · rcases n with _ | n <;> simp_all
  · rcases n with _ | _ | _ | _ | n <;> simp_all

/-- `badHist` is not linearizable: the only `WRITE(1)` would have to precede `q`'s first read and
follow `q`'s `WRITE(0)`. -/
theorem badHist_not_lin : ¬ ∃ L, IsLinearization badHist L := by
  rintro ⟨L, hL⟩
  have h1 := hL.complete (true, 1) (by unfold Completed; decide)
  obtain ⟨⟨k, o⟩, hm, hk⟩ := List.mem_map.1 h1
  simp only at hk; subst hk
  have ho : o = .write 0 := by
    have h' : opOf badHist (true, 1) = some o := hL.op_eq _ hm
    have h'' : opOf badHist (true, 1) = some (.write 0) := rfl
    exact Option.some.inj (h'.symm.trans h'')
  subst ho
  obtain ⟨A₁, A₂, rfl⟩ := List.mem_iff_append.1 hm
  have hnd := hL.nodup
  simp only [List.map_append, List.map_cons] at hnd h1
  -- the first read of `q` returns `1`, so `WRITE(1)` is before `q`'s `WRITE(0)`
  have hpre01 : Precedes badHist (true, 0) (true, 1) :=
    ⟨[.inv false (.write 1), .inv true .read, .ret true 1], _, rfl, by unfold Completed; decide, by unfold Invoked; decide⟩
  have hs := hL.realtime _ _ hpre01 (by simp)
  simp only [List.map_append, List.map_cons] at hs
  have h0A : (true, 0) ∈ A₁.map Prod.fst := mem_left_of_sublist_pair hnd hs
  have hr0 := hL.respIn_eq (x := (true, 0)) (r := 1) rfl
  rw [ObjSpec.respIn_append_of_mem h0A] at hr0
  obtain ⟨y₁, hy₁, hy₁w⟩ := respIn_exists_write hr0 (by decide)
  -- the last read of `q` returns `1`, so `WRITE(1)` is after `q`'s `WRITE(0)`
  have hpre13 : Precedes badHist (true, 1) (true, 3) :=
    ⟨[.inv false (.write 1), .inv true .read, .ret true 1, .inv true (.write 0), .ret true 0], _,
      rfl, by unfold Completed; decide, by unfold Invoked; decide⟩
  have h3 := hL.complete (true, 3) (by unfold Completed; decide)
  have hs3 := hL.realtime _ _ hpre13 h3
  simp only [List.map_append, List.map_cons] at hs3
  have h3A : (true, 3) ∉ A₁.map Prod.fst := fun h =>
    not_sublist_pair_both hnd hs3
      (sublist_pair_iff.2 ⟨A₁.map Prod.fst, (true, 1) :: A₂.map Prod.fst, rfl, h, by simp⟩)
  have hr3 := hL.respIn_eq (x := (true, 3)) (r := 1) rfl
  rw [ObjSpec.respIn_append_of_not_mem h3A, ObjSpec.respIn_cons_of_ne _ _ _ (by decide)] at hr3
  obtain ⟨y₂, hy₂, hy₂w⟩ := respIn_exists_write hr3 (by simp)
  -- both are the unique `WRITE(1)` of `p`
  have e1 : y₁.1 = (false, 0) := by
    have := hL.op_eq y₁ (by simp [hy₁]); rw [hy₁w] at this
    rcases opOf_badHist this with h | h
    · exact h.1
    · exact absurd h.2 (by decide)
  have e2 : y₂.1 = (false, 0) := by
    have := hL.op_eq y₂ (by simp [hy₂]); rw [hy₂w] at this
    rcases opOf_badHist this with h | h
    · exact h.1
    · exact absurd h.2 (by decide)
  rw [List.nodup_append] at hnd
  exact hnd.2.2 _ (List.mem_map_of_mem hy₁) _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hy₂))
    (e1.trans e2.symm)

/-- Distinct written values do not suffice: if the initial value `v₀` may be written again,
Algorithm 1 is not NRL (`badRun` writes pairwise distinct values, one of them `v₀ = 0`). -/
theorem alg1_not_nrl_of_initial_rewritten :
    ¬ (alg1 Bool ℕ 0).NRL (fun h => ∀ x y v, opOf h x = some (.write v) →
      opOf h y = some (.write v) → x = y) := by
  intro hN
  have := (Alg.nrl_iff _).1 hN badRun (by
    rw [badRun_hist]
    intro x y v hx hy
    rcases opOf_badHist hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases opOf_badHist hy with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all)
  rw [badRun_hist] at this
  exact badHist_not_lin this

end Podc.NestingSafeRecoverable
