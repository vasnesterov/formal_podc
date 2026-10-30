import Papers.PODC2026.ForgetIT.Protocol
import Papers.PODC2026.ForgetIT.Safety

/-!
# Every run of the timed algorithm is an execution of the asynchronous system

For every run `R` of `forgetIT prm K` (any adversary, any delivery times, no timing assumption)
and every time `τ` there is a reachable state of the system of `Spec.lean` in which the correct
processes have exactly their states at time `τ`, every message produced by a correct process up
to time `τ` is in `sent`, and every decision of a correct process up to time `τ` is a decision
event (`run_reach`). Consequently agreement holds in every run (`run_agreement`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ForgetIT

open Finset Cslib.Byzantine.PartialSync

variable {Val : Type} [DecidableEq Val] {n : ℕ}
variable {prm : Params (Fin n)} {F : Finset (Fin n)}

/-- A sequence of allowed rules executed by `p`, accumulating broadcasts. -/
inductive LExec (prm : Params (Fin n)) (p : Fin n) :
    LS (Fin n) Val × List (Msg Val) → LS (Fin n) Val × List (Msg Val) → Prop
  | refl (st) : LExec prm p st st
  | step {st st'} (a : Act (Fin n) Val) (h : Allowed prm p st.1 a)
      (h' : LExec prm p ((exec prm p a st.1).1, st.2 ++ (exec prm p a st.1).2) st') :
      LExec prm p st st'

namespace LExec

theorem trans {p : Fin n} {a b c : LS (Fin n) Val × List (Msg Val)} (h1 : LExec prm p a b)
    (h2 : LExec prm p b c) : LExec prm p a c := by
  induction h1 with
  | refl => exact h2
  | step a h _ ih => exact .step a h (ih h2)

theorem tryAct (p : Fin n) (st : LS (Fin n) Val × List (Msg Val)) (a : Act (Fin n) Val) :
    LExec prm p st (Podc.ForgetIT.tryAct prm p st a) := by
  unfold Podc.ForgetIT.tryAct
  split
  · exact .step a (by assumption) (.refl _)
  · exact .refl _

theorem foldl (p : Fin n) (cs : List (Act (Fin n) Val)) (st : LS (Fin n) Val × List (Msg Val)) :
    LExec prm p st (cs.foldl (Podc.ForgetIT.tryAct prm p) st) := by
  induction cs generalizing st with
  | nil => exact .refl _
  | cons a cs ih => exact (tryAct p st a).trans (ih _)

theorem iter (p : Fin n) (K : ℕ) (st : LS (Fin n) Val × List (Msg Val)) :
    LExec prm p st ((pass prm p)^[K] st) := by
  induction K generalizing st with
  | zero => exact .refl _
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    exact (foldl p _ st).trans (ih _)

end LExec

/-- Lifting a local execution of a correct process to the global system. -/
theorem lift {g : GS (Fin n) Val} {p : Fin n} (hp : p ∉ F) {st st' : LS (Fin n) Val × List (Msg Val)}
    (h : LExec prm p st st') (hloc : g.loc p = st.1) (S : Set (Fin n × Msg Val))
    (hS : g.sent = S ∪ {e | e.1 = p ∧ e.2 ∈ st.2}) :
    ∃ g', Relation.ReflTransGen (Step prm F) g g' ∧ g'.loc p = st'.1 ∧
      (∀ q, q ≠ p → g'.loc q = g.loc q) ∧ g'.sent = S ∪ {e | e.1 = p ∧ e.2 ∈ st'.2} ∧
      g.dec ⊆ g'.dec ∧
      ∀ V v, st'.1.decided = some (V, v) → st.1.decided = some (V, v) ∨ (p, V, v) ∈ g'.dec := by
  induction h generalizing g with
  | refl st => exact ⟨g, .refl, hloc, fun _ _ => rfl, hS, subset_rfl, fun V v h => Or.inl h⟩
  | @step st st' a hA _ ih =>
    have hen : En prm p a (g.loc p) := hloc ▸ hA.1
    obtain ⟨g', hr, h1, h2, h3, h4, h5⟩ := ih (g := g.act prm p a) (by rw [act_loc_self, hloc])
      (by
        ext e
        simp only [GS.act, hS, hloc, Set.mem_union, Set.mem_ofPred_eq, List.mem_append]
        tauto)
    refine ⟨g', .head (.act p a hp hen) hr, h1, fun q hq => by rw [h2 q hq, act_loc_ne hq], h3,
      fun e he => h4 (Or.inl he), fun V v hd => ?_⟩
    rcases h5 V v hd with h | h
    · rcases exec_decided prm p st.1 a with h' | ⟨w, rfl, h0, h'⟩
      · exact Or.inl (h' ▸ h)
      · right; rw [h'] at h; cases h
        exact h4 (Or.inr (by simp [decEv, hloc]))
    · exact Or.inr h

variable (prm) in
/-- Run states of `forgetIT`. -/
abbrev rst (K : ℕ) (R : Run (Fin n) (Msg Val) Val) (τ : ℕ) (p : Fin n) : LS (Fin n) Val :=
  R.st (forgetIT prm K) τ p

/-- The correspondence between a run at time `τ` and a global state. -/
structure Corr (K : ℕ) (R : Run (Fin n) (Msg Val) Val) (τ : ℕ) (g : GS (Fin n) Val) : Prop where
  loc : ∀ p ∉ R.faulty, g.loc p = rst prm K R τ p
  sent : ∀ p ∉ R.faulty, ∀ τ' ≤ τ, ∀ m ∈ (rst prm K R τ' p).out, (p, m) ∈ g.sent
  dec : ∀ p ∉ R.faulty, ∀ τ' ≤ τ, ∀ V v, (rst prm K R τ' p).decided = some (V, v) →
    (p, V, v) ∈ g.dec

/-- One tick of one correct process, lifted to the global system. -/
theorem tick {K : ℕ} {R : Run (Fin n) (Msg Val) Val} (τ : ℕ) {g : GS (Fin n) Val} {p : Fin n}
    (hp : p ∉ R.faulty) (hloc : g.loc p = rst prm K R τ p)
    (hsent : ∀ q ∉ R.faulty, ∀ τ' ≤ τ, ∀ m ∈ (rst prm K R τ' q).out, (q, m) ∈ g.sent) :
    ∃ g', Relation.ReflTransGen (Step prm R.faulty) g g' ∧ g'.loc p = rst prm K R (τ + 1) p ∧
      (∀ q, q ≠ p → g'.loc q = g.loc q) ∧ g.sent ⊆ g'.sent ∧
      (∀ m ∈ (rst prm K R (τ + 1) p).out, (p, m) ∈ g'.sent) ∧ g.dec ⊆ g'.dec ∧
      ∀ V v, (rst prm K R (τ + 1) p).decided = some (V, v) →
        (rst prm K R τ p).decided = some (V, v) ∨ (p, V, v) ∈ g'.dec := by
  set s := rst prm K R τ p with hs
  -- 1. delivery
  set s1 : LS (Fin n) Val := { s with rcv := s.rcv ++ inboxList (R.inbox (forgetIT prm K) p τ) }
  have hvol : Step prm R.faulty g (g.setLoc p { g.loc p with rcv := s1.rcv, acc := s1.acc }) := by
    refine .vol p hp _ _ (fun e he => ?_) (fun V q => Or.inr (by rw [hloc]))
    rw [hloc]
    simp only [s1, List.mem_append] at he
    rcases he with he | he
    · exact Or.inl he
    · right
      simp only [inboxList, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at he
      obtain ⟨q, m, hm, rfl⟩ := he
      by_cases hq : q ∈ R.faulty
      · exact Or.inl hq
      · right
        rw [Run.inbox_eq_flatMap] at hm
        simp only [List.mem_flatMap, List.mem_range, Run.dlv] at hm
        obtain ⟨τ', hτ', hm⟩ := hm
        split_ifs at hm with hdl
        · rw [Run.out_of_correct _ _ hq] at hm
          exact hsent q hq τ' (by omega) m hm
        · simp at hm
  set g1 := g.setLoc p { g.loc p with rcv := s1.rcv, acc := s1.acc }
  have hg1 : g1.loc p = s1 := by
    simp only [g1, GS.setLoc, Function.update_self, hloc]; rfl
  -- 2. the passes
  have hL := LExec.iter (prm := prm) p K (s1, [])
  obtain ⟨g2, hr2, h21, h22, h23, h24, h25⟩ := lift (F := R.faulty) hp hL hg1 g1.sent
    (by ext e; simp)
  -- 3. the clock
  set st := (pass prm p)^[K] (s1, [])
  have hstep : rst prm K R (τ + 1) p = { st.1 with clk := s.clk + 1, out := st.2 } := by
    simp only [rst, Run.st_succ]; rfl
  let s3 : LS (Fin n) Val :=
    { g2.loc p with clk := s.clk + 1, entered := st.1.entered, active := st.1.active, out := st.2 }
  refine ⟨g2.setLoc p s3, (Relation.ReflTransGen.head hvol hr2).tail (.aux p hp _ _ _ _),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [GS.setLoc, Function.update_self, hstep, s3, h21]
  · intro q hq
    simp only [GS.setLoc, Function.update_of_ne hq]
    rw [h22 q hq]; simp [g1, GS.setLoc, Function.update_of_ne hq]
  · intro e he; show e ∈ g2.sent; rw [h23]; exact Or.inl he
  · intro m hm; show (p, m) ∈ g2.sent; rw [h23, hstep] at *; exact Or.inr ⟨rfl, hm⟩
  · exact h24
  · intro V v hd
    rw [hstep] at hd
    rcases h25 V v hd with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- Process a list of distinct correct processes for one tick. -/
theorem tickList {K : ℕ} {R : Run (Fin n) (Msg Val) Val} (τ : ℕ) (L : List (Fin n))
    (hL : L.Nodup) (hLF : ∀ p ∈ L, p ∉ R.faulty) {g : GS (Fin n) Val}
    (hloc : ∀ p ∈ L, g.loc p = rst prm K R τ p)
    (hsent : ∀ q ∉ R.faulty, ∀ τ' ≤ τ, ∀ m ∈ (rst prm K R τ' q).out, (q, m) ∈ g.sent) :
    ∃ g', Relation.ReflTransGen (Step prm R.faulty) g g' ∧
      (∀ p ∈ L, g'.loc p = rst prm K R (τ + 1) p) ∧ (∀ q ∉ L, g'.loc q = g.loc q) ∧
      g.sent ⊆ g'.sent ∧ (∀ p ∈ L, ∀ m ∈ (rst prm K R (τ + 1) p).out, (p, m) ∈ g'.sent) ∧
      g.dec ⊆ g'.dec ∧ ∀ p ∈ L, ∀ V v, (rst prm K R (τ + 1) p).decided = some (V, v) →
        (rst prm K R τ p).decided = some (V, v) ∨ (p, V, v) ∈ g'.dec := by
  induction L generalizing g with
  | nil => exact ⟨g, .refl, by simp, fun _ _ => rfl, subset_rfl, by simp, subset_rfl, by simp⟩
  | cons p L ih =>
    have hp : p ∉ R.faulty := hLF p (by simp)
    obtain ⟨g1, hr1, h11, h12, h13, h14, h15, h16⟩ :=
      tick τ hp (hloc p (by simp)) hsent
    have hpL : p ∉ L := (List.nodup_cons.1 hL).1
    obtain ⟨g2, hr2, h21, h22, h23, h24, h25, h26⟩ := ih (List.nodup_cons.1 hL).2
      (fun q hq => hLF q (by simp [hq]))
      (fun q hq => by rw [h12 q (by rintro rfl; exact hpL hq)]; exact hloc q (by simp [hq]))
      (fun q hq τ' hτ' m hm => h13 (hsent q hq τ' hτ' m hm))
    refine ⟨g2, hr1.trans hr2, ?_, ?_, h13.trans h23, ?_, h15.trans h25, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [h22 q hpL, h11]
      · exact h21 q hq
    · intro q hq
      rw [h22 q (fun h => hq (by simp [h])), h12 q (fun h => hq (by simp [h]))]
    · intro q hq m hm
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h23 (h14 m hm)
      · exact h24 q hq m hm
    · intro q hq V v hd
      rcases List.mem_cons.1 hq with rfl | hq
      · rcases h16 V v hd with h | h
        · exact Or.inl h
        · exact Or.inr (h25 h)
      · exact h26 q hq V v hd

/-- **Refinement**: every run state of `forgetIT` corresponds to a reachable state of the
asynchronous system. -/
theorem run_reach (K : ℕ) (R : Run (Fin n) (Msg Val) Val) (τ : ℕ) :
    ∃ g, Reach prm R.faulty R.inp g ∧ Corr (prm := prm) K R τ g := by
  induction τ with
  | zero =>
    refine ⟨initGS prm R.faulty R.inp, .refl, ⟨fun p _ => ?_, fun p hp τ' hτ' m hm => ?_,
      fun p _ τ' hτ' V v h => ?_⟩⟩
    · simp [initGS, rst, forgetIT]
    · obtain rfl : τ' = 0 := by omega
      exact ⟨hp, by simpa [rst, forgetIT, initLS] using hm⟩
    · obtain rfl : τ' = 0 := by omega
      simp [rst, forgetIT, initLS, initR, startLS] at h
  | succ τ ih =>
    obtain ⟨g, hg, hc⟩ := ih
    set L := (List.finRange n).filter (· ∉ R.faulty)
    obtain ⟨g', hr, h1, -, h3, h4, h5, h6⟩ := tickList (K := K) (R := R) τ L
      ((List.nodup_finRange n).filter _) (fun p hp => by simpa [L] using hp)
      (fun p hp => hc.loc p (by simpa [L] using hp)) hc.sent
    have hmem : ∀ p ∉ R.faulty, p ∈ L := fun p hp => by simp [L, hp]
    refine ⟨g', hg.trans hr, ⟨fun p hp => h1 p (hmem p hp), fun p hp τ' hτ' m hm => ?_,
      fun p hp τ' hτ' V v h => ?_⟩⟩
    · rcases Nat.lt_or_ge τ' (τ + 1) with h | h
      · exact h3 (hc.sent p hp τ' (by omega) m hm)
      · obtain rfl : τ' = τ + 1 := by omega
        exact h4 p (hmem p hp) m hm
    · rcases Nat.lt_or_ge τ' (τ + 1) with h' | h'
      · exact h5 (hc.dec p hp τ' (by omega) V v h)
      · obtain rfl : τ' = τ + 1 := by omega
        rcases h6 p (hmem p hp) V v h with h | h
        · exact h5 (hc.dec p hp τ le_rfl V v h)
        · exact h

/-- **Agreement in every run** of `forgetIT` (Theorem 2, agreement): if two correct processes
have decided (at any times), they decided the same value. No timing assumption is needed. -/
theorem run_agreement (hn : n = 3 * prm.f + 1) (K : ℕ) (R : Run (Fin n) (Msg Val) Val)
    (hF : R.faulty.card ≤ prm.f) {p p' : Fin n} (hp : p ∉ R.faulty) (hp' : p' ∉ R.faulty)
    {τ τ' : ℕ} {v v' : Val} (hd : (forgetIT prm K).decide p (R.st (forgetIT prm K) τ p) = some v)
    (hd' : (forgetIT prm K).decide p' (R.st (forgetIT prm K) τ' p') = some v') : v = v' := by
  obtain ⟨g, hg, hc⟩ := run_reach (prm := prm) K R (max τ τ')
  simp only [forgetIT, Option.map_eq_some_iff] at hd hd'
  obtain ⟨⟨V, w⟩, h1, rfl⟩ := hd
  obtain ⟨⟨V', w'⟩, h2, rfl⟩ := hd'
  exact agreement (by simp [hn]) hF hg (hc.dec p hp τ (le_max_left _ _) V w h1)
    (hc.dec p' hp' τ' (le_max_right _ _) V' w' h2)

end Podc.ForgetIT
