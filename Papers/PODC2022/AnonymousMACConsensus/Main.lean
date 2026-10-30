import Papers.PODC2022.AnonymousMACConsensus.Regular
import Papers.PODC2022.AnonymousMACConsensus.Preservation

/-!
# Theorem 1 of Tseng–Zhang (PODC 2022): MAC-SC implements a regular store-collect object

Main result: `theorem_1`. Two concrete executions on two nodes complement it:

* `collect_sees_store` (non-vacuity): node `0` stores `7`, then node `1` collects and obtains
  `(7, 0)`;
* `theorem_1_needs_priority`: without assumption (iii) of the paper (the message handler has
  priority over the main thread), the same schedule in which node `1` reads its view while the
  message of node `0` is still queued violates Property I(i). So the assumption is necessary.
-/

namespace Podc.AnonymousMACConsensus

variable {ι V : Type*}

/-- **Theorem 1** of [Tseng–Zhang, PODC'22]: MAC-SC correctly implements the store-collect object,
i.e. every execution of Algorithm 1 in the abstract MAC layer (asynchronous, single hop, any number
of crashes, handler with priority) yields a history that satisfies regularity (Definition 1). -/
theorem theorem_1 [DecidableEq ι] : ImplementsStoreCollect ι V true :=
  fun _ _ hr => hr.inv.hinv.regular

/-! ## Two concrete executions -/

section Examples

lemma phase_update_self [DecidableEq ι] (v : ι → View ι V) (q : ι → List (View ι V)) (n : ι → ℕ)
    (f : ι → Phase ι V) (cr : Set ι) (i : ι) (x : Phase ι V) :
    (Config.mk v q n (Function.update f i x) cr).phase i = x := by simp

/-- The schedule shared by both examples: node `0` runs `Store₀(7)` to completion; then node `1`
runs `Collect₁`, processing the message of `0` before reading its view iff `handleFirst`. -/
lemma reach_example (prio : Bool) (handleFirst : Bool) (hprio : prio = true → handleFirst = true) :
    ∃ c W, Reach prio c
      [Label.inv (0 : Fin 2) 0 (Op.store (7 : ℕ)), Label.ret 0 0 .ack, Label.inv 1 0 .collect,
        Label.ret 1 0 (.view W)] ∧
      W 0 = if handleFirst then some (0, 7) else none := by
  have r1 := Reach.step (Reach.init (prio := prio) (ι := Fin 2) (V := ℕ))
    (Step.invoke _ 0 (.store 7) (by simp [Config.init]) (by simp [Config.init]))
  have r2 := Reach.step r1 (Step.exec _ 0 (.store 7) (by simp [Config.init])
    (phase_update_self _ _ _ _ _ _ _) (by simp [Config.init]))
  have r3 := Reach.step r2 (Step.deliver _ 0 0 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
  have r4 := Reach.step r3 (Step.deliver _ 0 1 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
  have r5 := Reach.step r4 (Step.ack _ 0 _ _ _ (by simp [Config.init]) (phase_update_self _ _ _ _ _ _ _)
    (by intro k _; fin_cases k <;> simp))
  have r6 := Reach.step r5 (Step.ret _ 0 _ _ (by simp [Config.init]) (phase_update_self _ _ _ _ _ _ _))
  have r7 := Reach.step r6 (Step.invoke _ 1 .collect (by simp [Config.init])
    (by simp [Config.init]))
  cases handleFirst with
  | true =>
    have r8 := Reach.step r7 (Step.handle _ 1 _ [] (by simp [Config.init])
      (by simp [Config.init]; rfl))
    have r9 := Reach.step r8 (Step.exec _ 1 .collect (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _) (by simp [Config.init]))
    have r10 := Reach.step r9 (Step.deliver _ 1 0 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
    have r11 := Reach.step r10 (Step.deliver _ 1 1 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
    have r12 := Reach.step r11 (Step.ack _ 1 _ _ _ (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _) (by intro k _; fin_cases k <;> simp))
    have r13 := Reach.step r12 (Step.ret _ 1 _ _ (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _))
    simp only [List.nil_append, Option.toList, List.cons_append, List.append_nil, resp,
      Config.init] at r13
    refine ⟨_, _, r13, ?_⟩
    simp [lineView, View.merge, View.single, newer, key, View.empty]
  | false =>
    have r9 := Reach.step r7 (Step.exec _ 1 .collect (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _) (by simp at hprio; simp [hprio]))
    have r10 := Reach.step r9 (Step.deliver _ 1 0 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
    have r11 := Reach.step r10 (Step.deliver _ 1 1 _ _ _ (phase_update_self _ _ _ _ _ _ _) (by simp))
    have r12 := Reach.step r11 (Step.ack _ 1 _ _ _ (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _) (by intro k _; fin_cases k <;> simp))
    have r13 := Reach.step r12 (Step.ret _ 1 _ _ (by simp [Config.init])
      (phase_update_self _ _ _ _ _ _ _))
    simp only [List.nil_append, Option.toList, List.cons_append, List.append_nil, resp,
      Config.init] at r13
    refine ⟨_, _, r13, ?_⟩
    simp [lineView, View.empty]

/-- Non-vacuity: with handler priority, after `Store₀(7)` completes, `Collect₁` returns a view
containing `(7, 0)` (the value `7` of node `0`'s operation number `0`). -/
theorem collect_sees_store :
    ∃ (c : Config (Fin 2) ℕ) (W : View (Fin 2) ℕ), Reach true c
      [Label.inv 0 0 (Op.store 7), Label.ret 0 0 .ack, Label.inv 1 0 .collect,
        Label.ret 1 0 (.view W)] ∧ W 0 = some (0, 7) := by
  obtain ⟨c, W, hr, hW⟩ := reach_example true true (fun _ => rfl)
  exact ⟨c, W, hr, by simpa using hW⟩

/-- Assumption (iii) of the paper (the handler has priority over the main thread) is necessary:
without it, MAC-SC violates Property I(i). Node `0` completes `Store₀(7)`; its message has been
delivered to node `1` but is still in `1`'s queue when `Collect₁` (invoked after the store
returned) reads `view₁ = ∅`. -/
theorem theorem_1_needs_priority : ¬ ImplementsStoreCollect (Fin 2) ℕ false := by
  intro hI
  obtain ⟨c, W, hr, hW⟩ := reach_example false false (fun h => absurd h (by decide))
  have hreg := ((hI c _ hr).1 1 0 W (by simp) 0).1
  simp only [Bool.false_eq_true, ite_false] at hW
  apply hreg hW 0 7 (by simp [IsStore])
  exact ⟨.ack, .collect, 1, 2, by norm_num, rfl, rfl⟩

end Examples

end Podc.AnonymousMACConsensus
