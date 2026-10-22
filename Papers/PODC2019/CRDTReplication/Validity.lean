import Papers.PODC2019.CRDTReplication.Safety

/-!
# Generated states and Theorem 1 (Validity)

Every payload state occurring in a reachable configuration (acceptor payloads, states recorded by
proposers, states in messages) is *generated* from `s₀` by joins and by the updates invoked so far
(`Gen`). Hence (with a causal history `H`) its causal history consists of invoked updates
(`C_subset_of_gen`); with the ghost record of learned states this gives Theorem 1.
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- The update commands invoked in `h`. -/
def invUpd (h : List (Label P D.spec)) : Set D.U :=
  {u | ∃ y, opOf h y = some (CRDT.Cmd.upd u)}

/-- States generated from `s₀` by joins and by the commands in `U`. -/
inductive Gen (D : CRDT) (U : Set D.U) : D.S → Prop
  | init : Gen D U D.s₀
  | sup {s t} : Gen D U s → Gen D U t → Gen D U (s ⊔ t)
  | app {u s} : u ∈ U → Gen D U s → Gen D U (D.app u s)

lemma Gen.mono {U U' : Set D.U} (hU : U ⊆ U') {s : D.S} (h : Gen D U s) : Gen D U' s := by
  induction h with
  | init => exact .init
  | sup _ _ ih₁ ih₂ => exact .sup ih₁ ih₂
  | app hu _ ih => exact .app (hU hu) ih

/-- The causal history of a generated state consists of the generating commands. -/
lemma C_subset_of_gen (H : D.CausalHistory) {U : Set D.U} {s : D.S} (h : Gen D U s) :
    H.C s ⊆ U := by
  induction h with
  | init => rw [H.C_init]; exact Set.empty_subset _
  | sup _ _ ih₁ ih₂ => rw [H.C_sup]; exact Set.union_subset ih₁ ih₂
  | app hu _ ih => rw [H.C_app]; exact Set.insert_subset hu ih

/-- The state carried by a message. -/
def Msg.st : Msg P D → Option D.S
  | .merge _ s => some s
  | .merged _ => none
  | .prepare _ _ s => some s
  | .ack _ _ s => some s
  | .vote _ _ s => some s
  | .voted _ _ s => some s

/-- The states recorded by a proposer. -/
def Phase.sts : Phase P D → Set D.S
  | .prep _ _ acks => {σ | ∃ a n, acks a = some (n, σ)}
  | .vote _ _ _ s _ => {s}
  | _ => ∅

lemma lub_gen {U : Set D.U} {acks : P → Option (ℕ × D.S)}
    (h : ∀ a n σ, acks a = some (n, σ) → Gen D U σ) : Gen D U (lub acks) := by
  have hst : ∀ a, Gen D U (ackState acks a) := by
    intro a
    unfold ackState
    cases ha : acks a with
    | none => exact .init
    | some x => exact h a x.1 x.2 ha
  unfold lub
  suffices ∀ s : Finset P, Gen D U (Finset.fold _ D.s₀ (ackState acks) s) from this _
  intro s
  induction s using Finset.cons_induction with
  | empty => exact .init
  | cons a s ha ih => rw [Finset.fold_cons]; exact .sup (hst a) ih

/-- All states in the local state of `p` and in the messages sent are generated. -/
def AllGen (U : Set D.U) (C : Config P (Loc P D) (Msg P D)) : Prop :=
  (∀ a, Gen D U (C.loc a).s ∧ ∀ σ ∈ (C.loc a).phase.sts, Gen D U σ) ∧
  ∀ x ∈ C.sent, ∀ σ, x.2.2.st = some σ → Gen D U σ

lemma startAttempt_gen {U : Set D.U} {p : P} {l : Loc P D} {q : D.Q} {n : Option ℕ} {s : D.S}
    (hs : Gen D U s) :
    (∀ σ ∈ (startAttempt p l q n s).1.phase.sts, Gen D U σ) ∧
    ∀ x ∈ (startAttempt p l q n s).2, ∀ σ, x.2.st = some σ → Gen D U σ := by
  refine ⟨fun σ hσ => by simp [startAttempt, Phase.sts] at hσ, fun x hx σ hσ => ?_⟩
  obtain ⟨a, m⟩ := x
  simp only [startAttempt, mem_toAll] at hx
  subst hx
  simp only [Msg.st, Option.some.injEq] at hσ
  rw [← hσ]; exact hs

/-- Local transitions keep all states generated (by the commands invoked after the step). -/
lemma AllGen.trans {sent : Multiset (P × P × Msg P D)} {U : Set D.U} {p : P} {l₀ l : Loc P D}
    {out : Multiset (P × Msg P D)} {ℓ : Option (Label P D.spec)}
    (htr : Trans V QS sent p l₀ l out ℓ) (hl₀ : Gen D U l₀.s ∧ ∀ σ ∈ l₀.phase.sts, Gen D U σ)
    (hsent : ∀ x ∈ sent, ∀ σ, x.2.2.st = some σ → Gen D U σ)
    (hinv : ∀ u, ℓ = some (.inv p (CRDT.Cmd.upd u)) → u ∈ U) :
    (Gen D U l.s ∧ ∀ σ ∈ l.phase.sts, Gen D U σ) ∧ ∀ x ∈ out, ∀ σ, x.2.st = some σ → Gen D U σ := by
  obtain ⟨hs₀, hph₀⟩ := hl₀
  cases htr with
  | inv hst =>
    rename_i o
    unfold invokeStep at hst
    split at hst
    · rename_i hidle
      cases o with
      | upd u =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        have hg : Gen D U (D.app u l₀.s) := .app (hinv u rfl) hs₀
        refine ⟨⟨hg, fun σ hσ => by simp [Phase.sts] at hσ⟩, fun x hx σ hσ => ?_⟩
        obtain ⟨a, m⟩ := x
        rw [mem_toOthers] at hx; obtain ⟨-, rfl⟩ := hx
        simp only [Msg.st, Option.some.injEq] at hσ; rw [← hσ]; exact hg
      | qry q =>
        simp only [Option.some.injEq] at hst
        rw [← (Prod.mk.inj hst).1, ← (Prod.mk.inj hst).2]
        have hg := startAttempt_gen (U := U) (p := p) (q := q) (n := none)
          (l := { l₀ with nOps := l₀.nOps + 1 }) .init
        exact ⟨⟨hs₀, hg.1⟩, hg.2⟩
    · simp at hst
  | internal hst =>
    unfold internalStep at hst
    split at hst
    · split_ifs at hst
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      exact ⟨⟨hs₀, fun σ hσ => by simp [Phase.sts] at hσ⟩, by simp⟩
    · rename_i q i acks hph
      have hacks : ∀ a n σ, acks a = some (n, σ) → Gen D U σ :=
        fun a n σ ha => hph₀ σ (by rw [hph]; exact ⟨a, n, ha⟩)
      have hlub := lub_gen hacks
      split_ifs at hst
      · simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl, rfl⟩ := hst
        exact ⟨⟨hs₀, fun σ hσ => by simp [Phase.sts] at hσ⟩, by simp⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl, rfl⟩ := hst
        refine ⟨⟨hs₀, fun σ hσ => ?_⟩, fun x hx σ hσ => ?_⟩
        · simp only [Phase.sts, Set.mem_singleton_iff] at hσ; rw [hσ]; exact hlub
        · obtain ⟨a, m⟩ := x
          rw [mem_toAll] at hx; subst hx
          simp only [Msg.st, Option.some.injEq] at hσ; rw [← hσ]; exact hlub
      · simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl, rfl⟩ := hst
        exact ⟨⟨hs₀, (startAttempt_gen hlub).1⟩, (startAttempt_gen hlub).2⟩
    · split_ifs at hst
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      exact ⟨⟨hs₀, fun σ hσ => by simp [Phase.sts] at hσ⟩, by simp⟩
    · rename_i n q i acks hph
      have hlub := lub_gen (U := U) fun a n σ ha => hph₀ σ (by rw [hph]; exact ⟨a, n, ha⟩)
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      exact ⟨⟨hs₀, (startAttempt_gen hlub).1⟩, (startAttempt_gen hlub).2⟩
    · rename_i n q i n' s M hph
      have hs : Gen D U s := hph₀ s (by rw [hph]; rfl)
      simp only [Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl, rfl⟩ := hst
      exact ⟨⟨hs₀, (startAttempt_gen hs).1⟩, (startAttempt_gen hs).2⟩
    · simp at hst
  | recv hm =>
    rename_i src m
    have hmst : ∀ σ, m.st = some σ → Gen D U σ := fun σ hσ => hsent _ hm σ hσ
    cases m with
    | merge k s' =>
      have := hmst s' rfl
      refine ⟨⟨.sup hs₀ this, hph₀⟩, fun x hx σ hσ => ?_⟩
      simp only [receiveStep, Multiset.mem_singleton] at hx; subst hx; simp [Msg.st] at hσ
    | prepare i n s' =>
      have := hmst s' rfl
      simp only [receiveStep]
      split_ifs
      · refine ⟨⟨.sup hs₀ this, hph₀⟩, fun x hx σ hσ => ?_⟩
        rw [Multiset.mem_singleton] at hx; subst hx
        simp only [Msg.st, Option.some.injEq] at hσ; rw [← hσ]; exact .sup hs₀ this
      · exact ⟨⟨.sup hs₀ this, hph₀⟩, by simp⟩
    | vote n i s' =>
      have := hmst s' rfl
      simp only [receiveStep]
      split_ifs
      · refine ⟨⟨.sup hs₀ this, hph₀⟩, fun x hx σ hσ => ?_⟩
        rw [Multiset.mem_singleton] at hx; subst hx
        simp only [Msg.st, Option.some.injEq] at hσ; rw [← hσ]; exact this
      · exact ⟨⟨.sup hs₀ this, hph₀⟩, by simp⟩
    | merged k =>
      simp only [receiveStep]
      refine ⟨⟨?_, ?_⟩, by simp⟩ <;> split <;> (try split_ifs) <;>
        simp_all [Phase.sts]
    | ack n i s' =>
      have := hmst s' rfl
      simp only [receiveStep]
      refine ⟨⟨?_, ?_⟩, by simp⟩
      · split <;> (try split_ifs) <;> simp_all
      · split
        · rename_i q i' acks hph
          split_ifs
          · intro σ hσ
            simp only [Phase.sts, Set.mem_ofPred_eq] at hσ
            obtain ⟨a, n', ha⟩ := hσ
            by_cases has : a = src
            · subst has
              rw [Function.update_self, Option.some.injEq, Prod.mk.injEq] at ha
              rw [← ha.2]; exact this
            · rw [Function.update_of_ne has] at ha
              exact hph₀ σ (by rw [hph]; exact ⟨a, n', ha⟩)
          · exact hph₀
        · exact hph₀
    | voted n i s' =>
      simp only [receiveStep]
      refine ⟨⟨?_, ?_⟩, by simp⟩ <;> split <;> (try split_ifs) <;>
        simp_all [Phase.sts]

/-- **Generated states.** In a reachable configuration, every state is generated by the update
commands invoked so far. -/
theorem allGen_of_reach {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : AllGen (invUpd h) C := by
  induction hr with
  | init =>
    refine ⟨fun a => ⟨.init, fun σ hσ => ?_⟩, by simp [Protocol.initCfg]⟩
    simp [Protocol.initCfg, alg, initLoc, Phase.sts] at hσ
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    have hU : invUpd h₀ ⊆ invUpd (h₀ ++ ℓ.toList) := by
      rintro u ⟨y, hy⟩; exact ⟨y, opOf_append_of_eq_some hy _⟩
    obtain ⟨ihl, ihs⟩ := ih
    have ihl' : ∀ a, Gen D (invUpd (h₀ ++ ℓ.toList)) (C₀.loc a).s ∧
        ∀ σ ∈ (C₀.loc a).phase.sts, Gen D (invUpd (h₀ ++ ℓ.toList)) σ :=
      fun a => ⟨(ihl a).1.mono hU, fun σ hσ => ((ihl a).2 σ hσ).mono hU⟩
    have ihs' : ∀ x ∈ C₀.sent, ∀ σ, x.2.2.st = some σ → Gen D (invUpd (h₀ ++ ℓ.toList)) σ :=
      fun x hx σ hσ => (ihs x hx σ hσ).mono hU
    rcases reach_step_cases hr hs with ⟨hloc, hsent, rfl⟩ | ⟨p, l, out, htr, hloc, hsent⟩
    · simp only [Option.toList_none, List.append_nil] at ihl' ihs' ⊢
      exact ⟨fun a => by rw [hloc]; exact ihl' a, fun x hx => by rw [hsent] at hx; exact ihs' x hx⟩
    · have hinv : ∀ u, ℓ = some (.inv p (CRDT.Cmd.upd u)) → u ∈ invUpd (h₀ ++ ℓ.toList) := by
        rintro u rfl
        refine ⟨(p, (opsOf h₀ p).length), ?_⟩
        rw [Option.toList_some, opOf_concat_inv, ite_eq_left rfl]
      obtain ⟨hl, hout⟩ := AllGen.trans htr (ihl' p) ihs' hinv
      refine ⟨fun a => ?_, fun x hx σ hσ => ?_⟩
      · rw [hloc]
        by_cases hap : a = p
        · subst hap; rw [Function.update_self]; exact hl
        · rw [Function.update_of_ne hap]; exact ihl' a
      · rw [hsent] at hx
        rcases Multiset.mem_add.1 hx with hx | hx
        · exact ihs' x hx σ hσ
        · exact hout _ (mem_outMsgs.1 hx).2 σ hσ

end Podc.CRDTReplication
