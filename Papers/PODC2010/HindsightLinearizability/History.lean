import Papers.PODC2010.HindsightLinearizability.Trace
import Podc.Computability.Distributed.SharedMemory.PastLinPoints

/-!
# Temporal traversal and the history invariant (Sections 6 and 7)

This file carries out the paper's argument for the linearization points as an invariant of the
finite executions `β` of the set algorithm (`hist_of_run`).

* **Temporal traversal (Lemma 6.3 + Lemma 5.4).** For a thread running `contains k`, at every
  moment of its traversal, the node `p` it is at (resp. the link `p.n ↦ c` it has just crossed)
  was a backbone node (resp. backbone link) at some state `j` after the invocation
  (`GhostC`). Each crossing extends this by the Hindsight Lemma `hindsight_node`.
* **Local window (Lemma 5.7).** When `contains k` leaves the loop with `p.k < k ≤ c.k`, the local
  window at the state `j` where `p.n ↦ c` was a backbone link shows `k ∈ Abs(τ j) ↔ c.k = k`,
  i.e. the returned value is the specified one at state `j` (`GhostC`, `done` case; `HistC`
  for completed operations).
* **Effectful operations.** `add`/`remove` take effect at their successful atomic section, where
  `Abs` moves as the specification prescribes, and later return the specified response
  (`GhostE`, `HistE`, `HistE2`, `HistInj`).
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory HeapState

variable {P : Type} [DecidableEq P]

local notation "Cfg" => Config setSpec (fun _ : Unit => heapObj) P Loc

/-! ### Thread steps without effect -/

/-- The possible local transitions of a step of thread `q` that is not a successful atomic
section. -/
lemma tau_cases {C C' : Cfg} (hC : Inv C) {q : P} (hs : (impl P).step C (.tau q) = some C')
    (hno : secOk (C.mem ()) (C.loc q) = none) :
    C'.mem () = C.mem () ∧ C'.pend = C.pend ∧ (∀ q', q' ≠ q → C'.loc q' = C.loc q') ∧
    ((∃ o, C.loc q = .start o ∧ C'.loc q = .cross o 1) ∨
     (∃ o pp c, C.loc q = .cross o pp ∧ (C.mem ()).next pp = some c ∧
        C'.loc q = .test o pp c) ∨
     (∃ o pp c, C.loc q = .test o pp c ∧ (C.mem ()).key c < fin o.key ∧
        C'.loc q = .cross o c) ∨
     (∃ k pp c, C.loc q = .test (.contains k) pp c ∧ ¬ (C.mem ()).key c < fin k ∧
        C'.loc q = .done (decide ((C.mem ()).key c = fin k))) ∨
     (∃ o pp c, C.loc q = .test o pp c ∧ (∀ k, o ≠ .contains k) ∧
        C'.loc q = .sec o pp c) ∨
     (∃ o pp c, C.loc q = .sec o pp c ∧ C'.loc q = .start o)) := by
  have hmem := step_not_secOk hC hs (fun p hp => by cases hp; exact hno)
  obtain ⟨h1, h2, op, k, hact, hmem', hloc⟩ := step_tau' hs
  refine ⟨hmem, h2, fun q' hq' => by rw [hloc, Function.update_of_ne hq'], ?_⟩
  obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 h1
  have hl := (hC.2 q).2 o' ho'
  have hm := hC.1
  rw [hloc, Function.update_self]
  cases hlq : C.loc q with
  | idle => rw [hlq] at hl; exact hl.elim
  | err => rw [hlq] at hl; exact hl.elim
  | done b => rw [hlq] at hact; simp [act] at hact
  | start o =>
    rw [hlq] at hact
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    exact Or.inl ⟨o, rfl, by simp [heapδ, hm.H_eq]⟩
  | cross o pp =>
    rw [hlq] at hact hl
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hp, hpk⟩ := hl
    obtain ⟨v, -, hv', -⟩ := hm.next_lt pp hp (hm.ne_zero_of_key_lt hpk)
    exact Or.inr (Or.inl ⟨_, pp, v, rfl, hv', by simp [heapδ, hv']⟩)
  | test o pp c =>
    rw [hlq] at hact hl
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    simp only [heapδ, afterKey]
    split_ifs with hck
    · exact Or.inr (Or.inr (Or.inl ⟨o, pp, c, rfl, hck, rfl⟩))
    · cases o with
      | contains k => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, pp, c, rfl, hck, rfl⟩)))
      | add k =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, pp, c, rfl, (fun _ h => by cases h),
          rfl⟩))))
      | remove k =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, pp, c, rfl, (fun _ h => by cases h),
          rfl⟩))))
  | sec o pp c =>
    rw [hlq] at hact hl hno
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hnc, -⟩ := hl
    simp only [secOk] at hno
    split_ifs at hno with hv
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, pp, c, rfl, ?_⟩))))
    cases o with
    | contains k => exact absurd rfl (hnc k)
    | add k => simp [secOp, heapδ, hv]
    | remove k => simp [secOp, heapδ, hv]

/-! ### The invariant -/

/-- Temporal traversal and local window for pending `contains` operations. -/
def GhostC (β : List (Label P setSpec)) (C : Cfg) : Prop :=
  ∀ p k, C.pend p = some (.contains k) →
    (∀ o pp, C.loc p = .cross o pp → ∃ j ≤ β.length, Invoked (β.take j) (curOp β p) ∧
      (memAt β j).hs.Backbone pp) ∧
    (∀ o pp c, C.loc p = .test o pp c → ∃ j ≤ β.length, Invoked (β.take j) (curOp β p) ∧
      (memAt β j).hs.BackboneLink pp c) ∧
    (∀ b, C.loc p = .done b → ∃ j ≤ β.length, Invoked (β.take j) (curOp β p) ∧
      (k ∈ Abs (memAt β j) ↔ b = true))

/-- A pending `add`/`remove` about to return has taken effect, with the specified response. -/
def GhostE (β : List (Label P setSpec)) (C : Cfg) : Prop :=
  ∀ p o b, C.pend p = some o → (∀ k, o ≠ .contains k) → C.loc p = .done b →
    ∃ n < β.length, effAt β n = some (curOp β p, o) ∧ (setSpec.δ (Abs (memAt β n)) o).2 = b

/-- Every completed `contains` has a state in its interval at which its response is the
specified one. -/
def HistC (β : List (Label P setSpec)) : Prop :=
  ∀ x k r, opOf β x = some (.contains k) → respOf β x = some r →
    ∃ j ≤ β.length, Invoked (β.take j) x ∧ ¬ Completed (β.take j) x ∧
      (k ∈ Abs (memAt β j) ↔ r = true)

/-- Effects get the specified responses; an effect of a pending operation is followed by its
return. -/
def HistE (β : List (Label P setSpec)) (C : Cfg) : Prop :=
  ∀ n < β.length, ∀ x o, effAt β n = some (x, o) →
    (∀ r, respOf β x = some r → r = (setSpec.δ (Abs (memAt β n)) o).2) ∧
    (¬ Completed β x → C.loc x.1 = .done (setSpec.δ (Abs (memAt β n)) o).2 ∧ x = curOp β x.1)

/-- Every completed `add`/`remove` has taken effect. -/
def HistE2 (β : List (Label P setSpec)) : Prop :=
  ∀ x o, opOf β x = some o → (∀ k, o ≠ .contains k) → Completed β x →
    ∃ n < β.length, effAt β n = some (x, o)

/-- Every operation takes effect at most once. -/
def HistInj (β : List (Label P setSpec)) : Prop :=
  ∀ n < β.length, ∀ n' < β.length, ∀ x o o', effAt β n = some (x, o) →
    effAt β n' = some (x, o') → n = n'

/-- The history invariant. -/
def Hist (β : List (Label P setSpec)) (C : Cfg) : Prop :=
  Inv C ∧ GhostC β C ∧ GhostE β C ∧ HistC β ∧ HistE β C ∧ HistE2 β ∧ HistInj β

lemma hist_nil : Hist ([] : List (Label P setSpec)) (impl P).initCfg := by
  refine ⟨inv_init, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p k h; simp [Impl.initCfg] at h
  · intro p o b h; simp [Impl.initCfg] at h
  · intro x k r h; simp [opOf] at h
  · intro n hn; simp at hn
  · intro x o h; simp [opOf] at h
  · intro n hn; simp at hn

/-! ### Preservation -/

lemma effAt_last {α : List (Label P setSpec)} {C : Cfg} (hrun : (impl P).run α = some C)
    (ℓ : Label P setSpec) :
    effAt (α ++ [ℓ]) α.length = match ℓ with
      | .tau p => (secOk (C.mem ()) (C.loc p)).map (fun o => (curOp α p, o))
      | _ => none := by
  have hc : cfgAt (α ++ [ℓ]) α.length = C := by rw [cfgAt_append _ le_rfl, cfgAt_length hrun]
  cases ℓ <;> simp [effAt, memAt, hc]

/-- One step of thread `q` that is not an effect and changes nothing else. -/
lemma ghostC_of_same {α : List (Label P setSpec)} {C C' : Cfg} {ℓ : Label P setSpec}
    (hGC : GhostC α C) {p : P} (hpend : C'.pend p = C.pend p) (hloc : C'.loc p = C.loc p)
    (hcur : curOp (α ++ [ℓ]) p = curOp α p) (k : ℤ) (hp : C'.pend p = some (.contains k)) :
    (∀ o pp, C'.loc p = .cross o pp → ∃ j ≤ (α ++ [ℓ]).length,
      Invoked ((α ++ [ℓ]).take j) (curOp (α ++ [ℓ]) p) ∧ (memAt (α ++ [ℓ]) j).hs.Backbone pp) ∧
    (∀ o pp c, C'.loc p = .test o pp c → ∃ j ≤ (α ++ [ℓ]).length,
      Invoked ((α ++ [ℓ]).take j) (curOp (α ++ [ℓ]) p) ∧
      (memAt (α ++ [ℓ]) j).hs.BackboneLink pp c) ∧
    (∀ b, C'.loc p = .done b → ∃ j ≤ (α ++ [ℓ]).length,
      Invoked ((α ++ [ℓ]).take j) (curOp (α ++ [ℓ]) p) ∧
      (k ∈ Abs (memAt (α ++ [ℓ]) j) ↔ b = true)) := by
  rw [hpend] at hp
  obtain ⟨h1, h2, h3⟩ := hGC p k hp
  rw [hloc, hcur]
  have hl : (α ++ [ℓ]).length = α.length + 1 := by simp
  refine ⟨fun o pp h => ?_, fun o pp c h => ?_, fun b h => ?_⟩
  · obtain ⟨j, hj, h4, h5⟩ := h1 o pp h
    exact ⟨j, by omega, by rw [List.take_append_of_le_length hj]; exact h4,
      by rw [memAt_append _ hj]; exact h5⟩
  · obtain ⟨j, hj, h4, h5⟩ := h2 o pp c h
    exact ⟨j, by omega, by rw [List.take_append_of_le_length hj]; exact h4,
      by rw [memAt_append _ hj]; exact h5⟩
  · obtain ⟨j, hj, h4, h5⟩ := h3 b h
    exact ⟨j, by omega, by rw [List.take_append_of_le_length hj]; exact h4,
      by rw [memAt_append _ hj]; exact h5⟩

lemma ghostE_of_same {α : List (Label P setSpec)} {C C' : Cfg} {ℓ : Label P setSpec}
    (hGE : GhostE α C) {p : P} (hpend : C'.pend p = C.pend p) (hloc : C'.loc p = C.loc p)
    (hcur : curOp (α ++ [ℓ]) p = curOp α p) (o : SetOp) (b : Bool) (hp : C'.pend p = some o)
    (hnc : ∀ k, o ≠ .contains k) (hd : C'.loc p = .done b) :
    ∃ n < (α ++ [ℓ]).length, effAt (α ++ [ℓ]) n = some (curOp (α ++ [ℓ]) p, o) ∧
      (setSpec.δ (Abs (memAt (α ++ [ℓ]) n)) o).2 = b := by
  rw [hpend] at hp; rw [hloc] at hd
  obtain ⟨n, hn, h1, h2⟩ := hGE p o b hp hnc hd
  refine ⟨n, by simp; omega, ?_, ?_⟩
  · rw [effAt_append _ hn, hcur]; exact h1
  · rw [memAt_append _ hn.le]; exact h2

lemma histC_of_not_ret {α : List (Label P setSpec)} (hval : (impl P).Valid α) (hHC : HistC α)
    {ℓ : Label P setSpec} (hℓ : ∀ p r, ℓ ≠ .ret p r) : HistC (α ++ [ℓ]) := by
  intro x k r hx hr
  rw [respOf_append_of_not_ret hℓ] at hr
  have hinv := (Impl.Valid.wellFormed _ hval).invoked_of_completed
    (Completed.of_respOf_eq_some hr)
  rw [opOf_append_of_invoked hinv] at hx
  obtain ⟨j, hj, h1, h2, h3⟩ := hHC x k r hx hr
  exact ⟨j, by simp; omega, by rw [List.take_append_of_le_length hj]; exact h1,
    by rw [List.take_append_of_le_length hj]; exact h2, by rw [memAt_append _ hj]; exact h3⟩

lemma histE2_of_not_ret {α : List (Label P setSpec)} (hval : (impl P).Valid α)
    (hHE2 : HistE2 α) {ℓ : Label P setSpec} (hℓ : ∀ p r, ℓ ≠ .ret p r) :
    HistE2 (α ++ [ℓ]) := by
  intro x o hx hnc hc
  rw [completed_append_of_not_ret hℓ] at hc
  have hinv := (Impl.Valid.wellFormed _ hval).invoked_of_completed hc
  rw [opOf_append_of_invoked hinv] at hx
  obtain ⟨n, hn, h⟩ := hHE2 x o hx hnc hc
  exact ⟨n, by simp; omega, by rw [effAt_append _ hn]; exact h⟩

lemma hist_step {α : List (Label P setSpec)} {C C' : Cfg} (hrun : (impl P).run α = some C)
    (hH : Hist α C) {ℓ : Label P setSpec} (hs : (impl P).step C ℓ = some C') :
    Hist (α ++ [ℓ]) C' := by
  obtain ⟨hI, hGC, hGE, hHC, hHE, hHE2, hInj⟩ := hH
  have hrun' : (impl P).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_concat, hrun]; exact hs
  have hval : (impl P).Valid α := ⟨C, hrun⟩
  have hI' : Inv C' := inv_step hI hs
  have hlen : (α ++ [ℓ]).length = α.length + 1 := by simp
  have hmemC : memAt α α.length = C.mem () := by unfold memAt; rw [cfgAt_length hrun]
  have hmemC' : memAt (α ++ [ℓ]) α.length = C.mem () := by
    rw [memAt_append _ le_rfl, hmemC]
  have hmemC'' : memAt (α ++ [ℓ]) (α.length + 1) = C'.mem () := by
    have := cfgAt_length hrun'; rw [hlen] at this; unfold memAt; rw [this]
  have hlast := effAt_last hrun ℓ
  -- effects at old indices are unchanged
  have hInjOld : ∀ (hlast' : effAt (α ++ [ℓ]) α.length = none), HistInj (α ++ [ℓ]) := by
    intro hl' n hn n' hn' x o o' h1 h2
    rw [hlen] at hn hn'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hn' with hn' | rfl
      · rw [effAt_append _ hn] at h1; rw [effAt_append _ hn'] at h2
        exact hInj n hn n' hn' x o o' h1 h2
      · rw [hl'] at h2; cases h2
    · rw [hl'] at h1; cases h1
  cases ℓ with
  | inv q o =>
    obtain ⟨hq0, -, hpend, hloc, -⟩ := Impl.step_inv hs
    have hl' : effAt (α ++ [.inv q o]) α.length = none := hlast
    refine ⟨hI', ?_, ?_, histC_of_not_ret hval hHC (fun _ _ h => by cases h), ?_,
      histE2_of_not_ret hval hHE2 (fun _ _ h => by cases h), hInjOld hl'⟩
    · intro p k hp
      by_cases hpq : p = q
      · subst hpq
        simp only [hloc, Function.update_self]
        exact ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ h => by cases h)⟩
      · exact ghostC_of_same hGC (by rw [hpend, Function.update_of_ne hpq])
          (by rw [hloc, Function.update_of_ne hpq]) (curOp_append_inv _ _ _ _) k hp
    · intro p o' b hp hnc hd
      by_cases hpq : p = q
      · subst hpq; simp [hloc, impl] at hd
      · exact ghostE_of_same hGE (by rw [hpend, Function.update_of_ne hpq])
          (by rw [hloc, Function.update_of_ne hpq]) (curOp_append_inv _ _ _ _) o' b hp hnc hd
    · intro n hn x o' h
      rw [hlen] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · rw [effAt_append _ hn] at h
        obtain ⟨h1, h2⟩ := hHE n hn x o' h
        refine ⟨fun r hr => ?_, fun hc => ?_⟩
        · rw [respOf_append_of_not_ret (fun _ _ h => by cases h)] at hr
          rw [memAt_append _ hn.le]; exact h1 r hr
        · rw [completed_append_of_not_ret (fun _ _ h => by cases h)] at hc
          obtain ⟨h3, h4⟩ := h2 hc
          have hxq : x.1 ≠ q := by
            rintro hxq
            have := (hI.2 x.1).1
            rw [hxq] at h3 this
            rw [this hq0] at h3; cases h3
          rw [hloc, Function.update_of_ne hxq, memAt_append _ hn.le, curOp_append_inv]
          exact ⟨h3, h4⟩
      · rw [hl'] at h; cases h
  | ret q r =>
    obtain ⟨hq0, hpend, -, l, hact, hloc⟩ := Impl.step_ret hs
    have hl' : effAt (α ++ [.ret q r]) α.length = none := hlast
    obtain ⟨o₀, ho₀⟩ := Option.ne_none_iff_exists'.1 hq0
    -- the returning thread was about to return `r`
    have hdone : C.loc q = .done r := by
      have hli := (hI.2 q).2 o₀ ho₀
      cases hlq : C.loc q <;> simp only [impl, act, hlq] at hact <;> rw [hlq] at hli <;>
        first | exact hli.elim | (cases hact; done) | (injection hact with h1 h2; rw [h1])
    set x₀ := curOp α q with hx₀
    obtain ⟨hinv₀, hnc₀, hop₀⟩ := (impl P).run_pend_curOp hrun ho₀
    have hresp : ∀ y, respOf (α ++ [.ret q r]) y = if y = x₀ then some r else respOf α y := by
      intro y; rw [respOf_append_ret]
    have hcur : ∀ p, p ≠ q → curOp (α ++ [.ret q r]) p = curOp α p :=
      fun p hp => curOp_append_ret_of_ne _ _ (Ne.symm hp)
    refine ⟨hI', ?_, ?_, ?_, ?_, ?_, hInjOld hl'⟩
    · intro p k hp
      by_cases hpq : p = q
      · subst hpq; simp [hpend] at hp
      · exact ghostC_of_same hGC (by rw [hpend, Function.update_of_ne hpq])
          (by rw [hloc, Function.update_of_ne hpq]) (hcur p hpq) k hp
    · intro p o' b hp hnc hd
      by_cases hpq : p = q
      · subst hpq; simp [hpend] at hp
      · exact ghostE_of_same hGE (by rw [hpend, Function.update_of_ne hpq])
          (by rw [hloc, Function.update_of_ne hpq]) (hcur p hpq) o' b hp hnc hd
    · intro x k r' hx hr
      have hval' : (impl P).Valid (α ++ [.ret q r]) := ⟨C', hrun'⟩
      by_cases hxx : x = x₀
      · subst hxx
        simp only [hresp, ↓reduceIte] at hr; cases hr
        rw [opOf_append_of_invoked hinv₀, hop₀] at hx; cases hx
        obtain ⟨-, -, h3⟩ := hGC q k ho₀
        obtain ⟨j, hj, h4, h5⟩ := h3 r hdone
        refine ⟨j, by simp; omega, ?_, ?_, ?_⟩
        · rw [List.take_append_of_le_length hj]; exact h4
        · rw [List.take_append_of_le_length hj]
          intro hc
          have := hc.mono (β := α.drop j)
          rw [List.take_append_drop] at this
          exact hnc₀ this
        · rw [memAt_append _ hj]; exact h5
      · simp only [hresp, hxx, ↓reduceIte] at hr
        have hinv := (Impl.Valid.wellFormed _ hval).invoked_of_completed
          (Completed.of_respOf_eq_some hr)
        rw [opOf_append_of_invoked hinv] at hx
        obtain ⟨j, hj, h1, h2, h3⟩ := hHC x k r' hx hr
        exact ⟨j, by simp; omega, by rw [List.take_append_of_le_length hj]; exact h1,
          by rw [List.take_append_of_le_length hj]; exact h2, by rw [memAt_append _ hj]; exact h3⟩
    · intro n hn x o' h
      rw [hlen] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · rw [effAt_append _ hn] at h
        obtain ⟨h1, h2⟩ := hHE n hn x o' h
        rw [memAt_append _ hn.le]
        by_cases hxx : x = x₀
        · subst hxx
          obtain ⟨h3, -⟩ := h2 hnc₀
          rw [hdone] at h3
          refine ⟨fun r' hr' => ?_, fun hc => absurd ((completed_append_ret _).2 (Or.inr rfl)) hc⟩
          simp only [hresp, ↓reduceIte] at hr'; cases hr'
          cases h3; rfl
        · refine ⟨fun r' hr' => h1 r' (by simp only [hresp, hxx, ↓reduceIte] at hr'; exact hr'), fun hc => ?_⟩
          have hc' : ¬ Completed α x := fun h' => hc h'.mono
          obtain ⟨h3, h4⟩ := h2 hc'
          have hxq : x.1 ≠ q := by
            intro hxq; apply hxx; rw [h4, hxq]
          rw [hloc, Function.update_of_ne hxq, hcur _ hxq]
          exact ⟨h3, h4⟩
      · rw [hl'] at h; cases h
    · intro x o' hx hnc hc
      rw [completed_append_ret] at hc
      have hval' : (impl P).Valid (α ++ [.ret q r]) := ⟨C', hrun'⟩
      rcases hc with hc | hc
      · have hinv := (Impl.Valid.wellFormed _ hval).invoked_of_completed hc
        rw [opOf_append_of_invoked hinv] at hx
        obtain ⟨n, hn, h⟩ := hHE2 x o' hx hnc hc
        exact ⟨n, by simp; omega, by rw [effAt_append _ hn]; exact h⟩
      · have hxx : x = x₀ := hc
        subst hxx
        rw [opOf_append_of_invoked hinv₀, hop₀] at hx; cases hx
        obtain ⟨n, hn, h1, -⟩ := hGE q o₀ r ho₀ hnc hdone
        exact ⟨n, by simp; omega, by rw [effAt_append _ hn]; exact h1⟩
  | tau q =>
    obtain ⟨hq0, hpend, op, kk, hact, -, hlocU⟩ := step_tau' hs
    have hother : ∀ p, p ≠ q → C'.loc p = C.loc p :=
      fun p hp => by rw [hlocU, Function.update_of_ne hp]
    have hcur : ∀ p, curOp (α ++ [.tau q]) p = curOp α p := fun p => curOp_append_tau _ _ _
    have hnr : ∀ (p : P) (r : Bool), (Label.tau q : Label P setSpec) ≠ .ret p r :=
      fun _ _ h => by cases h
    have hnd : ∀ b, C.loc q ≠ .done b := by
      intro b hb; rw [hb] at hact; simp [act] at hact
    obtain ⟨o₀, ho₀⟩ := Option.ne_none_iff_exists'.1 hq0
    have hli := (hI.2 q).2 o₀ ho₀
    have hHEold : ∀ n < α.length, ∀ x o, effAt α n = some (x, o) →
        (∀ r, respOf (α ++ [.tau q]) x = some r →
          r = (setSpec.δ (Abs (memAt (α ++ [.tau q]) n)) o).2) ∧
        (¬ Completed (α ++ [.tau q]) x →
          C'.loc x.1 = .done (setSpec.δ (Abs (memAt (α ++ [.tau q]) n)) o).2 ∧
          x = curOp (α ++ [.tau q]) x.1) := by
      intro n hn x o h
      obtain ⟨h1, h2⟩ := hHE n hn x o h
      rw [memAt_append _ hn.le]
      refine ⟨fun r hr => h1 r (by rwa [respOf_append_of_not_ret hnr] at hr), fun hc => ?_⟩
      rw [completed_append_of_not_ret hnr] at hc
      obtain ⟨h3, h4⟩ := h2 hc
      have hxq : x.1 ≠ q := fun hxq => hnd _ (hxq ▸ h3)
      rw [hother _ hxq, hcur]
      exact ⟨h3, h4⟩
    have hpendp : ∀ p, C'.pend p = C.pend p := fun p => by rw [hpend]
    rcases hsec : secOk (C.mem ()) (C.loc q) with _ | o
    · -- not an effect
      have hl' : effAt (α ++ [.tau q]) α.length = none := by rw [hlast]; simp [hsec]
      obtain ⟨-, -, -, hcases⟩ := tau_cases hI hs hsec
      refine ⟨hI', ?_, ?_, histC_of_not_ret hval hHC hnr, ?_, histE2_of_not_ret hval hHE2 hnr,
        hInjOld hl'⟩
      · intro p k hp
        by_cases hpq : p = q
        · subst hpq
          have hk0 : o₀ = .contains k := by rw [hpendp, ho₀] at hp; exact Option.some.inj hp
          subst hk0
          have hGq := hGC p k ho₀
          rcases hcases with ⟨o, hl, hl'⟩ | ⟨o, pp, c, hl, hnext, hl'⟩ | ⟨o, pp, c, hl, hk, hl'⟩ |
            ⟨k', pp, c, hl, hk, hl'⟩ | ⟨o, pp, c, hl, hnc, hl'⟩ | ⟨o, pp, c, hl, hl'⟩
          · rw [hl']
            refine ⟨fun o' pp' h => ?_, (fun _ _ _ h => by cases h), (fun _ h => by cases h)⟩
            cases h
            refine ⟨α.length + 1, by simp, ?_, ?_⟩
            · rw [List.take_of_length_le (by simp)]
              exact ((impl P).run_pend_curOp hrun' (by rw [hpendp]; exact ho₀)).1
            · rw [hmemC'']
              show Relation.ReflTransGen _ (C'.mem ()).H 1
              rw [hI'.1.H_eq]
          · rw [hl']
            refine ⟨(fun _ _ h => by cases h), fun o' pp' c' h => ?_, (fun _ h => by cases h)⟩
            cases h
            obtain ⟨j, hj, hinvj, hbb⟩ := hGq.1 o pp hl
            have hstep : ∀ h, j ≤ h → h < α.length →
                DeltaEN (trace α h) (trace α (h + 1)) ∧ DeltaBN (trace α h) (trace α (h + 1)) ∧
                NoReclaim (trace α h) (trace α (h + 1)) := by
              intro h _ hh
              obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := stepProps_trace hval hh
              exact ⟨h6, h7, h8⟩
            obtain ⟨j', hjj', hj'le, hbb', hlink'⟩ := hindsight_node (τ := trace α) hj hstep hbb
              ((memInv_memAt hval j).backbone_lt hbb)
              (by show (memAt α α.length).next pp = some c; rw [hmemC]; exact hnext)
            refine ⟨j', by simp; omega, ?_, ?_⟩
            · rw [List.take_append_of_le_length hj'le, hcur]
              exact hinvj.take_mono hjj'
            · rw [memAt_append _ hj'le]; exact ⟨hbb', hlink'⟩
          · rw [hl']
            refine ⟨fun o' pp' h => ?_, (fun _ _ _ h => by cases h), (fun _ h => by cases h)⟩
            cases h
            obtain ⟨j, hj, hinvj, hbl⟩ := hGq.2.1 o pp c hl
            refine ⟨j, by simp; omega, ?_, ?_⟩
            · rw [List.take_append_of_le_length hj, hcur]; exact hinvj
            · rw [memAt_append _ hj]; exact hbl.backbone_target
          · rw [hl']
            refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun b h => ?_⟩
            cases h
            rw [hl] at hli
            obtain ⟨hk'k, -, -, hpk, -⟩ := hli
            cases hk'k
            obtain ⟨j, hj, hinvj, hbl⟩ := hGq.2.1 _ pp c hl
            have hmj := memInv_memAt hval j
            have hppj := hmj.backbone_lt hbl.1
            have hcj := hmj.closed hppj hbl.2
            have e1 := (memAt_mono hval hj le_rfl hppj).2
            have e2 := (memAt_mono hval hj le_rfl hcj).2
            rw [hmemC] at e1 e2
            have hw := hmj.mem_Abs_iff_of_link hbl.1 hbl.2 (k := k)
              (by rw [← e1]; exact hpk) (by rw [← e2]; exact not_lt.1 hk)
            refine ⟨j, by simp; omega, ?_, ?_⟩
            · rw [List.take_append_of_le_length hj, hcur]; exact hinvj
            · rw [memAt_append _ hj, hw, e2]; simp
          · rw [hl] at hli
            exact absurd hli.1 (hnc k)
          · rw [hl']
            exact ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ h => by cases h)⟩
        · exact ghostC_of_same hGC (hpendp p) (hother p hpq) (hcur p) k hp
      · intro p o b hp hnc hd
        by_cases hpq : p = q
        · subst hpq
          rw [hpendp, ho₀] at hp
          cases hp
          rcases hcases with ⟨o, hl, hl'⟩ | ⟨o, pp, c, hl, hnext, hl'⟩ | ⟨o, pp, c, hl, hk, hl'⟩ |
            ⟨k', pp, c, hl, hk, hl'⟩ | ⟨o, pp, c, hl, hnc', hl'⟩ | ⟨o, pp, c, hl, hl'⟩ <;>
            rw [hl'] at hd <;> try cases hd
          rw [hl] at hli
          exact absurd hli.1.symm (hnc k')
        · exact ghostE_of_same hGE (hpendp p) (hother p hpq) (hcur p) o b hp hnc hd
      · intro n hn x o h
        rw [hlen] at hn
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
        · rw [effAt_append _ hn] at h; exact hHEold n hn x o h
        · rw [hl'] at h; cases h
    · -- the successful atomic section of `q`
      obtain ⟨hpo, hnc, hdone', habs⟩ := step_secOk hI hs hsec
      have hl' : effAt (α ++ [.tau q]) α.length = some (curOp α q, o) := by
        rw [hlast]; simp [hsec]
      have hsecl : ∃ o' pp c, C.loc q = .sec o' pp c := by
        cases hlq : C.loc q <;> rw [hlq] at hsec <;> simp [secOk] at hsec
        exact ⟨_, _, _, rfl⟩
      refine ⟨hI', ?_, ?_, histC_of_not_ret hval hHC hnr, ?_, histE2_of_not_ret hval hHE2 hnr,
        ?_⟩
      · intro p k hp
        by_cases hpq : p = q
        · subst hpq; rw [hpendp, hpo] at hp; cases hp; exact absurd rfl (hnc k)
        · exact ghostC_of_same hGC (hpendp p) (hother p hpq) (hcur p) k hp
      · intro p o' b hp hnc' hd
        by_cases hpq : p = q
        · subst hpq
          rw [hpendp, hpo] at hp; cases hp
          rw [hdone'] at hd; cases hd
          exact ⟨α.length, by simp, by rw [hcur]; exact hl', by rw [hmemC']⟩
        · exact ghostE_of_same hGE (hpendp p) (hother p hpq) (hcur p) o' b hp hnc' hd
      · intro n hn x o' h
        rw [hlen] at hn
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
        · rw [effAt_append _ hn] at h; exact hHEold n hn x o' h
        · rw [hl'] at h; cases h
          refine ⟨fun r hr => ?_, fun _ => ?_⟩
          · rw [respOf_append_of_not_ret hnr] at hr
            exact absurd (Completed.of_respOf_eq_some hr) (not_completed_curOp _ _)
          · rw [hmemC', hcur]; exact ⟨hdone', rfl⟩
      · intro n hn n' hn' x o₁ o₂ h1 h2
        rw [hlen] at hn hn'
        have key : ∀ m < α.length, ∀ o₃, effAt α m ≠ some (curOp α q, o₃) := by
          intro m hm o₃ hm'
          obtain ⟨-, h⟩ := hHE m hm _ o₃ hm'
          obtain ⟨h3, -⟩ := h (not_completed_curOp _ _)
          obtain ⟨o', pp, c, hlq⟩ := hsecl
          rw [hlq] at h3; cases h3
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hn' with hn' | rfl
        · rw [effAt_append _ hn] at h1; rw [effAt_append _ hn'] at h2
          exact hInj n hn n' hn' x o₁ o₂ h1 h2
        · rw [effAt_append _ hn] at h1; rw [hl'] at h2; cases h2
          exact absurd h1 (key n hn _)
        · rw [effAt_append _ hn'] at h2; rw [hl'] at h1; cases h1
          exact absurd h2 (key n' hn' _)
        · rfl

/-- The history invariant holds for every finite execution. -/
theorem hist_of_run {α : List (Label P setSpec)} {C : Cfg} (h : (impl P).run α = some C) :
    Hist α C :=
  (impl P).run_induction (Q := Hist) hist_nil (fun _ _ _ _ hr hH hs => hist_step hr hH hs) h

/-- **Lemma 6.3 + Lemma 5.4, for `contains`.** In every execution `β`, if thread `p` runs
`contains k` and has just crossed the link `pp.n ↦ c` (it is about to test `c.k < k`), then
`pp.n ↦ c` was a backbone link at some state `j` of the trace after the invocation. -/
theorem temporal_traversal {β : List (Label P setSpec)} {C : Cfg} (h : (impl P).run β = some C)
    {p : P} {k : ℤ} {o : SetOp} {pp c : ℕ} (hp : C.pend p = some (.contains k))
    (hl : C.loc p = .test o pp c) :
    ∃ j ≤ β.length, Invoked (β.take j) (curOp β p) ∧ (trace β j).BackboneLink pp c :=
  ((hist_of_run h).2.1 p k hp).2.1 o pp c hl

/-- **The `contains` case of Theorem 7.5 (via Lemma 5.7).** Every completed `contains k` with
response `r` has a state `j` between its invocation and its response with
`k ∈ Abs(τ j) ↔ r = true`. -/
theorem contains_hindsight {β : List (Label P setSpec)} {C : Cfg}
    (h : (impl P).run β = some C) {x : OpId P} {k : ℤ} {r : Bool}
    (hx : opOf β x = some (.contains k)) (hr : respOf β x = some r) :
    ∃ j ≤ β.length, Invoked (β.take j) x ∧ ¬ Completed (β.take j) x ∧
      (k ∈ Abs (memAt β j) ↔ r = true) :=
  (hist_of_run h).2.2.2.1 x k r hx hr

end Podc.HindsightLinearizability
