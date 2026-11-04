import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.MemInv

/-!
# Algorithm A is linearizable (Theorem 5)

Linearization points (replacing the paper's Definitions 8–9, see the notes below):

* a `ReadMax` is linearized at its read of the root (line 2), as in Definition 9;
* a `WriteMax(v)` is linearized at the **first moment during its execution interval at which the
  root holds a value `≥ v`**: at its invocation if the root already holds `≥ v`, otherwise at the
  (successful, non-trivial) CAS on the root that makes the root reach `≥ v`. Several `WriteMax`
  operations can be linearized at the same CAS (in any order; they are all `≤` the new root
  value, and one of them has exactly that value).

The invariant `LInv` says: the linearization `L` built so far linearizes the execution, the root
holds the abstract state `linState L`, and a pending `WriteMax(v)` is in `L` iff `v ≤` root. Three
facts from the memory invariant `MInv` make this work: the root is non-decreasing (Lemma 8); a
new root value is the operand of a pending `WriteMax` (`MInv.good`, replaces Lemma 10); and a
`WriteMax(v)` returns only when the root holds `≥ v` (`PInv` of `wDone`, replaces Lemma 11).

## Differences from the paper's proof

Definition 9 linearizes a `WriteMax` at the first event after which the root *counts* it
(Definition 8: a chain of *visible*, i.e. value-changing, events from a leaf write of the
operation to the root). A `WriteMax` can complete without ever being counted by the root —
e.g. when its CASes succeed trivially because a sibling subtree already propagated a larger value,
when its leaf write is trivial, or when it returns early at line 16 — so Definition 9 leaves such
operations without a linearization point, and Invariant 1 / Lemma 9 are false
(`AlgA/Counterexample.lean`). The linearization above repairs this.
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

open Cslib.SharedMemory

variable {N : ℕ} {lay : Layout N}

/-- The status of the current instance `x` of a process in local state `l` with respect to the
linearization `L`. -/
def LStat (C : Cfg N) (L : List (OpId (Fin N) × MaxOp)) (x : OpId (Fin N)) (l : Loc) : Prop :=
  (l = .rRoot → x ∉ L.map Prod.fst) ∧
  (∀ r, l = .rDone r → maxRegObj.respIn maxRegObj.init L x = some r) ∧
  (l = .wDone → x ∈ L.map Prod.fst) ∧
  (∀ v, l.wOp = some v → (x ∈ L.map Prod.fst ↔ v ≤ nv C 1))

/-- The linearization invariant. -/
structure LInv (α : List (Label (Fin N) maxRegObj)) (C : Cfg N)
    (L : List (OpId (Fin N) × MaxOp)) : Prop where
  lin : IsLinearization α L
  root : linState (A := maxRegObj) L = nv C 1
  st : ∀ p, LStat C L (curOp α p) (C.loc p)

/-! ### Sequences of `writeMax` -/

lemma runOps_writeMax_le {R' : ℕ} :
    ∀ (os : List MaxOp) (q : ℕ), q ≤ R' → (∀ o ∈ os, ∃ v ≤ R', o = .writeMax v) →
      maxRegObj.runOps q os ≤ R' ∧ q ≤ maxRegObj.runOps q os ∧
      ∀ v, MaxOp.writeMax v ∈ os → v ≤ maxRegObj.runOps q os
  | [], q, hq, _ => ⟨hq, le_rfl, by simp⟩
  | o :: os, q, hq, h => by
    obtain ⟨v, hv, rfl⟩ := h o (by simp)
    obtain ⟨h1, h2, h3⟩ := runOps_writeMax_le os (max q v) (max_le hq hv)
      (fun o ho => h o (by simp [ho]))
    refine ⟨h1, (le_max_left q v).trans h2, fun w hw => ?_⟩
    simp only [List.mem_cons, MaxOp.writeMax.injEq] at hw
    rcases hw with rfl | hw
    · exact (le_max_right q w).trans h2
    · exact h3 w hw

/-- A `writeMax` entry gets response `0`. -/
lemma respIn_eq_zero {K : Type} [DecidableEq K] {x : K} :
    ∀ (L : List (K × MaxOp)) (q : ℕ), x ∈ L.map Prod.fst →
      (∀ y ∈ L, y.1 = x → ∃ v, y.2 = .writeMax v) → maxRegObj.respIn q L x = some 0
  | [], _, hx, _ => by simp at hx
  | (y, o) :: L, q, hx, h => by
    by_cases hy : y = x
    · subst hy
      obtain ⟨v, hv⟩ := h (y, o) (by simp) rfl
      simp only at hv; subst hv
      rw [ObjSpec.respIn_cons_self]
    · rw [ObjSpec.respIn_cons_of_ne _ _ _ hy]
      refine respIn_eq_zero L _ ?_ (fun z hz => h z (by simp [hz]))
      have := Ne.symm hy; simpa [this] using hx

/-- The `WriteMax` operations to linearize when the root goes from `R` to `R'`. -/
def pushes (α : List (Label (Fin N) maxRegObj)) (C : Cfg N) (R R' : ℕ) :
    List (OpId (Fin N) × MaxOp) :=
  (List.finRange N).filterMap fun q => match (C.loc q).wOp with
    | some v => if R < v ∧ v ≤ R' then some (curOp α q, .writeMax v) else none
    | none => none

lemma mem_pushes {α : List (Label (Fin N) maxRegObj)} {C : Cfg N} {R R' : ℕ}
    {y : OpId (Fin N) × MaxOp} :
    y ∈ pushes α C R R' ↔ ∃ q v, (C.loc q).wOp = some v ∧ R < v ∧ v ≤ R' ∧
      y = (curOp α q, .writeMax v) := by
  simp only [pushes, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨q, hq⟩
    cases hw : (C.loc q).wOp with
    | none => simp [hw] at hq
    | some v =>
      simp only [hw] at hq
      split_ifs at hq with h
      cases hq; exact ⟨q, v, hw, h.1, h.2, rfl⟩
  · rintro ⟨q, v, hw, h1, h2, rfl⟩
    exact ⟨q, by simp [hw, h1, h2]⟩

lemma mem_pushes_fst {α : List (Label (Fin N) maxRegObj)} {C : Cfg N} {R R' : ℕ} {q : Fin N} :
    curOp α q ∈ (pushes α C R R').map Prod.fst ↔
      ∃ v, (C.loc q).wOp = some v ∧ R < v ∧ v ≤ R' := by
  simp only [List.mem_map, mem_pushes]
  constructor
  · rintro ⟨y, ⟨q', v, hw, h1, h2, rfl⟩, hy⟩
    simp only [curOp, Prod.mk.injEq] at hy
    obtain rfl := hy.1
    exact ⟨v, hw, h1, h2⟩
  · rintro ⟨v, hw, h1, h2⟩
    exact ⟨_, ⟨q, v, hw, h1, h2, rfl⟩, rfl⟩

lemma nodup_pushes (α : List (Label (Fin N) maxRegObj)) (C : Cfg N) (R R' : ℕ) :
    ((pushes α C R R').map Prod.fst).Nodup := by
  unfold pushes
  rw [List.map_filterMap]
  refine (List.nodup_finRange N).filterMap ?_
  intro a a' b ha ha'
  cases hw : (C.loc a).wOp <;> cases hw' : (C.loc a').wOp <;> simp_all
  obtain ⟨-, rfl⟩ := ha
  simp [curOp] at ha'
  exact ha'.2.1.symm

/-! ### Facts about single steps -/

section Facts

variable {C C' : Cfg N} {p : Fin N}

lemma PInv.pend_of_wOp (h : PInv lay C p) {v : ℕ} (hw : (C.loc p).wOp = some v) :
    C.pend p = some (.writeMax v) := by
  unfold PInv PCommon at h
  split at h <;> simp_all [Loc.wOp]

lemma PInv.of_wDone (h : PInv lay C p) (hl : C.loc p = .wDone) :
    ∃ v, C.pend p = some (.writeMax v) ∧ v ≤ nv C 1 := by
  unfold PInv at h; rw [hl] at h; exact h

lemma PInv.of_rRoot (h : PInv lay C p) (hl : C.loc p = .rRoot) :
    C.pend p = some .readMax := by
  unfold PInv at h; rw [hl] at h; exact h

/-- What an internal step does to the local state of the stepping process. -/
lemma tau_trans (h : (impl lay).step C (.tau p) = some C') :
    (∀ r, C'.loc p = .rDone r → C.loc p = .rRoot ∧ C' = upd C p 1 (nv C 1) (.rDone (nv C 1))) ∧
    C'.loc p ≠ .rRoot ∧
    (C'.loc p = .wDone → ∃ v, (C.loc p).wOp = some v) ∧
    (∀ v, (C'.loc p).wOp = some v → (C.loc p).wOp = some v) := by
  cases hl : C.loc p with
  | idle | rDone _ | wDone =>
    exfalso
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    simp [impl, hl] at hact
  | rRoot =>
    have hact : (impl lay).act p (C.loc p) = .access 1 .read (fun r => .rDone (val r)) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    refine ⟨fun r _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩ <;> simp [Loc.wOp]
  | wRead v =>
    have hact : (impl lay).act p (C.loc p) = .access (lay.leaf (.inr p)) .read
        (fun r => if v ≤ val r then .wDone else .wLeaf v (lay.leaf (.inr p))) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    by_cases hv : v ≤ C.mem (lay.leaf (.inr p)) <;> simp [hv, val, Loc.wOp]
  | wLeaf v x =>
    have hact : (impl lay).act p (C.loc p) = .access x (.write v) (fun _ => up v x) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    simp only [upd_loc_self, up]
    split_ifs <;> simp [Loc.wOp]
  | pOld v c j =>
    have hact : (impl lay).act p (C.loc p) =
        .access (c / 2) .read (fun r => .pL v c j (val r)) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    simp [Loc.wOp]
  | pL v c j old =>
    have hact : (impl lay).act p (C.loc p) =
        .access (2 * (c / 2)) .read (fun r => .pR v c j old (val r)) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    simp [Loc.wOp]
  | pR v c j old l =>
    have hact : (impl lay).act p (C.loc p) =
        .access (2 * (c / 2) + 1) .read (fun r => .pCas v c j old l (val r)) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    simp [Loc.wOp]
  | pCas v c j old l r =>
    have hact : (impl lay).act p (C.loc p) = .access (c / 2) (.cas old (max l r))
        (fun _ => if j then up v (c / 2) else .pOld v c true) := by
      rw [hl]; rfl
    obtain rfl := step_tau_upd h hact
    simp only [upd_loc_self, up]
    cases j <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> (try split_ifs) <;>
      simp [Loc.wOp]

lemma LStat.append {L M : List (OpId (Fin N) × MaxOp)} {x : OpId (Fin N)} {l : Loc}
    (h : LStat C L x l) (hx : x ∉ M.map Prod.fst) (hroot : nv C' 1 = nv C 1) :
    LStat C' (L ++ M) x l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun hl => ?_, fun r hl => ?_, fun hl => ?_, fun v hv => ?_⟩
  · simp only [List.map_append, List.mem_append, not_or]; exact ⟨h1 hl, hx⟩
  · have := h2 r hl
    rw [ObjSpec.respIn_append_of_mem (ObjSpec.mem_of_respIn_eq_some this)]; exact this
  · simp only [List.map_append, List.mem_append]; exact Or.inl (h3 hl)
  · simp only [List.map_append, List.mem_append, hroot]
    rw [← h4 v hv]; simp [hx]

lemma LStat.idle (L : List (OpId (Fin N) × MaxOp)) (x : OpId (Fin N)) :
    LStat C L x .idle := ⟨by simp, by simp, by simp, by simp [Loc.wOp]⟩

end Facts

/-! ### Preservation of the linearization invariant -/

theorem LInv.step {α : List (Label (Fin N) maxRegObj)} {C C' : Cfg N}
    {L : List (OpId (Fin N) × MaxOp)} {ℓ : Label (Fin N) maxRegObj}
    (hα : (impl lay).run α = some C) (hI : MInv lay C) (hL : LInv α C L)
    (h : (impl lay).step C ℓ = some C') : ∃ L', LInv (α ++ [ℓ]) C' L' := by
  obtain ⟨hI', hF⟩ := hI.step h
  have hα' : (impl lay).run (α ++ [ℓ]) = some C' := by
    rw [Impl.run_concat, hα]; exact h
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hidle := (hI.proc p).pend_none h0
    have hroot : nv C' 1 = nv C 1 := by simp [nv, hmem]
    have hx : curOp α p ∉ L.map Prod.fst := fun hm =>
      (impl lay).not_invoked_curOp_of_idle hα h0 (hL.lin.mem_invoked hm)
    have hp' : C'.pend p = some o := by rw [hpend]; simp
    obtain ⟨-, hnc, hop⟩ := (impl lay).run_pend_curOp hα' hp'
    simp only [curOp_append_inv] at hnc hop
    have hC'p : C'.loc p = (impl lay).invoke p .idle o := by
      rw [hloc, Function.update_self, hidle]
    have hother : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => (hF.other q hq).1
    by_cases hw : ∃ v, o = .writeMax v ∧ v ≤ nv C 1
    · obtain ⟨v, rfl, hv⟩ := hw
      refine ⟨L ++ [(curOp α p, .writeMax v)], ⟨(hL.lin.append_inv p _).push hop hx hnc, ?_,
        fun q => ?_⟩⟩
      · rw [linState_concat, hL.root, hroot]; simp [hv]
      · rw [curOp_append_inv]
        by_cases hq : q = p
        · subst hq
          rw [hC'p]
          refine ⟨by simp only [impl]; split_ifs <;> simp, by simp only [impl]; split_ifs <;> simp,
            by simp only [impl]; split_ifs <;> simp, fun w hw' => ?_⟩
          have : w = v := by simp [impl] at hw'; split_ifs at hw' <;> simp_all [Loc.wOp]
          subst this; simp [hroot, hv]
        · rw [hother q hq]
          exact (hL.st q).append (by simp [curOp, hq]) hroot
    · refine ⟨L, ⟨hL.lin.append_inv p o, by rw [hL.root, hroot], fun q => ?_⟩⟩
      rw [curOp_append_inv]
      by_cases hq : q = p
      · subst hq
        rw [hC'p]
        cases o with
        | readMax => exact ⟨fun _ => hx, by simp [impl], by simp [impl], by simp [impl, Loc.wOp]⟩
        | writeMax v =>
          have hv : ¬ v ≤ nv C 1 := fun hv => hw ⟨v, rfl, hv⟩
          refine ⟨by simp only [impl]; split_ifs <;> simp, by simp only [impl]; split_ifs <;> simp,
            by simp only [impl]; split_ifs <;> simp, fun w hw' => ?_⟩
          have : w = v := by simp [impl] at hw'; split_ifs at hw' <;> simp_all [Loc.wOp]
          subst this; simp [hroot, hv, hx]
      · rw [hother q hq]
        simpa using (hL.st q).append (M := []) (by simp) hroot
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    have hroot : nv C' 1 = nv C 1 := by simp [nv, hmem]
    have hr : maxRegObj.respIn maxRegObj.init L (curOp α p) = some r := by
      have hst := hL.st p
      cases hlp : C.loc p <;> simp [impl, hlp] at hact
      · have := hI.proc p; unfold PInv at this; rw [hlp] at this; exact absurd this h0
      · obtain ⟨rfl, -⟩ := hact; exact hst.2.1 _ hlp
      · obtain ⟨rfl, -⟩ := hact
        obtain ⟨v, hpv, -⟩ := (hI.proc p).of_wDone hlp
        obtain ⟨-, -, hop⟩ := (impl lay).run_pend_curOp hα hpv
        refine respIn_eq_zero L _ (hst.2.2.1 hlp) fun y hy hyx => ⟨v, ?_⟩
        have := hL.lin.op_eq y hy
        rw [hyx, hop] at this
        exact (Option.some.inj this).symm
    have hl : l = .idle := by
      cases hlp : C.loc p <;> simp [impl, hlp] at hact
      all_goals exact hact.2.symm
    refine ⟨L, ⟨hL.lin.append_ret_of_respIn hr, by rw [hL.root, hroot], fun q => ?_⟩⟩
    by_cases hq : q = p
    · subst hq; rw [hloc, Function.update_self, hl]; exact LStat.idle _ _
    · rw [curOp_append_ret_of_ne _ _ (Ne.symm hq), (hF.other q hq).1]
      simpa using (hL.st q).append (M := []) (by simp) hroot
  | tau p =>
    simp only [Label.proc] at hF
    obtain ⟨hrd, hnr, hwd, hwo⟩ := tau_trans h
    have hpp : C.pend p ≠ none := (Impl.step_tau h).1
    have hpend' : C'.pend = C.pend := (Impl.step_tau h).2.1
    have hother : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => (hF.other q hq).1
    -- the status of `p` when its operand is unchanged
    by_cases hroot : nv C' 1 = nv C 1
    · by_cases hrr : C.loc p = .rRoot
      · -- the linearization point of `ReadMax` (line 2)
        have hpr := (hI.proc p).of_rRoot hrr
        obtain ⟨-, hnc, hop⟩ := (impl lay).run_pend_curOp hα hpr
        have hx : curOp α p ∉ L.map Prod.fst := (hL.st p).1 hrr
        have hC' : C' = upd C p 1 (nv C 1) (.rDone (nv C 1)) := by
          have hact : (impl lay).act p (C.loc p) = .access 1 .read (fun r => .rDone (val r)) := by
            rw [hrr]; rfl
          exact step_tau_upd h hact
        refine ⟨L ++ [(curOp α p, .readMax)], ⟨(hL.lin.push hop hx hnc).append_tau p, ?_,
          fun q => ?_⟩⟩
        · rw [linState_concat, hL.root, hroot]
        · rw [curOp_append_tau]
          by_cases hq : q = p
          · subst hq
            rw [hC', upd_loc_self]
            refine ⟨by simp, fun r hr => ?_, by simp, by simp [Loc.wOp]⟩
            simp only [Loc.rDone.injEq] at hr; subst hr
            rw [ObjSpec.respIn_concat_self hx]
            exact congrArg some hL.root
          · rw [hother q hq]
            exact (hL.st q).append (by simp [curOp, hq]) hroot
      · refine ⟨L, ⟨hL.lin.append_tau p, by rw [hL.root, hroot], fun q => ?_⟩⟩
        rw [curOp_append_tau]
        by_cases hq : q = p
        · subst hq
          obtain ⟨h1, h2, h3, h4⟩ := hL.st q
          refine ⟨fun hl => absurd hl hnr, fun r hl => absurd (hrd r hl).1 hrr, fun hl => ?_,
            fun v hv => by rw [hroot]; exact h4 v (hwo v hv)⟩
          obtain ⟨v, hv⟩ := hwd hl
          obtain ⟨v', hpv', hle⟩ := hI'.proc q |>.of_wDone hl
          rw [hpend', (hI.proc q).pend_of_wOp hv] at hpv'
          cases hpv'
          exact (h4 v hv).2 (hroot ▸ hle)
        · rw [hother q hq]
          simpa using (hL.st q).append (M := []) (by simp) hroot
    · -- the root changes: a successful CAS on the root
      rcases hF.change 1 hroot with ⟨v, hv, -⟩ | ⟨v, c, j, old, l, r, hpc, hc1, hold, hnew⟩
      · exfalso
        have := ((hI.proc p).wLeaf hv).2.1 ▸ lay.two_le_leafOf p v
        omega
      set R := nv C 1 with hRdef
      set R' := nv C' 1 with hR'def
      have hRR : R < R' := lt_of_le_of_ne (hF.mono 1) (Ne.symm hroot)
      set M := pushes α C R R' with hM
      have hMmem : ∀ y ∈ M, ∃ q v, (C.loc q).wOp = some v ∧ R < v ∧ v ≤ R' ∧
          y = (curOp α q, .writeMax v) := fun y hy => mem_pushes.1 hy
      have hlin : IsLinearization α (L ++ M) := by
        refine hL.lin.push_list M (fun y hy => ?_) (nodup_pushes α C R R') (fun y hy => ?_)
        · obtain ⟨q, v, hw, -, -, rfl⟩ := hMmem y hy
          obtain ⟨-, hnc, hop⟩ := (impl lay).run_pend_curOp hα ((hI.proc q).pend_of_wOp hw)
          exact ⟨hop, hnc⟩
        · obtain ⟨q, v, hw, h1, -, rfl⟩ := hMmem y hy
          intro hm
          have := ((hL.st q).2.2.2 v hw).1 hm
          omega
      have hstate : linState (A := maxRegObj) (L ++ M) = R' := by
        rw [linState_append, hL.root]
        have hops : ∀ o ∈ M.map Prod.snd, ∃ v ≤ R', o = .writeMax v := by
          intro o ho
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ho
          obtain ⟨q, v, -, -, h2, rfl⟩ := hMmem y hy
          exact ⟨v, h2, rfl⟩
        obtain ⟨h1, -, h3⟩ := runOps_writeMax_le (M.map Prod.snd) R hRR.le hops
        refine le_antisymm h1 ?_
        -- the new root value is the operand of a pending `WriteMax`
        have hgood : Good C R' := by
          have := hI.proc p; unfold PInv at this; rw [hpc] at this
          obtain ⟨-, -, -, -, -, h5, h6, -⟩ := this
          rw [hnew]; exact good_max h5 h6
        rcases hgood with hg | ⟨q, hq⟩
        · omega
        · refine h3 R' (List.mem_map.2 ⟨(curOp α q, .writeMax R'), ?_, rfl⟩)
          exact mem_pushes.2 ⟨q, R', hq, hRR, le_rfl, rfl⟩
      refine ⟨L ++ M, ⟨hlin.append_tau p, hstate, fun q => ?_⟩⟩
      rw [curOp_append_tau]
      have hMfst : curOp α q ∈ M.map Prod.fst ↔ ∃ v, (C.loc q).wOp = some v ∧ R < v ∧ v ≤ R' :=
        mem_pushes_fst
      obtain ⟨h1, h2, h3, h4⟩ := hL.st q
      by_cases hq : q = p
      · subst hq
        refine ⟨fun hl => absurd hl hnr, fun r hl => by
          have := (hrd r hl).1; rw [this] at hpc; exact absurd hpc (by simp),
          fun hl => ?_, fun w hw => ?_⟩
        · obtain ⟨v', hpv', hle⟩ := hI'.proc q |>.of_wDone hl
          rw [hpend', (hI.proc q).pend_of_wOp (by rw [hpc]; rfl : (C.loc q).wOp = some v)] at hpv'
          cases hpv'
          simp only [List.map_append, List.mem_append, hMfst]
          by_cases hvR : v ≤ R
          · exact Or.inl ((h4 v (by rw [hpc]; rfl)).2 hvR)
          · exact Or.inr ⟨v, by rw [hpc]; rfl, by omega, hle⟩
        · have hw0 := hwo w hw
          simp only [List.map_append, List.mem_append, hMfst, h4 w hw0]
          constructor
          · rintro (h | ⟨w', hw', -, h⟩)
            · omega
            · rw [hw0] at hw'; cases hw'; exact h
          · intro h
            by_cases hwR : w ≤ R
            · exact Or.inl hwR
            · exact Or.inr ⟨w, hw0, by omega, h⟩
      · rw [hother q hq]
        refine ⟨fun hl => ?_, fun r hl => ?_, fun hl => ?_, fun w hw => ?_⟩
        · simp only [List.map_append, List.mem_append, hMfst, not_or]
          refine ⟨h1 hl, ?_⟩
          rintro ⟨w, hw, -⟩; rw [hl] at hw; cases hw
        · have := h2 r hl
          rw [ObjSpec.respIn_append_of_mem (ObjSpec.mem_of_respIn_eq_some this)]; exact this
        · simp only [List.map_append, List.mem_append]; exact Or.inl (h3 hl)
        · simp only [List.map_append, List.mem_append, hMfst, h4 w hw]
          constructor
          · rintro (h | ⟨w', hw', -, h⟩)
            · omega
            · rw [hw] at hw'; cases hw'; exact h
          · intro h
            by_cases hwR : w ≤ R
            · exact Or.inl hwR
            · exact Or.inr ⟨w, hw, by omega, h⟩

/-- **Theorem 5** of [Hendler–Khait, PODC'14]: Algorithm A is a linearizable implementation of
an `N`-process (unbounded) max register, for every leaf layout. -/
theorem linearizable (lay : Layout N) : (impl lay).Linearizable := by
  refine (impl lay).linearizable_of_run fun α C hα => ?_
  have : MInv lay C ∧ ∃ L, LInv α C L := by
    refine (impl lay).run_induction (Q := fun α C => MInv lay C ∧ ∃ L, LInv α C L) ?_ ?_ hα
    · refine ⟨mInv_init, [], isLinearization_nil, by simp [impl, Impl.initCfg, nv]; rfl,
        fun q => ?_⟩
      exact LStat.idle _ _
    · rintro α C ℓ C' hα ⟨hI, L, hL⟩ hs
      exact ⟨(hI.step hs).1, LInv.step hα hI hL hs⟩
  obtain ⟨-, L, hL⟩ := this
  exact ⟨L, hL.lin⟩

end Podc.ReadUpdateTradeoffs.AlgA
