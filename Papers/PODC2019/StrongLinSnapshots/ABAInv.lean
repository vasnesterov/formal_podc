import Papers.PODC2019.StrongLinSnapshots.ABADefs

/-!
# Algorithm 2: the simulation invariant

The linearization points are those of the paper (Q-1, Q-2): a `DWrite` at its write to `X`
(line 2), a `DRead` at its last read of `X` (line 37, the one that ends the loop). The invariant
relates a configuration to the abstract state `(x, F)` of the linearization (`F q` = "some
`DWrite` was linearized since `q`'s last linearized `DRead`").

* `RInv` (reader `q`): while `q` is *clean* (`CleanPC`: idle, writing, about to return, or in
  the first iteration of a `DRead` whose announcement `A[q]` is unchanged),
  `F q ↔ X.tag ≠ A[q]`; within the loop, the values read so far determine the outcome.
* `WInv` (writer `p`): if `X` carries a tag `(p, s')` then `s'` is the newest (or, after a new
  `GetSeq`, the second newest) entry of `usedQ`; a chosen but not yet written `s` is not among
  the older entries.
* `ProtBy` (Observation 6(b) of the paper, as an invariant): if a clean reader `q` announces
  `A[q] = (p, s')`, then `p` will not use `s'` before reading `A[q]` again: either `(q, s') ∈ na`
  or `s'` is in `usedQ` at a position that keeps it there until `p` reads `A[q]` again.
-/

namespace Podc.StrongLinSnapshots

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false

variable {n : ℕ} {V : Type}

/-- Whether a program counter is about to write `X`. -/
def PC.isWX : PC n V → Bool
  | .wX _ _ => true
  | _ => false

/-- The number of `GetSeq` calls, starting from index `c`, up to and including the one that
reads `A[q]`. -/
def dist (c q : Fin n) : ℕ := if c.val ≤ q.val then q.val - c.val + 1 else q.val + n - c.val + 1

lemma nextIdx_val (c : Fin n) : (nextIdx c).val = if c.val + 1 < n then c.val + 1 else 0 := by
  have := c.isLt
  unfold nextIdx
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : c.val + 1 = n := by omega
    simp [this]

lemma dist_le (c q : Fin n) : dist c q ≤ n := by
  have := c.isLt; have := q.isLt; unfold dist; split_ifs <;> omega

lemma one_le_dist (c q : Fin n) : 1 ≤ dist c q := by unfold dist; split_ifs <;> omega

lemma dist_next {c q : Fin n} (h : c ≠ q) : dist (nextIdx c) q + 1 = dist c q := by
  have h' : c.val ≠ q.val := fun e => h (Fin.ext e)
  have := c.isLt; have := q.isLt
  unfold dist; rw [nextIdx_val]
  split_ifs <;> omega

lemma two_le_dist {c q : Fin n} (h : c ≠ q) : 2 ≤ dist c q := by
  have := dist_next h; have := one_le_dist (nextIdx c) q; omega

/-- Clean program counters of a reader: its announcement `A[q]` is the one of its last
completed `DRead` (or initial), and the current `DRead` (if any) has not failed yet. -/
def CleanPC : PC n V → Prop
  | .r34 ch => ch = false
  | .r35 ch _ => ch = false
  | .r36 ch _ _ => ch = false
  | .r37 ch v a => ch = false ∧ a = v.2
  | _ => True

/-- The reader invariant of `q`, given its program counter, `X`, `A[q]` and the abstract flag
`F = F q`. -/
def RInv (pc : PC n V) (X : Val n V) (a : Tag n) (F : Bool) : Prop :=
  (CleanPC pc → (F = true ↔ X.2 ≠ a)) ∧
  match pc with
  | .r34 ch => ch = true → F = true
  | .r35 ch v => (ch = true → F = true) ∧ (F = false → X = v)
  | .r36 ch v a' => a' = a ∧ (ch = true → F = true) ∧ (F = false → X = v)
  | .r37 ch v a' => a = v.2 ∧ (ch = true → F = true) ∧ (F = false → X = v) ∧
      (a' ≠ v.2 → F = true)
  | _ => True

/-- The writer invariant of `p` (local state `l`, contents `X` of `X`). -/
def WInv (p : Fin n) (l : Loc n V) (X : Val n V) : Prop :=
  l.gs.usedQ.length ≤ n + 1 ∧
  (∀ x s, l.pc = .wX x s → l.gs.usedQ[0]? = some s ∧ s ∉ l.gs.usedQ.tail) ∧
  (∀ s', X.2 = some (p, s') → l.gs.usedQ[if l.pc.isWX then 1 else 0]? = some s')

/-- Writer `p` (local state `l`) will not reuse `s'` while reader `q` announces `(p, s')`. -/
def ProtBy (l : Loc n V) (q : Fin n) (s' : Seq n) : Prop :=
  (∀ x s, l.pc = .wX x s → s ≠ s') ∧
  (l.gs.na q = some s' ∨ ∃ j, l.gs.usedQ[j]? = some s' ∧ dist l.gs.c q + j ≤ n + 1)

variable [DecidableEq V] {v₀ : V} {pick : List (Seq n) → Seq n}

/-- Shorthand for the configurations of Algorithm 2. -/
abbrev Cfg (n : ℕ) (V : Type) (v₀ : V) :=
  Config (abaObj (Fin n) V v₀) (B n V v₀) (Fin n) (Loc n V)

/-- Shorthand for executions. -/
abbrev Exec (n : ℕ) (V : Type) (v₀ : V) := List (Label (Fin n) (abaObj (Fin n) V v₀))

/-- Shorthand for linearizations. -/
abbrev LinT (n : ℕ) (V : Type) (v₀ : V) := List (OpId (Fin n) × (abaObj (Fin n) V v₀).Op)

/-- The status of a process: pending and not linearized, or linearized with the response it is
about to return, or idle. -/
def St (α : Exec n V v₀) (C : Cfg n V v₀) (Lin : LinT n V v₀) (p : Fin n) : Prop :=
  match (C.loc p).pc with
  | .idle => C.pend p = none
  | .wA x | .wX x _ => C.pend p ≠ none ∧ curOp α p ∉ Lin.map Prod.fst ∧
      opOf α (curOp α p) = some (.dwrite x)
  | .r34 _ | .r35 _ _ | .r36 _ _ _ | .r37 _ _ _ => C.pend p ≠ none ∧
      curOp α p ∉ Lin.map Prod.fst ∧ opOf α (curOp α p) = some (.dread p)
  | .wRet x => C.pend p ≠ none ∧
      (abaObj (Fin n) V v₀).respIn (abaObj (Fin n) V v₀).init Lin (curOp α p) = some (x, true)
  | .rRet x ch => C.pend p ≠ none ∧
      (abaObj (Fin n) V v₀).respIn (abaObj (Fin n) V v₀).init Lin (curOp α p) = some (x, ch)

/-- The simulation invariant. -/
structure Inv (α : Exec n V v₀) (C : Cfg n V v₀) (Lin : LinT n V v₀) : Prop where
  lin : IsLinearization α Lin
  st : ∀ p, St α C Lin p
  val : (linState Lin).1 = (C.mem none).1
  rd : ∀ q, RInv (C.loc q).pc (C.mem none) (C.mem (some q)).2 ((linState Lin).2 q)
  wr : ∀ p, WInv p (C.loc p) (C.mem none)
  prot : ∀ q p s', CleanPC (C.loc q).pc → (C.mem (some q)).2 = some (p, s') →
    ProtBy (C.loc p) q s'

/-! ## Auxiliary lemmas -/

lemma St.transfer {α α' : Exec n V v₀} {C C' : Cfg n V v₀} {Lin M : LinT n V v₀} {q : Fin n}
    (h : St α C Lin q) (hloc : C'.loc q = C.loc q) (hpend : C'.pend q = C.pend q)
    (hcur : curOp α' q = curOp α q)
    (hop : ∀ o, opOf α (curOp α q) = some o → opOf α' (curOp α q) = some o)
    (hM : curOp α q ∉ M.map Prod.fst) : St α' C' (Lin ++ M) q := by
  unfold St at h ⊢
  rw [hloc, hpend, hcur]
  split at h <;>
  first
  | exact h
  | exact ⟨h.1, by simp only [List.map_append, List.mem_append, not_or]; exact ⟨h.2.1, hM⟩,
      hop _ h.2.2⟩
  | exact ⟨h.1, ObjSpec.respIn_append_of_eq_some h.2 _⟩

lemma length_excl_lt (na : Fin n → Option (Seq n)) (u : List (Seq n)) (hu : u.length ≤ n + 1) :
    (excl na u).length < 2 * n + 2 := by
  unfold excl
  rw [List.length_append]
  have := (List.length_filterMap_le na (List.finRange n)).trans (le_of_eq (List.length_finRange))
  omega

lemma mem_excl_of_na {na : Fin n → Option (Seq n)} {u : List (Seq n)} {q : Fin n} {s : Seq n}
    (h : na q = some s) : s ∈ excl na u := by
  unfold excl
  exact List.mem_append_left _ (List.mem_filterMap.2 ⟨q, List.mem_finRange q, h⟩)

lemma mem_excl_of_usedQ {na : Fin n → Option (Seq n)} {u : List (Seq n)} {s : Seq n}
    (h : s ∈ u) : s ∈ excl na u := by
  unfold excl
  exact List.mem_append_right _ h

/-- The sequence number chosen by `GetSeq` is not excluded. -/
lemma getSeq_fst_notMem (hpick : PickSpec pick) (p : Fin n) (g : GS n) (t : Tag n)
    (hu : g.usedQ.length ≤ n + 1) :
    (getSeq pick p g t).1 ∉ excl (naUpd p g.c g.na t) g.usedQ :=
  hpick _ (length_excl_lt _ _ hu)

lemma linState_dwrite (Lin : LinT n V v₀) (y : OpId (Fin n)) (x : V) :
    linState (Lin ++ [(y, ABAOp.dwrite x)]) = ((x, fun _ => true) : V × (Fin n → Bool)) := by
  rw [linState_concat]

lemma linState_dread (Lin : LinT n V v₀) (y : OpId (Fin n)) (q : Fin n) :
    linState (Lin ++ [(y, ABAOp.dread q)]) =
      (((linState Lin).1, Function.update (linState Lin).2 q false) : V × (Fin n → Bool)) := by
  rw [linState_concat]

/-! ## Local lemmas about the invariant components -/

lemma WInv.congr {p : Fin n} {l l' : Loc n V} {X : Val n V} (h : WInv p l X)
    (hg : l'.gs = l.gs) (h1 : l.pc.isWX = false) (h2 : l'.pc.isWX = false) : WInv p l' X := by
  obtain ⟨h0, -, h3⟩ := h
  refine ⟨hg ▸ h0, fun x s hs => by simp [hs, PC.isWX] at h2, fun s' hs' => ?_⟩
  have := h3 s' hs'
  rw [h1] at this; rw [h2, hg]; exact this

lemma ProtBy.congr {l l' : Loc n V} {q : Fin n} {s' : Seq n} (h : ProtBy l q s')
    (hg : l'.gs = l.gs) (h2 : l'.pc.isWX = false) : ProtBy l' q s' := by
  refine ⟨fun x s hs => by simp [hs, PC.isWX] at h2, ?_⟩
  rw [hg]; exact h.2

/-- A clean reader's announcement `(p, s')` is protected right after it is established, i.e.
when `X` carries the same tag (from the writer invariant). -/
lemma protBy_of_wInv {p q : Fin n} {l : Loc n V} {X : Val n V} {s' : Seq n} (h : WInv p l X)
    (hX : X.2 = some (p, s')) : ProtBy l q s' := by
  obtain ⟨-, h2, h3⟩ := h
  have hq := h3 s' hX
  refine ⟨fun x s hs => ?_, Or.inr ⟨if l.pc.isWX then 1 else 0, hq, ?_⟩⟩
  · obtain ⟨h0, hnot⟩ := h2 x s hs
    rw [hs] at hq; simp only [PC.isWX, ite_true] at hq
    intro hss; subst hss
    apply hnot
    cases hu : l.gs.usedQ with
    | nil => simp [hu] at hq
    | cons a t =>
      rw [hu] at hq
      exact List.mem_of_getElem? (by simpa using hq : t[0]? = some _)
  · have := dist_le l.gs.c q; split_ifs <;> omega

/-- `GetSeq` keeps the protection of an announcement `(p, s')` of a clean reader `q` (whose
announcement is read if `c = q`). -/
lemma protBy_getSeq (hpick : PickSpec pick) {p q : Fin n} {l : Loc n V} {s' : Seq n} {x : V}
    {t : Tag n} (h : ProtBy l q s') (hu : l.gs.usedQ.length ≤ n + 1)
    (ht : l.gs.c = q → t = some (p, s')) :
    ProtBy (⟨.wX x (getSeq pick p l.gs t).1, (getSeq pick p l.gs t).2⟩ : Loc n V) q s' := by
  set g := l.gs
  have hnotin := getSeq_fst_notMem hpick p g t hu
  -- `s'` is excluded
  have hex : s' ∈ excl (naUpd p g.c g.na t) g.usedQ ∧
      ((naUpd p g.c g.na t) q = some s' ∨ ∃ j, g.usedQ[j]? = some s' ∧ dist g.c q + j ≤ n + 1 ∧
        g.c ≠ q) := by
    by_cases hc : g.c = q
    · have hna : naUpd p g.c g.na t q = some s' := by
        rw [ht hc]; unfold naUpd; rw [← hc, Function.update_self]; simp
      exact ⟨mem_excl_of_na hna, Or.inl hna⟩
    · have hna : naUpd p g.c g.na t q = g.na q := by
        unfold naUpd; rw [Function.update_of_ne (Ne.symm hc)]
      rcases h.2 with h1 | ⟨j, hj, hd⟩
      · rw [← hna] at h1; exact ⟨mem_excl_of_na h1, Or.inl h1⟩
      · exact ⟨mem_excl_of_usedQ (List.mem_of_getElem? hj), Or.inr ⟨j, hj, hd, hc⟩⟩
  refine ⟨fun x' s hs => ?_, ?_⟩
  · simp only [PC.wX.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    intro he; exact hnotin (he ▸ hex.1)
  · rcases hex.2 with h1 | ⟨j, hj, hd, hc⟩
    · exact Or.inl h1
    · refine Or.inr ⟨j + 1, ?_, ?_⟩
      · have h2 := two_le_dist hc
        simp only [getSeq, List.getElem?_take]
        rw [ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
        simpa using hj
      · have := dist_next hc; simp only [getSeq]; omega

/-- The reader invariant after a `DWrite` is linearized (all flags set), given that the new
tag of `X` differs from a clean reader's announcement. -/
lemma RInv.of_true {pc : PC n V} {X X' : Val n V} {a : Tag n} {F : Bool} (h : RInv pc X a F)
    (hX : CleanPC pc → X'.2 ≠ a) : RInv pc X' a true := by
  refine ⟨fun hc => by simpa using hX hc, ?_⟩
  obtain ⟨-, h2⟩ := h
  cases pc <;> simp_all

lemma initInv : Inv (v₀ := v₀) [] (impl v₀ pick).initCfg [] := by
  refine ⟨isLinearization_nil, fun p => ?_, rfl, fun q => ?_, fun p => ?_, ?_⟩
  · simp [St, impl, implG, Impl.initCfg]
  · refine ⟨fun _ => ?_, ?_⟩
    · simp [impl, implG, Impl.initCfg, linState, ObjSpec.runOps]
    · simp [impl, implG, Impl.initCfg]
  · refine ⟨by simp [impl, implG, Impl.initCfg], fun x s h => ?_, fun s' h => ?_⟩
    · simp [impl, implG, Impl.initCfg] at h
    · simp [impl, implG, Impl.initCfg] at h
  · intro q p s' _ h
    simp [impl, implG, Impl.initCfg] at h

end Podc.StrongLinSnapshots
