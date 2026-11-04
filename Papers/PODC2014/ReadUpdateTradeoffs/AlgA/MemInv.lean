import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.Defs

/-!
# Algorithm A: the memory invariant (Lemma 8 and the propagation guarantee)

The invariant `MInv` of the reachable configurations of Algorithm A. It contains

* **Lemma 8** (every node value is non-decreasing), via the state invariant "an internal node
  holds at most the maximum of its children" (`MInv.nodeMax`) and the per-process facts
  `old ≤ max(left, right)` (`PInv`); `Frame.mono` is the monotonicity of a step;
* the **double-refresh argument** behind Lemmas 9 and 11 (`Iter`, `Cond`): after a process has
  completed both refreshes of a node `n` whose child `c` on its path holds a value `≥ v`, the node
  holds a value `≥ v`. Hence a `WriteMax(v)` returns only when the root holds a value `≥ v`
  (`PInv` of `wDone`);
* the facts used for linearizability: every node value is `0`, at most the root, or the operand
  of a `WriteMax` in progress (`Good`, `MInv.good`).

`Cond C n c v` says: every process that is refreshing node `n` and whose `old` still equals the
current value of `n` will compute a new value `≥ v` (it has read, or will read, the child `c`
after `c` reached `v`). It is the state-based replacement of the paper's timing arguments
("`read_lc` of `p_k` occurs after ...").
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

open Cslib.SharedMemory

variable {N : ℕ}

/-- The value stored at node `n` (as a natural number). -/
def nv (C : Cfg N) (n : ℕ) : ℕ := C.mem n

/-! ### Views of local states -/

namespace Loc

/-- The operand of a `WriteMax` in progress (before returning). -/
def wOp : Loc → Option ℕ
  | .wRead v | .wLeaf v _ | .pOld v _ _ | .pL v _ _ _ | .pR v _ _ _ _ | .pCas v _ _ _ _ _ => some v
  | _ => none

/-- The operand of a `WriteMax` in its `Propagate` phase. -/
def propOp : Loc → Option ℕ
  | .pOld v _ _ | .pL v _ _ _ | .pR v _ _ _ _ | .pCas v _ _ _ _ _ => some v
  | _ => none

/-- The node being refreshed, once its old value has been read (lines 8–9). -/
def atNode : Loc → Option ℕ
  | .pL _ c _ _ | .pR _ c _ _ _ | .pCas _ c _ _ _ _ => some (c / 2)
  | _ => none

/-- The old value read in line 7. -/
def old : Loc → ℕ
  | .pL _ _ _ o | .pR _ _ _ o _ | .pCas _ _ _ o _ _ => o
  | _ => 0

/-- The value that the process will try to install (line 8) is `≥ v`, provided the child `c`
holds a value `≥ v`: it has not read `c` yet, or it read a value `≥ v` from it. -/
def NewGe (c v : ℕ) : Loc → Prop
  | .pR _ _ _ _ l => c = 2 * (c / 2) → v ≤ l
  | .pCas _ _ _ _ l r => v ≤ max l r
  | _ => True

end Loc

/-- Every process refreshing node `m` whose `old` equals the current value of `m` will install a
value `≥ v` (see the module docstring). -/
def Cond (C : Cfg N) (m c v : ℕ) : Prop :=
  ∀ q, (C.loc q).atNode = some m → (C.loc q).old = nv C m → (C.loc q).NewGe c v

/-- The state of the double refresh of node `m` (child `c`, operand `v`) by a process holding
`old`: in the first iteration, `m` still holds `old` or `Cond` holds; in the second iteration,
`m` already holds a value `≥ v`, or it still holds `old` and `Cond` holds. -/
def Iter (C : Cfg N) (m c v : ℕ) : Bool → ℕ → Prop
  | false, old => nv C m = old ∨ Cond C m c v
  | true, old => v ≤ nv C m ∨ (nv C m = old ∧ Cond C m c v)

/-- `x` is `≤` the root value or the operand of a `WriteMax` in progress. -/
def Good (C : Cfg N) (x : ℕ) : Prop := x ≤ nv C 1 ∨ ∃ q, (C.loc q).wOp = some x

/-- Facts common to all states of `Propagate` at child `c` of process `p` with operand `v`. -/
def PCommon (lay : Layout N) (C : Cfg N) (p : Fin N) (v c : ℕ) : Prop :=
  C.pend p = some (.writeMax v) ∧ 2 ≤ c ∧ (∃ k, lay.leafOf p v / 2 ^ k = c) ∧ v ≤ nv C c

/-- The per-process part of the invariant. -/
def PInv (lay : Layout N) (C : Cfg N) (p : Fin N) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .rRoot => C.pend p = some .readMax
  | .rDone _ => C.pend p = some .readMax
  | .wDone => ∃ v, C.pend p = some (.writeMax v) ∧ v ≤ nv C 1
  | .wRead v => C.pend p = some (.writeMax v) ∧ N ≤ v
  | .wLeaf v x => C.pend p = some (.writeMax v) ∧ x = lay.leafOf p v ∧ nv C x ≤ v
  | .pOld v c j => PCommon lay C p v c ∧ (j = true → v ≤ nv C (c / 2) ∨ Cond C (c / 2) c v)
  | .pL v c j old => PCommon lay C p v c ∧ old ≤ nv C (c / 2) ∧
      old ≤ max (nv C (2 * (c / 2))) (nv C (2 * (c / 2) + 1)) ∧ Iter C (c / 2) c v j old
  | .pR v c j old l => PCommon lay C p v c ∧ old ≤ nv C (c / 2) ∧
      old ≤ max l (nv C (2 * (c / 2) + 1)) ∧ l ≤ nv C (2 * (c / 2)) ∧ Good C l ∧
      (c = 2 * (c / 2) → v ≤ l) ∧ Iter C (c / 2) c v j old
  | .pCas v c j old l r => PCommon lay C p v c ∧ old ≤ nv C (c / 2) ∧ old ≤ max l r ∧
      l ≤ nv C (2 * (c / 2)) ∧ r ≤ nv C (2 * (c / 2) + 1) ∧ Good C l ∧ Good C r ∧
      v ≤ max l r ∧ Iter C (c / 2) c v j old

/-- The memory invariant of Algorithm A. -/
structure MInv (lay : Layout N) (C : Cfg N) : Prop where
  proc : ∀ p, PInv lay C p
  /-- An internal node holds at most the maximum of its children. -/
  nodeMax : ∀ n, n ∉ Set.range lay.leaf → nv C n ≤ max (nv C (2 * n)) (nv C (2 * n + 1))
  good : ∀ n, Good C (nv C n)
  /-- The leaf of `T_L` for `v` holds `0` or `v`. -/
  tl : ∀ v : Fin N, nv C (lay.leaf (.inl v)) ≤ v
  /-- The own leaf of `T_R` is propagated, or being propagated. -/
  tr : ∀ p, nv C (lay.leaf (.inr p)) ≤ nv C 1 ∨
    (C.loc p).propOp = some (nv C (lay.leaf (.inr p)))

/-- What a step of `p` from `C` to `C'` may do (used to transfer the invariant of the other
processes). -/
structure Frame (lay : Layout N) (C C' : Cfg N) (p : Fin N) : Prop where
  other : ∀ q, q ≠ p → C'.loc q = C.loc q ∧ C'.pend q = C.pend q
  mono : ∀ n, nv C n ≤ nv C' n
  change : ∀ n, nv C' n ≠ nv C n →
    (∃ v, C.loc p = .wLeaf v n ∧ nv C' n = v) ∨
    (∃ v c j old l r, C.loc p = .pCas v c j old l r ∧ c / 2 = n ∧ nv C n = old ∧
      nv C' n = max l r)
  frozen : (C'.loc p).atNode ≠ none → ∀ n, nv C' n = nv C n
  exit : ∀ x, (C.loc p).wOp = some x → (C'.loc p).wOp = some x ∨ x ≤ nv C' 1
  propExit : ∀ x, (C.loc p).propOp = some x → (C'.loc p).propOp = some x ∨ x ≤ nv C' 1
  wleaf : ∀ v x, C.loc p = .wLeaf v x → (C'.loc p).propOp = some v
  newGe : ∀ m c v, c / 2 = m → v ≤ nv C c → Cond C m c v → (C'.loc p).atNode = some m →
    (C'.loc p).old = nv C' m → (C'.loc p).NewGe c v

variable {lay : Layout N}

/-! ### Layout facts -/

lemma Layout.leafOf_mem (lay : Layout N) (p : Fin N) (v : ℕ) :
    lay.leafOf p v ∈ Set.range lay.leaf := by
  unfold Layout.leafOf; split <;> exact ⟨_, rfl⟩

lemma Layout.two_le_leafOf (lay : Layout N) (p : Fin N) (v : ℕ) : 2 ≤ lay.leafOf p v := by
  obtain ⟨a, ha⟩ := lay.leafOf_mem p v; rw [← ha]; exact lay.two_le a

/-- The parent of a node on the path of a leaf is not a leaf. -/
lemma Layout.half_not_leaf (lay : Layout N) {p : Fin N} {v k c : ℕ}
    (h : lay.leafOf p v / 2 ^ k = c) : c / 2 ∉ Set.range lay.leaf := by
  rintro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := lay.leafOf_mem p v
  rw [← ha] at h
  refine lay.not_anc a b (k + 1) (by omega) ?_
  rw [hb, ← h, Nat.div_div_eq_div_mul, pow_succ]

lemma Layout.leafOf_inj (lay : Layout N) {p q : Fin N} {v w : ℕ}
    (h : lay.leafOf p v = lay.leafOf q w) : (v < N ∧ v = w) ∨ (N ≤ v ∧ N ≤ w ∧ p = q) := by
  unfold Layout.leafOf at h
  split_ifs at h with h1 h2 h2
  · have := lay.inj h; simp at this; exact Or.inl ⟨h1, this⟩
  · exact absurd (lay.inj h) (by simp)
  · exact absurd (lay.inj h) (by simp)
  · have := lay.inj h; simp at this; exact Or.inr ⟨by omega, by omega, this⟩

lemma Layout.leafOf_of_lt (lay : Layout N) (p : Fin N) {v : ℕ} (h : v < N) :
    lay.leafOf p v = lay.leaf (.inl ⟨v, h⟩) := by simp [Layout.leafOf, h]

lemma Layout.leafOf_of_le (lay : Layout N) (p : Fin N) {v : ℕ} (h : N ≤ v) :
    lay.leafOf p v = lay.leaf (.inr p) := by simp [Layout.leafOf, not_lt.2 h]

/-! ### Elementary consequences of the invariant -/

lemma Good.of_le {C : Cfg N} {x : ℕ} (h : x ≤ nv C 1) : Good C x := Or.inl h

lemma good_max {C : Cfg N} {l r : ℕ} (hl : Good C l) (hr : Good C r) : Good C (max l r) := by
  rcases le_total l r with h | h
  · rw [max_eq_right h]; exact hr
  · rw [max_eq_left h]; exact hl

lemma PInv.old_le {C : Cfg N} {p : Fin N} (h : PInv lay C p) {m : ℕ}
    (hm : (C.loc p).atNode = some m) : (C.loc p).old ≤ nv C m := by
  unfold PInv at h
  split at h <;> simp_all [Loc.atNode, Loc.old]

lemma PInv.pend_none {C : Cfg N} {p : Fin N} (h : PInv lay C p) (hp : C.pend p = none) :
    C.loc p = .idle := by
  unfold PInv PCommon at h
  split at h <;> simp_all

lemma PInv.wLeaf {C : Cfg N} {p : Fin N} (h : PInv lay C p) {v x : ℕ}
    (hl : C.loc p = .wLeaf v x) :
    C.pend p = some (.writeMax v) ∧ x = lay.leafOf p v ∧ nv C x ≤ v := by
  unfold PInv at h; rw [hl] at h; exact h

lemma PInv.wLeaf_mem {C : Cfg N} {p : Fin N} (h : PInv lay C p) {v x : ℕ}
    (hl : C.loc p = .wLeaf v x) : x ∈ Set.range lay.leaf := by
  rw [(h.wLeaf hl).2.1]; exact lay.leafOf_mem p v

section Frame

variable {C C' : Cfg N} {p : Fin N}

lemma Frame.good (hF : Frame lay C C' p) {x : ℕ} (h : Good C x) : Good C' x := by
  rcases h with h | ⟨q, hq⟩
  · exact Or.inl (h.trans (hF.mono 1))
  · by_cases hqp : q = p
    · subst hqp
      rcases hF.exit x hq with h | h
      · exact Or.inr ⟨q, h⟩
      · exact Or.inl h
    · exact Or.inr ⟨q, by rw [(hF.other q hqp).1]; exact hq⟩

lemma Frame.cond_of_ne (hI : MInv lay C) (hF : Frame lay C C' p) {m c v : ℕ}
    (hm : nv C' m ≠ nv C m) : Cond C' m c v := by
  intro q hq hold
  by_cases hqp : q = p
  · subst hqp
    exact absurd (hF.frozen (by rw [hq]; simp) m) hm
  · rw [(hF.other q hqp).1] at hq hold
    have h1 := (hI.proc q).old_le hq
    have h2 : nv C m < nv C' m := lt_of_le_of_ne (hF.mono m) (Ne.symm hm)
    rw [← hold] at h2
    exact absurd h1 (not_le.2 h2)

lemma Frame.cond (hI : MInv lay C) (hF : Frame lay C C' p) {m c v : ℕ} (hcm : c / 2 = m)
    (hv : v ≤ nv C c) (h : Cond C m c v) : Cond C' m c v := by
  by_cases hm : nv C' m = nv C m
  · intro q hq hold
    by_cases hqp : q = p
    · subst hqp; exact hF.newGe m c v hcm hv h hq hold
    · rw [(hF.other q hqp).1] at hq hold ⊢
      exact h q hq (hold.trans hm)
  · exact hF.cond_of_ne hI hm

lemma Frame.iter (hI : MInv lay C) (hF : Frame lay C C' p) {m c v k : ℕ} {q : Fin N}
    (hc : lay.leafOf q v / 2 ^ k = c) (hcm : c / 2 = m) (hv : v ≤ nv C c) {j : Bool} {o : ℕ}
    (h : Iter C m c v j o) : Iter C' m c v j o := by
  have hnl : m ∉ Set.range lay.leaf := hcm ▸ lay.half_not_leaf hc
  cases j with
  | false =>
    by_cases hm : nv C' m = nv C m
    · rcases h with h | h
      · exact Or.inl (hm.trans h)
      · exact Or.inr (hF.cond hI hcm hv h)
    · exact Or.inr (hF.cond_of_ne hI hm)
  | true =>
    by_cases hm : nv C' m = nv C m
    · rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (h.trans (hF.mono m))
      · exact Or.inr ⟨hm.trans h1, hF.cond hI hcm hv h2⟩
    · rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (h.trans (hF.mono m))
      · left
        rcases hF.change m hm with ⟨v', hv', -⟩ | ⟨v', c', j', old', l', r', hp, hc', hold, hnew⟩
        · exact absurd ((hI.proc p).wLeaf_mem hv') hnl
        · have := h2 p (by rw [hp]; simp [Loc.atNode, hc']) (by rw [hp]; simp [Loc.old, hold])
          rw [hp] at this
          simp only [Loc.NewGe] at this
          rw [hnew]; exact this

lemma Frame.pCommon (hF : Frame lay C C' p) {q : Fin N} (hq : q ≠ p) {v c : ℕ}
    (h : PCommon lay C q v c) : PCommon lay C' q v c :=
  ⟨by rw [(hF.other q hq).2]; exact h.1, h.2.1, h.2.2.1, h.2.2.2.trans (hF.mono c)⟩

/-- The invariant of a process other than the one taking the step is preserved. -/
lemma Frame.pInv (hI : MInv lay C) (hF : Frame lay C C' p) {q : Fin N} (hq : q ≠ p) :
    PInv lay C' q := by
  obtain ⟨hl, hpd⟩ := hF.other q hq
  have h := hI.proc q
  unfold PInv at h ⊢
  rw [hl, hpd]
  cases hlq : C.loc q with
  | idle | rRoot | rDone _ | wRead _ => rw [hlq] at h; exact h
  | wDone =>
    rw [hlq] at h; obtain ⟨v, h1, h2⟩ := h; exact ⟨v, h1, h2.trans (hF.mono 1)⟩
  | wLeaf v x =>
    rw [hlq] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, ?_⟩
    by_cases hx : nv C' x = nv C x
    · rw [hx]; exact h3
    · rcases hF.change x hx with ⟨v', hv', hnew⟩ | ⟨v', c', j', old', l', r', hp, hc', -, -⟩
      · obtain ⟨-, hx', -⟩ := (hI.proc p).wLeaf hv'
        rcases lay.leafOf_inj (h2.symm.trans hx') with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
        · omega
        · exact absurd rfl hq
      · obtain ⟨⟨-, -, ⟨k, hk⟩, -⟩, -⟩ : PCommon lay C p v' c' ∧ _ := by
          have := hI.proc p; unfold PInv at this; rw [hp] at this; exact ⟨this.1, trivial⟩
        exact absurd (h2 ▸ lay.leafOf_mem q v) (hc' ▸ lay.half_not_leaf hk)
  | pOld v c j =>
    rw [hlq] at h
    obtain ⟨hc, hj⟩ := h
    refine ⟨hF.pCommon hq hc, fun hj' => ?_⟩
    rcases hj hj' with h | h
    · exact Or.inl (h.trans (hF.mono _))
    · exact Or.inr (hF.cond hI rfl hc.2.2.2 h)
  | pL v c j old =>
    rw [hlq] at h
    obtain ⟨hc, h1, h2, h3⟩ := h
    obtain ⟨k, hk⟩ := hc.2.2.1
    refine ⟨hF.pCommon hq hc, h1.trans (hF.mono _), h2.trans (max_le_max (hF.mono _) (hF.mono _)),
      hF.iter hI hk rfl hc.2.2.2 h3⟩
  | pR v c j old l =>
    rw [hlq] at h
    obtain ⟨hc, h1, h2, h3, h4, h5, h6⟩ := h
    obtain ⟨k, hk⟩ := hc.2.2.1
    refine ⟨hF.pCommon hq hc, h1.trans (hF.mono _), h2.trans (max_le_max le_rfl (hF.mono _)),
      h3.trans (hF.mono _), hF.good h4, h5, hF.iter hI hk rfl hc.2.2.2 h6⟩
  | pCas v c j old l r =>
    rw [hlq] at h
    obtain ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    obtain ⟨k, hk⟩ := hc.2.2.1
    refine ⟨hF.pCommon hq hc, h1.trans (hF.mono _), h2, h3.trans (hF.mono _),
      h4.trans (hF.mono _), hF.good h5, hF.good h6, h7, hF.iter hI hk rfl hc.2.2.2 h8⟩

/-- The invariant is preserved by a step that satisfies `Frame` and the invariant of the stepping
process. -/
theorem MInv.of_frame (hI : MInv lay C) (hF : Frame lay C C' p) (hp : PInv lay C' p) :
    MInv lay C' where
  proc q := by
    by_cases hq : q = p
    · subst hq; exact hp
    · exact hF.pInv hI hq
  nodeMax n hn := by
    by_cases hx : nv C' n = nv C n
    · rw [hx]; exact (hI.nodeMax n hn).trans (max_le_max (hF.mono _) (hF.mono _))
    · rcases hF.change n hx with ⟨v', hv', -⟩ | ⟨v', c', j', old', l', r', hpc, hc', -, hnew⟩
      · exact absurd ((hI.proc p).wLeaf_mem hv') hn
      · have := hI.proc p; unfold PInv at this; rw [hpc] at this
        obtain ⟨-, -, -, h3, h4, -⟩ := this
        rw [hnew, ← hc']
        exact max_le_max (h3.trans (hF.mono _)) (h4.trans (hF.mono _))
  good n := by
    by_cases hx : nv C' n = nv C n
    · rw [hx]; exact hF.good (hI.good n)
    · rcases hF.change n hx with ⟨v', hv', hnew⟩ | ⟨v', c', j', old', l', r', hpc, hc', -, hnew⟩
      · rw [hnew]
        rcases hF.exit v' (by rw [hv']; rfl) with h | h
        · exact Or.inr ⟨p, h⟩
        · exact Or.inl h
      · have := hI.proc p; unfold PInv at this; rw [hpc] at this
        obtain ⟨-, -, -, -, -, h5, h6, -⟩ := this
        rw [hnew]; exact hF.good (good_max h5 h6)
  tl v := by
    by_cases hx : nv C' (lay.leaf (.inl v)) = nv C (lay.leaf (.inl v))
    · rw [hx]; exact hI.tl v
    · rcases hF.change _ hx with ⟨v', hv', hnew⟩ | ⟨v', c', j', old', l', r', hpc, hc', -, -⟩
      · obtain ⟨-, hx', -⟩ := (hI.proc p).wLeaf hv'
        have : v' = v := by
          unfold Layout.leafOf at hx'
          split_ifs at hx' with h
          · have := lay.inj hx'; simp [Fin.ext_iff] at this; omega
          · exact absurd (lay.inj hx') (by simp)
        rw [hnew, this]
      · have := hI.proc p; unfold PInv at this; rw [hpc] at this
        obtain ⟨k, hk⟩ := this.1.2.2.1
        exact absurd ⟨_, hc'.symm⟩ (lay.half_not_leaf hk)
  tr q := by
    by_cases hx : nv C' (lay.leaf (.inr q)) = nv C (lay.leaf (.inr q))
    · rw [hx]
      rcases hI.tr q with h | h
      · exact Or.inl (h.trans (hF.mono 1))
      · by_cases hq : q = p
        · subst hq
          rcases hF.propExit _ h with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        · exact Or.inr (by rw [(hF.other q hq).1]; exact h)
    · rcases hF.change _ hx with ⟨v', hv', hnew⟩ | ⟨v', c', j', old', l', r', hpc, hc', -, -⟩
      · obtain ⟨-, hx', -⟩ := (hI.proc p).wLeaf hv'
        have : q = p := by
          unfold Layout.leafOf at hx'
          split_ifs at hx'
          · exact absurd (lay.inj hx') (by simp)
          · simpa using lay.inj hx'
        subst this
        exact Or.inr (by rw [hnew]; exact hF.wleaf _ _ hv')
      · have := hI.proc p; unfold PInv at this; rw [hpc] at this
        obtain ⟨k, hk⟩ := this.1.2.2.1
        exact absurd ⟨_, hc'.symm⟩ (lay.half_not_leaf hk)

end Frame

/-! ### The steps -/

/-- The configuration after process `p` sets node `i` to `x` and moves to local state `l'`. -/
def upd (C : Cfg N) (p : Fin N) (i x : ℕ) (l' : Loc) : Cfg N :=
  { C with mem := Function.update C.mem i x, loc := Function.update C.loc p l' }

section Upd

variable {C : Cfg N} {p : Fin N} {i x : ℕ} {l' : Loc}

@[simp] lemma upd_loc_self : (upd C p i x l').loc p = l' := by simp [upd]

lemma upd_loc_ne {q : Fin N} (h : q ≠ p) : (upd C p i x l').loc q = C.loc q := by
  simp [upd, Function.update_of_ne h]

@[simp] lemma upd_pend : (upd C p i x l').pend = C.pend := rfl

lemma nv_upd (n : ℕ) : nv (upd C p i x l') n = if n = i then x else nv C n := by
  by_cases h : n = i
  · subst h; simp [upd, nv]
  · simp [upd, nv, h]

@[simp] lemma nv_upd_self : nv (upd C p i x l') i = x := by simp [nv_upd]

/-- A `Frame` for a step of `p` that sets node `i` to `x` and moves `p` to `l'`. -/
lemma frame_upd (hmono : nv C i ≤ x)
    (hchange : x ≠ nv C i → (∃ v, C.loc p = .wLeaf v i ∧ x = v) ∨
      (∃ v c j old l r, C.loc p = .pCas v c j old l r ∧ c / 2 = i ∧ nv C i = old ∧
        x = max l r))
    (hfrozen : l'.atNode ≠ none → x = nv C i)
    (hexit : ∀ y, (C.loc p).wOp = some y → l'.wOp = some y ∨ y ≤ nv (upd C p i x l') 1)
    (hpexit : ∀ y, (C.loc p).propOp = some y → l'.propOp = some y ∨ y ≤ nv (upd C p i x l') 1)
    (hwleaf : ∀ v x', C.loc p = .wLeaf v x' → l'.propOp = some v)
    (hnew : ∀ m c v, c / 2 = m → v ≤ nv C c → Cond C m c v → l'.atNode = some m →
      l'.old = nv C m → l'.NewGe c v) :
    Frame lay C (upd C p i x l') p where
  other q hq := ⟨upd_loc_ne hq, rfl⟩
  mono n := by rw [nv_upd]; split_ifs with h <;> [exact h ▸ hmono; exact le_rfl]
  change n hn := by
    rw [nv_upd] at hn ⊢
    split_ifs at hn ⊢ with h
    · subst h; exact hchange hn
    · exact absurd rfl hn
  frozen hl n := by
    rw [nv_upd]; split_ifs with h
    · subst h; exact hfrozen (by simpa using hl)
    · rfl
  exit y hy := by simpa using hexit y hy
  propExit y hy := by simpa using hpexit y hy
  wleaf v x' hv := by simpa using hwleaf v x' hv
  newGe m c v hcm hv hc hm hold := by
    simp only [upd_loc_self] at hm hold ⊢
    have hfr : x = nv C i := hfrozen (by rw [hm]; simp)
    refine hnew m c v hcm hv hc hm (hold.trans ?_)
    rw [nv_upd]; split_ifs with h
    · subst h; exact hfr
    · rfl

end Upd

section Steps

variable {C : Cfg N} {p : Fin N}

lemma PCommon.toUpd {v c : ℕ} (h : PCommon lay C p v c) {i x : ℕ} {l' : Loc}
    (hm : nv C i ≤ x) : PCommon lay (upd C p i x l') p v c := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans ?_⟩
  rw [nv_upd]; split_ifs with h' <;> [exact h' ▸ hm; exact le_rfl]

@[simp] lemma nv_upd_same {i : ℕ} {l' : Loc} (n : ℕ) : nv (upd C p i (nv C i) l') n = nv C n := by
  rw [nv_upd]; split_ifs with h <;> [rw [h]; rfl]

lemma PCommon.toUpd_same {v c : ℕ} (h : PCommon lay C p v c) {i : ℕ} {l' : Loc} :
    PCommon lay (upd C p i (nv C i) l') p v c := PCommon.toUpd h le_rfl

/-- A read step of `p` (memory unchanged). -/
lemma frame_read {i : ℕ} {l' : Loc}
    (hexit : ∀ y, (C.loc p).wOp = some y → l'.wOp = some y ∨ y ≤ nv C 1)
    (hpexit : ∀ y, (C.loc p).propOp = some y → l'.propOp = some y ∨ y ≤ nv C 1)
    (hwleaf : ∀ v x', C.loc p ≠ .wLeaf v x')
    (hnew : ∀ m c v, c / 2 = m → v ≤ nv C c → Cond C m c v → l'.atNode = some m →
      l'.old = nv C m → l'.NewGe c v) :
    Frame lay C (upd C p i (nv C i) l') p :=
  frame_upd le_rfl (fun h => absurd rfl h) (fun _ => rfl) (by simpa using hexit)
    (by simpa using hpexit) (fun v x' h => absurd h (hwleaf v x')) hnew

lemma step_rRoot (hl : C.loc p = .rRoot) (hp : PInv lay C p) :
    Frame lay C (upd C p 1 (nv C 1) (.rDone (nv C 1))) p ∧
      PInv lay (upd C p 1 (nv C 1) (.rDone (nv C 1))) p := by
  unfold PInv at hp; rw [hl] at hp
  refine ⟨frame_read (by simp [hl, Loc.wOp]) (by simp [hl, Loc.propOp]) (by simp [hl])
    (by simp [Loc.atNode]), ?_⟩
  unfold PInv; simp only [upd_loc_self, upd_pend]; exact hp

lemma step_wRead (hI : MInv lay C) {v : ℕ} (hl : C.loc p = .wRead v) :
    let l' := if v ≤ nv C (lay.leaf (.inr p)) then Loc.wDone else .wLeaf v (lay.leaf (.inr p))
    Frame lay C (upd C p (lay.leaf (.inr p)) (nv C (lay.leaf (.inr p))) l') p ∧
      PInv lay (upd C p (lay.leaf (.inr p)) (nv C (lay.leaf (.inr p))) l') p := by
  intro l'
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  have htr : nv C (lay.leaf (.inr p)) ≤ nv C 1 := by
    rcases hI.tr p with h | h
    · exact h
    · rw [hl] at h; simp [Loc.propOp] at h
  refine ⟨frame_read ?_ (by simp [hl, Loc.propOp]) (by simp [hl]) ?_, ?_⟩
  · intro y hy
    simp only [hl, Loc.wOp, Option.some.injEq] at hy; subst hy
    by_cases h : v ≤ nv C (lay.leaf (.inr p))
    · exact Or.inr (h.trans htr)
    · left; simp [l', h, Loc.wOp]
  · intro m c w _ _ _ hm; simp only [l'] at hm; split_ifs at hm <;> simp [Loc.atNode] at hm
  · unfold PInv; simp only [upd_loc_self, upd_pend, l']
    split_ifs with h
    · exact ⟨v, hp.1, by simpa using h.trans htr⟩
    · exact ⟨hp.1, (lay.leafOf_of_le p hp.2).symm, by simp; omega⟩

lemma step_wLeaf (hI : MInv lay C) {v x : ℕ} (hl : C.loc p = .wLeaf v x) :
    Frame lay C (upd C p x v (up v x)) p ∧ PInv lay (upd C p x v (up v x)) p := by
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hx : 2 ≤ x := h2 ▸ lay.two_le_leafOf p v
  have hup : up v x = .pOld v x false := by simp [up]; omega
  rw [hup]
  refine ⟨frame_upd h3 (fun _ => Or.inl ⟨v, hl, rfl⟩) (by simp [Loc.atNode])
    (fun y hy => by simp [hl, Loc.wOp] at hy; simp [hy, Loc.wOp])
    (by simp [hl, Loc.propOp]) (fun v' x' h => by rw [hl] at h; cases h; rfl)
    (by simp [Loc.atNode]), ?_⟩
  unfold PInv; simp only [upd_loc_self]
  exact ⟨⟨h1, hx, ⟨0, by simp [h2]⟩, by simp⟩, by simp⟩

lemma step_pOld (hI : MInv lay C) {v c : ℕ} {j : Bool} (hl : C.loc p = .pOld v c j) :
    Frame lay C (upd C p (c / 2) (nv C (c / 2)) (.pL v c j (nv C (c / 2)))) p ∧
      PInv lay (upd C p (c / 2) (nv C (c / 2)) (.pL v c j (nv C (c / 2)))) p := by
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  obtain ⟨hc, hj⟩ := hp
  obtain ⟨k, hk⟩ := hc.2.2.1
  have hF : Frame lay C (upd C p (c / 2) (nv C (c / 2)) (.pL v c j (nv C (c / 2)))) p :=
    frame_read (fun y hy => by simp [hl, Loc.wOp] at hy; simp [hy, Loc.wOp])
      (fun y hy => by simp [hl, Loc.propOp] at hy; simp [hy, Loc.propOp]) (by simp [hl])
      (by simp [Loc.NewGe])
  refine ⟨hF, ?_⟩
  unfold PInv; simp only [upd_loc_self, nv_upd_same]
  refine ⟨PCommon.toUpd_same hc, le_rfl, hI.nodeMax _ (lay.half_not_leaf hk), ?_⟩
  cases j with
  | false => exact Or.inl (by simp)
  | true =>
    rcases hj rfl with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr ⟨by simp, hF.cond hI rfl hc.2.2.2 h⟩

lemma step_pL (hI : MInv lay C) {v c old : ℕ} {j : Bool} (hl : C.loc p = .pL v c j old) :
    Frame lay C (upd C p (2 * (c / 2)) (nv C (2 * (c / 2)))
        (.pR v c j old (nv C (2 * (c / 2))))) p ∧
      PInv lay (upd C p (2 * (c / 2)) (nv C (2 * (c / 2)))
        (.pR v c j old (nv C (2 * (c / 2))))) p := by
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  obtain ⟨hc, h1, h2, h3⟩ := hp
  obtain ⟨k, hk⟩ := hc.2.2.1
  have hF : Frame lay C (upd C p (2 * (c / 2)) (nv C (2 * (c / 2)))
      (.pR v c j old (nv C (2 * (c / 2))))) p :=
    frame_read (fun y hy => by simp [hl, Loc.wOp] at hy; simp [hy, Loc.wOp])
      (fun y hy => by simp [hl, Loc.propOp] at hy; simp [hy, Loc.propOp]) (by simp [hl])
      (fun m c' w hcm hw _ hm _ => by
        simp only [Loc.atNode, Option.some.injEq] at hm
        simp only [Loc.NewGe]
        intro hc'
        rw [hm, ← hcm, ← hc']; exact hw)
  refine ⟨hF, ?_⟩
  unfold PInv; simp only [upd_loc_self, nv_upd_same]
  refine ⟨PCommon.toUpd_same hc, h1, h2, le_rfl, hF.good (hI.good _), fun h => h ▸ hc.2.2.2, ?_⟩
  exact hF.iter hI hk rfl hc.2.2.2 h3

lemma step_pR (hI : MInv lay C) {v c old l : ℕ} {j : Bool} (hl : C.loc p = .pR v c j old l) :
    Frame lay C (upd C p (2 * (c / 2) + 1) (nv C (2 * (c / 2) + 1))
        (.pCas v c j old l (nv C (2 * (c / 2) + 1)))) p ∧
      PInv lay (upd C p (2 * (c / 2) + 1) (nv C (2 * (c / 2) + 1))
        (.pCas v c j old l (nv C (2 * (c / 2) + 1)))) p := by
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  obtain ⟨hc, h1, h2, h3, h4, h5, h6⟩ := hp
  obtain ⟨k, hk⟩ := hc.2.2.1
  have hF : Frame lay C (upd C p (2 * (c / 2) + 1) (nv C (2 * (c / 2) + 1))
      (.pCas v c j old l (nv C (2 * (c / 2) + 1)))) p :=
    frame_read (fun y hy => by simp [hl, Loc.wOp] at hy; simp [hy, Loc.wOp])
      (fun y hy => by simp [hl, Loc.propOp] at hy; simp [hy, Loc.propOp]) (by simp [hl])
      (fun m c' w hcm hw hC hm hold => by
        simp only [Loc.atNode, Option.some.injEq] at hm
        simp only [Loc.old] at hold
        have := hC p (by simp [hl, Loc.atNode, hm]) (by simp [hl, Loc.old, hold])
        simp only [hl, Loc.NewGe] at this
        simp only [Loc.NewGe]
        by_cases hc' : c' = 2 * (c' / 2)
        · exact (this hc').trans (le_max_left _ _)
        · have : c' = 2 * (c / 2) + 1 := by omega
          rw [← this]; exact hw.trans (le_max_right _ _))
  refine ⟨hF, ?_⟩
  unfold PInv; simp only [upd_loc_self, nv_upd_same]
  refine ⟨PCommon.toUpd_same hc, h1, h2, h3, le_rfl, hF.good h4, hF.good (hI.good _), ?_,
    hF.iter hI hk rfl hc.2.2.2 h6⟩
  by_cases hc' : c = 2 * (c / 2)
  · exact (h5 hc').trans (le_max_left _ _)
  · have : c = 2 * (c / 2) + 1 := by omega
    rw [← this]; exact hc.2.2.2.trans (le_max_right _ _)

/-- The value of node `c / 2` after `CAS(old, max l r)`. -/
def casVal (C : Cfg N) (c old l r : ℕ) : ℕ := if nv C (c / 2) = old then max l r else nv C (c / 2)

/-- The local state after the CAS of line 9. -/
def afterCas (v c : ℕ) (j : Bool) : Loc := if j then up v (c / 2) else .pOld v c true

/-- **The double refresh** (lines 6–9): after the CAS of the second iteration at node `c / 2`,
the node holds a value `≥ v`. -/
lemma step_pCas (hI : MInv lay C) {v c old l r : ℕ} {j : Bool}
    (hl : C.loc p = .pCas v c j old l r) :
    Frame lay C (upd C p (c / 2) (casVal C c old l r) (afterCas v c j)) p ∧
      PInv lay (upd C p (c / 2) (casVal C c old l r) (afterCas v c j)) p ∧
      (j = true → v ≤ casVal C c old l r) := by
  have hp := hI.proc p; unfold PInv at hp; rw [hl] at hp
  obtain ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  obtain ⟨k, hk⟩ := hc.2.2.1
  set x := casVal C c old l r with hx
  have hmono : nv C (c / 2) ≤ x := by
    simp only [hx, casVal]; split_ifs with h
    · rw [h]; exact h2
    · exact le_rfl
  have hsucc : nv C (c / 2) = old → v ≤ x := fun h => by simp [hx, casVal, h, h7]
  have hge : v ≤ x ∨ (j = false ∧ Cond C (c / 2) c v) := by
    cases j with
    | false =>
      rcases h8 with h | h
      · exact Or.inl (hsucc h)
      · exact Or.inr ⟨rfl, h⟩
    | true =>
      rcases h8 with h | ⟨h, -⟩
      · exact Or.inl (h.trans hmono)
      · exact Or.inl (hsucc h)
  have hm1 : 1 ≤ c / 2 := by have := hc.2.1; omega
  have hroot : ∀ {l' : Loc}, c / 2 ≤ 1 → nv (upd C p (c / 2) x l') 1 = x := fun h => by
    have : c / 2 = 1 := by omega
    rw [← this, nv_upd_self]
  have hexit : ∀ y, y = v → (afterCas v c j).wOp = some y ∨
      y ≤ nv (upd C p (c / 2) x (afterCas v c j)) 1 := by
    rintro y rfl
    cases j with
    | false => left; simp [afterCas, Loc.wOp]
    | true =>
      by_cases h : c / 2 ≤ 1
      · right; rw [hroot h]
        rcases hge with h' | ⟨h', -⟩
        · exact h'
        · cases h'
      · left; simp [afterCas, up, h, Loc.wOp]
  have hF : Frame lay C (upd C p (c / 2) x (afterCas v c j)) p := by
    refine frame_upd hmono ?_ ?_ ?_ ?_ (by simp [hl]) ?_
    · intro hne
      right
      have heq : nv C (c / 2) = old := by
        by_contra h; simp [hx, casVal, h] at hne
      exact ⟨v, c, j, old, l, r, hl, rfl, heq, by simp [hx, casVal, heq]⟩
    · intro h; exfalso; apply h
      cases j <;> simp [afterCas, up] <;> (try split_ifs) <;> simp [Loc.atNode]
    · intro y hy; simp [hl, Loc.wOp] at hy; exact hexit y hy.symm
    · intro y hy
      simp [hl, Loc.propOp] at hy
      rcases hexit y hy.symm with h | h
      · left
        revert h
        cases j <;> simp only [afterCas, up] <;> (try split_ifs) <;> simp [Loc.wOp, Loc.propOp]
      · exact Or.inr h
    · intro m c' w _ _ _ hm
      exfalso
      cases j <;> simp [afterCas, up] at hm <;> (try split_ifs at hm) <;> simp [Loc.atNode] at hm
  refine ⟨hF, ?_, fun hj => ?_⟩
  · unfold PInv
    cases j with
    | false =>
      simp only [afterCas, upd_loc_self, Bool.false_eq_true, ite_false]
      refine ⟨PCommon.toUpd hc hmono, fun _ => ?_⟩
      rw [nv_upd_self]
      rcases hge with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr (hF.cond hI rfl hc.2.2.2 h)
    | true =>
      have hv : v ≤ x := by
        rcases hge with h | ⟨h, -⟩
        · exact h
        · cases h
      simp only [afterCas, upd_loc_self, ite_true, up]
      split_ifs with h
      · exact ⟨v, hc.1, by rw [hroot h]; exact hv⟩
      · refine ⟨⟨hc.1, by omega, ⟨k + 1, ?_⟩, by rw [nv_upd_self]; exact hv⟩, by simp⟩
        rw [pow_succ, ← Nat.div_div_eq_div_mul, hk]
  · subst hj
    rcases hge with h | ⟨h, -⟩
    · exact h
    · cases h

end Steps

/-! ### Preservation -/

/-- The invariant holds initially. -/
theorem mInv_init : MInv lay (impl lay).initCfg where
  proc p := by unfold PInv; simp [impl, Impl.initCfg]
  nodeMax n _ := by simp [impl, Impl.initCfg, nv]
  good n := Or.inl (by simp [impl, Impl.initCfg, nv])
  tl v := by simp [impl, Impl.initCfg, nv]
  tr p := Or.inl (by simp [impl, Impl.initCfg, nv])

section Preservation

variable {C C' : Cfg N} {p : Fin N}

lemma step_tau_upd {i : ℕ} {o : (Base i).Op} {k : (Base i).Resp → Loc}
    (h : (impl lay).step C (.tau p) = some C')
    (hact : (impl lay).act p (C.loc p) = .access i o k) :
    C' = upd C p i ((Base i).δ (C.mem i) o).1 (k ((Base i).δ (C.mem i) o).2) := by
  rw [Impl.step_tau_eq_some (Impl.step_tau h).1 hact] at h
  exact (Option.some.inj h).symm

/-- **Preservation of the memory invariant** by every step; the step satisfies `Frame` (in
particular it does not decrease any node: **Lemma 8**). -/
theorem MInv.step (hI : MInv lay C) {ℓ : Label (Fin N) maxRegObj}
    (h : (impl lay).step C ℓ = some C') : MInv lay C' ∧ Frame lay C C' ℓ.proc := by
  suffices hFP : Frame lay C C' ℓ.proc ∧ PInv lay C' ℓ.proc from
    ⟨hI.of_frame hFP.1 hFP.2, hFP.1⟩
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hidle := (hI.proc p).pend_none h0
    have hC'p : C'.loc p = (impl lay).invoke p .idle o := by
      rw [hloc, Function.update_self, hidle]
    simp only [Label.proc]
    refine ⟨⟨fun q hq => ⟨by rw [hloc, Function.update_of_ne hq],
        by rw [hpend, Function.update_of_ne hq]⟩,
      fun n => by simp [nv, hmem], fun n hn => absurd (by simp [nv, hmem]) hn,
      fun _ n => by simp [nv, hmem], fun y hy => by simp [hidle, Loc.wOp] at hy,
      fun y hy => by simp [hidle, Loc.propOp] at hy, fun v x hv => by simp [hidle] at hv,
      fun m c v _ _ _ hm => ?_⟩, ?_⟩
    · rw [hC'p] at hm
      cases o <;> simp [impl] at hm <;> (try split_ifs at hm) <;> simp [Loc.atNode] at hm
    · unfold PInv
      rw [hC'p, hpend]
      cases o with
      | readMax => simp [impl]
      | writeMax v =>
        simp only [impl]
        split_ifs with hv
        · refine ⟨by simp, rfl, ?_⟩
          rw [lay.leafOf_of_lt p hv]
          have := hI.tl ⟨v, hv⟩
          simpa [nv, hmem] using this
        · exact ⟨by simp, by omega⟩
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    have hl : l = .idle ∧ ((C.loc p).wOp = none ∧ (C.loc p).propOp = none ∧
        ∀ v x, C.loc p ≠ .wLeaf v x) := by
      cases hlp : C.loc p <;> simp [impl, hlp] at hact
      · have := hI.proc p; unfold PInv at this; rw [hlp] at this; exact absurd this h0
      all_goals (obtain ⟨-, rfl⟩ := hact; simp [Loc.wOp, Loc.propOp])
    obtain ⟨rfl, hw, hpr, hwl⟩ := hl
    simp only [Label.proc]
    refine ⟨⟨fun q hq => ⟨by rw [hloc, Function.update_of_ne hq],
        by rw [hpend, Function.update_of_ne hq]⟩,
      fun n => by simp [nv, hmem], fun n hn => absurd (by simp [nv, hmem]) hn,
      fun _ n => by simp [nv, hmem], fun y hy => by simp [hw] at hy,
      fun y hy => by simp [hpr] at hy, fun v x hv => absurd hv (hwl v x),
      fun m c v _ _ _ hm => by simp [hloc, Loc.atNode] at hm⟩, ?_⟩
    unfold PInv; simp [hloc, hpend]
  | tau p =>
    simp only [Label.proc]
    cases hl : C.loc p with
    | idle | rDone _ | wDone =>
      exfalso
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      simp [impl, hl] at hact
    | rRoot =>
      have hact : (impl lay).act p (C.loc p) = .access 1 .read (fun r => .rDone (val r)) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_rRoot hl (hI.proc p)
    | wRead v =>
      have hact : (impl lay).act p (C.loc p) = .access (lay.leaf (.inr p)) .read
          (fun r => if v ≤ val r then .wDone else .wLeaf v (lay.leaf (.inr p))) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_wRead hI hl
    | wLeaf v x =>
      have hact : (impl lay).act p (C.loc p) = .access x (.write v) (fun _ => up v x) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_wLeaf hI hl
    | pOld v c j =>
      have hact : (impl lay).act p (C.loc p) =
          .access (c / 2) .read (fun r => .pL v c j (val r)) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_pOld hI hl
    | pL v c j old =>
      have hact : (impl lay).act p (C.loc p) =
          .access (2 * (c / 2)) .read (fun r => .pR v c j old (val r)) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_pL hI hl
    | pR v c j old l =>
      have hact : (impl lay).act p (C.loc p) =
          .access (2 * (c / 2) + 1) .read (fun r => .pCas v c j old l (val r)) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      exact step_pR hI hl
    | pCas v c j old l r =>
      have hact : (impl lay).act p (C.loc p) = .access (c / 2) (.cas old (max l r))
          (fun _ => if j then up v (c / 2) else .pOld v c true) := by
        rw [hl]; rfl
      obtain rfl := step_tau_upd h hact
      have heq : ((Base (c / 2)).δ (C.mem (c / 2)) (.cas old (max l r))).1 =
          casVal C c old l r := by
        simp only [casVal, nv]; split_ifs <;> simp_all
      rw [heq]
      exact (step_pCas hI hl).imp_right And.left

end Preservation

/-- The memory invariant holds in every reachable configuration. -/
theorem mInv_of_run {α : List (Label (Fin N) maxRegObj)} {C : Cfg N}
    (h : (impl lay).run α = some C) : MInv lay C :=
  (impl lay).invariant_of_run mInv_init (fun _ _ _ hC hs => (hC.step hs).1) h

/-- **Lemma 8** of [Hendler–Khait, PODC'14]: in every execution, the value of every node is
non-decreasing. -/
theorem lemma8 {α : List (Label (Fin N) maxRegObj)} {C C' : Cfg N}
    {ℓ : Label (Fin N) maxRegObj} (h : (impl lay).run α = some C)
    (hs : (impl lay).step C ℓ = some C') (n : ℕ) : C.mem n ≤ C'.mem n :=
  ((mInv_of_run h).step hs).2.mono n

/-- **Propagation guarantee** (the content of Lemmas 9 and 11 of [Hendler–Khait, PODC'14]): a
`WriteMax(v)` about to return finds the root holding a value `≥ v`. -/
theorem root_ge_of_wDone {α : List (Label (Fin N) maxRegObj)} {C : Cfg N} {p : Fin N} {v : ℕ}
    (h : (impl lay).run α = some C) (hl : C.loc p = .wDone)
    (hp : C.pend p = some (.writeMax v)) : v ≤ C.mem 1 := by
  have := (mInv_of_run h).proc p
  unfold PInv at this; rw [hl] at this
  obtain ⟨w, hw, hle⟩ := this
  rw [hp] at hw; cases hw; exact hle

end Podc.ReadUpdateTradeoffs.AlgA
