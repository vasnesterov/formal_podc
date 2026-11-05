import Papers.PODC2019.AbortableMutexAmortized.Invariant

/-!
# RMR complexity (Section 5 and Appendix C)

* The shared variables `Var n` and the variable accessed by each step (`access`).
* DSM cost model (`dsmCost`, with a `home` partition map; `go_p` is in `p`'s partition) and CC cost
  model (`ccCost`, `ccUpd`: per-process caches, reads cache, non-reads invalidate everywhere).
* The paper's potentials `PhiD` (`ΦDSM`) and `PhiC` (`ΦCC`).
* Lemma 5.2 (`lemma_5_2`) and Lemma 5.3 (`lemma_5_3`): per-line amortized costs.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-! ## Shared variables and cost models -/

/-- The shared variables of Algorithm 1: `tail`, the nodes (`sentinel` and `node_p`), and the
busy-wait flags `go_p`. -/
inductive Var (n : ℕ) where
  /-- `tail` -/
  | tail
  /-- a node (`none` = `sentinel`, `some p` = `node_p`) -/
  | node (a : Node n)
  /-- `go_p` -/
  | go (p : Fin n)
  deriving DecidableEq

/-- `Var n ≃ Unit ⊕ Option (Fin n) ⊕ Fin n`. -/
def Var.equiv : Var n ≃ Unit ⊕ Option (Fin n) ⊕ Fin n where
  toFun
    | .tail => .inl ()
    | .node a => .inr (.inl a)
    | .go p => .inr (.inr p)
  invFun
    | .inl _ => .tail
    | .inr (.inl a) => .node a
    | .inr (.inr p) => .go p
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ <;> rfl

instance : Fintype (Var n) := Fintype.ofEquiv _ Var.equiv.symm

/-- **Theorem 5.1** (space complexity `O(n)`): Algorithm 1 uses exactly `2n + 2` shared variables
(`tail`, `n + 1` nodes and `n` flags `go_p`), plus a constant number of local variables per
process. -/
theorem theorem_5_1 : Fintype.card (Var n) = 2 * n + 2 := by
  rw [Fintype.card_congr Var.equiv]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_option, Fintype.card_fin]
  omega

/-- The variable written by `*v_p ← true` (lines 8, 11); the invariant (`I11`) guarantees that
`v_p` is a go-address there, otherwise we pick `tail` (the step does not change anything then). -/
def goTarget : Val n → Var n
  | .go q => .go q
  | _ => .tail

/-- The shared variable accessed by the step `(p, ab)` and whether the operation is a read
(the only read is line 4, `wait till go_p`; every other line is a FAS or a write). -/
def access (s : State n) (p : Fin n) (ab : Bool) : Var n × Bool :=
  match lineOf s p ab with
  | .l1 | .l7 | .l10 => (.node (s.mynode p), false)
  | .l2 => (.tail, false)
  | .l3 | .l6 | .l9 => (.node (s.pred p), false)
  | .l4 => (.go p, true)
  | .l5 => (.go p, false)
  | .l8 | .l11 => (goTarget (s.v p), false)

/-- DSM cost of a step: an access is remote (costs 1) unless the variable lies in `p`'s memory
partition `home x = some p`. -/
def dsmCost (home : Var n → Option (Fin n)) (s : State n) (p : Fin n) (ab : Bool) : ℕ :=
  if home (access s p ab).1 = some p then 0 else 1

/-- CC caches: `C p x` iff `x` is in `p`'s cache. -/
abbrev Cache (n : ℕ) := Fin n → Var n → Bool

/-- CC cost of an access `(x, r)` by `p`: a read of a cached variable is free, every other
access costs one RMR. -/
def ccCost (C : Cache n) (p : Fin n) (a : Var n × Bool) : ℕ :=
  if a.2 = true ∧ C p a.1 = true then 0 else 1

/-- CC cache update: a read brings `x` into `p`'s cache; a non-read operation (write, FAS)
invalidates `x` in all caches. -/
def ccUpd (C : Cache n) (p : Fin n) (a : Var n × Bool) : Cache n :=
  if a.2 then Function.update C p (Function.update (C p) a.1 true)
  else fun q y => if y = a.1 then false else C q y

/-- A memory layout satisfying the DSM hypothesis (`go_p` in `p`'s partition, everything else in
global memory); shows that the hypothesis of `lemma_5_2` and `theorem_5_4_dsm` is satisfiable. -/
def stdHome : Var n → Option (Fin n)
  | .go q => some q
  | _ => none

theorem stdHome_go (q : Fin n) : stdHome (.go q) = some q := rfl

/-- The empty caches. -/
def emptyCache : Cache n := fun _ _ => false

theorem dsmCost_le_one (home : Var n → Option (Fin n)) (s : State n) (p : Fin n) (ab : Bool) :
    dsmCost home s p ab ≤ 1 := by
  unfold dsmCost; split_ifs <;> omega

theorem ccCost_le_one (C : Cache n) (p : Fin n) (a : Var n × Bool) : ccCost C p a ≤ 1 := by
  unfold ccCost; split_ifs <;> omega

/-! ## Potentials -/

/-- Indicator `1{P}` (as an integer). -/
def ind (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split_ifs <;> omega
theorem ind_le_one (P : Prop) [Decidable P] : ind P ≤ 1 := by unfold ind; split_ifs <;> omega
theorem ind_of_not {P : Prop} [Decidable P] (h : ¬ P) : ind P = 0 := by simp [ind, h]
theorem ind_of {P : Prop} [Decidable P] (h : P) : ind P = 1 := by simp [ind, h]
theorem ind_mono {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) : ind P ≤ ind Q := by
  unfold ind; split_ifs <;> simp_all
theorem ind_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : ind P = ind Q := by
  unfold ind; split_ifs <;> simp_all

/-- `*mynode_q = pred_q`: `q` has marked its node as aborted. -/
def abd (s : State n) (q : Fin n) : Prop := s.node (s.mynode q) = .addr (s.pred q)

instance (s : State n) (q : Fin n) : Decidable (abd s q) := by unfold abd; infer_instance

/-- The summand of `ΦDSM` for process `q`. -/
def phiD (s : State n) (q : Fin n) : ℤ :=
  ind (s.go q = true) + ind (s.pc q = .l6) + ind (abd s q)

/-- The DSM potential `ΦDSM = Σ_p 1{go_p = true} + 1{PC_p = 6} + 1{*mynode_p = pred_p}`. -/
def PhiD (s : State n) : ℤ := ∑ q, phiD s q

/-- The summand of `ΦCC` for process `q`. -/
def phiC (s : State n) (C : Cache n) (q : Fin n) : ℤ :=
  3 * ind (s.go q = true) + ind (s.pc q = .l6) + ind (abd s q) + ind (C q (.go q) = false)

/-- The CC potential
`ΦCC = Σ_p 3·1{go_p = true} + 1{PC_p = 6} + 1{*mynode_p = pred_p} + 1{notcached(p)}`. -/
def PhiC (s : State n) (C : Cache n) : ℤ := ∑ q, phiC s C q

/-- The part of `ΦCC` that depends on the flags and caches only. -/
def PhiX (g : Fin n → Bool) (C : Cache n) : ℤ :=
  ∑ q, (2 * ind (g q = true) + ind (C q (.go q) = false))

theorem PhiC_eq (s : State n) (C : Cache n) : PhiC s C = PhiD s + PhiX s.go C := by
  unfold PhiC PhiD PhiX
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold phiC phiD; ring

/-! ## Sum bookkeeping -/

theorem sum_sub_le {f g b : Fin n → ℤ} (h : ∀ q, g q - f q ≤ b q) :
    ∑ q, g q - ∑ q, f q ≤ ∑ q, b q := by
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun q _ => h q

theorem sum_sub_eq_of_ne {f g : Fin n → ℤ} (p : Fin n) (h : ∀ q, q ≠ p → g q = f q) :
    ∑ q, g q - ∑ q, f q = g p - f p := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    Finset.sum_congr rfl fun q hq => h q (Finset.ne_of_mem_erase hq)]
  ring

/-! ## Facts from the invariant -/

theorem act_not_addr {s : State n} (h : Inv s) {p : Fin n} (hact : (s.pc p).act = true) (c : Node n) :
    s.node (s.mynode p) ≠ .addr c := by
  rcases h.loc.i7 p hact with h1 | ⟨y, -, -, h1⟩ <;> rw [h1] <;> simp

theorem act_not_abd {s : State n} (h : Inv s) {p : Fin n} (hact : (s.pc p).act = true) :
    ¬ abd s p := act_not_addr h hact _

/-- The value read by a FAS on `*pred_p` (lines 3, 6) is a node address only when `pred_p` is the
node of an aborted queue member `x ≠ p` with `*mynode_x = pred_x` (`a₀` never holds an address
by `I9`; an active member's node holds `nil` or a go-address by `I7`). -/
theorem owner_of_addr {s : State n} (h : Inv s) {p : Fin n} (hact : (s.pc p).act = true)
    {b : Node n} (hb : s.node (s.pred p) = .addr b) :
    ∃ x, x ≠ p ∧ s.mynode x = s.pred p ∧ abd s x := by
  have hs := h.struct
  have hl := h.loc
  have hp : p ∈ Qof s := (hs.mem p).2 (Or.inl hact)
  rcases hs.ok.chain.pred_mem hp with h0 | ⟨x, hx, hx'⟩
  · rw [h0] at hb
    by_cases hy : ∃ y, s.pred y = a0of s ∧ s.pc y = .l7
    · obtain ⟨y, hy1, hy2⟩ := hy
      rcases hl.i9b y hy1 hy2 with h1 | h1 <;> rw [h1] at hb <;> simp at hb
    · have := hl.i9a fun y hy1 hy2 => hy ⟨y, hy1, hy2⟩
      rw [this] at hb; simp at hb
  · rcases (hs.mem x).1 hx with hxa | ⟨hxb, hxn⟩
    · exact absurd (hx' ▸ hb) (act_not_addr h hxa b)
    · refine ⟨x, ?_, hx'.symm, hxn⟩
      rintro rfl
      revert hact hxb; cases s.pc x <;> simp [PC.act, PC.ab]

/-! ## DSM potential change per line -/

section DPhi

variable {s : State n} {p : Fin n}

theorem dPhi_l1 (h : Inv s) (hpc : s.pc p = .l1) (ab : Bool) :
    PhiD (step s p ab) - PhiD s ≤ 0 := by
  have hinj := h.struct.ok.inj
  have := sum_sub_le (f := phiD s) (g := phiD (step s p ab)) (b := fun _ => 0) fun q => by
    simp only [step, hpc]
    by_cases hq : q = p
    · subst hq
      simp [phiD, abd, ind, hpc]
      split_ifs <;> simp_all
    · have : s.mynode q ≠ s.mynode p := fun e => hq (hinj e)
      simp [phiD, abd, ind, hq, this]
  simpa [PhiD] using this

theorem dPhi_l2 (h : Inv s) (hpc : s.pc p = .l2) (ab : Bool) :
    PhiD (step s p ab) - PhiD s ≤ 0 := by
  have h6 := h.loc.i6a p hpc
  have := sum_sub_le (f := phiD s) (g := phiD (step s p ab)) (b := fun _ => 0) fun q => by
    simp only [step, hpc]
    by_cases hq : q = p
    · subst hq
      simp [phiD, abd, ind, hpc, h6]
    · simp [phiD, abd, ind, hq]
  simpa [PhiD] using this

theorem loopPC_eq_l6 {w : Val n} : loopPC w = .l6 ↔ ∃ b, w = .addr b := by
  cases w <;> simp [loopPC]

/-- Writing a non-address value into a node can only clear `abd`. -/
theorem abd_of_write {s s' : State n} {q : Fin n} {a : Node n} {w : Val n}
    (hw : ∀ c, w ≠ .addr c) (hn : s'.node = Function.update s.node a w)
    (hm : s'.mynode q = s.mynode q) (hp : s'.pred q = s.pred q) (h : abd s' q) :
    abd s q ∧ s.mynode q ≠ a := by
  unfold abd at *
  rw [hn, hm, hp] at h
  by_cases e : s.mynode q = a
  · subst e; simp at h; exact absurd h (hw _)
  · simp [e] at h; exact ⟨h, e⟩

/-- An active process whose node is not overwritten by an address does not become aborted. -/
theorem not_abd_of_write {s s' : State n} {q : Fin n} {a : Node n} {w : Val n}
    (hna : ∀ c, s.node (s.mynode q) ≠ .addr c) (hw : ∀ c, w ≠ .addr c)
    (hn : s'.node = Function.update s.node a w) (hm : s'.mynode q = s.mynode q) : ¬ abd s' q := by
  unfold abd; rw [hn, hm]
  by_cases e : s.mynode q = a
  · subst e; simp; exact hw _
  · simp [e]; exact hna _

theorem dPhi_fasPred (h : Inv s) (hact : (s.pc p).act = true) :
    PhiD (fasPred s p) - PhiD s ≤ -ind (s.pc p = .l6) := by
  have hna := act_not_addr h hact
  have hnab := act_not_abd h hact
  have hw : ∀ c, (Val.go p : Val n) ≠ .addr c := by simp
  have hself : ¬ abd (fasPred s p) p := not_abd_of_write hna hw rfl rfl
  have hoth : ∀ q, q ≠ p → abd (fasPred s p) q → abd s q ∧ s.mynode q ≠ s.pred p :=
    fun q hq => abd_of_write hw rfl rfl (by simp [fasPred, hq])
  have hpc : ∀ q, q ≠ p → (fasPred s p).pc q = s.pc q := fun q hq => by simp [fasPred, hq]
  by_cases hb : ∃ b, s.node (s.pred p) = .addr b
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨x, hxp, hxm, hxa⟩ := owner_of_addr h hact hb
    have := sum_sub_le (f := phiD s) (g := phiD (fasPred s p))
      (b := fun q => (if q = p then 1 - ind (s.pc p = .l6) else 0) + (if q = x then -1 else 0))
      fun q => by
        simp only [phiD]
        have hg : (fasPred s p).go = s.go := rfl
        by_cases hq : q = p
        · subst hq
          simp only [hg, ite_true, ite_false, ind_of_not hself, ind_of_not hnab, (Ne.symm hxp)]
          linarith [ind_le_one ((fasPred s q).pc q = .l6)]
        · by_cases hqx : q = x
          · subst hqx
            have : ¬ abd (fasPred s p) q := fun e => (hoth q hq e).2 hxm
            simp only [hg, hpc q hq, ind_of_not this, ind_of hxa, hq, ite_true, ite_false]
            linarith
          · simp only [hg, hpc q hq, hq, hqx, ite_false]
            linarith [ind_mono (fun e => (hoth q hq e).1)]
    have hs : ∑ q : Fin n, ((if q = p then 1 - ind (s.pc p = .l6) else 0) +
        (if q = x then (-1 : ℤ) else 0)) = -ind (s.pc p = .l6) := by
      simp [Finset.sum_add_distrib]; ring
    unfold PhiD; linarith
  · have hl : loopPC (s.node (s.pred p)) ≠ .l6 := fun e => hb (loopPC_eq_l6.1 e)
    have := sum_sub_le (f := phiD s) (g := phiD (fasPred s p))
      (b := fun q => if q = p then -ind (s.pc p = .l6) else 0)
      fun q => by
        simp only [phiD]
        have hg : (fasPred s p).go = s.go := rfl
        by_cases hq : q = p
        · subst hq
          have : ¬ (fasPred s q).pc q = .l6 := by simpa [fasPred] using hl
          simp only [hg, ite_true, ind_of_not hself, ind_of_not hnab, ind_of_not this]
          linarith
        · simp only [hg, hpc q hq, hq, ite_false]
          linarith [ind_mono (fun e => (hoth q hq e).1)]
    simpa [PhiD] using this

theorem dPhi_line9 (h : Inv s) (hact : (s.pc p).act = true) :
    PhiD (line9 s p) - PhiD s ≤ 0 := by
  have hna := act_not_addr h hact
  have hnab := act_not_abd h hact
  have hw : ∀ c, (Val.nil : Val n) ≠ .addr c := by simp
  have hself : ¬ abd (line9 s p) p := not_abd_of_write hna hw rfl rfl
  have hoth : ∀ q, q ≠ p → abd (line9 s p) q → abd s q ∧ s.mynode q ≠ s.pred p :=
    fun q hq => abd_of_write hw rfl rfl (by simp [line9, hq])
  have := sum_sub_le (f := phiD s) (g := phiD (line9 s p)) (b := fun _ => 0) fun q => by
    simp only [phiD]
    have hg : (line9 s p).go = s.go := rfl
    by_cases hq : q = p
    · subst hq
      have : ¬ (line9 s q).pc q = .l6 := by simp [line9]; split_ifs <;> simp
      simp only [hg, ind_of_not hself, ind_of_not this]
      linarith [ind_nonneg (s.pc q = .l6), ind_nonneg (abd s q)]
    · have hpc : (line9 s p).pc q = s.pc q := by simp [line9, hq]
      simp only [hg, hpc]
      linarith [ind_mono (fun e => (hoth q hq e).1)]
  simpa [PhiD] using this

theorem dPhi_l4 (hpc : s.pc p = .l4) :
    PhiD (step s p false) - PhiD s ≤ 0 := by
  have := sum_sub_le (f := phiD s) (g := phiD (step s p false)) (b := fun _ => 0) fun q => by
    simp only [step, hpc, Bool.false_eq_true, ite_false]
    by_cases hg : s.go p = true
    · simp only [hg, ite_true]
      by_cases hq : q = p
      · subst hq; simp [phiD, abd, ind, hpc]
      · simp [phiD, abd, ind, hq]
    · simp [hg]
  simpa [PhiD] using this

theorem dPhi_l5 (h : Inv s) (hpc : s.pc p = .l5) :
    PhiD (step s p false) - PhiD s ≤ 0 := by
  have hg := h.loc.i12 p hpc
  have := sum_sub_le (f := phiD s) (g := phiD (step s p false)) (b := fun _ => 0) fun q => by
    simp only [step, hpc]
    by_cases hq : q = p
    · subst hq; simp [phiD, abd, ind, hpc, hg]
    · simp [phiD, abd, ind, hq]
  simpa [PhiD] using this

theorem dPhi_l7 (h : Inv s) (hpc : s.pc p = .l7) (ab : Bool) :
    PhiD (step s p ab) - PhiD s ≤ 0 := by
  have hinj := h.struct.ok.inj
  have h10 := h.loc.i10 p hpc
  have h9 := h.loc.i9b p h10 hpc
  have hne := h.struct.a0_ne p
  have := sum_sub_le (f := phiD s) (g := phiD (step s p ab)) (b := fun _ => 0) fun q => by
    simp only [step, hpc]
    by_cases hq : q = p
    · subst hq
      have : s.pred q ≠ s.mynode q := h10 ▸ hne.symm
      have hn : ¬ abd { s with
          node := Function.update s.node (s.mynode q) .token
          v := Function.update s.v q (s.node (s.mynode q))
          mynode := Function.update s.mynode q (s.pred q)
          pc := Function.update s.pc q
            (if s.node (s.mynode q) = .nil then .l1 else .l8) } q := by
        unfold abd
        simp only [Function.update_self, Function.update_of_ne this]
        rw [h10]; rcases h9 with h9 | h9 <;> rw [h9] <;> simp
      have h6 : ¬ (Function.update s.pc q
            (if s.node (s.mynode q) = .nil then PC.l1 else .l8)) q = .l6 := by
        simp; split_ifs <;> simp
      simp only [phiD, ind_of_not hn, ind_of_not h6, hpc]
      linarith [ind_nonneg (abd s q), ind_nonneg (PC.l7 = PC.l6)]
    · have : s.mynode q ≠ s.mynode p := fun e => hq (hinj e)
      simp [phiD, abd, ind, hq, this]
  simpa [PhiD] using this

theorem dPhi_wake (hpc : s.pc p = .l8 ∨ s.pc p = .l11) :
    PhiD (wake s p) - PhiD s ≤ 1 := by
  have h6 : s.pc p ≠ .l6 := by rcases hpc with h | h <;> rw [h] <;> simp
  rcases hv : s.v p with _ | _ | _ | r
  case go =>
    have := sum_sub_le (f := phiD s) (g := phiD (wake s p)) (b := fun q => if q = r then 1 else 0)
      fun q => by
        simp only [phiD, abd, ind, wake, hv, Function.update_apply]
        split_ifs <;> simp_all
    simpa [PhiD] using this
  all_goals
    have := sum_sub_le (f := phiD s) (g := phiD (wake s p)) (b := fun _ => 0)
      fun q => by
        simp only [phiD, abd, ind, wake, hv, Function.update_apply]
        split_ifs <;> simp_all
    simp only [PhiD]; linarith [this, show (∑ _q : Fin n, (0 : ℤ)) = 0 by simp]

theorem dPhi_l10 (h : Inv s) (hpc : s.pc p = .l10) (ab : Bool) :
    PhiD (step s p ab) - PhiD s ≤ 1 := by
  have hinj := h.struct.ok.inj
  have := sum_sub_le (f := phiD s) (g := phiD (step s p ab)) (b := fun q => if q = p then 1 else 0)
    fun q => by
      simp only [step, hpc]
      by_cases hq : q = p
      · subst hq
        simp only [phiD, abd, ind, Function.update_apply, ite_true, hpc]
        split_ifs <;> simp_all
      · have : s.mynode q ≠ s.mynode p := fun e => hq (hinj e)
        simp [phiD, abd, ind, hq, this]
  simpa [PhiD] using this

end DPhi

/-! ## Lemma 5.2 (DSM) -/

/-- The amortized DSM cost `α = cost + ΔΦDSM` of the step `(p, ab)` from `s`. -/
def amortD (home : Var n → Option (Fin n)) (s : State n) (p : Fin n) (ab : Bool) : ℤ :=
  (dsmCost home s p ab : ℤ) + PhiD (step s p ab) - PhiD s

/-- The paper's bounds in Lemma 5.2. -/
def boundD : PC → ℤ
  | .l4 | .l5 | .l6 => 0
  | .l8 | .l10 | .l11 => 2
  | _ => 1

/-- The step `(p, false)` at line 4 or 5 is a local access in DSM (`go_p` is in `p`'s partition). -/
theorem dsmCost_go {home : Var n → Option (Fin n)} (hhome : ∀ q, home (.go q) = some q)
    {s : State n} {p : Fin n} (hpc : s.pc p = .l4 ∨ s.pc p = .l5) : dsmCost home s p false = 0 := by
  rcases hpc with hpc | hpc <;> simp [dsmCost, access, lineOf, hpc, hhome]

/-- **Lemma 5.2** (Appendix C): in the DSM model (with `go_p` in `p`'s partition), the amortized
cost w.r.t. `ΦDSM` of a step executing line `ℓ` is at most 1 for `ℓ ∈ {1, 2, 3, 7, 9}`, at most 2
for `ℓ ∈ {8, 10, 11}` and at most 0 for `ℓ ∈ {4, 5, 6}` (an aborting step at lines 4–6 executes
line 9). -/
theorem lemma_5_2 {home : Var n → Option (Fin n)} (hhome : ∀ q, home (.go q) = some q)
    {s : State n} (h : Inv s) (p : Fin n) (ab : Bool) :
    amortD home s p ab ≤ boundD (lineOf s p ab) := by
  have hc : (dsmCost home s p ab : ℤ) ≤ 1 := by exact_mod_cast dsmCost_le_one home s p ab
  unfold amortD
  cases hpc : s.pc p with
  | l1 => simp only [lineOf, hpc, boundD]; linarith [dPhi_l1 h hpc ab]
  | l2 => simp only [lineOf, hpc, boundD]; linarith [dPhi_l2 h hpc ab]
  | l3 =>
    have e : step s p ab = fasPred s p := by simp [step, hpc]
    have := dPhi_fasPred h (p := p) (by simp [hpc, PC.act])
    simp only [lineOf, hpc, boundD, e]; linarith [ind_nonneg (s.pc p = .l6)]
  | l4 =>
    cases ab with
    | false =>
      have hc0 := dsmCost_go hhome (Or.inl hpc)
      simp only [lineOf, hpc, boundD, hc0, Nat.cast_zero, Bool.false_eq_true, ite_false]
      linarith [dPhi_l4 hpc]
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      simp only [lineOf, hpc, boundD, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l5 =>
    cases ab with
    | false =>
      have hc0 := dsmCost_go hhome (Or.inr hpc)
      simp only [lineOf, hpc, boundD, hc0, Nat.cast_zero, Bool.false_eq_true, ite_false]
      linarith [dPhi_l5 h hpc]
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      simp only [lineOf, hpc, boundD, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l6 =>
    cases ab with
    | false =>
      have e : step s p false = fasPred s p := by simp [step, hpc]
      have := dPhi_fasPred h (p := p) (by simp [hpc, PC.act])
      rw [ind_of hpc] at this
      simp only [lineOf, hpc, boundD, e, Bool.false_eq_true, ite_false]; linarith
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      simp only [lineOf, hpc, boundD, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l7 => simp only [lineOf, hpc, boundD]; linarith [dPhi_l7 h hpc ab]
  | l8 =>
    have e : step s p ab = wake s p := by simp [step, hpc]
    simp only [lineOf, hpc, boundD, e]; linarith [dPhi_wake (p := p) (Or.inl hpc)]
  | l9 =>
    have e : step s p ab = line9 s p := by simp [step, hpc]
    simp only [lineOf, hpc, boundD, e]
    linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l10 => simp only [lineOf, hpc, boundD]; linarith [dPhi_l10 h hpc ab]
  | l11 =>
    have e : step s p ab = wake s p := by simp [step, hpc]
    simp only [lineOf, hpc, boundD, e]; linarith [dPhi_wake (p := p) (Or.inr hpc)]

/-! ## Lemma 5.3 (CC) -/

/-- The amortized CC cost `α = cost + ΔΦCC` of the step `(p, ab)` from `(s, C)`. -/
def amortC (C : Cache n) (s : State n) (p : Fin n) (ab : Bool) : ℤ :=
  (ccCost C p (access s p ab) : ℤ) + PhiC (step s p ab) (ccUpd C p (access s p ab)) - PhiC s C

/-- The (correct) per-line bounds of Lemma 5.3. -/
def boundC : PC → ℤ
  | .l4 | .l5 | .l6 => 0
  | .l8 | .l11 => 5
  | .l10 => 2
  | _ => 1

theorem PhiX_congr {g g' : Fin n → Bool} {C C' : Cache n} (hg : g' = g)
    (hC : ∀ q, C' q (.go q) = C q (.go q)) : PhiX g' C' = PhiX g C := by
  subst hg; unfold PhiX; simp only [hC]

/-- A FAS on a node or on `tail` costs one RMR and changes `ΦCC` exactly as it changes `ΦDSM`. -/
theorem amortC_of_nonGo {C : Cache n} {s : State n} {p : Fin n} {ab : Bool} {x : Var n}
    (ha : access s p ab = (x, false)) (hx : ∀ q, x ≠ .go q) (hg : (step s p ab).go = s.go) :
    amortC C s p ab = 1 + PhiD (step s p ab) - PhiD s := by
  unfold amortC
  rw [PhiC_eq, PhiC_eq, PhiX_congr hg (C' := ccUpd C p (access s p ab)) (C := C) fun q => by
    simp [ccUpd, ha, (hx q).symm]]
  simp [ccCost, ha]; ring

/-- Lines 8 and 11 in CC: one RMR, `go_q` rises (`+3`) and is invalidated in `q`'s cache (`+1`):
amortized cost at most 5. -/
theorem amortC_wake {C : Cache n} {s : State n} {p : Fin n} {ab : Bool}
    (hpc : s.pc p = .l8 ∨ s.pc p = .l11) : amortC C s p ab ≤ 5 := by
  have e : step s p ab = wake s p := by rcases hpc with hpc | hpc <;> simp [step, hpc]
  have hD := dPhi_wake (p := p) hpc
  rcases hv : s.v p with _ | _ | _ | r
  case go =>
    have ha : access s p ab = (.go r, false) := by
      rcases hpc with hpc | hpc <;> simp [access, lineOf, hpc, hv, goTarget]
    have hX : PhiX (wake s p).go (ccUpd C p (.go r, false)) - PhiX s.go C ≤ 3 := by
      unfold PhiX
      rw [sum_sub_eq_of_ne r fun q hq => by simp [ccUpd, wake, hv, hq]]
      simp only [wake, hv, ccUpd, Function.update_self, ite_true, Bool.false_eq_true, ite_false]
      linarith [ind_nonneg (s.go r = true), ind_nonneg (C r (.go r) = false),
        ind_le_one True]
    unfold amortC
    rw [PhiC_eq, PhiC_eq, ha, e]
    have hc : (ccCost C p (.go r, false) : ℤ) = 1 := by simp [ccCost]
    linarith
  all_goals
    have ha : access s p ab = (.tail, false) := by
      rcases hpc with hpc | hpc <;> simp [access, lineOf, hpc, hv, goTarget]
    rw [amortC_of_nonGo ha (by simp) (by simp [e, wake, hv]), e]
    linarith

/-- **Lemma 5.3** (Appendix C), with the correct constants: in the CC model, the amortized cost
w.r.t. `ΦCC` of a step executing line `ℓ` is at most 0 for `ℓ ∈ {4, 5, 6}`, at most 1 for
`ℓ ∈ {1, 2, 3, 7, 9}`, at most 2 for `ℓ = 10` and at most 5 for `ℓ ∈ {8, 11}`.

The paper claims `αCC(8), αCC(11) ≤ 4` ("real cost one, potential increase of three units"),
overlooking that the write `*v_p ← true` to `go_q` also invalidates `go_q` in `q`'s cache, which
raises `1{notcached(q)}` by one more unit; 5 is attained (model check, `n = 2`). The lemma's
qualitative claim (a constant bound) is unaffected. -/
theorem lemma_5_3 {s : State n} (h : Inv s) (C : Cache n) (p : Fin n) (ab : Bool) :
    amortC C s p ab ≤ boundC (lineOf s p ab) := by
  have hnt : ∀ q, (Var.tail : Var n) ≠ .go q := by simp
  have hnn : ∀ (a : Node n) q, (Var.node a : Var n) ≠ .go q := by simp
  cases hpc : s.pc p with
  | l1 =>
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.mynode p)) (by simp [step, hpc])]
    simp only [lineOf, hpc, boundC]; linarith [dPhi_l1 h hpc ab]
  | l2 =>
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) hnt (by simp [step, hpc])]
    simp only [lineOf, hpc, boundC]; linarith [dPhi_l2 h hpc ab]
  | l3 =>
    have e : step s p ab = fasPred s p := by simp [step, hpc]
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, fasPred])]
    have := dPhi_fasPred h (p := p) (by simp [hpc, PC.act])
    simp only [lineOf, hpc, boundC, e]; linarith [ind_nonneg (s.pc p = .l6)]
  | l4 =>
    cases ab with
    | false =>
      have ha : access s p false = (.go p, true) := by simp [access, lineOf, hpc]
      have hg : (step s p false).go = s.go := by
        simp only [step, hpc, Bool.false_eq_true, ite_false]; split_ifs <;> rfl
      have hX : PhiX (step s p false).go (ccUpd C p (.go p, true)) - PhiX s.go C =
          -ind (C p (.go p) = false) := by
        rw [hg]; unfold PhiX
        rw [sum_sub_eq_of_ne p fun q hq => by simp [ccUpd, hq]]
        simp [ccUpd, ind]
      unfold amortC
      rw [PhiC_eq, PhiC_eq, ha]
      simp only [lineOf, hpc, boundC, Bool.false_eq_true, ite_false]
      have hc : (ccCost C p (.go p, true) : ℤ) = ind (C p (.go p) = false) := by
        simp only [ccCost, ind]; cases C p (.go p) <;> simp
      linarith [dPhi_l4 hpc]
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, line9])]
      simp only [lineOf, hpc, boundC, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l5 =>
    cases ab with
    | false =>
      have ha : access s p false = (.go p, false) := by simp [access, lineOf, hpc]
      have hg5 := h.loc.i12 p hpc
      have hX : PhiX (step s p false).go (ccUpd C p (.go p, false)) - PhiX s.go C ≤ -1 := by
        simp only [step, hpc, Bool.false_eq_true, ite_false]; unfold PhiX
        rw [sum_sub_eq_of_ne p fun q hq => by simp [ccUpd, hq]]
        simp [ccUpd, ind, hg5]; split_ifs <;> norm_num
      unfold amortC
      rw [PhiC_eq, PhiC_eq, ha]
      simp only [lineOf, hpc, boundC, Bool.false_eq_true, ite_false]
      have hc : (ccCost C p (.go p, false) : ℤ) = 1 := by simp [ccCost]
      linarith [dPhi_l5 h hpc]
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, line9])]
      simp only [lineOf, hpc, boundC, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l6 =>
    cases ab with
    | false =>
      have e : step s p false = fasPred s p := by simp [step, hpc]
      rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, fasPred])]
      have := dPhi_fasPred h (p := p) (by simp [hpc, PC.act])
      rw [ind_of hpc] at this
      simp only [lineOf, hpc, boundC, e, Bool.false_eq_true, ite_false]; linarith
    | true =>
      have e : step s p true = line9 s p := by simp [step, hpc]
      rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, line9])]
      simp only [lineOf, hpc, boundC, e, ite_true]
      linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l7 =>
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.mynode p)) (by simp [step, hpc])]
    simp only [lineOf, hpc, boundC]; linarith [dPhi_l7 h hpc ab]
  | l8 => exact amortC_wake (Or.inl hpc) |>.trans (by simp [lineOf, hpc, boundC])
  | l9 =>
    have e : step s p ab = line9 s p := by simp [step, hpc]
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.pred p)) (by simp [e, line9])]
    simp only [lineOf, hpc, boundC, e]
    linarith [dPhi_line9 h (p := p) (by simp [hpc, PC.act])]
  | l10 =>
    rw [amortC_of_nonGo (by simp [access, lineOf, hpc]) (hnn (s.mynode p)) (by simp [step, hpc])]
    simp only [lineOf, hpc, boundC]; linarith [dPhi_l10 h hpc ab]
  | l11 => exact amortC_wake (Or.inr hpc) |>.trans (by simp [lineOf, hpc, boundC])

end Podc.AbortableMutexAmortized
