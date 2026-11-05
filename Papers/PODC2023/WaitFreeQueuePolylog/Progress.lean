import Papers.PODC2023.WaitFreeQueuePolylog.Linearizable

/-!
# Corollary 23: wait-freedom, with an explicit bound on the number of steps

A potential `μ` on local states (the number of steps an operation may still take) strictly
decreases at every step of the process. An operation therefore takes at most
`μ(app0) ≤ 36·H + 8` steps of our model (`steps_le`), where `H` is the height of the tree: at most
`34` per level for the double refresh (`17` per `Refresh`), `6` for `Append`, and `2H + 2` for
`IndexDequeue`, `FindResponse` and `GetEnqueue`. Each step of our model is one shared-memory
access, except that the searches of lines 91 and 114 are single steps (see `Complexity.lean`
for their lengths).
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- Steps still needed after `Propagate` reached the root. -/
def tailCost (H : ℕ) : FifoOp V → ℕ
  | .enq _ => 0
  | .deq => 2 * H + 2

/-- Potential inside the `k`-th `Refresh(v)` with `pos` steps of that refresh left. -/
def refPos (H : ℕ) (o : FifoOp V) (v k pos : ℕ) : ℕ :=
  tailCost H o + 34 * Nat.log 2 v + (if k = 1 then 17 else 0) + pos

/-- Potential inside `Advance` (`s` = steps left in it). -/
def ctxPos (H : ℕ) (o : FifoOp V) : Ctx → ℕ → ℕ
  | .app, s => tailCost H o + 34 * H + s
  | .ref v k _ d, s => refPos H o v k (if d = 0 then 11 + s else 6 + s)
  | .own v k _ _, s => refPos H o v k s

/-- The potential: an upper bound on the number of remaining steps of the current operation. -/
def mu (H : ℕ) (l : Loc V) : ℕ :=
  match l.pc with
  | .idle => 0
  | .done _ => 0
  | .app0 => tailCost H l.cur + 34 * H + 6
  | .app1 _ => tailCost H l.cur + 34 * H + 5
  | .app2 _ _ => tailCost H l.cur + 34 * H + 4
  | .app3 _ => 0
  | .adv0 c _ _ => ctxPos H l.cur c 3
  | .adv1 c _ _ _ => ctxPos H l.cur c 2
  | .adv2 c _ _ => ctxPos H l.cur c 1
  | .r25 v k => refPos H l.cur v k 17
  | .r27 v k _ d => refPos H l.cur v k (if d = 0 then 16 else 11)
  | .r28 v k _ d _ => refPos H l.cur v k (if d = 0 then 15 else 10)
  | .c43 v k _ => refPos H l.cur v k 6
  | .c44 v k _ _ => refPos H l.cur v k 5
  | .r35 v k _ _ => refPos H l.cur v k 4
  | .idx v _ _ => H + 2 + Nat.log 2 v
  | .fr _ _ => H + 2
  | .ge v _ _ => H + 1 - Nat.log 2 v

lemma log_leaf {H : ℕ} (p : Fin np) (hnp : np ≤ 2 ^ H) : Nat.log 2 (2 ^ H + p.val) = H := by
  have h1 : 2 ^ H ≤ 2 ^ H + p.val := by omega
  have h2 : 2 ^ H + p.val < 2 ^ (H + 1) := by have := p.isLt; rw [pow_succ]; omega
  exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

lemma log_half {v : ℕ} (hv : 2 ≤ v) : Nat.log 2 (v / 2) + 1 = Nat.log 2 v := by
  rw [Nat.log_div_base]; have : 1 ≤ Nat.log 2 v := Nat.le_log_of_pow_le (by norm_num) (by simpa)
  omega

/-- After a refresh ends (lines 17–22), the potential has dropped below that of the last step
of the refresh. -/
lemma mu_refDone (hnp : np ≤ 2 ^ H) (hH : 1 ≤ H) {p : Fin np} {l : Loc V} {v k : ℕ}
    {res : Bool} (hv1 : 1 ≤ v) (hv : v < 2 ^ H) (hk : k = 1 ∨ k = 2) :
    mu H ⟨refDone (2 ^ H + p.val) l v k res, l.cur, l.lh⟩ < refPos H l.cur v k 1 := by
  unfold refDone
  split_ifs with h1 h2
  · simp only [mu, refPos, h1.1]; simp
  · subst h2
    simp only [afterProp]
    cases hc : l.cur with
    | enq x => simp [mu, refPos, tailCost]
    | deq =>
      have hL : 2 ^ H + p.val ≠ 1 := by
        have : 2 ^ 1 ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH; omega
      simp only [hL, if_false, mu, refPos, tailCost, log_leaf p hnp]; omega
  · have := log_half (v := v) (by omega)
    simp only [mu, refPos]; split_ifs <;> omega

end Podc.WaitFreeQueuePolylog

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

lemma getEnqStep_fst (M : Mem V) (v b i : ℕ) :
    (getEnqStep M v b i).1 = 2 * v ∨ (getEnqStep M v b i).1 = 2 * v + 1 := by
  unfold getEnqStep; simp only; split_ifs <;> simp

lemma log_child {v d : ℕ} (hv : 1 ≤ v) (hd : d < 2) : Nat.log 2 (2 * v + d) = Nat.log 2 v + 1 :=
  log_two_mul_add hv hd

/-- **The potential decreases at every step of a process.** -/
theorem mu_step (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {os : List (FifoOp V)} {rs : List (Option V)}
    {pend : Option (FifoOp V)} {M : Mem V} {G : Ghost np} {p : Fin np} {l : Loc V}
    (hS : Shape H np M) (hP : PInv H os rs M G p pend l)
    (hact : ∃ i o k, act H Variant.fixed p.val l = .access i o k) :
    mu H (stepLoc H p l M).2 < mu H l := by
  have hL : 2 ^ H + p.val ≠ 1 := by
    have : 2 ^ 1 ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH; omega
  obtain ⟨pc, cur, lh⟩ := l
  obtain ⟨-, hpc⟩ := hP
  cases pc with
  | idle => obtain ⟨_, _, _, h⟩ := hact; cases h
  | done r => obtain ⟨_, _, _, h⟩ := hact; cases h
  | app0 => simp [stepLoc, act, memδ, mu]
  | app1 h =>
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hpc
    have hb : M.blk (2 ^ H + p.val) (h - 1) = some (M.bk (2 ^ H + p.val) (h - 1)) := by
      have : h - 1 ≤ cnt M (leafOf H p) := by omega
      obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 (hS.blk_isSome this)
      simp only [leafOf] at hB; simp [Mem.bk, hB]
    simp [stepLoc, act, memδ, mu, hb]
  | app2 h B => simp [stepLoc, act, memδ, mu, Variant.fixed, enterAdv, hL, ctxPos]
  | app3 h => exact hpc.elim
  | adv0 c w hw => cases c <;> simp [stepLoc, act, memδ, mu, ctxPos, refPos] <;> split_ifs <;> omega
  | adv1 c w hw hp =>
    cases c <;> simp [stepLoc, act, memδ, mu, ctxPos, refPos] <;> split_ifs <;> omega
  | adv2 c w hw =>
    obtain ⟨-, -, hc⟩ := hpc
    show mu H ⟨afterAdv (2 ^ H + p.val) ⟨.adv2 c w hw, cur, lh⟩ c, cur, lh⟩ < _
    cases c with
    | app =>
      have hlog := log_half (v := 2 ^ H + p.val) (by omega)
      rw [log_leaf p hnp] at hlog
      simp only [afterAdv, mu, refPos, ctxPos, ite_true]; omega
    | ref v k h d =>
      obtain ⟨-, -, hd, -⟩ := hc
      simp only [afterAdv]
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp [mu, refPos, ctxPos] <;> omega
    | own v k h res =>
      obtain ⟨⟨r1, r2, r3, -⟩, -⟩ := hc
      have := mu_refDone (p := p) (l := ⟨.adv2 (.own v k h res) w hw, cur, lh⟩) (res := res)
        hnp hH r1 r2 r3
      simp only [afterAdv, mu, ctxPos]; exact this
  | r25 v k => simp [stepLoc, act, memδ, mu, refPos]
  | r27 v k h d => simp [stepLoc, act, memδ, mu, refPos]; split_ifs <;> omega
  | r28 v k h d ch =>
    obtain ⟨⟨r1, -⟩, -, hd, -⟩ := hpc
    simp only [stepLoc, act, memδ]
    by_cases hb : (M.blk (2 * v + d) ch).isSome
    · rw [hb]
      simp only [enterAdv, show 2 * v + d ≠ 1 by omega, if_false, mu, ctxPos, refPos]
      split_ifs <;> omega
    · simp only [Bool.not_eq_true] at hb
      rw [hb]
      simp only [afterAdv]
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp [mu, refPos] <;> omega
  | c43 v k h => simp [stepLoc, act, memδ, mu, refPos]
  | c44 v k h el =>
    obtain ⟨⟨r1, r2, r3, -⟩, -⟩ := hpc
    have := mu_refDone (p := p) (l := ⟨.c44 v k h el, cur, lh⟩) (res := true) hnp hH r1 r2 r3
    simp only [stepLoc, act, memδ]
    cases hz : createBlock M v h el with
    | some B => simp only [mu, refPos]; omega
    | none =>
      simp only [mu, refPos] at this ⊢
      exact this.trans_le (by omega)
  | r35 v k h B =>
    simp only [stepLoc, act, memδ]
    by_cases hn : (M.blk v h).isNone
    · simp only [hn, if_true, enterAdv]
      split_ifs <;> simp only [mu, ctxPos, refPos] <;> omega
    · simp only [hn, if_false, Bool.false_eq_true, enterAdv]
      split_ifs <;> simp only [mu, ctxPos, refPos] <;> omega
  | idx v b i =>
    obtain ⟨-, -, -, hv2, -⟩ := hpc
    have := log_half hv2
    simp only [stepLoc, act, memδ]
    split_ifs <;> simp only [mu] <;> omega
  | fr b i =>
    simp only [stepLoc, act, memδ]
    cases hf : findResp M b i with
    | none => simp [mu]
    | some r => obtain ⟨be, ie⟩ := r; simp [mu]
  | ge v b i =>
    obtain ⟨-, -, hv1, hvT, -⟩ := hpc
    simp only [stepLoc, act, memδ, isLeaf]
    by_cases hleaf : 2 ^ H ≤ v
    · have : Nat.log 2 v < H + 1 := Nat.log_lt_of_lt_pow (by omega) hvT
      simp only [hleaf, decide_true, ite_true, mu]; omega
    · have h1 : Nat.log 2 v < H := Nat.log_lt_of_lt_pow (by omega) (by omega)
      simp only [hleaf, decide_false, Bool.false_eq_true, ite_false, mu]
      rcases getEnqStep_fst M v b i with h | h <;> rw [h]
      · have := log_child (d := 0) hv1 (by norm_num); simp at this; rw [this]; omega
      · rw [log_child hv1 (by norm_num)]; omega

end Podc.WaitFreeQueuePolylog

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- The potential of a process does not increase at any step taken while it is pending, and
decreases at its own internal steps. -/
theorem mu_cfg (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) (p : Fin np)
    {C C' : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)}
    {ℓ : Label (Fin np) (queueObj V)} (hC : (Q H np V).Reachable C) (hp : C.pend p ≠ none)
    (hs : (Q H np V).step C ℓ = some C') :
    mu H (C'.loc p) ≤ mu H (C.loc p) ∧ (ℓ = .tau p → mu H (C'.loc p) < mu H (C.loc p)) := by
  obtain ⟨α, hα⟩ := hC
  obtain ⟨G, hI⟩ := exists_inv hH hnp hα
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 hp
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, l', hact, hloc⟩ := Impl.step_ret hs
      have hact' : act H Variant.fixed q.val (C.loc q) = .ret r l' := hact
      refine ⟨?_, fun h => by cases h⟩
      rw [hloc, Function.update_self]
      rcases act_ret_cases hact' with hidle | ⟨-, rfl⟩
      · have h2 : act H Variant.fixed q.val (C.loc q) = .ret none (C.loc q) := by
          generalize C.loc q = l at hidle ⊢
          obtain ⟨pc, cur, lh⟩ := l
          simp only at hidle; subst hidle; rfl
        rw [h2] at hact'; injection hact' with _ h3; rw [← h3]
      · simp [mu]
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
      have hact' : act H Variant.fixed q.val (C.loc q) = .access i o k := hact
      have hL' : C'.loc q = (stepLoc H q (C.loc q) (C.mem ())).2 := by
        rw [hloc]; simp only [Function.update_self, stepLoc, hact']; rfl
      have := mu_step hH hnp hI.shape (hI.proc q) ⟨i, o, k, hact'⟩
      rw [hL']
      exact ⟨this.le, fun _ => this⟩
  · rw [(Impl.step_other hs hq).1]
    exact ⟨le_rfl, fun h => by subst h; exact (hq rfl).elim⟩

/-- **Corollary 23.** The (repaired) queue implementation is wait-free. -/
theorem corollary_23 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) :
    (queueImpl H Variant.fixed np : Impl (queueObj V) (fun _ : Unit => memObj V) (Fin np)
      (Loc V)).WaitFree :=
  Impl.waitFree_of_cfgPotential (Q H np V) (Q H np V).Reachable ⟨[], rfl⟩
    (fun _ _ _ hC hs => hC.step hs) (fun p C => mu H (C.loc p))
    (fun p _ _ _ hC hp hs => mu_cfg hH hnp p hC hp hs)

/-- **Step bound (Theorem 22, first part, in steps of our model).** After an operation is
invoked, its process takes at most `36·H + 8` steps before it returns; every step is one
shared-memory access except the single steps of `FindResponse` and `GetEnqueue`, which include
the searches of lines 91 and 114. For `H = ⌈log₂ p⌉` this is `O(log p)` steps. -/
theorem steps_le (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {α γ : List (Label (Fin np) (queueObj V))}
    {p : Fin np} {o : FifoOp V} (hv : (Q H np V).Valid (α ++ .inv p o :: γ))
    (hret : ∀ r, .ret p r ∉ γ) : γ.countP (Label.isTauOf p) ≤ 36 * H + 8 := by
  obtain ⟨C', h⟩ := hv
  rw [Impl.run, Impl.runFrom_append] at h
  cases hα : (Q H np V).runFrom (Q H np V).initCfg α with
  | none => simp [hα] at h
  | some C₀ =>
    simp only [hα, Option.bind_some, Impl.runFrom_cons] at h
    cases hs : (Q H np V).step C₀ (.inv p o) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv hs
      have hR1 : (Q H np V).Reachable C₁ := ⟨α ++ [.inv p o], by
        rw [Impl.run_concat, Impl.run, hα]; exact hs⟩
      have key := (Q H np V).countP_isTauOf_add_le_of_cfgPotential p (fun C => mu H (C.loc p))
        γ C₁ C' h (by simp [hpend]) hret (fun β ℓ D D' _ hD hs' hDp _ => by
          refine mu_cfg hH hnp p ⟨α ++ .inv p o :: β, ?_⟩ hDp hs'
          rw [Impl.run, Impl.runFrom_append, hα]
          simp only [Option.bind_some, Impl.runFrom_cons, hs]; exact hD)
      have h0 : mu H (C₁.loc p) ≤ 36 * H + 8 := by
        rw [hloc, Function.update_self]
        cases o <;> simp [Q, queueImpl, mu, tailCost] <;> omega
      omega

end Podc.WaitFreeQueuePolylog
