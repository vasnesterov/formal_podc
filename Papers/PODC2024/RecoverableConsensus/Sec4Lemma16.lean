import Papers.PODC2024.RecoverableConsensus.Sec4Common
import Podc.Foundations.Data.Finset.SumUpdate

/-!
# Lemma 16 of Ovens (PODC'24): `T_{n,n'}` has recoverable consensus number `n'`

* Lower bound (`alg16_recConsensus`): one object `O` of type `T_{n,n'}`, initially `s`; a process
  with input `x` applies `opR`; on `s_{v,i}` it decides `v`, on `⊥` it decides `0`, on `s` it
  applies `op_x` and decides the returned bit. Invariant `Inv16` (valid under arbitrary
  individual crashes): `O = s` and nobody decided, or `O = s_{v,i}` with
  `i + #(processes about to apply op) ≤ n'`, `v` an input and every decided value equal to `v`;
  the letter of `O` never changes once set. In particular `opR` never returns `⊥`.
* Upper bound (`not_recSolvable`): valency argument w.r.t. `E*_z` with crash budget `z = n`
  (the paper uses `⌈n/2⌉` for `m = n' + 1` processes). After excluding registers and `opR`,
  `σ₀`, `σ₁` (`schedFrom`) are permutations of all `m` processes starting with a team-0 resp.
  team-1 process; afterwards the values of `O` have the same `idx > n'` (or are both `s⊥`).
  The process `last = p_{m-1}` is then crashed and run solo; the construction (`rounds`) is by
  induction on `n - idx` (outer) and on the length of `last`'s solo run to a decision (inner):
  steps on other objects are identical, `opR` breaks `O` in both runs (equal memory, same
  response ⇒ contradiction), `op_y` increases `idx` in both and `last` crashes again; if `last`
  decides before touching `O`, the decisions in the two runs contradict univalence
  (`contra_out`). The crash bookkeeping (`Good`, `inEs_steps_append`) uses that every crash of
  `last` happens after the steps of all smaller processes in `σ`.
-/

namespace Cslib.SharedMemory.Recoverable.Ovens.Sec4

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

set_option linter.unusedSectionVars false

/-! ## Crash budgets -/

/-- Steps of distinct processes, one of which is smaller than `last`, followed by events of
`last` with at most `z * m` crashes, are in `E*_z`. -/
lemma inEs_steps_append {z m : ℕ} (last : Fin m) (σ : List (Fin m)) {r₀ : Fin m} (hr₀ : r₀ ∈ σ)
    (hlt : r₀ < last) (ρ : List (Ev m)) (hρ : ∀ e ∈ ρ, e.proc = last)
    (hc : crashes last ρ ≤ z * m) : InEs z (σ.map Ev.step ++ ρ) := by
  intro M p'
  rw [List.take_append, crashes_append, stepsBelow_append]
  have h0 : crashes p' ((σ.map Ev.step).take M) = 0 :=
    crashes_eq_zero_of_crashFree ((crashFree_steps σ).take M) p'
  rw [h0, Nat.zero_add]
  have hle : crashes p' (ρ.take (M - (σ.map Ev.step).length)) ≤ crashes p' ρ :=
    (List.take_sublist _ _).count_le _
  by_cases hp' : p' = last
  · subst hp'
    by_cases hM : M ≤ (σ.map Ev.step).length
    · rw [show M - (σ.map Ev.step).length = 0 by omega, List.take_zero, crashes_nil]
      exact Nat.zero_le _
    · rw [List.take_of_length_le (show (σ.map Ev.step).length ≤ M by omega)]
      have hpos : 0 < stepsBelow p' (σ.map Ev.step) := by
        unfold stepsBelow
        rw [List.countP_pos_iff]
        exact ⟨.step r₀, List.mem_map_of_mem hr₀, by simp [Ev.isStepBelow, hlt]⟩
      have : z * m ≤ z * m * (stepsBelow p' (σ.map Ev.step) +
          stepsBelow p' (ρ.take (M - (σ.map Ev.step).length))) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
  · have : crashes p' ρ = 0 := by
      apply List.count_eq_zero.2
      intro h
      exact hp' (by simpa using hρ _ h)
    omega

/-! ## Lemma 16, upper bound -/

section Upper

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {n n' m : ℕ}
  {A : Alg m (withRW (ιS := ιS) R (Tnn n n'))} {z : ℕ} {C : Cfg A}

/-- Extensions of `α p` by `β` followed by any events of `last` with at most `c` crashes are
in `E*_z`. -/
def Good (α : List (Ev m)) (last r : Fin m) (β : List (Ev m)) (c : ℕ) : Prop :=
  ∀ ρ : List (Ev m), (∀ e ∈ ρ, e.proc = last) → crashes last ρ ≤ c →
    InEs z (α ++ [.step r] ++ β ++ ρ)

lemma Good.inEs {α : List (Ev m)} {last r : Fin m} {β : List (Ev m)} {c : ℕ}
    (h : Good (z := z) α last r β c) : InEs z (α ++ [.step r] ++ β) := by
  simpa using h [] (by simp) (by simp)

lemma Good.step {α : List (Ev m)} {last r : Fin m} {β : List (Ev m)} {c : ℕ}
    (h : Good (z := z) α last r β c) : Good (z := z) α last r (β ++ [.step last]) c := by
  intro ρ hρ hc
  have := h (.step last :: ρ) (by simpa using hρ) (by simpa using hc)
  simpa using this

lemma Good.stepCrash {α : List (Ev m)} {last r : Fin m} {β : List (Ev m)} {c : ℕ}
    (h : Good (z := z) α last r β (c + 1)) :
    Good (z := z) α last r (β ++ [.step last, .crash last]) c := by
  intro ρ hρ hc
  have := h (.step last :: .crash last :: ρ) (by simpa using hρ) (by simp; omega)
  simpa using this

/-- If `last` is in an output state after both `α p β₀` and `α q β₁`, where `p`, `q` are on
different teams, we get a contradiction. -/
lemma contra_out {α : List (Ev m)} {p q last : Fin m} (hp : Team z C α p false)
    (hq : Team z C α q true) {β₀ β₁ : List (Ev m)} (h₀ : InEs z (α ++ [.step p] ++ β₀))
    (h₁ : InEs z (α ++ [.step q] ++ β₁)) {w : Bool}
    (hw₀ : (run C (α ++ [.step p] ++ β₀)).Out last w)
    (hw₁ : (run C (α ++ [.step q] ++ β₁)).Out last w) : False := by
  have e₀ := (Univ.append hp h₀).2 [] (by simp) (by simpa using h₀) w (by simpa using Dec.of_out hw₀)
  have e₁ := (Univ.append hq h₁).2 [] (by simp) (by simpa using h₁) w (by simpa using Dec.of_out hw₁)
  rw [e₀] at e₁
  exact Bool.false_ne_true e₁

/-- The inductive construction in the proof of Lemma 16: two configurations reached after
`α p` resp. `α q` (different teams), indistinguishable to `last`, with the same values of all
objects except `O`, whose values have the same `idx > n'` (so that `opR` breaks `O` in both).
Running `last` solo (crashing it after each `op₀`/`op₁` on `O`) leads to a contradiction.
Outer induction: `n - idx` (number of remaining `op` operations before `O = s⊥`); inner
induction: number of solo steps of `last` until it outputs. -/
lemma rounds (hA : RecConsensus A) (hC : Reach A (fun _ => True) C) (hn : 0 < n)
    {α : List (Ev m)} {p q : Fin m} (hp : Team z C α p false) (hq : Team z C α q true)
    (last : Fin m) (j : ιS) :
    ∀ d K (β₀ β₁ : List (Ev m)) (c : ℕ),
      n - idx (n := n) ((run C (α ++ [.step p] ++ β₀)).mem (Sum.inr j)) = d →
      (∃ w, (run (run C (α ++ [.step p] ++ β₀)) (solo last K)).Out last w) →
      Good (z := z) α last p β₀ c → Good (z := z) α last q β₁ c →
      n - idx (n := n) ((run C (α ++ [.step p] ++ β₀)).mem (Sum.inr j)) ≤ c →
      (run C (α ++ [.step p] ++ β₀)).loc last = (run C (α ++ [.step q] ++ β₁)).loc last →
      (∀ i, i ≠ Sum.inr j →
        (run C (α ++ [.step p] ++ β₀)).mem i = (run C (α ++ [.step q] ++ β₁)).mem i) →
      idx (n := n) ((run C (α ++ [.step p] ++ β₀)).mem (Sum.inr j)) =
        idx (n := n) ((run C (α ++ [.step q] ++ β₁)).mem (Sum.inr j)) →
      n' < idx (n := n) ((run C (α ++ [.step p] ++ β₀)).mem (Sum.inr j)) → False := by
  have hAdm := admOK_true (n := m) z
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ihK =>
  intro β₀ β₁ c hd hK hg₀ hg₁ hc hloc hmem hidx hlt
  have e₀ : run C (α ++ [.step p] ++ (β₀ ++ [.step last])) =
      (run C (α ++ [.step p] ++ β₀)).stepP last := by
    rw [← List.append_assoc, run_concat]; rfl
  have e₁ : run C (α ++ [.step q] ++ (β₁ ++ [.step last])) =
      (run C (α ++ [.step q] ++ β₁)).stepP last := by
    rw [← List.append_assoc, run_concat]; rfl
  have e₀' : run C (α ++ [.step p] ++ (β₀ ++ [.step last, .crash last])) =
      ((run C (α ++ [.step p] ++ β₀)).stepP last).next (.crash last) := by
    rw [show β₀ ++ [.step last, .crash last] = β₀ ++ [.step last] ++ [.crash last] by simp,
      ← List.append_assoc, run_concat, ← List.append_assoc, run_concat]; rfl
  have e₁' : run C (α ++ [.step q] ++ (β₁ ++ [.step last, .crash last])) =
      ((run C (α ++ [.step q] ++ β₁)).stepP last).next (.crash last) := by
    rw [show β₁ ++ [.step last, .crash last] = β₁ ++ [.step last] ++ [.crash last] by simp,
      ← List.append_assoc, run_concat, ← List.append_assoc, run_concat]; rfl
  have hinp : (run C (α ++ [.step p] ++ β₀)).inp = (run C (α ++ [.step q] ++ β₁)).inp := by
    rw [run_inp, run_inp]
  generalize hD₀ : run C (α ++ [.step p] ++ β₀) = D₀ at *
  generalize hD₁ : run C (α ++ [.step q] ++ β₁) = D₁ at *
  have hcontra : ∀ γ₀ γ₁, InEs z (α ++ [.step p] ++ γ₀) → InEs z (α ++ [.step q] ++ γ₁) →
      (run C (α ++ [.step p] ++ γ₀)).mem = (run C (α ++ [.step q] ++ γ₁)).mem →
      (run C (α ++ [.step p] ++ γ₀)).loc last = (run C (α ++ [.step q] ++ γ₁)).loc last →
      False := by
    intro γ₀ γ₁ h₀ h₁ hm hl
    refine team_contra hA hAdm hC hp hq (r := last) h₀ h₁ ⟨hm, fun r hr => ?_⟩
    simp only [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨hl, by rw [run_inp, run_inp]⟩
  by_cases hI : n ≤ idx (n := n) (D₀.mem (Sum.inr j))
  · -- both values are `s⊥`
    have hb₀ := eq_bot_of_idx hn hI
    have hb₁ := eq_bot_of_idx hn (hidx ▸ hI)
    refine hcontra β₀ β₁ hg₀.inEs hg₁.inEs ?_ ?_
    · rw [hD₀, hD₁]
      funext i
      by_cases hi : i = Sum.inr j
      · subst hi; exact hb₀.trans hb₁.symm
      · exact hmem i hi
    · rw [hD₀, hD₁]; exact hloc
  have hIlt : idx (n := n) (D₀.mem (Sum.inr j)) < n := by omega
  rcases hact : A.act (D₀.loc last) with ⟨i, o, k⟩ | w
  swap
  · -- `last` has already decided in both configurations
    refine contra_out hp hq hg₀.inEs hg₁.inEs (last := last) (w := w) ?_ ?_
    · rw [hD₀]; exact hact
    · rw [hD₁, Cfg.Out, ← hloc]; exact hact
  have hact₁ : A.act (D₁.loc last) = .access i o k := by rw [← hloc]; exact hact
  by_cases hi : i = Sum.inr j
  swap
  · -- an operation on another object: same step in both configurations
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := by
      rcases K with _ | K'
      · obtain ⟨w, hw⟩ := hK
        rw [solo, List.replicate_zero, run_nil, Cfg.Out, hact] at hw
        cases hw
      · exact ⟨K', rfl⟩
    have hOi : Sum.inr j ≠ i := Ne.symm hi
    refine ihK K' (by omega) (β₀ ++ [.step last]) (β₁ ++ [.step last]) c ?_ ?_ hg₀.step hg₁.step
      ?_ ?_ ?_ ?_ ?_ <;> rw [e₀] <;> (try rw [e₁])
    · rw [stepP_mem_other D₀ hact hOi]; exact hd
    · obtain ⟨w, hw⟩ := hK
      exact ⟨w, by rw [solo, List.replicate_succ, run_cons] at hw; exact hw⟩
    · rw [stepP_mem_other D₀ hact hOi]; exact hc
    · rw [stepP_loc_self D₀ hact, stepP_loc_self D₁ hact₁, hmem i hi]
    · intro i' hi'
      by_cases hii : i' = i
      · subst hii
        rw [stepP_mem_self D₀ hact, stepP_mem_self D₁ hact₁, hmem i' hi']
      · rw [stepP_mem_other D₀ hact hii, stepP_mem_other D₁ hact₁ hii]; exact hmem i' hi'
    · rw [stepP_mem_other D₀ hact hOi, stepP_mem_other D₁ hact₁ hOi]; exact hidx
    · rw [stepP_mem_other D₀ hact hOi]; exact hlt
  subst hi
  have hlt₁ : n' < idx (n := n) (D₁.mem (Sum.inr j)) := hidx ▸ hlt
  cases o with
  | opR =>
    -- `opR` breaks `O` in both configurations, with the same response `⊥`
    have r₀ : (withRW R (Tnn n n') (Sum.inr j)).δ (D₀.mem (Sum.inr j)) TOp.opR =
        (TVal.bot, TResp.bot) := tδ_opR_of_lt hlt
    have r₁ : (withRW R (Tnn n n') (Sum.inr j)).δ (D₁.mem (Sum.inr j)) TOp.opR =
        (TVal.bot, TResp.bot) := tδ_opR_of_lt hlt₁
    refine hcontra (β₀ ++ [.step last]) (β₁ ++ [.step last]) hg₀.step.inEs hg₁.step.inEs ?_ ?_ <;>
      rw [e₀, e₁]
    · funext i
      by_cases hi : i = Sum.inr j
      · subst hi; rw [stepP_mem_self D₀ hact, stepP_mem_self D₁ hact₁, r₀, r₁]
      · rw [stepP_mem_other D₀ hact hi, stepP_mem_other D₁ hact₁ hi]; exact hmem i hi
    · rw [stepP_loc_self D₀ hact, stepP_loc_self D₁ hact₁, r₀, r₁]
  | op y =>
    -- `op_y` increases `idx` in both configurations; then `last` crashes
    have r₀ : idx (n := n) ((withRW R (Tnn n n') (Sum.inr j)).δ (D₀.mem (Sum.inr j)) (TOp.op y)).1 =
        min (idx (n := n) (D₀.mem (Sum.inr j)) + 1) n := idx_op _ y
    have r₁ : idx (n := n) ((withRW R (Tnn n n') (Sum.inr j)).δ (D₁.mem (Sum.inr j)) (TOp.op y)).1 =
        min (idx (n := n) (D₁.mem (Sum.inr j)) + 1) n := idx_op _ y
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨w, K', hK'⟩ := hA.exists_soloOut hAdm
      (hC.run_true (α ++ [.step p] ++ (β₀ ++ [.step last, .crash last]))) last
    refine ihd (n - (idx (n := n) (D₀.mem (Sum.inr j)) + 1)) (by omega) K'
      (β₀ ++ [.step last, .crash last]) (β₁ ++ [.step last, .crash last]) c' ?_ ⟨w, hK'⟩
      hg₀.stepCrash hg₁.stepCrash ?_ ?_ ?_ ?_ ?_ <;> rw [e₀'] <;> (try rw [e₁'])
    · rw [crash_mem, stepP_mem_self D₀ hact, r₀]; omega
    · rw [crash_mem, stepP_mem_self D₀ hact, r₀]; omega
    · rw [crash_loc_self, crash_loc_self, stepP_inp, stepP_inp, hinp]
    · intro i hi
      rw [crash_mem, crash_mem, stepP_mem_other D₀ hact hi, stepP_mem_other D₁ hact₁ hi]
      exact hmem i hi
    · rw [crash_mem, crash_mem, stepP_mem_self D₀ hact, stepP_mem_self D₁ hact₁, r₀, r₁, hidx]
    · rw [crash_mem, stepP_mem_self D₀ hact, r₀]; omega

end Upper

end Cslib.SharedMemory.Recoverable.Ovens.Sec4

namespace Cslib.SharedMemory.Recoverable.Ovens.Sec4

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-- A permutation of all processes starting with `r`. -/
def schedFrom {m : ℕ} (r : Fin m) : List (Fin m) := r :: (List.finRange m).erase r

lemma schedFrom_nodup {m : ℕ} (r : Fin m) : (schedFrom r).Nodup :=
  List.nodup_cons.2 ⟨(List.nodup_finRange m).not_mem_erase, (List.nodup_finRange m).erase r⟩

lemma mem_schedFrom {m : ℕ} (r r' : Fin m) : r' ∈ schedFrom r := by
  by_cases h : r' = r
  · simp [schedFrom, h]
  · simp [schedFrom, List.mem_erase_of_ne h]

lemma length_schedFrom {m : ℕ} (r : Fin m) : (schedFrom r).length = m := by
  simp [schedFrom, List.length_erase_of_mem (List.mem_finRange r)]
  have := r.isLt; omega

/-- **Lemma 16, upper bound**: recoverable wait-free consensus among `m > n'` processes cannot be
solved with objects of type `T_{n,n'}` and read/write objects. We use the crash budget `z = n`
(the paper uses `⌈n/2⌉` for `m = n' + 1`). -/
theorem not_recSolvable {n n' m : ℕ} (h1 : 1 ≤ n') (h2 : n' < n) (hm : n' < m) :
    ¬ RecSolvable (Tnn n n') m := by
  rintro ⟨ιR, ιS, _, _, R, hR, A, hA⟩
  have hm0 : 0 < m := by omega
  let x : Fin m → Bool := fun p => decide (p.val = 1)
  have hAdm := admOK_true (n := m) n
  have hC : Reach A (fun _ => True) (initCfg A x) := Reach.initial hAdm x
  have hb := biv_initial hA hAdm x ⟨⟨0, hm0⟩, by simp [x]⟩ ⟨⟨1, by omega⟩, by simp [x]⟩
  obtain ⟨α, hc⟩ := exists_crit hA hAdm hC hb
  obtain ⟨i, hpo⟩ := hc.poised hA hAdm hC hm0
  rcases i with jR | j
  · exact hc.not_forall_poised_of_rwLike hA hAdm hC hm0 (i := Sum.inl jR) (hR jR) hpo
  have hops := all_ops hA hAdm hC hm0 hc hpo
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA hAdm hC hm0
  let last : Fin m := ⟨m - 1, by omega⟩
  set D := run (initCfg A x) α with hD
  -- the configurations after `σ_r` (a permutation starting with `r`) and a crash of `last`
  have key : ∀ r, (run (initCfg A x) (α ++ [.step r] ++
        (((List.finRange m).erase r).map Ev.step ++ [.crash last]))).loc last =
        A.init last (x last) ∧
      (∀ i, i ≠ Sum.inr j → (run (initCfg A x) (α ++ [.step r] ++
        (((List.finRange m).erase r).map Ev.step ++ [.crash last]))).mem i = D.mem i) ∧
      idx (n := n) ((run (initCfg A x) (α ++ [.step r] ++
        (((List.finRange m).erase r).map Ev.step ++ [.crash last]))).mem (Sum.inr j)) =
        min (idx (n := n) (D.mem (Sum.inr j)) + m) n ∧
      Good (z := n) α last r (((List.finRange m).erase r).map Ev.step ++ [.crash last]) n := by
    intro r
    have e : α ++ [.step r] ++ (((List.finRange m).erase r).map Ev.step ++ [.crash last]) =
        α ++ (schedFrom r).map Ev.step ++ [.crash last] := by simp [schedFrom]
    obtain ⟨h1, -, h3⟩ := run_ops (n' := n') j (schedFrom r) D (schedFrom_nodup r)
      (fun r' _ => hops r')
    rw [e, run_concat, run_append, ← hD]
    refine ⟨by simp [hD, run_inp, initCfg], fun i hi => h1 i hi, by rw [crash_mem, h3, length_schedFrom], ?_⟩
    intro ρ hρ hcρ
    have e' : α ++ [.step r] ++ (((List.finRange m).erase r).map Ev.step ++ [.crash last]) ++ ρ =
        α ++ ((schedFrom r).map Ev.step ++ (.crash last :: ρ)) := by simp [schedFrom]
    rw [e']
    refine hc.1.append (inEs_steps_append last (schedFrom r) (r₀ := ⟨0, hm0⟩)
      (mem_schedFrom r _) (by rw [Fin.lt_def]; simp [last]; omega) _ ?_ ?_)
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact hρ e he
    · have : n * 2 ≤ n * m := Nat.mul_le_mul_left n (by omega)
      simp only [crashes_cons_crash, ite_true]
      omega
  obtain ⟨hp1, hp2, hp3, hp4⟩ := key p
  obtain ⟨hq1, hq2, hq3, hq4⟩ := key q
  obtain ⟨w, K, hK⟩ := hA.exists_soloOut hAdm (hC.run_true (α ++ [.step p] ++
    (((List.finRange m).erase p).map Ev.step ++ [.crash last]))) last
  refine rounds hA hC (by omega) hp hq last j _ K _ _ n rfl ⟨w, hK⟩ hp4 hq4 (by omega)
    (by rw [hp1, hq1]) (fun i hi => by rw [hp2 i hi, hq2 i hi]) (by rw [hp3, hq3]) ?_
  rw [hp3]
  omega

/-! ## Lemma 16, lower bound: the algorithm -/

/-- Local states of the recoverable algorithm: about to apply `opR`, about to apply `op_x`
(after `opR` returned `s`), or decided `b`. -/
inductive L16 where
  | init (x : Bool)
  | apply (x : Bool)
  | done (b : Bool)

/-- What to do after `opR` returns `r`. -/
def readK {n : ℕ} (x : Bool) : TResp n → L16
  | .val .s => .apply x
  | .val (.sv v _) => .done v
  | _ => .done false

/-- The recoverable consensus algorithm for `n'` processes of Section 4: a process with input `x`
applies `opR` to `O` (initially `s`); if it returns `s_{v,i}` it decides `v`, if it returns `⊥` it
decides `0`, and if it returns `s` it applies `op_x` and decides the returned bit. -/
def alg16 (n n' : ℕ) : Alg n' (T1 n n') where
  L := L16
  init _ x := .init x
  act
    | .init x => .access (Sum.inr ()) TOp.opR (readK (n := n) x)
    | .apply x => .access (Sum.inr ()) (TOp.op x) (fun r => L16.done (bitOf (n := n) r))
    | .done b => .out b
  mem₀ := mem0

section Alg16

variable {n n' : ℕ}

/-- The value of `O`. -/
abbrev O16 (D : Cfg (alg16 n n')) : TVal n := D.mem (Sum.inr ())

def L16.isApply : L16 → Bool
  | .apply _ => true
  | _ => false

/-- The processes about to apply `op₀`/`op₁`. -/
def applySet (D : Cfg (alg16 n n')) : Finset (Fin n') :=
  Finset.univ.filter (fun p => L16.isApply (D.loc p) = true)

/-- The letter of a value `s_{v,i}`. -/
def letter {n : ℕ} : TVal n → Option Bool
  | .sv v _ => some v
  | _ => none

/-- The invariant (for all executions, with crashes): either `O = s` and nobody has decided, or
`O = s_{v,i}` where `i` plus the number of processes about to apply `op` is at most `n'`, `v` is
an input, and all decided processes decided `v`. -/
structure Inv16 (x : Fin n' → Bool) (D : Cfg (alg16 n n')) : Prop where
  inp : D.inp = x
  loc : ∀ p, D.loc p = L16.init (x p) ∨ D.loc p = L16.apply (x p) ∨ ∃ b, D.loc p = L16.done b
  val : (O16 D = .s ∧ ∀ p b, D.loc p ≠ L16.done b) ∨
    (∃ v i, O16 D = .sv v i ∧ i.val + 1 + (applySet D).card ≤ n' ∧ (∃ q, x q = v) ∧
      ∀ p b, D.loc p = L16.done b → b = v)

lemma inv16_init (x : Fin n' → Bool) : Inv16 x (initCfg (alg16 n n') x) :=
  ⟨rfl, fun p => Or.inl rfl, Or.inl ⟨rfl, fun p b h => by cases h⟩⟩

lemma out16 {D : Cfg (alg16 n n')} {p : Fin n'} {v : Bool} (h : D.Out p v) :
    D.loc p = L16.done v := by
  unfold Cfg.Out at h
  revert h
  rcases D.loc p with x | x | b
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h; rfl

lemma card_applySet_le (D : Cfg (alg16 n n')) : (applySet D).card ≤ n' := by
  have := Finset.card_le_card (Finset.subset_univ (applySet D))
  simpa using this

/-- Changing the state of one process `r`. -/
lemma card_applySet_change {D E : Cfg (alg16 n n')} (r : Fin n')
    (h : ∀ p, p ≠ r → E.loc p = D.loc p) :
    (applySet E).card + (if L16.isApply (D.loc r) = true then 1 else 0) =
      (applySet D).card + (if L16.isApply (E.loc r) = true then 1 else 0) :=
  Fintype.card_filter_add_ite_eq_of_eq_off (p := fun l => L16.isApply (D.loc l) = true)
    (q := fun l => L16.isApply (E.loc l) = true) r fun x hx => by rw [h x hx]

lemma inv16_next (hn : n' < n) {x : Fin n' → Bool} {D : Cfg (alg16 n n')} (hI : Inv16 x D)
    (e : Ev n') : Inv16 x (D.next e) ∧
      ∀ v, letter (O16 D) = some v → letter (O16 (D.next e)) = some v := by
  rcases e with r | r
  · show Inv16 x (D.stepP r) ∧ ∀ v, letter (O16 D) = some v → letter (O16 (D.stepP r)) = some v
    have hEq : ∀ q, q ≠ r → (D.stepP r).loc q = D.loc q := fun q hq => stepP_loc_other D hq
    have hinp : (D.stepP r).inp = x := (stepP_inp D r).trans hI.inp
    have hlocE : ∀ (l : L16), (D.stepP r).loc r = l → (l = L16.apply (x r) ∨ ∃ b, l = L16.done b) →
        ∀ p, (D.stepP r).loc p = L16.init (x p) ∨ (D.stepP r).loc p = L16.apply (x p) ∨
          ∃ b, (D.stepP r).loc p = L16.done b := by
      intro l hl hl' p
      by_cases hpr : p = r
      · subst hpr
        rcases hl' with h | ⟨b, h⟩
        · right; left; rw [hl, h]
        · right; right; exact ⟨b, by rw [hl, h]⟩
      · rw [hEq p hpr]; exact hI.loc p
    rcases hI.loc r with hr | hr | ⟨b, hr⟩
    · -- `r` applies `opR`
      have hact : (alg16 n n').act (D.loc r) =
          .access (Sum.inr ()) TOp.opR (readK (n := n) (x r)) := by rw [hr]; rfl
      have hEr : (D.stepP r).loc r = readK (x r) (tδ n n' (O16 D) .opR).2 := stepP_loc_self D hact
      have hEm : O16 (D.stepP r) = (tδ n n' (O16 D) .opR).1 := stepP_mem_self D hact
      rcases hI.val with ⟨hs, hnd⟩ | ⟨v, i, hv, hle, hvx, hdone⟩
      · rw [hs] at hEr hEm
        change (D.stepP r).loc r = L16.apply (x r) at hEr
        change O16 (D.stepP r) = .s at hEm
        refine ⟨⟨hinp, hlocE _ hEr (Or.inl rfl), Or.inl ⟨hEm, fun p b hp => ?_⟩⟩, fun v hv' => ?_⟩
        · by_cases hpr : p = r
          · subst hpr; rw [hEr] at hp; cases hp
          · rw [hEq p hpr] at hp; exact hnd p b hp
        · rw [hs] at hv'; simp [letter] at hv'
      · have hi : i.val + 1 ≤ n' := by omega
        rw [hv, tδ_sv_opR v i hi] at hEr hEm
        change (D.stepP r).loc r = L16.done v at hEr
        have hc := card_applySet_change (D := D) (E := D.stepP r) r hEq
        rw [hr, hEr] at hc
        simp only [L16.isApply, Bool.false_eq_true, ite_false] at hc
        refine ⟨⟨hinp, hlocE _ hEr (Or.inr ⟨v, rfl⟩),
          Or.inr ⟨v, i, hEm, by omega, hvx, fun p b hp => ?_⟩⟩, fun w hw => ?_⟩
        · by_cases hpr : p = r
          · subst hpr; rw [hEr] at hp; cases hp; rfl
          · rw [hEq p hpr] at hp; exact hdone p b hp
        · rw [hEm]; rw [hv] at hw; exact hw
    · -- `r` applies `op_{x r}`
      have hact : (alg16 n n').act (D.loc r) =
          .access (Sum.inr ()) (TOp.op (x r)) (fun r => L16.done (bitOf (n := n) r)) := by
        rw [hr]; rfl
      have hEr : (D.stepP r).loc r = L16.done (bitOf (tδ n n' (O16 D) (.op (x r))).2) :=
        stepP_loc_self D hact
      have hEm : O16 (D.stepP r) = (tδ n n' (O16 D) (.op (x r))).1 := stepP_mem_self D hact
      have hc := card_applySet_change (D := D) (E := D.stepP r) r hEq
      rw [hr, hEr] at hc
      simp only [L16.isApply, Bool.false_eq_true, ite_false, ite_true] at hc
      have hcD := card_applySet_le D
      rcases hI.val with ⟨hs, hnd⟩ | ⟨v, i, hv, hle, hvx, hdone⟩
      · have h0 : 0 < n - 1 := by have := r.isLt; omega
        rw [hs, tδ_s_op (x r) h0] at hEr hEm
        change (D.stepP r).loc r = L16.done (x r) at hEr
        refine ⟨⟨hinp, hlocE _ hEr (Or.inr ⟨_, rfl⟩),
          Or.inr ⟨x r, ⟨0, h0⟩, hEm, by simp only; omega, ⟨r, rfl⟩, fun p b hp => ?_⟩⟩,
          fun w hw => ?_⟩
        · by_cases hpr : p = r
          · subst hpr; rw [hEr] at hp; cases hp; rfl
          · rw [hEq p hpr] at hp; exact absurd hp (hnd p b)
        · rw [hs] at hw; simp [letter] at hw
      · have hi1 : i.val + 1 < n - 1 := by omega
        rw [hv, tδ_sv_op v (x r) i hi1] at hEr hEm
        change (D.stepP r).loc r = L16.done v at hEr
        refine ⟨⟨hinp, hlocE _ hEr (Or.inr ⟨_, rfl⟩),
          Or.inr ⟨v, ⟨i.val + 1, hi1⟩, hEm, by simp only; omega, hvx, fun p b hp => ?_⟩⟩,
          fun w hw => ?_⟩
        · by_cases hpr : p = r
          · subst hpr; rw [hEr] at hp; cases hp; rfl
          · rw [hEq p hpr] at hp; exact hdone p b hp
        · rw [hEm]; rw [hv] at hw; exact hw
    · rw [stepP_of_out D (show D.Out r b by rw [Cfg.Out, hr]; rfl)]
      exact ⟨hI, fun _ h => h⟩
  · -- crash of `r`
    have hEr : (D.next (.crash r)).loc r = L16.init (x r) := by rw [crash_loc_self, hI.inp]; rfl
    have hEq : ∀ q, q ≠ r → (D.next (.crash r)).loc q = D.loc q :=
      fun q hq => next_loc_other D (.crash r) (by simpa using hq)
    have hEm : O16 (D.next (.crash r)) = O16 D := rfl
    have hc := card_applySet_change (D := D) (E := D.next (.crash r)) r hEq
    rw [hEr] at hc
    simp only [L16.isApply, Bool.false_eq_true, ite_false] at hc
    have hcle : (applySet (D.next (.crash r))).card ≤ (applySet D).card := by
      split_ifs at hc <;> omega
    have hloc : ∀ p, (D.next (.crash r)).loc p = L16.init (x p) ∨
        (D.next (.crash r)).loc p = L16.apply (x p) ∨ ∃ b, (D.next (.crash r)).loc p = L16.done b := by
      intro p
      by_cases hpr : p = r
      · subst hpr; left; exact hEr
      · rw [hEq p hpr]; exact hI.loc p
    have hdone : ∀ p b, (D.next (.crash r)).loc p = L16.done b → D.loc p = L16.done b := by
      intro p b hp
      by_cases hpr : p = r
      · subst hpr; rw [hEr] at hp; cases hp
      · rwa [hEq p hpr] at hp
    refine ⟨⟨by rw [next_inp]; exact hI.inp, hloc, ?_⟩, fun v hv => by rw [hEm]; exact hv⟩
    rcases hI.val with ⟨hs, hnd⟩ | ⟨v, i, hv, hle, hvx, hd⟩
    · exact Or.inl ⟨hEm.trans hs, fun p b hp => hnd p b (hdone p b hp)⟩
    · exact Or.inr ⟨v, i, hEm.trans hv, by omega, hvx, fun p b hp => hd p b (hdone p b hp)⟩

lemma inv16_run (hn : n' < n) {x : Fin n' → Bool} : ∀ (β : List (Ev n')) (D : Cfg (alg16 n n')),
    Inv16 x D → Inv16 x (run D β) ∧ ∀ v, letter (O16 D) = some v → letter (O16 (run D β)) = some v
  | [], _, h => ⟨h, fun _ h => h⟩
  | e :: β, D, h => by
    obtain ⟨h1, h2⟩ := inv16_next hn h e
    obtain ⟨h3, h4⟩ := inv16_run hn β _ h1
    exact ⟨h3, fun v hv => h4 v (h2 v hv)⟩

/-- A decided value is the letter of the value of `O`, and an input. -/
lemma letter_of_done {x : Fin n' → Bool} {D : Cfg (alg16 n n')} (hI : Inv16 x D) {p : Fin n'}
    {v : Bool} (h : D.loc p = L16.done v) : letter (O16 D) = some v ∧ ∃ q, x q = v := by
  rcases hI.val with ⟨-, hnd⟩ | ⟨w, i, hw, -, hwx, hd⟩
  · exact absurd h (hnd p v)
  · obtain rfl := hd p v h
    rw [hw]
    exact ⟨rfl, hwx⟩

lemma agree16_aux (hn : n' < n) {x : Fin n' → Bool} (γ : List (Ev n')) {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) {p q : Fin n'} {v w : Bool}
    (hv : (run (initCfg (alg16 n n') x) (γ.take k₁)).Out p v)
    (hw : (run (initCfg (alg16 n n') x) (γ.take k₂)).Out q w) : v = w := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [List.take_add, run_append] at hw
  have hI : ∀ β, Inv16 x (run (initCfg (alg16 n n') x) β) :=
    fun β => (inv16_run hn β _ (inv16_init x)).1
  have hl := (letter_of_done (hI (γ.take k₁)) (out16 hv)).1
  obtain ⟨hI', hlet⟩ := inv16_run hn ((γ.drop k₁).take d) _ (hI (γ.take k₁))
  have hl' := (letter_of_done hI' (out16 hw)).1
  rw [hlet v hl] at hl'
  exact Option.some.inj hl'

/-- Ranking for progress: at most two operations before deciding. -/
def rank16 : L16 → ℕ
  | .init _ => 2
  | .apply _ => 1
  | .done _ => 0

/-- The algorithm of Section 4 solves recoverable wait-free consensus among `n' < n`
processes. -/
theorem alg16_recConsensus (hn : n' < n) : RecConsensus (alg16 n n') := by
  refine ⟨fun x γ _ v w hv hw => ?_, fun x γ _ v hv => ?_, fun x e p N _ hinf hN => ?_⟩
  · obtain ⟨k₁, -, p, hp⟩ := hv
    obtain ⟨k₂, -, q, hq⟩ := hw
    rcases le_total k₁ k₂ with h | h
    · exact agree16_aux hn γ h hp hq
    · exact (agree16_aux hn γ h hq hp).symm
  · obtain ⟨k, -, p, hp⟩ := hv
    have hI := (inv16_run hn (γ.take k) _ (inv16_init (n := n) x)).1
    exact (letter_of_done hI (out16 hp)).2
  · refine prog_of_rank (A := alg16 n n') rank16 (fun l i o k r hl => ?_) _ e p N hinf hN
    cases l with
    | init x =>
      cases hl
      rcases r with b | (_ | _ | ⟨v, i⟩) | _ <;> simp [readK, rank16]
    | apply x => cases hl; simp [rank16]
    | done b => cases hl

end Alg16

end Cslib.SharedMemory.Recoverable.Ovens.Sec4

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Sec4

/-- **Lemma 16** of Ovens (PODC'24): `T_{n,n'}` has recoverable consensus number `n'`. -/
theorem lemma16 {n n' : ℕ} (h1 : 1 ≤ n') (h2 : n' < n) : RecConsensusNumber (Tnn n n') n' :=
  ⟨⟨Empty, Unit, inferInstance, inferInstance, noRW, fun e => e.elim, alg16 n n',
    alg16_recConsensus h2⟩, fun _ hm => not_recSolvable h1 h2 hm⟩

end Cslib.SharedMemory.Recoverable.Ovens
