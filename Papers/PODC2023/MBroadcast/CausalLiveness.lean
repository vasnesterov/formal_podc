import Papers.PODC2023.MBroadcast.CausalInv

/-!
# Algorithm 2: liveness (Theorem 1, Local termination and Global CS-termination)

Infinite executions (`Exec`): sequences of configurations and actions, starting from `initCfg`,
each configuration obtained from the previous one by a (successful) step. A process is *correct*
if it never crashes. *Weak fairness* (`Exec.Fair`): every reception or own-delivery action that is
enabled at all times from some point on is eventually taken. For receptions this is the
reliability of the channels (a message to a correct process whose causal predecessors have been
delivered is eventually delivered); for `own` it is the progress of a correct process whose
`wait` condition holds. *Resilience* (`Exec.Resilient`): at most `t` processes crash.

Main results:
* `Exec.eventually_received`: every network message to a correct destination is eventually
  received (strong induction on its id: its causal predecessors have smaller ids);
* `Exec.global_cs_termination`: if a correct process `p` invokes `mbroadcast(m)`, every correct
  process eventually mdelivers `m` from `p` (only the correctness of the receiver is needed for
  `q ≠ p`);
* `Exec.local_termination`: if a correct process invokes `mbroadcast(m)`, it eventually
  mdelivers `m` itself, i.e. returns (at most `t` crashes; no assumption `t < n/2` is needed).
-/

set_option linter.unusedSectionVars false

namespace Podc.MBroadcast.Causal

open Finset

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

/-- Actions subject to weak fairness: receptions and own deliveries (line 3). -/
def Action.IsLocal : Action P M → Prop
  | .recv _ _ => True
  | .own _ => True
  | _ => False

/-- An infinite execution of Algorithm 2 with parameter `t`. -/
structure Exec (t : ℕ) (P M : Type) [Fintype P] [DecidableEq P] [DecidableEq M] where
  cfg : ℕ → Cfg P M
  act : ℕ → Action P M
  start : cfg 0 = initCfg
  step : ∀ k, Causal.step t (cfg k) (act k) = some (cfg (k + 1))

namespace Exec

variable {t : ℕ} (E : Exec t P M)

/-- `p` never crashes in `E`. -/
def Correct (p : P) : Prop := ∀ k, p ∉ (E.cfg k).crashed

/-- Weak fairness: a local action enabled at all times from `T` on is taken at some time
`≥ T`. -/
def Fair : Prop :=
  ∀ a : Action P M, a.IsLocal → ∀ T : ℕ, (∀ k, T ≤ k → (Causal.step t (E.cfg k) a).isSome) →
    ∃ k, T ≤ k ∧ E.act k = a

/-- At most `t` processes crash. -/
def Resilient : Prop := ∀ k, (E.cfg k).crashed.card ≤ t

lemma reachable (k : ℕ) : Reachable t (E.cfg k) := by
  induction k with
  | zero => rw [E.start]; exact .init
  | succ k ih => exact .step _ ih (E.step k)

lemma log_prefix {k k' : ℕ} (h : k ≤ k') : ∃ l, (E.cfg k').log = (E.cfg k).log ++ l := by
  induction k', h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ k' _ ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l', hl'⟩ := step_log_prefix (E.step k')
    exact ⟨l ++ l', by rw [hl', hl, List.append_assoc]⟩

lemma getElem?_mono {k k' i : ℕ} {e : GEv P M} (h : k ≤ k') (he : (E.cfg k).log[i]? = some e) :
    (E.cfg k').log[i]? = some e := by
  obtain ⟨l, hl⟩ := E.log_prefix h
  rw [hl]; exact getElem?_append_of_some he

lemma mem_mono {k k' : ℕ} {e : GEv P M} (h : k ≤ k') (he : e ∈ (E.cfg k).log) :
    e ∈ (E.cfg k').log := by
  obtain ⟨l, hl⟩ := E.log_prefix h
  rw [hl]; exact List.mem_append_left _ he

lemma crashed_mono {k k' : ℕ} (h : k ≤ k') : (E.cfg k).crashed ⊆ (E.cfg k').crashed := by
  induction k', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ k' _ ih => exact ih.trans (step_crashed_mono (E.step k'))

end Exec

-- CSLib candidate
/-- Finitely many eventually-true monotone properties are eventually simultaneously true. -/
lemma exists_forall_of_mono {α : Type} (s : Finset α) (Q : α → ℕ → Prop)
    (hmono : ∀ a k k', k ≤ k' → Q a k → Q a k') (h : ∀ a ∈ s, ∃ k, Q a k) :
    ∃ K, ∀ a ∈ s, Q a K := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨K, hK⟩ := ih (fun b hb => h b (mem_insert_of_mem hb))
    obtain ⟨ka, hka⟩ := h a (mem_insert_self _ _)
    refine ⟨max K ka, fun b hb => ?_⟩
    rw [mem_insert] at hb
    rcases hb with rfl | hb
    · exact hmono _ _ _ (le_max_right _ _) hka
    · exact hmono _ _ _ (le_max_left _ _) (hK b hb)

omit [Fintype P] in
lemma rcv_mem_deliver (C : Cfg P M) (p : P) (x : ℕ) (r : Rec P M) :
    GEv.rcv p x ∈ (deliver C p x r).log := by
  unfold deliver
  split
  · split_ifs <;> simp
  · simp

lemma step_recv_of {t : ℕ} {C : Cfg P M} {p : P} {x : ℕ} {r : Rec P M}
    (hx : C.log[x]? = some (.snd r)) (hcr : p ∉ C.crashed) (hdst : p ∈ r.dst)
    (hnr : GEv.rcv p x ∉ C.log) (hcaus : CausalReady C.log p r) :
    step t C (.recv p x) = some (deliver C p x r) := by
  simp only [step, hx]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hcr, hdst, hnr, hcaus⟩)]

lemma step_own_isSome {t : ℕ} {C : Cfg P M} {p : P} {m : M} {A : Finset P}
    (hph : C.phase p = .wait m A) (hcr : p ∉ C.crashed) (hA : Fintype.card P - t - 1 ≤ A.card) :
    (step t C (.own p)).isSome := by
  simp only [step, hph]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hcr, hA⟩)]; rfl

namespace Exec

variable {t : ℕ} (E : Exec t P M)

/-- **Reliable causal delivery.** Every network message to a correct destination is eventually
received. -/
theorem eventually_received (hfair : E.Fair) :
    ∀ (x k : ℕ) (r : Rec P M) (q : P), (E.cfg k).log[x]? = some (.snd r) → q ∈ r.dst →
      E.Correct q → ∃ k', GEv.rcv q x ∈ (E.cfg k').log := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro k r q hx hq hcq
  have I := (E.reachable k).inv
  -- the causal predecessors of `x` with destination `q` are eventually received
  obtain ⟨K, hK⟩ := exists_forall_of_mono r.dep
    (fun y k' => needs (E.cfg k).log q y = true → GEv.rcv q y ∈ (E.cfg k').log)
    (fun y k1 k2 h12 h hn => E.mem_mono h12 (h hn))
    (fun y hy => by
      by_cases hn : needs (E.cfg k).log q y = true
      · obtain ⟨r', hr', hq'⟩ := needs_iff.1 hn
        obtain ⟨k', hk'⟩ := ih y (I.depLt x r hx y hy) k r' q hr' hq' hcq
        exact ⟨k', fun _ => hk'⟩
      · exact ⟨0, fun h => absurd h hn⟩)
  by_contra hnot
  push Not at hnot
  obtain ⟨k', hk', hact⟩ := hfair (.recv q x) trivial (max K k) (fun k' hk' => by
    have hx' := E.getElem?_mono (le_of_max_le_right hk') hx
    rw [step_recv_of hx' (hcq k') hq (hnot k') (fun y hy hn => ?_)]
    · rfl
    · have hyx := I.depLt x r hx y hy
      have hxl := lt_of_getElem?_eq_some hx
      obtain ⟨r', hr', hq'⟩ := needs_iff.1 hn
      have hn0 : needs (E.cfg k).log q y = true := by
        refine needs_iff.2 ⟨r', ?_, hq'⟩
        obtain ⟨l, hl⟩ := E.log_prefix (le_of_max_le_right hk')
        rw [hl] at hr'
        exact getElem?_old (by omega) hr'
      exact E.mem_mono (le_of_max_le_left hk') (hK y hy hn0))
  have hs := E.step k'
  rw [hact] at hs
  obtain ⟨r', -, -, -, -, -, hC'⟩ := step_recv hs
  exact hnot (k' + 1) (hC' ▸ rcv_mem_deliver _ _ _ _)

/-- After `invoke p m` at time `k`, `init(m)` of `p` is in the log at position
`|log_k| + 1`. -/
lemma invoke_init {p : P} {m : M} {k : ℕ} (hk : E.act k = .invoke p m) :
    (E.cfg (k + 1)).log[(E.cfg k).log.length + 1]? =
        some (.snd ⟨p, univ.erase p, .init m, (E.cfg k).past p⟩) ∧
      GEv.mb (.bc p m) ∈ (E.cfg (k + 1)).log := by
  have hs := E.step k
  rw [hk] at hs
  obtain ⟨-, -, -, hC'⟩ := step_invoke hs
  rw [hC']
  simp

/-- A correct process `q ≠ p` that receives `init(m)` of `p` mdelivers `m` from `p`. -/
lemma dl_of_rcv_init {k k1 : ℕ} {p q : P} {m : M} {x : ℕ} {D : Finset ℕ}
    (hx : (E.cfg k).log[x]? = some (.snd ⟨p, univ.erase p, .init m, D⟩))
    (hr : GEv.rcv q x ∈ (E.cfg k1).log) :
    ∃ z : ℕ, (E.cfg k1).log[z]? = some (.rcv q x) ∧
      (∃ r : Rec P M, (E.cfg k1).log[z + 1]? = some (.snd r) ∧ r.src = q ∧ r.dst = {p} ∧
        r.body = .ack m) ∧
      Ev.dl q p m ∈ (E.cfg k1).trace := by
  have I := (E.reachable k1).inv
  obtain ⟨z, hz⟩ := mem_iff_getElem?'.1 hr
  obtain ⟨r0, hr0, hxz, -⟩ := I.rcv z q x hz
  have hx' := E.getElem?_mono (le_max_left k k1) hx
  have hr0' := E.getElem?_mono (le_max_right k k1) hr0
  rw [hx'] at hr0'; cases hr0'
  obtain ⟨r1, h1, h2, h3, h4, h5⟩ := I.hdl z q x _ m hz hr0 rfl
  refine ⟨z, hz, ⟨r1, h1, h2, h3, h4⟩, ?_⟩
  unfold Cfg.trace
  rw [mem_filterMap_mbOf]; exact List.mem_of_getElem? h5

/-- **Global CS-termination** (Theorem 1). If a correct process `p` invokes `mbroadcast(m)`,
every correct process `q ≠ p` eventually mdelivers `m` from `p`. -/
theorem global_cs_termination_other (hfair : E.Fair) {p q : P} {m : M} {k0 : ℕ}
    (hk0 : E.act k0 = .invoke p m) (hqp : q ≠ p) (hq : E.Correct q) :
    ∃ k, Ev.dl q p m ∈ (E.cfg k).trace := by
  obtain ⟨hx, -⟩ := E.invoke_init hk0
  obtain ⟨k1, hk1⟩ := E.eventually_received hfair _ _ _ q hx (by simp [hqp]) hq
  obtain ⟨-, -, -, h⟩ := E.dl_of_rcv_init hx hk1
  exact ⟨k1, h⟩

/-- At most `t` processes are faulty, hence at least `n - t - 1` correct processes differ from
`p`. -/
lemma card_correct_ne (hres : E.Resilient) [DecidablePred E.Correct] (p : P) :
    Fintype.card P - t - 1 ≤ (univ.filter (fun c => c ≠ p ∧ E.Correct c)).card := by
  classical
  set F := univ.filter (fun c => ¬ E.Correct c)
  obtain ⟨K, hK⟩ := exists_forall_of_mono F (fun c k => c ∈ (E.cfg k).crashed)
    (fun c k k' h hc => E.crashed_mono h hc)
    (fun c hc => by
      simp only [F, mem_filter, mem_univ, true_and, Correct, not_forall, not_not] at hc
      exact hc)
  have hF : F.card ≤ t := (card_le_card (fun c hc => hK c hc)).trans (hres K)
  have hU : (univ : Finset P) ⊆ insert p (univ.filter (fun c => c ≠ p ∧ E.Correct c) ∪ F) := by
    intro c _
    by_cases hcp : c = p
    · simp [hcp]
    · by_cases hc : E.Correct c
      · simp [hcp, hc]
      · simp [F, hc]
  have := card_le_card hU
  have h2 := card_insert_le p (univ.filter (fun c => c ≠ p ∧ E.Correct c) ∪ F)
  have h3 := card_union_le (univ.filter (fun c => c ≠ p ∧ E.Correct c)) F
  rw [card_univ] at this
  omega

/-- **Local termination** (Theorem 1). If a correct process `p` invokes `mbroadcast(m)`, it
eventually mdelivers `m` itself, i.e. returns from its invocation. -/
theorem local_termination (hfair : E.Fair) (hres : E.Resilient) {p : P} {m : M} {k0 : ℕ}
    (hk0 : E.act k0 = .invoke p m) (hp : E.Correct p) :
    ∃ k, Ev.dl p p m ∈ (E.cfg k).trace := by
  classical
  obtain ⟨hx, hbc⟩ := E.invoke_init hk0
  set x := (E.cfg k0).log.length + 1
  set Cs := univ.filter (fun c => c ≠ p ∧ E.Correct c)
  by_contra hnot
  push Not at hnot
  have hnot' : ∀ k, GEv.mb (.dl p p m) ∉ (E.cfg k).log := fun k h =>
    hnot k (by unfold Cfg.trace; rw [mem_filterMap_mbOf]; exact h)
  -- every correct `c ≠ p` acknowledges `m`, and `p` eventually receives the acknowledgement
  obtain ⟨K, hK⟩ := exists_forall_of_mono Cs
    (fun c k => ∃ (w y : ℕ) (r : Rec P M), (E.cfg k).log[w]? = some (.rcv p y) ∧
      (E.cfg k).log[y]? = some (.snd r) ∧ r.src = c ∧ r.body = .ack m)
    (fun c k k' h ⟨w, y, r, h1, h2, h3, h4⟩ =>
      ⟨w, y, r, E.getElem?_mono h h1, E.getElem?_mono h h2, h3, h4⟩)
    (fun c hc => by
      simp only [Cs, mem_filter, mem_univ, true_and] at hc
      obtain ⟨k1, hk1⟩ := E.eventually_received hfair _ _ _ c hx (by simp [hc.1]) hc.2
      obtain ⟨z, -, ⟨r, hr, hsrc, hdst, hb⟩, -⟩ := E.dl_of_rcv_init hx hk1
      obtain ⟨k2, hk2⟩ := E.eventually_received hfair _ _ _ p hr (by simp [hdst]) hp
      obtain ⟨w, hw⟩ := mem_iff_getElem?'.1 hk2
      exact ⟨max k1 k2, w, z + 1, r, E.getElem?_mono (le_max_right _ _) hw,
        E.getElem?_mono (le_max_left _ _) hr, hsrc, hb⟩)
  -- from `max K (k0 + 1)` on, `p` waits for acks of `m` and has enough of them
  have hwait : ∀ k, k0 + 1 ≤ k → ∃ A, (E.cfg k).phase p = .wait m A := by
    intro k hk
    rcases (E.reachable k).inv.live p m (E.mem_mono hk hbc) with h | h
    · exact h
    · exact absurd h (hnot' k)
  have hcard := E.card_correct_ne hres p
  obtain ⟨k, hkT, hact⟩ := hfair (.own p) trivial (max K (k0 + 1)) (fun k hk => by
    obtain ⟨A, hA⟩ := hwait k (le_of_max_le_right hk)
    refine step_own_isSome hA (hp k) (hcard.trans (card_le_card fun c hc => ?_))
    obtain ⟨w, y, r, h1, h2, h3, h4⟩ := hK c hc
    have I := (E.reachable k).inv
    exact h3 ▸ I.ackIn p m A hA w y r (E.getElem?_mono (le_of_max_le_left hk) h1)
      (E.getElem?_mono (le_of_max_le_left hk) h2) h4)
  have hs := E.step k
  rw [hact] at hs
  obtain ⟨m', A', hph, -, -, hC'⟩ := step_own hs
  obtain ⟨A, hA⟩ := hwait k (le_of_max_le_right hkT)
  rw [hA] at hph; cases hph
  apply hnot' (k + 1)
  rw [hC']; simp

/-- **Global CS-termination** (Theorem 1). If a correct process `p` invokes `mbroadcast(m)`,
every correct process eventually mdelivers `m` from `p`. -/
theorem global_cs_termination (hfair : E.Fair) (hres : E.Resilient) {p q : P} {m : M}
    {k0 : ℕ} (hk0 : E.act k0 = .invoke p m) (hp : E.Correct p) (hq : E.Correct q) :
    ∃ k, Ev.dl q p m ∈ (E.cfg k).trace := by
  by_cases hqp : q = p
  · subst hqp; exact E.local_termination hfair hres hk0 hp
  · exact E.global_cs_termination_other hfair hk0 hqp hq

end Exec

end Podc.MBroadcast.Causal
