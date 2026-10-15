import Papers.PODC2016.TwoBitRegisters.InvHist
import Mathlib

/-!
# Message complexity (Theorem 2 of the paper)

Theorem 2: "a read operation requires `O(n)` messages, and a write operation requires `O(n²)`
messages". Messages are counted with the ghost log `C.sent` of all messages ever sent. We prove
the amortized statements (a write by itself may cause fewer messages, and catch-up messages of
line 16 may be sent long after the write returned):

* `write_messages`: at most `n (n - 1)` `WRITE` messages per invoked write;
* `read_messages`: at most `2 (n - 1)` `READ`/`PROCEED` messages per invoked read.

Per channel: process `i` sends at most `w_sync_i[i]` `WRITE` messages to `j` (each value at most
once), exactly `r_sync_i[i]` (= number of reads of `i`) `READ` messages, and `j` answers each
of them with at most one `PROCEED`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- `WRITE` messages. -/
def Msg.isWrite : Msg V → Bool
  | .write _ _ => true
  | _ => false

/-- Number of `WRITE` messages ever sent by `i` to `j`. -/
def wSent (C : Cfg P V) (i j : P) : ℕ :=
  C.sent.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true)

/-- Invariant on the message log. -/
structure InvM (w : P) {v₀ : V} (C : Cfg P V) (h : List (Label P (register V v₀))) : Prop where
  wsent : ∀ i j, wSent C i j = if i = j then 0 else sent C i j
  rsent : ∀ i j, C.sent.count (i, j, .read) = if i = j then 0 else R C i i
  psent : ∀ i j, C.sent.count (j, i, .proceed) + tk C j i + cR C i j ≤ C.sent.count (i, j, .read)
  rs_w : R C w w = 0
  rs_self : ∀ i, i ≠ w → R C i i = (opsOf h i).length

@[simp] lemma Config.apply_sent {C : Cfg P V} {p : P} {l : Loc P V} {out : Multiset (P × Msg V)}
    {net : Multiset (P × P × Msg V)} : (C.apply p l out net).sent = C.sent + outMsgs p out := rfl

lemma wSent_add (C : Cfg P V) (s : Multiset (P × P × Msg V)) (i j : P) :
    (C.sent + s).countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) =
      wSent C i j + s.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) := by
  rw [Multiset.countP_add]; rfl

lemma countP_outMsgs_sendTo_write {c : P → Prop} [DecidablePred c] {b : Bool} {v : V} {p : P}
    (i j : P) :
    (outMsgs p (sendTo c (Msg.write b v))).countP
        (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) =
      if i = p ∧ c j then 1 else 0 := by
  simp only [outMsgs, sendTo, Multiset.map_map, Function.comp_def, Multiset.countP_map]
  rw [← Finset.filter_val, Finset.card_val, Finset.filter_filter]
  by_cases h : i = p ∧ c j
  · rw [if_pos h]
    obtain ⟨rfl, hc⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Msg.isWrite,
      and_true]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hc, rfl⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ℓ hℓ hh
    exact h ⟨hh.2.1.symm, hh.2.2.1 ▸ hh.1⟩

lemma countP_outMsgs_nonwrite {p : P} {out : Multiset (P × Msg V)}
    (hout : ∀ x ∈ out, x.2.isWrite = false) (i j : P) :
    (outMsgs p out).countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) = 0 := by
  rw [Multiset.countP_eq_zero]
  intro x hx
  simp only [outMsgs, Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simp [hout y hy]

lemma countP_outMsgs_single {p q : P} {m : Msg V} (i j : P) :
    (outMsgs p ({(q, m)} : Multiset (P × Msg V))).countP
        (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) =
      if p = i ∧ q = j ∧ m.isWrite = true then 1 else 0 := by
  rw [show outMsgs p ({(q, m)} : Multiset (P × Msg V)) = {(p, q, m)} from rfl, countP_singleton']

/-- Steps that send nothing. -/
lemma InvM.of_nosend {w : P} {v₀ : V} {C C' : Cfg P V} {h h' : List (Label P (register V v₀))}
    (hM : InvM w C h) (hsent : C'.sent = C.sent) (hR : ∀ i, R C' i i = R C i i)
    (hops : ∀ i, i ≠ w → opsOf h' i = opsOf h i)
    (hpipe : ∀ i j, tk C' j i + cR C' i j ≤ tk C j i + cR C i j)
    (hS : ∀ i j, i ≠ j → sent C' i j = sent C i j) : InvM w C' h' where
  wsent i j := by
    have := hM.wsent i j
    simp only [wSent, hsent] at this ⊢
    split_ifs at this ⊢ with hij
    · exact this
    · rw [hS i j hij]; exact this
  rsent i j := by rw [hsent, hR]; exact hM.rsent i j
  psent i j := by
    have := hM.psent i j; have := hpipe i j; rw [hsent]; omega
  rs_w := by rw [hR]; exact hM.rs_w
  rs_self i hi := by rw [hR, hops i hi]; exact hM.rs_self i hi

lemma invM_init (w : P) (t : ℕ) (v₀ : V) :
    InvM w ((alg w t v₀).initCfg) ([] : List (Label P (register V v₀))) where
  wsent i j := by simp [wSent, Protocol.initCfg, sent, alg, Loc.init, W]
  rsent i j := by simp [Protocol.initCfg, alg, Loc.init, R]
  psent i j := by simp [Protocol.initCfg, alg, Loc.init, tk, cR]
  rs_w := by simp [Protocol.initCfg, alg, Loc.init, R]
  rs_self i _ := by simp [Protocol.initCfg, alg, Loc.init, R]

/-- A step that adds the messages `out` of `p` (possibly `WRITE`s) to the log, with the given
effect on the `WRITE` counters. -/
lemma InvM.of_wsend {w : P} {v₀ : V} {C C' : Cfg P V} {h h' : List (Label P (register V v₀))}
    (hM : InvM w C h) (p : P) (out : Multiset (P × Msg V)) (hsent : C'.sent = C.sent + outMsgs p out)
    (hro : ∀ x ∈ out, x.2.isWrite = true)
    (hR : ∀ i, R C' i i = R C i i) (hops : ∀ i, i ≠ w → opsOf h' i = opsOf h i)
    (hpipe : ∀ i j, tk C' j i + cR C' i j ≤ tk C j i + cR C i j)
    (hw : ∀ i j, (outMsgs p out).countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) +
      (if i = j then 0 else sent C i j) = if i = j then 0 else sent C' i j) : InvM w C' h' where
  wsent i j := by
    have := hM.wsent i j; have := hw i j
    simp only [wSent, hsent, Multiset.countP_add] at *; omega
  rsent i j := by
    have hz : (outMsgs p out).count (i, j, .read) = 0 := by
      rw [Multiset.count_eq_zero]; intro hx
      simp only [outMsgs, Multiset.mem_map] at hx
      obtain ⟨y, hy, he⟩ := hx
      have := hro y hy; simp only [Prod.mk.injEq] at he; rw [he.2.2] at this; simp [Msg.isWrite] at this
    rw [hsent, Multiset.count_add, hz, hR]; simpa using hM.rsent i j
  psent i j := by
    have hz : ∀ a b, (outMsgs p out).count (a, b, .proceed) = 0 := by
      intro a b; rw [Multiset.count_eq_zero]; intro hx
      simp only [outMsgs, Multiset.mem_map] at hx
      obtain ⟨y, hy, he⟩ := hx
      have := hro y hy; simp only [Prod.mk.injEq] at he; rw [he.2.2] at this; simp [Msg.isWrite] at this
    have hz' : ∀ a b, (outMsgs p out).count (a, b, .read) = 0 := by
      intro a b; rw [Multiset.count_eq_zero]; intro hx
      simp only [outMsgs, Multiset.mem_map] at hx
      obtain ⟨y, hy, he⟩ := hx
      have := hro y hy; simp only [Prod.mk.injEq] at he; rw [he.2.2] at this; simp [Msg.isWrite] at this
    have := hM.psent i j; have := hpipe i j
    rw [hsent, Multiset.count_add, Multiset.count_add, hz, hz']; omega
  rs_w := by rw [hR]; exact hM.rs_w
  rs_self i hi := by rw [hR, hops i hi]; exact hM.rs_self i hi

/-- **Invariant of the message log.** -/
theorem invM_of_reach {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : (alg w t v₀).Reach C h) : InvM w C h := by
  induction hr with
  | init => exact invM_init w t v₀
  | @step C h s C' ℓ hr hs ih =>
    have hI := invW_of_reach hr
    have hP := invP_of_reach hr
    cases s with
    | inv p o =>
      obtain ⟨-, rfl, l, out, hinv, rfl⟩ := step_inv hs
      cases o with
      | write v =>
        obtain ⟨hpw, -, rfl, rfl⟩ := invoke_write hinv
        subst p
        set C' := C.apply w _ _ C.net with hC'
        obtain ⟨o, ho⟩ : ∃ o, o = W C w w := ⟨_, rfl⟩
        have hWw : ∀ j, W C' w j = if j = w then o + 1 else W C w j := by
          intro j; by_cases hj : j = w <;> simp [hC', W, hj, ho]
        have hWo : ∀ i, i ≠ w → ∀ j, W C' i j = W C i j := by intro i hi j; simp [hC', W, hi]
        refine ih.of_wsend w _ rfl (by
            intro x hx; simp only [sendTo, Multiset.mem_map] at hx
            obtain ⟨_, _, rfl⟩ := hx; rfl)
          ?_ ?_ ?_ ?_
        · intro i; by_cases hi : i = w
          · subst hi; simp [hC', R]
          · simp [hC', R, hi]
        · intro i hi; simp [Ne.symm hi]
        · intro i j
          have h1 : tk C' j i = tk C j i := by
            by_cases hj : j = w
            · subst hj; simp [hC', tk]
            · simp [hC', tk, hj]
          have h2 : cR C' i j = cR C i j := by
            simp only [cR, hC', Config.apply_net, Multiset.count_add]
            rw [count_outMsgs_sendTo]; simp
          omega
        · intro i j
          rw [countP_outMsgs_sendTo_write]
          by_cases hij : i = j
          · subst hij; simp only [ite_true]
            split_ifs with hh
            · obtain ⟨rfl, hh⟩ := hh; simp at hh
            · omega
          · simp only [hij, ite_false]
            by_cases hi : i = w
            · subst hi
              have hS' : sent C' i j = min (o + 1) (W C i j + 1) := by
                simp only [sent]; rw [hWw, hWw, if_pos rfl, if_neg (Ne.symm hij)]
              have hS : sent C i j = min o (W C i j + 1) := by simp only [sent, ho]
              have := hI.ws_le i j
              split_ifs with hh
              · simp only [Function.update_apply, Ne.symm hij, ite_false, true_and] at hh
                simp only [W] at hS hS' this ho; omega
              · simp only [Function.update_apply, Ne.symm hij, ite_false, true_and] at hh
                simp only [W] at hS hS' this ho; omega
            · simp only [hi, false_and, ite_false, zero_add]
              simp [sent, hWo i hi]
      | read =>
        obtain ⟨hpw, hidle, rfl, rfl⟩ := invoke_read hinv
        set C' := C.apply p _ _ C.net with hC'
        have hR : ∀ i j, R C' i j = if i = p ∧ j = p then R C p p + 1 else R C i j := by
          intro i j
          by_cases hi : i = p
          · subst hi; by_cases hj : j = i <;> simp [hC', R, hj, Function.update_apply]
          · simp [hC', R, hi]
        have htk : ∀ j i, tk C' j i = tk C j i := by
          intro j i; by_cases hj : j = p
          · subst hj; simp [hC', tk]
          · simp [hC', tk, hj]
        have hcnt : ∀ x, C'.net.count x = C.net.count x +
            if x.1 = p ∧ x.2.1 ≠ p ∧ x.2.2 = .read then 1 else 0 := by
          intro x; simp [hC', Multiset.count_add, count_outMsgs_sendTo]
        have hscnt : ∀ x, C'.sent.count x = C.sent.count x +
            if x.1 = p ∧ x.2.1 ≠ p ∧ x.2.2 = .read then 1 else 0 := by
          intro x; simp [hC', Multiset.count_add, count_outMsgs_sendTo]
        have hW : ∀ i j, W C' i j = W C i j := by
          intro i j; by_cases hi : i = p
          · subst hi; simp [hC', W]
          · simp [hC', W, hi]
        have hS : ∀ i j, sent C' i j = sent C i j := by intro i j; simp [sent, hW]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro i j
          have h0 : wSent C' i j = wSent C i j := by
            simp only [wSent, hC', Config.apply_sent, Multiset.countP_add]
            rw [countP_outMsgs_nonwrite (fun x hx => by
              simp only [sendTo, Multiset.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl)]
            rfl
          rw [h0, hS]; exact ih.wsent i j
        · intro i j
          rw [hscnt, hR, ih.rsent i j]
          by_cases hij : i = j
          · subst hij; simp
          · by_cases hi : i = p
            · subst hi; simp [hij, Ne.symm hij]
            · simp [hi, hij]
        · intro i j
          have := ih.psent i j
          have e1 : C'.sent.count (j, i, .proceed) = C.sent.count (j, i, .proceed) := by
            rw [hscnt]; simp
          have e2 : cR C' i j = cR C i j + if i = p ∧ ¬ j = p then 1 else 0 := by
            simp only [cR, hcnt]; simp
          have e3 : C'.sent.count (i, j, .read) =
              C.sent.count (i, j, .read) + if i = p ∧ ¬ j = p then 1 else 0 := by
            rw [hscnt]; simp
          rw [e1, e3, htk, e2]; omega
        · rw [hR, if_neg (fun h => hpw h.1.symm)]
          exact ih.rs_w
        · intro i hi
          rw [hR]
          by_cases hip : i = p
          · subst hip; simp [ih.rs_self i hi]
          · simp [hip, Ne.symm hip, ih.rs_self i hi]
    | internal p a =>
      obtain ⟨hpc, l, out, r, hint, rfl, rfl⟩ := step_internal hs
      have hnos : ∀ (l : Loc P V), l.ws = (C.loc p).ws → l.rs = (C.loc p).rs →
          l.tasks = (C.loc p).tasks →
          InvM w (C.apply p l 0 C.net) (h ++ (r.map (Label.ret p)).toList) := by
        intro l hws hrs htasks
        set C' := C.apply p l 0 C.net with hC'
        have hW : ∀ i j, W C' i j = W C i j := by
          intro i j; by_cases hi : i = p
          · subst hi; simp [hC', W, hws]
          · simp [hC', W, hi]
        refine ih.of_nosend (by simp [hC']) ?_ ?_ ?_ ?_
        · intro i; by_cases hi : i = p
          · subst hi; simp [hC', R, hrs]
          · simp [hC', R, hi]
        · intro i _; cases r <;> simp
        · intro i j
          have h1 : tk C' j i = tk C j i := by
            by_cases hj : j = p
            · subst hj; simp [hC', tk, htasks]
            · simp [hC', tk, hj]
          have h2 : cR C' i j = cR C i j := by simp [hC', cR]
          omega
        · intro i j; simp [sent, hW]
      cases a with
      | wret => obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint; exact hnos _ rfl rfl rfl
      | r8 => obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint; exact hnos _ rfl rfl rfl
      | rret => obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint; exact hnos _ rfl rfl rfl
      | proceed j sn =>
        obtain ⟨hmem, -, rfl, rfl, rfl⟩ := internal_proceed hint
        simp only [Option.map_none, Option.toList_none, List.append_nil]
        set C' := C.apply p _ _ C.net with hC'
        have hjp : j ≠ p := hP.tasks_ne p j sn hmem
        have hW : ∀ i k, W C' i k = W C i k := by
          intro i k; by_cases hi : i = p
          · subst hi; simp [hC', W]
          · simp [hC', W, hi]
        have hR : ∀ i k, R C' i k = R C i k := by
          intro i k; by_cases hi : i = p
          · subst hi; simp [hC', R]
          · simp [hC', R, hi]
        have hscnt : ∀ x, C'.sent.count x = C.sent.count x + if x = (p, j, .proceed) then 1 else 0 := by
          intro x; simp [hC', Multiset.count_add, count_outMsgs_single]
        have htk : ∀ k i, tk C' k i + (if k = p ∧ i = j then 1 else 0) = tk C k i := by
          intro k i
          by_cases hk : k = p
          · subst hk
            have := countP_erase_of_mem (fun x : P × ℕ => x.1 = i) hmem
            simp only [tk, hC', Config.apply_loc', ite_true]
            by_cases hi : i = j
            · subst hi; simp at this ⊢; omega
            · simp [hi, Ne.symm hi] at this ⊢; omega
          · simp [tk, hC', hk]
        have hcR : ∀ i k, cR C' i k = cR C i k := by
          intro i k; simp [hC', cR, Multiset.count_add, count_outMsgs_single]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro i k
          have h0 : wSent C' i k = wSent C i k := by
            simp only [wSent, hC', Config.apply_sent, Multiset.countP_add]
            rw [countP_outMsgs_single]; simp [Msg.isWrite]
          have hS : sent C' i k = sent C i k := by simp [sent, hW]
          rw [h0, hS]; exact ih.wsent i k
        · intro i k; rw [hscnt, hR, ih.rsent i k]; simp
        · intro i k
          have := ih.psent i k
          have h1 := htk k i
          have e1 : C'.sent.count (i, k, .read) = C.sent.count (i, k, .read) := by
            rw [hscnt]; simp
          have e2 : C'.sent.count (k, i, .proceed) =
              C.sent.count (k, i, .proceed) + if k = p ∧ i = j then 1 else 0 := by
            rw [hscnt]; congr 1
            by_cases hh : k = p ∧ i = j
            · rw [if_pos hh, if_pos (by rw [hh.1, hh.2])]
            · rw [if_neg hh, if_neg (by simp only [Prod.mk.injEq, and_true]; exact hh)]
          rw [e1, e2, hcR]; omega
        · rw [hR]; exact ih.rs_w
        · intro i hi; rw [hR]; exact ih.rs_self i hi
    | recv src dst m =>
      obtain ⟨-, hm, l, out, r, hrc, rfl, rfl⟩ := step_recv hs
      cases m with
      | write b v =>
        obtain ⟨hb, rfl, hcase⟩ := receive_write hrc
        simp only [Option.map_none, Option.toList_none, List.append_nil]
        obtain ⟨hqp, hsq, -, hqa, -⟩ := hI.recv_facts hm hb
        have hle0 := hI.ws_le dst src
        rcases hcase with ⟨ha, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩ | ⟨heq, rfl, rfl⟩ | himp
        · -- adopt
          set C' := C.apply dst _ _ (C.net.erase (src, dst, .write b v)) with hC'
          obtain ⟨a, haq⟩ : ∃ a, W C dst src = a := ⟨_, rfl⟩
          have hap : W C dst dst = a := by simp only [W] at ha haq ⊢; omega
          have hWd : ∀ j, W C' dst j = if j = dst ∨ j = src then a + 1 else W C dst j := by
            intro j
            by_cases hj : j = src
            · subst hj; simp [hC', W, haq]
            · by_cases hj' : j = dst
              · subst hj'; simp [hC', W, hj, haq, Function.update_apply]
              · simp [hC', W, hj, hj', Function.update_apply]
          have hWo : ∀ i, i ≠ dst → ∀ j, W C' i j = W C i j := by
            intro i hi j; simp [hC', W, hi]
          refine ih.of_wsend dst _ rfl (by
              intro x hx; simp only [sendTo, Multiset.mem_map] at hx
              obtain ⟨_, _, rfl⟩ := hx; rfl) ?_ (fun _ _ => rfl) ?_ ?_
          · intro i; by_cases hi : i = dst
            · subst hi; simp [hC', R]
            · simp [hC', R, hi]
          · intro i j
            have h1 : tk C' j i = tk C j i := by
              by_cases hj : j = dst
              · subst hj; simp [hC', tk]
              · simp [hC', tk, hj]
            have h2 : cR C' i j = cR C i j := by
              simp only [cR, hC', Config.apply_net, Multiset.count_add, count_outMsgs_sendTo]
              rw [Multiset.count_erase_of_ne (by simp)]; simp
            omega
          · intro i j
            rw [countP_outMsgs_sendTo_write]
            by_cases hij : i = j
            · subst hij; simp only [ite_true]
              split_ifs with hh
              · obtain ⟨rfl, hh⟩ := hh; simp at hh
              · omega
            · simp only [hij, ite_false]
              by_cases hi : i = dst
              · subst i
                have hj : j ≠ dst := Ne.symm hij
                have hle := hI.ws_le dst j
                have hS' : sent C' dst j = min (a + 1) (W C' dst j + 1) := by
                  simp only [sent]; rw [hWd dst, if_pos (Or.inl rfl)]
                have hS : sent C dst j = min a (W C dst j + 1) := by simp only [sent, hap]
                have hf : (Function.update (C.loc dst).ws dst (W C dst src + 1) j =
                    W C dst src + 1 - 1) ↔ W C dst j = a := by
                  simp [Function.update_apply, hj, haq, W]
                rw [hS', hS, hWd j]
                by_cases hjs : j = src
                · subst hjs
                  simp only [hj, or_true, ite_true, true_and]
                  rw [if_pos (hf.2 haq)]
                  simp only [W] at haq hap hle ⊢; omega
                · simp only [hj, hjs, or_self, ite_false, true_and]
                  by_cases hja : W C dst j = a
                  · rw [if_pos (hf.2 hja)]; simp only [W] at hja hap hle ⊢; omega
                  · rw [if_neg (fun h => hja (hf.1 h))]; simp only [W] at hja hap hle ⊢; omega
              · simp only [hi, false_and, ite_false, zero_add]
                simp [sent, hWo i hi]
        · -- line 16
          set C' := C.apply dst _ _ (C.net.erase (src, dst, .write b v)) with hC'
          have hWd : ∀ j, W C' dst j = if j = src then W C dst src + 1 else W C dst j := by
            intro j; by_cases hj : j = src
            · subst hj; simp [hC', W]
            · simp [hC', W, hj]
          have hWo : ∀ i, i ≠ dst → ∀ j, W C' i j = W C i j := by
            intro i hi j; simp [hC', W, hi]
          refine ih.of_wsend dst _ rfl (by simp [Msg.isWrite]) ?_ (fun _ _ => rfl) ?_ ?_
          · intro i; by_cases hi : i = dst
            · subst hi; simp [hC', R]
            · simp [hC', R, hi]
          · intro i j
            have h1 : tk C' j i = tk C j i := by
              by_cases hj : j = dst
              · subst hj; simp [hC', tk]
              · simp [hC', tk, hj]
            have h2 : cR C' i j = cR C i j := by
              simp only [cR, hC', Config.apply_net, Multiset.count_add, count_outMsgs_single]
              rw [Multiset.count_erase_of_ne (by simp)]; simp
            omega
          · intro i j
            rw [countP_outMsgs_single]
            by_cases hij : i = j
            · subst hij; simp only [ite_true]
              split_ifs with hh
              · obtain ⟨rfl, rfl, -⟩ := hh; exact absurd rfl hqp
              · omega
            · simp only [hij, ite_false]
              by_cases hi : i = dst
              · subst hi
                have hpp : W C' i i = W C i i := by rw [hWd, if_neg (Ne.symm hqp)]
                by_cases hj : j = src
                · subst hj
                  simp only [true_and, Msg.isWrite, and_true, ite_true]
                  simp only [sent, hpp, hWd, ite_true]
                  simp only [W] at hlt ⊢; omega
                · simp [Ne.symm hj, sent, hpp, hWd, hj]
              · simp only [Ne.symm hi, false_and, ite_false, zero_add]
                simp [sent, hWo i hi]
        · -- nothing sent
          set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, .write b v))
            with hC'
          refine ih.of_nosend (by simp [hC']) ?_ (fun _ _ => rfl) ?_ ?_
          · intro i; by_cases hi : i = dst
            · subst hi; simp [hC', R]
            · simp [hC', R, hi]
          · intro i j
            have h1 : tk C' j i = tk C j i := by
              by_cases hj : j = dst
              · subst hj; simp [hC', tk]
              · simp [hC', tk, hj]
            have h2 : cR C' i j = cR C i j := by
              simp only [cR, hC', Config.apply_net, Multiset.count_add]
              rw [Multiset.count_erase_of_ne (by simp)]; simp
            omega
          · intro i j _
            by_cases hi : i = dst
            · subst i
              have hdd : W C' dst dst = W C dst dst := by
                simp [hC', W, Function.update_apply, Ne.symm hqp]
              by_cases hj : j = src
              · subst j
                have h1 : W C' dst src = W C dst src + 1 := by simp [hC', W]
                simp only [sent, hdd, h1]; simp only [W] at heq ⊢; omega
              · have h1 : W C' dst j = W C dst j := by simp [hC', W, hj]
                simp only [sent, hdd, h1]
            · simp [sent, hC', W, hi]
        · simp only [W] at hle0 himp; omega
      | read =>
        obtain ⟨rfl, rfl, rfl⟩ := receive_read hrc
        simp only [Option.map_none, Option.toList_none, List.append_nil]
        set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, .read)) with hC'
        have hsd : src ≠ dst := by
          intro he; subst he; have := hP.read_ne src
          simp only [cR] at this; rw [Multiset.count_eq_zero] at this; exact this hm
        refine ih.of_nosend (by simp [hC']) ?_ (fun _ _ => rfl) ?_ ?_
        · intro i; by_cases hi : i = dst
          · subst hi; simp [hC', R]
          · simp [hC', R, hi]
        · intro i j
          have hpos : 1 ≤ C.net.count (src, dst, .read) := Multiset.one_le_count_iff_mem.2 hm
          by_cases hh : i = src ∧ j = dst
          · obtain ⟨rfl, rfl⟩ := hh
            simp only [tk, cR, hC', Config.apply_loc', ite_true, Config.apply_net,
              Multiset.countP_add, countP_singleton', Multiset.count_add, outMsgs_zero,
              Multiset.count_zero, add_zero, Multiset.count_erase_self]
            simp; omega
          · have h1 : tk C' j i = tk C j i := by
              by_cases hj : j = dst
              · subst hj
                have hi : i ≠ src := fun h => hh ⟨h, rfl⟩
                simp [tk, hC', Multiset.countP_add, countP_singleton', Ne.symm hi]
              · simp [tk, hC', hj]
            have h2 : cR C' i j = cR C i j := by
              simp only [cR, hC', Config.apply_net, outMsgs_zero, add_zero]
              rw [Multiset.count_erase_of_ne]
              simp only [ne_eq, Prod.mk.injEq, and_true]; exact hh
            omega
        · intro i j _
          have hW : ∀ a b, W C' a b = W C a b := by
            intro a b; by_cases ha : a = dst
            · subst ha; simp [hC', W]
            · simp [hC', W, ha]
          simp only [sent, hW]
      | proceed =>
        obtain ⟨rfl, rfl, rfl⟩ := receive_proceed hrc
        simp only [Option.map_none, Option.toList_none, List.append_nil]
        set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, .proceed))
          with hC'
        have hsd : src ≠ dst := by
          intro he; subst he; have := hP.proceed_ne src
          simp only [cP] at this; rw [Multiset.count_eq_zero] at this; exact this hm
        refine ih.of_nosend (by simp [hC']) ?_ (fun _ _ => rfl) ?_ ?_
        · intro i; by_cases hi : i = dst
          · subst hi; simp [hC', R, Function.update_apply, Ne.symm hsd]
          · simp [hC', R, hi]
        · intro i j
          have h1 : tk C' j i = tk C j i := by
            by_cases hj : j = dst
            · subst hj; simp [tk, hC']
            · simp [tk, hC', hj]
          have h2 : cR C' i j = cR C i j := by
            simp only [cR, hC', Config.apply_net, outMsgs_zero, add_zero]
            rw [Multiset.count_erase_of_ne (by simp)]
          omega
        · intro i j _
          have hW : ∀ a b, W C' a b = W C a b := by
            intro a b; by_cases ha : a = dst
            · subst ha; simp [hC', W]
            · simp [hC', W, ha]
          simp only [sent, hW]
    | drop src dst m =>
      obtain ⟨-, -, rfl, rfl⟩ := step_drop hs
      refine ih.of_nosend rfl (fun _ => rfl) (fun _ _ => by simp) ?_ (fun _ _ _ => rfl)
      intro i j
      simp only [tk, cR]
      have : (C.net.erase (src, dst, m)).count (i, j, .read) ≤ C.net.count (i, j, .read) :=
        Multiset.count_le_of_le _ (Multiset.erase_le _ _)
      omega
    | crash p =>
      obtain ⟨-, rfl, rfl⟩ := step_crash hs
      exact ih.of_nosend rfl (fun _ => rfl) (fun _ _ => by simp) (fun _ _ => le_refl _)
        (fun _ _ _ => rfl)
    | skip =>
      obtain ⟨rfl, rfl⟩ := step_skip hs
      simpa using ih

/-- **Lemma 5** of the paper (R1/R2), about the messages actually sent (ghost log `C.sent`):
the number of `WRITE` messages ever sent by `p_i` to `p_j ≠ p_i` is `w_sync_i[j]` if
`w_sync_i[i] = w_sync_i[j]` (R1) and `w_sync_i[j] + 1` if `w_sync_i[i] > w_sync_i[j]` (R2),
i.e. it is `sent C i j = min (w_sync_i[i], w_sync_i[j] + 1)`. Holds for every process (the paper
states it for correct ones). -/
theorem lemma5_sent {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : (alg w t v₀).Reach C h) {i j : P} (hij : i ≠ j) :
    wSent C i j = sent C i j ∧
      (W C i i = W C i j → wSent C i j = W C i j) ∧
      (W C i j < W C i i → wSent C i j = W C i j + 1) := by
  have h1 := (invM_of_reach hr).wsent i j
  rw [if_neg hij] at h1
  refine ⟨h1, fun he => ?_, fun hlt => ?_⟩ <;> rw [h1] <;> simp only [sent] <;> omega

/-! ## Counting -/

lemma card_filter_eq_sum (s : Multiset (P × P × Msg V)) (q : Msg V → Prop) [DecidablePred q] :
    (s.filter (fun x => q x.2.2)).card =
      ∑ i, ∑ j, s.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ q x.2.2) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨a1, a2, a3⟩ := a
    rw [Multiset.filter_cons]
    simp only [Multiset.countP_cons, Finset.sum_add_distrib]
    by_cases hq : q a3
    · simp [hq, ih, Finset.sum_ite_eq, add_comm, ite_and]
    · simp [hq, ih]

lemma countP_nonwrite (s : Multiset (P × P × Msg V)) (i j : P) :
    s.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = false) =
      s.count (i, j, .read) + s.count (i, j, .proceed) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    obtain ⟨a1, a2, a3⟩ := a
    simp only [Multiset.countP_cons, Multiset.count_cons, ih]
    by_cases h1 : a1 = i
    · subst h1
      by_cases h2 : a2 = j
      · subst h2; cases a3 <;> simp [Msg.isWrite] <;> omega
      · cases a3 <;> simp [Msg.isWrite, h2, Ne.symm h2]
    · cases a3 <;> simp [Msg.isWrite, h1, Ne.symm h1]

lemma sum_ne_const (c : P → ℕ) (i : P) :
    ∑ j, (if i = j then 0 else c i) = (Fintype.card P - 1) * c i := by
  have h1 : ∑ j, (if i = j then 0 else c i) + ∑ j, (if i = j then c i else 0) =
      Fintype.card P * c i := by
    rw [← Finset.sum_add_distrib]
    simp only [Finset.sum_congr rfl (fun j _ => show (if i = j then 0 else c i) +
      (if i = j then c i else 0) = c i by split_ifs <;> simp), Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  rw [Finset.sum_ite_eq] at h1
  simp only [Finset.mem_univ, ite_true] at h1
  have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨i⟩
  rw [Nat.sub_mul, one_mul]
  omega

/-- **Theorem 2 (write messages).** At most `n (n - 1)` `WRITE` messages are ever sent per
invoked write: each process forwards each value at most once to each other process. -/
theorem write_messages {w : P} {t : ℕ} {v₀ : V} (ht : 2 * t < Fintype.card P) {C : Cfg P V}
    {h : List (Label P (register V v₀))} (hr : (alg w t v₀).Reach C h) :
    (C.sent.filter (fun x => x.2.2.isWrite = true)).card ≤
      Fintype.card P * (Fintype.card P - 1) * (opsOf h w).length := by
  have hM := invM_of_reach hr
  have hI := invW_of_reach hr
  obtain ⟨g, hH⟩ := invH_of_reach ht hr
  rw [card_filter_eq_sum C.sent (fun m => m.isWrite = true)]
  have hb : ∀ i j, C.sent.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true) ≤
      if i = j then 0 else (opsOf h w).length := by
    intro i j
    have := hM.wsent i j
    simp only [wSent] at this
    split_ifs at this ⊢ with hij
    · exact this.le
    · rw [← hH.own_w]
      exact this.le.trans ((InvW.sent_le_own C i j).trans (hI.own_le i))
  calc ∑ i, ∑ j, C.sent.countP (fun x => x.1 = i ∧ x.2.1 = j ∧ x.2.2.isWrite = true)
      ≤ ∑ i : P, ∑ j : P, (if i = j then 0 else (opsOf h w).length) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = ∑ i : P, (Fintype.card P - 1) * (opsOf h w).length :=
        Finset.sum_congr rfl (fun i _ => sum_ne_const (fun _ => (opsOf h w).length) i)
    _ = Fintype.card P * (Fintype.card P - 1) * (opsOf h w).length := by
        simp [Finset.sum_const, Finset.card_univ, mul_assoc]

/-- **Theorem 2 (read messages).** At most `2 (n - 1)` `READ`/`PROCEED` messages are ever sent
per invoked read (`n - 1` requests, each answered at most once). -/
theorem read_messages {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V}
    {h : List (Label P (register V v₀))} (hr : (alg w t v₀).Reach C h) :
    (C.sent.filter (fun x => x.2.2.isWrite = false)).card ≤
      2 * (Fintype.card P - 1) * ∑ i, (if i = w then 0 else (opsOf h i).length) := by
  have hM := invM_of_reach hr
  rw [card_filter_eq_sum C.sent (fun m => m.isWrite = false)]
  simp only [countP_nonwrite]
  have hRi : ∀ i, R C i i = if i = w then 0 else (opsOf h i).length := by
    intro i; split_ifs with hi
    · subst hi; exact hM.rs_w
    · exact hM.rs_self i hi
  have hb : ∀ i j, C.sent.count (i, j, .read) + C.sent.count (i, j, .proceed) ≤
      (if i = j then 0 else R C i i) + (if j = i then 0 else R C j j) := by
    intro i j
    have h1 := hM.rsent i j
    have h2 := hM.psent j i
    have h3 := hM.rsent j i
    omega
  calc ∑ i, ∑ j, (C.sent.count (i, j, .read) + C.sent.count (i, j, .proceed))
      ≤ ∑ i : P, ∑ j : P, ((if i = j then 0 else R C i i) + (if j = i then 0 else R C j j)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = ∑ i : P, ∑ j : P, (if i = j then 0 else R C i i) +
        ∑ j : P, ∑ i : P, (if j = i then 0 else R C j j) := by
        simp only [Finset.sum_add_distrib]; congr 1; exact Finset.sum_comm
    _ = 2 * ((Fintype.card P - 1) * ∑ i, R C i i) := by
        simp only [Finset.sum_congr rfl (fun i _ => sum_ne_const (fun k => R C k k) i),
          ← Finset.mul_sum]
        ring
    _ = 2 * (Fintype.card P - 1) * ∑ i, (if i = w then 0 else (opsOf h i).length) := by
        rw [Finset.sum_congr rfl (fun i _ => hRi i)]; ring

end Podc.TwoBit
