import Papers.PODC2016.TwoBitRegisters.Steps

/-!
# The alternating-bit invariant of the `WRITE` messages (Lemmas 1–5 of the paper)

For every pair `i ≠ j`, process `i` has sent to `j` exactly
`sent C i j = min (w_sync_i[i], w_sync_i[j] + 1)` messages `WRITE(-,-)` (Lemma 5); the `k`-th one is
`WRITE(k mod 2, v_k)`. Those not yet processed by `j` are exactly the numbers
`k ∈ (w_sync_j[i], sent C i j]` (at most two of them, with different parities — Property P1);
only messages of crashed senders can be lost. Together with `w_sync_i[j] ≤ w_sync_i[i]`
(Lemma 3), `w_sync_j[i] ≤ sent C i j ≤ w_sync_i[i]` (Lemma 2) and the agreement of all local
histories with the writer's (Lemma 4), this is `InvW`, an invariant of every reachable
configuration (`invW_of_reach`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Configurations of the algorithm. -/
abbrev Cfg (P V : Type) := Config P (Loc P V) (Msg V)

/-- `w_sync_i[j]` in configuration `C`. -/
abbrev W (C : Cfg P V) (i j : P) : ℕ := (C.loc i).ws j

/-- Number of `WRITE` messages sent so far by `i` to `j`. -/
def sent (C : Cfg P V) (i j : P) : ℕ := min (W C i i) (W C i j + 1)

/-- The writer's history `history_w`. -/
abbrev Hw (w : P) (C : Cfg P V) (k : ℕ) : V := (C.loc w).hist k

/-- The invariant of the write part of the algorithm. -/
structure InvW (w : P) (C : Cfg P V) : Prop where
  /-- Lemma 3. -/
  ws_le : ∀ i j, W C i j ≤ W C i i
  /-- `j` has processed at most the messages that `i` has sent to it. -/
  recv_le : ∀ i j, i ≠ j → W C j i ≤ sent C i j
  /-- `WRITE` messages in transit from `i` to `j` are the not yet processed ones. -/
  net_write : ∀ i j b v, 0 < C.net.count (i, j, .write b v) →
    i ≠ j ∧ ∃ k, W C j i < k ∧ k ≤ sent C i j ∧ b = par k ∧ v = Hw w C k
  /-- No duplicates. -/
  count_write : ∀ i j b v, C.net.count (i, j, .write b v) ≤ 1
  /-- Messages of non-crashed senders are not lost. -/
  exact : ∀ i j k, i ≠ j → i ∉ C.crashed → W C j i < k → k ≤ sent C i j →
    0 < C.net.count (i, j, .write (par k) (Hw w C k))
  /-- Lemma 4: local histories are prefixes of the writer's history. -/
  hist : ∀ i k, k ≤ W C i i → (C.loc i).hist k = Hw w C k
  /-- Nobody knows more values than the writer. -/
  own_le : ∀ i, W C i i ≤ W C w w

namespace InvW

variable {w : P} {C : Cfg P V}

lemma sent_le_own (C : Cfg P V) (i j : P) : sent C i j ≤ W C i i := min_le_left _ _

lemma sent_le_succ (C : Cfg P V) (i j : P) : sent C i j ≤ W C i j + 1 := min_le_right _ _

/-- At most two unprocessed messages per channel (Property P1). -/
lemma sent_le_two (hI : InvW w C) {i j : P} (hij : i ≠ j) : sent C i j ≤ W C j i + 2 := by
  have h1 := hI.recv_le j i (Ne.symm hij)
  have h2 := sent_le_succ C i j
  have h3 := sent_le_succ C j i
  omega

/-- A message that passes the parity test of line 11 is the next one (alternating bit). -/
lemma eq_next (hI : InvW w C) {i j : P} {b : Bool} {v : V}
    (hm : 0 < C.net.count (i, j, .write b v)) (hb : b = par (W C j i + 1)) :
    i ≠ j ∧ W C j i + 1 ≤ sent C i j ∧ v = Hw w C (W C j i + 1) := by
  obtain ⟨hij, k, hk1, hk2, rfl, rfl⟩ := hI.net_write i j b v hm
  have h2 := hI.sent_le_two hij
  have hk : k = W C j i + 1 := by
    rw [par_eq_iff] at hb
    omega
  subst hk
  exact ⟨hij, hk2, rfl⟩

end InvW

/-! ## Initial configuration and frame lemma -/

lemma invW_init (w : P) (t : ℕ) (v₀ : V) : InvW w ((alg w t v₀).initCfg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Protocol.initCfg, alg, Loc.init, W, sent, Hw]
  intros; omega

/-- Steps that change neither `w_sync`, nor histories, nor (except by losing messages of crashed
senders) the `WRITE` messages in transit preserve `InvW`. -/
lemma InvW.frame {w : P} {C C' : Cfg P V} (hI : InvW w C)
    (hws : ∀ i, (C'.loc i).ws = (C.loc i).ws) (hh : ∀ i, (C'.loc i).hist = (C.loc i).hist)
    (hle : ∀ i j b v, C'.net.count (i, j, .write b v) ≤ C.net.count (i, j, .write b v))
    (hge : ∀ i j b v, i ∉ C'.crashed →
      C.net.count (i, j, .write b v) ≤ C'.net.count (i, j, .write b v))
    (hcr : C.crashed ⊆ C'.crashed) : InvW w C' := by
  have hW : ∀ i j, W C' i j = W C i j := fun i j => by simp [W, hws]
  have hS : ∀ i j, sent C' i j = sent C i j := fun i j => by simp [sent, hW]
  have hH : ∀ k, Hw w C' k = Hw w C k := fun k => by simp [Hw, hh]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; rw [hW, hW]; exact hI.ws_le i j
  · intro i j hij; rw [hW, hS]; exact hI.recv_le i j hij
  · intro i j b v hm
    simp only [hW, hS, hH]
    exact hI.net_write i j b v (lt_of_lt_of_le hm (hle i j b v))
  · intro i j b v; exact (hle i j b v).trans (hI.count_write i j b v)
  · intro i j k hij hi h1 h2
    rw [hW] at h1; rw [hS] at h2; rw [hH]
    exact lt_of_lt_of_le (hI.exact i j k hij (fun h => hi (hcr h)) h1 h2) (hge i j _ _ hi)
  · intro i k hk; rw [hW] at hk; rw [hH, hh]; exact hI.hist i k hk
  · intro i; rw [hW, hW]; exact hI.own_le i

@[simp] lemma Config.apply_loc' {C : Cfg P V} {p : P} {l : Loc P V} {out : Multiset (P × Msg V)}
    {net : Multiset (P × P × Msg V)} (i : P) :
    (C.apply p l out net).loc i = if i = p then l else C.loc i := by
  simp [Config.apply, Function.update_apply]

@[simp] lemma Config.apply_net {C : Cfg P V} {p : P} {l : Loc P V} {out : Multiset (P × Msg V)}
    {net : Multiset (P × P × Msg V)} : (C.apply p l out net).net = net + outMsgs p out := rfl

@[simp] lemma Config.apply_crashed {C : Cfg P V} {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} {net : Multiset (P × P × Msg V)} :
    (C.apply p l out net).crashed = C.crashed := rfl

/-! ## Lines 1–2 -/

lemma InvW.of_invoke_write {w : P} {C : Cfg P V} (hI : InvW w C) {p : P} {v : V} {l : Loc P V}
    {out : Multiset (P × Msg V)} (h : invoke w p (.write v) (C.loc p) = some (l, out)) :
    InvW w (C.apply p l out C.net) := by
  obtain ⟨hpw, -, rfl, rfl⟩ := invoke_write h
  subst p
  set C' := C.apply w _ _ C.net with hC'
  obtain ⟨o, ho⟩ : ∃ o, o = W C w w := ⟨_, rfl⟩
  have hWw : ∀ j, W C' w j = if j = w then o + 1 else W C w j := by
    intro j; by_cases hj : j = w <;> simp [hC', W, hj, Function.update_apply, ho]
  have hWo : ∀ i, i ≠ w → ∀ j, W C' i j = W C i j := by
    intro i hi j; simp [hC', W, hi]
  have hH : ∀ k, Hw w C' k = if k = o + 1 then v else Hw w C k := by
    intro k; by_cases hk : k = o + 1 <;> simp [hC', Hw, hk, Function.update_apply, ho, W]
  have hcnt : ∀ i j b v', C'.net.count (i, j, .write b v') = C.net.count (i, j, .write b v') +
      if i = w ∧ (j ≠ w ∧ W C w j = o) ∧ b = par (o + 1) ∧ v' = v then 1 else 0 := by
    intro i j b v'
    simp only [hC', Config.apply_net, Multiset.count_add, count_outMsgs_sendTo]
    congr 1
    by_cases hj : j = w
    · simp [hj, W, ho]
    · simp [hj, W, ho, and_comm]
  have hS : ∀ i j, i ≠ w → sent C' i j = sent C i j := by
    intro i j hi; simp [sent, hWo i hi]
  have hSw : ∀ j, j ≠ w → sent C' w j = min (o + 1) (W C w j + 1) := by
    intro j hj; simp [sent, hWw, hj]
  have hsentw : ∀ j, sent C w j = min o (W C w j + 1) := fun j => by rw [ho]; rfl
  have hown : ∀ i, W C i i ≤ o := fun i => ho ▸ hI.own_le i
  have hsent_own : ∀ i j, sent C i j ≤ o := fun i j =>
    (InvW.sent_le_own C i j).trans (hown i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ws_le
    intro i j
    by_cases hi : i = w
    · subst i; rw [hWw j, hWw w, if_pos rfl]; have := hI.ws_le w j; split_ifs <;> omega
    · rw [hWo i hi, hWo i hi]; exact hI.ws_le i j
  · -- recv_le
    intro i j hij
    by_cases hi : i = w
    · subst i
      have hj : j ≠ w := Ne.symm hij
      rw [hWo j hj, hSw j hj]
      have := hI.recv_le w j hij; rw [hsentw] at this
      omega
    · rw [hS i j hi]
      by_cases hj : j = w
      · subst j; rw [hWw, if_neg hi]; exact hI.recv_le i w hij
      · rw [hWo j hj]; exact hI.recv_le i j hij
  · -- net_write
    intro i j b v' hm
    rw [hcnt] at hm
    by_cases hnew : i = w ∧ (j ≠ w ∧ W C w j = o) ∧ b = par (o + 1) ∧ v' = v
    · obtain ⟨rfl, ⟨hj, hjo⟩, rfl, rfl⟩ := hnew
      refine ⟨Ne.symm hj, o + 1, ?_, ?_, rfl, by rw [hH, if_pos rfl]⟩
      · rw [hWo j hj]
        have := hI.recv_le i j (Ne.symm hj); rw [hsentw] at this; omega
      · rw [hSw j hj]; omega
    · rw [if_neg hnew, Nat.add_zero] at hm
      obtain ⟨hij, k, hk1, hk2, hb, hv⟩ := hI.net_write i j b v' hm
      have hko : k ≤ o := hk2.trans (hsent_own i j)
      refine ⟨hij, k, ?_, ?_, hb, ?_⟩
      · by_cases hj : j = w
        · subst j; rw [hWw, if_neg hij]; exact hk1
        · rw [hWo j hj]; exact hk1
      · by_cases hi : i = w
        · subst i; rw [hSw j (Ne.symm hij)]; rw [hsentw] at hk2; omega
        · rw [hS i j hi]; exact hk2
      · rw [hH, if_neg (by omega)]; exact hv
  · -- count_write
    intro i j b v'
    rw [hcnt]
    by_cases hnew : i = w ∧ (j ≠ w ∧ W C w j = o) ∧ b = par (o + 1) ∧ v' = v
    · rw [if_pos hnew]
      obtain ⟨rfl, ⟨hj, hjo⟩, rfl, rfl⟩ := hnew
      suffices C.net.count (i, j, .write (par (o + 1)) v') = 0 by omega
      by_contra hc
      obtain ⟨-, k, hk1, hk2, hb, -⟩ := hI.net_write i j _ _ (Nat.pos_of_ne_zero hc)
      rw [hsentw] at hk2
      have h3 := hI.recv_le j i hj
      have h4 := InvW.sent_le_succ C j i
      rw [par_eq_iff] at hb
      omega
    · rw [if_neg hnew, Nat.add_zero]; exact hI.count_write i j b v'
  · -- exact
    intro i j k hij hi h1 h2
    rw [hcnt]
    by_cases hiw : i = w
    · subst i
      have hj : j ≠ w := Ne.symm hij
      rw [hWo j hj] at h1; rw [hSw j hj] at h2
      by_cases hk : k ≤ sent C w j
      · have hko : k ≤ o := hk.trans (hsent_own w j)
        rw [hH, if_neg (by omega)]
        have := hI.exact w j k hij hi h1 hk; omega
      · rw [hsentw] at hk
        have hk' : k = o + 1 := by omega
        subst hk'
        have := hI.ws_le w j
        rw [hH, if_pos rfl, if_pos ⟨rfl, ⟨hj, by omega⟩, rfl, rfl⟩]; omega
    · rw [hS i j hiw] at h2
      have hko : k ≤ o := h2.trans (hsent_own i j)
      rw [hH, if_neg (by omega)]
      have h1' : W C j i < k := by
        by_cases hj : j = w
        · subst j; rw [hWw, if_neg hiw] at h1; exact h1
        · rw [hWo j hj] at h1; exact h1
      have := hI.exact i j k hij hi h1' h2; omega
  · -- hist
    intro i k hk
    by_cases hi : i = w
    · subst i; rfl
    · rw [hWo i hi] at hk
      have hko : k ≤ o := hk.trans (hown i)
      rw [hH, if_neg (by omega)]
      simp only [hC', Config.apply_loc', hi, ite_false]
      exact hI.hist i k hk
  · -- own_le
    intro i
    by_cases hi : i = w
    · subst i; exact le_refl _
    · rw [hWo i hi, hWw, if_pos rfl]; have := hown i; omega

/-! ## Lines 11–18 -/

lemma count_erase_add {α : Type} [DecidableEq α] (x m : α) (s t : Multiset α) :
    (s.erase m + t).count x = (if x = m then s.count x - 1 else s.count x) + t.count x := by
  rw [Multiset.count_add]
  split_ifs with h
  · subst h; rw [Multiset.count_erase_self]
  · rw [Multiset.count_erase_of_ne h]

lemma sent_mono {C C' : Cfg P V} {i j : P} (h1 : W C i i ≤ W C' i i) (h2 : W C i j ≤ W C' i j) :
    sent C i j ≤ sent C' i j := by
  simp only [sent]; omega

/-- Common facts for the reception of `WRITE(b, v)` by `p` from `q`. -/
lemma InvW.recv_facts {w : P} {C : Cfg P V} (hI : InvW w C) {p q : P} {b : Bool} {v : V}
    (hm : (q, p, Msg.write b v) ∈ C.net) (hb : b = par (W C p q + 1)) :
    q ≠ p ∧ W C p q + 1 ≤ sent C q p ∧ v = Hw w C (W C p q + 1) ∧ W C p q ≤ W C q p ∧
      ∀ b' v', (b', v') ≠ (b, v) → 0 < C.net.count (q, p, .write b' v') →
        ∃ k, W C p q + 1 < k ∧ k ≤ sent C q p ∧ b' = par k ∧ v' = Hw w C k := by
  obtain ⟨hqp, h1, h2⟩ := hI.eq_next (Multiset.count_pos.2 hm) hb
  have h3 := InvW.sent_le_succ C q p
  refine ⟨hqp, h1, h2, by omega, ?_⟩
  intro b' v' hne hc
  obtain ⟨-, k, hk1, hk2, rfl, rfl⟩ := hI.net_write q p b' v' hc
  have h4 := hI.sent_le_two hqp
  refine ⟨k, ?_, hk2, rfl, rfl⟩
  by_contra hk
  have : k = W C p q + 1 := by omega
  subst this
  exact hne (by rw [hb, h2])

/-- Lines 13–15 and 18: `p` learns a new value from `q` and forwards it. -/
lemma InvW.of_recv_adopt {w : P} {C : Cfg P V} (hI : InvW w C) {p q : P} {b : Bool} {v : V}
    (hm : (q, p, Msg.write b v) ∈ C.net) (hb : b = par (W C p q + 1))
    (ha : W C p q + 1 = W C p p + 1) :
    InvW w (C.apply p
      { C.loc p with
        hist := Function.update (C.loc p).hist (W C p q + 1) v,
        ws := Function.update (Function.update (C.loc p).ws p (W C p q + 1)) q (W C p q + 1) }
      (sendTo (fun ℓ => Function.update (C.loc p).ws p (W C p q + 1) ℓ = W C p q + 1 - 1)
        (.write (par (W C p q + 1)) v))
      (C.net.erase (q, p, .write b v))) := by
  obtain ⟨hqp, hsq, hv, hqa, hother⟩ := hI.recv_facts hm hb
  set C' := C.apply p _ _ _ with hC'
  -- `p` is not the writer
  have hpw : p ≠ w := by
    rintro rfl
    have := InvW.sent_le_own C q p
    have := hI.own_le q
    omega
  obtain ⟨a, haq⟩ : ∃ a, W C p q = a := ⟨_, rfl⟩
  have hap : W C p p = a := by omega
  have hWp : ∀ j, W C' p j = if j = p ∨ j = q then a + 1 else W C p j := by
    intro j
    by_cases hj : j = q
    · subst hj; simp [hC', W, haq]
    · by_cases hj' : j = p
      · subst hj'; simp [hC', W, hj, haq, Function.update_apply]
      · simp [hC', W, hj, hj', Function.update_apply]
  have hWo : ∀ i, i ≠ p → ∀ j, W C' i j = W C i j := by
    intro i hi j; simp [hC', W, hi]
  have hH : ∀ k, Hw w C' k = Hw w C k := by
    intro k; simp [hC', Hw, Ne.symm hpw]
  have hcnt : ∀ x, C'.net.count x =
      (if x = (q, p, .write b v) then C.net.count x - 1 else C.net.count x) +
        if x.1 = p ∧ (x.2.1 ≠ p ∧ W C p x.2.1 = a) ∧ x.2.2 = .write (par (a + 1)) v then 1 else 0 := by
    intro x
    rw [hC', Config.apply_net, count_erase_add, count_outMsgs_sendTo]
    congr 1
    obtain ⟨i, j, m⟩ := x
    by_cases hj : j = p
    · subst hj; simp [haq]
    · simp [hj, haq, W]
  have hsent_le : ∀ i j, sent C i j ≤ sent C' i j := by
    intro i j
    by_cases hi : i = p
    · subst i; have := hI.ws_le p j; apply sent_mono <;> rw [hWp] <;> split_ifs <;> omega
    · exact sent_mono (by rw [hWo i hi]) (by rw [hWo i hi])
  have hSo : ∀ i j, i ≠ p → sent C' i j = sent C i j := by
    intro i j hi; simp [sent, hWo i hi]
  have hcount_le1 := hI.count_write
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ws_le
    intro i j
    by_cases hi : i = p
    · subst i; rw [hWp, hWp, if_pos (Or.inl rfl)]
      have := hI.ws_le p j; split_ifs <;> omega
    · rw [hWo i hi, hWo i hi]; exact hI.ws_le i j
  · -- recv_le
    intro i j hij
    by_cases hi : i = p
    · subst i
      rw [hWo j (Ne.symm hij)]
      exact (hI.recv_le p j hij).trans (hsent_le p j)
    · rw [hSo i j hi]
      by_cases hj : j = p
      · subst j
        rw [hWp]
        split_ifs with h
        · rcases h with h | rfl
          · exact absurd h hi
          · omega
        · exact hI.recv_le i p hij
      · rw [hWo j hj]; exact hI.recv_le i j hij
  · -- net_write
    intro i j b' v' hpos
    rw [hcnt] at hpos
    by_cases hnew : (i, j, Msg.write b' v').1 = p ∧ ((i, j, Msg.write b' v').2.1 ≠ p ∧
        W C p (i, j, Msg.write b' v').2.1 = a) ∧
        (i, j, Msg.write b' v').2.2 = .write (par (a + 1)) v
    · simp only [Msg.write.injEq] at hnew
      obtain ⟨rfl, ⟨hj, hja⟩, rfl, rfl⟩ := hnew
      refine ⟨Ne.symm hj, a + 1, ?_, ?_, rfl, (hH _).symm ▸ (haq ▸ hv)⟩
      · rw [hWo j hj]
        have := hI.recv_le i j (Ne.symm hj)
        have := InvW.sent_le_own C i j
        omega
      · rw [sent, hWp, hWp, if_pos (Or.inl rfl)]
        split_ifs <;> omega
    · rw [if_neg hnew, Nat.add_zero] at hpos
      have hpos' : 0 < C.net.count (i, j, .write b' v') := by split_ifs at hpos <;> omega
      obtain ⟨hij, k, hk1, hk2, hkb, hkv⟩ := hI.net_write i j b' v' hpos'
      refine ⟨hij, k, ?_, hk2.trans (hsent_le i j), hkb, (hH k).symm ▸ hkv⟩
      by_cases hj : j = p
      · subst j
        rw [hWp]
        split_ifs with h
        · rcases h with h | rfl
          · exact absurd h hij
          · -- the message is not the one being received
            have hne : (b', v') ≠ (b, v) := by
              intro he
              simp only [Prod.mk.injEq] at he
              have := hcount_le1 i p b' v'
              rw [if_pos (by simp [he.1, he.2])] at hpos; omega
            obtain ⟨k', hk', hk'2, hb', hv'⟩ := hother b' v' hne hpos'
            have := hI.count_write i p b' v'
            have h5 := hI.sent_le_two hqp
            rw [hkb, par_eq_iff] at hb'
            omega
        · exact hk1
      · rw [hWo j hj]; exact hk1
  · -- count_write
    intro i j b' v'
    rw [hcnt]
    have h1 := hI.count_write i j b' v'
    by_cases hnew : (i, j, Msg.write b' v').1 = p ∧ ((i, j, Msg.write b' v').2.1 ≠ p ∧
        W C p (i, j, Msg.write b' v').2.1 = a) ∧
        (i, j, Msg.write b' v').2.2 = .write (par (a + 1)) v
    · rw [if_pos hnew]
      simp only [Msg.write.injEq] at hnew
      obtain ⟨rfl, ⟨hj, hja⟩, hb'', hv''⟩ := hnew
      subst b' v'
      rw [if_neg (by simp [hqp.symm])]
      suffices C.net.count (i, j, .write (par (a + 1)) v) = 0 by omega
      by_contra hc
      obtain ⟨-, k, hk1, hk2, hkb, -⟩ := hI.net_write i j _ _ (Nat.pos_of_ne_zero hc)
      have h3 := hI.recv_le j i hj
      have h4 := InvW.sent_le_succ C j i
      have h5 : sent C i j ≤ a := by simp only [sent]; omega
      rw [par_eq_iff] at hkb
      omega
    · rw [if_neg hnew, Nat.add_zero]; split_ifs <;> omega
  · -- exact
    intro i j k hij hi h1 h2
    rw [hcnt]
    by_cases hip : i = p
    · subst i
      rw [hWo j (Ne.symm hij)] at h1
      by_cases hk : k ≤ sent C p j
      · have := hI.exact p j k hij hi h1 hk
        rw [if_neg (by simp [hqp.symm]), hH]; omega
      · -- the new message
        have hsj : sent C p j = min a (W C p j + 1) := by simp [sent, hap]
        have hs'j : sent C' p j = min (a + 1) (W C' p j + 1) := by
          simp only [sent]; rw [hWp p, if_pos (Or.inl rfl)]
        rw [hs'j, hWp] at h2
        have hja : j ≠ p ∧ W C p j = a := by
          refine ⟨Ne.symm hij, ?_⟩
          have := hI.ws_le p j
          split_ifs at h2 with hh
          · rcases hh with hh | rfl
            · exact absurd hh.symm hij
            · omega
          · omega
        have hk' : k = a + 1 := by
          have := hI.ws_le p j
          split_ifs at h2 <;> omega
        subst hk'
        rw [if_neg (by simp [hqp.symm]), if_pos ⟨rfl, hja, by rw [hH, ← haq, hv]⟩]; omega
    · rw [hSo i j hip] at h2
      rw [hH]
      by_cases hj : j = p
      · subst j
        rw [hWp] at h1
        split_ifs at h1 with hh
        · rcases hh with hh | rfl
          · exact absurd hh hij
          · -- channel q → p: `k ≥ a + 2`
            have := hI.exact i p k hij hi (by omega) h2
            have hne : (i, p, Msg.write (par k) (Hw w C k)) ≠ (i, p, .write b v) := by
              intro he
              simp only [Prod.mk.injEq, Msg.write.injEq, true_and] at he
              rw [hb, par_eq_iff] at he
              have := hI.sent_le_two hqp
              omega
            rw [if_neg hne]; omega
        · have := hI.exact i p k hij hi h1 h2
          have hne : (i, p, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
            intro he; simp only [Prod.mk.injEq] at he; exact hh (Or.inr he.1)
          rw [if_neg hne]; omega
      · rw [hWo j hj] at h1
        have := hI.exact i j k hij hi h1 h2
        have hne : (i, j, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hj he.2.1
        rw [if_neg hne]; omega
  · -- hist
    intro i k hk
    rw [hH]
    by_cases hi : i = p
    · subst i
      rw [hWp, if_pos (Or.inl rfl)] at hk
      simp only [hC', Config.apply_loc', ite_true]
      rcases Nat.lt_or_ge k (a + 1) with hlt | hge
      · rw [Function.update_of_ne (by omega)]; exact hI.hist p k (by omega)
      · have : k = a + 1 := by omega
        subst this
        rw [haq, Function.update_self, hv, haq]
    · rw [hWo i hi] at hk
      simp only [hC', Config.apply_loc', hi, ite_false]
      exact hI.hist i k hk
  · -- own_le
    intro i
    rw [hWo w (Ne.symm hpw)]
    by_cases hi : i = p
    · subst i; rw [hWp, if_pos (Or.inl rfl)]
      have := InvW.sent_le_own C q p
      have := hI.own_le q
      omega
    · rw [hWo i hi]; exact hI.own_le i

/-- Lines 16 and 18: `p` already knows the value; it helps `q` catch up if `q` lags. -/
lemma InvW.of_recv_old {w : P} {C : Cfg P V} (hI : InvW w C) {p q : P} {b : Bool} {v : V}
    (hm : (q, p, Msg.write b v) ∈ C.net) (hb : b = par (W C p q + 1))
    {out : Multiset (P × Msg V)}
    (hout : (W C p q + 1 < W C p p ∧
        out = {(q, .write (par (W C p q + 1 + 1)) ((C.loc p).hist (W C p q + 1 + 1)))}) ∨
      (W C p q + 1 = W C p p ∧ out = 0)) :
    InvW w (C.apply p { C.loc p with ws := Function.update (C.loc p).ws q (W C p q + 1) }
      out (C.net.erase (q, p, .write b v))) := by
  obtain ⟨hqp, hsq, hv, hqa, hother⟩ := hI.recv_facts hm hb
  set C' := C.apply p _ _ _ with hC'
  obtain ⟨a, haq⟩ : ∃ a, W C p q = a := ⟨_, rfl⟩
  obtain ⟨o, hop⟩ : ∃ o, W C p p = o := ⟨_, rfl⟩
  have hao : a + 1 ≤ o := by rcases hout with h | h <;> omega
  have hWp : ∀ j, W C' p j = if j = q then a + 1 else W C p j := by
    intro j
    by_cases hj : j = q
    · subst hj; simp [hC', W, haq]
    · simp [hC', W, hj]
  have hWo : ∀ i, i ≠ p → ∀ j, W C' i j = W C i j := by
    intro i hi j; simp [hC', W, hi]
  have hWpp : W C' p p = o := by rw [hWp, if_neg (Ne.symm hqp), hop]
  have hH : ∀ k, Hw w C' k = Hw w C k := by
    intro k
    by_cases hpw : w = p
    · subst hpw; simp [hC', Hw]
    · simp [hC', Hw, hpw]
  -- the message sent at line 16, if any
  have hcnt : ∀ x, C'.net.count x =
      (if x = (q, p, .write b v) then C.net.count x - 1 else C.net.count x) +
        if a + 1 < o ∧ x = (p, q, .write (par (a + 2)) (Hw w C (a + 2))) then 1 else 0 := by
    intro x
    rw [hC', Config.apply_net, count_erase_add]
    congr 1
    rcases hout with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · rw [count_outMsgs_single, haq, hI.hist p (a + 1 + 1) (by omega)]
      simp only [show a + 1 + 1 = a + 2 by rfl]
      by_cases hx : x = (p, q, .write (par (a + 2)) (Hw w C (a + 2)))
      · rw [if_pos hx, if_pos ⟨by omega, hx⟩]
      · rw [if_neg hx, if_neg (fun h => hx h.2)]
    · rw [outMsgs_zero, Multiset.count_zero, if_neg (by omega)]
  have hsent_le : ∀ i j, sent C i j ≤ sent C' i j := by
    intro i j
    by_cases hi : i = p
    · subst i; have := hI.ws_le p j
      apply sent_mono
      · rw [hWpp, hop]
      · rw [hWp]; split_ifs with h
        · rw [h]; omega
        · exact le_refl _
    · exact sent_mono (by rw [hWo i hi]) (by rw [hWo i hi])
  have hSo : ∀ i j, i ≠ p → sent C' i j = sent C i j := by
    intro i j hi; simp [sent, hWo i hi]
  have hsentpq : sent C p q = a + 1 := by simp only [sent]; omega
  have hsent'pq : sent C' p q = min o (a + 2) := by
    simp only [sent]; rw [hWpp, hWp, if_pos rfl]
  have hSpj : ∀ j, j ≠ q → sent C' p j = sent C p j := by
    intro j hj; simp only [sent]; rw [hWpp, hWp, if_neg hj, hop]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ws_le
    intro i j
    by_cases hi : i = p
    · subst i; rw [hWp, hWpp]; have := hI.ws_le p j; split_ifs <;> omega
    · rw [hWo i hi, hWo i hi]; exact hI.ws_le i j
  · -- recv_le
    intro i j hij
    by_cases hi : i = p
    · subst i
      rw [hWo j (Ne.symm hij)]
      exact (hI.recv_le p j hij).trans (hsent_le p j)
    · rw [hSo i j hi]
      by_cases hj : j = p
      · subst j
        rw [hWp]
        split_ifs with h
        · subst i; omega
        · exact hI.recv_le i p hij
      · rw [hWo j hj]; exact hI.recv_le i j hij
  · -- net_write
    intro i j b' v' hpos
    rw [hcnt] at hpos
    by_cases hnew : a + 1 < o ∧ (i, j, Msg.write b' v') = (p, q, .write (par (a + 2)) (Hw w C (a + 2)))
    · obtain ⟨hlt, he⟩ := hnew
      simp only [Prod.mk.injEq, Msg.write.injEq] at he
      obtain ⟨hi1, hj1, hb1, hv1⟩ := he
      subst i j b' v'
      refine ⟨hqp.symm, a + 2, ?_, ?_, rfl, (hH _).symm⟩
      · rw [hWo q hqp]; have := hI.recv_le p q hqp.symm; omega
      · rw [hsent'pq]; omega
    · rw [if_neg hnew, Nat.add_zero] at hpos
      have hpos' : 0 < C.net.count (i, j, .write b' v') := by split_ifs at hpos <;> omega
      obtain ⟨hij, k, hk1, hk2, hkb, hkv⟩ := hI.net_write i j b' v' hpos'
      refine ⟨hij, k, ?_, hk2.trans (hsent_le i j), hkb, (hH k).symm ▸ hkv⟩
      by_cases hj : j = p
      · subst j
        rw [hWp]
        split_ifs with h
        · subst i
          have hne : (b', v') ≠ (b, v) := by
            intro he
            simp only [Prod.mk.injEq] at he
            have := hI.count_write q p b' v'
            rw [if_pos (by simp [he.1, he.2])] at hpos; omega
          obtain ⟨k', hk', hk'2, hb', hv'⟩ := hother b' v' hne hpos'
          have h5 := hI.sent_le_two hqp
          rw [hkb, par_eq_iff] at hb'
          omega
        · exact hk1
      · rw [hWo j hj]; exact hk1
  · -- count_write
    intro i j b' v'
    rw [hcnt]
    have h1 := hI.count_write i j b' v'
    by_cases hnew : a + 1 < o ∧ (i, j, Msg.write b' v') = (p, q, .write (par (a + 2)) (Hw w C (a + 2)))
    · rw [if_pos hnew]
      obtain ⟨hlt, he⟩ := hnew
      have hne : (i, j, Msg.write b' v') ≠ (q, p, .write b v) := by
        rw [he]; simp [hqp.symm]
      rw [if_neg hne, he]
      suffices C.net.count (p, q, .write (par (a + 2)) (Hw w C (a + 2))) = 0 by omega
      by_contra hc
      obtain ⟨-, k, hk1, hk2, hkb, -⟩ := hI.net_write p q _ _ (Nat.pos_of_ne_zero hc)
      rw [hsentpq] at hk2
      rw [par_eq_iff] at hkb
      omega
    · rw [if_neg hnew, Nat.add_zero]; split_ifs <;> omega
  · -- exact
    intro i j k hij hi h1 h2
    rw [hcnt, hH]
    by_cases hip : i = p
    · subst i
      rw [hWo j (Ne.symm hij)] at h1
      have hne : (p, j, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
        simp [hqp.symm]
      rw [if_neg hne]
      by_cases hk : k ≤ sent C p j
      · have := hI.exact p j k hij hi h1 hk; omega
      · by_cases hjq : j = q
        · subst j
          rw [hsent'pq] at h2; rw [hsentpq] at hk
          have hk' : k = a + 2 := by omega
          subst hk'
          rw [if_pos ⟨by omega, rfl⟩]; omega
        · rw [hSpj j hjq] at h2; exact absurd h2 hk
    · rw [hSo i j hip] at h2
      by_cases hj : j = p
      · subst j
        rw [hWp] at h1
        split_ifs at h1 with hh
        · subst i
          have := hI.exact q p k hij hi (by omega) h2
          have hne : (q, p, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
            intro he
            simp only [Prod.mk.injEq, Msg.write.injEq, true_and] at he
            rw [hb, par_eq_iff] at he
            have := hI.sent_le_two hqp
            omega
          rw [if_neg hne]; omega
        · have := hI.exact i p k hij hi h1 h2
          have hne : (i, p, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
            intro he; simp only [Prod.mk.injEq] at he; exact hh he.1
          rw [if_neg hne]; omega
      · rw [hWo j hj] at h1
        have := hI.exact i j k hij hi h1 h2
        have hne : (i, j, Msg.write (par k) (Hw w C k)) ≠ (q, p, .write b v) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hj he.2.1
        rw [if_neg hne]; omega
  · -- hist
    intro i k hk
    rw [hH]
    by_cases hi : i = p
    · subst i
      rw [hWpp] at hk
      simp only [hC', Config.apply_loc', ite_true]
      exact hI.hist p k (by omega)
    · rw [hWo i hi] at hk
      simp only [hC', Config.apply_loc', hi, ite_false]
      exact hI.hist i k hk
  · -- own_le
    intro i
    have hw : W C' w w = W C w w := by
      by_cases hpw : w = p
      · subst hpw; rw [hWpp, hop]
      · exact hWo w hpw w
    rw [hw]
    by_cases hi : i = p
    · subst i; rw [hWpp, ← hop]; exact hI.own_le p
    · rw [hWo i hi]; exact hI.own_le i

/-! ## All other transitions -/

lemma InvW.apply_nonwrite {w : P} {C : Cfg P V} (hI : InvW w C) {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} {net : Multiset (P × P × Msg V)}
    (hws : l.ws = (C.loc p).ws) (hh : l.hist = (C.loc p).hist)
    (hout : ∀ x ∈ out, ∀ b v, x.2 ≠ .write b v)
    (hnet : ∀ i j b v, net.count (i, j, .write b v) = C.net.count (i, j, .write b v)) :
    InvW w (C.apply p l out net) := by
  have hz : ∀ i j b v, (outMsgs p out).count (i, j, Msg.write b v) = 0 := by
    intro i j b v
    rw [Multiset.count_eq_zero]
    intro hx
    simp only [outMsgs, Multiset.mem_map] at hx
    obtain ⟨y, hy, he⟩ := hx
    simp only [Prod.mk.injEq] at he
    exact hout y hy b v he.2.2
  refine hI.frame ?_ ?_ ?_ ?_ (by simp)
  · intro i; by_cases hi : i = p <;> simp [hi, hws]
  · intro i; by_cases hi : i = p <;> simp [hi, hh]
  · intro i j b v; simp [Multiset.count_add, hz, hnet]
  · intro i j b v _; simp [Multiset.count_add, hz, hnet]

/-- **Lemmas 1–5**: `InvW` holds in every reachable configuration. -/
theorem invW_of_reach {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : (alg w t v₀).Reach C h) : InvW w C := by
  induction hr with
  | init => exact invW_init w t v₀
  | @step C h s C' ℓ hr hs ih =>
    cases s with
    | inv p o =>
      obtain ⟨-, -, l, out, hinv, rfl⟩ := step_inv hs
      cases o with
      | write v => exact ih.of_invoke_write hinv
      | read =>
        obtain ⟨-, -, rfl, rfl⟩ := invoke_read hinv
        refine ih.apply_nonwrite rfl rfl ?_ (fun _ _ _ _ => rfl)
        intro x hx b v
        simp only [sendTo, Multiset.mem_map] at hx
        obtain ⟨_, _, rfl⟩ := hx
        simp
    | internal p a =>
      obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal hs
      cases a with
      | wret =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint
        exact ih.apply_nonwrite rfl rfl (by simp) (fun _ _ _ _ => rfl)
      | r8 =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
        exact ih.apply_nonwrite rfl rfl (by simp) (fun _ _ _ _ => rfl)
      | rret =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint
        exact ih.apply_nonwrite rfl rfl (by simp) (fun _ _ _ _ => rfl)
      | proceed j sn =>
        obtain ⟨-, -, rfl, rfl, -⟩ := internal_proceed hint
        exact ih.apply_nonwrite rfl rfl (by simp) (fun _ _ _ _ => rfl)
    | recv src dst m =>
      obtain ⟨-, hm, l, out, r, hrc, rfl, -⟩ := step_recv hs
      cases m with
      | write b v =>
        obtain ⟨hb, -, hcase⟩ := receive_write hrc
        rcases hcase with ⟨ha, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩ | ⟨heq, rfl, rfl⟩ | himp
        · exact ih.of_recv_adopt hm hb ha
        · exact ih.of_recv_old hm hb (Or.inl ⟨hlt, rfl⟩)
        · exact ih.of_recv_old hm hb (Or.inr ⟨heq, rfl⟩)
        · have := ih.ws_le dst src; simp only [W] at this; omega
      | read =>
        obtain ⟨rfl, rfl, -⟩ := receive_read hrc
        refine ih.apply_nonwrite rfl rfl (by simp) ?_
        intro i j b v
        rw [Multiset.count_erase_of_ne (by simp)]
      | proceed =>
        obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
        refine ih.apply_nonwrite rfl rfl (by simp) ?_
        intro i j b v
        rw [Multiset.count_erase_of_ne (by simp)]
    | drop src dst m =>
      obtain ⟨hsrc, -, -, rfl⟩ := step_drop hs
      refine ih.frame (fun _ => rfl) (fun _ => rfl) ?_ ?_ (fun _ h => h)
      · intro i j b v
        by_cases he : (i, j, Msg.write b v) = (src, dst, m)
        · rw [he, Multiset.count_erase_self]; omega
        · rw [Multiset.count_erase_of_ne he]
      · intro i j b v hi
        have he : (i, j, Msg.write b v) ≠ (src, dst, m) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hi (he.1 ▸ hsrc)
        rw [Multiset.count_erase_of_ne he]
    | crash p =>
      obtain ⟨-, -, rfl⟩ := step_crash hs
      exact ih.frame (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => le_refl _)
        (fun _ _ _ _ _ => le_refl _) (Finset.subset_insert _ _)
    | skip =>
      obtain ⟨rfl, -⟩ := step_skip hs
      exact ih

end Podc.TwoBit
