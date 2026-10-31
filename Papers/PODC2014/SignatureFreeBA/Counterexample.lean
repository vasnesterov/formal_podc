import Papers.PODC2014.SignatureFreeBA.Embed
import Papers.PODC2014.SignatureFreeBA.Liveness

/-!
# Counterexample to Lemma 5 (termination) and Theorem 3

Mostéfaoui, Moumen, Raynal, PODC 2014, Lemma 5 ("each non-faulty process decides with
probability 1"), Theorem 2 (BC-Termination) and Theorem 3 ("the expected decision time is …
four rounds").

For `n = 4`, `t = 1`, inputs `0, 0, 1` and process `3` Byzantine we give an adversary
`strat : ℕ → State → Ev`. It chooses the next event from the time and the current global state
only. The global state contains the coins already used by some process (through the estimates
they produced), and nothing about the other coins, so the adversary cannot see future coins.
This is the adversary of the paper's model: it controls the message schedule and the Byzantine
process, and the coin of a round becomes known once a correct process has obtained it
(Section 4.1 asks only that the Byzantine processes cannot compute coins *in advance*).

`counterexample`: for **every** coin sequence the generated execution is a weakly fair
execution of the algorithm in which no process ever decides. So the probability of
termination is `0` for every distribution of the coins (`prob_termination_eq_zero`).

The round-by-round schedule is `Local.script` (checked by `decide` in `Local.lean`); here we
glue the rounds together: `gen_eq` computes the whole execution in closed form.
-/

namespace Podc.SignatureFreeBA.Attack

open Cslib.Byzantine.AsyncBroadcast Podc.SignatureFreeBA Podc.SignatureFreeBA.Local

/-! ### The execution in closed form -/

/-- The estimate of processes `0, 1` at the start of round `r` (process `2` has the other
value). -/
def aR (coin : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | 1 => false
  | r + 2 => coin (r + 1)

/-- The tag of process `2`'s estimate at round `r` (`true` from round 2 on: its `values` was a
singleton). -/
def d2R (r : ℕ) : Bool := decide (2 ≤ r)

/-- The schedule of round `r`. -/
def scr (coin : ℕ → Bool) (r : ℕ) : List LE := script (aR coin r) (d2R r) (coin r)

/-- Round `r` after the first `k` events of its schedule. -/
def part (coin : ℕ → Bool) (r k : ℕ) : LS :=
  run (coin r) (start (aR coin r) (d2R r)) ((scr coin r).take k)

/-- All rounds while round `r` is at position `k`. -/
def Lc (coin : ℕ → Bool) (r k : ℕ) : ℕ → LS := fun r' =>
  if r' = 0 then empty else if r' < r then part coin r' 62 else if r' = r then part coin r k
  else empty

/-- Round 1 while the first `j` processes have broadcast their input. -/
def own0 (j : ℕ) : LS := { empty with sent := fun p m => decide (p.val < j) && (start false false).sent p m }

/-- All rounds during the first four steps. -/
def L0 (j : ℕ) : ℕ → LS := fun r' => if r' = 1 then own0 j else empty

/-- The round at time `i ≥ 4`. -/
def seg (i : ℕ) : ℕ := (i - 4) / 62 + 1

/-- The position in the round at time `i ≥ 4`. -/
def pos (i : ℕ) : ℕ := (i - 4) % 62

/-- The global state at time `i`. -/
def G (coin : ℕ → Bool) (i : ℕ) : State Pr Msg Bool :=
  if i < 4 then asm (L0 i) ∅ else asm (Lc coin (seg i) (pos i)) {3}

/-! ### The adversary -/

/-- The first four events: processes `0, 1, 2` start round 1, then `3` is corrupted. -/
def ev0 : ℕ → Ev
  | 0 => .send 0 (.bval 1 false (some false))
  | 1 => .send 1 (.bval 1 false (some false))
  | 2 => .send 2 (.bval 1 true (some false))
  | _ => .corrupt 3

open Classical in
/-- The estimate of process `0` for round `r`, read from a global state. -/
noncomputable def readEst (σ : State Pr Msg Bool) (r : ℕ) : Bool :=
  decide ((0, Msg.bval r true (some false)) ∈ σ.sent)

/-- **The adversary.** At time `i ≥ 4` (round `r`, position `k`) it reads the estimate `a` of
process `0` for round `r` and, once process `0` has called `random()` in round `r`, its
estimate `s` for round `r + 1` (= the coin of round `r`) from the global state, and plays the
`k`-th event of the schedule `script a d2 s`. Before process `0` has called `random()` the
schedule does not depend on `s` (`script_getElem_pre`). -/
noncomputable def strat (i : ℕ) (σ : State Pr Msg Bool) : Ev :=
  if i < 4 then ev0 i
  else embedEv (seg i) ((script (readEst σ (seg i)) (d2R (seg i)) (readEst σ (seg i + 1))).getD
    (pos i) .skip)

/-! ### Facts about the rounds -/

theorem LS.ext' {ℓ ℓ' : LS} (h1 : ℓ.sent = ℓ'.sent) (h2 : ℓ.rcv = ℓ'.rcv) (h3 : ℓ.nxt = ℓ'.nxt) :
    ℓ = ℓ' := by
  cases ℓ; cases ℓ'; simp_all

theorem scr_length (coin : ℕ → Bool) (r : ℕ) : (scr coin r).length = 62 := script_length _ _ _

theorem part_full (coin : ℕ → Bool) (r : ℕ) :
    part coin r 62 = final (aR coin r) (d2R r) (coin r) := by
  unfold part final
  rw [← scr_length coin r, List.take_length]
  rfl

theorem part_own (coin : ℕ → Bool) (r k : ℕ) (p : Pr) (v d : Bool) :
    (part coin r k).sent p (.bval v (some d)) = (start (aR coin r) (d2R r)).sent p (.bval v (some d)) :=
  run_sent_own _ _ _ _ _ _

theorem part_nxt (coin : ℕ → Bool) (r k : ℕ) (hk : k ≤ 62) (p : Pr) :
    (part coin r k).nxt p = none ∨ (part coin r k).nxt p = (part coin r 62).nxt p := by
  rw [part_full]; exact prefix_nxt _ _ _ k hk p

theorem final_nxt' (coin : ℕ → Bool) (r : ℕ) (p : Pr) (v d : Bool)
    (h : (part coin r 62).nxt p = some (v, d)) :
    (p = 0 ∧ v = coin r ∧ d = false) ∨ (p = 1 ∧ v = coin r ∧ d = false) ∨
      (p = 2 ∧ v = !coin r ∧ d = true) := by
  rw [part_full] at h
  obtain ⟨h0, h1, h2, h3⟩ := final_nxt (aR coin r) (d2R r) (coin r)
  fin_cases p <;> simp_all

/-- The estimates computed in round `r ≥ 1` are the own broadcasts of round `r + 1`. -/
theorem nxt_iff_start (coin : ℕ → Bool) (r : ℕ) (hr : 1 ≤ r) (p : Pr) (v d : Bool) :
    (part coin r 62).nxt p = some (v, d) ↔
      (start (aR coin (r + 1)) (d2R (r + 1))).sent p (.bval v (some d)) = true := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have ha : aR coin (r + 1 + 1) = coin (r + 1) := rfl
  have hd : d2R (r + 1 + 1) = true := by simp [d2R]
  rw [ha, hd, part_full]
  obtain ⟨h0, h1, h2, h3⟩ := final_nxt (aR coin (r + 1)) (d2R (r + 1)) (coin (r + 1))
  fin_cases p <;> cases v <;> cases d <;> simp_all [start]

theorem Lc_cur (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) : Lc coin r k r = part coin r k := by
  unfold Lc; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem Lc_lt (coin : ℕ → Bool) (r k r' : ℕ) (h1 : 1 ≤ r') (h : r' < r) :
    Lc coin r k r' = part coin r' 62 := by
  unfold Lc; rw [ite_eq_right (by omega), ite_eq_left h]

theorem Lc_zero (coin : ℕ → Bool) (r k : ℕ) : Lc coin r k 0 = empty := by
  unfold Lc; rw [ite_eq_left rfl]

theorem Lc_gt (coin : ℕ → Bool) (r k r' : ℕ) (h : r < r') : Lc coin r k r' = empty := by
  unfold Lc; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Own estimates of round `r ≤ R` in the assembled state. -/
theorem mem_est_iff (coin : ℕ → Bool) (R k : ℕ) (B : Set Pr) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ R)
    (p : Pr) (v d : Bool) :
    (p, .bval r v (some d)) ∈ (asm (Lc coin R k) B).sent ↔
      (start (aR coin r) (d2R r)).sent p (.bval v (some d)) = true := by
  rw [mem_sent_asm]
  have hl : (Lc coin R k (rnd (.bval r v (some d)))).sent p (loc (.bval r v (some d))) =
      (start (aR coin r) (d2R r)).sent p (.bval v (some d)) := by
    simp only [rnd, loc]
    rcases lt_or_eq_of_le h2 with h | h
    · rw [Lc_lt coin R k r h1 h, part_own]
    · subst h; rw [Lc_cur coin r k h1, part_own]
  rw [hl]
  constructor
  · rintro (h | ⟨r', v', d', he, hn⟩)
    · exact h
    · simp only [Msg.bval.injEq, Option.some.injEq] at he
      obtain ⟨hr, rfl, rfl⟩ := he
      subst hr
      rcases Nat.eq_zero_or_pos r' with h0 | h0
      · subst h0; rw [Lc_zero] at hn; exact absurd hn (by simp [empty])
      · rw [Lc_lt coin R k r' h0 (by omega)] at hn
        exact (nxt_iff_start coin r' h0 p _ _).1 hn
  · exact Or.inl

/-- Own estimates of round `R + 1` in the assembled state: those computed in round `R`. -/
theorem mem_est_next_iff (coin : ℕ → Bool) (R k : ℕ) (B : Set Pr) (h1 : 1 ≤ R) (p : Pr)
    (v d : Bool) :
    (p, .bval (R + 1) v (some d)) ∈ (asm (Lc coin R k) B).sent ↔ (part coin R k).nxt p = some (v, d) := by
  rw [mem_sent_asm]
  simp only [rnd, loc, Lc_gt coin R k (R + 1) (by omega)]
  constructor
  · rintro (h | ⟨r', v', d', he, hn⟩)
    · simp [empty] at h
    · simp only [Msg.bval.injEq, Option.some.injEq, Nat.add_right_cancel_iff] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rwa [Lc_cur coin R k h1] at hn
  · intro h
    exact Or.inr ⟨R, v, d, rfl, by rw [Lc_cur coin R k h1]; exact h⟩

/-- No own estimates beyond round `R + 1`, nor for round 0. -/
theorem not_mem_est_far (coin : ℕ → Bool) (R k : ℕ) (B : Set Pr) (r : ℕ) (h : r = 0 ∨ R + 1 < r)
    (p : Pr) (v : Bool) (d : Option Bool) : (p, .bval r v d) ∉ (asm (Lc coin R k) B).sent := by
  rw [mem_sent_asm]
  rintro (h' | ⟨r', v', d', he, hn⟩)
  · simp only [rnd, loc] at h'
    rcases h with rfl | h
    · rw [Lc_zero] at h'; simp [empty] at h'
    · rw [Lc_gt coin R k r (by omega)] at h'; simp [empty] at h'
  · simp only [Msg.bval.injEq] at he
    obtain ⟨rfl, -, -⟩ := he
    rcases h with h | h
    · omega
    · rw [Lc_gt coin R k r' (by omega)] at hn; simp [empty] at hn

theorem readEst_cur (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) :
    readEst (asm (Lc coin r k) {3}) r = aR coin r := by
  unfold readEst
  have h := mem_est_iff coin r k {3} r hr le_rfl 0 true false
  cases ha : aR coin r <;> simp only [start, ha] at h <;> simp [h]

theorem readEst_next (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ 62) (hk' : 21 ≤ k) :
    readEst (asm (Lc coin r k) {3}) (r + 1) = coin r := by
  unfold readEst
  have h := mem_est_next_iff coin r k {3} hr 0 true false
  have := prefix_nxt0 (aR coin r) (d2R r) (coin r) k hk hk'
  change (part coin r k).nxt 0 = _ at this
  rw [this] at h
  cases hc : coin r <;> simp_all

theorem seg_pos (i : ℕ) : 1 ≤ seg i := by unfold seg; omega

theorem pos_lt (i : ℕ) : pos i < 62 := by unfold pos; omega

theorem G_ge (coin : ℕ → Bool) (i : ℕ) (hi : 4 ≤ i) :
    G coin i = asm (Lc coin (seg i) (pos i)) {3} := by
  unfold G; rw [ite_eq_right (by omega)]

theorem G_lt (coin : ℕ → Bool) (i : ℕ) (hi : i < 4) : G coin i = asm (L0 i) ∅ := by
  unfold G; rw [ite_eq_left hi]

/-- The adversary plays the schedule of the current round. -/
theorem strat_G (coin : ℕ → Bool) (i : ℕ) (hi : 4 ≤ i) :
    strat i (G coin i) = embedEv (seg i) ((scr coin (seg i))[pos i]'(by
      rw [scr_length]; exact pos_lt i)) := by
  unfold strat
  rw [ite_eq_right (by omega), G_ge coin i hi, readEst_cur coin _ _ (seg_pos i)]
  congr 1
  have hl : pos i < (script (aR coin (seg i)) (d2R (seg i))
      (readEst (asm (Lc coin (seg i) (pos i)) {3}) (seg i + 1))).length := by
    rw [script_length]; exact pos_lt i
  by_cases hk : pos i < 28
  · rw [List.getD_eq_getElem _ _ hl]
    unfold scr
    rw [script_getElem_pre _ _ _ _ hk, script_getElem_pre _ _ _ _ hk]
  · rw [readEst_next coin _ _ (seg_pos i) (pos_lt i).le (by omega)]
    exact List.getD_eq_getElem _ _ _

theorem frame_Lc (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) : Frame (Lc coin r k) r where
  pos := hr
  cons p v d h := by
    rw [Lc_cur coin r k hr, part_own]
    rcases Nat.lt_or_ge 1 r with h1 | h1
    · rw [Lc_lt coin r k (r - 1) (by omega) (by omega)] at h
      have := (nxt_iff_start coin (r - 1) (by omega) p v d).1 h
      rwa [Nat.sub_add_cancel hr] at this
    · have : r - 1 = 0 := by omega
      rw [this, Lc_zero] at h
      simp [empty] at h
  next p m := by rw [Lc_gt coin r k (r + 1) (by omega)]; rfl

/-- One step of the schedule of round `r`. -/
theorem apply_G (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) (hk : k < 62) :
    apply coin (embedEv r ((scr coin r)[k]'(by rw [scr_length]; exact hk))) (asm (Lc coin r k) {3}) =
      asm (Function.update (Lc coin r k) r (part coin r (k + 1))) {3} := by
  have hk' : k < (scr coin r).length := by rw [scr_length]; exact hk
  have hg : guard (Lc coin r k r) (scr coin r)[k] := by
    rw [Lc_cur coin r k hr]
    exact Valid.guard _ _ _ (valid_script _ _ _) k hk'
  rw [apply_embed coin _ r (frame_Lc coin r k hr) _ hg, Lc_cur coin r k hr]
  congr 2
  unfold part
  rw [run_take_succ _ _ _ _ hk']

theorem update_Lc (coin : ℕ → Bool) (r k : ℕ) (hr : 1 ≤ r) :
    Function.update (Lc coin r k) r (part coin r (k + 1)) = Lc coin r (k + 1) := by
  funext r'
  by_cases h : r' = r
  · subst h; rw [Function.update_self, Lc_cur coin r' _ hr]
  · rw [Function.update_of_ne h]
    unfold Lc
    split_ifs <;> rfl

/-- End of a round: the next round starts with the estimates computed in this one. -/
theorem update_Lc_last (coin : ℕ → Bool) (r : ℕ) (hr : 1 ≤ r) :
    asm (Function.update (Lc coin r 61) r (part coin r 62)) {3} = asm (Lc coin (r + 1) 0) {3} := by
  have hL : ∀ r', r' ≠ r + 1 → Function.update (Lc coin r 61) r (part coin r 62) r' =
      Lc coin (r + 1) 0 r' := by
    intro r' hr'
    by_cases h : r' = r
    · subst h; rw [Function.update_self, Lc_lt coin (r' + 1) 0 r' hr (by omega)]
    · rw [Function.update_of_ne h]
      unfold Lc
      split_ifs <;> first | rfl | omega
  have hA : Function.update (Lc coin r 61) r (part coin r 62) (r + 1) = empty := by
    rw [Function.update_of_ne (by omega), Lc_gt coin r 61 (r + 1) (by omega)]
  have hB : Lc coin (r + 1) 0 (r + 1) = start (aR coin (r + 1)) (d2R (r + 1)) := by
    rw [Lc_cur coin (r + 1) 0 (by omega)]; rfl
  have hnx : ∀ r' p, (Function.update (Lc coin r 61) r (part coin r 62) r').nxt p =
      (Lc coin (r + 1) 0 r').nxt p := by
    intro r' p
    by_cases h : r' = r + 1
    · subst h; rw [hA, hB]; rfl
    · rw [hL r' h]
  have hns : ∀ p m, NxtSent (Function.update (Lc coin r 61) r (part coin r 62)) p m ↔
      NxtSent (Lc coin (r + 1) 0) p m := by
    intro p m; unfold NxtSent; simp only [hnx]
  refine state_eq ?_ ?_ rfl rfl
  · ext ⟨p, m⟩
    simp only [asm, Set.mem_ofPred_eq, hns]
    by_cases h : rnd m = r + 1
    · rw [h, hA, hB]
      constructor
      · rintro (h' | h')
        · simp [empty] at h'
        · exact Or.inr h'
      · rintro (h' | h')
        · right
          cases m with
          | aux r'' w => simp [loc, start] at h'
          | bval r'' v d =>
            simp only [rnd] at h
            subst h
            cases d with
            | none => simp [loc, start] at h'
            | some d =>
              refine ⟨r, v, d, rfl, ?_⟩
              rw [Lc_lt coin (r + 1) 0 r hr (by omega)]
              exact (nxt_iff_start coin r hr p v d).2 h'
        · exact Or.inr h'
    · rw [hL _ h]
  · ext ⟨a, b, m⟩
    simp only [asm, Set.mem_ofPred_eq]
    by_cases h : rnd m = r + 1
    · rw [h, hA, hB]; simp [empty, start]
    · rw [hL _ h]

/-- **When the adversary uses the coin.** The schedule of round `r` depends on the coin of
round `r` only from position 28 on, when processes `0` and `1` have already called `random()`
in round `r` (and on the coins of earlier rounds). So the adversary never needs a coin before
two correct processes (and the Byzantine one) have asked for it: a threshold coin revealed by
`n − t` shares gives it this information. -/
theorem coin_used_late (coin coin' : ℕ → Bool) (r k : ℕ) (hk : k < 62)
    (h : ∀ r' < r, coin r' = coin' r')
    (hne : (scr coin r).getD k .skip ≠ (scr coin' r).getD k .skip) :
    28 ≤ k ∧ (part coin r k).nxt 0 ≠ none ∧ (part coin r k).nxt 1 ≠ none := by
  have ha : aR coin r = aR coin' r := by
    match r, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | r + 2, h => exact h (r + 1) (by omega)
  have h28 : 28 ≤ k := by
    by_contra hlt
    apply hne
    unfold scr script
    rw [List.getD_append _ _ _ _ (by rw [pre_length]; omega),
      List.getD_append _ _ _ _ (by rw [pre_length]; omega), ha]
  refine ⟨h28, ?_, ?_⟩
  · have := prefix_nxt0 (aR coin r) (d2R r) (coin r) k hk.le (by omega)
    change (part coin r k).nxt 0 = _ at this
    simp [this]
  · have := prefix_nxt1 (aR coin r) (d2R r) (coin r) k hk.le h28
    change (part coin r k).nxt 1 = _ at this
    simp [this]

/-! ### The first four steps -/

theorem own0_succ : ∀ p : Pr, p.val < 3 → ∀ a (c : LM),
    (decide (a.val < p.val + 1) && (start false false).sent a c) =
      ((a == p && c == .bval (x0 p) (some false)) || (decide (a.val < p.val) && (start false false).sent a c)) := by
  decide

theorem L0_succ (j : ℕ) :
    L0 (j + 1) = Function.update (L0 j) 1 (own0 (j + 1)) := by
  funext r'
  by_cases h : r' = 1
  · subst h; simp [L0]
  · rw [Function.update_of_ne h]; simp [L0, h]

theorem apply_seg0 (coin : ℕ → Bool) (p : Pr) (hp : p.val < 3) :
    apply coin (.send p (.bval 1 (x0 p) (some false))) (asm (L0 p.val) ∅) = asm (L0 (p.val + 1)) ∅ := by
  have hg : p ∉ (asm (L0 p.val) ∅).bad ∧ (mmr 1 coin).send p (x0 p) ((asm (L0 p.val) ∅).inbox p)
      ((asm (L0 p.val) ∅).out p) (.bval 1 (x0 p) (some false)) := by
    refine ⟨Set.notMem_empty p, rfl, rfl, ?_⟩
    rintro m (hm | ⟨r, v, d, rfl, hn⟩) ⟨v', d', hm'⟩
    · subst hm'
      simp [L0, own0, rnd, loc] at hm
    · simp only [L0, own0, empty] at hn
      split_ifs at hn
  simp only [apply]
  rw [ite_eq_left hg, L0_succ p.val]
  refine (asm_update_sent (L0 p.val) ∅ 1 (own0 (p.val + 1)) ?_ ?_ p (.bval (x0 p) (some false)) ?_).symm
  · simp [L0, own0]
  · simp [L0, own0]
  · intro a c
    simp only [L0, ite_true, own0]
    exact own0_succ p hp a c

theorem L0_three (coin : ℕ → Bool) : L0 3 = Lc coin 1 0 := by
  funext r'
  by_cases h : r' = 1
  · subst h
    rw [Lc_cur coin 1 0 le_rfl]
    refine LS.ext' ?_ rfl rfl
    funext a c
    simp only [L0, ite_true, own0, part, scr, List.take_zero, run]
    revert a c
    show ∀ a c, (decide (a.val < 3) && (start false false).sent a c) = (start false false).sent a c
    decide
  · rcases Nat.eq_zero_or_pos r' with h0 | h0
    · subst h0; rw [Lc_zero]; rfl
    · rw [Lc_gt coin 1 0 r' (by omega)]; simp [L0, h]

theorem init_eq : (State.init : State Pr Msg Bool) = asm (L0 0) ∅ := by
  refine state_eq ?_ ?_ rfl rfl
  · ext ⟨p, m⟩
    simp only [State.init, Set.mem_empty_iff_false, false_iff, asm, Set.mem_ofPred_eq, not_or]
    refine ⟨by unfold L0 own0 empty; split_ifs <;> simp, ?_⟩
    rintro ⟨r, v, d, -, hn⟩
    unfold L0 own0 empty at hn; split_ifs at hn
  · ext ⟨a, b, m⟩
    simp only [State.init, Set.mem_empty_iff_false, false_iff, asm, Set.mem_ofPred_eq]
    unfold L0 own0 empty; split_ifs <;> simp

/-! ### The execution -/

/-- The generated execution is the closed form `G`. -/
theorem gen_eq (coin : ℕ → Bool) (i : ℕ) : gen strat coin i = G coin i := by
  induction i with
  | zero => rw [gen, G_lt coin 0 (by omega)]; exact init_eq
  | succ i ih =>
    rw [gen, ih]
    rcases lt_or_ge i 3 with hi | hi
    · have h1 : strat i (G coin i) = ev0 i := by unfold strat; rw [ite_eq_left (by omega)]
      rw [h1, G_lt coin i (by omega), G_lt coin (i + 1) (by omega)]
      interval_cases i
      · exact apply_seg0 coin 0 (by decide)
      · exact apply_seg0 coin 1 (by decide)
      · exact apply_seg0 coin 2 (by decide)
    rcases eq_or_lt_of_le hi with hi | hi
    · subst hi
      have h1 : strat 3 (G coin 3) = .corrupt 3 := by unfold strat; rw [ite_eq_left (by omega)]; rfl
      rw [h1, G_lt coin 3 (by omega), G_ge coin 4 le_rfl]
      have hs : seg 4 = 1 := rfl
      have hp : pos 4 = 0 := rfl
      rw [hs, hp]
      simp only [apply]
      rw [ite_eq_left (by simp [asm])]
      refine state_eq ?_ ?_ rfl ?_
      · simp only [asm, L0_three coin]
      · simp only [asm, L0_three coin]
      · simp [asm]
    · have h4 : 4 ≤ i := hi
      rw [strat_G coin i h4, G_ge coin i h4, apply_G coin _ _ (seg_pos i) (pos_lt i),
        G_ge coin (i + 1) (by omega)]
      by_cases hk : pos i < 61
      · have e1 : seg (i + 1) = seg i := by unfold seg pos at *; omega
        have e2 : pos (i + 1) = pos i + 1 := by unfold seg pos at *; omega
        rw [update_Lc coin _ _ (seg_pos i), e1, e2]
      · have hk' : pos i = 61 := by have := pos_lt i; omega
        have e1 : seg (i + 1) = seg i + 1 := by unfold seg pos at *; omega
        have e2 : pos (i + 1) = 0 := by unfold seg pos at *; omega
        rw [e1, e2, hk']
        exact update_Lc_last coin _ (seg_pos i)

/-! ### Fairness and absence of decisions -/

/-- Start of round `r + 1`. -/
def Tm (r : ℕ) : ℕ := 4 + 62 * r

theorem G_Tm (coin : ℕ → Bool) (r : ℕ) : G coin (Tm r) = asm (Lc coin (r + 1) 0) {3} := by
  rw [G_ge coin _ (by unfold Tm; omega)]
  have e1 : seg (Tm r) = r + 1 := by unfold seg Tm; omega
  have e2 : pos (Tm r) = 0 := by unfold pos Tm; omega
  rw [e1, e2]

theorem G_bad (coin : ℕ → Bool) (i : ℕ) : (G coin i).bad = if i < 4 then ∅ else {3} := by
  unfold G; split_ifs <;> rfl

theorem gen_bad_sub (coin : ℕ → Bool) (i : ℕ) (p : Pr) (hp : p ≠ 3) :
    p ∉ (gen strat coin i).bad := by
  rw [gen_eq, G_bad]; split_ifs
  · exact Set.notMem_empty p
  · exact hp

theorem correct_iff (coin : ℕ → Bool) (p : Pr) : (genExec strat coin).Correct p ↔ p ≠ 3 := by
  constructor
  · intro h h3
    have := h 4
    simp only [genExec, gen_eq, G_bad] at this
    exact this (by simp [h3])
  · intro hp i
    exact gen_bad_sub coin i p hp

theorem start_own1 : ∀ p : Pr, p ≠ 3 → (start false false).sent p (.bval (x0 p) (some false)) = true := by
  decide

theorem start_tag_true (a : Bool) (p : Pr) (o : Bool)
    (h : (start a true).sent p (.bval o (some true)) = true) : o = !a := by
  fin_cases p <;> simp_all [start]

theorem start_tag_true' (p : Pr) (o : Bool) : (start false false).sent p (.bval o (some true)) = false := by
  fin_cases p <;> cases o <;> rfl

theorem fair (coin : ℕ → Bool) : (genExec strat coin).Fair := by
  have hσ : ∀ i, (genExec strat coin).σ i = G coin i := gen_eq coin
  refine ⟨?_, ?_, ?_⟩
  · -- every message between correct processes is delivered by the end of its round
    intro q s m i hq hs hm
    rw [correct_iff] at hq hs
    obtain ⟨R, hR⟩ : ∃ R, rnd m = R := ⟨_, rfl⟩
    have hj : i ≤ Tm (R + i) := by unfold Tm; omega
    have hm' := (genExec strat coin).sent_mono hj hm
    rw [hσ, G_Tm, mem_sent_asm, hR] at hm'
    have hfs : 1 ≤ R ∧ (part coin R 62).sent s (loc m) = true := by
      rcases hm' with h | ⟨r'', v, d, he, hn⟩
      · rcases Nat.eq_zero_or_pos R with h0 | h0
        · rw [h0, Lc_zero] at h; simp [empty] at h
        · rw [Lc_lt coin _ 0 R h0 (by omega)] at h; exact ⟨h0, h⟩
      · subst he
        simp only [rnd] at hR
        subst hR
        rcases Nat.eq_zero_or_pos r'' with h0 | h0
        · rw [h0, Lc_zero] at hn; simp [empty] at hn
        · rw [Lc_lt coin _ 0 r'' h0 (by omega)] at hn
          exact ⟨by omega, by rw [loc, part_own]; exact (nxt_iff_start coin r'' h0 s v d).1 hn⟩
    refine ⟨Tm (R + i), ?_⟩
    rw [hσ, G_Tm, mem_rcv_asm, hR, Lc_lt coin _ 0 R hfs.1 (by omega)]
    rw [part_full] at hfs ⊢
    exact final_delivered _ _ _ q s (loc m) hq hs hfs.2
  · -- every guard of a correct process is eventually disabled (each message class is
    -- eventually sent), so weak fairness holds vacuously for messages not sent
    intro p m i hp hg
    rw [correct_iff] at hp
    exfalso
    match m with
    | .bval r v none =>
      have h := hg (Tm (r + i + 1)) (by unfold Tm; omega)
      rw [hσ, G_Tm] at h
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        have := h.1
        rw [bvCnt_asm, Lc_zero] at this
        simp [lcnt, empty] at this
      · obtain ⟨d, hd⟩ := final_bval (aR coin r) (d2R r) (coin r) p v hp
        refine h.2 d (Or.inl ?_)
        simp only [rnd, loc]
        rw [Lc_lt coin _ 0 r h0 (by omega), part_full]
        exact hd
    | .bval 0 v (some d) =>
      exact hg i le_rfl
    | .bval 1 v (some d) =>
      have h := hg (Tm (1 + i + 1)) (by unfold Tm; omega)
      rw [hσ, G_Tm] at h
      refine h.2.2 (.bval 1 (x0 p) (some false)) ?_ ⟨_, _, rfl⟩
      exact (mem_est_iff coin _ 0 {3} 1 le_rfl (by omega) p _ _).2 (start_own1 p hp)
    | .bval (r + 2) v (some d) =>
      have h := hg (Tm (r + i + 2)) (by unfold Tm; omega)
      rw [hσ, G_Tm] at h
      obtain ⟨h0, h1, h2, h3⟩ := final_nxt (aR coin (r + 1)) (d2R (r + 1)) (coin (r + 1))
      obtain ⟨v', d', hn⟩ : ∃ v' d', (part coin (r + 1) 62).nxt p = some (v', d') := by
        rw [part_full]; fin_cases p <;> simp_all
      refine h.2.1 (.bval (r + 2) v' (some d')) (Or.inr ⟨r + 1, v', d', rfl, ?_⟩) ⟨_, _, rfl⟩
      rw [Lc_lt coin _ 0 (r + 1) (by omega) (by omega)]
      exact hn
    | .aux r w =>
      have h := hg (Tm (r + i + 1)) (by unfold Tm; omega)
      rw [hσ, G_Tm] at h
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        obtain ⟨v, d, hv⟩ := h.1
        exact not_mem_est_far coin _ 0 {3} 0 (Or.inl rfl) p v _ hv
      · obtain ⟨w', hw⟩ := final_aux (aR coin r) (d2R r) (coin r) p hp
        refine h.2.2 (.aux r w') (Or.inl ?_) ⟨_, rfl⟩
        simp only [rnd, loc]
        rw [Lc_lt coin _ 0 r h0 (by omega), part_full]
        exact hw
  · -- the decision guard never holds: singleton estimates always disagree with the coin
    intro p o i hp hg
    exfalso
    obtain ⟨r, hm, hc⟩ := hg (Tm i) (by unfold Tm; omega)
    rw [hσ, G_Tm] at hm
    change (p, Msg.bval (r + 1) o (some true)) ∈ (asm (Lc coin (i + 1) 0) {3}).sent at hm
    rcases Nat.lt_or_ge (i + 1) (r + 1) with h1 | h1
    · by_cases h2 : r = i + 1
      · subst h2
        rw [mem_est_next_iff coin _ 0 {3} (by omega)] at hm
        simp [part, scr, run, start] at hm
      · exact not_mem_est_far coin _ 0 {3} (r + 1) (Or.inr (by omega)) p o _ hm
    · rw [mem_est_iff coin _ 0 {3} (r + 1) (by omega) h1] at hm
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        rw [show aR coin (0 + 1) = false from rfl, show d2R (0 + 1) = false from rfl,
          start_tag_true'] at hm
        exact absurd hm (by simp)
      · obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [show d2R (r + 1 + 1) = true by simp [d2R]] at hm
        have := start_tag_true _ p o hm
        rw [show aR coin (r + 1 + 1) = coin (r + 1) from rfl] at this
        rw [this] at hc
        cases h : coin (r + 1) <;> simp [h] at hc

theorem no_decision (coin : ℕ → Bool) (i : ℕ) (p : Pr) :
    ((genExec strat coin).σ i).dec p = none := by
  show (gen strat coin i).dec p = none
  rw [gen_eq]; unfold G; split_ifs <;> rfl

/-- **Counterexample to Lemma 5, BC-Termination (Theorem 2) and Theorem 3.** For `n = 4`,
`t = 1` (so `n > 3t`), inputs `0, 0, 1` for the correct processes `0, 1, 2` and the Byzantine
process `3`, the adversary `strat` (a function of the time and the current global state) makes
the algorithm run forever without any decision, **for every coin sequence**: the execution is a
weakly fair execution of the algorithm (every message between correct processes is delivered,
every enabled step is eventually taken), exactly the processes `0, 1, 2` are correct, and no
process ever decides. -/
theorem counterexample : 3 * 1 < Fintype.card Pr ∧
    ∃ strat : ℕ → State Pr Msg Bool → Ev, ∀ coin : ℕ → Bool,
      (genExec strat coin).Fair ∧ (∀ p, (genExec strat coin).Correct p ↔ p ≠ 3) ∧
      ∀ i p, ((genExec strat coin).σ i).dec p = none :=
  ⟨by decide, strat, fun coin => ⟨fair coin, correct_iff coin, no_decision coin⟩⟩

/-- Hence, whatever the distribution of the common coin, the probability that some (correct)
process ever decides is `0` against this adversary (the paper claims `1`, and an expected
number of 4 rounds). -/
theorem prob_termination_eq_zero (μ : MeasureTheory.Measure (ℕ → Bool)) (p : Pr) :
    μ {coin | ∃ i, ((genExec strat coin).σ i).dec p ≠ none} = 0 := by
  have : {coin | ∃ i, ((genExec strat coin).σ i).dec p ≠ none} = ∅ := by
    ext coin
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_not]
    exact fun i => no_decision coin i p
  rw [this, MeasureTheory.measure_empty]

end Podc.SignatureFreeBA.Attack
