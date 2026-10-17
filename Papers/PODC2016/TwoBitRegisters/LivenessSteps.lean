import Papers.PODC2016.TwoBitRegisters.InvHist

/-!
# Effects of single steps (for the liveness proof)

Monotonicity of `w_sync`, the effect of receiving the next `WRITE` message, enabledness of the
continuations of `wait` statements, persistence of the control phase of a busy process, and the
effect of steps on the `READ()`/`PROCEED()` pipeline of a pair of processes.
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {w : P} {t : ℕ} {v₀ : V}
variable {C C' : Cfg P V} {s : Step P (register V v₀) (Msg V) (Act P)}
  {ℓ : Option (Label P (register V v₀))}

lemma W_apply_mono {q : P} {l : Loc P V} {out : Multiset (P × Msg V)}
    {net : Multiset (P × P × Msg V)} (hl : ∀ j, (C.loc q).ws j ≤ l.ws j) (i j : P) :
    W C i j ≤ W (C.apply q l out net) i j := by
  by_cases hi : i = q
  · subst hi; simp [W, hl]
  · simp [W, hi]

/-- `w_sync` only increases. -/
lemma W_step_mono (hI : InvW w C) (h : (alg w t v₀).step C s = some (C', ℓ)) (i j : P) :
    W C i j ≤ W C' i j := by
  cases s with
  | inv p o =>
    obtain ⟨-, -, l, out, hinv, rfl⟩ := step_inv h
    cases o with
    | write v =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_write hinv
      apply W_apply_mono; intro k
      by_cases hk : k = p
      · subst hk; simp
      · simp [hk]
    | read =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_read hinv
      apply W_apply_mono; intro k; exact le_refl _
  | internal p a =>
    obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal h
    cases a with
    | wret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint
      apply W_apply_mono; intro k; exact le_refl _
    | r8 =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
      apply W_apply_mono; intro k; exact le_refl _
    | rret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint
      apply W_apply_mono; intro k; exact le_refl _
    | proceed q sn =>
      obtain ⟨-, -, rfl, rfl, -⟩ := internal_proceed hint
      apply W_apply_mono; intro k; exact le_refl _
  | recv src dst m =>
    obtain ⟨-, -, l, out, r, hrc, rfl, -⟩ := step_recv h
    cases m with
    | write b v =>
      obtain ⟨-, -, hcase⟩ := receive_write hrc
      have hle := hI.ws_le dst src
      simp only [W] at hle
      rcases hcase with ⟨ha, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
      · apply W_apply_mono; intro k
        by_cases hk : k = src
        · subst hk; simp
        · by_cases hk' : k = dst
          · subst hk'; simp [hk]; omega
          · simp [hk, hk']
      · apply W_apply_mono; intro k
        by_cases hk : k = src
        · subst hk; simp
        · simp [hk]
      · apply W_apply_mono; intro k
        by_cases hk : k = src
        · subst hk; simp
        · simp [hk]
      · omega
    | read =>
      obtain ⟨rfl, rfl, -⟩ := receive_read hrc
      apply W_apply_mono; intro k; exact le_refl _
    | proceed =>
      obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
      apply W_apply_mono; intro k; exact le_refl _
  | drop src dst m =>
    obtain ⟨-, -, -, rfl⟩ := step_drop h; exact le_refl _
  | crash p =>
    obtain ⟨-, -, rfl⟩ := step_crash h; exact le_refl _
  | skip =>
    obtain ⟨rfl, -⟩ := step_skip h; exact le_refl _

lemma W_apply_le_succ {q : P} {l : Loc P V} {out : Multiset (P × Msg V)}
    {net : Multiset (P × P × Msg V)} (hl : ∀ j, l.ws j ≤ (C.loc q).ws j + 1) (i j : P) :
    W (C.apply q l out net) i j ≤ W C i j + 1 := by
  by_cases hi : i = q
  · subst hi; simp only [W, Config.apply_loc', ite_true]; exact hl j
  · simp [W, hi]

lemma W_step_le_succ (hI : InvW w C) (h : (alg w t v₀).step C s = some (C', ℓ)) (i j : P) :
    W C' i j ≤ W C i j + 1 := by
  cases s with
  | inv p o =>
    obtain ⟨-, -, l, out, hinv, rfl⟩ := step_inv h
    cases o with
    | write v =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_write hinv
      apply W_apply_le_succ; intro k
      by_cases hk : k = p
      · subst hk; simp
      · simp [hk]
    | read =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_read hinv
      apply W_apply_le_succ; intro k; dsimp only; omega
  | internal p a =>
    obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal h
    cases a with
    | wret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint
      apply W_apply_le_succ; intro k; dsimp only; omega
    | r8 =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
      apply W_apply_le_succ; intro k; dsimp only; omega
    | rret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint
      apply W_apply_le_succ; intro k; dsimp only; omega
    | proceed q sn =>
      obtain ⟨-, -, rfl, rfl, -⟩ := internal_proceed hint
      apply W_apply_le_succ; intro k; dsimp only; omega
  | recv src dst m =>
    obtain ⟨-, -, l, out, r, hrc, rfl, -⟩ := step_recv h
    cases m with
    | write b v =>
      obtain ⟨-, -, hcase⟩ := receive_write hrc
      have hle := hI.ws_le dst src
      simp only [W] at hle
      rcases hcase with ⟨ha, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
      · apply W_apply_le_succ; intro k
        by_cases hk : k = src
        · subst hk; simp
        · by_cases hk' : k = dst
          · subst hk'; simp [hk]; omega
          · simp [hk, hk']
      · apply W_apply_le_succ; intro k
        by_cases hk : k = src
        · subst hk; simp
        · simp [hk]
      · apply W_apply_le_succ; intro k
        by_cases hk : k = src
        · subst hk; simp
        · simp [hk]
      · omega
    | read =>
      obtain ⟨rfl, rfl, -⟩ := receive_read hrc
      apply W_apply_le_succ; intro k; dsimp only; omega
    | proceed =>
      obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
      apply W_apply_le_succ; intro k; dsimp only; omega
  | drop src dst m =>
    obtain ⟨-, -, -, rfl⟩ := step_drop h; simp only [W]; omega
  | crash p =>
    obtain ⟨-, -, rfl⟩ := step_crash h; simp only [W]; omega
  | skip =>
    obtain ⟨rfl, -⟩ := step_skip h; omega


/-- **Lemma 1** of the paper: every `w_sync_i[j]` increases by steps of `1`. -/
theorem lemma1 (hI : InvW w C) (h : (alg w t v₀).step C s = some (C', ℓ)) (i j : P) :
    W C' i j = W C i j ∨ W C' i j = W C i j + 1 := by
  have h1 := W_step_mono hI h i j
  have h2 := W_step_le_succ hI h i j
  omega

/-- Line 18: processing a `WRITE` message from `src` increments `w_sync_dst[src]`. -/
lemma W_recv_write (hI : InvW w C) {src dst : P} {b : Bool} {v : V}
    (h : (alg w t v₀).step C (.recv src dst (.write b v)) = some (C', ℓ)) :
    W C' dst src = W C dst src + 1 := by
  obtain ⟨-, -, l, out, r, hrc, rfl, -⟩ := step_recv h
  obtain ⟨-, -, hcase⟩ := receive_write hrc
  have hle := hI.ws_le dst src
  simp only [W] at hle
  rcases hcase with ⟨ha, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
  · simp [W]
  · simp [W]
  · simp [W]
  · omega

/-- The reception of a `WRITE` message passing the parity test of line 11 is enabled. -/
lemma enabled_recv_write {src dst : P} {b : Bool} {v : V} (hd : dst ∉ C.crashed)
    (hm : (src, dst, Msg.write b v) ∈ C.net) (hb : b = par (W C dst src + 1)) :
    (alg w t v₀).Enabled C (.recv src dst (.write b v)) := by
  simp only [Protocol.Enabled, Protocol.step, hd, hm, not_true_eq_false, or_self, ite_false,
    Option.isSome_map]
  simp only [alg, receive, W] at hb ⊢
  rw [if_pos hb]
  split_ifs <;> simp

lemma enabled_recv {src dst : P} {m : Msg V} (hd : dst ∉ C.crashed)
    (hm : (src, dst, m) ∈ C.net) (hs : (receive dst src m (C.loc dst)).isSome) :
    (alg w t v₀).Enabled C (.recv src dst m) := by
  simp only [Protocol.Enabled, Protocol.step, hd, hm, not_true_eq_false, or_self, ite_false,
    Option.isSome_map]
  exact hs

lemma enabled_internal {p : P} {a : Act P} (hp : p ∉ C.crashed)
    (hs : (internal (Fintype.card P - t) p a (C.loc p)).isSome) :
    (alg w t v₀).Enabled C (.internal p a) := by
  simp only [Protocol.Enabled, Protocol.step, hp, ite_false, Option.isSome_map]
  exact hs

/-- The control phase and `r_sync_p[p]` of a busy process change only at its own steps: a
response, or the transition from line 7 to line 9. -/
lemma phase_step (hI : InvW w C) (hP : InvP C) (h : (alg w t v₀).step C s = some (C', ℓ)) {p : P}
    (hbusy : (C.loc p).phase ≠ .idle) (hnoret : ∀ r, ℓ ≠ some (.ret p r)) :
    R C' p p = R C p p ∧ ((C'.loc p).phase = (C.loc p).phase ∨
      ∃ rsn, (C.loc p).phase = .r7 rsn ∧ (C'.loc p).phase = .r9 (W C p p)) := by
  cases s with
  | inv q o =>
    obtain ⟨-, -, l, out, hinv, rfl⟩ := step_inv h
    by_cases hq : p = q
    · subst hq
      cases o with
      | write v => exact absurd (invoke_write hinv).2.1 hbusy
      | read => exact absurd (invoke_read hinv).2.1 hbusy
    · simp [R, hq]
  | internal q a =>
    obtain ⟨-, l, out, r, hint, rfl, rfl⟩ := step_internal h
    by_cases hq : p = q
    · subst hq
      cases a with
      | wret =>
        obtain ⟨_, -, -, -, -, rfl⟩ := internal_wret hint
        exact absurd rfl (hnoret _)
      | r8 =>
        obtain ⟨rsn, hph, -, rfl, rfl, -⟩ := internal_r8 hint
        refine ⟨by simp [R], Or.inr ⟨rsn, hph, by simp [W]⟩⟩
      | rret =>
        obtain ⟨_, -, -, -, -, rfl⟩ := internal_rret hint
        exact absurd rfl (hnoret _)
      | proceed j sn =>
        obtain ⟨-, -, rfl, rfl, -⟩ := internal_proceed hint
        simp [R]
    · simp [R, hq]
  | recv src dst m =>
    obtain ⟨-, hm, l, out, r, hrc, rfl, -⟩ := step_recv h
    by_cases hq : p = dst
    · subst hq
      cases m with
      | write b v =>
        obtain ⟨-, -, hcase⟩ := receive_write hrc
        rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
        · simp [R]
        · simp [R]
        · simp [R]
        · have := hI.ws_le p src; simp only [W] at this; omega
      | read =>
        obtain ⟨rfl, rfl, -⟩ := receive_read hrc
        simp [R]
      | proceed =>
        obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
        have hsp : src ≠ p := by
          rintro rfl
          have := hP.proceed_ne src
          simp only [cP] at this
          exact absurd (Multiset.count_pos.2 hm) (by omega)
        simp [R, Ne.symm hsp]
    · simp [R, hq]
  | drop src dst m =>
    obtain ⟨-, -, -, rfl⟩ := step_drop h; simp
  | crash q =>
    obtain ⟨-, -, rfl⟩ := step_crash h; simp
  | skip =>
    obtain ⟨rfl, -⟩ := step_skip h; simp

/-- Effect of an arbitrary step on the `READ()`/`PROCEED()` pipeline from a busy reader `p` to
a non-crashed process `j`: `READ()`s in transit do not increase, `r_sync_p[j]` and the number of
`PROCEED()`s sent by `j` to `p` (in transit or counted) do not decrease, and a pending `READ()`
handler of `j` for `p` disappears only when `j` sends a `PROCEED()`. -/
lemma pipe_step (hI : InvW w C) (hP : InvP C) (h : (alg w t v₀).step C s = some (C', ℓ))
    {p j : P} (hpj : p ≠ j) (hbusy : (C.loc p).phase ≠ .idle) (hj : j ∉ C.crashed) :
    cR C' p j ≤ cR C p j ∧ R C p j ≤ R C' p j ∧ cP C j p + R C p j ≤ cP C' j p + R C' p j ∧
    (∀ sn, (p, sn) ∈ (C.loc j).tasks →
      (p, sn) ∈ (C'.loc j).tasks ∨ cP C j p + R C p j < cP C' j p + R C' p j) := by
  cases s with
  | inv q o =>
    obtain ⟨-, -, l, out, hinv, rfl⟩ := step_inv h
    have hqp : q ≠ p := by
      rintro rfl
      cases o with
      | write v => exact hbusy (invoke_write hinv).2.1
      | read => exact hbusy (invoke_read hinv).2.1
    cases o with
    | write v =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_write hinv
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [cR, Multiset.count_add, count_outMsgs_sendTo]
      · simp [R, Ne.symm hqp]
      · simp [cP, R, Multiset.count_add, count_outMsgs_sendTo, Ne.symm hqp]
      · intro sn hsn; left
        by_cases hjq : j = q
        · subst hjq; simpa using hsn
        · simpa [hjq] using hsn
    | read =>
      obtain ⟨-, -, rfl, rfl⟩ := invoke_read hinv
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [cR, Multiset.count_add, count_outMsgs_sendTo, Ne.symm hqp]
      · simp [R, Ne.symm hqp]
      · simp [cP, R, Multiset.count_add, count_outMsgs_sendTo, Ne.symm hqp]
      · intro sn hsn; left
        by_cases hjq : j = q
        · subst hjq; simpa using hsn
        · simpa [hjq] using hsn
  | internal q a =>
    obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal h
    cases a with
    | wret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint
      refine ⟨by simp [cR], ?_, ?_, ?_⟩
      · by_cases hq : p = q
        · subst hq; simp [R]
        · simp [R, hq]
      · by_cases hq : p = q
        · subst hq; simp [R, cP]
        · simp [R, cP, hq]
      · intro sn hsn; left
        by_cases hjq : j = q
        · subst hjq; simpa using hsn
        · simpa [hjq] using hsn
    | r8 =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
      refine ⟨by simp [cR], ?_, ?_, ?_⟩
      · by_cases hq : p = q
        · subst hq; simp [R]
        · simp [R, hq]
      · by_cases hq : p = q
        · subst hq; simp [R, cP]
        · simp [R, cP, hq]
      · intro sn hsn; left
        by_cases hjq : j = q
        · subst hjq; simpa using hsn
        · simpa [hjq] using hsn
    | rret =>
      obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint
      refine ⟨by simp [cR], ?_, ?_, ?_⟩
      · by_cases hq : p = q
        · subst hq; simp [R]
        · simp [R, hq]
      · by_cases hq : p = q
        · subst hq; simp [R, cP]
        · simp [R, cP, hq]
      · intro sn hsn; left
        by_cases hjq : j = q
        · subst hjq; simpa using hsn
        · simpa [hjq] using hsn
    | proceed j' sn' =>
      obtain ⟨hmem, -, rfl, rfl, -⟩ := internal_proceed hint
      set C' := C.apply q _ ({(j', Msg.proceed)} : Multiset (P × Msg V)) C.net with hC'
      have hRe : R C' p j = R C p j := by
        by_cases hq : p = q
        · subst hq; simp [hC', R]
        · simp [hC', R, hq]
      have hcP : cP C' j p = cP C j p + if q = j ∧ j' = p then 1 else 0 := by
        simp only [hC', cP, Config.apply_net, Multiset.count_add, count_outMsgs_single]
        congr 1
        by_cases he : q = j ∧ j' = p
        · obtain ⟨rfl, rfl⟩ := he; simp
        · rw [if_neg he, if_neg]; simp only [Prod.mk.injEq, and_true]; tauto
      refine ⟨by simp [hC', cR, Multiset.count_add, count_outMsgs_single], by rw [hRe], ?_, ?_⟩
      · rw [hRe, hcP]; omega
      · intro sn hsn
        by_cases hjq : j = q
        · subst hjq
          by_cases he : (p, sn) = (j', sn')
          · right
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            rw [hRe, hcP, if_pos ⟨rfl, rfl⟩]; omega
          · left
            simp only [hC', Config.apply_loc', ite_true]
            exact (Multiset.mem_erase_of_ne he).2 hsn
        · left; simpa [hC', hjq] using hsn
  | recv src dst m =>
    obtain ⟨-, hm, l, out, r, hrc, rfl, -⟩ := step_recv h
    cases m with
    | write b v =>
      obtain ⟨-, -, hcase⟩ := receive_write hrc
      have hle := hI.ws_le dst src
      simp only [W] at hle
      have hloc : l.rs = (C.loc dst).rs ∧ l.tasks = (C.loc dst).tasks ∧
          ∀ x ∈ out, ∃ b v, x.2 = Msg.write b v := by
        rcases hcase with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | himp
        · exact ⟨rfl, rfl, write_out_sendTo⟩
        · exact ⟨rfl, rfl, by simp⟩
        · exact ⟨rfl, rfl, by simp⟩
        · omega
      obtain ⟨hrs, htasks, hout⟩ := hloc
      have hR : ∀ x y, R (C.apply dst l out (C.net.erase (src, dst, .write b v))) x y = R C x y := by
        intro x y; by_cases hx : x = dst
        · subst hx; simp [R, hrs]
        · simp [R, hx]
      have hT : ∀ x, ((C.apply dst l out (C.net.erase (src, dst, .write b v))).loc x).tasks =
          (C.loc x).tasks := by
        intro x; by_cases hx : x = dst
        · subst hx; simp [htasks]
        · simp [hx]
      have hcnt : ∀ x y (m' : Msg V), (∀ b v, m' ≠ .write b v) →
          (C.apply dst l out (C.net.erase (src, dst, .write b v))).net.count (x, y, m') =
            C.net.count (x, y, m') := by
        intro x y m' hm'
        have hne : (x, y, m') ≠ (src, dst, Msg.write b v) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hm' b v he.2.2
        simp only [Config.apply_net, Multiset.count_add,
          count_outMsgs_of_write hout x y m' hm', add_zero]
        exact Multiset.count_erase_of_ne hne _
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [cR]; rw [hcnt _ _ _ (by simp)]
      · rw [hR]
      · simp only [cP]; rw [hcnt _ _ _ (by simp), hR]
      · intro sn hsn; left; rw [hT]; exact hsn
    | read =>
      obtain ⟨rfl, rfl, -⟩ := receive_read hrc
      set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, Msg.read))
        with hC'
      have hR : ∀ x y, R C' x y = R C x y := by
        intro x y; by_cases hx : x = dst
        · subst hx; simp [hC', R]
        · simp [hC', R, hx]
      refine ⟨?_, by rw [hR], ?_, ?_⟩
      · simp only [hC', cR, Config.apply_net, outMsgs_zero, add_zero]
        exact Multiset.count_le_of_le _ (Multiset.erase_le _ _)
      · rw [hR]
        simp only [hC', cP, Config.apply_net, outMsgs_zero, add_zero]
        rw [Multiset.count_erase_of_ne (by simp)]
      · intro sn hsn; left
        by_cases hx : j = dst
        · subst hx; simp [hC', hsn]
        · simpa [hC', hx] using hsn
    | proceed =>
      obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
      have hsd : src ≠ dst := by
        rintro rfl
        have := hP.proceed_ne src
        simp only [cP] at this
        exact absurd (Multiset.count_pos.2 hm) (by omega)
      set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, Msg.proceed))
        with hC'
      have hT : ∀ x, (C'.loc x).tasks = (C.loc x).tasks := by
        intro x; by_cases hx : x = dst
        · subst hx; simp [hC']
        · simp [hC', hx]
      have hR : R C' p j = R C p j + if p = dst ∧ j = src then 1 else 0 := by
        by_cases hx : p = dst
        · subst hx
          by_cases hy : j = src
          · subst hy; simp [hC', R]
          · simp [hC', R, hy]
        · simp [hC', R, hx]
      have hcP : cP C' j p + (if p = dst ∧ j = src then 1 else 0) = cP C j p := by
        simp only [hC', cP, Config.apply_net, outMsgs_zero, add_zero]
        by_cases he : p = dst ∧ j = src
        · obtain ⟨rfl, rfl⟩ := he
          rw [Multiset.count_erase_self, if_pos ⟨rfl, rfl⟩]
          have h1 := Multiset.count_pos.2 hm
          omega
        · rw [if_neg he, Multiset.count_erase_of_ne (by
            simp only [ne_eq, Prod.mk.injEq, and_true]; tauto)]
          simp
      refine ⟨?_, by rw [hR]; omega, by rw [hR]; omega, ?_⟩
      · simp only [hC', cR, Config.apply_net, outMsgs_zero, add_zero]
        rw [Multiset.count_erase_of_ne (by simp)]
      · intro sn hsn; left; rw [hT]; exact hsn
  | drop src dst m =>
    obtain ⟨hsrc, -, -, rfl⟩ := step_drop h
    refine ⟨Multiset.count_le_of_le _ (Multiset.erase_le _ _), le_refl _, ?_,
      fun sn hsn => Or.inl hsn⟩
    simp only [cP, R]
    rw [Multiset.count_erase_of_ne]
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro he; subst he; exact absurd hsrc hj
  | crash q =>
    obtain ⟨-, -, rfl⟩ := step_crash h
    exact ⟨le_refl _, le_refl _, le_refl _, fun sn hsn => Or.inl hsn⟩
  | skip =>
    obtain ⟨rfl, -⟩ := step_skip h
    exact ⟨le_refl _, le_refl _, le_refl _, fun sn hsn => Or.inl hsn⟩

/-! ## Effects of specific steps -/

lemma pipe_recv_read {p j : P} (h : (alg w t v₀).step C (.recv p j .read) = some (C', ℓ)) :
    cR C' p j + 1 = cR C p j := by
  obtain ⟨-, hm, l, out, r, hrc, rfl, -⟩ := step_recv h
  obtain ⟨rfl, rfl, -⟩ := receive_read hrc
  simp only [cR, Config.apply_net, outMsgs_zero, add_zero]
  rw [Multiset.count_erase_self]
  have := Multiset.count_pos.2 hm
  omega

lemma pipe_proceed {p j : P} {sn : ℕ} (hpj : p ≠ j)
    (h : (alg w t v₀).step C (.internal j (.proceed p sn)) = some (C', ℓ)) :
    cP C' j p + R C' p j = cP C j p + R C p j + 1 := by
  obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal h
  obtain ⟨-, -, rfl, rfl, -⟩ := internal_proceed hint
  simp [cP, R, Multiset.count_add, count_outMsgs_single, hpj]
  omega

lemma pipe_recv_proceed {p j : P}
    (h : (alg w t v₀).step C (.recv j p .proceed) = some (C', ℓ)) :
    R C' p j = R C p j + 1 := by
  obtain ⟨-, -, l, out, r, hrc, rfl, -⟩ := step_recv h
  obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
  simp [R]

lemma wret_label {p : P} (h : (alg w t v₀).step C (.internal p .wret) = some (C', ℓ)) :
    ∃ r, ℓ = some (.ret p r) := by
  obtain ⟨-, l, out, r, hint, rfl, rfl⟩ := step_internal h
  obtain ⟨_, -, -, -, -, rfl⟩ := internal_wret hint
  exact ⟨_, rfl⟩

lemma rret_label {p : P} (h : (alg w t v₀).step C (.internal p .rret) = some (C', ℓ)) :
    ∃ r, ℓ = some (.ret p r) := by
  obtain ⟨-, l, out, r, hint, rfl, rfl⟩ := step_internal h
  obtain ⟨_, -, -, -, -, rfl⟩ := internal_rret hint
  exact ⟨_, rfl⟩

lemma r8_phase {p : P} (h : (alg w t v₀).step C (.internal p .r8) = some (C', ℓ)) :
    ∃ sn, (C'.loc p).phase = .r9 sn := by
  obtain ⟨-, l, out, r, hint, rfl, -⟩ := step_internal h
  obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
  exact ⟨(C.loc p).ws p, by simp⟩

end Podc.TwoBit
