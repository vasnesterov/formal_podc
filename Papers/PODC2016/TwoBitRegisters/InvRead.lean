import Papers.PODC2016.TwoBitRegisters.InvWrite

/-!
# The `READ()`/`PROCEED()` pipeline

For a reader `i` and another process `j`, every `READ()` sent by `i` to `j` is, at any time,
either in transit, or a pending handler of `j` (waiting at line 20), or a `PROCEED()` in transit
back to `i`, or counted in `r_sync_i[j]`; only messages of crashed processes can be lost
(`InvP.pipe`, `InvP.pipe_eq`). This is what makes the counting at line 7 sound without any
sequence number in the messages, although channels are not FIFO.
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- `READ()` messages from `i` to `j` in transit. -/
abbrev cR (C : Cfg P V) (i j : P) : ℕ := C.net.count (i, j, .read)

/-- `READ()` handlers of `j` for `i` waiting at line 20. -/
abbrev tk (C : Cfg P V) (j i : P) : ℕ := (C.loc j).tasks.countP (fun x => x.1 = i)

/-- `PROCEED()` messages from `j` to `i` in transit. -/
abbrev cP (C : Cfg P V) (j i : P) : ℕ := C.net.count (j, i, .proceed)

/-- `r_sync_i[j]`. -/
abbrev R (C : Cfg P V) (i j : P) : ℕ := (C.loc i).rs j

/-- Pipeline invariant. -/
structure InvP (C : Cfg P V) : Prop where
  pipe : ∀ i j, i ≠ j → cR C i j + tk C j i + cP C j i + R C i j ≤ R C i i
  pipe_eq : ∀ i j, i ≠ j → i ∉ C.crashed → j ∉ C.crashed →
    cR C i j + tk C j i + cP C j i + R C i j = R C i i
  tasks_ne : ∀ j i sn, (i, sn) ∈ (C.loc j).tasks → i ≠ j
  tasks_le : ∀ j i sn, (i, sn) ∈ (C.loc j).tasks → sn ≤ W C j j
  read_ne : ∀ i, cR C i i = 0
  proceed_ne : ∀ i, cP C i i = 0
  r7_rsn : ∀ i rsn, (C.loc i).phase = .r7 rsn → rsn = R C i i

lemma countP_erase_of_mem {α : Type} [DecidableEq α] (q : α → Prop) [DecidablePred q]
    {s : Multiset α} {a : α} (h : a ∈ s) :
    s.countP q = (s.erase a).countP q + if q a then 1 else 0 := by
  conv_lhs => rw [← Multiset.cons_erase h]
  rw [Multiset.countP_cons]

lemma count_erase_of_mem' {α : Type} [DecidableEq α] {s : Multiset α} {a : α} (h : a ∈ s) :
    s.count a = (s.erase a).count a + 1 := by
  rw [Multiset.count_erase_self]
  have := Multiset.count_pos.2 h
  omega

lemma countP_singleton' {α : Type} (q : α → Prop) [DecidablePred q] (a : α) :
    ({a} : Multiset α).countP q = if q a then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons]; simp

lemma invP_init (w : P) (t : ℕ) (v₀ : V) : InvP ((alg w t v₀).initCfg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Protocol.initCfg, alg, Loc.init, W, cR, tk, cP, R]

/-- Messages sent by a local transition that sends only `WRITE` messages. -/
lemma count_outMsgs_of_write {p : P} {out : Multiset (P × Msg V)}
    (hout : ∀ x ∈ out, ∃ b v, x.2 = .write b v) (i j : P) (m : Msg V)
    (hm : ∀ b v, m ≠ .write b v) : (outMsgs p out).count (i, j, m) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hx
  simp only [outMsgs, Multiset.mem_map] at hx
  obtain ⟨y, hy, he⟩ := hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨b, v, hb⟩ := hout y hy
  exact hm b v (he.2.2 ▸ hb)

/-- Frame lemma: a transition of `p` that only changes `w_sync` (monotonically), histories and
phases (not into `r7`) and only sends/receives `WRITE` messages preserves `InvP`. -/
lemma InvP.frame_write {C : Cfg P V} (hP : InvP C) {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} {net : Multiset (P × P × Msg V)}
    (hrs : l.rs = (C.loc p).rs) (htasks : l.tasks = (C.loc p).tasks)
    (hws : ∀ j, (C.loc p).ws j ≤ l.ws j)
    (hph : ∀ rsn, l.phase = .r7 rsn → (C.loc p).phase = .r7 rsn)
    (hout : ∀ x ∈ out, ∃ b v, x.2 = .write b v)
    (hnet : ∀ i j, net.count (i, j, .read) = C.net.count (i, j, .read) ∧
      net.count (i, j, .proceed) = C.net.count (i, j, .proceed)) :
    InvP (C.apply p l out net) := by
  set C' := C.apply p l out net with hC'
  have hR : ∀ i j, R C' i j = R C i j := by
    intro i j; by_cases hi : i = p
    · subst hi; simp [hC', R, hrs]
    · simp [hC', R, hi]
  have hT : ∀ j, (C'.loc j).tasks = (C.loc j).tasks := by
    intro j; by_cases hj : j = p
    · subst hj; simp [hC', htasks]
    · simp [hC', hj]
  have hcR : ∀ i j, cR C' i j = cR C i j := by
    intro i j
    simp [hC', cR, Multiset.count_add, (hnet i j).1,
      count_outMsgs_of_write hout i j .read (by simp)]
  have hcP : ∀ i j, cP C' i j = cP C i j := by
    intro i j
    simp [hC', cP, Multiset.count_add, (hnet i j).2,
      count_outMsgs_of_write hout i j .proceed (by simp)]
  have htk : ∀ j i, tk C' j i = tk C j i := by intro j i; simp [tk, hT]
  have hW : ∀ j, W C j j ≤ W C' j j := by
    intro j; by_cases hj : j = p
    · subst hj; simp only [hC', W, Config.apply_loc', ite_true]; exact hws j
    · simp [hC', W, hj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij; rw [hcR, htk, hcP, hR, hR]; exact hP.pipe i j hij
  · intro i j hij hi hj; rw [hcR, htk, hcP, hR, hR]; exact hP.pipe_eq i j hij hi hj
  · intro j i sn h; rw [hT] at h; exact hP.tasks_ne j i sn h
  · intro j i sn h; rw [hT] at h; exact (hP.tasks_le j i sn h).trans (hW j)
  · intro i; rw [hcR]; exact hP.read_ne i
  · intro i; rw [hcP]; exact hP.proceed_ne i
  · intro i rsn h
    rw [hR]
    by_cases hi : i = p
    · subst hi; simp only [hC', Config.apply_loc', ite_true] at h
      exact hP.r7_rsn i rsn (hph rsn h)
    · simp only [hC', Config.apply_loc', hi, ite_false] at h
      exact hP.r7_rsn i rsn h

lemma write_out_sendTo {c : P → Prop} [DecidablePred c] {b : Bool} {v : V} :
    ∀ x ∈ sendTo c (Msg.write b v), ∃ b' v', x.2 = Msg.write b' v' := by
  intro x hx
  simp only [sendTo, Multiset.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact ⟨b, v, rfl⟩

lemma net_erase_write {C : Cfg P V} (src dst : P) (b : Bool) (v : V) (i j : P) :
    (C.net.erase (src, dst, .write b v)).count (i, j, .read) = C.net.count (i, j, .read) ∧
      (C.net.erase (src, dst, .write b v)).count (i, j, .proceed) =
        C.net.count (i, j, .proceed) :=
  ⟨Multiset.count_erase_of_ne (by simp) _, Multiset.count_erase_of_ne (by simp) _⟩

/-- The pipeline invariant holds in every reachable configuration. -/
theorem invP_of_reach {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}
    (hr : (alg w t v₀).Reach C h) : InvP C := by
  induction hr with
  | init => exact invP_init w t v₀
  | @step C h s C' ℓ hr hs ih =>
    cases s with
    | inv p o =>
      obtain ⟨hpc, -, l, out, hinv, rfl⟩ := step_inv hs
      cases o with
      | write v =>
        obtain ⟨-, -, rfl, rfl⟩ := invoke_write hinv
        refine ih.frame_write rfl rfl ?_ (by simp) write_out_sendTo (fun _ _ => ⟨rfl, rfl⟩)
        intro j; by_cases hj : j = p <;> simp [Function.update_apply, hj]
      | read =>
        obtain ⟨hpw, hidle, rfl, rfl⟩ := invoke_read hinv
        set C' := C.apply p _ _ C.net with hC'
        have hcnt : ∀ i j m, C'.net.count (i, j, m) =
            C.net.count (i, j, m) + if i = p ∧ j ≠ p ∧ m = .read then 1 else 0 := by
          intro i j m; simp [hC', Multiset.count_add, count_outMsgs_sendTo]
        have hR : ∀ i j, R C' i j = if i = p ∧ j = p then R C p p + 1 else R C i j := by
          intro i j
          by_cases hi : i = p
          · subst hi; by_cases hj : j = i <;> simp [hC', R, hj, Function.update_apply]
          · simp [hC', R, hi]
        have hT : ∀ j, (C'.loc j).tasks = (C.loc j).tasks := by
          intro j; by_cases hj : j = p
          · subst hj; simp [hC']
          · simp [hC', hj]
        have htk : ∀ j i, tk C' j i = tk C j i := by intro j i; simp [tk, hT]
        have hWW : ∀ j, W C' j j = W C j j := by
          intro j; by_cases hj : j = p
          · subst hj; simp [hC', W]
          · simp [hC', W, hj]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i j hij
          have := ih.pipe i j hij
          simp only [cR, cP, hcnt, htk, hR] at this ⊢
          by_cases hi : i = p
          · subst hi; simp [Ne.symm hij]; omega
          · simp [hi]; omega
        · intro i j hij hi hj
          have := ih.pipe_eq i j hij hi hj
          simp only [cR, cP, hcnt, htk, hR] at this ⊢
          by_cases hi' : i = p
          · subst hi'; simp [Ne.symm hij]; omega
          · simp [hi']; omega
        · intro j i sn h; rw [hT] at h; exact ih.tasks_ne j i sn h
        · intro j i sn h; rw [hT] at h; rw [hWW]; exact ih.tasks_le j i sn h
        · intro i; simp only [cR, hcnt]; simp [ih.read_ne i]
        · intro i; simp only [cP, hcnt]; simp [ih.proceed_ne i]
        · intro i rsn h
          by_cases hi : i = p
          · subst hi
            simp only [hC', Config.apply_loc', ite_true, Phase.r7.injEq] at h
            rw [hR, if_pos ⟨rfl, rfl⟩, ← h]
          · simp only [hC', Config.apply_loc', hi, ite_false] at h
            rw [hR, if_neg (fun h' => hi h'.1)]; exact ih.r7_rsn i rsn h
    | internal p a =>
      obtain ⟨hpc, l, out, r, hint, rfl, -⟩ := step_internal hs
      cases a with
      | wret =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_wret hint
        exact ih.frame_write rfl rfl (fun _ => le_refl _) (by simp) (by simp)
          (fun _ _ => ⟨rfl, rfl⟩)
      | r8 =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_r8 hint
        exact ih.frame_write rfl rfl (fun _ => le_refl _) (by simp) (by simp)
          (fun _ _ => ⟨rfl, rfl⟩)
      | rret =>
        obtain ⟨_, -, -, rfl, rfl, -⟩ := internal_rret hint
        exact ih.frame_write rfl rfl (fun _ => le_refl _) (by simp) (by simp)
          (fun _ _ => ⟨rfl, rfl⟩)
      | proceed j sn =>
        obtain ⟨hmem, hle, rfl, rfl, -⟩ := internal_proceed hint
        set C' := C.apply p _ _ C.net with hC'
        have hjp : j ≠ p := ih.tasks_ne p j sn hmem
        have hcnt : ∀ x, C'.net.count x = C.net.count x + if x = (p, j, .proceed) then 1 else 0 := by
          intro x; simp [hC', Multiset.count_add, count_outMsgs_single]
        have hR : ∀ i k, R C' i k = R C i k := by
          intro i k; by_cases hi : i = p
          · subst hi; simp [hC', R]
          · simp [hC', R, hi]
        have hTo : ∀ k, k ≠ p → (C'.loc k).tasks = (C.loc k).tasks := by
          intro k hk; simp [hC', hk]
        have hTp : (C'.loc p).tasks = (C.loc p).tasks.erase (j, sn) := by simp [hC']
        have htk : ∀ k i, tk C' k i = tk C k i - if k = p ∧ i = j then 1 else 0 := by
          intro k i
          by_cases hk : k = p
          · subst hk
            simp only [tk, hTp]
            have := countP_erase_of_mem (fun x : P × ℕ => x.1 = i) hmem
            by_cases hi : i = j
            · subst hi; simp at this ⊢; omega
            · simp [Ne.symm hi, hi] at this ⊢; omega
          · simp [tk, hTo k hk, hk]
        have htkpos : 1 ≤ tk C p j := by
          simp only [tk]; rw [countP_erase_of_mem (fun x : P × ℕ => x.1 = j) hmem]; simp
        have hWW : ∀ k, W C' k k = W C k k := by
          intro k; by_cases hk : k = p
          · subst hk; simp [hC', W]
          · simp [hC', W, hk]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i k hik
          have := ih.pipe i k hik
          have h1 := htkpos
          simp only [cR, cP, hcnt, htk, hR] at this h1 ⊢
          by_cases hh : k = p ∧ i = j
          · obtain ⟨rfl, rfl⟩ := hh; simp; omega
          · simp [hh]; omega
        · intro i k hik hi hk
          have := ih.pipe_eq i k hik hi hk
          have h1 := htkpos
          simp only [cR, cP, hcnt, htk, hR] at this h1 ⊢
          by_cases hh : k = p ∧ i = j
          · obtain ⟨rfl, rfl⟩ := hh; simp; omega
          · simp [hh]; omega
        · intro k i sn' h
          by_cases hk : k = p
          · subst hk; rw [hTp] at h; exact ih.tasks_ne k i sn' (Multiset.mem_of_mem_erase h)
          · rw [hTo k hk] at h; exact ih.tasks_ne k i sn' h
        · intro k i sn' h
          rw [hWW]
          by_cases hk : k = p
          · subst hk; rw [hTp] at h; exact ih.tasks_le k i sn' (Multiset.mem_of_mem_erase h)
          · rw [hTo k hk] at h; exact ih.tasks_le k i sn' h
        · intro i; simp only [cR, hcnt]; simp [ih.read_ne i]
        · intro i
          simp only [cP, hcnt]
          rw [if_neg (by simp only [Prod.mk.injEq]; intro h; exact hjp (h.1 ▸ h.2.1).symm)]
          simp [ih.proceed_ne i]
        · intro i rsn h
          rw [hR]
          by_cases hi : i = p
          · subst hi; simp only [hC', Config.apply_loc', ite_true] at h
            exact ih.r7_rsn i rsn h
          · simp only [hC', Config.apply_loc', hi, ite_false] at h
            exact ih.r7_rsn i rsn h
    | recv src dst m =>
      obtain ⟨hdc, hm, l, out, r, hrc, rfl, -⟩ := step_recv hs
      cases m with
      | write b v =>
        obtain ⟨hb, -, hcase⟩ := receive_write hrc
        rcases hcase with ⟨ha, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩ | ⟨heq, rfl, rfl⟩ | himp
        · refine ih.frame_write rfl rfl ?_ (fun _ h => h) write_out_sendTo
            (net_erase_write _ _ _ _)
          intro j
          by_cases hj : j = src
          · subst hj; simp
          · by_cases hj' : j = dst
            · subst hj'; simp [hj, ha]
            · simp [hj, hj', Function.update_apply]
        · refine ih.frame_write rfl rfl ?_ (fun _ h => h) (by simp) (net_erase_write _ _ _ _)
          intro j; by_cases hj : j = src <;> simp [hj, Function.update_apply]
        · refine ih.frame_write rfl rfl ?_ (fun _ h => h) (by simp) (net_erase_write _ _ _ _)
          intro j; by_cases hj : j = src <;> simp [hj, Function.update_apply]
        · have := (invW_of_reach hr).ws_le dst src; simp only [W] at this; omega
      | read =>
        obtain ⟨rfl, rfl, -⟩ := receive_read hrc
        have hsd : src ≠ dst := by
          intro he; subst he; have := ih.read_ne src
          simp only [cR] at this; rw [Multiset.count_eq_zero] at this; exact this hm
        set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, .read)) with hC'
        have hcnt : ∀ x, C'.net.count x = C.net.count x - if x = (src, dst, .read) then 1 else 0 := by
          intro x
          simp only [hC', Config.apply_net, outMsgs_zero, add_zero]
          by_cases hx : x = (src, dst, .read)
          · subst hx; rw [Multiset.count_erase_self]; simp
          · rw [Multiset.count_erase_of_ne hx]; simp [hx]
        have hpos : 1 ≤ C.net.count (src, dst, .read) := Multiset.one_le_count_iff_mem.2 hm
        have hR : ∀ i k, R C' i k = R C i k := by
          intro i k; by_cases hi : i = dst
          · subst hi; simp [hC', R]
          · simp [hC', R, hi]
        have hTo : ∀ k, k ≠ dst → (C'.loc k).tasks = (C.loc k).tasks := by
          intro k hk; simp [hC', hk]
        have hTd : (C'.loc dst).tasks = (C.loc dst).tasks + {(src, W C dst dst)} := by simp [hC', W]
        have htk : ∀ k i, tk C' k i = tk C k i + if i = src ∧ k = dst then 1 else 0 := by
          intro k i
          by_cases hk : k = dst
          · subst hk; simp only [tk, hTd, Multiset.countP_add]
            by_cases hi : i = src
            · subst hi; simp [countP_singleton']
            · simp [Ne.symm hi, hi, countP_singleton']
          · simp [tk, hTo k hk, hk]
        have hcR : ∀ i k, cR C' i k + (if i = src ∧ k = dst then 1 else 0) = cR C i k := by
          intro i k
          simp only [cR, hcnt]
          by_cases hh : i = src ∧ k = dst
          · obtain ⟨rfl, rfl⟩ := hh; simp; omega
          · have : (i, k, (Msg.read : Msg V)) ≠ (src, dst, Msg.read) := by
              simp only [ne_eq, Prod.mk.injEq, and_true]; exact hh
            simp [hh, this]
        have hcP : ∀ k i, cP C' k i = cP C k i := by
          intro k i; simp only [cP, hcnt]; simp
        have hWW : ∀ k, W C' k k = W C k k := by
          intro k; by_cases hk : k = dst
          · subst hk; simp [hC', W]
          · simp [hC', W, hk]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i k hik
          have := ih.pipe i k hik
          have h1 := hcR i k
          have h2 := htk k i
          rw [hcP, hR, hR]
          omega
        · intro i k hik hi hk
          have := ih.pipe_eq i k hik hi hk
          have h1 := hcR i k
          have h2 := htk k i
          rw [hcP, hR, hR]
          omega
        · intro k i sn' h
          by_cases hk : k = dst
          · subst hk; rw [hTd] at h
            rcases Multiset.mem_add.1 h with h | h
            · exact ih.tasks_ne k i sn' h
            · simp only [Multiset.mem_singleton, Prod.mk.injEq] at h
              rw [h.1]; exact hsd
          · rw [hTo k hk] at h; exact ih.tasks_ne k i sn' h
        · intro k i sn' h
          rw [hWW]
          by_cases hk : k = dst
          · subst hk; rw [hTd] at h
            rcases Multiset.mem_add.1 h with h | h
            · exact ih.tasks_le k i sn' h
            · simp only [Multiset.mem_singleton, Prod.mk.injEq] at h
              rw [h.2]
          · rw [hTo k hk] at h; exact ih.tasks_le k i sn' h
        · intro i; simp only [cR, hcnt]; simp [ih.read_ne i]
        · intro i; simp only [cP, hcnt]; simp [ih.proceed_ne i]
        · intro i rsn h
          rw [hR]
          by_cases hi : i = dst
          · subst hi; simp only [hC', Config.apply_loc', ite_true] at h
            exact ih.r7_rsn i rsn h
          · simp only [hC', Config.apply_loc', hi, ite_false] at h
            exact ih.r7_rsn i rsn h
      | proceed =>
        obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
        have hsd : src ≠ dst := by
          intro he; subst he; have := ih.proceed_ne src
          simp only [cP] at this; rw [Multiset.count_eq_zero] at this; exact this hm
        set C' := C.apply dst _ (0 : Multiset (P × Msg V)) (C.net.erase (src, dst, .proceed))
          with hC'
        have hcnt : ∀ x, C'.net.count x =
            C.net.count x - if x = (src, dst, .proceed) then 1 else 0 := by
          intro x
          simp only [hC', Config.apply_net, outMsgs_zero, add_zero]
          by_cases hx : x = (src, dst, .proceed)
          · subst hx; rw [Multiset.count_erase_self]; simp
          · rw [Multiset.count_erase_of_ne hx]; simp [hx]
        have hpos : 1 ≤ C.net.count (src, dst, .proceed) := Multiset.one_le_count_iff_mem.2 hm
        have hR : ∀ i k, R C' i k = R C i k + if i = dst ∧ k = src then 1 else 0 := by
          intro i k; by_cases hi : i = dst
          · subst hi
            by_cases hk : k = src
            · subst hk; simp [hC', R]
            · simp [hC', R, hk, Function.update_apply]
          · simp [hC', R, hi]
        have hT : ∀ k, (C'.loc k).tasks = (C.loc k).tasks := by
          intro k; by_cases hk : k = dst
          · subst hk; simp [hC']
          · simp [hC', hk]
        have htk : ∀ k i, tk C' k i = tk C k i := by intro k i; simp [tk, hT]
        have hcP : ∀ k i, cP C' k i + (if i = dst ∧ k = src then 1 else 0) = cP C k i := by
          intro k i
          simp only [cP, hcnt]
          by_cases hh : i = dst ∧ k = src
          · obtain ⟨rfl, rfl⟩ := hh; simp; omega
          · have : (k, i, (Msg.proceed : Msg V)) ≠ (src, dst, Msg.proceed) := by
              simp only [ne_eq, Prod.mk.injEq, and_true]; tauto
            simp [hh, this]
        have hcR : ∀ i k, cR C' i k = cR C i k := by
          intro i k; simp only [cR, hcnt]; simp
        have hRii : ∀ i, R C' i i = R C i i := by
          intro i; rw [hR]; simp only [add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false]
          rintro ⟨rfl, rfl⟩; exact hsd rfl
        have hWW : ∀ k, W C' k k = W C k k := by
          intro k; by_cases hk : k = dst
          · subst hk; simp [hC', W]
          · simp [hC', W, hk]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i k hik
          have := ih.pipe i k hik
          have h1 := hcP k i
          have h2 := hR i k
          rw [hcR, htk, hRii]
          omega
        · intro i k hik hi hk
          have := ih.pipe_eq i k hik hi hk
          have h1 := hcP k i
          have h2 := hR i k
          rw [hcR, htk, hRii]
          omega
        · intro k i sn' h; rw [hT] at h; exact ih.tasks_ne k i sn' h
        · intro k i sn' h; rw [hT] at h; rw [hWW]; exact ih.tasks_le k i sn' h
        · intro i; simp only [cR, hcnt]; simp [ih.read_ne i]
        · intro i; simp only [cP, hcnt]; simp [ih.proceed_ne i]
        · intro i rsn h
          have hi' : i ≠ dst ∨ i ≠ src := by
            by_cases hi : i = dst
            · right; rw [hi]; exact Ne.symm hsd
            · left; exact hi
          rw [hRii]
          by_cases hi : i = dst
          · subst hi; simp only [hC', Config.apply_loc', ite_true] at h
            exact ih.r7_rsn i rsn h
          · simp only [hC', Config.apply_loc', hi, ite_false] at h
            exact ih.r7_rsn i rsn h
    | drop src dst m =>
      obtain ⟨hsrc, hm, -, rfl⟩ := step_drop hs
      have hcnt : ∀ x, (C.net.erase (src, dst, m)).count x =
          C.net.count x - if x = (src, dst, m) then 1 else 0 := by
        intro x
        by_cases hx : x = (src, dst, m)
        · subst hx; rw [Multiset.count_erase_self]; simp
        · rw [Multiset.count_erase_of_ne hx]; simp [hx]
      refine ⟨?_, ?_, ih.tasks_ne, ih.tasks_le, ?_, ?_, ih.r7_rsn⟩
      · intro i k hik
        have := ih.pipe i k hik
        simp only [cR, cP, tk, R, hcnt] at this ⊢
        omega
      · intro i k hik hi hk
        have := ih.pipe_eq i k hik hi hk
        simp only [cR, cP, tk, R, hcnt] at this ⊢
        have h1 : (i, k, Msg.read) ≠ (src, dst, m) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hi (he.1 ▸ hsrc)
        have h2 : (k, i, Msg.proceed) ≠ (src, dst, m) := by
          intro he; simp only [Prod.mk.injEq] at he; exact hk (he.1 ▸ hsrc)
        simp only [h1, h2, if_false]
        omega
      · intro i; have := ih.read_ne i; simp only [cR, hcnt] at this ⊢; omega
      · intro i; have := ih.proceed_ne i; simp only [cP, hcnt] at this ⊢; omega
    | crash p =>
      obtain ⟨-, -, rfl⟩ := step_crash hs
      refine ⟨ih.pipe, ?_, ih.tasks_ne, ih.tasks_le, ih.read_ne, ih.proceed_ne, ih.r7_rsn⟩
      intro i k hik hi hk
      exact ih.pipe_eq i k hik (fun h => hi (Finset.mem_insert_of_mem h))
        (fun h => hk (Finset.mem_insert_of_mem h))
    | skip =>
      obtain ⟨rfl, -⟩ := step_skip hs
      exact ih

end Podc.TwoBit
