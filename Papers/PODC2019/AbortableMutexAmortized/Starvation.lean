import Papers.PODC2019.AbortableMutexAmortized.StarvationDefs

/-!
# Starvation freedom (Section 4.1, Appendix B)

* `lemma_4_3` — `δ(p) ≥ 1`, and `δ(p) = 1` iff `p` is in the CS.
* `promoters_nonempty`, `promoters_not_l1` — `Ψ(p)` is a nonempty set of processes outside the
  Remainder section (claimed in the text of Section 4.1).
* `lemma_4_4_part1`, `lemma_4_4_part2` — Lemma 4.4.
* `theorem_4_5` — starvation freedom.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-! ## Frame lemmas for a step -/

section Frame

variable {s : State n} {π x : Fin n} {ab : Bool}

theorem sf_pc_ne (h : x ≠ π) : (step s π ab).pc x = s.pc x := by
  unfold step; split <;> (try split) <;> (try split) <;>
    simp [fasPred, line9, wake, Function.update_of_ne h]

theorem sf_v_ne (h : x ≠ π) : (step s π ab).v x = s.v x := by
  unfold step; split <;> (try split) <;> (try split) <;>
    simp [fasPred, line9, wake, Function.update_of_ne h]

theorem sf_pred_ne (h : x ≠ π) : (step s π ab).pred x = s.pred x := by
  unfold step; split <;> (try split) <;> (try split) <;>
    simp [fasPred, line9, wake, Function.update_of_ne h]

theorem sf_mynode_ne (h : x ≠ π) : (step s π ab).mynode x = s.mynode x := by
  unfold step; split <;> (try split) <;> (try split) <;>
    simp [fasPred, line9, wake, Function.update_of_ne h]

/-- The go-flag of another process only changes when `π` wakes it at line 8 or 11. -/
theorem sf_go_ne (h : x ≠ π) :
    (step s π ab).go x = s.go x ∨
      ((s.pc π = .l8 ∨ s.pc π = .l11) ∧ s.v π = .go x ∧ (step s π ab).go x = true) := by
  unfold step; split <;> (try split) <;> (try split) <;>
    simp_all [fasPred, line9, wake] <;>
    · rcases s.v π with _ | _ | _ | q <;> simp [Function.update_apply]
      by_cases hq : x = q <;> simp [hq]

/-- A process gets to line 8 or 11 only from line 7 or 10, with the old contents of its node. -/
theorem sf_enter (h : (step s π ab).pc π = .l8 ∨ (step s π ab).pc π = .l11) :
    (s.pc π = .l7 ∨ s.pc π = .l10) ∧ (step s π ab).v π = s.node (s.mynode π) := by
  revert h
  unfold step; split <;> (try split) <;> (try split) <;>
    simp_all [fasPred, line9, wake, loopPC] <;>
    (split <;> simp)

/-- Waking at line 8 or 11 sets the go-flag. -/
theorem sf_wake_go {q : Fin n} (h : s.pc π = .l8 ∨ s.pc π = .l11) (hv : s.v π = .go q) :
    (step s π ab).go q = true := by
  rcases h with h | h <;> simp [step, h, wake, hv]

/-- A process in the Try section that does not abort stays in the Try section or enters the CS. -/
theorem sf_try_step {p : Fin n} (hp : InTry (s.pc p)) (hab : ¬(π = p ∧ ab = true)) :
    InTry ((step s π ab).pc p) ∨ (step s π ab).pc p = .l7 := by
  by_cases hπ : p = π
  · subst hπ
    have hab : ab = false := by simpa using hab
    subst hab
    unfold InTry at hp ⊢
    rcases hp with h | h | h | h <;>
      simp [step, h, fasPred, loopPC] <;> (try split) <;> simp_all
  · rw [sf_pc_ne hπ]; exact Or.inl hp

end Frame

/-! ## Queue prefixes under a step -/

/-- The prefix of `Q` ending at `p` either stays the same or gets shorter in a step. -/
theorem sf_prefix_step {π p : Fin n} {Q Q' : List (Fin n)} (h : QStep π Q Q') (hnd : Q.Nodup)
    (hp : p ∈ Q) (hp' : p ∈ Q') :
    qPrefix Q' p = qPrefix Q p ∨ (qPrefix Q' p).length < (qPrefix Q p).length := by
  cases h with
  | same => exact Or.inl rfl
  | enq =>
    left
    obtain ⟨A, B, rfl, hA⟩ := sf_exists_split_mem hnd hp
    rw [show A ++ p :: B ++ [π] = A ++ p :: (B ++ [π]) by simp, qPrefix_eq hA, qPrefix_eq hA]
  | splice L x R =>
    have hd := List.nodup_append.1 hnd
    rcases List.mem_append.1 hp' with hL | hR
    · left
      obtain ⟨A, B, rfl, hA⟩ := sf_exists_split_mem hd.1 hL
      rw [show A ++ p :: B ++ π :: R = A ++ p :: (B ++ π :: R) by simp, qPrefix_eq hA,
        show A ++ p :: B ++ x :: π :: R = A ++ p :: (B ++ x :: π :: R) by simp, qPrefix_eq hA]
    · right
      have hd2 := List.nodup_cons.1 hd.2.1
      obtain ⟨A, B, hAB, hA⟩ := sf_exists_split_mem hd2.2 hR
      have hpL : p ∉ L := fun h => hd.2.2 p h p (by simp [hR]) rfl
      have hpx : p ≠ x := fun e => hd2.1 (e ▸ hR)
      rw [hAB, show L ++ (A ++ p :: B) = (L ++ A) ++ p :: B by simp,
        show L ++ x :: (A ++ p :: B) = (L ++ x :: A) ++ p :: B by simp,
        qPrefix_eq (by simp [hpL, hA]), qPrefix_eq (by simp [hpL, hA, hpx])]
      simp
  | deq R =>
    right
    have hd := List.nodup_cons.1 hnd
    obtain ⟨A, B, rfl, hA⟩ := sf_exists_split_mem hd.2 hp'
    have hpπ : p ≠ π := fun e => hd.1 (e ▸ hp')
    rw [show π :: (A ++ p :: B) = (π :: A) ++ p :: B by simp, qPrefix_eq hA,
      qPrefix_eq (by simp [hA, hpπ])]
    simp

/-! ## The queue around `p` -/

theorem sf_mem_Qof_of_try {s : State n} (h : Inv s) {p : Fin n}
    (hp : InTry (s.pc p) ∨ s.pc p = .l7) : p ∈ Qof s := by
  refine h.mem_Qof.2 (Or.inl ?_)
  rcases hp with (e | e | e | e) | e <;> simp [e, PC.act]

theorem sf_pc_ne_l1 {c : PC} (hp : InTry c ∨ c = .l7) : c ≠ .l1 := by
  rcases hp with (e | e | e | e) | e <;> simp [e]

/-- The predecessor node of `q_m`: `a₀` if `m = 1`, else the node of `q_{m-1}`. -/
theorem sf_pred_split {s : State n} {Q C E : List (Fin n)} {a0 : Node n} {qm : Fin n}
    (hs : Struct s Q a0) (hQ : Q = C ++ qm :: E) :
    (C = [] ∧ s.pred qm = a0) ∨ ∃ x ∈ C, s.pred qm = s.mynode x := by
  have hc := hs.ok.chain
  rw [hQ] at hc
  rcases List.eq_nil_or_concat C with rfl | ⟨C0, x, rfl⟩
  · exact Or.inl ⟨rfl, hc.1⟩
  · right
    refine ⟨x, by simp, ?_⟩
    have := ((chain_append _ _ _).1 hc).2.1
    rwa [List.concat_eq_append, lastN_concat] at this

/-- Lemma 4.3: for a process `p` in the Try section or CS, `δ(p) ≥ 1`, and `δ(p) = 1` iff `p` is
in the CS. -/
theorem lemma_4_3 {s : State n} (h : Inv s) {p : Fin n} (hp : InTry (s.pc p) ∨ s.pc p = .l7) :
    1 ≤ delta s p ∧ (delta s p = 1 ↔ s.pc p = .l7) := by
  have hpQ := sf_mem_Qof_of_try h hp
  obtain ⟨A, B, hQ, hA⟩ := sf_exists_split_mem h.struct.ok.nodup hpQ
  have hP : qPrefix (Qof s) p = A ++ [p] := by rw [hQ, qPrefix_eq hA]
  unfold delta
  rw [hP]
  rcases A with _ | ⟨a, A⟩
  · have h1 := one_le_fDigit (h.mem_Qof.1 hpQ)
    simp [deltaDigits, sf_pc_ne_l1 hp, fDigit_eq_one.symm]
    omega
  · have ha : InQ s a := h.mem_Qof.1 (by rw [hQ]; simp)
    have hge := le_decVal_deltaDigits (s := s) (P := A ++ [p]) (one_le_fDigit ha)
    have h10 : 10 ≤ 10 ^ (A ++ [p]).length :=
      le_self_pow₀ (by norm_num) (by simp)
    have hne : s.pc p ≠ .l7 := by
      intro e
      have h0 := h.loc.i10 p e
      obtain ⟨R, hR⟩ := h.struct.ok.head hpQ h0
      rw [hQ] at hR
      simp only [List.cons_append, List.cons.injEq] at hR
      exact hA (by simp [hR.1])
    simp only [List.cons_append] at hge ⊢
    refine ⟨by omega, ?_⟩
    simp only [hne, iff_false]; omega

/-! ## Steps of the leader `q_m` -/

/-- If `q_{m-1}` (at line 1, in `Q`) stays in the queue after a step of another process that does
not touch `q_{m-1}`'s local variables, its node still holds `pred_{q_{m-1}}`. -/
theorem sf_node_of_stay {s t : State n} {x : Fin n} (hx : s.pc x = .l1) (hpc : t.pc x = s.pc x)
    (hmy : t.mynode x = s.mynode x) (hpr : t.pred x = s.pred x) (hin : InQ t x) :
    t.node (s.mynode x) = .addr (s.pred x) := by
  rcases hin with h | ⟨-, h⟩
  · rw [hpc, hx] at h; simp [PC.act] at h
  · rwa [hmy, hpr] at h

/-- The effect of a step of the leader `q_m` (proof of Lemma 4.4, Appendix B), assuming that all of
`q₁, …, q_m` are still in the queue afterwards: either the digit `f(q_m)` decreases, or `q_m` is
waiting at line 4 with `go = false` and the step changes nothing. (When `m > 1` and `q_m` executes
line 3, 6 or 9, or when `q_m` exits, some `q_j`, `j ≤ m`, leaves the queue; that case is handled
by the length argument.) -/
theorem sf_leader_step {s : State n} (h : Inv s) {C E : List (Fin n)} {qm : Fin n} {ab : Bool}
    (hQ : Qof s = C ++ qm :: E) (hC : ∀ c ∈ C, s.pc c = .l1) (hqm : s.pc qm ≠ .l1)
    (hin : ∀ y ∈ C ++ [qm], InQ (step s qm ab) y) :
    fDigit (step s qm ab) qm < fDigit s qm ∨
      (step s qm ab = s ∧ s.pc qm = .l4 ∧ s.go qm = false) := by
  have hs := h.struct
  have hl := h.loc
  have hqQ : InQ s qm := h.mem_Qof.1 (by rw [hQ]; simp)
  have hpred := sf_pred_split hs hQ
  -- `m = 1`: the leader's predecessor node `a₀` holds the token
  have htoken : C = [] → s.pc qm ≠ .l7 → s.node (s.pred qm) = .token := by
    rintro rfl h7
    rcases hpred with ⟨-, hpa⟩ | ⟨x, hx, -⟩
    · rw [hpa]
      refine hl.i9a (fun y hy hy7 => ?_)
      have hyQ : y ∈ Qof s := h.mem_Qof.2 (Or.inl (by simp [hy7, PC.act]))
      obtain ⟨R, hR⟩ := hs.ok.head hyQ hy
      rw [hQ] at hR
      simp only [List.nil_append, List.cons.injEq] at hR
      exact h7 (hR.1 ▸ hy7)
    · simp at hx
  -- `m > 1`: the leader cannot execute lines 3, 6, 9 without removing `q_{m-1}`
  have hx_ne : ∀ x ∈ C, x ≠ qm := fun x hx e => hqm (e ▸ hC x hx)
  have hfas : s.pc qm ≠ .l7 → (∀ y ∈ C ++ [qm], InQ (fasPred s qm) y) →
      (fasPred s qm).pc qm = .l7 := by
    intro h7 hin'
    rcases hpred with ⟨rfl, -⟩ | ⟨x, hx, hpx⟩
    · simp [fasPred, htoken rfl h7, loopPC]
    · have hxn := hx_ne x hx
      have := sf_node_of_stay (hC x hx) (by simp [fasPred, Function.update_of_ne hxn])
        (by simp [fasPred]) (by simp [fasPred, Function.update_of_ne hxn])
        (hin' x (by simp [hx]))
      simp [fasPred, ← hpx] at this
  have hl9 : s.pc qm ≠ .l7 → (∀ y ∈ C ++ [qm], InQ (line9 s qm) y) →
      (line9 s qm).pc qm = .l7 := by
    intro h7 hin'
    rcases hpred with ⟨rfl, -⟩ | ⟨x, hx, hpx⟩
    · simp [line9, htoken rfl h7]
    · have hxn := hx_ne x hx
      have := sf_node_of_stay (hC x hx) (by simp [line9, Function.update_of_ne hxn])
        (by simp [line9]) (by simp [line9, Function.update_of_ne hxn])
        (hin' x (by simp [hx]))
      simp [line9, ← hpx] at this
  have hf7 : ∀ t : State n, t.pc qm = .l7 → fDigit t qm = 1 := fun t e => fDigit_eq_one.2 e
  rcases hpc : s.pc qm
  · exact absurd hpc hqm
  · simp [InQ, hpc, PC.act, PC.ab] at hqQ
  · -- line 3
    left
    have e : step s qm ab = fasPred s qm := by simp [step, hpc]
    rw [e] at hin ⊢
    rw [hf7 _ (hfas (by simp [hpc]) hin)]; simp [fDigit, hpc]
  · -- line 4
    cases ab
    · by_cases hg : s.go qm
      · left; simp [step, hpc, hg, fDigit]
      · right; simp [step, hpc, hg]
    · left
      have e : step s qm true = line9 s qm := by simp [step, hpc]
      rw [e] at hin ⊢
      rw [hf7 _ (hl9 (by simp [hpc]) hin)]; simp [fDigit, hpc]; split <;> omega
  · -- line 5
    left
    cases ab
    · simp [step, hpc, fDigit]
    · have e : step s qm true = line9 s qm := by simp [step, hpc]
      rw [e] at hin ⊢
      rw [hf7 _ (hl9 (by simp [hpc]) hin)]; simp [fDigit, hpc]
  · -- line 6
    left
    cases ab
    · have e : step s qm false = fasPred s qm := by simp [step, hpc]
      rw [e] at hin ⊢
      rw [hf7 _ (hfas (by simp [hpc]) hin)]; simp [fDigit, hpc]
    · have e : step s qm true = line9 s qm := by simp [step, hpc]
      rw [e] at hin ⊢
      rw [hf7 _ (hl9 (by simp [hpc]) hin)]; simp [fDigit, hpc]
  · -- line 7: `q_m = q₁` leaves the queue
    exfalso
    have h0 := hl.i10 qm hpc
    have hq := hin qm (by simp)
    have hmy : s.mynode qm ≠ s.pred qm := h0 ▸ hs.a0_ne qm
    have h9b := hl.i9b qm h0 hpc
    rw [← h0] at h9b
    by_cases hn : s.node (s.mynode qm) = .nil
    · simp [step, hpc, hn, InQ, PC.act, PC.ab, Function.update_of_ne hmy.symm] at hq
      rcases h9b with h9 | h9 <;> simp [h9] at hq
    · simp [step, hpc, hn, InQ, PC.act, PC.ab] at hq
  · simp [InQ, hpc, PC.act, PC.ab] at hqQ
  · -- line 9
    left
    have e : step s qm ab = line9 s qm := by simp [step, hpc]
    rw [e] at hin ⊢
    rw [hf7 _ (hl9 (by simp [hpc]) hin)]; simp [fDigit, hpc]
  · -- line 10
    left
    by_cases hn : s.node (s.mynode qm) = .nil <;> simp [step, hpc, fDigit, hn]
  · -- line 11
    left
    simp [step, hpc, wake, fDigit]

/-! ## The promoters set -/

/-- The decomposition of `p`'s queue prefix `q₁ … q_i` as `C ++ q_m :: D` (`C` at line 1). -/
theorem sf_decomp {s : State n} (h : Inv s) {p : Fin n} (hp : InTry (s.pc p) ∨ s.pc p = .l7) :
    ∃ C qm D B, qPrefix (Qof s) p = C ++ qm :: D ∧ Qof s = (C ++ qm :: D) ++ B ∧
      (∀ c ∈ C, s.pc c = .l1) ∧ s.pc qm ≠ .l1 := by
  obtain ⟨A, B, hQ, hA⟩ := sf_exists_split_mem h.struct.ok.nodup (sf_mem_Qof_of_try h hp)
  obtain ⟨C, qm, D, hAD, hC, hqm⟩ :=
    sf_exists_split (s := s) (P := A ++ [p]) ⟨p, by simp, sf_pc_ne_l1 hp⟩
  refine ⟨C, qm, D, B, by rw [hQ, qPrefix_eq hA, hAD], by rw [hQ, ← hAD]; simp, hC, hqm⟩

theorem sf_promoters_eq {s : State n} {p qm : Fin n} {C D : List (Fin n)}
    (hP : qPrefix (Qof s) p = C ++ qm :: D) (hC : ∀ c ∈ C, s.pc c = .l1) (hqm : s.pc qm ≠ .l1) :
    promoters s p = psiOf s qm := by
  unfold promoters; rw [hP, leaderQm_split hC hqm]

/-- Section 4.1: for `p` in the Try section or CS, the promoters set `Ψ(p)` is nonempty and
consists of processes outside the Remainder section. (For `m ≥ 2`, `q_m` is never waiting at
line 4 with `go = false`, by `I11`.) -/
theorem promoters_spec {s : State n} (h : Inv s) {p : Fin n}
    (hp : InTry (s.pc p) ∨ s.pc p = .l7) :
    (promoters s p).Nonempty ∧ ∀ r ∈ promoters s p, s.pc r ≠ .l1 := by
  obtain ⟨C, qm, D, B, hP, hQ, hC, hqm⟩ := sf_decomp h hp
  rw [sf_promoters_eq hP hC hqm]
  unfold psiOf
  split_ifs with hcond
  · refine ⟨?_, fun r hr => by rcases hr.1 with e | e <;> simp [e]⟩
    rcases sf_pred_split (C := C) (qm := qm) (E := D ++ B) h.struct (by rw [hQ]; simp) with ⟨-, hpa⟩ | ⟨x, hx, hpx⟩
    · obtain ⟨r, hr8, hrv⟩ := h.loc.i11a qm hpa hcond.1 hcond.2
      exact ⟨r, Or.inl hr8, hrv⟩
    · exfalso
      have hxQ : InQ s x := h.mem_Qof.1 (by rw [hQ]; simp [hx])
      have hx1 := hC x hx
      have hxn : s.node (s.mynode x) = .addr (s.pred x) :=
        (hxQ.resolve_left (by simp [hx1, PC.act])).2
      rcases h.loc.i11b x qm hxQ hpx hcond.1 hcond.2 with e | ⟨-, e, -⟩
      · rw [hxn] at e; simp at e
      · rw [hx1] at e; simp at e
  · exact ⟨⟨qm, rfl⟩, fun r hr => by rw [Set.mem_singleton_iff.1 hr]; exact hqm⟩

/-! ## Lemma 4.4 -/

/-- Lemma 4.4 in combined form: after a step of `π` (other than an aborting step of `p` itself),
either `δ(p)` decreases, or `π ∉ Ψ(p)` and both `δ(p)` and `Ψ(p)` are unchanged. -/
theorem sf_core {s : State n} (h : Inv s) {p π : Fin n} {ab : Bool} (hp : InTry (s.pc p))
    (hab : ¬(π = p ∧ ab = true)) :
    delta (step s π ab) p < delta s p ∨
      (π ∉ promoters s p ∧ delta (step s π ab) p = delta s p ∧
        promoters (step s π ab) p = promoters s p) := by
  have h' : Inv (step s π ab) := h.stepInv π ab
  have hpQ : p ∈ Qof s := sf_mem_Qof_of_try h (Or.inl hp)
  have hpQ' : p ∈ Qof (step s π ab) := sf_mem_Qof_of_try h' (sf_try_step hp hab)
  obtain ⟨C, qm, D, B, hP, hQ, hC, hqm⟩ := sf_decomp h (Or.inl hp)
  have hQ2 : Qof s = C ++ qm :: (D ++ B) := by rw [hQ]; simp
  rcases sf_prefix_step (h.qstep π ab) h.struct.ok.nodup hpQ hpQ' with hP' | hP'
  swap
  · -- some process before `p` left the queue: `δ(p)` has fewer digits
    left
    unfold delta
    rw [hP] at hP' ⊢
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, C ++ qm :: D = y :: rest := by cases C <;> simp
    have hyQ : InQ s y := h.mem_Qof.1 (by rw [hQ, hyr]; simp)
    rw [hyr] at hP' ⊢
    have h1 := decVal_deltaDigits_lt (step s π ab) (qPrefix (Qof (step s π ab)) p)
    have h2 := le_decVal_deltaDigits (P := rest) (one_le_fDigit hyQ)
    have h3 : 10 ^ (qPrefix (Qof (step s π ab)) p).length ≤ 10 ^ rest.length :=
      Nat.pow_le_pow_right (by norm_num) (by simp at hP'; omega)
    omega
  -- the prefix `q₁ … q_i` is unchanged
  have hin : ∀ y ∈ C ++ qm :: D, InQ (step s π ab) y := fun y hy =>
    h'.mem_Qof.1 (List.mem_of_mem_take (by
      change y ∈ qPrefix (Qof (step s π ab)) p; rw [hP', hP]; exact hy))
  have hnd : (C ++ qm :: D).Nodup := (hQ ▸ h.struct.ok.nodup).of_append_left
  have hdelta : delta s p = decVal (deltaDigits s (C ++ qm :: D)) := by unfold delta; rw [hP]
  have hdelta' : delta (step s π ab) p = decVal (deltaDigits (step s π ab) (C ++ qm :: D)) := by
    unfold delta; rw [hP', hP]
  rw [hdelta, hdelta', sf_promoters_eq hP hC hqm]
  by_cases hπC : π ∈ C
  · -- `π = q_j`, `j < m`: it moves from line 1 to line 3, the digit `d_j` drops from 3 to 2
    left
    obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hπC
    have hπ1 : s.pc π = .l1 := hC π (by simp)
    have hπQ : InQ s π := h.mem_Qof.1 (by rw [hQ]; simp)
    have hn : s.node (s.mynode π) = .addr (s.pred π) :=
      (hπQ.resolve_left (by simp [hπ1, PC.act])).2
    have hnd1 : π ∉ C1 := by
      intro hm
      have := (List.nodup_append.1 hnd).1
      exact (List.nodup_append.1 this).2.2 π hm π (by simp) rfl
    rw [show C1 ++ π :: C2 ++ qm :: D = C1 ++ π :: (C2 ++ qm :: D) by simp]
    refine decVal_lt_of_split (fun c hc => hC c (by simp [hc])) (fun c hc => ?_) ?_
    · rw [sf_pc_ne (ne_of_mem_of_not_mem hc hnd1)]; exact hC c (by simp [hc])
    · simp [step, hπ1, hn, fDigit]
  have hx_ne : ∀ c ∈ C, c ≠ qm := fun c hc e => hqm (e ▸ hC c hc)
  by_cases hπq : π = qm
  · -- `π = q_m`
    subst hπq
    rcases sf_leader_step h hQ2 hC hqm (ab := ab) (fun y hy => hin y (by
        rcases List.mem_append.1 hy with hy | hy
        · simp [hy]
        · simp at hy; simp [hy])) with hlt | ⟨heq, h4, hg⟩
    · left
      exact decVal_lt_of_split hC
        (fun c hc => by rw [sf_pc_ne (hx_ne c hc)]; exact hC c hc) hlt
    · right
      rw [heq, sf_promoters_eq hP hC hqm]
      exact ⟨by simp [psiOf, h4, hg], rfl, rfl⟩
  -- `π` is none of `q₁, …, q_m`
  have hCpc : ∀ c ∈ C, (step s π ab).pc c = .l1 := fun c hc => by
    rw [sf_pc_ne (ne_of_mem_of_not_mem hc hπC)]; exact hC c hc
  have hqpc : (step s π ab).pc qm = s.pc qm := sf_pc_ne (Ne.symm hπq)
  have hqm' : (step s π ab).pc qm ≠ .l1 := hqpc ▸ hqm
  rw [sf_promoters_eq (hP'.trans hP) hCpc hqm']
  have hdig : fDigit (step s π ab) qm = fDigit s qm →
      deltaDigits (step s π ab) (C ++ qm :: D) = deltaDigits s (C ++ qm :: D) := by
    intro e; rw [deltaDigits_split hC hqm, deltaDigits_split hCpc hqm', e]
  by_cases hcond : s.pc qm = .l4 ∧ s.go qm = false
  · by_cases hπΨ : (s.pc π = .l8 ∨ s.pc π = .l11) ∧ s.v π = .go qm
    · -- `π ∈ Ψ(p)` wakes `q_m`: the digit `d_m` drops from 9 to 8
      left
      apply decVal_lt_of_split hC hCpc
      have := sf_wake_go hπΨ.1 hπΨ.2 (ab := ab)
      simp [fDigit, hqpc, hcond.1, hcond.2, this]
    · right
      have hgo : (step s π ab).go qm = s.go qm :=
        (sf_go_ne (Ne.symm hπq)).resolve_right (fun ⟨a, b, _⟩ => hπΨ ⟨a, b⟩)
      have hf : fDigit (step s π ab) qm = fDigit s qm := by simp [fDigit, hqpc, hgo]
      refine ⟨by simpa [psiOf, hcond] using hπΨ, by rw [hdig hf], ?_⟩
      simp only [psiOf, hqpc, hgo, hcond, and_self, ↓reduceIte]
      ext r
      by_cases hr : r = π
      · subst hr
        refine ⟨fun ⟨h811, hv⟩ => ?_, fun h => absurd h hπΨ⟩
        -- `π` cannot newly become a promoter (`I7`)
        exfalso
        obtain ⟨h710, hv'⟩ := sf_enter h811
        rw [hv'] at hv
        have hact : (s.pc r).act = true := by rcases h710 with e | e <;> simp [e, PC.act]
        rcases h.loc.i7 r hact with e | ⟨y, -, hy, hy'⟩
        · rw [e] at hv; simp at hv
        · rw [hv] at hy'
          simp only [Val.go.injEq] at hy'
          subst hy'
          rcases sf_pred_split h.struct hQ2 with ⟨-, hpa⟩ | ⟨x, hx, hpx⟩
          · exact h.struct.a0_ne r (hy.symm.trans hpa)
          · have := h.struct.ok.inj (hy.symm.trans hpx)
            exact hπC (this ▸ hx)
      · simp [sf_pc_ne hr, sf_v_ne hr]
  · right
    have hgo : s.pc qm = .l4 → (step s π ab).go qm = true := by
      intro e4
      have hg : s.go qm = true := by simpa [e4] using hcond
      rcases sf_go_ne (Ne.symm hπq) (s := s) (ab := ab) with e | ⟨-, -, e⟩
      · rw [e, hg]
      · exact e
    have hf : fDigit (step s π ab) qm = fDigit s qm := by
      unfold fDigit; rw [hqpc]
      split <;> try rfl
      next e4 => simp [hgo e4, by simpa [e4] using hcond]
    have hcond' : ¬((step s π ab).pc qm = .l4 ∧ (step s π ab).go qm = false) := by
      rintro ⟨e4, eg⟩
      rw [hqpc] at e4
      rw [hgo e4] at eg; simp at eg
    refine ⟨by simp [psiOf, hcond, hπq], by rw [hdig hf], ?_⟩
    simp only [psiOf, hcond, hcond', ↓reduceIte]

/-- Lemma 4.4 (1): if `p` is in the Try section and a promoter `π ∈ Ψ(p)` takes a step, `δ(p)`
decreases. (An aborting step of `p` itself is excluded: `p` then leaves the Try section and `δ(p)`
is undefined.) -/
theorem lemma_4_4_part1 {s : State n} (h : Inv s) {p π : Fin n} {ab : Bool}
    (hp : InTry (s.pc p)) (hab : ¬(π = p ∧ ab = true)) (hπ : π ∈ promoters s p) :
    delta (step s π ab) p < delta s p :=
  (sf_core h hp hab).resolve_right (fun h' => h'.1 hπ)

/-- Lemma 4.4 (2): if `p` is in the Try section and a process `π ∉ Ψ(p)` takes a step, then
either `δ(p)` decreases, or `δ(p)` and `Ψ(p)` stay the same. -/
theorem lemma_4_4_part2 {s : State n} (h : Inv s) {p π : Fin n} {ab : Bool}
    (hp : InTry (s.pc p)) (hab : ¬(π = p ∧ ab = true)) (_hπ : π ∉ promoters s p) :
    delta (step s π ab) p < delta s p ∨
      (delta (step s π ab) p = delta s p ∧ promoters (step s π ab) p = promoters s p) :=
  (sf_core h hp hab).imp_right (fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩)

/-! ## Theorem 4.5 -/

/-- Fairness of a schedule: a process outside the Remainder section (line 1) eventually takes a
step. (In particular no process stays in the CS, the Exit or the Abort section forever.) Processes
in the Remainder section may stop taking steps. -/
def Fair (σ : ℕ → Fin n × Bool) : Prop :=
  ∀ q t, (exec σ t).pc q ≠ .l1 → ∃ t' ≥ t, (σ t').1 = q

/-- Non-vacuity: the round-robin schedule without aborts is fair. -/
theorem fair_roundRobin (hn : 0 < n) :
    Fair (fun t => ((⟨t % n, Nat.mod_lt _ hn⟩ : Fin n), false)) := by
  intro q t _
  refine ⟨n * t + q, ?_, ?_⟩
  · have : t ≤ n * t := Nat.le_mul_of_pos_left t hn
    omega
  · ext; simp [Nat.mod_eq_of_lt q.2]

theorem sf_pc_stay (σ : ℕ → Fin n × Bool) {q : Fin n} {t : ℕ} :
    ∀ k, (∀ j < k, (σ (t + j)).1 ≠ q) → (exec σ (t + k)).pc q = (exec σ t).pc q
  | 0, _ => rfl
  | k + 1, h => by
    change (step (exec σ (t + k)) (σ (t + k)).1 (σ (t + k)).2).pc q = _
    rw [sf_pc_ne (Ne.symm (h k (by omega))),
      sf_pc_stay σ k (fun j hj => h j (by omega))]

theorem sf_reach_cs (σ : ℕ → Fin n × Bool) (hfair : Fair σ) {p : Fin n}
    (hnab : ∀ t, σ t ≠ (p, true)) (d : ℕ) :
    ∀ t, delta (exec σ t) p = d → InTry ((exec σ t).pc p) →
      ∃ t' ≥ t, (exec σ t').pc p = .l7 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro t hd hp
  have hinv : ∀ t, Inv (exec σ t) := fun t => (reachable_exec σ t).inv
  have hab : ∀ t, ¬((σ t).1 = p ∧ (σ t).2 = true) := fun t ⟨h1, h2⟩ =>
    hnab t (Prod.ext h1 h2)
  -- once `δ(p)` drops below `d`, the induction hypothesis applies
  have hdone : ∀ t', t ≤ t' → InTry ((exec σ t').pc p) ∨ (exec σ t').pc p = .l7 →
      delta (exec σ t') p < d → ∃ t'' ≥ t, (exec σ t'').pc p = .l7 := by
    intro t' ht' hp' hlt
    rcases hp' with hp' | hp'
    · obtain ⟨t'', h1, h2⟩ := ih _ hlt t' rfl hp'
      exact ⟨t'', by omega, h2⟩
    · exact ⟨t', ht', hp'⟩
  -- until then `δ(p)` and `Ψ(p)` stay unchanged
  have hclaim : ∀ j, (∃ t' ≥ t, (exec σ t').pc p = .l7) ∨
      (delta (exec σ (t + j)) p = d ∧ promoters (exec σ (t + j)) p = promoters (exec σ t) p ∧
        InTry ((exec σ (t + j)).pc p)) := by
    intro j
    induction j with
    | zero => exact Or.inr ⟨hd, rfl, hp⟩
    | succ j ihj =>
      rcases ihj with hj | ⟨hjd, hjΨ, hjp⟩
      · exact Or.inl hj
      have hstep := sf_try_step (π := (σ (t + j)).1) (ab := (σ (t + j)).2) hjp (hab (t + j))
      rcases sf_core (hinv (t + j)) hjp (hab (t + j)) with hlt | ⟨-, hd', hΨ'⟩
      · exact Or.inl (hdone (t + (j + 1)) (by omega) hstep (hjd ▸ hlt))
      · rcases hstep with hstep | hstep
        · exact Or.inr ⟨hd'.trans hjd, hΨ'.trans hjΨ, hstep⟩
        · exact Or.inl ⟨t + (j + 1), by omega, hstep⟩
  -- a promoter eventually takes a step
  obtain ⟨⟨r, hr⟩, hr1⟩ := promoters_spec (hinv t) (Or.inl hp)
  obtain ⟨t1, ht1, hσ⟩ := hfair r t (hr1 r hr)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht1
  rcases hclaim k with hk | ⟨hkd, hkΨ, hkp⟩
  · exact hk
  have hlt := lemma_4_4_part1 (hinv (t + k)) hkp (hab (t + k)) (hσ ▸ hkΨ ▸ hr)
  exact hdone (t + k + 1) (by omega) (sf_try_step hkp (hab (t + k))) (hkd ▸ hlt)

/-- Theorem 4.5 (starvation freedom): in a fair execution, a process in the Try section (lines 3–6;
we also allow line 2, the second line of the doorway) that does not abort eventually enters the CS
(line 7). -/
theorem theorem_4_5 (σ : ℕ → Fin n × Bool) (hfair : Fair σ) {p : Fin n}
    (hnab : ∀ t, σ t ≠ (p, true)) {t : ℕ}
    (hp : (exec σ t).pc p = .l2 ∨ InTry ((exec σ t).pc p)) :
    ∃ t' ≥ t, (exec σ t').pc p = .l7 := by
  rcases hp with hp | hp
  · have hex : ∃ k, (σ (t + k)).1 = p := by
      obtain ⟨t1, ht1, h1⟩ := hfair p t (by simp [hp])
      exact ⟨t1 - t, by rwa [Nat.add_sub_cancel' ht1]⟩
    have hk := Nat.find_spec hex
    have hstay := sf_pc_stay σ (Nat.find hex) (fun j hj => Nat.find_min hex hj)
    rw [hp] at hstay
    have h3 : (exec σ (t + Nat.find hex + 1)).pc p = .l3 := by
      change (step (exec σ (t + Nat.find hex)) (σ (t + Nat.find hex)).1
        (σ (t + Nat.find hex)).2).pc p = _
      rw [hk]; simp [step, hstay]
    obtain ⟨t', ht', h7⟩ := sf_reach_cs σ hfair hnab _ _ rfl (Or.inl h3)
    exact ⟨t', by omega, h7⟩
  · exact sf_reach_cs σ hfair hnab _ t rfl hp

end Podc.AbortableMutexAmortized
