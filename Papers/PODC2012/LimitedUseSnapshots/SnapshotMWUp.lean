import Papers.PODC2012.LimitedUseSnapshots.SnapshotMWStep

/-!
# Algorithm 4: `Update(s, i, record_i)` (Line 3), the linearization point of `MW-Update`s

When process `p` writes its record with timestamp `t` for component `j` and `t` exceeds the
largest timestamp `M` of component `j` in `s`, all pending `MW-Update`s of component `j` with a
determined timestamp in `(M, t)` are linearized, followed by `p`'s own operation (so the value of
`p` wins, as the largest timestamp does in `CombineScan`).
-/

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable {n c : ℕ} {W : Type} {w₀ : Fin c → W} [NeZero n]
  {α : List (Label (Fin n) (mwSnap c W w₀))} {C C' : Cfg4 n c W w₀} {L : Lin4 c W w₀ n}

lemma inv4_step_up (hα : (alg4 n w₀).run α = some C) (hI : Inv4 α C L) {p : Fin n}
    {j : Fin c} (hpc : (C.loc p).pc = .up j) (h : (alg4 n w₀).step C (.tau p) = some C') :
    ∃ L', Inv4 (α ++ [.tau p]) C' L' := by
  classical
  have hP := hI.proc p
  simp only [PInv4, hpc] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  set R := (C.loc p).rcd with hR
  set t := (R j).2 with ht
  set v := (R j).1 with hv
  set S := C.mem .s with hSdef
  set M := maxTs S j with hMdef
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act4 (w₀ := w₀) p (C.loc p) = .access .s (SOp.update p R)
      (fun _ => ⟨R, .ack⟩) := by simp [act4, hpc, hR]
  have hC' := tau_cfg4 hpend hact h
  have hS' : C'.mem .s = Function.update S p R := by rw [hC']; simp [hSdef]
  have hts : C'.mem .ts = C.mem .ts := by rw [hC']; rfl
  have hlocp : C'.loc p = ⟨R, .ack⟩ := by rw [hC']; simp
  have hloc : ∀ k, k ≠ p → C'.loc k = C.loc k := fun k hk => by
    rw [hC']; exact Function.update_of_ne hk _ _
  have hpd : ∀ k, C'.pend k = C.pend k := fun k => by rw [hC']
  -- the new content of `s`
  have hrow : ∀ j', j' ≠ j → ∀ k, Function.update S p R k j' = S k j' := by
    intro j' hj' k
    by_cases hk : k = p
    · subst hk; simp [h2 j' hj']
    · simp [Function.update_of_ne hk]
  have hM' : maxTs (Function.update S p R) j = max M t := maxTs_update h6.le
  have hMj' : ∀ j', j' ≠ j → maxTs (Function.update S p R) j' = maxTs S j' :=
    fun j' hj' => maxTs_congr (hrow j' hj')
  have hgood : Good w₀ (Function.update S p R) := by
    intro k j'
    by_cases hk : k = p
    · subst hk
      by_cases hj : j' = j
      · subst hj; simp only [Function.update_self]
        exact ⟨fun h0 => absurd h0 (by omega), fun _ => h3⟩
      · simp only [Function.update_self]; rw [← h2 j' hj]; exact hI.good k j'
    · simp only [Function.update_of_ne hk]; exact hI.good k j'
  have htslt : ∀ k j', (Function.update S p R k j').2 < n * (C.mem .ts + 1) := by
    intro k j'
    by_cases hk : k = p
    · subst hk
      by_cases hj : j' = j
      · subst hj; simpa using h5
      · simp only [Function.update_self]; rw [← h2 j' hj]; exact hI.ts_lt k j'
    · simp only [Function.update_of_ne hk]; exact hI.ts_lt k j'
  have hcomb' : ∀ j', j' ≠ j → combine (Function.update S p R) j' = combine S j' :=
    fun j' hj' => combine_congr (hrow j' hj')
  -- facts on the other processes
  have hdet : ∀ k thr, k ≠ p → detTs k (C.loc k) = some (j, thr) → thr ≠ t := by
    intro k thr hk hd he
    have := ((hI.proc k).of_detTs hd).2.2.1
    rw [he] at this
    exact hk (Fin.ext (by rw [← this, h3]))
  by_cases hMt : M < t
  · -- linearize the covered pending updates of component `j`, then `p`'s own
    set others := (List.finRange n).filter (fun k => decide (k ≠ p ∧
      ∃ thr, detTs k (C.loc k) = some (j, thr) ∧ M < thr ∧ thr < t)) with hothers
    have hmemo : ∀ k, k ∈ others ↔ k ≠ p ∧
        ∃ thr, detTs k (C.loc k) = some (j, thr) ∧ M < thr ∧ thr < t := fun k => by
      simp [hothers]
    set Ms : Lin4 c W w₀ n :=
      others.map (fun k => (curOp α k, (C.pend k).getD .scan)) ++ [(curOp α p, .update j v)]
      with hMs
    have hcur_inj : ∀ a b, curOp α a = curOp α b → a = b := fun a b h => congrArg Prod.fst h
    have hfst : Ms.map Prod.fst = others.map (curOp α) ++ [curOp α p] := by simp [hMs]
    have hmemMs : ∀ k, curOp α k ∈ Ms.map Prod.fst ↔ k ∈ others ∨ k = p := by
      intro k
      rw [hfst, List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h)
        · obtain ⟨k', hk', he⟩ := List.mem_map.1 h; exact Or.inl (hcur_inj _ _ he ▸ hk')
        · exact Or.inr (hcur_inj _ _ h)
      · rintro (h | rfl)
        · exact Or.inl (List.mem_map.2 ⟨k, h, rfl⟩)
        · exact Or.inr rfl
    have hothers_op : ∀ k ∈ others, ∃ v', C.pend k = some (.update j v') ∧
        curOp α k ∉ L.map Prod.fst := by
      intro k hk
      obtain ⟨-, thr, hd, hlt, -⟩ := (hmemo k).1 hk
      obtain ⟨⟨v', hv'⟩, hiff, -, -⟩ := (hI.proc k).of_detTs hd
      rw [← hSdef, ← hMdef] at hiff
      exact ⟨v', hv', fun hx => by have := hiff.1 hx; omega⟩
    have hpnot : curOp α p ∉ L.map Prod.fst := fun hx => by have := h7.1 hx; omega
    have hL' : IsLinearization (α ++ [.tau p]) (L ++ Ms) := by
      refine (hI.lin.append_tau p).push_list Ms ?_ ?_ ?_
      · intro y hy
        rw [hMs, List.mem_append] at hy
        rcases hy with hy | hy
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
          obtain ⟨v', hv', -⟩ := hothers_op k hk
          obtain ⟨hinv, -, hop⟩ := Impl.run_pend_curOp hα hv'
          refine ⟨by rw [opOf_append_of_invoked hinv, hop, hv']; rfl, ?_⟩
          have := not_completed_curOp (α ++ [.tau p]) k
          rwa [curOp_append_tau] at this
        · rw [List.mem_singleton] at hy; subst hy
          obtain ⟨hinv, -, hop⟩ := Impl.run_pend_curOp hα h1
          refine ⟨by rw [opOf_append_of_invoked hinv, hop], ?_⟩
          have := not_completed_curOp (α ++ [.tau p]) p
          rwa [curOp_append_tau] at this
      · rw [hfst, List.nodup_append]
        refine ⟨((List.nodup_finRange n).filter _).map (fun a b h => hcur_inj a b h),
          List.nodup_singleton _, ?_⟩
        intro a ha b hb he
        rw [List.mem_singleton] at hb; subst hb
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
        exact ((hmemo k).1 hk).1 (hcur_inj _ _ he)
      · intro y hy
        rw [hMs, List.mem_append] at hy
        rcases hy with hy | hy
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
          obtain ⟨-, -, hn⟩ := hothers_op k hk
          exact hn
        · rw [List.mem_singleton] at hy; subst hy; exact hpnot
    have hstate : linState (A := mwSnap c W w₀) (L ++ Ms) = combine (Function.update S p R) := by
      rw [linState_append, hI.state, hMs, List.map_append, List.map_cons, List.map_nil]
      rw [runOps_updates_last j]
      · funext j'
        by_cases hj : j' = j
        · rw [hj]
          rw [Function.update_self]
          have ha : (Function.update S p R p j).2 = maxTs (Function.update S p R) j := by
            simp only [Function.update_self]; rw [hM']; exact (max_eq_right hMt.le).symm
          have hb : maxTs (Function.update S p R) j ≠ 0 := by rw [hM']; omega
          rw [combine_eq hgood ha hb]; simp [hv]
        · rw [Function.update_of_ne hj, hcomb' j' hj]
      · intro o ho
        obtain ⟨⟨y, o'⟩, hy, rfl⟩ := List.mem_map.1 ho
        obtain ⟨k, hk, he⟩ := List.mem_map.1 hy
        simp only [Prod.mk.injEq] at he; obtain ⟨-, rfl⟩ := he
        obtain ⟨v', hv', -⟩ := hothers_op k hk
        exact ⟨v', by rw [hv']; rfl⟩
    refine ⟨L ++ Ms, hL', by rw [hS', hts]; exact htslt, by rw [hS']; exact hgood,
      by rw [hS']; exact hstate, fun k => ?_⟩
    rw [hS', hts, curOp_append_tau, hpd]
    by_cases hk : k = p
    · subst hk
      rw [hlocp]
      unfold PInv4; dsimp only
      refine ⟨⟨j, v, h1⟩, by simp, ?_⟩
      rw [List.map_append, List.mem_append]; exact Or.inr ((hmemMs k).2 (Or.inr rfl))
    · rw [hloc k hk]
      have hmemk : curOp α k ∈ (L ++ Ms).map Prod.fst ↔
          curOp α k ∈ L.map Prod.fst ∨ k ∈ others := by
        rw [List.map_append, List.mem_append, hmemMs k]
        simp [hk]
      refine (hI.proc k).frame (by simp [Function.update_of_ne hk, hSdef]) le_rfl ?_ ?_
        (fun y hy => ObjSpec.respIn_append_of_mem hy _)
      · intro j₁ thr hd hiff
        rw [hmemk, hiff]
        by_cases hj : j₁ = j
        · subst hj
          have hne := hdet k thr hk hd
          rw [hM', hmemo k]
          constructor
          · rintro (h | ⟨-, thr', hd', h1', h2'⟩)
            · exact le_max_of_le_left h
            · rw [hd] at hd'; cases hd'; exact le_max_of_le_right h2'.le
          · intro hle
            rcases le_or_gt thr M with h | h
            · exact Or.inl h
            · refine Or.inr ⟨hk, thr, hd, h, ?_⟩
              rcases le_max_iff.1 hle with h' | h'
              · omega
              · omega
        · rw [hMj' j₁ hj, hmemo k]
          constructor
          · rintro (h | ⟨-, thr', hd', -⟩)
            · exact h
            · rw [hd] at hd'; cases hd'; exact absurd rfl hj
          · exact Or.inl
      · intro hd
        rw [hmemk, hmemo k]
        constructor
        · rintro (h | ⟨-, thr', hd', -⟩)
          · exact h
          · rw [hd] at hd'; cases hd'
        · exact Or.inl
  · -- `p`'s operation is already linearized; nothing changes in the abstract state
    have hle : t ≤ M := not_lt.1 hMt
    have hpin : curOp α p ∈ L.map Prod.fst := h7.2 hle
    obtain ⟨k₀, hk₀⟩ := exists_maxTs S j
    have hMpos : M ≠ 0 := by omega
    have hk₀p : k₀ ≠ p := by
      rintro rfl; rw [hMdef, ← hk₀] at hle; omega
    have hcomb : combine (Function.update S p R) = combine S := by
      funext j'
      by_cases hj : j' = j
      · subst hj
        rw [combine_eq hgood (k := k₀) (by
            simp only [Function.update_of_ne hk₀p]; rw [hM', hk₀, max_eq_left hle])
          (by rw [hM', max_eq_left hle]; exact hMpos),
          combine_eq hI.good hk₀ hMpos, Function.update_of_ne hk₀p]
      · exact hcomb' j' hj
    refine ⟨L, hI.lin.append_tau p, by rw [hS', hts]; exact htslt, by rw [hS']; exact hgood,
      by rw [hS', hcomb]; exact hI.state, fun k => ?_⟩
    rw [hS', hts, curOp_append_tau, hpd]
    by_cases hk : k = p
    · subst hk
      rw [hlocp]
      unfold PInv4; dsimp only
      exact ⟨⟨j, v, h1⟩, by simp, hpin⟩
    · rw [hloc k hk]
      refine (hI.proc k).frame (by simp [Function.update_of_ne hk, hSdef]) le_rfl ?_
        (fun _ => Iff.rfl) (fun _ _ => rfl)
      intro j₁ thr hd hiff
      rw [hiff]
      by_cases hj : j₁ = j
      · subst hj; rw [hM', max_eq_left hle]
      · rw [hMj' j₁ hj]

end Podc.LimitedUseSnapshots.Snapshot.MW
