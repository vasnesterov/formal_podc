import Papers.PODC2012.LimitedUseSnapshots.SnapshotMWInv

/-!
# Algorithm 4: preservation of the invariant, Theorem 5.1 (linearizability)
-/

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable {n c : ℕ} {W : Type} {w₀ : Fin c → W} [NeZero n]
  {α : List (Label (Fin n) (mwSnap c W w₀))} {C C' : Cfg4 n c W w₀} {L : Lin4 c W w₀ n}

lemma inv4_init : Inv4 ([] : List (Label (Fin n) (mwSnap c W w₀))) (alg4 n w₀).initCfg [] := by
  refine ⟨isLinearization_nil, fun k j => ?_, fun k j => ⟨fun _ => rfl, fun h => absurd rfl h⟩,
    ?_, fun k => ⟨rfl, rfl⟩⟩
  · show 0 < n * (0 + 1); simpa using NeZero.pos n
  · funext j
    rw [combine_eq_zero (w₀ := w₀) (fun k j => ⟨fun _ => rfl, fun h => absurd rfl h⟩)]
    · rfl
    · exact Nat.eq_zero_of_le_zero (Finset.sup_le fun _ _ => le_rfl)

lemma tau_cfg4 {p : Fin n} (hpend : C.pend p ≠ none) {i : Obj4}
    {o : (obj4 n c W w₀ i).Op} {k : (obj4 n c W w₀ i).Resp → Loc4 c W}
    (hact : act4 p (C.loc p) = .access i o k)
    (h : (alg4 n w₀).step C (.tau p) = some C') :
    C' = { C with mem := Function.update C.mem i ((obj4 n c W w₀ i).δ (C.mem i) o).1,
                  loc := Function.update C.loc p (k ((obj4 n c W w₀ i).δ (C.mem i) o).2) } := by
  rw [Impl.step_tau_eq_some (I := alg4 n w₀) hpend hact] at h
  exact (Option.some.inj h).symm

/-! ### Invocations and responses -/

lemma inv4_step_inv (hα : (alg4 n w₀).run α = some C) (hI : Inv4 α C L) {p : Fin n}
    {o : MOp c W} (h : (alg4 n w₀).step C (.inv p o) = some C') :
    Inv4 (α ++ [.inv p o]) C' L := by
  obtain ⟨hpend, -, hpend', hloc', hmem'⟩ := Impl.step_inv h
  refine ⟨hI.lin.append_inv p o, by rw [hmem']; exact hI.ts_lt, by rw [hmem']; exact hI.good,
    by rw [hmem']; exact hI.state, fun k => ?_⟩
  rw [hmem', curOp_append_inv]
  by_cases hk : k = p
  · subst hk
    have hidle := (hpend ▸ hI.proc k).pc_idle
    have hP := hI.proc k
    rw [hpend] at hP
    unfold PInv4 at hP; rw [hidle] at hP
    have hnot : curOp α k ∉ L.map Prod.fst := fun hx =>
      Impl.not_invoked_curOp_of_idle hα hpend (hI.lin.mem_invoked hx)
    rw [hloc', hpend', Function.update_self, Function.update_self]
    cases o with
    | update j v => exact ⟨rfl, hP.2, hnot⟩
    | scan => exact ⟨rfl, hP.2, hnot⟩
  · rw [hloc', hpend', Function.update_of_ne hk, Function.update_of_ne hk]; exact hI.proc k

lemma inv4_step_ret (hα : (alg4 n w₀).run α = some C) (hI : Inv4 α C L) {p : Fin n}
    {r : Option (Fin c → W)} (h : (alg4 n w₀).step C (.ret p r) = some C') :
    Inv4 (α ++ [.ret p r]) C' L := by
  obtain ⟨hpend, hpend', hmem', l, hact, hloc'⟩ := Impl.step_ret h
  have hP := hI.proc p
  have hact' : act4 (w₀ := w₀) p (C.loc p) = .ret r l := hact
  have key : l = ⟨(C.loc p).rcd, .idle⟩ ∧
      (mwSnap c W w₀).respIn (mwSnap c W w₀).init L (curOp α p) = some r ∧
      C.mem .s p = (C.loc p).rcd := by
    cases hpc : (C.loc p).pc with
    | idle => simp only [PInv4, hpc] at hP; exact absurd hP.1 hpend
    | ack =>
      simp only [PInv4, hpc] at hP
      simp only [act4, hpc, Action.ret.injEq] at hact'
      obtain ⟨rfl, rfl⟩ := hact'
      obtain ⟨⟨j, v, h1⟩, h2, h3⟩ := hP
      obtain ⟨-, -, hop⟩ := Impl.run_pend_curOp hα h1
      exact ⟨rfl, respIn_update hI.lin h3 hop, h2⟩
    | retS val =>
      simp only [PInv4, hpc] at hP
      simp only [act4, hpc, Action.ret.injEq] at hact'
      obtain ⟨rfl, rfl⟩ := hact'
      exact ⟨rfl, hP.2.2, hP.2.1⟩
    | _ => simp [act4, hpc] at hact'
  obtain ⟨rfl, hr, hs⟩ := key
  refine ⟨hI.lin.append_ret_of_respIn hr, by rw [hmem']; exact hI.ts_lt,
    by rw [hmem']; exact hI.good, by rw [hmem']; exact hI.state, fun k => ?_⟩
  rw [hmem']
  by_cases hk : k = p
  · subst hk
    rw [hloc', hpend', Function.update_self, Function.update_self]
    exact ⟨rfl, hs⟩
  · rw [hloc', hpend', Function.update_of_ne hk, Function.update_of_ne hk,
      curOp_append_ret_of_ne α r (Ne.symm hk)]
    exact hI.proc k

/-! ### `ReadMax(timestamp)` and `WriteMax(timestamp)` (Lines 13–14) -/

lemma inv4_step_rd (hI : Inv4 α C L) {p : Fin n} {j : Fin c} {v : W}
    (hpc : (C.loc p).pc = .rd j v) (h : (alg4 n w₀).step C (.tau p) = some C') :
    Inv4 (α ++ [.tau p]) C' L := by
  have hP := hI.proc p
  simp only [PInv4, hpc] at hP
  obtain ⟨h1, h2, hnot⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act4 (w₀ := w₀) p (C.loc p) = .access .ts MaxOp.readMax
      (fun r => ⟨(C.loc p).rcd, .wr j v r⟩) := by simp [act4, hpc]
  have hC' := tau_cfg4 hpend hact h
  have hmem : C'.mem = C.mem := by
    rw [hC']; exact Function.update_eq_self _ _
  refine ⟨hI.lin.append_tau p, by rw [hmem]; exact hI.ts_lt, by rw [hmem]; exact hI.good,
    by rw [hmem]; exact hI.state, fun k => ?_⟩
  rw [hmem, curOp_append_tau]
  by_cases hk : k = p
  · subst hk
    have hloc : C'.loc k = ⟨(C.loc k).rcd, .wr j v (C.mem .ts)⟩ := by rw [hC']; simp
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]
    unfold PInv4; dsimp only
    have hlt : ∀ j', ((C.loc k).rcd j').2 < n * (C.mem .ts + 1) + k := fun j' => by
      rw [← h2]; exact lt_of_lt_of_le (hI.ts_lt k j') (Nat.le_add_right _ _)
    refine ⟨h1, h2, le_rfl, hlt, ?_⟩
    have hm : maxTs (C.mem .s) j < n * (C.mem .ts + 1) :=
      maxTs_lt (Nat.mul_pos (NeZero.pos n) (Nat.succ_pos _)) fun k' => hI.ts_lt k' j
    constructor
    · intro hx; exact absurd hx hnot
    · intro hle; omega
  · have hloc : C'.loc k = C.loc k := by rw [hC']; exact Function.update_of_ne hk _ _
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]; exact hI.proc k

lemma inv4_step_wr (hI : Inv4 α C L) {p : Fin n} {j : Fin c} {v : W} {r : ℕ}
    (hpc : (C.loc p).pc = .wr j v r) (h : (alg4 n w₀).step C (.tau p) = some C') :
    Inv4 (α ++ [.tau p]) C' L := by
  have hP := hI.proc p
  simp only [PInv4, hpc] at hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act4 (w₀ := w₀) p (C.loc p) = .access .ts (MaxOp.writeMax (r + 1))
      (fun _ => ⟨Function.update (C.loc p).rcd j (v, n * (r + 1) + p), .up j⟩) := by
    simp [act4, hpc]
  have hC' := tau_cfg4 hpend hact h
  have hS : C'.mem .s = C.mem .s := by rw [hC']; rfl
  have hts : C'.mem .ts = max (C.mem .ts) (r + 1) := by rw [hC']; simp
  have hmr : C.mem .ts ≤ C'.mem .ts := by rw [hts]; exact le_max_left _ _
  refine ⟨hI.lin.append_tau p, fun k j' => ?_, by rw [hS]; exact hI.good,
    by rw [hS]; exact hI.state, fun k => ?_⟩
  · rw [hS]; exact lt_of_lt_of_le (hI.ts_lt k j') (Nat.mul_le_mul_left n (Nat.succ_le_succ hmr))
  rw [hS, curOp_append_tau]
  by_cases hk : k = p
  · subst hk
    have hloc : C'.loc k = ⟨Function.update (C.loc k).rcd j (v, n * (r + 1) + k), .up j⟩ := by
      rw [hC']; simp
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]
    unfold PInv4; dsimp only
    simp only [Function.update_self]
    refine ⟨h1, fun j' hj' => by rw [Function.update_of_ne hj', h2], ?_,
      Nat.add_pos_left (Nat.mul_pos (NeZero.pos n) (Nat.succ_pos r)) _, ?_,
      by rw [h2]; exact h4 j, h5⟩
    · rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt k.isLt
    · rw [hts]
      have : n * (r + 1) + k < n * (r + 1 + 1) := by
        rw [Nat.mul_add n (r + 1) 1, Nat.mul_one]; exact Nat.add_lt_add_left k.isLt _
      exact lt_of_lt_of_le this (Nat.mul_le_mul_left n (Nat.succ_le_succ (le_max_right _ _)))
  · have hloc : C'.loc k = C.loc k := by rw [hC']; exact Function.update_of_ne hk _ _
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]
    exact (hI.proc k).frame rfl hmr (fun _ _ _ h => h) (fun _ => Iff.rfl) (fun _ _ => rfl)

end Podc.LimitedUseSnapshots.Snapshot.MW

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable {n c : ℕ} {W : Type} {w₀ : Fin c → W} [NeZero n]
  {α : List (Label (Fin n) (mwSnap c W w₀))} {C C' : Cfg4 n c W w₀} {L : Lin4 c W w₀ n}

/-! ### `MW-Scan`: `Scan(s)` (Line 5), its linearization point -/

lemma inv4_step_sc (hα : (alg4 n w₀).run α = some C) (hI : Inv4 α C L) {p : Fin n}
    (hpc : (C.loc p).pc = .sc) (h : (alg4 n w₀).step C (.tau p) = some C') :
    Inv4 (α ++ [.tau p]) C' (L ++ [(curOp α p, .scan)]) := by
  have hP := hI.proc p
  simp only [PInv4, hpc] at hP
  obtain ⟨h1, h2, hnot⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act4 (w₀ := w₀) p (C.loc p) = .access .s SOp.scan
      (fun view => ⟨(C.loc p).rcd, .retS (combine (view.getD fun _ => rec₀ c W w₀))⟩) := by
    simp [act4, hpc]
  have hC' := tau_cfg4 hpend hact h
  have hmem : C'.mem = C.mem := by rw [hC']; exact Function.update_eq_self _ _
  obtain ⟨hinv, -, hop⟩ := Impl.run_pend_curOp hα h1
  have hL' : IsLinearization (α ++ [.tau p]) (L ++ [(curOp α p, .scan)]) := by
    refine (hI.lin.append_tau p).push ?_ hnot ?_
    · rw [opOf_append_of_invoked hinv]; exact hop
    · have := not_completed_curOp (α ++ [.tau p]) p
      rwa [curOp_append_tau] at this
  have hstate : linState (A := mwSnap c W w₀) (L ++ [(curOp α p, .scan)]) =
      linState (A := mwSnap c W w₀) L := by rw [linState_concat]
  refine ⟨hL', by rw [hmem]; exact hI.ts_lt, by rw [hmem]; exact hI.good,
    by rw [hmem, hstate]; exact hI.state, fun k => ?_⟩
  rw [hmem, curOp_append_tau]
  by_cases hk : k = p
  · subst hk
    have hloc : C'.loc k = ⟨(C.loc k).rcd, .retS (combine (C.mem .s))⟩ := by rw [hC']; simp
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]
    unfold PInv4; dsimp only
    refine ⟨h1, h2, ?_⟩
    rw [ObjSpec.respIn_concat_self hnot, ← hI.state]; rfl
  · have hloc : C'.loc k = C.loc k := by rw [hC']; exact Function.update_of_ne hk _ _
    have hpd : C'.pend k = C.pend k := by rw [hC']
    rw [hloc, hpd]
    have hmemk : curOp α k ∈ (L ++ [(curOp α p, MOp.scan)]).map Prod.fst ↔
        curOp α k ∈ L.map Prod.fst := by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro (h | h); exact h; exact absurd (congrArg Prod.fst h) hk
      · exact Or.inl
    exact (hI.proc k).frame rfl le_rfl (fun _ _ _ h => hmemk.trans h) (fun _ => hmemk)
      (fun y hy => ObjSpec.respIn_append_of_mem hy _)

end Podc.LimitedUseSnapshots.Snapshot.MW
