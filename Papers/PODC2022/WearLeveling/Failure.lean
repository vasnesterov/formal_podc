import Papers.PODC2022.WearLeveling.Endurance

/-!
# The counter fails with `k·T + 2` FAIs

A sequential execution of a single thread: `k·T + 1` FAIs, a system-wide crash, one more FAI.
If worn-out words keep their old value (stuck-at), the `(k·T+1)`-st FAI's write-back of `A[0]`
is lost; after the crash the array is back to the state after `k·T` increments and the last FAI
returns `k·T` a second time — the history is not strictly linearizable. With
`guarantees_kT_succ` this shows that, in the sense of Definition 2.1, the counter has endurance
exactly `k·T + 1` (`hasEndurance_counter`), not `k·T`.
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

variable {k : ℕ} [NeZero k] {P : Type} [DecidableEq P]

/-- One FAI of thread `p`, run solo; `r` = the index of the word it increments. -/
def soloOp (p : P) (r : ℕ) : List (Ev k P Unit) :=
  [.inv p (), .step p, .step p] ++ List.replicate (2 * r) (.step p) ++ [.step p, .step p, .step p]

lemma exec_cons' (W : Wear k ℕ) (C : Cfg (counter k) P) (e : Ev k P Unit) (es : List (Ev k P Unit)) :
    exec W C (e :: es) =
      ((exec W (step1 W C e).1 es).1, (step1 W C e).2 ++ (exec W (step1 W C e).1 es).2) := rfl

lemma writeBack_clean (W : Wear k ℕ) (C : Cfg (counter k) P) {i : Fin k}
    (h : C.dirty i = false) : writeBack W C i = C := by
  simp [writeBack, h]

/-- The loop of failed CASes (lines 5, 9–11) on clean words that do not hold `it`. -/
lemma exec_loop (W : Wear k ℕ) (p : P) (a : ℕ) (it r : ℕ) (hr : r < k) :
    ∀ (d : ℕ) (C : Cfg (counter k) P) (idx : Fin k), idx.val + d = r →
      (∀ i, C.dirty i = false) → (∀ i : Fin k, i.val < r → C.cache i ≠ it) →
      C.ts p = .run a () (CL.cas it idx) →
      exec W C (List.replicate (2 * d) (.step p)) =
        ({ C with ts := Function.update C.ts p (.run a () (CL.cas it ⟨r, hr⟩)) }, []) := by
  intro d
  induction d with
  | zero =>
    intro C idx hidx _ _ hp
    have : idx = ⟨r, hr⟩ := Fin.ext (by simpa using hidx)
    subst this
    simp only [Nat.mul_zero, List.replicate_zero, exec_nil]
    rw [← hp, Function.update_eq_self]
    rfl
  | succ d ih =>
    intro C idx hidx hcl hc hp
    rw [show 2 * (d + 1) = 2 * d + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
      exec_cons', step_cas_fail W hp (hc idx (by omega))]
    dsimp only
    rw [exec_cons', step_flF W (C := { C with ts := _ }) (a := a) (o := ()) (it := it) (idx := idx)
      (by simp)]
    dsimp only
    have hlt : idx.val + 1 < k := by omega
    rw [writeBack_clean W _ (by exact hcl idx), nextPC_of_lt k hlt]
    simp only [Function.update_idem, List.nil_append]
    rw [ih { C with ts := Function.update C.ts p (.run a () (CL.cas it ⟨idx.val + 1, hlt⟩)) }
      ⟨idx.val + 1, hlt⟩ (by simp; omega) hcl hc (by simp)]
    simp [Function.update_idem]

lemma stair_pos_last (it : ℕ) (r : Fin k) : stair k (it * k + r.val) (last k) = it := by
  have hr := r.isLt
  apply le_antisymm
  · rw [stair_le_iff, last_val]; omega
  · rw [le_stair_iff, last_val]; omega

lemma stair_pos_lt (it : ℕ) (r i : Fin k) (hi : i.val < r.val) :
    stair k (it * k + r.val) i = it + 1 := by
  apply le_antisymm
  · rw [stair_le_iff, Nat.succ_mul]; omega
  · rw [le_stair_iff, Nat.succ_mul]; omega

/-- A solo FAI from a quiescent configuration with clean cache holding `stair (it·k + r)`
increments word `r` and returns `it·k + r`. -/
lemma exec_soloOp (W : Wear k ℕ) (C : Cfg (counter k) P) (p : P) (hp : C.ts p = .idle)
    (hcl : ∀ i, C.dirty i = false) (it : ℕ) (r : Fin k)
    (hcache : C.cache = stair k (it * k + r.val)) :
    exec W C (soloOp p r.val) =
      ({ writeBack W { C with cache := Function.update C.cache r (it + 1),
                              dirty := Function.update C.dirty r true } r with
          ts := C.ts, cnt := C.cnt + 1 }, [.inv C.cnt p (), .res C.cnt (r.val + it * k)]) := by
  unfold soloOp
  rw [exec_append, exec_append]
  -- prefix: invocation, line 1, line 2
  have hpre : exec W C [.inv p (), .step p, .step p] =
      ({ C with ts := Function.update C.ts p (.run C.cnt () (CL.cas it 0)), cnt := C.cnt + 1 },
        [.inv C.cnt p ()]) := by
    rw [exec_cons', inv_idle W hp]
    dsimp only
    rw [exec_cons', step_rd W (a := C.cnt) (o := ()) (by simp)]
    dsimp only
    rw [exec_cons', step_fl W (a := C.cnt) (o := ()) (it := C.cache (last k)) (by simp)]
    dsimp only
    rw [writeBack_clean W _ (by exact hcl _)]
    have hl : C.cache (last k) = it := by rw [hcache, stair_pos_last]
    simp only [Function.update_idem, hl]
    rfl
  rw [hpre]
  dsimp only
  set C3 : Cfg (counter k) P :=
    { C with ts := Function.update C.ts p (.run C.cnt () (CL.cas it 0)), cnt := C.cnt + 1 }
    with hC3
  have hloop := exec_loop W p C.cnt it r.val r.isLt r.val C3 0 (by simp) hcl
    (fun i hi => by show C.cache i ≠ it; rw [hcache, stair_pos_lt it r i hi]; omega)
    (by simp [hC3])
  rw [hloop]
  dsimp only
  -- suffix: successful CAS, line 6, line 7
  have hr : (⟨r.val, r.isLt⟩ : Fin k) = r := rfl
  rw [hr, exec_cons', step_cas_succ W (a := C.cnt) (o := ()) (it := it) (idx := r) (by simp)
    (by show C.cache r = it; rw [hcache, stair_pos_self])]
  dsimp only
  rw [exec_cons', step_flS W (a := C.cnt) (o := ()) (it := it) (idx := r) (by simp)]
  dsimp only
  rw [exec_cons', step_ret W (a := C.cnt) (o := ()) (it := it) (idx := r) (by simp [writeBack_ts])]
  have hts : Function.update C3.ts p TS.idle = C.ts := by
    rw [hC3]; dsimp only; rw [Function.update_idem, ← hp, Function.update_eq_self]
  simp only [exec_nil, List.append_nil, List.nil_append, List.cons_append, Function.update_idem, hts]
  refine Prod.ext ?_ rfl
  simp only [hC3, Alg.writeBack]
  split_ifs <;> rfl

/-! ### Sequential executions -/

/-- `j` sequential FAIs of thread `p`. -/
def seqOps (p : P) : ℕ → List (Ev k P Unit)
  | 0 => []
  | j + 1 => seqOps p j ++ soloOp p (j % k)

/-- The history of `j` sequential FAIs of `p` (the `i`-th returns `i`). -/
def seqHist (p : P) : ℕ → List (HEv P Unit ℕ)
  | 0 => []
  | j + 1 => seqHist p j ++ [.inv j p (), .res j j]

/-- Quiescent configuration after `j` FAIs, all of them persistent. -/
structure Canon (j : ℕ) (C : Cfg (counter k) P) : Prop where
  cache : C.cache = stair k j
  pm : C.pm = stair k j
  wear : C.wear = stair k j
  clean : ∀ i, C.dirty i = false
  idle : ∀ q, C.ts q = .idle
  cnt : C.cnt = j

/-- Words that wear out get stuck at their old value. -/
def stuck : Fin k → ℕ → ℕ → ℕ → ℕ := fun _ _ old _ => old

lemma canon_seqOps (T : ℕ) (junk : Fin k → ℕ → ℕ → ℕ → ℕ) (p : P) :
    ∀ j, j ≤ k * T → Canon j (exec ⟨T, junk⟩ (initCfg (counter k) P) (seqOps p j)).1 ∧
      (exec ⟨T, junk⟩ (initCfg (counter k) P) (seqOps p j)).2 = seqHist p j
  | 0, _ => ⟨⟨by funext i; rw [stair_zero]; rfl, by funext i; rw [stair_zero]; rfl,
      by funext i; rw [stair_zero]; rfl, fun _ => rfl, fun _ => rfl, rfl⟩, rfl⟩
  | j + 1, hj => by
    obtain ⟨hC, hH⟩ := canon_seqOps T junk p j (by omega)
    obtain ⟨it, r, hjr⟩ := exists_pos (k := k) j
    have hr : j % k = r.val := by
      rw [hjr]; simp [Nat.mul_add_mod_of_lt r.isLt]
    have hitT : it < T := by
      by_contra hc; push Not at hc
      have := Nat.mul_le_mul_right k hc
      rw [Nat.mul_comm T k] at this; omega
    simp only [seqOps, seqHist]
    rw [exec_append, hr, exec_soloOp _ _ p (hC.idle p) hC.clean it r (by rw [hC.cache, hjr])]
    have hd : (Function.update (exec ⟨T, junk⟩ (initCfg (counter k) P) (seqOps p j)).1.dirty r
        true) r = true := by simp
    have hw : (((exec ⟨T, junk⟩ (initCfg (counter k) P) (seqOps p j)).1.wear r : ℕ) : ℕ∞) <
        (T : ℕ∞) := by
      rw [hC.wear, hjr, stair_pos_self]; exact_mod_cast hitT
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [writeBack_cache]; rw [hC.cache, hjr, stair_succ]
    · simp only [Alg.writeBack, hd, ite_true, hw, ite_true]
      rw [hC.pm, hjr, stair_succ]; simp
    · simp only [Alg.writeBack, hd, ite_true]
      rw [hC.wear, hjr, stair_succ, stair_pos_self]
    · intro i; simp only [writeBack_dirty]
      by_cases hi : i = r
      · subst hi; simp
      · simp [Function.update_of_ne hi, hC.clean i]
    · exact hC.idle
    · simp [writeBack_cnt, hC.cnt]
    · rw [hH, hC.cnt, hjr]; simp [Nat.add_comm, Nat.mul_comm]

/-- In a strict linearization of a FAI history, two distinct operations never return the same
value. -/
lemma strictLin_res_inj {h : List (HEv P Unit ℕ)} {L : List (ℕ × Unit)}
    (hL : IsStrictLin faiObj h L) {a b v : ℕ} (ha : HEv.res a v ∈ h) (hb : HEv.res b v ∈ h) :
    a = b := by
  have hpos : ∀ c, HEv.res c v ∈ h → ∃ n, L[n]? = some (c, ()) ∧ v = n := by
    intro c hc
    obtain ⟨x, hx, hxc⟩ := List.mem_map.1 (hL.mem_of_res c v hc)
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
    have hlt := (List.getElem?_eq_some_iff.1 hn).1
    have hleg := (legal_iff_getElem L).1 hL.legal n x hn v (hxc ▸ hc)
    refine ⟨n, by rw [hn, ← hxc], ?_⟩
    rw [hleg]
    simp [faiObj_runOps, List.length_take]; omega
  obtain ⟨n, hn, rfl⟩ := hpos a ha
  obtain ⟨n', hn', hv⟩ := hpos b hb
  subst hv
  rw [hn] at hn'
  simpa using hn'

/-- The failing execution: `k·T + 1` sequential FAIs, a crash, one more FAI. -/
def failSched (T : ℕ) (p : P) : List (Ev k P Unit) :=
  seqOps p (k * T + 1) ++ [.crash] ++ soloOp p 0

/-- With stuck-at wear-out, the last FAI of `failSched` returns `k·T` again. -/
lemma hist_failSched (T : ℕ) (p : P) :
    HEv.res (k * T) (k * T) ∈ hist (counter k) P ⟨T, stuck⟩ (failSched T p) ∧
    HEv.res (k * T + 1) (k * T) ∈ hist (counter k) P ⟨T, stuck⟩ (failSched T p) ∧
    invCount (hist (counter k) P ⟨T, stuck⟩ (failSched T p)) = k * T + 2 := by
  obtain ⟨hC, hH⟩ := canon_seqOps (k := k) T stuck p (k * T) le_rfl
  set C := (exec ⟨T, stuck⟩ (initCfg (counter k) P) (seqOps p (k * T))).1 with hCdef
  have h0 : (k * T) % k = (0 : Fin k).val := by simp
  have hpos0 : k * T = T * k + (0 : Fin k).val := by simp [Nat.mul_comm]
  -- the `(k·T+1)`-st FAI: the write-back of `A[0]` is stuck
  have h00 : ((0 : Fin k) : ℕ) = 0 := by simp
  have hop := exec_soloOp ⟨T, stuck⟩ C p (hC.idle p) hC.clean T 0 (by rw [hC.cache, hpos0])
  rw [h00] at hop
  have hd : (Function.update C.dirty (0 : Fin k) true) (0 : Fin k) = true := by simp
  have hw : ¬ ((C.wear 0 : ℕ) : ℕ∞) < (T : ℕ∞) := by
    rw [hC.wear, hpos0, stair_pos_self]; simp
  set D := (exec ⟨T, stuck⟩ C (soloOp p 0)).1 with hD
  have hDpm : D.pm = stair k (k * T) := by
    rw [hD, hop]; simp only [Alg.writeBack, hd, ite_true, hw, ite_false, stuck]
    rw [Function.update_eq_self, hC.pm]
  have hDts : ∀ q, D.ts q = .idle := by rw [hD, hop]; exact hC.idle
  have hDcnt : D.cnt = k * T + 1 := by rw [hD, hop]; simp [writeBack_cnt, hC.cnt]
  -- the crash and the last FAI
  set E := (step1 ⟨T, stuck⟩ D .crash).1 with hE
  have hop2 := exec_soloOp ⟨T, stuck⟩ E p (by simp [hE, Alg.step1]) (by simp [hE, Alg.step1]) T 0
    (by simp only [hE, Alg.step1]; rw [hDpm, hpos0])
  rw [h00] at hop2
  have hEcnt : E.cnt = k * T + 1 := by simp [hE, Alg.step1, hDcnt]
  have hhist : hist (counter k) P ⟨T, stuck⟩ (failSched T p) =
      seqHist p (k * T) ++ [.inv (k * T) p (), .res (k * T) (0 + T * k)] ++ [.crash] ++
        [.inv (k * T + 1) p (), .res (k * T + 1) (0 + T * k)] := by
    unfold hist failSched
    simp only [seqOps, Nat.mul_mod_right]
    rw [exec_append, exec_append, exec_append, hH, ← hCdef, ← hD]
    have hcr : exec ⟨T, stuck⟩ D [.crash] = (E, [.crash]) := rfl
    rw [hcr]
    dsimp only
    rw [hop2, hop]
    simp [hC.cnt, hEcnt]
  rw [hhist]
  refine ⟨by simp [Nat.mul_comm], by simp [Nat.mul_comm], ?_⟩
  have hc : ∀ j, invCount (seqHist p j) = j := by
    intro j; induction j with
    | zero => rfl
    | succ j ih => simp [seqHist, ih]
  simp [hc]

/-- With `k·T + 2` FAIs the counter is not safe: if worn-out words are stuck at their old value,
the execution `failSched` (`k·T + 1` sequential FAIs, a crash, one more FAI) has two FAIs that
return `k·T`. -/
theorem not_safeUpTo_kT_add_two (T : ℕ) (p : P) :
    ¬ SafeUpTo (counter k) P ⟨T, stuck⟩ (k * T + 2 : ℕ) := by
  intro hS
  obtain ⟨h1, h2, h3⟩ := hist_failSched (k := k) T p
  obtain ⟨L, hL⟩ := hS (failSched T p) (by rw [h3])
  have := strictLin_res_inj hL h1 h2
  omega

/-- **Theorem 4.3, precise version.** In the sense of Definition 2.1, with words of endurance `T`
(surviving `T` write-backs; afterwards arbitrary/stuck values), the counter of Figure 1 has
endurance exactly `k·T + 1`. -/
theorem hasEndurance_counter [Finite P] [Nonempty P] (T : ℕ) :
    HasEndurance (counter k) P T (k * T + 1) := by
  refine ⟨guarantees_kT_succ T, fun h => ?_⟩
  exact not_safeUpTo_kT_add_two (k := k) T (Classical.arbitrary P) (h stuck).1

/-- The literal claim of Theorem 4.3 ("endurance `k·T`" in the sense of Definition 2.1) fails:
the counter does not lose safety or liveness in any execution with `k·T + 1` FAIs. -/
theorem not_hasEndurance_kT [Finite P] (T : ℕ) : ¬ HasEndurance (counter k) P T (k * T) :=
  fun h => h.2 (guarantees_kT_succ T)

end Podc.WearLeveling
