import Papers.PODC2024.HistoryIndependent.Alg4Lin
import Papers.PODC2024.HistoryIndependent.Alg4WaitFree

/-!
# Algorithm 4: Lemmas 10, 11 and Theorem 12

Theorem 12 of Attiya, Bender, Farach-Colton, Oshman, Schiller, *History-Independent Concurrent
Objects* (PODC 2024): Algorithm 4 is a linearizable, wait-free, quiescent history-independent
SWSR `K`-valued register implemented from binary registers.

* `lemma10`: a `Read` reaching Line 7 has `val ≠ ⊥`;
* `lemma11`: a `1` in `B` seen while a `Read` is pending was written by a `Write` that overlaps
  the `Read` (it was invoked, and it did not return before the `Read` was invoked);
* `mem_quiescent` (Lemmas 35/36 and the memory part of the HI proof): in a quiescent configuration
  the memory is the canonical representation of the last written value;
* `theorem12`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K] {v₀ : Fin K}

/-- **Lemma 34** (the part used by Lemma 10). If a `TryRead` fails, i.e. its upward scan reads
`A[K-1] = 0` (and all previous cells as `0`), then some `Write` executed Line 16 after the
`TryRead` started: the number `nA` of writes that executed Line 16 exceeds its value `sT` at the
start of the `TryRead`. (The paper also shows that this `Write` reaches Line 18 before the
`TryRead` returns; that part is not needed.) -/
theorem lemma34 {α : List (Lbl v₀)} (hα : (alg4 v₀).Valid α) {b : Bool} {j : Fin K}
    (hs : (sOf v₀ α).rpc = .up b j) (hA : (sOf v₀ α).A j = false) (hK : j.val + 1 = K) :
    (sOf v₀ α).sT < (sOf v₀ α).nA := by
  have hI := inv_sOf hα
  have h1 := hI.nA_ne_sT hs hA (by omega)
  have h2 : (sOf v₀ α).sT ≤ (sOf v₀ α).nA := by
    cases b
    · exact (hI.h4 j hs).2
    · exact (hI.h4' j hs).2
  omega

/-- **Lemma 10.** If a `Read` reaches Line 7, then `val ≠ ⊥`. -/
theorem lemma10 {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg4 v₀).run α = some C)
    {val : Option (Fin K)} (hl : (C.loc .r).rpc = .setF2 val) : val ≠ none := by
  have hR := rel_run v₀ h
  have hI := inv_sOf ⟨C, h⟩
  rw [hR.rpc] at hl
  have := hI.l10 (by simp [hl, RPC.late])
  simp only [hl, RPC.val?] at this
  intro hv; simp [hv] at this

/-- **Lemma 11.** While a `Read` (the `k`-th, `k = |opsOf α r| - 1`) is pending, every `1` in
`B[x]` was written (in Line 13) by a `Write` `(w, t - 1)`, `t = tagB x` (the ghost "last writer"
of `B[x]`), that overlaps the `Read`: it has been invoked, and it did not return before the
`Read` was invoked. In particular this holds for the `1` read by the `Read` in Line 6. -/
theorem lemma11 {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg4 v₀).run α = some C)
    (hr : C.pend .r ≠ none) {x : Fin K} (hx : C.mem (.b x) = true) :
    1 ≤ (sOf v₀ α).tagB x ∧ Invoked α (.w, (sOf v₀ α).tagB x - 1) ∧
      ¬ Precedes α (.w, (sOf v₀ α).tagB x - 1) (.r, (opsOf α .r).length - 1) := by
  have hv : (alg4 v₀).Valid α := ⟨C, h⟩
  have hR := rel_run v₀ h
  have hI := inv_sOf hv
  have hL := link hv
  have hr' : (sOf v₀ α).rpc ≠ .idle := fun h' => hr (hR.pendR.2 h')
  have hnR : (opsOf α .r).length = (sOf v₀ α).pis.length + 1 := by
    simp [hL.opsR, St.nR, hr']
  rw [hnR, Nat.add_sub_cancel]
  rw [hR.memB] at hx
  obtain ⟨b1, b2, -⟩ := hI.bval x hx
  have hlo := hI.b11 hr' x hx
  refine ⟨b1, ?_, ?_⟩
  · simp only [Invoked, hL.opsW, List.length_map]; simp only [St.n] at b2; omega
  · rintro ⟨β, γ, rfl, hc, hni⟩
    have hβ : (alg4 v₀).Valid β := (alg4 v₀).valid_of_prefix hv (List.prefix_append _ _)
    have hLβ := link hβ
    simp only [Completed, hLβ.respsW, List.length_take] at hc
    simp only [Invoked, hLβ.opsR, List.length_replicate, not_lt] at hni
    have h2 := (rel_ge hv).2 hr' hni
    omega

/-- The canonical memory representation of the value `v`: `A[v] = 1`, all other cells `0`
(the initial memory is `canon v₀`). -/
def canonMem (v : Fin K) : (i : Cell K) → (Obj K i).State := memInit v

/-- **Memory at quiescent configurations** (Lemmas 35, 36 and the proof of history
independence): flags are `0`, `B` is `0`, and `A` is the indicator of the last written value. -/
theorem mem_quiescent {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg4 v₀).run α = some C)
    (hq : C.Quiescent) : C.mem = canonMem ((sOf v₀ α).vals v₀ (sOf v₀ α).n) := by
  have hR := rel_run v₀ h
  have hI := inv_sOf ⟨C, h⟩
  have hw : (sOf v₀ α).wpc = .idle := hR.pendW.1 (hq .w)
  have hr : (sOf v₀ α).rpc = .idle := hR.pendR.1 (hq .r)
  funext i
  cases i with
  | a j =>
    rw [hR.memA]
    have h1 := hI.memA j
    have h2 := hI.lastv
    simp only [hw, WPC.newv, WPC.old, reduceCtorEq, false_or] at h1
    simp only [St.c, hw, ite_true] at h2
    simp only [canonMem, memInit]
    rw [← h2]
    cases hA : (sOf v₀ α).A j <;> simp_all
  | b j =>
    rw [hR.memB]
    simp only [canonMem, memInit]
    by_contra hB
    rcases hI.bprot j (by simpa using hB) with h' | ⟨-, -, h' | ⟨h', -⟩⟩
    · simp [hr, RPC.cov] at h'
    · simp [hw, WPC.win] at h'
    · simp [hw, WPC.win'] at h'
  | f1 => rw [hR.memF1, hI.f1, hr]; rfl
  | f2 => rw [hR.memF2, hI.f2, hr]; rfl

/-- In a quiescent execution, every linearization ends in the value of the last write. -/
theorem linState_quiescent {α : List (Lbl v₀)} {C : Cfg v₀} (h : (alg4 v₀).run α = some C)
    (hq : C.Quiescent) {L : List (OpId Proc × RWOp (Fin K))} (hL : IsLinearization α L) :
    linState (A := Reg v₀) L = (sOf v₀ α).vals v₀ (sOf v₀ α).n := by
  have hv : (alg4 v₀).Valid α := ⟨C, h⟩
  have hR := rel_run v₀ h
  have hk := link hv
  have hw : (sOf v₀ α).wpc = .idle := hR.pendW.1 (hq .w)
  rw [hL.linState_of_changer hv.wellFormed .w]
  · rw [hk.opsW]
    have := writeVal_map_write (v₀ := v₀) (sOf v₀ α).wv (le_refl _)
    simp only [writeVal] at this
    rw [List.take_of_length_le (by simp)] at this
    exact this
  · intro p hp o ho
    cases p with
    | w => exact absurd rfl hp
    | r =>
      rw [hk.opsR] at ho
      rw [List.eq_of_mem_replicate ho]
      intro q; rfl
  · rw [hk.respsW, hk.opsW]; simp [St.c, hw, St.n]

/-- **Quiescent history independence** (strong form): for *every* linearization function, two
quiescent executions whose linearizations end in the same state have the same memory. -/
theorem quiescentHI_any (h : List (Lbl v₀) → List (OpId Proc × RWOp (Fin K)))
    (hh : (alg4 v₀).IsLinFun h) :
    ∀ α α' C C', (alg4 v₀).run α = some C → (alg4 v₀).run α' = some C' →
      C.Quiescent → C'.Quiescent → linState (A := Reg v₀) (h α) = linState (h α') →
        C.mem = C'.mem := by
  intro α α' C C' h1 h2 hq1 hq2 hl
  rw [mem_quiescent h1 hq1, mem_quiescent h2 hq2,
    ← linState_quiescent h1 hq1 (hh α ⟨C, h1⟩), ← linState_quiescent h2 hq2 (hh α' ⟨C', h2⟩), hl]

/-- Algorithm 4 is quiescent history independent. -/
theorem quiescentHI : (alg4 v₀).QuiescentHI :=
  ⟨linFun, isLinFun, quiescentHI_any linFun isLinFun⟩

/-- **Theorem 12.** Algorithm 4 is a linearizable, wait-free, quiescent history-independent
SWSR `K`-valued register (from binary registers). -/
theorem theorem12 : (alg4 v₀).Linearizable ∧ (alg4 v₀).WaitFree ∧ (alg4 v₀).QuiescentHI :=
  ⟨linearizable, waitFree v₀, quiescentHI⟩

/-- **Non-vacuity.** There is a quiescent execution in which `Write(v)` completes and then a
`Read` completes and returns `v`. -/
theorem nonvacuous (v : Fin K) : ∃ α C, (alg4 v₀).run α = some C ∧ C.Quiescent ∧
    opsOf α .w = [.write v] ∧ opsOf α .r = [.read] ∧ respsOf α .r = [v] ∧
    Precedes α (.w, 0) (.r, 0) := by
  have hof := (waitFree v₀).obstructionFree
  obtain ⟨C1, h1, hp1, hproc1, hops1, hresp1⟩ := (alg4 v₀).soloOps_spec hof .w [.write v]
    (by intro o ho; simp at ho; subst ho; exact Or.inl ⟨rfl, v, rfl⟩)
    (α := []) (C := (alg4 v₀).initCfg) rfl rfl
  set α1 := (alg4 v₀).soloOps .w (alg4 v₀).initCfg [.write v]
  have hrun1 : (alg4 v₀).run α1 = some C1 := h1
  have hr1 : C1.pend .r = none := by
    rw [((alg4 v₀).runFrom_other h1 (fun ℓ hℓ => by rw [hproc1 ℓ hℓ]; decide)).2]; rfl
  obtain ⟨C2, h2, hp2, hproc2, hops2, hresp2⟩ := (alg4 v₀).soloOps_spec hof .r [.read]
    (by intro o ho; simp at ho; subst ho; exact Or.inr ⟨rfl, rfl⟩) hrun1 hr1
  set α2 := (alg4 v₀).soloOps .r C1 [.read]
  have hrun : (alg4 v₀).run (α1 ++ α2) = some C2 := by
    rw [(alg4 v₀).run_append_of_eq hrun1]; exact h2
  have hw2 : C2.pend .w = none := by
    rw [((alg4 v₀).runFrom_other h2 (fun ℓ hℓ => by rw [hproc2 ℓ hℓ]; decide)).2]; exact hp1
  have ow1 : opsOf α2 .w = [] := opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hproc2 ℓ hℓ]; decide)
  have or1 : opsOf α1 .r = [] := opsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hproc1 ℓ hℓ]; decide)
  have rr1 : respsOf α1 .r = [] :=
    respsOf_eq_nil_of_proc_ne (fun ℓ hℓ => by rw [hproc1 ℓ hℓ]; decide)
  have hops : opsOf (α1 ++ α2) .w = [.write v] := by rw [opsOf_append, hops1, ow1]; rfl
  have hprec : Precedes (α1 ++ α2) (.w, 0) (.r, 0) :=
    ⟨α1, α2, rfl, by simp [Completed, hresp1], by simp [Invoked, or1]⟩
  have hRF := readsFrom (v₀ := v₀) ⟨C2, hrun⟩
  have hlen : (respsOf (α1 ++ α2) .r).length = 1 := by
    rw [respsOf_append, rr1, List.nil_append, hresp2]; rfl
  -- the read reads from the write
  have hrf1 : rfOf (α1 ++ α2) 0 = 1 := by
    have h0 : rfOf (α1 ++ α2) 0 ≠ 0 := fun h0 =>
      hRF.not_overwritten 0 (by omega) (by rw [h0]; exact hprec)
    have h2' : ¬ 2 ≤ rfOf (α1 ++ α2) 0 := fun h2' => by
      apply hRF.not_future 0 (by omega) (by omega)
      refine ⟨α1 ++ α2, [], by simp, by simp only [Completed]; omega, ?_⟩
      simp only [Invoked, hops, List.length_singleton, not_lt]; omega
    omega
  have hval := hRF.read_val 0 (by omega)
  rw [hrf1, hops, writeVal_succ (v := v) rfl] at hval
  refine ⟨α1 ++ α2, C2, hrun, fun p => by cases p <;> assumption, hops, ?_, ?_, hprec⟩
  · rw [opsOf_append, or1, hops2]; rfl
  · rw [respsOf_append, rr1, List.nil_append]
    obtain ⟨x, hx⟩ : ∃ x, respsOf α2 .r = [x] :=
      List.length_eq_one_iff.1 (by rw [hresp2]; rfl)
    rw [hx]
    simp only [respOf, respsOf_append, rr1, List.nil_append, hx] at hval
    simpa using hval

end Alg4

end Cslib.SharedMemory
