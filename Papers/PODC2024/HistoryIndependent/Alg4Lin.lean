import Papers.PODC2024.HistoryIndependent.Alg4Main
import Podc.SharedMemory.History

/-!
# Algorithm 4: history of an execution, reads-from assignment, linearizability
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K] {v₀ : Fin K}

/-! ### Frame lemmas -/

lemma stepW_frame (s : St K) : (stepW s).pis = s.pis ∧ (stepW s).lo = s.lo ∧
    (stepW s).rpc = s.rpc ∧ (stepW s).wv = s.wv ∧ (stepW s).rf = s.rf := by
  unfold stepW; split <;> simp

lemma stepR_frame (s : St K) : (stepR s).pis = s.pis ∧ (stepR s).lo = s.lo ∧
    (stepR s).wpc = s.wpc ∧ (stepR s).wv = s.wv := by
  unfold stepR; split <;> simp

lemma stepW_wpc_ne_idle {s : St K} (h : s.wpc ≠ .idle) : (stepW s).wpc ≠ .idle := by
  unfold stepW; split <;> simp_all <;> split <;> simp

lemma stepR_rpc_ne_idle {s : St K} (h : s.rpc ≠ .idle) : (stepR s).rpc ≠ .idle := by
  unfold stepR; split <;> simp_all; split <;> simp

lemma stepW_c {s : St K} (h : s.wpc ≠ .idle) : (stepW s).c = s.c := by
  simp [St.c, St.n, h, stepW_wpc_ne_idle h, (stepW_frame s).2.2.2.1]

lemma stepR_c (s : St K) : (stepR s).c = s.c := by
  simp [St.c, St.n, (stepR_frame s).2.2.1, (stepR_frame s).2.2.2]

/-! ### Preservation along an execution -/

/-- A property of abstract states preserved by enabled steps (under the invariant) that holds
after `β` holds after every valid extension `β ++ γ`. -/
lemma preserve (Q : St K → Prop)
    (hQ : ∀ s ℓ, Inv v₀ s → Enabled v₀ s ℓ → Q s → Q (sstep v₀ s ℓ))
    {β γ : List (Lbl v₀)} (h : (alg4 v₀).Valid (β ++ γ)) (hβ : Q (sOf v₀ β)) :
    Q (sOf v₀ (β ++ γ)) := by
  induction γ using List.reverseRecOn with
  | nil => simpa using hβ
  | append_singleton γ ℓ ih =>
    rw [← List.append_assoc] at h ⊢
    have hv : (alg4 v₀).Valid (β ++ γ) := (alg4 v₀).valid_of_prefix h (List.prefix_append _ _)
    rw [sOf_snoc]
    exact hQ _ _ (inv_sOf hv) (enabled_of_valid v₀ h) (ih hv)

/-! ### The history of an execution -/

/-- Number of invoked `Read`s. -/
def St.nR (s : St K) : ℕ := s.pis.length + if s.rpc = .idle then 0 else 1

/-- The history of an execution in terms of the abstract state. -/
structure Link (α : List (Lbl v₀)) (s : St K) : Prop where
  opsW : opsOf α .w = s.wv.map RWOp.write
  respsW : respsOf α .w = s.wv.take s.c
  opsR : opsOf α .r = List.replicate s.nR RWOp.read
  respsR : respsOf α .r = s.pis.map (s.vals v₀)

lemma St.c_le_n (s : St K) : s.c ≤ s.n := by unfold St.c; split_ifs <;> omega

theorem link {α : List (Lbl v₀)} (h : (alg4 v₀).Valid α) : Link α (sOf v₀ α) := by
  induction α using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | append_singleton α ℓ ih =>
    have hv : (alg4 v₀).Valid α := (alg4 v₀).valid_of_prefix h (List.prefix_append _ _)
    have hL := ih hv
    have hI := inv_sOf hv
    have hen := enabled_of_valid v₀ h
    rw [sOf_snoc]
    set s := sOf v₀ α with hs
    have hpisn : ∀ p ∈ s.pis, p ≤ s.n := fun p hp =>
      (hI.pis1 p hp).trans (hI.fl1.trans s.nA_le_n)
    suffices H : (s.wv.map RWOp.write ++ (ℓ.invOf .w).toList = (sstep v₀ s ℓ).wv.map RWOp.write) ∧
        (s.wv.take s.c ++ (ℓ.retOf .w).toList = (sstep v₀ s ℓ).wv.take (sstep v₀ s ℓ).c) ∧
        (List.replicate s.nR RWOp.read ++ (ℓ.invOf .r).toList =
          List.replicate (sstep v₀ s ℓ).nR RWOp.read) ∧
        (s.pis.map (s.vals v₀) ++ (ℓ.retOf .r).toList =
          (sstep v₀ s ℓ).pis.map ((sstep v₀ s ℓ).vals v₀)) by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [opsOf_concat, hL.opsW]; exact H.1
      · rw [respsOf_concat, hL.respsW]; exact H.2.1
      · rw [opsOf_concat, hL.opsR]; exact H.2.2.1
      · rw [respsOf_concat, hL.respsR]; exact H.2.2.2
    cases ℓ with
    | inv p o =>
      cases p with
      | w =>
        obtain ⟨hw, v, rfl⟩ := hen
        refine ⟨by simp [sstep], ?_, by simp [sstep, St.nR]; split_ifs with hh <;> simp [hh], ?_⟩
        · simp [sstep, St.c, St.n, hw]
        · simp only [sstep, Label.retOf_inv, Option.toList_none, List.append_nil]
          refine List.map_congr_left fun p hp => ?_
          exact (St.vals_append v₀ s v (hpisn p hp)).symm
      | r =>
        obtain ⟨hr, rfl⟩ := hen
        refine ⟨by simp [sstep], by simp [sstep, St.c, St.n]; split_ifs with hh <;> simp [hh], ?_,
          by simp [sstep, St.vals]⟩
        simp [sstep, St.nR, hr, List.replicate_succ']
    | tau p =>
      cases p with
      | w =>
        obtain ⟨e1, e2, e3, e4, -⟩ := stepW_frame s
        have e5 := stepW_c hen.1
        refine ⟨by simp [sstep, e4], by simp [sstep, e4, e5], by simp [sstep, St.nR, e1, e3],
          by simp [sstep, St.vals, e1, e4]⟩
      | r =>
        obtain ⟨e1, e2, e3, e4⟩ := stepR_frame s
        have e5 := stepR_c s
        have e6 := stepR_rpc_ne_idle hen.1
        refine ⟨by simp [sstep, e4], by simp [sstep, e4, e5], ?_,
          by simp [sstep, St.vals, e1, e4]⟩
        simp [sstep, St.nR, e1, e6, hen.1]
    | ret p x =>
      cases p with
      | w =>
        have hw : s.wpc = .done x := hen
        have hn1 := hI.pend_n (by simp [hw])
        have hc := hI.pend_c (by simp [hw])
        have hx := (hI.pendv x (by simp [hw, WPC.val?])).1
        refine ⟨by simp [sstep, hw], ?_, by simp [sstep, hw, St.nR],
          by simp [sstep, hw, St.vals]⟩
        simp only [sstep, hw, Label.retOf_ret, ite_true, Option.toList_some]
        have : St.c { s with last := x, wpc := .idle } = s.n := by simp [St.c, St.n]
        rw [this, ← hc]
        simp only [St.n] at hn1 hc ⊢
        rw [List.take_add_one, hx]
        simp only [St.vals, St.n, ← hc]
        simp [List.getElem?_eq_getElem (show s.c < s.wv.length by omega)]
      | r =>
        obtain ⟨val, hr, rfl⟩ := hen
        have hl := hI.l10 (by simp [hr, RPC.late])
        simp only [hr, RPC.val?] at hl
        obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.1 hl
        have hv := (hI.rf v (by simp [hr, RPC.val?])).1
        refine ⟨by simp [sstep, hr], by simp [sstep, hr, St.c, St.n], ?_, ?_⟩
        · simp [sstep, hr, St.nR]
        · simp [sstep, hr, St.vals, hv]

/-! ### The reads-from assignment and linearizability -/

/-- **Reads-from assignment.** Read `k` reads from write `rfOf α k` (1-based, `0` = initial
value): if it returns a value found in `A`, the `Write` whose Line 16 wrote that `1`; if it
returns a value found in `B`, the `Write` *preceding* the one that wrote that `1` to `B`
(Line 13 writes `last-val`). -/
def rfOf (α : List (Lbl v₀)) (k : ℕ) : ℕ := (sOf v₀ α).pis.getD k 0

lemma writeVal_map_write (ws : List (Fin K)) {m : ℕ} (hm : m ≤ ws.length) :
    writeVal v₀ (ws.map RWOp.write) m = (v₀ :: ws).getD m v₀ := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [writeVal_succ (v := ws[m]) (by simp [List.getElem?_eq_getElem (show m < ws.length by omega)])]
    simp [List.getElem?_eq_getElem (show m < ws.length by omega)]

lemma pis_le_n {s : St K} (hI : Inv v₀ s) {p : ℕ} (hp : p ∈ s.pis) : p ≤ s.n :=
  (hI.pis1 p hp).trans (hI.fl1.trans s.nA_le_n)

/-- The completed reads' reads-from values form a prefix-stable list. -/
lemma pis_prefix {β γ : List (Lbl v₀)} (h : (alg4 v₀).Valid (β ++ γ)) :
    (sOf v₀ β).pis <+: (sOf v₀ (β ++ γ)).pis := by
  refine preserve (fun s => (sOf v₀ β).pis <+: s.pis) ?_ h (List.prefix_refl _)
  intro s ℓ _ _ hs
  cases ℓ with
  | inv p o => cases p <;> cases o <;> simpa [sstep] using hs
  | tau p =>
    cases p
    · simpa [sstep, (stepW_frame s).1] using hs
    · simpa [sstep, (stepR_frame s).1] using hs
  | ret p x =>
    cases p
    · simp only [sstep]; split <;> simpa using hs
    · simp only [sstep]; split
      · exact hs.trans (List.prefix_append _ _)
      · exact hs

/-- Reads invoked after `β` (in which `c₀` writes completed) have `lo ≥ c₀` and read from a
write `≥ c₀`. -/
lemma rel_ge {β γ : List (Lbl v₀)} (h : (alg4 v₀).Valid (β ++ γ)) :
    (∀ k (hk : k < (sOf v₀ (β ++ γ)).pis.length), (sOf v₀ β).nR ≤ k →
      (sOf v₀ β).c ≤ (sOf v₀ (β ++ γ)).pis[k]) ∧
    ((sOf v₀ (β ++ γ)).rpc ≠ .idle → (sOf v₀ β).nR ≤ (sOf v₀ (β ++ γ)).pis.length →
      (sOf v₀ β).c ≤ (sOf v₀ (β ++ γ)).lo) := by
  let K0 := (sOf v₀ β).nR
  let c0 := (sOf v₀ β).c
  let Q : St K → Prop := fun s => c0 ≤ s.c ∧
    (∀ k (hk : k < s.pis.length), K0 ≤ k → c0 ≤ s.pis[k]) ∧
    (s.rpc ≠ .idle → K0 ≤ s.pis.length → c0 ≤ s.lo)
  have hQ : Q (sOf v₀ (β ++ γ)) := by
    refine preserve Q ?_ h ⟨le_rfl, fun k hk hK => ?_, fun hr hK => ?_⟩
    · intro s ℓ hI hen ⟨q1, q2, q3⟩
      cases ℓ with
      | inv p o =>
        cases p with
        | w =>
          obtain ⟨hw, v, rfl⟩ := hen
          have : St.c { s with wpc := .scanB v 0, wv := s.wv ++ [v] } = s.c := by
            simp [St.c, St.n, hw]
          exact ⟨this ▸ q1, q2, fun hr hK => q3 hr hK⟩
        | r =>
          obtain ⟨hr, rfl⟩ := hen
          exact ⟨q1, q2, fun _ _ => q1⟩
      | tau p =>
        cases p with
        | w =>
          obtain ⟨e1, e2, e3, -, -⟩ := stepW_frame s
          refine ⟨(stepW_c hen.1) ▸ q1, ?_, ?_⟩
          · simp only [sstep, e1]; exact q2
          · simp only [sstep, e1, e2, e3]; exact q3
        | r =>
          obtain ⟨e1, e2, -, -⟩ := stepR_frame s
          refine ⟨(stepR_c s) ▸ q1, ?_, ?_⟩
          · simp only [sstep, e1]; exact q2
          · simp only [sstep, e1, e2]; exact fun _ => q3 hen.1
      | ret p x =>
        cases p with
        | w =>
          have hw : s.wpc = .done x := hen
          have hc := hI.pend_c (by simp [hw])
          simp only [sstep, hw]
          refine ⟨?_, q2, q3⟩
          have : St.c { s with last := x, wpc := .idle } = s.n := by simp [St.c, St.n]
          rw [this]; omega
        | r =>
          obtain ⟨val, hr, rfl⟩ := hen
          have hl := hI.l10 (by simp [hr, RPC.late])
          simp only [hr, RPC.val?] at hl
          obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.1 hl
          have hlo := (hI.rf v (by simp [hr, RPC.val?])).2.2.1
          simp only [sstep, hr]
          refine ⟨q1, fun k hk hK => ?_, fun h' => absurd rfl h'⟩
          simp only [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
          · rw [List.getElem_append_left hk']; exact q2 k hk' hK
          · simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton]
            exact (q3 (by simp [hr]) hK).trans hlo
    · exfalso; simp only [K0, St.nR] at hK; omega
    · simp only [K0, St.nR, hr, ite_false] at hK; omega
  exact hQ.2

/-- **The reads-from criterion holds for every execution of Algorithm 4.** -/
theorem readsFrom {α : List (Lbl v₀)} (hα : (alg4 v₀).Valid α) :
    SWSRReadsFrom α Proc.w Proc.r (rfOf α) := by
  have hL := link hα
  have hI := inv_sOf hα
  set s := sOf v₀ α with hs
  have hnR : (respsOf α .r).length = s.pis.length := by rw [hL.respsR]; simp
  have hrf : ∀ k (hk : k < s.pis.length), rfOf α k = s.pis[k] := fun k hk => by
    simp [rfOf, ← hs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  refine ⟨by decide, hα.wellFormed, fun p o ho => (alg4 v₀).allowed_of_mem_opsOf hα ho,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- write_resp
    intro j v x hop hresp
    rw [opOf, hL.opsW] at hop
    rw [respOf, hL.respsW] at hresp
    simp only [List.getElem?_map, Option.map_eq_some_iff, RWOp.write.injEq] at hop
    obtain ⟨v', h1, rfl⟩ := hop
    rw [List.getElem?_take] at hresp
    split_ifs at hresp
    rw [h1] at hresp; exact (Option.some.inj hresp).symm
  · -- read_val
    intro k hk
    rw [hnR] at hk
    rw [respOf, hL.respsR, hrf k hk, hL.opsW, List.getElem?_map, List.getElem?_eq_getElem hk,
      Option.map_some, writeVal_map_write _ (pis_le_n hI (List.getElem_mem hk))]
    rfl
  · -- not_future
    intro k hk hpos hprec
    rw [hnR] at hk
    obtain ⟨β, γ, rfl, hc, hni⟩ := hprec
    have hβ : (alg4 v₀).Valid β := (alg4 v₀).valid_of_prefix hα (List.prefix_append _ _)
    have hLβ := link hβ
    have hIβ := inv_sOf hβ
    simp only [Completed, hLβ.respsR, List.length_map] at hc
    simp only [Invoked, hLβ.opsW, List.length_map, not_lt] at hni
    obtain ⟨t, ht⟩ := pis_prefix hα
    have : s.pis[k] = (sOf v₀ β).pis[k] := by
      simp only [hs, ← ht, List.getElem_append_left hc]
    have hle := pis_le_n hIβ (List.getElem_mem hc)
    rw [hrf k hk] at hpos hni
    simp only [St.n] at hle
    omega
  · -- not_overwritten
    intro k hk hprec
    rw [hnR] at hk
    obtain ⟨β, γ, rfl, hc, hni⟩ := hprec
    have hβ : (alg4 v₀).Valid β := (alg4 v₀).valid_of_prefix hα (List.prefix_append _ _)
    have hLβ := link hβ
    simp only [Completed, hLβ.respsW, List.length_take] at hc
    simp only [Invoked, hLβ.opsR, List.length_replicate, not_lt] at hni
    have := (rel_ge hα).1 k hk hni
    rw [hrf k hk] at hc
    have e : s.pis[k] = (sOf v₀ (β ++ γ)).pis[k] := rfl
    omega
  · -- mono
    intro k k' hkk hk' _
    rw [hnR] at hk'
    rw [hrf k (by omega), hrf k' hk']
    exact List.pairwise_iff_getElem.1 hI.pis2 k k' (by omega) hk' hkk

/-- The linearization function of Algorithm 4 (reads-from linearization). -/
noncomputable def linFun (α : List (Lbl v₀)) : List (OpId Proc × RWOp (Fin K)) :=
  swsrLin α Proc.w Proc.r (rfOf α)

/-- **Algorithm 4 is linearizable** (Theorem 12). -/
theorem isLinFun : (alg4 v₀).IsLinFun linFun :=
  (alg4 v₀).isLinFun_swsrLin Proc.w Proc.r rfOf (fun _ hα => readsFrom hα)

theorem linearizable : (alg4 v₀).Linearizable := ⟨_, isLinFun⟩

end Alg4

end Cslib.SharedMemory
