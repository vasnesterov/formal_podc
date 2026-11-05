import Papers.PODC2023.WaitFreeQueuePolylog.Progress

/-!
# Lemmas 20 and 21: the lengths of the searches

The searches of lines 91 and 114 are single steps of our model. Their lengths are bounded here:

* **Lemma 20** (`lemma_20`): the search of `FindResponse(b, i)` in the root for the block `bₑ`
  of the enqueue to return covers at most `size(bₑ) + size(b-1) + 1` blocks (the paper proves
  `2·size(bₑ) + size(b-1) + 1`). A doubling search followed by a binary search therefore reads
  `O(log(size(bₑ) + size(b-1) + 2))` blocks.
* **Lemma 21** (`lemma_21`): every block contains at most one operation of each process, and at
  most `c` operations if the point contention never exceeds `c` (`lemma_21_subblocks`: at most
  `c` direct subblocks in each child), so each binary search of line 114 reads `O(log c)` blocks.
-/

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-! ### Lemma 20, abstractly -/

/-- Prefix sums `E`, `D` of enqueues and dequeues of the root blocks and the sizes `S`
(line 50), for blocks `0..m`. -/
structure RootSums (E D S : ℕ → ℕ) (m : ℕ) : Prop where
  zero : E 0 = 0 ∧ D 0 = 0 ∧ S 0 = 0
  emono : ∀ j, 1 ≤ j → j ≤ m → E (j - 1) ≤ E j
  dmono : ∀ j, 1 ≤ j → j ≤ m → D (j - 1) ≤ D j
  ne : ∀ j, 1 ≤ j → j ≤ m → E (j - 1) + D (j - 1) < E j + D j
  size : ∀ j, 1 ≤ j → j ≤ m → S j = S (j - 1) + (E j - E (j - 1)) - (D j - D (j - 1))

namespace RootSums

variable {E D S : ℕ → ℕ} {m : ℕ}

lemma S_le_E (h : RootSums E D S m) : ∀ j, j ≤ m → S j ≤ E j := by
  intro j hj
  induction j with
  | zero => rw [h.zero.1, h.zero.2.2]
  | succ j ih =>
    have := ih (by omega); have := h.size (j + 1) (by omega) hj; have := h.emono (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at *; omega

/-- Non-null dequeues up to block `j`. -/
def N (E S : ℕ → ℕ) (j : ℕ) : ℕ := E j - S j

lemma N_mono (h : RootSums E D S m) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : N E S a ≤ N E S b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    have := ih (by omega); have := h.size (b + 1) (by omega) hb
    have := h.emono (b + 1) (by omega) hb; have := h.S_le_E b (by omega)
    have := h.S_le_E (b + 1) hb
    simp only [N, Nat.add_sub_cancel] at *; omega

lemma E_mono (h : RootSums E D S m) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : E a ≤ E b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => have := h.emono (b + 1) (by omega) hb; simp at this; exact (ih (by omega)).trans this

lemma D_mono (h : RootSums E D S m) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : D a ≤ D b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => have := h.dmono (b + 1) (by omega) hb; simp at this; exact (ih (by omega)).trans this

lemma ED_strict (h : RootSums E D S m) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) :
    E a + D a + (b - a) ≤ E b + D b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => have := h.ne (b + 1) (by omega) hb; simp at this; have := ih (by omega); omega

/-- **Lemma 20 (arithmetic).** If the `i`-th dequeue of block `b` is not null and returns the
`e`-th enqueue (`e = i + E(b-1) - S(b-1)`), which lies in block `bₑ` (`e ≤ E(bₑ)`), then
`b - bₑ ≤ S(bₑ) + S(b-1) + 1`. -/
theorem search_bound (h : RootSums E D S m) {b be i : ℕ} (hb1 : 1 ≤ b) (hbm : b ≤ m)
    (hi1 : 1 ≤ i) (hbe : be ≤ b)
    (hle : i + E (b - 1) - S (b - 1) ≤ E be) :
    b - be ≤ S be + S (b - 1) + 1 := by
  by_cases hcase : b ≤ be + 1
  · omega
  have hSE := h.S_le_E (b - 1) (by omega)
  -- no block strictly between `be` and `b` ends with an empty queue
  have hpos : ∀ j, be < j → j ≤ b - 1 → 0 < S j := by
    intro j h1 h2
    by_contra h0
    have hm1 := h.N_mono (show j ≤ b - 1 from h2) (by omega)
    have hEm := h.E_mono h1.le (show j ≤ m by omega)
    simp only [N] at hm1; omega
  -- hence the sizes are computed without truncation between `be` and `b - 1`
  have hexact : ∀ j, be ≤ j → j ≤ b - 1 → S j + (D j - D be) = S be + (E j - E be) := by
    intro j hj hjb
    induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      have ih := ih (by omega)
      have hp := hpos (j + 1) (by omega) hjb
      have hs := h.size (j + 1) (by omega) (by omega)
      have he := h.emono (j + 1) (by omega) (by omega)
      have hd := h.dmono (j + 1) (by omega) (by omega)
      have e1 := h.E_mono hj (show j ≤ m by omega)
      have d1 := h.D_mono hj (show j ≤ m by omega)
      simp only [Nat.add_sub_cancel] at hs he hd
      omega
  have hx := hexact (b - 1) (by omega) le_rfl
  have hSbe := h.S_le_E be (by omega)
  have e1 := h.E_mono (show be ≤ b - 1 by omega) (by omega)
  have d1 := h.D_mono (show be ≤ b - 1 by omega) (by omega)
  have hst := h.ED_strict (show be ≤ b - 1 by omega) (by omega)
  omega

end RootSums

end Podc.WaitFreeQueuePolylog

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ} {M : Mem V}

lemma rootSums_of_shape (hS : Shape H np M) :
    RootSums (fun j => (M.bk 1 j).sumenq) (fun j => (M.bk 1 j).sumdeq) (fun j => (M.bk 1 j).size)
      (cnt M 1) where
  zero := by simp [hS.bk_zero, Blk.zero]
  emono j h1 h2 := sumenq_mono hS (by omega) h2
  dmono j h1 h2 := sumdeq_mono hS (by omega) h2
  ne j h1 h2 := hS.nonempty 1 j h1 h2
  size j h1 h2 := hS.size j h1 h2

/-- **Lemma 20.** When `FindResponse(b, i)` finds the block `bₑ` of the enqueue to return, at
most `size(bₑ) + size(b-1) + 1` root blocks separate `bₑ` from `b`; hence the doubling search
of line 91 (from `b` downwards) followed by a binary search reads
`O(log(size(bₑ) + size(b-1) + 2))` blocks. -/
theorem lemma_20 (hS : Shape H np M) {b i be ie : ℕ} (hb1 : 1 ≤ b) (hb : b ≤ cnt M 1)
    (hi1 : 1 ≤ i) (hf : findResp M b i = some (be, ie)) :
    b - be ≤ (M.bk 1 be).size + (M.bk 1 (b - 1)).size + 1 := by
  unfold findResp at hf
  simp only at hf
  split at hf
  · cases hf
  rename_i hnn
  simp only [Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨hbe, -⟩ := hf
  have hR := rootSums_of_shape hS
  have hSE := hR.S_le_E (b - 1) (by omega)
  have hm := sumenq_mono hS (show b - 1 ≤ b by omega) hb
  obtain ⟨-, s2, s3, -⟩ := wfq_findFirst_spec (fun j => (M.bk 1 j).sumenq)
    (i + (M.bk 1 (b - 1)).sumenq - (M.bk 1 (b - 1)).size) 0 b ⟨b, by omega, le_rfl, by omega⟩
  rw [hbe] at s2 s3
  exact hR.search_bound hb1 hb hi1 s2 s3

end Podc.WaitFreeQueuePolylog

namespace Podc.WaitFreeQueuePolylog

open Cslib.SharedMemory

variable {V : Type} {H np : ℕ}

/-- The processes with a pending operation after the execution `β` (point contention). -/
def pendingSet (β : List (Label (Fin np) (queueObj V))) : Finset (Fin np) :=
  Finset.univ.filter fun q => (respsOf β q).length < (opsOf β q).length

lemma ops_len_pos {M : Mem V} (hS : Shape H np M) {c j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ cnt M c) :
    1 ≤ (ops H np M c j).length := by
  have e := wfq_len_enqs_rng (H := H) (np := np) hS (w := c) (show j - 1 ≤ j by omega) hj
  have d := wfq_len_deqs_rng (H := H) (np := np) hS (w := c) (show j - 1 ≤ j by omega) hj
  have hr : rng (j - 1) j = [j] := by simp [rng]; omega
  rw [hr] at e d
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e d
  have hne := hS.nonempty c j h1 hj
  have := length_enqs_add_length_deqs (ops H np M c j)
  omega

lemma length_flatMap_ge {X : Type} (s : List ℕ) (f : ℕ → List X) (h : ∀ j ∈ s, 1 ≤ (f j).length) :
    s.length ≤ (s.flatMap f).length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h a (by simp); have := ih (fun j hj => h j (by simp [hj])); omega

/-- **Lemma 21.** In every reachable configuration, each block contains at most one operation
of each process, and at most `c` operations if the point contention of the execution never
exceeds `c`. -/
theorem lemma_21 (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H) {α : List (Label (Fin np) (queueObj V))}
    {C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)}
    (h : (Q H np V).run α = some C) {c : ℕ}
    (hc : ∀ β, β <+: α → (pendingSet β).card ≤ c) :
    ∀ n b, 1 ≤ b → b ≤ cnt (C.mem ()) n →
      ((ops H np (C.mem ()) n b).map fun y => y.1.1).Nodup ∧
      (ops H np (C.mem ()) n b).length ≤ c := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run_nil, Option.some.injEq] at h; subst h
    intro n b h1 h2
    rw [initCfg_mem, cnt_initMem] at h2; omega
  | append_singleton α ℓ ih =>
    have h' := h
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (Q H np V).runFrom (Q H np V).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      have ih := ih hα (fun β hβ => hc β (hβ.trans (List.prefix_append _ _)))
      obtain ⟨G₀, hI₀⟩ := exists_inv hH hnp hα
      obtain ⟨G', hI'⟩ := exists_inv hH hnp h'
      -- the memory changes monotonically
      have hag : ∀ m j, j ≤ cnt (C₀.mem ()) m → (C.mem ()).blk m j = (C₀.mem ()).blk m j := by
        cases ℓ with
        | inv p o =>
          have := (Impl.step_inv h).2.2.2.2; intro m j _; rw [this]
        | ret p r =>
          have := (Impl.step_ret h).2.2.1; intro m j _; rw [this]
        | tau p =>
          obtain ⟨hpn, -, i, o, k, hact, hmem, -⟩ := Impl.step_tau h
          have hact' : act H Variant.fixed p.val (C₀.loc p) = .access i o k := hact
          have hcur : ∀ o, C₀.pend p = some o → (opsOf α p)[(respsOf α p).length]? = some o :=
            fun o ho => ((Q H np V).run_pend_curOp hα ho).2.2
          have hR := stepRes hH hnp hI₀.shape hI₀.minv hI₀.ginv (hI₀.proc p) hcur ⟨i, o, k, hact'⟩
          have hM' : C.mem () = (stepLoc H p (C₀.loc p) (C₀.mem ())).1 := by
            rw [hmem]; simp only [Function.update_self, stepLoc, hact']; rfl
          intro m j hj
          rw [hM']
          exact hR.upd.blk_eq m j hj
      have hlin₀ := hI₀.lin
      have hproc' := hI'.proc
      have hS₀ := hI₀.shape
      have hS' := hI'.shape
      obtain ⟨M₀, hM₀⟩ : ∃ M : Mem V, C₀.mem () = M := ⟨_, rfl⟩
      obtain ⟨M', hM'⟩ : ∃ M : Mem V, C.mem () = M := ⟨_, rfl⟩
      rw [hM₀] at hlin₀ hS₀ ih
      rw [hM'] at hproc' hS'
      rw [hM₀, hM'] at hag
      rw [hM']
      have hcm : ∀ m, cnt M₀ m ≤ cnt M' m := by
        intro m
        by_contra hlt
        have h1 := (hS'.inst m (cnt M₀ m)).not.2 hlt
        rw [hag m _ le_rfl] at h1
        exact h1 (hS₀.blk_isSome le_rfl)
      intro n b hb1 hb
      by_cases hold : b ≤ cnt M₀ n
      · rw [ops_congr hS₀ hag n b hold]
        exact ih n b hb1 hold
      -- a new block: created by an internal step; all its operations are pending in `α`
      have hops : ∀ q, opsOf (α ++ [ℓ]) q = opsOf α q ∧ respsOf (α ++ [ℓ]) q = respsOf α q := by
        cases ℓ with
        | inv p o =>
          have := (Impl.step_inv h).2.2.2.2
          exfalso; apply hold
          have e : M' = M₀ := by rw [← hM', ← hM₀, this]
          rw [e] at hb; exact hb
        | ret p r =>
          have := (Impl.step_ret h).2.2.1
          exfalso; apply hold
          have e : M' = M₀ := by rw [← hM', ← hM₀, this]
          rw [e] at hb; exact hb
        | tau p => exact fun q => ⟨opsOf_append_tau α p q, respsOf_append_tau α p q⟩
      have hpow : 1 ≤ 2 ^ H := Nat.one_le_two_pow
      have hn0 : n ≠ 0 := by
        intro hn; subst hn; have := hS'.unused 0 (Or.inl rfl); omega
      have hnT : n < 2 ^ (H + 1) := by
        by_contra hc'
        have := hS'.unused n (Or.inr (by rw [pow_succ] at hc'; omega)); omega
      have hnd : ((pre H np M' n b).map Prod.fst).Nodup :=
        nodup_keys_preK (H := H) (np := np) M' (cnt M')
          (fun m => by simp [hS'.bk_zero, Blk.zero])
          (fun m j hj => hS'.mono m j hj) (fun m j hj => ⟨hS'.endl_le hj, hS'.endr_le hj⟩)
          (ht H n) n b hb
      have hpend : ∀ y ∈ ops H np M' n b, y.1.2 = (respsOf α y.1.1).length ∧
          y.1.1 ∈ pendingSet α := by
        intro y hy
        obtain ⟨hp1, -⟩ := mem_ops_prov hS' n b hb y hy
        have hlf := (hproc' y.1.1).1 (y.1.2 + 1) (by omega) hp1
        simp only [Nat.add_sub_cancel, (hops y.1.1).1] at hlf
        have hinv : y.1.2 < (opsOf α y.1.1).length := by
          by_contra hc'; rw [List.getElem?_eq_none (by omega)] at hlf; cases hlf
        have hcomp : (respsOf α y.1.1).length ≤ y.1.2 := by
          by_contra hc'
          have hC : Completed α y.1 := by simp only [Completed]; omega
          have hroot := hlin₀.complete _ hC
          rw [mem_rootLin_iff] at hroot
          obtain ⟨z, hz, hzy⟩ := List.mem_map.1 hroot
          have hsub : (2 ^ H + z.1.1) / 2 ^ ht H n = n := by
            rw [hzy]; exact ht_eq_of_mem_ops hy
          have hzn : z ∈ pre H np M₀ n (cnt M₀ n) := by
            by_cases hn1 : n = 1
            · subst hn1; exact hz
            · have := mem_anc hS₀ hnp hz n (by omega) hnT hsub
              refine mem_pre_mono ?_ this
              have h2 := endOf_lt_head hS₀ (m := n / 2) (d := n % 2) (by omega) le_rfl
              rw [two_mul_div_add] at h2
              exact Shape.lt_head_le_cnt h2
          rw [← pre_congr hS₀ hag le_rfl] at hzn
          have hnd' := hnd
          rw [pre_prefix M' n (show cnt M₀ n ≤ b by omega), List.map_append,
            List.nodup_append] at hnd'
          exact hnd'.2.2 z.1 (List.mem_map.2 ⟨z, hzn, rfl⟩) y.1
            (List.mem_map.2 ⟨y, List.mem_flatMap.2 ⟨b, mem_rng.2 ⟨by omega, le_rfl⟩, hy⟩, rfl⟩)
            hzy
        have hc2 : (opsOf α y.1.1).length ≤ (respsOf α y.1.1).length + 1 := by
          rcases (Q H np V).run_counts hα y.1.1 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
        refine ⟨by omega, ?_⟩
        simp only [pendingSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      -- keys are distinct, and determined by the process
      have hndk : ((ops H np M' n b).map Prod.fst).Nodup := by
        have hnd' := hnd
        rw [pre_prefix M' n (show b - 1 ≤ b by omega), List.map_append, List.nodup_append] at hnd'
        have hr : rng (b - 1) b = [b] := by simp [rng]; omega
        rw [hr] at hnd'; simpa using hnd'.2.1
      have hndp : ((ops H np M' n b).map fun y => y.1.1).Nodup := by
        have e : (ops H np M' n b).map (fun y => y.1.1) =
            ((ops H np M' n b).map Prod.fst).map Prod.fst := by simp
        rw [e]
        refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hndk
        obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
        obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
        exact Prod.ext hxy (by rw [(hpend x' hx').1, (hpend y' hy').1, hxy])
      refine ⟨hndp, ?_⟩
      have hsub : ((ops H np M' n b).map fun y => y.1.1).toFinset ⊆ pendingSet α := by
        intro q hq
        simp only [List.mem_toFinset, List.mem_map] at hq
        obtain ⟨y, hy, rfl⟩ := hq
        exact (hpend y hy).2
      have := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hndp, List.length_map] at this
      exact this.trans (hc α (List.prefix_append _ _))

/-- **Lemma 21, second part.** A block of an internal node has at most `c` direct subblocks in
each child (so the binary search of line 114 is among at most `c` blocks). -/
theorem lemma_21_subblocks (hH : 1 ≤ H) (hnp : np ≤ 2 ^ H)
    {α : List (Label (Fin np) (queueObj V))}
    {C : Config (queueObj V) (fun _ : Unit => memObj V) (Fin np) (Loc V)}
    (h : (Q H np V).run α = some C) {c : ℕ}
    (hc : ∀ β, β <+: α → (pendingSet β).card ≤ c) {n b d : ℕ} (hn1 : 1 ≤ n) (hn : n < 2 ^ H)
    (hb1 : 1 ≤ b) (hb : b ≤ cnt (C.mem ()) n) (hd : d < 2) :
    endOf (C.mem ()) n b d - endOf (C.mem ()) n (b - 1) d ≤ c := by
  obtain ⟨G, hI⟩ := exists_inv hH hnp h
  have hS := hI.shape
  have hlen := (lemma_21 hH hnp h hc n b hb1 hb).2
  obtain ⟨M, hM⟩ : ∃ M : Mem V, C.mem () = M := ⟨_, rfl⟩
  rw [hM] at hS hlen hb ⊢
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [Shape.ops_internal n b' hn1 hn] at hlen
  simp only [List.length_append, Nat.add_sub_cancel] at hlen ⊢
  have l1 := length_flatMap_ge (rng (M.bk n b').endl (M.bk n (b' + 1)).endl)
    (ops H np M (2 * n)) (fun j hj => by
      have := mem_rng.1 hj; have := hS.endl_le hb
      exact ops_len_pos hS (by omega) (by omega))
  have l2 := length_flatMap_ge (rng (M.bk n b').endr (M.bk n (b' + 1)).endr)
    (ops H np M (2 * n + 1)) (fun j hj => by
      have := mem_rng.1 hj; have := hS.endr_le hb
      exact ops_len_pos hS (by omega) (by omega))
  simp only [rng, List.length_range'] at l1 l2 hlen
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · simp only [endOf, Blk.endd, ite_true]; omega
  · simp only [endOf, Blk.endd, one_ne_zero, ite_false]; omega

end Podc.WaitFreeQueuePolylog
