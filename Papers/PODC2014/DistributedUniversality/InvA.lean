import Papers.PODC2014.DistributedUniversality.Basic

/-!
# Basic invariants: records of the base objects and local bookkeeping

`InvA` collects the facts about the adopt-commit and simultaneous-consensus records (validity,
agreement, no-conflict), the provenance of every proposed value (it is the proposal `operⱼ[m]` of
some process at the start of the round), and the relation between local variables and records.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ}

/-- The process has obtained its final adopt-commit results of the current round (line 5 or
later). -/
def pastAC : PC → Prop
  | .collect _ => True
  | .loc => True
  | .upd _ => True
  | .write => True
  | _ => False

/-- The process is at line 2 or before in the current round. -/
def prePh1 : PC → Prop
  | .n1Inv _ => True
  | .n1Resp _ => True
  | .scInv => True
  | .scResp => True
  | _ => False

/-- The process has executed lines 16–28 for object `m` in the current round. -/
def pastUpd (pc : PC) (m : Fin k) : Prop :=
  match pc with
  | .upd m' => m.val < m'
  | .write => True
  | _ => False

@[simp] lemma pastAC_collect (q : ℕ) : pastAC (.collect q) := trivial
@[simp] lemma pastAC_loc : pastAC .loc := trivial
@[simp] lemma pastAC_upd (m : ℕ) : pastAC (.upd m) := trivial
@[simp] lemma pastAC_write : pastAC .write := trivial
@[simp] lemma not_pastAC_init : ¬ pastAC .init := id
@[simp] lemma not_pastAC_n1Inv (m : ℕ) : ¬ pastAC (.n1Inv m) := id
@[simp] lemma not_pastAC_n1Resp (m : ℕ) : ¬ pastAC (.n1Resp m) := id
@[simp] lemma not_pastAC_scInv : ¬ pastAC .scInv := id
@[simp] lemma not_pastAC_scResp : ¬ pastAC .scResp := id
@[simp] lemma not_pastAC_acInv (j : ℕ) : ¬ pastAC (.acInv j) := id
@[simp] lemma not_pastAC_acResp (j : ℕ) : ¬ pastAC (.acResp j) := id

@[simp] lemma prePh1_n1Inv (m : ℕ) : prePh1 (.n1Inv m) := trivial
@[simp] lemma prePh1_n1Resp (m : ℕ) : prePh1 (.n1Resp m) := trivial
@[simp] lemma prePh1_scInv : prePh1 .scInv := trivial
@[simp] lemma prePh1_scResp : prePh1 .scResp := trivial
@[simp] lemma not_prePh1_init : ¬ prePh1 .init := id
@[simp] lemma not_prePh1_acInv (j : ℕ) : ¬ prePh1 (.acInv j) := id
@[simp] lemma not_prePh1_acResp (j : ℕ) : ¬ prePh1 (.acResp j) := id
@[simp] lemma not_prePh1_collect (q : ℕ) : ¬ prePh1 (.collect q) := id
@[simp] lemma not_prePh1_loc : ¬ prePh1 .loc := id
@[simp] lemma not_prePh1_upd (m : ℕ) : ¬ prePh1 (.upd m) := id
@[simp] lemma not_prePh1_write : ¬ prePh1 .write := id

@[simp] lemma pastUpd_upd (m' : ℕ) (m : Fin k) : pastUpd (.upd m') m ↔ m.val < m' := Iff.rfl
@[simp] lemma pastUpd_write (m : Fin k) : pastUpd .write m := trivial
@[simp] lemma not_pastUpd_init (m : Fin k) : ¬ pastUpd .init m := id
@[simp] lemma not_pastUpd_n1Inv (m' : ℕ) (m : Fin k) : ¬ pastUpd (.n1Inv m') m := id
@[simp] lemma not_pastUpd_n1Resp (m' : ℕ) (m : Fin k) : ¬ pastUpd (.n1Resp m') m := id
@[simp] lemma not_pastUpd_scInv (m : Fin k) : ¬ pastUpd .scInv m := id
@[simp] lemma not_pastUpd_scResp (m : Fin k) : ¬ pastUpd .scResp m := id
@[simp] lemma not_pastUpd_acInv (j : ℕ) (m : Fin k) : ¬ pastUpd (.acInv j) m := id
@[simp] lemma not_pastUpd_acResp (j : ℕ) (m : Fin k) : ¬ pastUpd (.acResp j) m := id
@[simp] lemma not_pastUpd_collect (q : ℕ) (m : Fin k) : ¬ pastUpd (.collect q) m := id
@[simp] lemma not_pastUpd_loc (m : Fin k) : ¬ pastUpd .loc m := id

/-- Basic invariants. -/
structure InvA (M : Mode) (s : St n k) : Prop where
  ca_n1 : ∀ i m, ((s.loc i).pc = .n1Inv m ∨ (s.loc i).pc = .n1Resp m) → M.ca = true
  init_r : ∀ i, (s.loc i).pc = .init ↔ (s.loc i).r = 0
  -- records of the base objects
  acR_inv : ∀ r b y j t w, s.acR r b y j = some (t, w) → ∃ own, s.acI r b y j = some own ∧
    (∃ j', s.acI r b y j' = some w) ∧
    ((t = true ∧ w = own) ∨ ∃ q w', q ≠ j ∧ s.acI r b y q = some w' ∧ w' ≠ own)
  acR_agree : ∀ r b y j j' v t w, s.acR r b y j = some (true, v) → s.acR r b y j' = some (t, w) →
    w = v
  acI0 : ∀ r y j w, s.acI r false y j = some w → s.opRec r y j = some w
  acI1 : ∀ r y j w, s.acI r true y j = some w → ∃ j', s.opRec r y j' = some w
  acI1ca : M.ca = true → M.typo4M = false → ∀ r y j w, s.acI r true y j = some w →
    ∃ j' t, s.acR r false y j' = some (t, w)
  scI_prov : ∀ r j u, s.scI r j = some u → ∀ y, ∃ j', s.opRec r y j' = some (u y)
  scI_ca : M.ca = true → ∀ r j u, s.scI r j = some u → ∀ y, ∃ j' t,
    s.acR r false y j' = some (t, u y)
  scR_valid : ∀ r j d y v, s.scR r j = some d → d y = some v → ∃ j' u, s.scI r j' = some u ∧
    u y = v
  finR_src : ∀ r m j tw, s.finR r m j = some tw →
    s.acR r true m j = some tw ∨ (tw.1 = true ∧ s.acR r false m j = some tw)
  acR_le : ∀ r b y j tw, s.acR r b y j = some tw → r ≤ (s.loc j).r
  opRec_le : ∀ r m j w, s.opRec r m j = some w → 1 ≤ r ∧ r ≤ (s.loc j).r
  finR_fut : ∀ r m j tw, s.finR r m j = some tw →
    r < (s.loc j).r ∨ (r = (s.loc j).r ∧ pastAC (s.loc j).pc)
  finR_past : ∀ i r m, 1 ≤ r → r < (s.loc i).r → ∃ tw, s.finR r m i = some tw
  -- local bookkeeping
  oper_rec : ∀ i m, (s.loc i).pc ≠ .init → ¬ pastUpd (s.loc i).pc m →
    s.opRec (s.loc i).r m i = some ((s.loc i).oper m)
  n1_loc : ∀ i m', ((s.loc i).pc = .n1Inv m' ∨ (s.loc i).pc = .n1Resp m') → ∀ y : Fin k,
    (y.val < m' → s.acR (s.loc i).r false y i = some ((s.loc i).tag y, (s.loc i).acop y)) ∧
    (m' ≤ y.val → s.acR (s.loc i).r false y i = none) ∧
    ((m' < y.val ∨ ((s.loc i).pc = .n1Inv m' ∧ m' = y.val)) → s.acI (s.loc i).r false y i = none)
  n1_pend : ∀ i m (hm : m < k), (s.loc i).pc = .n1Resp m →
    s.acI (s.loc i).r false ⟨m, hm⟩ i = some ((s.loc i).oper ⟨m, hm⟩)
  ph1_none : ∀ i, prePh1 (s.loc i).pc → ∀ y, s.acR (s.loc i).r true y i = none ∧
    s.acI (s.loc i).r true y i = none
  acI_le : ∀ r b y j w, s.acI r b y j = some w → r ≤ (s.loc j).r
  sc_loc : ∀ i, ((s.loc i).pc = .scInv ∨ (s.loc i).pc = .scResp) → M.ca = true → ∀ y,
    s.acR (s.loc i).r false y i = some ((s.loc i).tag y, (s.loc i).acop y)
  ph1_loc : ∀ i j, ((s.loc i).pc = .acInv j ∨ (s.loc i).pc = .acResp j) →
    s.scR (s.loc i).r i = some (s.loc i).scd ∧ (s.loc i).ord = ordOf (s.loc i).scd ∧ j ≤ k ∧
    ∀ y, (y ∈ (s.loc i).ord.take j →
        s.acR (s.loc i).r true y i = some ((s.loc i).tag y, (s.loc i).acop y)) ∧
      (y ∉ (s.loc i).ord.take j → s.acR (s.loc i).r true y i = none ∧
        (M.ca = true → s.acR (s.loc i).r false y i = some ((s.loc i).tag y, (s.loc i).acop y))) ∧
      (y ∉ (s.loc i).ord.take (if (s.loc i).pc = .acInv j then j else j + 1) →
        s.acI (s.loc i).r true y i = none)
  ac_pend : ∀ i j x, (s.loc i).pc = .acResp j → (s.loc i).ord[j]? = some x →
    s.acI (s.loc i).r true x i = some (acVal M (s.loc i) x)
  scI_le : ∀ r j u, s.scI r j = some u → r ≤ (s.loc j).r
  scI_none : ∀ i, ((∃ m, (s.loc i).pc = .n1Inv m) ∨ (∃ m, (s.loc i).pc = .n1Resp m) ∨
    (s.loc i).pc = .scInv) → s.scI (s.loc i).r i = none
  acI0_ca : ∀ r y j w, s.acI r false y j = some w → M.ca = true
  finR_pos : ∀ r m j tw, s.finR r m j = some tw → 1 ≤ r
  finR_loc : ∀ i, pastAC (s.loc i).pc → ∀ m,
    s.finR (s.loc i).r m i = some ((s.loc i).tag m, (s.loc i).acop m)


theorem invA_init (M : Mode) : InvA M (init : St n k) := by
  constructor <;> simp [init, initLoc]

section Steps
variable {M : Mode} {s s' : St n k} {a : Act n k}

theorem InvA.init_r_step (I : InvA M s) (h : stepFn M s a = some s') (i : Fin n) :
    (s'.loc i).pc = .init ↔ (s'.loc i).r = 0 := by
  have hI := I.init_r i
  du_step_cases h <;> by_cases hi : i = a.proc <;>
    first
    | simp [Function.update_of_ne hi, hI]
    | (subst hi; rw [hpc] at hI; simp [startPC, updPC, afterN1] at hI ⊢;
       (try split_ifs) <;> simp [hI])

theorem InvA.acI_mono (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j w, s.acI r b y j = some w → s'.acI r b y j = some w := by
  intro r b y j w hw
  du_step_cases h <;> simp only [tN1Inv_acI, tAcInv_acI, tInit_acI, tN1Resp_acI, tScInv_acI,
    tScResp_acI, tAcResp_acI, tCollect_acI, tLoc_acI, tUpdIn_acI, tUpdMine_acI, tUpdOther_acI,
    tUpdAdopt_acI, tWrite_acI, hw]
  · split_ifs with hc
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      have := (I.n1_loc a.proc m (Or.inl hpc) ⟨m, hm⟩).2.2 (Or.inr ⟨hpc, rfl⟩)
      simp [this] at hw
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, rfl, hyx, rfl⟩ := hc
      subst hyx
      obtain ⟨-, hord, -, hy⟩ := I.ph1_loc a.proc j (Or.inl hpc)
      have hxn := not_mem_take_of_getElem? (hord ▸ ordOf_nodup _) hx
      have := (hy y).2.2 (by simpa [hpc] using hxn)
      simp [this] at hw
    · rfl

theorem InvA.acR_mono (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j tw, s.acR r b y j = some tw → s'.acR r b y j = some tw := by
  intro r b y j tw hw
  du_step_cases h <;> simp only [tN1Inv_acR, tAcInv_acR, tInit_acR, tN1Resp_acR, tScInv_acR,
    tScResp_acR, tAcResp_acR, tCollect_acR, tLoc_acR, tUpdIn_acR, tUpdMine_acR, tUpdOther_acR,
    tUpdAdopt_acR, tWrite_acR, hw]
  · split_ifs with hc
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      have := (I.n1_loc a.proc m (Or.inr hpc) ⟨m, hm⟩).2.1 le_rfl
      simp [this] at hw
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, rfl, hyx, rfl⟩ := hc
      subst hyx
      obtain ⟨-, hord, -, hy⟩ := I.ph1_loc a.proc j (Or.inr hpc)
      have hxn := not_mem_take_of_getElem? (hord ▸ ordOf_nodup _) hx
      have := ((hy y).2.1 hxn).1
      simp [this] at hw
    · rfl

theorem InvA.opRec_mono (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j w, s.opRec r m j = some w → s'.opRec r m j = some w := by
  intro r m j w hw
  du_step_cases h <;> simp only [tN1Inv_opRec, tAcInv_opRec, tInit_opRec, tN1Resp_opRec,
    tScInv_opRec, tScResp_opRec, tAcResp_opRec, tCollect_opRec, tLoc_opRec, tUpdIn_opRec,
    tUpdMine_opRec, tUpdOther_opRec, tUpdAdopt_opRec, tWrite_opRec, hw]
  · split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have h1 := I.opRec_le _ _ _ _ hw
      have h2 := (I.init_r a.proc).1 hpc
      omega
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      have h1 := I.opRec_le _ _ _ _ hw
      omega
    · rfl

theorem InvA.finR_mono (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j tw, s.finR r m j = some tw → s'.finR r m j = some tw := by
  intro r m' j tw hw
  du_step_cases h <;> simp only [tN1Inv_finR, tAcInv_finR, tInit_finR, tN1Resp_finR, tScInv_finR,
    tScResp_finR, tAcResp_finR, tCollect_finR, tLoc_finR, tUpdIn_finR, tUpdMine_finR,
    tUpdOther_finR, tUpdAdopt_finR, tWrite_finR, hw]
  · split_ifs with hc
    · obtain ⟨rfl, rfl, -⟩ := hc
      rcases I.finR_fut _ _ _ _ hw with h1 | ⟨-, h1⟩
      · omega
      · simp [hpc] at h1
    · rfl
  · split_ifs with hc
    · obtain ⟨rfl, rfl, -⟩ := hc
      rcases I.finR_fut _ _ _ _ hw with h1 | ⟨-, h1⟩
      · omega
      · simp [hpc] at h1
    · rfl

theorem InvA.scI_mono (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r j u, s.scI r j = some u → s'.scI r j = some u := by
  intro r j u hw
  du_step_cases h <;> simp only [tN1Inv_scI, tAcInv_scI, tInit_scI, tN1Resp_scI, tScInv_scI,
    tScResp_scI, tAcResp_scI, tCollect_scI, tLoc_scI, tUpdIn_scI, tUpdMine_scI, tUpdOther_scI,
    tUpdAdopt_scI, tWrite_scI, hw]
  by_cases hc : r = (s.loc a.proc).r ∧ j = a.proc
  · obtain ⟨rfl, rfl⟩ := hc
    have := I.scI_none a.proc (Or.inr (Or.inr hpc))
    simp [this] at hw
  · simp [hc]

/-- Consequence of the adopt-commit guard used for `acR_inv`. -/
theorem acOK_inv {strong : Bool} {inv : Fin n → Option (Op n)}
    {resp : Fin n → Option (Bool × Op n)} {free : Option (Op n)} {i : Fin n} {own : Op n}
    {t : Bool} {v : Op n} (hok : acOK strong inv resp free i own t v) :
    (∃ j', inv j' = some v) ∧
    ((t = true ∧ v = own) ∨ ∃ q w', q ≠ i ∧ inv q = some w' ∧ w' ≠ own) := by
  obtain ⟨h1, -, -, h4, -⟩ := hok
  refine ⟨h1, ?_⟩
  by_cases hp : ∀ q, q ≠ i → ∀ w ∈ inv q, w = own
  · exact Or.inl (h4 hp)
  · push_neg at hp
    obtain ⟨q, hq, w, hw, hne⟩ := hp
    exact Or.inr ⟨q, w, hq, hw, hne⟩

theorem InvA.acR_inv_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j t w, s'.acR r b y j = some (t, w) → ∃ own, s'.acI r b y j = some own ∧
      (∃ j', s'.acI r b y j' = some w) ∧
      ((t = true ∧ w = own) ∨ ∃ q w', q ≠ j ∧ s'.acI r b y q = some w' ∧ w' ≠ own) := by
  intro r b y j0 t0 w0 hw
  have hmI := I.acI_mono h
  by_cases hold : s.acR r b y j0 = some (t0, w0)
  · obtain ⟨own, h1, ⟨j', h2⟩, h3⟩ := I.acR_inv _ _ _ _ _ _ hold
    refine ⟨own, hmI _ _ _ _ _ h1, ⟨j', hmI _ _ _ _ _ h2⟩, ?_⟩
    rcases h3 with h3 | ⟨q, w', hq, h4, h5⟩
    · exact Or.inl h3
    · exact Or.inr ⟨q, w', hq, hmI _ _ _ _ _ h4, h5⟩
  · du_step_cases h <;> simp only [tN1Inv_acR, tAcInv_acR, tInit_acR, tN1Resp_acR, tScInv_acR,
      tScResp_acR, tAcResp_acR, tCollect_acR, tLoc_acR, tUpdIn_acR, tUpdMine_acR,
      tUpdOther_acR, tUpdAdopt_acR, tWrite_acR] at hw <;> try exact absurd hw hold
    · split_ifs at hw with hc
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hv, hc'⟩ := acOK_inv hok
        simp only [tN1Resp_acI]
        exact ⟨_, I.n1_pend a.proc m hm hpc, hv, hc'⟩
      · exact absurd hw hold
    · split_ifs at hw with hc
      · obtain ⟨rfl, rfl, hyx, rfl⟩ := hc
        subst hyx
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hv, hc'⟩ := acOK_inv hok
        simp only [tAcResp_acI]
        exact ⟨_, I.ac_pend a.proc j y hpc hx, hv, hc'⟩
      · exact absurd hw hold

/-- A response entry that is new after a step was produced by the stepping process, with the
adopt-commit guard. -/
theorem InvA.acR_new (I : InvA M s) (h : stepFn M s a = some s') {r b y j tw}
    (hw : s'.acR r b y j = some tw) (hold : s.acR r b y j ≠ some tw) :
    j = a.proc ∧ r = (s.loc a.proc).r ∧ s.acR r b y j = none ∧ s'.acI = s.acI ∧
    ∃ own, s.acI r b y j = some own ∧
      acOK M.strongAC (s.acI r b y) (s.acR r b y) (s.acFree r b y) j own tw.1 tw.2 ∧
      ((b = false ∧ ∃ m, (s.loc a.proc).pc = .n1Resp m ∧ y.val = m ∧ own = (s.loc a.proc).oper y)
       ∨ (b = true ∧ ∃ jj, (s.loc a.proc).pc = .acResp jj ∧ (s.loc a.proc).ord[jj]? = some y ∧
          own = acVal M (s.loc a.proc) y)) := by
  du_step_cases h <;> simp only [tN1Inv_acR, tAcInv_acR, tInit_acR, tN1Resp_acR, tScInv_acR,
      tScResp_acR, tAcResp_acR, tCollect_acR, tLoc_acR, tUpdIn_acR, tUpdMine_acR,
      tUpdOther_acR, tUpdAdopt_acR, tWrite_acR] at hw <;> try exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hw
      subst hw
      exact ⟨rfl, rfl, (I.n1_loc a.proc m (Or.inr hpc) ⟨m, hm⟩).2.1 le_rfl, rfl, _,
        I.n1_pend a.proc m hm hpc, hok, Or.inl ⟨rfl, m, hpc, rfl, rfl⟩⟩
    · exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, hyx, rfl⟩ := hc
      subst hyx
      simp only [Option.some.injEq] at hw
      subst hw
      obtain ⟨-, hord, -, hy⟩ := I.ph1_loc a.proc j (Or.inr hpc)
      have hxn := not_mem_take_of_getElem? (hord ▸ ordOf_nodup _) hx
      exact ⟨rfl, rfl, ((hy y).2.1 hxn).1, rfl, _, I.ac_pend a.proc j y hpc hx, hok,
        Or.inr ⟨rfl, j, hpc, hx, rfl⟩⟩
    · exact absurd hw hold

theorem InvA.acR_agree_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j j' v t w, s'.acR r b y j = some (true, v) → s'.acR r b y j' = some (t, w) →
      w = v := by
  intro r b y j1 j2 v0 t0 w0 h1 h2
  by_cases o1 : s.acR r b y j1 = some (true, v0) <;>
    by_cases o2 : s.acR r b y j2 = some (t0, w0)
  · exact I.acR_agree _ _ _ _ _ _ _ _ o1 o2
  · obtain ⟨rfl, rfl, -, -, own, -, ⟨-, hag1, -, -, -⟩, -⟩ := I.acR_new h h2 o2
    exact (hag1 _ _ o1 rfl).symm
  · obtain ⟨rfl, rfl, -, -, own, -, ⟨-, -, hag2, -, -⟩, -⟩ := I.acR_new h h1 o1
    exact (hag2 rfl _ _ o2)
  · obtain ⟨rfl, rfl, -, -, -⟩ := I.acR_new h h1 o1
    obtain ⟨hj, -⟩ := I.acR_new h h2 o2
    subst hj
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact h2.2.symm

theorem InvA.acI_new (I : InvA M s) (h : stepFn M s a = some s') {r b y j w}
    (hw : s'.acI r b y j = some w) (hold : s.acI r b y j ≠ some w) :
    j = a.proc ∧ r = (s.loc a.proc).r ∧
    ((b = false ∧ ∃ m, (s.loc a.proc).pc = .n1Inv m ∧ y.val = m ∧ w = (s.loc a.proc).oper y)
     ∨ (b = true ∧ ∃ jj, (s.loc a.proc).pc = .acInv jj ∧ (s.loc a.proc).ord[jj]? = some y ∧
          w = acVal M (s.loc a.proc) y)) := by
  du_step_cases h <;> simp only [tN1Inv_acI, tAcInv_acI, tInit_acI, tN1Resp_acI, tScInv_acI,
      tScResp_acI, tAcResp_acI, tCollect_acI, tLoc_acI, tUpdIn_acI, tUpdMine_acI,
      tUpdOther_acI, tUpdAdopt_acI, tWrite_acI] at hw <;> try exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hw
      exact ⟨rfl, rfl, Or.inl ⟨rfl, m, hpc, rfl, hw.symm⟩⟩
    · exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, hyx, rfl⟩ := hc
      subst hyx
      simp only [Option.some.injEq] at hw
      exact ⟨rfl, rfl, Or.inr ⟨rfl, j, hpc, hx, hw.symm⟩⟩
    · exact absurd hw hold

theorem InvA.opRec_new (I : InvA M s) (h : stepFn M s a = some s') {r m j w}
    (hw : s'.opRec r m j = some w) (hold : s.opRec r m j ≠ some w) :
    j = a.proc ∧ (((s.loc a.proc).pc = .init ∧ r = 1 ∧ w = (a.proc, 0)) ∨
      ((s.loc a.proc).pc = .write ∧ r = (s.loc a.proc).r + 1 ∧ w = (s.loc a.proc).oper m)) := by
  du_step_cases h <;> simp only [tN1Inv_opRec, tAcInv_opRec, tInit_opRec, tN1Resp_opRec,
      tScInv_opRec, tScResp_opRec, tAcResp_opRec, tCollect_opRec, tLoc_opRec, tUpdIn_opRec,
      tUpdMine_opRec, tUpdOther_opRec, tUpdAdopt_opRec, tWrite_opRec] at hw <;>
      try exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hw
      exact ⟨rfl, Or.inl ⟨hpc, rfl, hw.symm⟩⟩
    · exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hw
      exact ⟨rfl, Or.inr ⟨hpc, rfl, hw.symm⟩⟩
    · exact absurd hw hold

theorem InvA.scI_new (I : InvA M s) (h : stepFn M s a = some s') {r j u}
    (hw : s'.scI r j = some u) (hold : s.scI r j ≠ some u) :
    j = a.proc ∧ r = (s.loc a.proc).r ∧ (s.loc a.proc).pc = .scInv ∧
      u = if M.ca then (s.loc a.proc).acop else (s.loc a.proc).oper := by
  du_step_cases h <;> simp only [tN1Inv_scI, tAcInv_scI, tInit_scI, tN1Resp_scI, tScInv_scI,
      tScResp_scI, tAcResp_scI, tCollect_scI, tLoc_scI, tUpdIn_scI, tUpdMine_scI, tUpdOther_scI,
      tUpdAdopt_scI, tWrite_scI] at hw <;> try exact absurd hw hold
  by_cases hc : r = (s.loc a.proc).r ∧ j = a.proc
  · obtain ⟨rfl, rfl⟩ := hc
    simp only [and_self, ↓reduceIte, Option.some.injEq] at hw
    exact ⟨rfl, rfl, hpc, hw.symm⟩
  · simp only [hc, ↓reduceIte] at hw
    exact absurd hw hold

theorem InvA.finR_new (I : InvA M s) (h : stepFn M s a = some s') {r m j tw}
    (hw : s'.finR r m j = some tw) (hold : s.finR r m j ≠ some tw) :
    j = a.proc ∧ r = (s.loc a.proc).r ∧ (s'.loc a.proc).pc = .collect 0 ∧
      (s'.loc a.proc).r = (s.loc a.proc).r ∧
      tw = ((s'.loc a.proc).tag m, (s'.loc a.proc).acop m) := by
  du_step_cases h <;> simp only [tN1Inv_finR, tAcInv_finR, tInit_finR, tN1Resp_finR, tScInv_finR,
      tScResp_finR, tAcResp_finR, tCollect_finR, tLoc_finR, tUpdIn_finR, tUpdMine_finR,
      tUpdOther_finR, tUpdAdopt_finR, tWrite_finR] at hw <;> try exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, hlast, hall⟩ := hc
      simp only [Option.some.injEq] at hw
      refine ⟨rfl, rfl, ?_, by simp, by simp [hw]⟩
      simp [hlast, afterN1]
      intro z; exact hall z
    · exact absurd hw hold
  · split_ifs at hw with hc
    · obtain ⟨rfl, rfl, hlast⟩ := hc
      simp only [Option.some.injEq] at hw
      exact ⟨rfl, rfl, by simp [hlast], by simp, by simp [hw]⟩
    · exact absurd hw hold

/-- The values proposed at line 3/4 (3M/4M) are proposals of the round. -/
theorem InvA.acVal_prov (I : InvA M s) {i : Fin n} {jj : ℕ} {y : Fin k}
    (hpc : (s.loc i).pc = .acInv jj) (hy : (s.loc i).ord[jj]? = some y) :
    (∃ j', s.opRec (s.loc i).r y j' = some (acVal M (s.loc i) y)) ∧
    (M.ca = true → M.typo4M = false →
      ∃ j' t, s.acR (s.loc i).r false y j' = some (t, acVal M (s.loc i) y)) := by
  obtain ⟨hscR, hord, -, hyy⟩ := I.ph1_loc i jj (Or.inl hpc)
  have hxn := not_mem_take_of_getElem? (hord ▸ ordOf_nodup _) hy
  obtain ⟨-, hca⟩ := (hyy y).2.1 hxn
  unfold acVal
  cases hd : (s.loc i).scd y with
  | some v =>
    obtain ⟨j', u, hu, huy⟩ := I.scR_valid _ _ _ _ _ hscR hd
    obtain ⟨j'', h''⟩ := I.scI_prov _ _ _ hu y
    refine ⟨⟨j'', by simpa [huy] using h''⟩, fun hc _ => ?_⟩
    obtain ⟨j3, t3, h3⟩ := I.scI_ca hc _ _ _ hu y
    exact ⟨j3, t3, by simpa [huy] using h3⟩
  | none =>
    simp only [Option.getD_none]
    by_cases hc : M.ca = true ∧ M.typo4M = false
    · simp only [hc, and_self, ↓reduceIte]
      have h1 := hca hc.1
      obtain ⟨own, -, ⟨j', hj'⟩, -⟩ := I.acR_inv _ _ _ _ _ _ h1
      exact ⟨⟨j', I.acI0 _ _ _ _ hj'⟩, fun _ _ => ⟨i, _, h1⟩⟩
    · simp only [hc, ↓reduceIte]
      refine ⟨⟨i, I.oper_rec i y (by simp [hpc]) (by simp [hpc])⟩, fun h1 h2 => ?_⟩
      exact absurd ⟨h1, h2⟩ hc

theorem InvA.acI0_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r y j w, s'.acI r false y j = some w → s'.opRec r y j = some w := by
  intro r y j w hw
  by_cases hold : s.acI r false y j = some w
  · exact I.opRec_mono h _ _ _ _ (I.acI0 _ _ _ _ hold)
  · obtain ⟨rfl, rfl, hc⟩ := I.acI_new h hw hold
    rcases hc with ⟨-, m, hpc, -, rfl⟩ | ⟨h1, -⟩
    · exact I.opRec_mono h _ _ _ _ (I.oper_rec _ y (by simp [hpc]) (by simp [hpc]))
    · simp at h1

theorem InvA.acI1_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r y j w, s'.acI r true y j = some w → ∃ j', s'.opRec r y j' = some w := by
  intro r y j w hw
  by_cases hold : s.acI r true y j = some w
  · obtain ⟨j', hj'⟩ := I.acI1 _ _ _ _ hold
    exact ⟨j', I.opRec_mono h _ _ _ _ hj'⟩
  · obtain ⟨rfl, rfl, hc⟩ := I.acI_new h hw hold
    rcases hc with ⟨h1, -⟩ | ⟨-, jj, hpc, hy, rfl⟩
    · simp at h1
    · obtain ⟨⟨j', hj'⟩, -⟩ := I.acVal_prov hpc hy
      exact ⟨j', I.opRec_mono h _ _ _ _ hj'⟩

theorem InvA.acI1ca_step (I : InvA M s) (h : stepFn M s a = some s') :
    M.ca = true → M.typo4M = false → ∀ r y j w, s'.acI r true y j = some w →
      ∃ j' t, s'.acR r false y j' = some (t, w) := by
  intro hca hty r y j w hw
  by_cases hold : s.acI r true y j = some w
  · obtain ⟨j', t, hj'⟩ := I.acI1ca hca hty _ _ _ _ hold
    exact ⟨j', t, I.acR_mono h _ _ _ _ _ hj'⟩
  · obtain ⟨rfl, rfl, hc⟩ := I.acI_new h hw hold
    rcases hc with ⟨h1, -⟩ | ⟨-, jj, hpc, hy, rfl⟩
    · simp at h1
    · obtain ⟨-, h2⟩ := I.acVal_prov hpc hy
      obtain ⟨j', t, hj'⟩ := h2 hca hty
      exact ⟨j', t, I.acR_mono h _ _ _ _ _ hj'⟩

theorem InvA.scI_prov_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r j u, s'.scI r j = some u → ∀ y, ∃ j', s'.opRec r y j' = some (u y) := by
  intro r j u hw y
  by_cases hold : s.scI r j = some u
  · obtain ⟨j', hj'⟩ := I.scI_prov _ _ _ hold y
    exact ⟨j', I.opRec_mono h _ _ _ _ hj'⟩
  · obtain ⟨rfl, rfl, hpc, rfl⟩ := I.scI_new h hw hold
    by_cases hc : M.ca = true
    · simp only [hc, ↓reduceIte]
      have h1 := I.sc_loc _ (Or.inl hpc) hc y
      obtain ⟨own, -, ⟨j', hj'⟩, -⟩ := I.acR_inv _ _ _ _ _ _ h1
      exact ⟨j', I.opRec_mono h _ _ _ _ (I.acI0 _ _ _ _ hj')⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, I.opRec_mono h _ _ _ _ (I.oper_rec _ y (by simp [hpc]) (by simp [hpc]))⟩

theorem InvA.scI_ca_step (I : InvA M s) (h : stepFn M s a = some s') :
    M.ca = true → ∀ r j u, s'.scI r j = some u → ∀ y, ∃ j' t,
      s'.acR r false y j' = some (t, u y) := by
  intro hc r j u hw y
  by_cases hold : s.scI r j = some u
  · obtain ⟨j', t, hj'⟩ := I.scI_ca hc _ _ _ hold y
    exact ⟨j', t, I.acR_mono h _ _ _ _ _ hj'⟩
  · obtain ⟨rfl, rfl, hpc, rfl⟩ := I.scI_new h hw hold
    simp only [hc, ↓reduceIte]
    exact ⟨_, _, I.acR_mono h _ _ _ _ _ (I.sc_loc _ (Or.inl hpc) hc y)⟩

theorem InvA.scR_valid_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r j d y v, s'.scR r j = some d → d y = some v → ∃ j' u, s'.scI r j' = some u ∧
      u y = v := by
  intro r j d y v hd hv
  by_cases hold : s.scR r j = some d
  · obtain ⟨j', u, hu, huy⟩ := I.scR_valid _ _ _ _ _ hold hv
    exact ⟨j', u, I.scI_mono h _ _ _ hu, huy⟩
  · du_step_cases h <;> simp only [tN1Inv_scR, tAcInv_scR, tInit_scR, tN1Resp_scR, tScInv_scR,
      tScResp_scR, tAcResp_scR, tCollect_scR, tLoc_scR, tUpdIn_scR, tUpdMine_scR, tUpdOther_scR,
      tUpdAdopt_scR, tWrite_scR] at hd <;> try exact absurd hd hold
    by_cases hc : r = (s.loc a.proc).r ∧ j = a.proc
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ↓reduceIte, Option.some.injEq] at hd
      subst hd
      obtain ⟨-, h2, -⟩ := hok
      obtain ⟨q, u, hu, huy⟩ := h2 y v hv
      exact ⟨q, u, by simpa using hu, huy⟩
    · simp only [hc, ↓reduceIte] at hd
      exact absurd hd hold

theorem InvA.finR_src_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j tw, s'.finR r m j = some tw →
      s'.acR r true m j = some tw ∨ (tw.1 = true ∧ s'.acR r false m j = some tw) := by
  intro r y j0 tw hw
  by_cases hold : s.finR r y j0 = some tw
  · rcases I.finR_src _ _ _ _ hold with h1 | ⟨h1, h2⟩
    · exact Or.inl (I.acR_mono h _ _ _ _ _ h1)
    · exact Or.inr ⟨h1, I.acR_mono h _ _ _ _ _ h2⟩
  · du_step_cases h <;> simp only [tN1Inv_finR, tAcInv_finR, tInit_finR, tN1Resp_finR, tScInv_finR,
      tScResp_finR, tAcResp_finR, tCollect_finR, tLoc_finR, tUpdIn_finR, tUpdMine_finR,
      tUpdOther_finR, tUpdAdopt_finR, tWrite_finR] at hw <;> try exact absurd hw hold
    · split_ifs at hw with hc
      · obtain ⟨rfl, rfl, hlast, hall⟩ := hc
        simp only [Option.some.injEq] at hw
        subst hw
        refine Or.inr ⟨hall y, ?_⟩
        by_cases hyx : y = ⟨m, hm⟩
        · subst hyx; simp
        · have hy : y.val < m := by
            have : y.val ≠ m := fun h' => hyx (Fin.ext h')
            have := y.isLt; omega
          have h1 := (I.n1_loc a.proc m (Or.inr hpc) y).1 hy
          have h2 := I.acR_mono h _ _ _ _ _ h1
          simpa [Function.update_of_ne hyx] using h2
      · exact absurd hw hold
    · split_ifs at hw with hc
      · obtain ⟨rfl, rfl, hlast⟩ := hc
        simp only [Option.some.injEq] at hw
        subst hw
        refine Or.inl ?_
        by_cases hyx : y = x
        · subst hyx; simp
        · obtain ⟨-, hord, -, hyy⟩ := I.ph1_loc a.proc j (Or.inr hpc)
          have hmem : y ∈ (s.loc a.proc).ord.take j := by
            have hj : j + 1 = (s.loc a.proc).ord.length := by
              have := (List.getElem?_eq_some_iff.1 hx).1; omega
            have h1 : y ∈ (s.loc a.proc).ord := by rw [hord]; exact mem_ordOf _ y
            rw [← List.take_length (l := (s.loc a.proc).ord), ← hj,
              take_succ_of_getElem? hx] at h1
            simpa [hyx] using h1
          have h2 := I.acR_mono h _ _ _ _ _ ((hyy y).1 hmem)
          simpa [Function.update_of_ne hyx] using h2
      · exact absurd hw hold

theorem InvA.acR_le_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j tw, s'.acR r b y j = some tw → r ≤ (s'.loc j).r := by
  intro r b y j tw hw
  have hm := r_mono h (fun i => (I.init_r i).1) j
  by_cases hold : s.acR r b y j = some tw
  · exact (I.acR_le _ _ _ _ _ hold).trans hm
  · obtain ⟨rfl, rfl, -⟩ := I.acR_new h hw hold
    exact hm

theorem InvA.acI_le_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r b y j w, s'.acI r b y j = some w → r ≤ (s'.loc j).r := by
  intro r b y j w hw
  have hm := r_mono h (fun i => (I.init_r i).1) j
  by_cases hold : s.acI r b y j = some w
  · exact (I.acI_le _ _ _ _ _ hold).trans hm
  · obtain ⟨rfl, rfl, -⟩ := I.acI_new h hw hold
    exact hm

theorem InvA.scI_le_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r j u, s'.scI r j = some u → r ≤ (s'.loc j).r := by
  intro r j u hw
  have hm := r_mono h (fun i => (I.init_r i).1) j
  by_cases hold : s.scI r j = some u
  · exact (I.scI_le _ _ _ hold).trans hm
  · obtain ⟨rfl, rfl, -⟩ := I.scI_new h hw hold
    exact hm

theorem InvA.opRec_le_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ r m j w, s'.opRec r m j = some w → 1 ≤ r ∧ r ≤ (s'.loc j).r := by
  intro r m j w hw
  have hm := r_mono h (fun i => (I.init_r i).1) j
  by_cases hold : s.opRec r m j = some w
  · obtain ⟨h1, h2⟩ := I.opRec_le _ _ _ _ hold
    exact ⟨h1, h2.trans hm⟩
  · obtain ⟨rfl, hc⟩ := I.opRec_new h hw hold
    have hr := r_post h
    rcases hc with ⟨hpc, rfl, -⟩ | ⟨hpc, rfl, -⟩
    · simp [hpc] at hr; omega
    · simp [hpc] at hr; omega

theorem InvA.ca_n1_step (I : InvA M s) (h : stepFn M s a = some s') :
    ∀ i m, ((s'.loc i).pc = .n1Inv m ∨ (s'.loc i).pc = .n1Resp m) → M.ca = true := by
  intro i m hm'
  by_cases hi : i = a.proc
  · subst hi
    du_step_cases h <;> simp only [tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc, tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc, tUpdAdopt_loc, tWrite_loc, Function.update_self] at hm' <;>
      first
      | exact I.ca_n1 _ _ (Or.inl hpc)
      | exact I.ca_n1 _ _ (Or.inr hpc)
      | (unfold startPC at hm'; split_ifs at hm' with hc <;> simp_all)
      | (split_ifs at hm' with hc <;> unfold afterN1 at hm' <;> (try split_ifs at hm') <;>
          simp_all)
      | simp at hm'
      | (split_ifs at hm' <;> simp at hm')
      | (unfold updPC at hm'; split_ifs at hm' <;> simp at hm')
  · rw [loc_ne h hi] at hm'
    exact I.ca_n1 i m hm'

end Steps

end Podc.DistributedUniversality
