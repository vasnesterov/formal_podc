import Papers.PODC2019.CryptoConsensusNumber.Fig3Defs

/-!
# Figure 3: the memory invariant

`MInv C K`: an invariant of reachable configurations of Figure 3 that does not mention the
history. `K` is a ghost set: the transfer tuples created so far (a tuple is created when its
originator invokes the transfer and passes the ownership test of line 1).

Per process (`PInv`): program-counter bookkeeping, `hist_p = AS[p]` (plus the pending decision
before line 11), `committed_a` = the tuples decided in the rounds `< round_a`, `AS[p]` contains
exactly the decisions of the rounds `p` went through, etc. Globally: the number of invocations
of `kC_a[r]` is the number of processes that went through round `r` of account `a` (all owners
of `a`), the first proposal is decided, a tuple is decided in at most one round.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct]

/-! ## Program-counter projections -/

/-- The transfer being executed (from the announcement on). -/
def PC.tx? : PC n Acct → Option (Tx n Acct)
  | .write tx => some tx
  | .coll tx _ _ => some tx
  | .snap tx _ => some tx
  | .prop tx _ _ => some tx
  | .upd tx _ _ => some tx
  | _ => none

/-- The transfer being executed, after it has been announced in the register. -/
def PC.posted : PC n Acct → Option (Tx n Acct)
  | .coll tx _ _ => some tx
  | .snap tx _ => some tx
  | .prop tx _ _ => some tx
  | .upd tx _ _ => some tx
  | _ => none

/-- The transfer being executed, before the loop. -/
def PC.pre : PC n Acct → Option (Tx n Acct)
  | .write tx => some tx
  | .coll tx _ _ => some tx
  | _ => none

/-- The transfer being executed and the set `collected`, in the loop. -/
def PC.loopC : PC n Acct → Option (Tx n Acct × Finset (Tx n Acct))
  | .snap tx c => some (tx, c)
  | .prop tx c _ => some (tx, c)
  | .upd tx c _ => some (tx, c)
  | _ => none

/-- The decision not yet written to `AS` (between lines 9 and 11). -/
def PC.updDec : PC n Acct → Option (Tx n Acct × Bool)
  | .upd _ _ d => d
  | _ => none

/-- The process is between lines 9 and 11 for account `a`. -/
def PC.updFor (a : Acct) : PC n Acct → Bool
  | .upd tx _ _ => decide (tx.a = a)
  | _ => false

/-- The process has invoked `kC_a[r]`. -/
def Invd (l : Loc n Acct) (a : Acct) (r : ℕ) : Prop :=
  r < l.rnd a ∨ (r = l.rnd a ∧ l.pc.updFor a = true)

instance (l : Loc n Acct) (a : Acct) (r : ℕ) : Decidable (Invd l a r) := by
  unfold Invd; infer_instance

section
variable {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ} {k : ℕ}

/-- The number of processes that invoked `kC_a[r]`. -/
def invCnt (C : Cfg μ q₀ k) (a : Acct) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun q => Invd (C.loc q) a r)).card
end

/-! ## The invariant -/

variable (μ : Acct → Finset (Fin n)) {q₀ : Acct → ℕ} {k : ℕ}

/-- Per-process part of the memory invariant. -/
structure PInv (K : Set (Tx n Acct)) (m : Mem n Acct k) (q : Fin n) (l : Loc n Acct)
    (pd : Option (ATOp (Fin n) Acct)) : Prop where
  idle : pd = none ↔ l.pc = .idle
  pendTx : ∀ tx, l.pc.tx? = some tx → pd = some (.transfer q tx.a tx.b tx.x)
  pendR : ∀ a, l.pc = .rscan a → pd = some (.read a)
  hist : l.hist = AS m q ∪ Option.toFinset l.pc.updDec
  com : ∀ a t, t ∈ l.com a ↔ ∃ r < l.rnd a, ∃ b, Dec m a r = some (t, b)
  asDec : ∀ t b, (t, b) ∈ AS m q → ∃ r < l.rnd t.a, Dec m t.a r = some (t, b)
  asAll : ∀ a r, r < l.rnd a → ∃ d, Dec m a r = some d ∧ d ∈ AS m q
  upd : ∀ tx c d, l.pc = .upd tx c d → d = Dec m tx.a (l.rnd tx.a) ∧ d.isSome
  txP : ∀ tx, l.pc.tx? = some tx → tx.p = q ∧ tx ∈ K ∧ tx.r ≤ l.rnd tx.a
  reg : ∀ tx, l.pc.posted = some tx → Reg m tx.a q = some tx
  notCom : ∀ tx, l.pc.pre = some tx → tx ∉ l.com tx.a
  coll : ∀ tx i acc, l.pc = .coll tx i acc →
    (∀ t ∈ acc, t ∈ K ∧ t.a = tx.a) ∧ (q.val < i.val → tx ∈ acc)
  loop : ∀ tx c, l.pc.loopC = some (tx, c) →
    tx ∈ c ∧ ∀ t ∈ c, t ∈ K ∧ t.a = tx.a ∧ t ∉ l.com tx.a
  prop : ∀ tx c pr, l.pc = .prop tx c pr → pr.1 ∈ c ∧ ∀ t ∈ c, pr.1.key ≤ t.key
  kCur : ∀ t ∈ K, t.p = q → l.pc.tx? = some t ∨ t ∈ l.com t.a
  kRnd : ∀ t ∈ K, t.p = q → l.pc.tx? = some t ∨ t.r < l.rnd t.a
  invdMem : ∀ a r, Invd l a r → q ∈ μ a

/-- The memory invariant. -/
structure MInv (C : Cfg μ q₀ k) (K : Set (Tx n Acct)) : Prop where
  proc : ∀ q, PInv μ K C.mem q (C.loc q) (C.pend q)
  kInj : ∀ t ∈ K, ∀ t' ∈ K, t.a = t'.a → t.p = t'.p → t.r = t'.r → t = t'
  kOwn : ∀ t ∈ K, t.p ∈ μ t.a
  regK : ∀ a i t, Reg C.mem a i = some t → t ∈ K ∧ t.a = a ∧ t.p = i
  cnt : ∀ a r, (KC C.mem a r).2 = invCnt C a r
  kcNone : ∀ a r, Dec C.mem a r = none ↔ (KC C.mem a r).2 = 0
  decK : ∀ a r t b, Dec C.mem a r = some (t, b) → t ∈ K ∧ t.a = a
  decUniq : ∀ a r r' t b b', Dec C.mem a r = some (t, b) → Dec C.mem a r' = some (t, b') → r = r'

variable {μ}

/-! ## Frame lemma -/

/-- `m'` extends the decisions of `m`. -/
def DecExt (m m' : Mem n Acct k) : Prop := ∀ a r d, Dec m a r = some d → Dec m' a r = some d

lemma PInv.frame {K K' : Set (Tx n Acct)} {m m' : Mem n Acct k} {q : Fin n} {l : Loc n Acct}
    {pd : Option (ATOp (Fin n) Acct)} (h : PInv μ K m q l pd)
    (hAS : AS m' q = AS m q) (hReg : ∀ a, Reg m' a q = Reg m a q) (hDec : DecExt m m')
    (hK : K ⊆ K') (hK' : ∀ t ∈ K', t.p = q → t ∈ K) : PInv μ K' m' q l pd where
  idle := h.idle
  pendTx := h.pendTx
  pendR := h.pendR
  hist := by rw [hAS]; exact h.hist
  com a t := by
    rw [h.com]
    constructor
    · rintro ⟨r, hr, b, hd⟩; exact ⟨r, hr, b, hDec _ _ _ hd⟩
    · rintro ⟨r, hr, b, hd⟩
      obtain ⟨d, hd', -⟩ := h.asAll a r hr
      rw [hDec _ _ _ hd'] at hd
      exact ⟨r, hr, b, hd ▸ hd'⟩
  asDec t b hm := by
    rw [hAS] at hm
    obtain ⟨r, hr, hd⟩ := h.asDec t b hm
    exact ⟨r, hr, hDec _ _ _ hd⟩
  asAll a r hr := by
    obtain ⟨d, hd, hm⟩ := h.asAll a r hr
    exact ⟨d, hDec _ _ _ hd, by rw [hAS]; exact hm⟩
  upd tx c d hpc := by
    obtain ⟨h1, h2⟩ := h.upd tx c d hpc
    refine ⟨?_, h2⟩
    obtain ⟨d', rfl⟩ := Option.isSome_iff_exists.1 h2
    rw [hDec _ _ _ h1.symm]
  txP tx htx := by
    obtain ⟨h1, h2, h3⟩ := h.txP tx htx; exact ⟨h1, hK h2, h3⟩
  reg tx htx := by rw [hReg]; exact h.reg tx htx
  notCom := h.notCom
  coll tx i acc hpc := by
    obtain ⟨h1, h2⟩ := h.coll tx i acc hpc
    exact ⟨fun t ht => ⟨hK (h1 t ht).1, (h1 t ht).2⟩, h2⟩
  loop tx c hpc := by
    obtain ⟨h1, h2⟩ := h.loop tx c hpc
    exact ⟨h1, fun t ht => ⟨hK (h2 t ht).1, (h2 t ht).2⟩⟩
  prop := h.prop
  kCur t ht htp := h.kCur t (hK' t ht htp) htp
  kRnd t ht htp := h.kRnd t (hK' t ht htp) htp
  invdMem := h.invdMem

lemma DecExt.refl (m : Mem n Acct k) : DecExt m m := fun _ _ _ h => h

/-- Assembling the invariant after a step of `q`. -/
lemma MInv.of_step {C : Cfg μ q₀ k} {K K' : Set (Tx n Acct)} (hI : MInv μ C K) (q : Fin n)
    (l' : Loc n Acct) (pd' : Option (ATOp (Fin n) Acct)) (m' : Mem n Acct k)
    (hq : PInv μ K' m' q l' pd')
    (hAS : ∀ q', q' ≠ q → AS m' q' = AS C.mem q')
    (hReg : ∀ q', q' ≠ q → ∀ a, Reg m' a q' = Reg C.mem a q') (hDec : DecExt C.mem m')
    (hK : K ⊆ K') (hK' : ∀ t ∈ K', t.p ≠ q → t ∈ K)
    (kInj : ∀ t ∈ K', ∀ t' ∈ K', t.a = t'.a → t.p = t'.p → t.r = t'.r → t = t')
    (kOwn : ∀ t ∈ K', t.p ∈ μ t.a)
    (regK : ∀ a i t, Reg m' a i = some t → t ∈ K' ∧ t.a = a ∧ t.p = i)
    (hcnt : ∀ a r, (KC m' a r).2 =
      (Finset.univ.filter (fun q'' => Invd (Function.update C.loc q l' q'') a r)).card)
    (kcNone : ∀ a r, Dec m' a r = none ↔ (KC m' a r).2 = 0)
    (decK : ∀ a r t b, Dec m' a r = some (t, b) → t ∈ K' ∧ t.a = a)
    (decUniq : ∀ a r r' t b b', Dec m' a r = some (t, b) → Dec m' a r' = some (t, b') → r = r') :
    MInv μ (⟨Function.update C.loc q l', Function.update C.pend q pd', m'⟩ : Cfg μ q₀ k) K' where
  proc q' := by
    by_cases hq' : q' = q
    · subst hq'; simpa using hq
    · simp only [Function.update_of_ne hq']
      exact (hI.proc q').frame (hAS q' hq') (hReg q' hq') hDec hK
        (fun t ht htp => hK' t ht (htp ▸ hq'))
  kInj := kInj
  kOwn := kOwn
  regK := regK
  cnt := hcnt
  kcNone := kcNone
  decK := decK
  decUniq := decUniq

/-! ## Initial configuration -/

lemma MInv.init : MInv μ (impl μ q₀ k).initCfg ∅ where
  proc q := {
    idle := by simp [Impl.initCfg, impl]
    pendTx := by simp [Impl.initCfg, impl, PC.tx?]
    pendR := by simp [Impl.initCfg, impl]
    hist := by simp [Impl.initCfg, impl, AS, memInit, PC.updDec]
    com := by simp [Impl.initCfg, impl]
    asDec := by simp [Impl.initCfg, impl, AS, memInit]
    asAll := by simp [Impl.initCfg, impl]
    upd := by simp [Impl.initCfg, impl]
    txP := by simp [Impl.initCfg, impl, PC.tx?]
    reg := by simp [Impl.initCfg, impl, PC.posted]
    notCom := by simp [Impl.initCfg, impl, PC.pre]
    coll := by simp [Impl.initCfg, impl]
    loop := by simp [Impl.initCfg, impl, PC.loopC]
    prop := by simp [Impl.initCfg, impl]
    kCur := by simp
    kRnd := by simp
    invdMem := by simp [Impl.initCfg, impl, Invd, PC.updFor] }
  kInj := by simp
  kOwn := by simp
  regK := by simp [Impl.initCfg, impl, Reg, memInit]
  cnt := by simp [Impl.initCfg, impl, KC, memInit, invCnt, Invd, PC.updFor]
  kcNone := by simp [Impl.initCfg, impl, KC, Dec, memInit]
  decK := by simp [Impl.initCfg, impl, KC, Dec, memInit]
  decUniq := by simp [Impl.initCfg, impl, KC, Dec, memInit]

/-! ## Derived facts -/

lemma mem_succ {S : Fin n → Hist n Acct} {t : Tx n Acct} : t ∈ succ S ↔ ∃ q, (t, true) ∈ S q := by
  simp [succ]

lemma mem_U {m : Mem n Acct k} {t : Tx n Acct} : t ∈ U m ↔ ∃ q, (t, true) ∈ AS m q := mem_succ

section Derived

variable {C : Cfg μ q₀ k} {K : Set (Tx n Acct)}

/-- If `kC_a[r]` is decided, all earlier rounds are decided and their decisions are in `AS`. -/
lemma MInv.dec_lt (hI : MInv μ C K) {a : Acct} {r r' : ℕ} (hr : Dec C.mem a r ≠ none)
    (hr' : r' < r) : ∃ q d, Dec C.mem a r' = some d ∧ d ∈ AS C.mem q := by
  have h1 : (KC C.mem a r).2 ≠ 0 := fun h => hr ((hI.kcNone a r).2 h)
  rw [hI.cnt, invCnt, Finset.card_ne_zero] at h1
  obtain ⟨q, hq⟩ := h1
  have hq' : Invd (C.loc q) a r := by simpa using hq
  have : r' < (C.loc q).rnd a := by unfold Invd at hq'; omega
  obtain ⟨d, hd, hm⟩ := (hI.proc q).asAll a r' this
  exact ⟨q, d, hd, hm⟩

lemma MInv.dec_lt_ne (hI : MInv μ C K) {a : Acct} {r r' : ℕ} (hr : Dec C.mem a r ≠ none)
    (hr' : r' ≤ r) : Dec C.mem a r' ≠ none := by
  rcases hr'.lt_or_eq with h | rfl
  · obtain ⟨q, d, hd, -⟩ := hI.dec_lt hr h; simp [hd]
  · exact hr

/-- Successful transfers recorded in `AS` are decided. -/
lemma MInv.dec_of_AS (hI : MInv μ C K) {q : Fin n} {t : Tx n Acct} {b : Bool}
    (h : (t, b) ∈ AS C.mem q) : ∃ r, Dec C.mem t.a r = some (t, b) := by
  obtain ⟨r, -, hr⟩ := (hI.proc q).asDec t b h
  exact ⟨r, hr⟩

lemma MInv.dec_of_U (hI : MInv μ C K) {t : Tx n Acct} (h : t ∈ U C.mem) :
    ∃ r, Dec C.mem t.a r = some (t, true) := by
  obtain ⟨q, hq⟩ := mem_U.1 h
  exact hI.dec_of_AS hq

/-- A tuple is decided with one result only. -/
lemma MInv.dec_res (hI : MInv μ C K) {a : Acct} {r r' : ℕ} {t : Tx n Acct} {b b' : Bool}
    (h : Dec C.mem a r = some (t, b)) (h' : Dec C.mem a r' = some (t, b')) : b = b' := by
  have := hI.decUniq a r r' t b b' h h'
  subst this
  rw [h] at h'
  cases h'; rfl

/-- In the loop, a collected tuple is undecided as long as the current round is undecided. -/
lemma MInv.undec_of_loop (hI : MInv μ C K) {q : Fin n} {tx t : Tx n Acct}
    {c : Finset (Tx n Acct)} (hpc : (C.loc q).pc.loopC = some (tx, c)) (ht : t ∈ c)
    (hund : Dec C.mem tx.a ((C.loc q).rnd tx.a) = none) (r : ℕ) (b : Bool) :
    Dec C.mem t.a r ≠ some (t, b) := by
  intro hd
  obtain ⟨-, hc⟩ := (hI.proc q).loop tx c hpc
  obtain ⟨-, hta, hcom⟩ := hc t ht
  rw [hta] at hd
  rcases lt_trichotomy r ((C.loc q).rnd tx.a) with h | h | h
  · exact hcom (((hI.proc q).com tx.a t).2 ⟨r, h, b, hd⟩)
  · rw [h, hund] at hd; cases hd
  · exact hI.dec_lt_ne (by rw [hd]; simp) h.le hund

end Derived

end CryptoCons.Fig3
