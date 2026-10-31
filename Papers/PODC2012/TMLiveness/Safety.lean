import Papers.PODC2012.TMLiveness.Model

-- CSLib candidate: Cslib/Computability/Distributed/TransactionalMemory/Safety.lean

/-!
# Safety properties of a TM: strict serializability and opacity (§2.4)

A finite history `h` is

* **strictly serializable** if there is a sequence `σ` of transactions — all committed ones and
  some commit-pending ones (which are then regarded as committed) — that respects the real-time
  order of `h` and in which every transaction is legal;
* **opaque** if there is a sequence `σ` of *all* transactions of `h`, where every commit-pending
  transaction is completed by a commit or an abort and every live transaction by an abort, that
  respects the real-time order of `h` and in which every transaction is legal.

A sequence `σ` of transactions is the paper's sequential history `H_s` (a sequential history
equivalent to `h` is a concatenation of its transactions in some order). Legality is the
sequential specification of read/write t-variables: a transaction reads, for each `x`, its own
last write to `x` if any, and otherwise the value written to `x` by the last preceding committed
transaction (or the initial value). Aborted transactions are checked but their writes are
discarded.

We also prove the basic facts on transaction bookkeeping used later: every reachable history is
well formed (`WF`), the real-time order can be read off the `snap` field (`prec_of_snap`), opacity
implies strict serializability (`EnsuresSafety.ss_of_opaque`), and the key combinatorial fact
behind the impossibility proofs: a configuration of transactions that cannot be legally
serialized (`conflict_seq`, `not_ss_of_conflict`).
-/

namespace Podc.TMLiveness

variable {P X V : Type*}

/-! ### Sequential specification -/

section Legal

variable [DecidableEq X] [DecidableEq V]

/-- Run the reads and writes of a transaction from the store `s`: reads must return the current
value (the transaction's own last write, or the store), writes update it. `none` if some read is
illegal. -/
def runOps (s : X → V) : List (Op X V) → Option (X → V)
  | [] => some s
  | .read y v :: l => if s y = v then runOps s l else none
  | .write y v :: l => runOps (Function.update s y v) l

/-- The last value a list of operations writes to `x`, if any. -/
def lastWrite (x : X) : List (Op X V) → Option V
  | [] => none
  | .read _ _ :: l => lastWrite x l
  | .write y v :: l => (lastWrite x l).or (if y = x then some v else none)

/-- The value a sequence of transactions read starting from the store `s` is legal; committed
transactions (`cm t = true`) update the store. -/
def LegalSeq {T : Type*} (ops : T → List (Op X V)) (cm : T → Bool) : List T → (X → V) → Prop
  | [], _ => True
  | t :: σ, s => ∃ s', runOps s (ops t) = some s' ∧ LegalSeq ops cm σ (if cm t then s' else s)

theorem runOps_lastWrite (x : X) :
    ∀ (l : List (Op X V)) (s s' : X → V), runOps s l = some s' →
      s' x = (lastWrite x l).getD (s x)
  | [], s, s', h => by simp [runOps] at h; simp [h, lastWrite]
  | .read y v :: l, s, s', h => by
    simp only [runOps] at h
    split_ifs at h
    simpa [lastWrite] using runOps_lastWrite x l s s' h
  | .write y v :: l, s, s', h => by
    simp only [runOps] at h
    rw [runOps_lastWrite x l _ _ h, lastWrite]
    cases hl : lastWrite x l with
    | some w => simp
    | none =>
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy, Function.update_of_ne (Ne.symm hy)]

theorem runOps_read_head {x : X} {a : V} {l : List (Op X V)} {s s' : X → V}
    (h : runOps s (.read x a :: l) = some s') : s x = a := by
  simp only [runOps] at h
  split_ifs at h with h1
  exact h1

theorem LegalSeq.stores {T : Type*} {ops : T → List (Op X V)} :
    ∀ {σ : List T} {s : X → V}, LegalSeq ops (fun _ => true) σ s →
      ∃ st : ℕ → X → V, st 0 = s ∧
        ∀ i (hi : i < σ.length), runOps (st i) (ops σ[i]) = some (st (i + 1))
  | [], s, _ => ⟨fun _ => s, rfl, fun i hi => by simp at hi⟩
  | t :: σ, s, h => by
    obtain ⟨s', h1, h2⟩ := h
    simp only [ite_true] at h2
    obtain ⟨st, hst0, hst⟩ := LegalSeq.stores h2
    refine ⟨fun i => if i = 0 then s else st (i - 1), by simp, ?_⟩
    intro i hi
    cases i with
    | zero => simpa [hst0] using h1
    | succ i =>
      simp only [List.getElem_cons_succ, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
      exact hst i (by simpa using hi)

theorem stores_const {T : Type*} {ops : T → List (Op X V)} {σ : List T} {st : ℕ → X → V}
    (hst : ∀ i (hi : i < σ.length), runOps (st i) (ops σ[i]) = some (st (i + 1))) (x : X)
    {p q : ℕ} (hpq : p ≤ q) (hq : q ≤ σ.length)
    (hw : ∀ i (hi : i < σ.length), p ≤ i → i < q → lastWrite x (ops σ[i]) = none) :
    st q x = st p x := by
  induction q, hpq using Nat.le_induction with
  | base => rfl
  | succ q hpq ih =>
    have hq' : q < σ.length := by omega
    rw [runOps_lastWrite x _ _ _ (hst q hq'), hw q hq' hpq (by omega)]
    simpa using ih (by omega) (fun i hi h1 h2 => hw i hi h1 (by omega))

end Legal

/-! ### Strict serializability and opacity -/

variable [DecidableEq P] [DecidableEq X] [DecidableEq V]

/-- Strict serializability (§2.4) w.r.t. the initial values `init`. -/
def StrictlySerializable (init : X → V) (h : List (Ev P X V)) : Prop :=
  ∃ σ : List (TxId P), σ.Nodup ∧
    (∀ t ∈ σ, Committed h t ∨ CommitPending h t) ∧
    (∀ t, Committed h t → t ∈ σ) ∧
    (∀ t₁ ∈ σ, ∀ t₂ ∈ σ, Prec h t₁ t₂ → [t₁, t₂].Sublist σ) ∧
    LegalSeq (txOps h) (fun _ => true) σ init

/-- Serializability w.r.t. the initial values `init`: as strict serializability, but the sequence
only has to respect the order of the transactions of each process, not the real-time order. -/
def Serializable (init : X → V) (h : List (Ev P X V)) : Prop :=
  ∃ σ : List (TxId P), σ.Nodup ∧
    (∀ t ∈ σ, Committed h t ∨ CommitPending h t) ∧
    (∀ t, Committed h t → t ∈ σ) ∧
    (∀ k j j', (k, j) ∈ σ → (k, j') ∈ σ → j < j' → [(k, j), (k, j')].Sublist σ) ∧
    LegalSeq (txOps h) (fun _ => true) σ init

/-- Opacity (§2.4) w.r.t. the initial values `init`: `C` is the set of commit-pending transactions
completed by a commit event. -/
def Opaque (init : X → V) (h : List (Ev P X V)) : Prop :=
  ∃ (σ : List (TxId P)) (C : TxId P → Bool), σ.Nodup ∧
    (∀ t, t ∈ σ ↔ Started h t) ∧
    (∀ t, C t = true → CommitPending h t) ∧
    (∀ t₁ ∈ σ, ∀ t₂ ∈ σ, Prec h t₁ t₂ → [t₁, t₂].Sublist σ) ∧
    LegalSeq (txOps h) (fun t => (info h).committed t || C t) σ init

/-! ### Bookkeeping lemmas -/

omit [DecidableEq X] [DecidableEq V] in
@[simp] theorem info_nil : info ([] : List (Ev P X V)) = HInfo.init := rfl

omit [DecidableEq X] [DecidableEq V] in
@[simp] theorem info_append_single (h : List (Ev P X V)) (e : Ev P X V) :
    info (h ++ [e]) = (info h).step e := by
  simp [info, List.foldl_append]

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
@[simp] theorem hist_nil : hist ([] : List (Step P X V)) = [] := rfl

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
@[simp] theorem hist_append_ev (h : List (Step P X V)) (e : Ev P X V) :
    hist (h ++ [.ev e]) = hist h ++ [e] := by
  simp [hist, List.filterMap_append, Step.ev?]

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
@[simp] theorem hist_append_tau (h : List (Step P X V)) (k : P) :
    hist (h ++ [.tau k]) = hist h := by
  simp [hist, List.filterMap_append, Step.ev?]

section StepLemmas
omit [DecidableEq X] [DecidableEq V]
variable (s : HInfo P X V) (k : P) (i : Inv X V) (r : Res V)

@[simp] theorem step_inv_cnt : (s.step (.inv k i)).cnt = s.cnt := rfl
@[simp] theorem step_inv_ops : (s.step (.inv k i)).ops = s.ops := rfl
@[simp] theorem step_inv_committed : (s.step (.inv k i)).committed = s.committed := rfl
@[simp] theorem step_inv_pend : (s.step (.inv k i)).pend = Function.update s.pend k (some i) := rfl
@[simp] theorem step_inv_began (t : TxId P) :
    (s.step (.inv k i)).began t = (s.began t || decide (t = (k, s.cnt k))) := rfl
@[simp] theorem step_inv_snap (t : TxId P) :
    (s.step (.inv k i)).snap t =
      if t = (k, s.cnt k) ∧ s.began t = false then s.cnt else s.snap t := rfl
@[simp] theorem step_res_cnt :
    (s.step (.res k i r)).cnt = if r.isEnd then Function.update s.cnt k (s.cnt k + 1) else s.cnt :=
  rfl
@[simp] theorem step_res_ops (t : TxId P) : (s.step (.res k i r)).ops t =
    if t = (k, s.cnt k) then s.ops t ++ (opOf i r).toList else s.ops t := rfl
@[simp] theorem step_res_committed (t : TxId P) : (s.step (.res k i r)).committed t =
    (s.committed t || (decide (t = (k, s.cnt k)) && r.isCommit)) := rfl
@[simp] theorem step_res_pend : (s.step (.res k i r)).pend = Function.update s.pend k none := rfl
@[simp] theorem step_res_began : (s.step (.res k i r)).began = s.began := rfl
@[simp] theorem step_res_snap : (s.step (.res k i r)).snap = s.snap := rfl

end StepLemmas

omit [DecidableEq X] [DecidableEq V] in
/-- The prefix of `h` before the first event of a begun transaction `t`: its completed
transactions are recorded in `snap t`. -/
theorem exists_prefix_of_began :
    ∀ (h : List (Ev P X V)) (t : TxId P), (info h).began t = true →
      ∃ u v, h = u ++ v ∧ (info u).began t = false ∧ (info u).cnt = (info h).snap t := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro t ht; simp [HInfo.init] at ht
  | append_singleton h e ih =>
    intro t ht
    by_cases hb : (info h).began t = true
    · obtain ⟨u, v, rfl, hu, hc⟩ := ih t hb
      refine ⟨u, v ++ [e], by simp, hu, ?_⟩
      rw [hc, info_append_single]
      cases e with
      | inv k i => simp [hb]
      | res k i r => simp
    · refine ⟨h, [e], rfl, by simpa using hb, ?_⟩
      rw [info_append_single]
      cases e with
      | inv k i =>
        simp only [info_append_single, step_inv_began, Bool.or_eq_true, decide_eq_true_eq] at ht
        have ht' : t = (k, (info h).cnt k) := ht.resolve_left hb
        have hb' : (info h).began t = false := by simpa using hb
        subst ht'
        simp [hb']
      | res k i r => simp [hb] at ht

omit [DecidableEq X] [DecidableEq V] in
/-- If `t₂` began when `t₁` was already complete, then `t₁` precedes `t₂` in real time. -/
theorem prec_of_snap {h : List (Ev P X V)} {t₁ t₂ : TxId P} (hb : Started h t₂)
    (hlt : t₁.2 < (info h).snap t₂ t₁.1) : Prec h t₁ t₂ := by
  obtain ⟨u, v, rfl, hu, hc⟩ := exists_prefix_of_began h t₂ hb
  exact ⟨u, v, rfl, by simp [Complete, hc, hlt], by simp [Started, hu], hb⟩

/-- Well-formedness invariants of the transaction information of a history. -/
structure WF (s : HInfo P X V) : Prop where
  committed_began : ∀ t, s.committed t = true → s.began t = true ∧ t.2 < s.cnt t.1
  began_snap : ∀ t, s.began t = true → s.snap t t.1 = t.2 ∧ t.2 ≤ s.cnt t.1
  pend_began : ∀ k, s.pend k ≠ none → s.began (k, s.cnt k) = true
  ops_nil : ∀ k, s.began (k, s.cnt k) = false → s.ops (k, s.cnt k) = []
  future : ∀ t, s.cnt t.1 < t.2 → s.began t = false ∧ s.ops t = [] ∧ s.committed t = false
  snap_le : ∀ t k, s.began t = true → s.snap t k ≤ s.cnt k

/-- An event that may follow: invocations by idle processes, responses to pending invocations. -/
def ValidEv (s : HInfo P X V) : Ev P X V → Prop
  | .inv k _ => s.pend k = none
  | .res k i _ => s.pend k = some i

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem WF.init : WF (HInfo.init : HInfo P X V) where
  committed_began := by simp [HInfo.init]
  began_snap := by simp [HInfo.init]
  pend_began := by simp [HInfo.init]
  ops_nil := by simp [HInfo.init]
  future := by simp [HInfo.init]
  snap_le := by simp [HInfo.init]

omit [DecidableEq X] [DecidableEq V] in
theorem WF.step {s : HInfo P X V} (hs : WF s) {e : Ev P X V} (he : ValidEv s e) :
    WF (s.step e) := by
  cases e with
  | inv k i =>
    simp only [ValidEv] at he
    constructor
    · intro t ht
      obtain ⟨h1, h2⟩ := hs.committed_began t (by simpa using ht)
      simp [h1, h2]
    · intro t ht
      simp only [step_inv_began, Bool.or_eq_true, decide_eq_true_eq] at ht
      by_cases hb : s.began t = true
      · have := hs.began_snap t hb
        simp [hb, this]
      · have ht' : t = (k, s.cnt k) := ht.resolve_left hb
        subst ht'
        simp [show s.began (k, s.cnt k) = false by simpa using hb]
    · intro k' hk'
      by_cases hkk : k' = k
      · subst hkk; simp
      · have : s.pend k' ≠ none := by simpa [Function.update_of_ne hkk] using hk'
        simp [hs.pend_began k' this]
    · intro k' hk'
      simp only [step_inv_began, step_inv_cnt, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hk'
      simpa using hs.ops_nil k' hk'.1
    · intro t ht
      have := hs.future t (by simpa using ht)
      refine ⟨?_, by simpa using this.2.1, by simpa using this.2.2⟩
      simp only [step_inv_began, this.1, Bool.false_or, decide_eq_false_iff_not]
      rintro rfl; simp at ht
    · intro t k' ht
      simp only [step_inv_began, Bool.or_eq_true, decide_eq_true_eq] at ht
      by_cases hb : s.began t = true
      · simpa [hb] using hs.snap_le t k' hb
      · have ht' : t = (k, s.cnt k) := ht.resolve_left hb
        subst ht'
        simp [show s.began (k, s.cnt k) = false by simpa using hb]
  | res k i r =>
    simp only [ValidEv] at he
    have hbk : s.began (k, s.cnt k) = true := hs.pend_began k (by simp [he])
    have hcnt : ∀ k', s.cnt k' ≤ (s.step (.res k i r)).cnt k' := by
      intro k'
      simp only [step_res_cnt]
      split_ifs
      · by_cases hkk : k' = k
        · subst hkk; simp
        · simp [Function.update_of_ne hkk]
      · exact le_rfl
    constructor
    · intro t ht
      simp only [step_res_committed, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ht
      rcases ht with ht | ⟨rfl, hr⟩
      · obtain ⟨h1, h2⟩ := hs.committed_began t ht
        exact ⟨by simpa using h1, lt_of_lt_of_le h2 (hcnt _)⟩
      · refine ⟨by simpa using hbk, ?_⟩
        cases r <;> simp_all [Res.isCommit, Res.isEnd]
    · intro t ht
      have := hs.began_snap t (by simpa using ht)
      exact ⟨by simpa using this.1, le_trans this.2 (hcnt _)⟩
    · intro k' hk'
      have hkk : k' ≠ k := by rintro rfl; simp at hk'
      have : s.pend k' ≠ none := by simpa [Function.update_of_ne hkk] using hk'
      have hc : (s.step (.res k i r)).cnt k' = s.cnt k' := by
        simp only [step_res_cnt]; split_ifs <;> simp [Function.update_of_ne hkk]
      simpa [hc] using hs.pend_began k' this
    · intro k' hk'
      by_cases hkk : k' = k
      · subst hkk
        by_cases hend : r.isEnd = true
        · have hc : (s.step (.res k' i r)).cnt k' = s.cnt k' + 1 := by simp [hend]
          rw [hc] at hk' ⊢
          have := hs.future (k', s.cnt k' + 1) (by simp)
          simp [this.2.1]
        · have hc : (s.step (.res k' i r)).cnt k' = s.cnt k' := by simp [hend]
          rw [hc] at hk'
          simp [hbk] at hk'
      · have hc : (s.step (.res k i r)).cnt k' = s.cnt k' := by
          simp only [step_res_cnt]; split_ifs <;> simp [Function.update_of_ne hkk]
        rw [hc] at hk' ⊢
        have hne : ((k', s.cnt k') : TxId P) ≠ (k, s.cnt k) := by simp [hkk]
        simp [hne, hs.ops_nil k' (by simpa using hk')]
    · intro t ht
      have ht' : s.cnt t.1 < t.2 := lt_of_le_of_lt (hcnt _) ht
      have := hs.future t ht'
      have hne : t ≠ (k, s.cnt k) := by rintro rfl; simp at ht'
      simp [this, hne]
    · intro t k' ht
      exact le_trans (by simpa using hs.snap_le t k' (by simpa using ht)) (hcnt k')

omit [DecidableEq X] [DecidableEq V] in
/-- Valid steps of a TM produce valid events. -/
theorem validEv_of_validStep {M : TM P X V} {h : List (Step P X V)} {e : Ev P X V}
    (hv : ValidStep M h (.ev e)) : ValidEv (info (hist h)) e := by
  cases e with
  | inv k i => exact hv
  | res k i r => exact hv.1

omit [DecidableEq X] [DecidableEq V] in
/-- The histories of finite executions are well formed. -/
theorem Reachable.wf {M : TM P X V} {h : List (Step P X V)} (hr : Reachable M h) :
    WF (info (hist h)) := by
  induction hr with
  | nil => exact WF.init
  | @snoc h s _ hv ih =>
    cases s with
    | ev e => simpa using ih.step (validEv_of_validStep hv)
    | tau k => simpa using ih

/-! ### Opacity implies strict serializability -/

theorem LegalSeq.filter {T : Type*} {ops : T → List (Op X V)} (cm : T → Bool) :
    ∀ {σ : List T} {s : X → V}, LegalSeq ops cm σ s → LegalSeq ops (fun _ => true) (σ.filter cm) s
  | [], _, _ => trivial
  | t :: σ, s, ⟨s', h1, h2⟩ => by
    by_cases hc : cm t = true
    · simp only [List.filter_cons, hc, ite_true] at h2 ⊢
      exact ⟨s', h1, by simpa using LegalSeq.filter cm h2⟩
    · simp only [List.filter_cons, hc] at h2 ⊢
      simpa using LegalSeq.filter cm h2

theorem ss_of_opaque {init : X → V} {h : List (Ev P X V)} (hwf : WF (info h))
    (ho : Opaque init h) : StrictlySerializable init h := by
  obtain ⟨σ, C, hnd, hmem, hC, hrt, hleg⟩ := ho
  refine ⟨σ.filter (fun t => (info h).committed t || C t), hnd.filter _, ?_, ?_, ?_,
    LegalSeq.filter _ hleg⟩
  · intro t ht
    simp only [List.mem_filter, Bool.or_eq_true] at ht
    rcases ht.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (hC t h1)
  · intro t ht
    simp only [List.mem_filter, Bool.or_eq_true]
    exact ⟨(hmem t).2 (hwf.committed_began t ht).1, Or.inl ht⟩
  · intro t₁ h₁ t₂ h₂ hp
    simp only [List.mem_filter] at h₁ h₂
    have := (hrt t₁ h₁.1 t₂ h₂.1 hp).filter (fun t => (info h).committed t || C t)
    simpa [h₁.2, h₂.2] using this

/-- A TM ensuring opacity ensures strict serializability. -/
theorem EnsuresSafety.ss_of_opaque {M : TM P X V} {init : X → V}
    (h : EnsuresSafety M (Opaque init)) : EnsuresSafety M (StrictlySerializable init) :=
  fun _ hr => Podc.TMLiveness.ss_of_opaque hr.wf (h _ hr)

/-! ### Strict serializability implies serializability -/

theorem serializable_of_ss {init : X → V} {h : List (Ev P X V)} (hwf : WF (info h))
    (hs : StrictlySerializable init h) : Serializable init h := by
  obtain ⟨σ, hnd, hmem, hcm, hrt, hleg⟩ := hs
  refine ⟨σ, hnd, hmem, hcm, fun k j j' hj hj' hlt => hrt _ hj _ hj' ?_, hleg⟩
  have hb : Started h (k, j') := by
    rcases hmem _ hj' with hc | ⟨hc, hp⟩
    · exact (hwf.committed_began _ hc).1
    · simp only at hc
      have := hwf.pend_began k (by simp [hp])
      rw [← hc] at this; exact this
  exact prec_of_snap hb (by rw [(hwf.began_snap _ hb).1]; exact hlt)

/-- A TM ensuring strict serializability ensures serializability. -/
theorem EnsuresSafety.serializable_of_ss {M : TM P X V} {init : X → V}
    (h : EnsuresSafety M (StrictlySerializable init)) : EnsuresSafety M (Serializable init) :=
  fun _ hr => Podc.TMLiveness.serializable_of_ss hr.wf (h _ hr)

/-! ### The conflict that rules out the last commit -/

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem idxOf_lt_of_sublist {T : Type*} [DecidableEq T] {a b : T} :
    ∀ {σ : List T}, [a, b].Sublist σ → σ.Nodup → a ≠ b → σ.idxOf a < σ.idxOf b
  | [], h, _, _ => by simp at h
  | c :: σ, h, hnd, hab => by
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.1 h with h' | ⟨l, hl, h'⟩
    · have ha : a ∈ σ := h'.subset (by simp)
      have hb : b ∈ σ := h'.subset (by simp)
      have hca : c ≠ a := by rintro rfl; exact hnd.1 ha
      have hcb : c ≠ b := by rintro rfl; exact hnd.1 hb
      simp only [List.idxOf_cons, beq_iff_eq, hca, hcb, ite_false]
      have := idxOf_lt_of_sublist h' hnd.2 hab
      omega
    · simp only [List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [List.idxOf_cons_self]
      simp [List.idxOf_cons, hab]

/-- **The conflict.** In a legal sequence of committed transactions, the following configuration
is impossible: `T₁` first reads `a` from `x` and last writes `b` to `x`; there is a set `Ch` of
transactions (the "chain", not containing `T₁`), each of which first reads from `x` a value
`≠ b`, with a last member `Tₗ` whose last write to `x` is `d ≠ a`; every other transaction either
does not write `x` or comes before `T₁` and before every chain member. -/
theorem conflict_seq {T : Type*} [DecidableEq T] (ops : T → List (Op X V)) {σ : List T}
    {s : X → V} (hleg : LegalSeq ops (fun _ => true) σ s) (hnd : σ.Nodup) (x : X)
    {a b d : V} {T₁ Tₗ : T} (Ch : T → Prop) (h₁ : T₁ ∈ σ) (hₗ : Tₗ ∈ σ) (hChₗ : Ch Tₗ)
    (hCh₁ : ¬ Ch T₁) (ha : ∃ r, ops T₁ = .read x a :: r) (hb : lastWrite x (ops T₁) = some b)
    (hd : lastWrite x (ops Tₗ) = some d) (hda : d ≠ a)
    (hCh : ∀ t ∈ σ, Ch t → σ.idxOf t ≤ σ.idxOf Tₗ ∧ ∃ c r, ops t = .read x c :: r ∧ c ≠ b)
    (hOth : ∀ t ∈ σ, t ≠ T₁ → ¬ Ch t →
      lastWrite x (ops t) = none ∨
        (σ.idxOf t < σ.idxOf T₁ ∧ ∀ t' ∈ σ, Ch t' → σ.idxOf t < σ.idxOf t')) :
    False := by
  classical
  obtain ⟨st, -, hst⟩ := hleg.stores
  obtain ⟨i₁, hi₁⟩ : ∃ i, σ.idxOf T₁ = i := ⟨_, rfl⟩
  obtain ⟨iₗ, hiₗ⟩ : ∃ i, σ.idxOf Tₗ = i := ⟨_, rfl⟩
  rw [hi₁] at hOth
  rw [hiₗ] at hCh
  have hi₁l : i₁ < σ.length := hi₁ ▸ List.idxOf_lt_length_iff.2 h₁
  have hiₗl : iₗ < σ.length := hiₗ ▸ List.idxOf_lt_length_iff.2 hₗ
  have hσ₁ : σ[i₁] = T₁ := by subst hi₁; exact List.getElem_idxOf hi₁l
  have hσₗ : σ[iₗ] = Tₗ := by subst hiₗ; exact List.getElem_idxOf hiₗl
  have hidx : ∀ m (hm : m < σ.length), σ.idxOf σ[m] = m := fun m hm => hnd.idxOf_getElem m hm
  -- values around `T₁` and `Tₗ`
  obtain ⟨r₁, hr₁⟩ := ha
  have hrun₁ := hst i₁ hi₁l
  rw [hσ₁] at hrun₁
  have hA : st i₁ x = a := runOps_read_head (by rw [hr₁] at hrun₁; exact hrun₁)
  have hB : st (i₁ + 1) x = b := by
    rw [runOps_lastWrite x _ _ _ hrun₁, hb]; rfl
  have hrunₗ := hst iₗ hiₗl
  rw [hσₗ] at hrunₗ
  have hD : st (iₗ + 1) x = d := by
    rw [runOps_lastWrite x _ _ _ hrunₗ, hd]; rfl
  have hne : i₁ ≠ iₗ := by
    intro h; subst h; apply hCh₁; rw [← hσ₁, hσₗ]; exact hChₗ
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `T₁` before `Tₗ`: the first chain member after `T₁` reads `b`
    have hex : ∃ m, i₁ < m ∧ ∃ hm : m < σ.length, Ch σ[m] := ⟨iₗ, hlt, hiₗl, by rwa [hσₗ]⟩
    let m := Nat.find hex
    obtain ⟨hm₁, hml, hmCh⟩ := Nat.find_spec hex
    have hmin : ∀ j, i₁ < j → j < m → ∀ hj : j < σ.length, ¬ Ch σ[j] := by
      intro j hj hjm hjl hCj
      exact Nat.find_min hex hjm ⟨hj, hjl, hCj⟩
    have hconst : st m x = st (i₁ + 1) x := by
      apply stores_const hst x (by omega) hml.le
      intro j hj h1 h2
      have hjm : ¬ Ch σ[j] := hmin j (by omega) h2 hj
      have hj1 : σ[j] ≠ T₁ := by
        intro he; have := hidx j hj; rw [he] at this; omega
      rcases hOth σ[j] (List.getElem_mem hj) hj1 hjm with hw | ⟨hw, -⟩
      · exact hw
      · rw [hidx j hj] at hw; omega
    obtain ⟨-, c, r, hc, hcb⟩ := hCh σ[m] (List.getElem_mem hml) hmCh
    have hrunm := hst m hml
    rw [hc] at hrunm
    have := runOps_read_head hrunm
    rw [hconst, hB] at this
    exact hcb this.symm
  · -- `Tₗ` before `T₁`: `T₁` reads `d`
    have hconst : st i₁ x = st (iₗ + 1) x := by
      apply stores_const hst x (by omega) hi₁l.le
      intro j hj h1 h2
      have hj1 : σ[j] ≠ T₁ := by
        intro he; have := hidx j hj; rw [he] at this; omega
      by_cases hjc : Ch σ[j]
      · have := (hCh σ[j] (List.getElem_mem hj) hjc).1
        rw [hidx j hj] at this; omega
      · rcases hOth σ[j] (List.getElem_mem hj) hj1 hjc with hw | ⟨-, hw⟩
        · exact hw
        · have := hw Tₗ hₗ hChₗ
          rw [hidx j hj, hiₗ] at this; omega
    rw [hA, hD] at hconst
    exact hda hconst.symm

/-- **The conflict in a history.** Let `T₁ = (p₁, c₁)` be committed, first read `a` from `x` and
last write `b` to `x`. Let the committed transactions of `p₂` that did not complete before `T₁`
began (those numbered `≥ j₀`) all first read from `x` a value `≠ b`, the last of them writing
`d ≠ a` to `x`. If all other committed transactions are earlier transactions of `p₂` and no
transaction is commit-pending, the history is not strictly serializable. -/
theorem not_ss_of_conflict {init : X → V} {h : List (Ev P X V)} (hwf : WF (info h)) (x : X)
    {p₁ p₂ : P} (hp : p₁ ≠ p₂) {c₁ j₀ jₗ : ℕ} {a b d : V}
    (hT₁ : Committed h (p₁, c₁)) (hj₀ : (info h).snap (p₁, c₁) p₂ = j₀)
    (ha : ∃ r, txOps h (p₁, c₁) = .read x a :: r) (hb : lastWrite x (txOps h (p₁, c₁)) = some b)
    (hcom : ∀ t, Committed h t → t = (p₁, c₁) ∨ t.1 = p₂)
    (hpend : ∀ t, ¬ CommitPending h t)
    (hread : ∀ j, j₀ ≤ j → Committed h (p₂, j) →
      ∃ c r, txOps h (p₂, j) = .read x c :: r ∧ c ≠ b)
    (hl : j₀ ≤ jₗ) (hlc : Committed h (p₂, jₗ))
    (hmax : ∀ j, j₀ ≤ j → Committed h (p₂, j) → j ≤ jₗ)
    (hd : lastWrite x (txOps h (p₂, jₗ)) = some d) (hda : d ≠ a) :
    ¬ StrictlySerializable init h := by
  rintro ⟨σ, hnd, hmem, hcm, hrt, hleg⟩
  have hstart : ∀ t, Committed h t → Started h t := fun t ht => (hwf.committed_began t ht).1
  have hsnap : ∀ t, Committed h t → (info h).snap t t.1 = t.2 :=
    fun t ht => (hwf.began_snap t (hstart t ht)).1
  have hcomσ : ∀ t ∈ σ, Committed h t := fun t ht => (hmem t ht).resolve_right (hpend t)
  -- same-process real-time order among committed transactions of `p₂`
  have hpp : ∀ j j', j < j' → Committed h (p₂, j) → Committed h (p₂, j') →
      σ.idxOf (p₂, j) < σ.idxOf (p₂, j') := by
    intro j j' hjj hj hj'
    have hpr : Prec h (p₂, j) (p₂, j') :=
      prec_of_snap (hstart _ hj') (by simpa [hsnap _ hj'] using hjj)
    exact idxOf_lt_of_sublist (hrt _ (hcm _ hj) _ (hcm _ hj') hpr) hnd
      (by simp [hjj.ne])
  refine conflict_seq (txOps h) hleg hnd x (T₁ := (p₁, c₁)) (Tₗ := (p₂, jₗ))
    (fun t => t.1 = p₂ ∧ j₀ ≤ t.2 ∧ Committed h t) (hcm _ hT₁) (hcm _ hlc) ⟨rfl, hl, hlc⟩
    (fun hc => hp hc.1) ha hb hd hda ?_ ?_
  · rintro ⟨k, j⟩ - ⟨rfl, hj, hc⟩
    refine ⟨?_, hread j hj hc⟩
    rcases (hmax j hj hc).lt_or_eq with hlt | rfl
    · exact (hpp j jₗ hlt hc hlc).le
    · exact le_rfl
  · rintro ⟨k, j⟩ ht hne hnc
    right
    have hc := hcomσ _ ht
    rcases hcom _ hc with h1 | h1
    · exact absurd h1 hne
    · simp only at h1
      subst h1
      have hj : j < j₀ := by
        by_contra hj; exact hnc ⟨rfl, by simpa using hj, hc⟩
      refine ⟨?_, ?_⟩
      · have hpr : Prec h (k, j) (p₁, c₁) :=
          prec_of_snap (hstart _ hT₁) (by simpa [hj₀] using hj)
        exact idxOf_lt_of_sublist (hrt _ ht _ (hcm _ hT₁) hpr) hnd (by simp [Ne.symm hp])
      · rintro ⟨k', j'⟩ - ⟨rfl, hj', hc'⟩
        exact hpp j j' (by simp at hj'; omega) hc hc'

/-- **The conflict in a history, for serializability.** Let `T₁ = (p₁, c₁)` be committed, first
read `a` from `x` and last write `b` to `x`. If all other committed transactions are transactions
of `p₂` that first read from `x` a value `≠ b`, the last of them writing `d ≠ a` to `x`, and no
transaction is commit-pending, the history is not serializable. -/
theorem not_serializable_of_conflict {init : X → V} {h : List (Ev P X V)} (x : X)
    {p₁ p₂ : P} (hp : p₁ ≠ p₂) {c₁ jₗ : ℕ} {a b d : V}
    (hT₁ : Committed h (p₁, c₁))
    (ha : ∃ r, txOps h (p₁, c₁) = .read x a :: r) (hb : lastWrite x (txOps h (p₁, c₁)) = some b)
    (hcom : ∀ t, Committed h t → t = (p₁, c₁) ∨ t.1 = p₂)
    (hpend : ∀ t, ¬ CommitPending h t)
    (hread : ∀ j, Committed h (p₂, j) → ∃ c r, txOps h (p₂, j) = .read x c :: r ∧ c ≠ b)
    (hlc : Committed h (p₂, jₗ)) (hmax : ∀ j, Committed h (p₂, j) → j ≤ jₗ)
    (hd : lastWrite x (txOps h (p₂, jₗ)) = some d) (hda : d ≠ a) :
    ¬ Serializable init h := by
  rintro ⟨σ, hnd, hmem, hcm, hpo, hleg⟩
  have hcomσ : ∀ t ∈ σ, Committed h t := fun t ht => (hmem t ht).resolve_right (hpend t)
  refine conflict_seq (txOps h) hleg hnd x (T₁ := (p₁, c₁)) (Tₗ := (p₂, jₗ))
    (fun t => t.1 = p₂ ∧ Committed h t) (hcm _ hT₁) (hcm _ hlc) ⟨rfl, hlc⟩
    (fun hc => hp hc.1) ha hb hd hda ?_ ?_
  · rintro ⟨k, j⟩ hj ⟨rfl, hc⟩
    refine ⟨?_, hread j hc⟩
    rcases (hmax j hc).lt_or_eq with hlt | rfl
    · exact (idxOf_lt_of_sublist (hpo _ _ _ hj (hcm _ hlc) hlt) hnd (by simp [hlt.ne])).le
    · exact le_rfl
  · intro t ht hne hnc
    rcases hcom _ (hcomσ t ht) with h1 | h1
    · exact absurd h1 hne
    · exact absurd ⟨h1, hcomσ t ht⟩ hnc

end Podc.TMLiveness
