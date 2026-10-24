import Papers.PODC2016.StorageCostLowerBounds.Model

/-!
# Theorem 4.1 (repaired): the storage lower bound without gossip

For a regular, live SWSR emulation without server gossip **in which servers do not push
messages to an idle reader** (`ReaderQuiet`), and every set `𝒩` of at least `n - f` servers,

  `|V| (|V| - 1) ≤ (∏_{i ∈ 𝒩} |S_i|) · ∑_{i ∈ 𝒩} |S_i|`        (`theorem41_count`)

which gives the paper's `∑_{𝒩} log|S_i| + max_{𝒩} log|S_i| ≥ log|V| + log(|V|-1) - log(n-f)`
(`theorem41`) and Corollary 4.2 (`corollary42`). The proof follows Section 4.3:

* `X` = the reader and the servers of `𝒩`; executions `α` in which only the writer and the
  servers of `𝒩` act (`GoodPre`). Along them the reader side is trivial, so two configurations
  agree on `X` as soon as the servers of `𝒩` have the same states (`agree_of_loc`); this is where
  `NoGossip` and `ReaderQuiet` are used (Lemma 4.8 (a)).
* `ReadExt C x` (valency, Definition 4.3): from `C`, a read by the reader, run with steps of `X`
  only (writer stopped, its messages delayed forever), returns `x`. Liveness provides such an
  extension (`exists_readExt`), with the writer crashed.
* Lemma 4.5 (`read_value`), Lemma 4.6 (critical pair), Lemma 4.8 (b) (`loc_step_ne`), Claim 4.9
  (`readExt_of_agree`, from the restriction lemma `agree_run_filter`).
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n : ℕ} {V : Type} {v₀ : V} {M L : Type}
variable (A : Algorithm (Node n) (register V v₀) M L) (𝒩 : Finset (Fin n))

/-- The reader and the servers of `𝒩`. -/
def XS (𝒩 : Finset (Fin n)) : Set (Node n) := {p | p = .rd ∨ ∃ i ∈ 𝒩, p = .srv i}

/-- Events of the writer and of the servers of `𝒩`, in the SWSR environment. -/
def GoodEv (e : Event (Node n) (register V v₀)) : Prop :=
  EvOk e ∧ (e.owner = .wr ∨ ∃ i ∈ 𝒩, e.owner = .srv i)

/-- Configurations reached by such events. -/
def GoodCfg (C : Config (Node n) (register V v₀) M L) : Prop :=
  ∃ E, (∀ e ∈ E, GoodEv 𝒩 e) ∧ C = A.run A.initCfg E

/-- **Valency** (Definition 4.3): from `C`, a read invoked at the reader and continued with
steps of the reader and the servers of `𝒩` only (no message of the writer or of the other
servers is received) returns `x`. -/
def ReadExt (C : Config (Node n) (register V v₀) M L) (x : V) : Prop :=
  ∃ F : List (Event (Node n) (register V v₀)),
    (∀ e ∈ F, e.owner ∈ XS 𝒩 ∧ ¬ e.IsInvoke ∧ ∀ q p, e = .deliver q p → q ∈ XS 𝒩) ∧
    Label.ret .rd x ∈ A.hist C (.invoke .rd RWOp.read :: F)

/-! ### Channels, local states, pending operations -/

/-- Messages enter a channel `q → p` only through steps of `q`, processing an input that is
available (a received message is in transit). -/
lemma mem_chan_step {C : Config (Node n) (register V v₀) M L} {e : Event (Node n) (register V v₀)}
    {q p : Node n} {m : M} (h : m ∈ (A.step C e).1.chan q p) :
    m ∈ C.chan q p ∨ (e.owner = q ∧ ∃ inp, (p, m) ∈ (A.handle q inp (C.loc q)).2.1 ∧
      ∀ a m', inp = .recv a m' → m' ∈ C.chan a q) := by
  have key : ∀ (C' : Config (Node n) (register V v₀) M L) (a : Node n) inp,
      C'.loc = C.loc → (∀ b m', inp = .recv b m' → m' ∈ C.chan b a) →
      m ∈ (C'.apply a (A.handle a inp (C'.loc a))).1.chan q p →
        m ∈ C'.chan q p ∨ (a = q ∧ ∃ inp, (p, m) ∈ (A.handle q inp (C.loc q)).2.1 ∧
          ∀ b m', inp = .recv b m' → m' ∈ C.chan b q) := by
    intro C' a inp hloc hinp hm
    simp only [Config.apply] at hm
    split_ifs at hm with ha
    · subst ha
      rcases List.mem_append.1 hm with hm | hm
      · exact Or.inl hm
      · right; refine ⟨rfl, inp, ?_, hinp⟩
        rw [← hloc]
        simp only [msgsTo, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
        obtain ⟨⟨b, m'⟩, ⟨h1, h2⟩, rfl⟩ := hm
        simp only at h2; subst h2; exact h1
    · exact Or.inl hm
  cases e with
  | invoke a o =>
    simp only [Algorithm.step] at h
    split at h
    · exact Or.inl h
    · rcases key _ a _ rfl (fun b m' h => by cases h) h with h | h
      · exact Or.inl h
      · exact Or.inr h
  | tick a c => exact key _ a _ rfl (fun b m' h => by cases h) h
  | deliver a b =>
    simp only [Algorithm.step] at h
    split at h
    · exact Or.inl h
    · rename_i m' rest hc
      have hpop : ∀ x, x ∈ (C.pop a b rest).chan q p → x ∈ C.chan q p := by
        intro x hx
        simp only [Config.pop] at hx
        split_ifs at hx with hab
        · obtain ⟨rfl, rfl⟩ := hab; rw [hc]; exact List.mem_cons_of_mem _ hx
        · exact hx
      rcases key (C.pop a b rest) b (.recv a m') rfl (fun b' m'' h => by
          simp only [Input.recv.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rw [hc]; simp) h with h' | h'
      · exact Or.inl (hpop m h')
      · exact Or.inr h'

variable {A 𝒩}

variable (A 𝒩) in
/-- Induction along good executions. -/
lemma good_induction (P : Config (Node n) (register V v₀) M L → Prop) (h0 : P A.initCfg)
    (hs : ∀ C e, GoodEv 𝒩 e → P C → P (A.step C e).1) {E : List (Event (Node n) (register V v₀))}
    (hE : ∀ e ∈ E, GoodEv 𝒩 e) : P (A.run A.initCfg E) := by
  induction E using List.reverseRecOn with
  | nil => exact h0
  | append_singleton E e ih =>
    rw [Algorithm.run_append]
    exact hs _ e (hE e (by simp)) (ih fun e' he' => hE e' (by simp [he']))

lemma GoodEv.owner_ne_rd {e : Event (Node n) (register V v₀)} (he : GoodEv 𝒩 e) :
    e.owner ≠ .rd := by
  intro h; rcases he.2 with h' | ⟨i, -, h'⟩ <;> rw [h] at h' <;> simp at h'

lemma GoodEv.not_invoke_srv {e : Event (Node n) (register V v₀)} (he : GoodEv 𝒩 e) (i : Fin n)
    (o : RWOp V) : e ≠ .invoke (.srv i) o := by
  rintro rfl
  rcases he.1 _ _ rfl with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h

lemma pend_step_none_of_not_invoke {C : Config (Node n) (register V v₀) M L} {p : Node n}
    (hp : C.pend p = none) {e : Event (Node n) (register V v₀)} (he : ∀ o, e ≠ .invoke p o) :
    (A.step C e).1.pend p = none := by
  by_cases ho : p = e.owner
  · cases e with
    | invoke q o => simp only [Event.owner] at ho; subst ho; exact absurd rfl (he o)
    | tick q c =>
      simp only [Event.owner] at ho; subst ho
      simp [Algorithm.step, Config.apply, hp, pendAfter]
    | deliver a q =>
      simp only [Event.owner] at ho; subst ho
      simp only [Algorithm.step]
      split
      · exact hp
      · simp [Config.apply, Config.pop, hp, pendAfter]
  · rw [pend_step_ne A C e ho]; exact hp

variable (𝒩) in
/-- Along good executions: the reader is untouched, the channels inside `XS 𝒩` stay empty and
servers have no pending operation. -/
theorem good_props (hNG : NoGossip A) (hQ : ReaderQuiet A) {E : List (Event (Node n) (register V v₀))}
    (hE : ∀ e ∈ E, GoodEv 𝒩 e) :
    (A.run A.initCfg E).loc .rd = A.init .rd ∧ (A.run A.initCfg E).pend .rd = none ∧
    (∀ x, (A.run A.initCfg E).chan .rd x = []) ∧ (∀ i, (A.run A.initCfg E).chan (.srv i) .rd = []) ∧
    (∀ i j, (A.run A.initCfg E).chan (.srv i) (.srv j) = []) ∧
    ∀ i, (A.run A.initCfg E).pend (.srv i) = none := by
  refine ⟨?_, ?_, ?_, hQ E (fun e he => (hE e he).1) (fun e he => (hE e he).owner_ne_rd), ?_, ?_⟩
  · refine good_induction A 𝒩 (fun C => C.loc .rd = A.init .rd) rfl (fun C e he h => ?_) hE
    rw [loc_step_ne A C e (Ne.symm he.owner_ne_rd)]; exact h
  · refine good_induction A 𝒩 (fun C => C.pend .rd = none) rfl (fun C e he h => ?_) hE
    rw [pend_step_ne A C e (Ne.symm he.owner_ne_rd)]; exact h
  · refine good_induction A 𝒩 (fun C => ∀ x, C.chan .rd x = []) (fun _ => rfl)
      (fun C e he h x => ?_) hE
    rw [List.eq_nil_iff_forall_not_mem]
    intro m hm
    rcases mem_chan_step A hm with hm | ⟨ho, -⟩
    · rw [h x] at hm; simp at hm
    · exact he.owner_ne_rd ho
  · refine good_induction A 𝒩 (fun C => ∀ i j, C.chan (.srv i) (.srv j) = []) (fun _ _ => rfl)
      (fun C e he h i j => ?_) hE
    rw [List.eq_nil_iff_forall_not_mem]
    intro m hm
    rcases mem_chan_step A hm with hm | ⟨-, inp, hm, -⟩
    · rw [h i j] at hm; simp at hm
    · exact hNG i inp _ _ hm j rfl
  · refine good_induction A 𝒩 (fun C => ∀ i, C.pend (.srv i) = none) (fun _ => rfl)
      (fun C e he h i => ?_) hE
    exact pend_step_none_of_not_invoke (A := A) (h i) (he.not_invoke_srv i)

variable (𝒩) in
/-- **Lemma 4.8 (a) / Claim 4.9.** Good configurations whose servers of `𝒩` have the same
states agree on `XS 𝒩`. -/
theorem agree_of_loc (hNG : NoGossip A) (hQ : ReaderQuiet A)
    {C C' : Config (Node n) (register V v₀) M L} (hC : GoodCfg A 𝒩 C) (hC' : GoodCfg A 𝒩 C')
    (hloc : ∀ i ∈ 𝒩, C.loc (.srv i) = C'.loc (.srv i)) : Agree (XS 𝒩) C C' := by
  obtain ⟨E, hE, rfl⟩ := hC
  obtain ⟨E', hE', rfl⟩ := hC'
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := good_props 𝒩 hNG hQ hE
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := good_props 𝒩 hNG hQ hE'
  refine ⟨fun p hp => ?_, fun q hq p hp => ?_⟩
  · rcases hp with rfl | ⟨i, hi, rfl⟩
    · exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
    · exact ⟨hloc i hi, (a6 i).trans (b6 i).symm⟩
  · rcases hq with rfl | ⟨i, -, rfl⟩
    · rw [a3, b3]
    · rcases hp with rfl | ⟨j, -, rfl⟩
      · rw [a4, b4]
      · rw [a5, b5]

/-- **Claim 4.9, transfer of valency.** -/
theorem readExt_of_agree {C C' : Config (Node n) (register V v₀) M L} (h : Agree (XS 𝒩) C' C)
    {x : V} (hx : ReadExt A 𝒩 C' x) : ReadExt A 𝒩 C x := by
  classical
  obtain ⟨F, hF, hret⟩ := hx
  refine ⟨F, hF, ?_⟩
  have hall : ∀ e ∈ (Event.invoke .rd RWOp.read :: F), e.owner ∈ XS 𝒩 := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact Or.inl rfl
    · exact (hF e he).1
  have hdel : ∀ q p, Event.deliver q p ∈ (Event.invoke .rd RWOp.read :: F) → p ∈ XS 𝒩 → q ∈ XS 𝒩 := by
    intro q p hm _
    rcases List.mem_cons.1 hm with h | hm
    · cases h
    · exact (hF _ hm).2.2 q p rfl
  have := (agree_run_filter A (XS 𝒩) _ hdel h).2
  rw [List.filter_eq_self.2 (fun e he => by simpa using hall e he)] at this
  rw [this, List.mem_filter]
  exact ⟨hret, by simp [XS, Label.proc]⟩

/-! ### Failure patterns and liveness -/

variable (𝒩) in
/-- Reader phase: the writer and the servers outside `𝒩` crash. -/
def fpR : FailurePattern (Node n) := ⟨{p | p = .wr ∨ ∃ i ∉ 𝒩, p = .srv i}, ∅⟩

variable (𝒩) in
/-- Writer phase: the reader and the servers outside `𝒩` crash. -/
def fpW : FailurePattern (Node n) := ⟨{p | p = .rd ∨ ∃ i ∉ 𝒩, p = .srv i}, ∅⟩

lemma srvFail_fpR : srvFail (fpR 𝒩) = 𝒩ᶜ := by ext i; simp [srvFail, fpR]
lemma srvFail_fpW : srvFail (fpW 𝒩) = 𝒩ᶜ := by ext i; simp [srvFail, fpW]

lemma card_compl_le {f : ℕ} (h : n - f ≤ 𝒩.card) : (𝒩ᶜ).card ≤ f := by
  rw [Finset.card_compl, Fintype.card_fin]; omega

lemma notMem_fpR {p : Node n} : p ∉ (fpR 𝒩).procs ↔ p ∈ XS 𝒩 := by
  rcases p with i | _ | _ <;> simp [fpR, XS]

lemma notMem_fpW {p : Node n} : p ∉ (fpW 𝒩).procs ↔ p = .wr ∨ ∃ i ∈ 𝒩, p = .srv i := by
  rcases p with i | _ | _ <;> simp [fpW]

lemma evOk_of_not_invoke {e : Event (Node n) (register V v₀)} (h : ¬ e.IsInvoke) : EvOk e := by
  rintro p o rfl; exact absurd trivial h

lemma canon_not_invoke {fp : FailurePattern (Node n)} {e : Event (Node n) (register V v₀)}
    (h : CanonEvent fp e) : ¬ e.IsInvoke := by
  cases e <;> simp_all [CanonEvent, Event.IsInvoke]

variable (A) in
/-- Liveness gives a read extension (the writer crashed, its messages never delivered). -/
theorem exists_readExt {f : ℕ} (hLive : Live A f) (hcard : n - f ≤ 𝒩.card)
    {E : List (Event (Node n) (register V v₀))} (hE : ∀ e ∈ E, EvOk e)
    (hpend : (A.run A.initCfg E).pend .rd = none) : ∃ x, ReadExt A 𝒩 (A.run A.initCfg E) x := by
  have hp₀ : (Node.rd : Node n) ∉ (fpR 𝒩).procs := by simp [fpR]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exists_canon_ret A hp₀ 0 E .rd RWOp.read
  have hret := hLive (fpR 𝒩) rfl (by rw [srvFail_fpR]; exact card_compl_le hcard) _ h3
    (fun t => by
      rcases Nat.lt_trichotomy t E.length with ht | rfl | ht
      · exact hE _ (h4 t ht)
      · rw [h1]; rintro p o he; simp only [Event.invoke.injEq] at he
        obtain ⟨rfl, rfl⟩ := he; exact Or.inr ⟨rfl, rfl⟩
      · exact evOk_of_not_invoke (canon_not_invoke (h5 t ht)))
    .rd (fun h => hp₀ h.1) E.length RWOp.read h1 (by rw [h2]; exact hpend)
  obtain ⟨F, hF, r, hr⟩ := h6 hret
  refine ⟨r, F, fun e he => ?_, hr⟩
  have hc := hF e he
  refine ⟨?_, canon_not_invoke hc, fun q p hqp => ?_⟩
  · cases e with
    | invoke => simp [CanonEvent] at hc
    | tick p c => exact notMem_fpR.1 hc
    | deliver q p => exact notMem_fpR.1 hc.2.1
  · subst hqp; exact notMem_fpR.1 hc.1

variable (A) in
/-- Liveness lets a write complete with steps of the writer and of the servers of `𝒩` only. -/
theorem exists_write {f : ℕ} (hLive : Live A f) (hcard : n - f ≤ 𝒩.card)
    {E : List (Event (Node n) (register V v₀))} (hE : ∀ e ∈ E, EvOk e)
    (hpend : (A.run A.initCfg E).pend .wr = none) (v : V) :
    ∃ F : List (Event (Node n) (register V v₀)), (∀ e ∈ F, GoodEv 𝒩 e ∧ ¬ e.IsInvoke) ∧
      ∃ r, Label.ret .wr r ∈ A.hist (A.run A.initCfg E) (.invoke .wr (RWOp.write v) :: F) := by
  have hp₀ : (Node.wr : Node n) ∉ (fpW 𝒩).procs := by simp [fpW]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := exists_canon_ret A hp₀ 0 E .wr (RWOp.write v)
  have hret := hLive (fpW 𝒩) rfl (by rw [srvFail_fpW]; exact card_compl_le hcard) _ h3
    (fun t => by
      rcases Nat.lt_trichotomy t E.length with ht | rfl | ht
      · exact hE _ (h4 t ht)
      · rw [h1]; rintro p o he; simp only [Event.invoke.injEq] at he
        obtain ⟨rfl, rfl⟩ := he; exact Or.inl ⟨rfl, v, rfl⟩
      · exact evOk_of_not_invoke (canon_not_invoke (h5 t ht)))
    .wr (fun h => hp₀ h.1) E.length (RWOp.write v) h1 (by rw [h2]; exact hpend)
  obtain ⟨F, hF, r, hr⟩ := h6 hret
  refine ⟨F, fun e he => ?_, r, hr⟩
  have hc := hF e he
  refine ⟨⟨evOk_of_not_invoke (canon_not_invoke hc), ?_⟩, canon_not_invoke hc⟩
  cases e with
  | invoke => simp [CanonEvent] at hc
  | tick p c => exact notMem_fpW.1 hc
  | deliver q p => exact notMem_fpW.1 hc.2.1

/-! ### Histories -/

lemma respsOf_pos_of_mem {h : List (Label (Node n) (register V v₀))} {p : Node n} {r : V}
    (hr : Label.ret p r ∈ h) : 0 < (respsOf h p).length := by
  apply List.length_pos_of_mem (a := r)
  simp only [respsOf, List.mem_filterMap]
  exact ⟨_, hr, by simp [Label.retOf]⟩

variable (A) in
lemma opsOf_hist_invoke {C : Config (Node n) (register V v₀) M L} {p : Node n} {o : RWOp V}
    (hp : C.pend p = none) {F : List (Event (Node n) (register V v₀))}
    (hF : ∀ e ∈ F, ¬ e.IsInvoke) (q : Node n) :
    opsOf (A.hist C (.invoke p o :: F)) q = if q = p then [o] else [] := by
  obtain ⟨r, hr, hr'⟩ := step_invoke_of_pend_none A C (o := o) hp
  rw [Algorithm.hist_cons, hr, opsOf_append, opsOf_hist_eq_nil A _ hF, List.append_nil,
    opsOf_cons]
  have : opsOf r q = [] := by
    simp only [opsOf, List.filterMap_eq_nil_iff]; exact fun l hl => hr' l hl q
  rw [this, List.append_nil]
  by_cases hq : q = p
  · subst hq; simp [Label.invOf]
  · simp [Label.invOf, Ne.symm hq, hq]

lemma opsOf_rd_good {E : List (Event (Node n) (register V v₀))} (hE : ∀ e ∈ E, GoodEv 𝒩 e) :
    opsOf (A.hist A.initCfg E) .rd = [] ∧ respsOf (A.hist A.initCfg E) .rd = [] := by
  have : ∀ l ∈ A.hist A.initCfg E, l.proc ≠ .rd := by
    intro l hl
    obtain ⟨e, he, h⟩ := proc_of_mem_hist A hl
    rw [h]; exact (hE e he).owner_ne_rd
  exact ⟨opsOf_eq_nil_of_proc_ne this, respsOf_eq_nil_of_proc_ne this⟩

/-- **Lemma 4.5** (and the regularity facts used in Lemma 4.6). A read from a good
configuration in which the first write has completed returns the value of write `m ≥ 1`; if two
writes have completed, `m ≥ 2`. -/
theorem read_value (hReg : IsRegular A) (hNG : NoGossip A) (hQ : ReaderQuiet A)
    {E : List (Event (Node n) (register V v₀))} (hE : ∀ e ∈ E, GoodEv 𝒩 e)
    (h1 : 0 < (respsOf (A.hist A.initCfg E) .wr).length) {x : V}
    (hx : ReadExt A 𝒩 (A.run A.initCfg E) x) :
    ∃ m, 1 ≤ m ∧ x = writeVal v₀ (opsOf (A.hist A.initCfg E) .wr) m ∧
      (1 < (respsOf (A.hist A.initCfg E) .wr).length → 2 ≤ m) := by
  obtain ⟨F, hF, hret⟩ := hx
  set H := A.hist A.initCfg E
  set C := A.run A.initCfg E
  set G := A.hist C (.invoke .rd RWOp.read :: F)
  have hF' : ∀ e ∈ F, ¬ e.IsInvoke := fun e he => (hF e he).2.1
  have hpr : C.pend .rd = none := (good_props 𝒩 hNG hQ hE).2.1
  have hoH : opsOf H .rd = [] := (opsOf_rd_good (A := A) hE).1
  have hrH : respsOf H .rd = [] := (opsOf_rd_good (A := A) hE).2
  have hoG := opsOf_hist_invoke A (o := RWOp.read) hpr hF'
  change ∀ q, opsOf G q = _ at hoG
  -- the read has exactly one response, `x`
  have hcnt := acc_run_counts A C (.invoke .rd RWOp.read :: F) .rd
  rw [hoG] at hcnt
  have hpc : pendCount C .rd = 0 := by simp [pendCount, hpr]
  simp only [ite_true, List.length_singleton, hpc, add_zero] at hcnt
  change 1 = (respsOf G .rd).length + _ at hcnt
  have hxG : x ∈ respsOf G .rd := by
    simp only [respsOf, List.mem_filterMap]; exact ⟨_, hret, by simp [Label.retOf]⟩
  have hGr : respsOf G .rd = [x] := by
    have hlen : (respsOf G .rd).length = 1 := by
      have := List.length_pos_of_mem hxG
      have : pendCount (A.run C (.invoke .rd RWOp.read :: F)) .rd ≤ 1 := by
        unfold pendCount; split_ifs <;> omega
      omega
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 hlen
    rw [hy] at hxG ⊢; simp at hxG; rw [hxG]
  have hEok : ∀ e ∈ E ++ (.invoke .rd RWOp.read :: F), EvOk e := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact (hE e he).1
    · rcases List.mem_cons.1 he with rfl | he
      · rintro p o h; simp only [Event.invoke.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl⟩
      · exact evOk_of_not_invoke (hF' e he)
  have hR := hReg _ hEok
  rw [Algorithm.hist_append] at hR
  change Regular v₀ (H ++ G) at hR
  have hrr : respsOf (H ++ G) .rd = [x] := by rw [respsOf_append, hrH, hGr]; rfl
  obtain ⟨m, hm1, -, hm3⟩ := hR 0 (by rw [hrr]; simp)
  have hopsw : opsOf (H ++ G) .wr = opsOf H .wr := by
    rw [opsOf_append, hoG]; simp
  rw [hopsw] at hm1
  simp only [respOf, hrr, List.getElem?_cons_zero, Option.some.injEq] at hm1
  have hprec : ∀ k, k < (respsOf H .wr).length → Precedes (H ++ G) (.wr, k) (.rd, 0) := by
    intro k hk
    exact ⟨H, G, rfl, hk, by simp [Invoked, hoH]⟩
  refine ⟨m, ?_, hm1, fun h2 => ?_⟩
  · by_contra h0
    exact hm3 (by rw [show m = 0 by omega]; exact hprec 0 h1)
  · by_contra h0
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl
    · exact hm3 (hprec 0 h1)
    · exact hm3 (hprec 1 h2)

lemma writeVal_one_write (a : V) {m : ℕ} (hm : 1 ≤ m) : writeVal v₀ [RWOp.write a] m = a := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [writeVal, ObjSpec.runOps]

lemma writeVal_two_writes (a b : V) {m : ℕ} (hm : 1 ≤ m) :
    writeVal v₀ [RWOp.write a, RWOp.write b] m = if m = 1 then a else b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases k with _ | k
  · simp [writeVal, ObjSpec.runOps]
  · simp [writeVal, ObjSpec.runOps]

lemma pend_none_of_acc {h : List (Label (Node n) (register V v₀))}
    {C : Config (Node n) (register V v₀) M L} (ha : Acc h C) {p : Node n}
    (h1 : (opsOf h p).length ≤ (respsOf h p).length) : C.pend p = none := by
  have := ha p
  unfold pendCount at this
  split_ifs at this with hc
  · simpa using hc
  · omega

/-- **Lemmas 4.4, 4.6, 4.8.** For distinct `v₁, v₂`, the execution `α^{(v₁,v₂)}` (write `v₁`, then
write `v₂`, only the writer and the servers of `𝒩` act) has a pair of critical points `C₁, C₂`:
consecutive, `C₁` is 1-valent, `C₂` is not 1-valent but some read from it returns, reads from
either return `v₁` or `v₂`, and at most the server `s ∈ 𝒩` changes its state between them. -/
theorem exists_crit {f : ℕ} (hReg : IsRegular A) (hLive : Live A f) (hNG : NoGossip A)
    (hQ : ReaderQuiet A) (hcard : n - f ≤ 𝒩.card) (hne : 𝒩.Nonempty) {v₁ v₂ : V}
    (hv : v₁ ≠ v₂) :
    ∃ (C₁ C₂ : Config (Node n) (register V v₀) M L) (s : Fin n), s ∈ 𝒩 ∧
      GoodCfg A 𝒩 C₁ ∧ GoodCfg A 𝒩 C₂ ∧ ReadExt A 𝒩 C₁ v₁ ∧ ¬ ReadExt A 𝒩 C₂ v₁ ∧
      (∃ x, ReadExt A 𝒩 C₂ x) ∧ (∀ x, ReadExt A 𝒩 C₁ x → x = v₁ ∨ x = v₂) ∧
      (∀ x, ReadExt A 𝒩 C₂ x → x = v₁ ∨ x = v₂) ∧
      ∀ j ∈ 𝒩, j ≠ s → C₂.loc (.srv j) = C₁.loc (.srv j) := by
  classical
  -- the first write
  obtain ⟨F₁, hF₁, r₁, hr₁⟩ := exists_write (𝒩 := 𝒩) A hLive hcard (E := []) (by simp) rfl v₁
  set E₁ : List (Event (Node n) (register V v₀)) := .invoke .wr (RWOp.write v₁) :: F₁
  have hgE₁ : ∀ e ∈ E₁, GoodEv 𝒩 e := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨?_, Or.inl rfl⟩
      rintro p o h; simp only [Event.invoke.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, v₁, rfl⟩
    · exact (hF₁ e he).1
  have hF₁' : ∀ e ∈ F₁, ¬ e.IsInvoke := fun e he => (hF₁ e he).2
  have hops₁ : opsOf (A.hist A.initCfg E₁) .wr = [RWOp.write v₁] := by
    have := opsOf_hist_invoke A (C := A.initCfg) (p := .wr) (o := RWOp.write v₁) rfl hF₁' .wr
    rw [ite_eq_left rfl] at this; exact this
  have hres₁ : 0 < (respsOf (A.hist A.initCfg E₁) .wr).length := respsOf_pos_of_mem hr₁
  have hpend₁ : (A.run A.initCfg E₁).pend .wr = none :=
    pend_none_of_acc (acc_hist A E₁) (by
      rw [hops₁, List.length_singleton]; exact hres₁)
  -- the second write
  obtain ⟨F₂, hF₂, r₂, hr₂⟩ := exists_write (𝒩 := 𝒩) A hLive hcard (E := E₁)
    (fun e he => (hgE₁ e he).1) hpend₁ v₂
  set L₂ : List (Event (Node n) (register V v₀)) := .invoke .wr (RWOp.write v₂) :: F₂
  have hgL₂ : ∀ e ∈ L₂, GoodEv 𝒩 e := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨?_, Or.inl rfl⟩
      rintro p o h; simp only [Event.invoke.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, v₂, rfl⟩
    · exact (hF₂ e he).1
  have hF₂' : ∀ e ∈ F₂, ¬ e.IsInvoke := fun e he => (hF₂ e he).2
  set Pt : ℕ → Config (Node n) (register V v₀) M L := fun i => A.run A.initCfg (E₁ ++ L₂.take i)
  have hgood : ∀ i, ∀ e ∈ E₁ ++ L₂.take i, GoodEv 𝒩 e := by
    intro i e he
    rcases List.mem_append.1 he with he | he
    · exact hgE₁ e he
    · exact hgL₂ e (List.mem_of_mem_take he)
  have hH : ∀ i, A.hist A.initCfg (E₁ ++ L₂.take i) =
      A.hist A.initCfg E₁ ++ A.hist (A.run A.initCfg E₁) (L₂.take i) :=
    fun i => Algorithm.hist_append _ _ _ _
  have hopsP : ∀ i, opsOf (A.hist A.initCfg (E₁ ++ L₂.take i)) .wr =
      if i = 0 then [RWOp.write v₁] else [RWOp.write v₁, RWOp.write v₂] := by
    intro i
    rw [hH, opsOf_append, hops₁]
    rcases i with _ | i
    · simp
    · have hF : ∀ e ∈ F₂.take i, ¬ e.IsInvoke := fun e he => hF₂' e (List.mem_of_mem_take he)
      have := opsOf_hist_invoke A (o := RWOp.write v₂) hpend₁ hF .wr
      simp only [L₂, List.take_succ_cons]
      rw [this]; simp
  have hresP : ∀ i, 0 < (respsOf (A.hist A.initCfg (E₁ ++ L₂.take i)) .wr).length := by
    intro i; rw [hH, respsOf_append, List.length_append]; omega
  have hres2 : 1 < (respsOf (A.hist A.initCfg (E₁ ++ L₂.take L₂.length)) .wr).length := by
    rw [hH, respsOf_append, List.length_append, List.take_length]
    have := respsOf_pos_of_mem hr₂
    omega
  -- values of reads at the points
  have hval : ∀ i x, ReadExt A 𝒩 (Pt i) x → x = v₁ ∨ x = v₂ := by
    intro i x hx
    obtain ⟨m, hm1, hm2, -⟩ := read_value hReg hNG hQ (hgood i) (hresP i) hx
    rw [hopsP] at hm2
    split_ifs at hm2
    · exact Or.inl (hm2.trans (writeVal_one_write v₁ hm1))
    · rw [writeVal_two_writes v₁ v₂ hm1] at hm2
      split_ifs at hm2
      · exact Or.inl hm2
      · exact Or.inr hm2
  have hP0 : ReadExt A 𝒩 (Pt 0) v₁ := by
    obtain ⟨x, hx⟩ := exists_readExt (𝒩 := 𝒩) A hLive hcard
      (E := E₁ ++ L₂.take 0) (fun e he => (hgood 0 e he).1) (good_props 𝒩 hNG hQ (hgood 0)).2.1
    obtain ⟨m, hm1, hm2, -⟩ := read_value hReg hNG hQ (hgood 0) (hresP 0) hx
    rw [hopsP, ite_eq_left rfl, writeVal_one_write v₁ hm1] at hm2
    rwa [hm2] at hx
  have hPM : ¬ ReadExt A 𝒩 (Pt L₂.length) v₁ := by
    intro hx
    obtain ⟨m, hm1, hm2, hm3⟩ := read_value hReg hNG hQ (hgood _) (hresP _) hx
    have hm := hm3 hres2
    rw [hopsP, ite_eq_right (by simp [L₂]), writeVal_two_writes v₁ v₂ hm1, ite_eq_right (by omega)] at hm2
    exact hv hm2
  -- the critical index
  have hex : ∃ j, ¬ ReadExt A 𝒩 (Pt j) v₁ := ⟨_, hPM⟩
  set j₀ := Nat.find hex
  have hj₀ : ¬ ReadExt A 𝒩 (Pt j₀) v₁ := Nat.find_spec hex
  have hj₀M : j₀ ≤ L₂.length := Nat.find_min' hex hPM
  have hj₀0 : j₀ ≠ 0 := fun h => hj₀ (by rw [h]; exact hP0)
  obtain ⟨i, hi⟩ : ∃ i, j₀ = i + 1 := ⟨j₀ - 1, by omega⟩
  have hPi : ReadExt A 𝒩 (Pt i) v₁ := by
    by_contra h; exact Nat.find_min hex (show i < j₀ by omega) h
  have hiL : i < L₂.length := by omega
  set e := L₂[i]
  have hstep : Pt (i + 1) = (A.step (Pt i) e).1 := by
    simp only [Pt, List.take_succ_eq_append_getElem hiL, ← List.append_assoc,
      Algorithm.run_append, Algorithm.run_cons, Algorithm.run_nil, e]
  have hge : GoodEv 𝒩 e := hgL₂ e (List.getElem_mem _)
  set s : Fin n := if h : ∃ s ∈ 𝒩, e.owner = .srv s then h.choose else hne.choose
  have hs : s ∈ 𝒩 := by
    simp only [s]; split_ifs with h
    · exact h.choose_spec.1
    · exact hne.choose_spec
  refine ⟨Pt i, Pt (i + 1), s, hs, ⟨_, hgood i, rfl⟩, ⟨_, hgood (i + 1), rfl⟩, hPi,
    by rw [← hi]; exact hj₀, ?_, hval i, hval (i + 1), fun j hj hjs => ?_⟩
  · exact exists_readExt (𝒩 := 𝒩) A hLive hcard (E := E₁ ++ L₂.take (i + 1))
      (fun e he => (hgood _ e he).1) (good_props 𝒩 hNG hQ (hgood _)).2.1
  · rw [hstep]
    apply loc_step_ne
    intro hown
    rcases hge.2 with h | ⟨s', hs', h⟩
    · rw [h] at hown; simp at hown
    · rw [h] at hown
      simp only [Node.srv.injEq] at hown
      subst hown
      apply hjs
      have hex' : ∃ s ∈ 𝒩, e.owner = .srv s := ⟨_, hs', h⟩
      simp only [s, dite_eq_left hex']
      exact Node.srv.inj (h.symm.trans hex'.choose_spec.2)

/-! ### The counting argument -/

lemma loc_mem_of_goodCfg {S : Fin n → Finset L} (hS : StateBound A S)
    {C : Config (Node n) (register V v₀) M L} (hC : GoodCfg A 𝒩 C) (i : Fin n) :
    C.loc (.srv i) ∈ S i := by
  obtain ⟨E, hE, rfl⟩ := hC
  exact hS E (fun e he => (hE e he).1) i

/-- **Theorem 4.1, counting form** (repaired: with `ReaderQuiet`). For every set `𝒩` of at least
`n - f` servers, `|V| (|V| - 1) ≤ (∏_{i ∈ 𝒩} |S_i|) · ∑_{i ∈ 𝒩} |S_i|`. -/
theorem theorem41_count [Fintype V] {f : ℕ} (hReg : IsRegular A) (hLive : Live A f)
    (hNG : NoGossip A) (hQ : ReaderQuiet A) {S : Fin n → Finset L} (hS : StateBound A S)
    (hcard : n - f ≤ 𝒩.card) (hne : 𝒩.Nonempty) :
    Fintype.card V * (Fintype.card V - 1) ≤ (∏ i ∈ 𝒩, (S i).card) * ∑ i ∈ 𝒩, (S i).card := by
  classical
  have hcrit : ∀ p : V × V, ∃ (C₁ C₂ : Config (Node n) (register V v₀) M L) (s : Fin n),
      p.1 ≠ p.2 → (s ∈ 𝒩 ∧
      GoodCfg A 𝒩 C₁ ∧ GoodCfg A 𝒩 C₂ ∧ ReadExt A 𝒩 C₁ p.1 ∧ ¬ ReadExt A 𝒩 C₂ p.1 ∧
      (∃ x, ReadExt A 𝒩 C₂ x) ∧ (∀ x, ReadExt A 𝒩 C₁ x → x = p.1 ∨ x = p.2) ∧
      (∀ x, ReadExt A 𝒩 C₂ x → x = p.1 ∨ x = p.2) ∧
      ∀ j ∈ 𝒩, j ≠ s → C₂.loc (.srv j) = C₁.loc (.srv j)) := by
    intro p
    by_cases h : p.1 = p.2
    · exact ⟨A.initCfg, A.initCfg, hne.choose, fun h' => absurd h h'⟩
    · obtain ⟨C₁, C₂, s, hh⟩ := exists_crit (A := A) (𝒩 := 𝒩) hReg hLive hNG hQ hcard hne h
      exact ⟨C₁, C₂, s, fun _ => hh⟩
  choose c₁ c₂ sv hc using hcrit
  let σ : V × V → (𝒩 → L) × (Σ _ : Fin n, L) := fun p =>
    (fun j => (c₁ p).loc (.srv j), ⟨sv p, (c₂ p).loc (.srv (sv p))⟩)
  let T : Finset ((𝒩 → L) × (Σ _ : Fin n, L)) :=
    (Fintype.piFinset fun j : 𝒩 => S j) ×ˢ (𝒩.sigma fun i => S i)
  have hT : T.card = (∏ i ∈ 𝒩, (S i).card) * ∑ i ∈ 𝒩, (S i).card := by
    simp only [T, Finset.card_product, Fintype.card_piFinset, Finset.card_sigma]
    rw [Finset.prod_coe_sort 𝒩 (fun i => (S i).card)]
  have hU : (Finset.univ : Finset V).offDiag.card = Fintype.card V * (Fintype.card V - 1) := by
    rw [Finset.offDiag_card, Finset.card_univ, Nat.mul_sub_one]
  rw [← hU, ← hT]
  refine Finset.card_le_card_of_injOn σ (fun p hp => ?_) (fun p hp p' hp' hpp' => ?_)
  · have hp' : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
    obtain ⟨hs, h1, h2, -⟩ := hc p hp'
    refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun j => ?_, Finset.mem_sigma.2 ⟨hs, ?_⟩⟩
    · exact loc_mem_of_goodCfg hS h1 j
    · exact loc_mem_of_goodCfg hS h2 _
  · have hpd : p.1 ≠ p.2 := (Finset.mem_offDiag.1 (Finset.mem_coe.1 hp)).2.2
    have hpd' : p'.1 ≠ p'.2 := (Finset.mem_offDiag.1 (Finset.mem_coe.1 hp')).2.2
    obtain ⟨hs, hg1, hg2, hP1, hnP2, hex2, hv1, hv2, hloc⟩ := hc p hpd
    obtain ⟨hs', hg1', hg2', hP1', hnP2', hex2', hv1', hv2', hloc'⟩ := hc p' hpd'
    simp only [σ, Prod.mk.injEq, Sigma.mk.injEq] at hpp'
    obtain ⟨hg, hss, hl⟩ := hpp'
    have hl' : (c₂ p).loc (.srv (sv p)) = (c₂ p').loc (.srv (sv p')) := eq_of_heq hl
    have hA1 : Agree (XS 𝒩) (c₁ p') (c₁ p) :=
      agree_of_loc 𝒩 hNG hQ hg1' hg1 (fun i hi => (congrFun hg ⟨i, hi⟩).symm)
    have hA2 : Agree (XS 𝒩) (c₂ p') (c₂ p) := by
      refine agree_of_loc 𝒩 hNG hQ hg2' hg2 (fun i hi => ?_)
      by_cases his : i = sv p
      · subst his; rw [hl', hss]
      · rw [hloc i hi his, hloc' i hi (hss ▸ his)]
        exact (congrFun hg ⟨i, hi⟩).symm
    obtain ⟨v₁, v₂⟩ := p
    obtain ⟨v₁', v₂'⟩ := p'
    simp only at *
    by_contra hne'
    by_cases hc1 : v₁' = v₁ ∨ v₁' = v₂
    · have hne2 : v₂' ≠ v₂ := by
        intro h; subst h
        rcases hc1 with rfl | rfl
        · exact hne' rfl
        · exact hpd' rfl
      obtain ⟨x, hx⟩ := hex2'
      rcases hv2' x hx with rfl | rfl
      · exact hnP2' hx
      · have := readExt_of_agree hA2 hx
        rcases hv2 _ this with h | h
        · subst h; exact hnP2 this
        · exact hne2 h
    · exact hc1 (hv1 _ (readExt_of_agree hA1 hP1'))

/-- **Theorem B.1, counting form** (repaired: without gossip and with `ReaderQuiet`):
`|V| ≤ ∏_{i ∈ 𝒩} |S_i|` for every set `𝒩` of at least `n - f` servers. -/
theorem theoremB1_count [Fintype V] {f : ℕ} (hReg : IsRegular A) (hLive : Live A f)
    (hNG : NoGossip A) (hQ : ReaderQuiet A) {S : Fin n → Finset L} (hS : StateBound A S)
    (hcard : n - f ≤ 𝒩.card) :
    Fintype.card V ≤ ∏ i ∈ 𝒩, (S i).card := by
  classical
  have hpt : ∀ v : V, ∃ C : Config (Node n) (register V v₀) M L, GoodCfg A 𝒩 C ∧
      ReadExt A 𝒩 C v ∧ ∀ x, ReadExt A 𝒩 C x → x = v := by
    intro v
    obtain ⟨F, hF, r, hr⟩ := exists_write (𝒩 := 𝒩) A hLive hcard (E := []) (by simp) rfl v
    set E : List (Event (Node n) (register V v₀)) := .invoke .wr (RWOp.write v) :: F
    have hgE : ∀ e ∈ E, GoodEv 𝒩 e := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · refine ⟨?_, Or.inl rfl⟩
        rintro p o h; simp only [Event.invoke.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨rfl, v, rfl⟩
      · exact (hF e he).1
    have hops : opsOf (A.hist A.initCfg E) .wr = [RWOp.write v] := by
      have := opsOf_hist_invoke A (C := A.initCfg) (p := .wr) (o := RWOp.write v) rfl
        (fun e he => (hF e he).2) .wr
      rw [ite_eq_left rfl] at this; exact this
    have hres : 0 < (respsOf (A.hist A.initCfg E) .wr).length := respsOf_pos_of_mem hr
    have hval : ∀ x, ReadExt A 𝒩 (A.run A.initCfg E) x → x = v := by
      intro x hx
      obtain ⟨m, hm1, hm2, -⟩ := read_value hReg hNG hQ hgE hres hx
      rw [hops, writeVal_one_write v hm1] at hm2; exact hm2
    obtain ⟨x, hx⟩ := exists_readExt (𝒩 := 𝒩) A hLive hcard (E := E)
      (fun e he => (hgE e he).1) (good_props 𝒩 hNG hQ hgE).2.1
    exact ⟨_, ⟨E, hgE, rfl⟩, by rw [← hval x hx]; exact hx, hval⟩
  choose C hC using hpt
  let σ : V → (𝒩 → L) := fun v j => (C v).loc (.srv j)
  have hle := Finset.card_le_card_of_injOn (s := Finset.univ)
    (t := Fintype.piFinset fun j : 𝒩 => S j) σ
    (fun v _ => Fintype.mem_piFinset.2 fun j => loc_mem_of_goodCfg hS (hC v).1 j)
    (fun v _ v' _ h => by
      have hA : Agree (XS 𝒩) (C v') (C v) :=
        agree_of_loc 𝒩 hNG hQ (hC v').1 (hC v).1 (fun i hi => (congrFun h ⟨i, hi⟩).symm)
      exact ((hC v).2.2 _ (readExt_of_agree hA (hC v').2.1)).symm)
  rw [Fintype.card_piFinset, Finset.prod_coe_sort 𝒩 (fun i => (S i).card)] at hle
  simpa using hle

/-- `RepliesOnly` (servers send to the reader only when processing a message of the reader)
implies `ReaderQuiet`. -/
theorem readerQuiet_of_repliesOnly (h : RepliesOnly A) : ReaderQuiet A := by
  intro E hok hE i
  clear hok
  suffices hgen : ∀ (C : Config (Node n) (register V v₀) M L), (∀ x, C.chan .rd x = []) →
      (∀ j, C.chan (.srv j) .rd = []) →
      (∀ x, (A.run C E).chan .rd x = []) ∧ ∀ j, (A.run C E).chan (.srv j) .rd = [] from
    (hgen _ (fun _ => rfl) (fun _ => rfl)).2 i
  induction E with
  | nil => exact fun C h1 h2 => ⟨h1, h2⟩
  | cons e E ih =>
    intro C h1 h2
    have hown : e.owner ≠ .rd := hE e (by simp)
    refine ih (fun e' he' => hE e' (by simp [he'])) _ (fun x => ?_) (fun j => ?_)
    · rw [List.eq_nil_iff_forall_not_mem]
      intro m hm
      rcases mem_chan_step A hm with hm | ⟨ho, -⟩
      · rw [h1 x] at hm; simp at hm
      · exact hown ho
    · rw [List.eq_nil_iff_forall_not_mem]
      intro m hm
      rcases mem_chan_step A hm with hm | ⟨ho, inp, hm, hinp⟩
      · rw [h2 j] at hm; simp at hm
      · -- the step of server `j` did not process a message of the reader
        have hinp' : ∀ m', inp ≠ .recv .rd m' := by
          intro m' he; have := hinp _ _ he; rw [h1] at this; simp at this
        exact h j inp _ hinp' _ hm rfl

end Podc.StorageCost
