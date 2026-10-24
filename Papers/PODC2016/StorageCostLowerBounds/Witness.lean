import Papers.PODC2016.StorageCostLowerBounds.Model

/-!
# Non-vacuity: a single-server register emulation

The hypotheses of the storage-cost theorems are satisfiable: with one server (`n = 1`, `f = 0`)
the obvious algorithm is an atomic (hence regular), live SWSR register emulation that does not
gossip, in which servers reply only to the reader's messages, and whose server has exactly
`|V|` states (`witness_hyps`).

* Writer: on `write v` it records `v` and sends `W v` to the server; on the acknowledgement `A`
  it returns.
* Server: it stores the value of the last `W v` it received and acknowledges it (`A`); on a query
  `Q` of the reader it answers `D` with the stored value.
* Reader: on `read` it sends `Q` to the server and returns the value of the answer `D v`.

Every node has a local state `(cur, stored) : V × V`; the writer uses `cur`, the server
`stored`, the reader none. At most one message of each client is in flight, which gives a simple
inductive invariant (`Inv`).
-/

namespace Podc.StorageCost.Witness

open Cslib.ChannelFailures Cslib.SharedMemory

variable {V : Type}

/-- Messages. -/
inductive Msg (V : Type) where
  /-- Writer to server: write `v`. -/
  | W (v : V)
  /-- Server to writer: acknowledgement. -/
  | A
  /-- Reader to server: query. -/
  | Q
  /-- Server to reader: the stored value. -/
  | D (v : V)

/-- Local states `(cur, stored)`. -/
abbrev LSt (V : Type) := V × V

/-- The only server. -/
abbrev s0 : Node 1 := .srv 0

/-- The transition function. -/
def handle : Node 1 → Input (Node 1) (RWOp V) (Msg V) → LSt V →
    LSt V × List (Node 1 × Msg V) × Option V
  | .wr, .invoke (.write v), l => ((v, l.2), [(.srv 0, .W v)], none)
  | .wr, .recv (.srv _) .A, l => (l, [], some l.1)
  | .rd, .invoke .read, l => (l, [(.srv 0, .Q)], none)
  | .rd, .recv (.srv _) (.D v), l => (l, [], some v)
  | .srv _, .recv .wr (.W v), l => ((l.1, v), [(.wr, .A)], none)
  | .srv _, .recv .rd .Q, l => (l, [(.rd, .D l.2)], none)
  | _, _, l => (l, [], none)

/-- The single-server algorithm. -/
def alg (v₀ : V) : Algorithm (Node 1) (register V v₀) (Msg V) (LSt V) where
  init _ := (v₀, v₀)
  handle := handle

/-! ### Static properties -/

lemma node_cases (x : Node 1) : x = s0 ∨ x = .wr ∨ x = .rd := by
  rcases x with i | _ | _
  · left; rw [Subsingleton.elim i 0]
  · simp
  · simp

/-- The algorithm does not gossip. -/
theorem noGossip (v₀ : V) : NoGossip (alg v₀) := by
  intro i inp l x hx j
  rcases inp with o | c | ⟨q, m⟩
  · simp [alg, handle] at hx
  · simp [alg, handle] at hx
  · rcases q with _ | _ | _ <;> rcases m <;> simp [alg, handle] at hx <;> subst hx <;> simp

/-- The server sends to the reader only when it processes a message of the reader. -/
theorem repliesOnly (v₀ : V) : RepliesOnly (alg v₀) := by
  intro i inp l hinp x hx
  rcases inp with o | c | ⟨q, m⟩
  · simp [alg, handle] at hx
  · simp [alg, handle] at hx
  · rcases q with _ | _ | _ <;> rcases m <;> simp [alg, handle] at hx
    · subst hx; simp
    · exact absurd rfl (hinp _)

/-! ### The invariant -/

abbrev Cfg (V : Type) (v₀ : V) := Config (Node 1) (register V v₀) (Msg V) (LSt V)
abbrev Hist (V : Type) (v₀ : V) := List (Label (Node 1) (register V v₀))

variable {v₀ : V}

/-- Number of invoked writes. -/
abbrev K (α : Hist V v₀) : ℕ := (opsOf α .wr).length

/-- Number of completed reads. -/
abbrev R (α : Hist V v₀) : ℕ := (respsOf α .rd).length

/-- Value of write `t`. -/
abbrev wv (α : Hist V v₀) (t : ℕ) : V := writeVal v₀ (opsOf α .wr) t

/-- Number of `W` messages processed by the server. -/
abbrev pp (C : Cfg V v₀) : ℕ := C.dlv .wr s0

/-- Pairs of nodes that may communicate. -/
def OkPair : Node 1 → Node 1 → Prop
  | .wr, .srv _ => True
  | .srv _, .wr => True
  | .rd, .srv _ => True
  | .srv _, .rd => True
  | _, _ => False

/-- The writer side: idle with everything processed, or a pending write whose `W` or `A` is in
transit. -/
def WrOk (C : Cfg V v₀) (α : Hist V v₀) : Prop :=
  (C.pend .wr = none ∧ pp C = K α ∧ C.chan .wr s0 = [] ∧ C.chan s0 .wr = []) ∨
  (C.pend .wr ≠ none ∧ (C.loc .wr).1 = wv α (K α) ∧
    ((pp C + 1 = K α ∧ C.chan .wr s0 = [.W (wv α (K α))] ∧ C.chan s0 .wr = []) ∨
     (pp C = K α ∧ C.chan .wr s0 = [] ∧ C.chan s0 .wr = [.A])))

/-- Responses of the writer. -/
def WRespOk (α : Hist V v₀) : Prop :=
  ∀ j < (respsOf α .wr).length, respOf α (.wr, j) = some (wv α (j + 1))

/-- Reads-from data of the completed reads. -/
def RFOk (C : Cfg V v₀) (α : Hist V v₀) (rf : ℕ → ℕ) : Prop :=
  ∀ j < R α, respOf α (.rd, j) = some (wv α (rf j)) ∧ rf j ≤ pp C ∧
    (0 < rf j → ¬ Precedes α (.rd, j) (.wr, rf j - 1)) ∧ ¬ Precedes α (.wr, rf j) (.rd, j) ∧
    ∀ j' < R α, j ≤ j' → rf j ≤ rf j'

/-- The reader side: idle, or a pending read whose `Q` or `D` is in transit; `lb` bounds the
writes that completed before the read was invoked. -/
def RdOk (C : Cfg V v₀) (α : Hist V v₀) (rf : ℕ → ℕ) : Prop :=
  (C.pend .rd = none ∧ C.chan .rd s0 = [] ∧ C.chan s0 .rd = []) ∨
  (C.pend .rd ≠ none ∧ ∃ lb, (∀ m, Precedes α (.wr, m) (.rd, R α) → m < lb) ∧
    ((C.chan .rd s0 = [.Q] ∧ C.chan s0 .rd = [] ∧ lb ≤ pp C) ∨
     (C.chan .rd s0 = [] ∧ ∃ p', C.chan s0 .rd = [.D (wv α p')] ∧ lb ≤ p' ∧ p' ≤ pp C ∧
       ∀ j < R α, rf j ≤ p')))

/-- The invariant. -/
structure Inv (C : Cfg V v₀) (α : Hist V v₀) : Prop where
  sfst : (C.loc s0).1 = v₀
  sval : (C.loc s0).2 = wv α (pp C)
  wr : WrOk C α
  wresp : WRespOk α
  rd : ∃ rf, RFOk C α rf ∧ RdOk C α rf
  other : ∀ a b, ¬ OkPair a b → C.chan a b = []

lemma WrOk.pp_le {C : Cfg V v₀} {α : Hist V v₀} (h : WrOk C α) : pp C ≤ K α := by
  rcases h with ⟨-, h, -⟩ | ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> omega

lemma WrOk.resps_le {C : Cfg V v₀} {α : Hist V v₀} (h : WrOk C α) (hacc : Acc α C) :
    (respsOf α .wr).length ≤ pp C := by
  have := hacc .wr
  rcases h with ⟨hp, h, -⟩ | ⟨hp, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;>
    simp [pendCount, hp] at this <;> simp only [K] at h <;> omega

theorem inv_init : Inv (alg v₀).initCfg ([] : Hist V v₀) := by
  refine ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩, fun j hj => by simp [respsOf] at hj,
    ⟨id, fun j hj => by simp [R, respsOf] at hj, Or.inl ⟨rfl, rfl, rfl⟩⟩, fun _ _ _ => rfl⟩

/-! ### Frame lemmas -/

/-- Steps that only touch the writer side (and the server) preserve the reader side. -/
theorem rd_preserve {C C' : Cfg V v₀} {α β : Hist V v₀} {rf : ℕ → ℕ} (hacc : Acc α C)
    (h : RFOk C α rf ∧ RdOk C α rf) (hβ : ∀ l ∈ β, l.proc = .wr)
    (hpp : pp C ≤ pp C') (hpK : pp C ≤ K α) (hpend : C'.pend .rd = C.pend .rd)
    (hq : C'.chan .rd s0 = C.chan .rd s0) (hd : C'.chan s0 .rd = C.chan s0 .rd) :
    RFOk C' (α ++ β) rf ∧ RdOk C' (α ++ β) rf := by
  have hβr : ∀ l ∈ β, l.proc ≠ .rd := fun l hl => by rw [hβ l hl]; simp
  have hopsr : opsOf (α ++ β) .rd = opsOf α .rd := by
    rw [opsOf_append, opsOf_eq_nil_of_proc_ne hβr, List.append_nil]
  have hrr : respsOf (α ++ β) .rd = respsOf α .rd := by
    rw [respsOf_append, respsOf_eq_nil_of_proc_ne hβr, List.append_nil]
  have hR : R (α ++ β) = R α := by simp only [R, hrr]
  have hwv : ∀ t ≤ K α, wv (α ++ β) t = wv α t := by
    intro t ht; simp only [wv, opsOf_append]; exact writeVal_append_of_le ht
  have hprd : ∀ x j, j < (opsOf α .rd).length →
      (Precedes (α ++ β) x (.rd, j) ↔ Precedes α x (.rd, j)) :=
    fun x j hj => precedes_append_iff_of_invoked hj
  have hpwr : ∀ x j, j < K α → (Precedes (α ++ β) x (.wr, j) ↔ Precedes α x (.wr, j)) :=
    fun x j hj => precedes_append_iff_of_invoked hj
  have hacr : (opsOf α .rd).length = R α + pendCount C .rd := hacc .rd
  obtain ⟨hrf, hrd⟩ := h
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hR] at hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrf j hj
    refine ⟨?_, h2.trans hpp, fun h0 hp => h3 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h4 ((hprd _ _ (by omega)).1 hp), fun j' hj' => h5 j' (by rw [hR] at hj'; exact hj')⟩
    rw [respOf_append_of_completed (show Completed α ((Node.rd : Node 1), j) from hj),
      hwv _ (by omega)]
    exact h1
  · rcases hrd with ⟨h1, h2, h3⟩ | ⟨h1, lb, hlb, h⟩
    · exact Or.inl ⟨by rw [hpend]; exact h1, by rw [hq]; exact h2, by rw [hd]; exact h3⟩
    · have hpr : (opsOf α .rd).length = R α + 1 := by
        simpa [pendCount, h1] using hacr
      refine Or.inr ⟨by rw [hpend]; exact h1, lb, fun m hm => hlb m ?_, ?_⟩
      · rw [hR] at hm; exact (hprd _ _ (by omega)).1 hm
      · rw [hq, hd, hR]
        rcases h with ⟨h2, h3, h4⟩ | ⟨h2, p', h3, h4, h5, h6⟩
        · exact Or.inl ⟨h2, h3, h4.trans hpp⟩
        · exact Or.inr ⟨h2, p', by rw [h3, hwv _ (by omega)], h4, h5.trans hpp, h6⟩

/-- Steps that only touch the reader side preserve the writer side. -/
theorem wr_preserve {C C' : Cfg V v₀} {α β : Hist V v₀} (hw : WrOk C α) (hresp : WRespOk α)
    (hβ : ∀ l ∈ β, l.proc = .rd) (hpp : pp C' = pp C) (hloc : C'.loc .wr = C.loc .wr)
    (hpend : C'.pend .wr = C.pend .wr) (h1 : C'.chan .wr s0 = C.chan .wr s0)
    (h2 : C'.chan s0 .wr = C.chan s0 .wr) :
    WrOk C' (α ++ β) ∧ WRespOk (α ++ β) ∧ ∀ t, wv (α ++ β) t = wv α t := by
  have hβw : ∀ l ∈ β, l.proc ≠ .wr := fun l hl => by rw [hβ l hl]; simp
  have hops : opsOf (α ++ β) .wr = opsOf α .wr := by
    rw [opsOf_append, opsOf_eq_nil_of_proc_ne hβw, List.append_nil]
  have hrw : respsOf (α ++ β) .wr = respsOf α .wr := by
    rw [respsOf_append, respsOf_eq_nil_of_proc_ne hβw, List.append_nil]
  have hK : K (α ++ β) = K α := by simp only [K, hops]
  have hwv : ∀ t, wv (α ++ β) t = wv α t := by intro t; simp only [wv, hops]
  refine ⟨?_, fun j hj => ?_, hwv⟩
  · unfold WrOk; rw [hpp, hloc, hpend, h1, h2, hK, hwv]; exact hw
  · rw [hrw] at hj
    simp only [respOf, hrw, hwv]; exact hresp j hj

/-! ### Generic step facts -/

lemma step_deliver_eq (C : Cfg V v₀) {a b : Node 1} {m : Msg V} {rest : List (Msg V)}
    (hc : C.chan a b = m :: rest) :
    (alg v₀).step C (.deliver a b) = (C.pop a b rest).apply b (handle b (.recv a m) (C.loc b)) := by
  simp [Algorithm.step, hc, alg]

lemma other_apply {C : Cfg V v₀} {p : Node 1} {r : LSt V × List (Node 1 × Msg V) × Option V}
    (hr : ∀ z ∈ r.2.1, OkPair p z.1) (ho : ∀ x y, ¬ OkPair x y → C.chan x y = []) :
    ∀ x y, ¬ OkPair x y → (C.apply p r).1.chan x y = [] := by
  intro x y hxy
  simp only [Config.apply]
  rw [ho x y hxy]
  split_ifs with hx
  · subst hx
    simp only [msgsTo, List.nil_append, List.map_eq_nil_iff, List.filter_eq_nil_iff,
      decide_eq_true_eq]
    intro z hz heq; exact hxy (heq ▸ hr z hz)
  · rfl

lemma other_pop {C : Cfg V v₀} {a b : Node 1} (hab : OkPair a b) (rest : List (Msg V))
    (ho : ∀ x y, ¬ OkPair x y → C.chan x y = []) :
    ∀ x y, ¬ OkPair x y → (C.pop a b rest).chan x y = [] := by
  intro x y hxy
  simp only [Config.pop]
  have : ¬ (x = a ∧ y = b) := by rintro ⟨rfl, rfl⟩; exact hxy hab
  simp only [this, ite_false]; exact ho x y hxy

lemma handle_tick (p : Node 1) (c : ℕ) (l : LSt V) : handle p (.tick c) l = (l, [], none) := by
  rcases p with _ | _ | _ <;> rfl

lemma apply_noop (C : Cfg V v₀) (p : Node 1) : C.apply p (C.loc p, [], none) = (C, []) := by
  rcases C with ⟨loc, pend, chan, sent, dlv⟩
  simp only [Config.apply, Function.update_eq_self, Prod.mk.injEq]
  refine ⟨?_, by simp [respOut]⟩
  have h1 : Function.update pend p (pendAfter (pend p) none) = pend := by
    have : pendAfter (pend p) none = pend p := by cases pend p <;> rfl
    rw [this, Function.update_eq_self]
  simp [h1, msgsTo]

@[simp] lemma pendAfter_none {A : ObjSpec} (o : Option A.Op) :
    pendAfter o (none : Option A.Resp) = o := by
  cases o <;> rfl

lemma okPair_wr_s0 : OkPair (.wr : Node 1) s0 := trivial
lemma okPair_s0_wr : OkPair s0 (.wr : Node 1) := trivial
lemma okPair_rd_s0 : OkPair (.rd : Node 1) s0 := trivial
lemma okPair_s0_rd : OkPair s0 (.rd : Node 1) := trivial

/-! ### The six effective steps -/

/-- The server receives `W v`. -/
theorem inv_deliver_W {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    {m : Msg V} {rest : List (Msg V)} (hc : C.chan .wr s0 = m :: rest) :
    Inv ((alg v₀).step C (.deliver .wr s0)).1 (α ++ ((alg v₀).step C (.deliver .wr s0)).2) := by
  rw [step_deliver_eq C hc]
  rcases hI.wr with ⟨-, -, h, -⟩ | ⟨hpw, hcur, ⟨hK, hW, hA⟩ | ⟨-, h, -⟩⟩
  · rw [h] at hc; simp at hc
  swap
  · rw [h] at hc; simp at hc
  rw [hW] at hc
  simp only [List.cons.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  set C' := ((C.pop .wr s0 []).apply s0 (handle s0 (.recv .wr (.W (wv α (K α)))) (C.loc s0)))
  have hl : C'.2 = [] := by simp [C', Config.apply, handle, respOut]
  rw [hl, List.append_nil]
  have hls : C'.1.loc s0 = ((C.loc s0).1, wv α (K α)) := by simp [C', Config.apply, handle]
  have hlw : C'.1.loc .wr = C.loc .wr := by simp [C', Config.apply, Config.pop]
  have hpend : ∀ x, C'.1.pend x = C.pend x := by
    intro x; simp [C', Config.apply, Config.pop, handle, Function.update_apply]
    intro hx; subst hx; exact pendAfter_none _
  have hpp : pp C'.1 = pp C + 1 := by simp [C', pp, Config.apply, Config.pop]
  have c1 : C'.1.chan .wr s0 = [] := by simp [C', Config.apply, Config.pop]
  have c2 : C'.1.chan s0 .wr = [.A] := by simp [C', Config.apply, Config.pop, hA, handle, msgsTo]
  have c3 : C'.1.chan .rd s0 = C.chan .rd s0 := by simp [C', Config.apply, Config.pop]
  have c4 : C'.1.chan s0 .rd = C.chan s0 .rd := by
    simp [C', Config.apply, Config.pop, handle, msgsTo]
  refine ⟨by rw [hls]; exact hI.sfst, by rw [hls, hpp]; simp only [K] at hK; rw [hK],
    Or.inr ⟨by rw [hpend]; exact hpw, by rw [hlw]; exact hcur, Or.inr ⟨by omega, c1, c2⟩⟩,
    hI.wresp, ?_, ?_⟩
  · obtain ⟨rf, h⟩ := hI.rd
    have := rd_preserve (β := []) hacc h (by simp) (by omega) hI.wr.pp_le (hpend _) c3 c4
    rw [List.append_nil] at this
    exact ⟨rf, this⟩
  · exact other_apply (fun z hz => by simp [handle] at hz; subst hz; trivial)
      (other_pop okPair_wr_s0 _ hI.other)

/-- The writer receives the acknowledgement `A`: the write returns. -/
theorem inv_deliver_A {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    {m : Msg V} {rest : List (Msg V)} (hc : C.chan s0 .wr = m :: rest) :
    Inv ((alg v₀).step C (.deliver s0 .wr)).1 (α ++ ((alg v₀).step C (.deliver s0 .wr)).2) := by
  rw [step_deliver_eq C hc]
  rcases hI.wr with ⟨-, -, -, h⟩ | ⟨hpw, hcur, ⟨-, -, h⟩ | ⟨hK, hW, hA⟩⟩
  · rw [h] at hc; simp at hc
  · rw [h] at hc; simp at hc
  rw [hA] at hc
  simp only [List.cons.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpw
  set C' := ((C.pop s0 .wr []).apply .wr (handle .wr (.recv s0 .A) (C.loc .wr)))
  have hl : C'.2 = [.ret .wr (wv α (K α))] := by
    simp [C', Config.apply, Config.pop, handle, respOut, ho, hcur]
  rw [hl]
  set β : Hist V v₀ := [.ret .wr (wv α (K α))]
  have hloc : ∀ x, C'.1.loc x = C.loc x := by
    intro x; simp [C', Config.apply, Config.pop, handle]
  have hpw' : C'.1.pend .wr = none := by simp [C', Config.apply, Config.pop, handle, pendAfter, ho]
  have hpr : C'.1.pend .rd = C.pend .rd := by simp [C', Config.apply, Config.pop]
  have hpp : pp C'.1 = pp C := by simp [C', pp, Config.apply, Config.pop]
  have c1 : C'.1.chan .wr s0 = [] := by
    simp [C', Config.apply, Config.pop, handle, msgsTo, hW]
  have c2 : C'.1.chan s0 .wr = [] := by simp [C', Config.apply, Config.pop]
  have c3 : C'.1.chan .rd s0 = C.chan .rd s0 := by
    simp [C', Config.apply, Config.pop]
  have c4 : C'.1.chan s0 .rd = C.chan s0 .rd := by simp [C', Config.apply, Config.pop]
  have hops : opsOf (α ++ β) .wr = opsOf α .wr := by simp [β]
  have hK' : K (α ++ β) = K α := by simp only [K, hops]
  have hwv : ∀ t, wv (α ++ β) t = wv α t := by intro t; simp only [wv, hops]
  have hacw : (opsOf α .wr).length = (respsOf α .wr).length + 1 := by
    simpa [pendCount, ho] using hacc .wr
  refine ⟨by rw [hloc]; exact hI.sfst, by rw [hloc, hpp, hwv]; exact hI.sval,
    Or.inl ⟨hpw', by rw [hpp, hK']; exact hK, c1, c2⟩, fun j hj => ?_, ?_, ?_⟩
  · have hrw : (respsOf (α ++ β) .wr).length = (respsOf α .wr).length + 1 := by simp [β]
    rw [hrw] at hj
    rw [hwv]
    by_cases hjc : j < (respsOf α .wr).length
    · rw [respOf_append_of_completed (show Completed α ((Node.wr : Node 1), j) from hjc)]
      exact hI.wresp j hjc
    · have hj' : j = (respsOf α .wr).length := by omega
      subst hj'
      simp only [respOf, respsOf_append, β, respsOf_cons, respsOf_nil, List.append_nil]
      rw [List.getElem?_append_right le_rfl]
      simp only [Label.retOf, ite_true, Nat.sub_self, Option.toList_some, List.getElem?_cons_zero]
      simp only [K] at *
      rw [hacw]
  · obtain ⟨rf, h⟩ := hI.rd
    exact ⟨rf, rd_preserve hacc h (by simp [β, Label.proc]) hpp.ge hI.wr.pp_le hpr c3 c4⟩
  · exact other_apply (fun z hz => by simp [handle] at hz) (other_pop okPair_s0_wr _ hI.other)

/-- The server receives the query `Q`: it answers with its value. -/
theorem inv_deliver_Q {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α)
    {m : Msg V} {rest : List (Msg V)} (hc : C.chan .rd s0 = m :: rest) :
    Inv ((alg v₀).step C (.deliver .rd s0)).1 (α ++ ((alg v₀).step C (.deliver .rd s0)).2) := by
  rw [step_deliver_eq C hc]
  obtain ⟨rf, hrf, hrd⟩ := hI.rd
  rcases hrd with ⟨-, h, -⟩ | ⟨hpr, lb, hlb, ⟨hQ, hD, hlbp⟩ | ⟨h, -⟩⟩
  · rw [h] at hc; simp at hc
  swap
  · rw [h] at hc; simp at hc
  rw [hQ] at hc
  simp only [List.cons.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  set C' := ((C.pop .rd s0 []).apply s0 (handle s0 (.recv .rd .Q) (C.loc s0)))
  have hl : C'.2 = [] := by simp [C', Config.apply, handle, respOut]
  rw [hl, List.append_nil]
  have hloc : ∀ x, C'.1.loc x = C.loc x := by
    intro x; simp [C', Config.apply, Config.pop, handle]
  have hpend : ∀ x, C'.1.pend x = C.pend x := by
    intro x; simp [C', Config.apply, Config.pop, handle, Function.update_apply]
    intro hx; subst hx; exact pendAfter_none _
  have hpp : pp C'.1 = pp C := by simp [C', pp, Config.apply, Config.pop]
  have c1 : C'.1.chan .wr s0 = C.chan .wr s0 := by simp [C', Config.apply, Config.pop]
  have c2 : C'.1.chan s0 .wr = C.chan s0 .wr := by
    simp [C', Config.apply, Config.pop, handle, msgsTo]
  have c3 : C'.1.chan .rd s0 = [] := by simp [C', Config.apply, Config.pop]
  have c4 : C'.1.chan s0 .rd = [.D (wv α (pp C))] := by
    simp [C', Config.apply, Config.pop, handle, msgsTo, hD, hI.sval]
  obtain ⟨hw, -, -⟩ := wr_preserve (β := []) hI.wr hI.wresp (by simp) hpp (hloc _) (hpend _) c1 c2
  rw [List.append_nil] at hw
  refine ⟨by rw [hloc]; exact hI.sfst, by rw [hloc, hpp]; exact hI.sval, hw, hI.wresp,
    ⟨rf, fun j hj => ?_, Or.inr ⟨by rw [hpend]; exact hpr, lb, hlb,
      Or.inr ⟨c3, pp C, c4, hlbp, by rw [hpp], fun j hj => (hrf j hj).2.1⟩⟩⟩, ?_⟩
  · rw [hpp]; exact hrf j hj
  · exact other_apply (fun z hz => by simp [handle] at hz; subst hz; trivial)
      (other_pop okPair_rd_s0 _ hI.other)

/-- The reader receives the answer `D v`: the read returns `v`. -/
theorem inv_deliver_D {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    {m : Msg V} {rest : List (Msg V)} (hc : C.chan s0 .rd = m :: rest) :
    Inv ((alg v₀).step C (.deliver s0 .rd)).1 (α ++ ((alg v₀).step C (.deliver s0 .rd)).2) := by
  rw [step_deliver_eq C hc]
  obtain ⟨rf, hrf, hrd⟩ := hI.rd
  rcases hrd with ⟨-, -, h⟩ | ⟨hpr, lb, hlb, ⟨-, h, -⟩ | ⟨hQ, p', hD, hlbp, hpp', hrfp⟩⟩
  · rw [h] at hc; simp at hc
  · rw [h] at hc; simp at hc
  rw [hD] at hc
  simp only [List.cons.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpr
  set C' := ((C.pop s0 .rd []).apply .rd (handle .rd (.recv s0 (.D (wv α p'))) (C.loc .rd)))
  have hl : C'.2 = [.ret .rd (wv α p')] := by
    simp [C', Config.apply, Config.pop, handle, respOut, ho]
  rw [hl]
  set β : Hist V v₀ := [.ret .rd (wv α p')]
  have hloc : ∀ x, C'.1.loc x = C.loc x := by
    intro x; simp [C', Config.apply, Config.pop, handle]
  have hpr' : C'.1.pend .rd = none := by
    simp [C', Config.apply, Config.pop, handle, pendAfter, ho]
  have hpw : C'.1.pend .wr = C.pend .wr := by simp [C', Config.apply, Config.pop]
  have hpp : pp C'.1 = pp C := by simp [C', pp, Config.apply, Config.pop]
  have c1 : C'.1.chan .wr s0 = C.chan .wr s0 := by simp [C', Config.apply, Config.pop]
  have c2 : C'.1.chan s0 .wr = C.chan s0 .wr := by simp [C', Config.apply, Config.pop]
  have c3 : C'.1.chan .rd s0 = [] := by simp [C', Config.apply, Config.pop, handle, msgsTo, hQ]
  have c4 : C'.1.chan s0 .rd = [] := by simp [C', Config.apply, Config.pop]
  obtain ⟨hw, hwr, hwv⟩ := wr_preserve (β := β) hI.wr hI.wresp (by simp [β, Label.proc]) hpp
    (hloc _) hpw c1 c2
  have hpK := hI.wr.pp_le
  have hacr : (opsOf α .rd).length = R α + 1 := by simpa [pendCount, ho] using hacc .rd
  have hRR : R (α ++ β) = R α + 1 := by simp [β, R]
  have hprd : ∀ x k, k < (opsOf α .rd).length →
      (Precedes (α ++ β) x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes (α ++ β) x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  refine ⟨by rw [hloc]; exact hI.sfst, by rw [hloc, hpp, hwv]; exact hI.sval, hw, hwr,
    ⟨Function.update rf (R α) p', fun j hj => ?_, Or.inl ⟨hpr', c3, c4⟩⟩, ?_⟩
  · rw [hRR] at hj
    simp only [hwv, hpp]
    by_cases hjR : j < R α
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hrf j hjR
      rw [Function.update_of_ne (by omega)]
      refine ⟨by
          rw [respOf_append_of_completed (show Completed α ((Node.rd : Node 1), j) from hjR)]
          exact h1, h2,
        fun h0 hp => h3 h0 ((hpwr _ _ (by omega)).1 hp),
        fun hp => h4 ((hprd _ _ (by omega)).1 hp), fun j' hj' hjj' => ?_⟩
      rw [hRR] at hj'
      by_cases hj'R : j' = R α
      · rw [hj'R, Function.update_self]; exact hrfp j hjR
      · rw [Function.update_of_ne hj'R]; exact h5 j' (by omega) hjj'
    · have hjR' : j = R α := by omega
      rw [hjR', Function.update_self]
      refine ⟨?_, hpp', fun h0 hp => ?_, fun hp => ?_, fun j' hj' hjj' => ?_⟩
      · simp only [respOf, respsOf_append, β, respsOf_cons, respsOf_nil, List.append_nil]
        rw [List.getElem?_append_right le_rfl]
        simp [Label.retOf]
      · have := ((hpwr _ _ (by omega)).1 hp).completed
        simp [Completed] at this
      · have := hlb _ ((hprd _ _ (by omega)).1 hp)
        omega
      · rw [hRR] at hj'
        have : j' = R α := by omega
        rw [this, Function.update_self]
  · exact other_apply (fun z hz => by simp [handle] at hz) (other_pop okPair_s0_rd _ hI.other)

/-- Invocation of `write v`. -/
theorem inv_invoke_wr {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    (hp : C.pend .wr = none) (v : V) :
    Inv ((alg v₀).step C (.invoke .wr (.write v))).1
      (α ++ ((alg v₀).step C (.invoke .wr (.write v))).2) := by
  rcases hI.wr with ⟨-, hpK, h1, h2⟩ | ⟨h, -⟩
  swap
  · exact absurd hp h
  set C' := (({ C with pend := Function.update C.pend .wr (some (.write v)) } : Cfg V v₀).apply
    .wr ((v, (C.loc .wr).2), [(s0, .W v)], none))
  have hstep : (alg v₀).step C (.invoke .wr (.write v)) = (C'.1, [.inv .wr (.write v)]) := by
    simp [C', Algorithm.step, hp, alg, handle, Config.apply, respOut]
  rw [hstep]
  set β : Hist V v₀ := [.inv .wr (.write v)]
  have hloc : ∀ x, x ≠ .wr → C'.1.loc x = C.loc x := by
    intro x hx; simp [C', Config.apply, hx]
  have hlw : (C'.1.loc .wr).1 = v := by simp [C', Config.apply]
  have hpw : C'.1.pend .wr = some (.write v) := by simp [C', Config.apply, pendAfter]
  have hpr : C'.1.pend .rd = C.pend .rd := by simp [C', Config.apply]
  have hpp : pp C'.1 = pp C := by simp [C', pp, Config.apply]
  have c1 : C'.1.chan .wr s0 = [.W v] := by simp [C', Config.apply, msgsTo, h1]
  have c2 : C'.1.chan s0 .wr = [] := by simp [C', Config.apply, h2]
  have c3 : C'.1.chan .rd s0 = C.chan .rd s0 := by simp [C', Config.apply]
  have c4 : C'.1.chan s0 .rd = C.chan s0 .rd := by simp [C', Config.apply]
  have hops : opsOf (α ++ β) .wr = opsOf α .wr ++ [.write v] := by simp [β]
  have hK' : K (α ++ β) = K α + 1 := by simp [K, hops]
  have hwv : ∀ t ≤ K α, wv (α ++ β) t = wv α t := by
    intro t ht; simp only [wv, hops]; exact writeVal_append_of_le ht
  have hwvK : wv (α ++ β) (K α + 1) = v := by
    simp only [wv, hops]; exact writeVal_succ (by simp)
  have hrw : respsOf (α ++ β) .wr = respsOf α .wr := by simp [β]
  have hacw : (opsOf α .wr).length = (respsOf α .wr).length := by
    simpa [pendCount, hp] using hacc .wr
  refine ⟨by rw [hloc _ (by simp)]; exact hI.sfst,
    by rw [hloc _ (by simp), hpp, hwv _ hI.wr.pp_le]; exact hI.sval,
    Or.inr ⟨by rw [hpw]; simp, by rw [hlw, hK', hwvK],
      Or.inl ⟨by rw [hpp, hK', hpK], by rw [c1, hK', hwvK], c2⟩⟩, fun j hj => ?_, ?_, ?_⟩
  · rw [hrw] at hj
    rw [respOf_append_of_completed (show Completed α ((Node.wr : Node 1), j) from hj),
      hwv _ (by simp only [K]; omega)]
    exact hI.wresp j hj
  · obtain ⟨rf, h⟩ := hI.rd
    exact ⟨rf, rd_preserve hacc h (by simp [β, Label.proc]) hpp.ge hI.wr.pp_le hpr c3 c4⟩
  · exact other_apply (fun z hz => by simp at hz; subst hz; trivial) hI.other

/-- Invocation of `read`. -/
theorem inv_invoke_rd {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    (hp : C.pend .rd = none) :
    Inv ((alg v₀).step C (.invoke .rd .read)).1 (α ++ ((alg v₀).step C (.invoke .rd .read)).2) := by
  obtain ⟨rf, hrf, hrd⟩ := hI.rd
  rcases hrd with ⟨-, h1, h2⟩ | ⟨h, -⟩
  swap
  · exact absurd hp h
  set C' := (({ C with pend := Function.update C.pend .rd (some .read) } : Cfg V v₀).apply
    .rd (C.loc .rd, [(s0, .Q)], none))
  have hstep : (alg v₀).step C (.invoke .rd .read) = (C'.1, [.inv .rd .read]) := by
    simp [C', Algorithm.step, hp, alg, handle, Config.apply, respOut]
  rw [hstep]
  set β : Hist V v₀ := [.inv .rd .read]
  have hloc : ∀ x, C'.1.loc x = C.loc x := by intro x; simp [C', Config.apply]
  have hpr : C'.1.pend .rd = some .read := by simp [C', Config.apply, pendAfter]
  have hpw : C'.1.pend .wr = C.pend .wr := by simp [C', Config.apply]
  have hpp : pp C'.1 = pp C := by simp [C', pp, Config.apply]
  have c1 : C'.1.chan .wr s0 = C.chan .wr s0 := by simp [C', Config.apply]
  have c2 : C'.1.chan s0 .wr = C.chan s0 .wr := by simp [C', Config.apply]
  have c3 : C'.1.chan .rd s0 = [.Q] := by simp [C', Config.apply, msgsTo, h1]
  have c4 : C'.1.chan s0 .rd = [] := by simp [C', Config.apply, h2]
  obtain ⟨hw, hwr, hwv⟩ := wr_preserve (β := β) hI.wr hI.wresp (by simp [β, Label.proc]) hpp
    (hloc _) hpw c1 c2
  have hacr : (opsOf α .rd).length = R α := by simpa [pendCount, hp] using hacc .rd
  have hrr : R (α ++ β) = R α := by simp [β, R]
  have hprd : ∀ x k, k < (opsOf α .rd).length →
      (Precedes (α ++ β) x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes (α ++ β) x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpK := hI.wr.pp_le
  refine ⟨by rw [hloc]; exact hI.sfst, by rw [hloc, hpp, hwv]; exact hI.sval, hw, hwr,
    ⟨rf, fun j hj => ?_, Or.inr ⟨by rw [hpr]; simp, (respsOf α .wr).length, fun m hm => ?_,
      Or.inl ⟨c3, c4, ?_⟩⟩⟩, ?_⟩
  · rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrf j hj
    refine ⟨by
        rw [respOf_append_of_completed (show Completed α ((Node.rd : Node 1), j) from hj), hwv]
        exact h1, by rw [hpp]; exact h2,
      fun h0 hp => h3 h0 ((hpwr _ _ (by omega)).1 hp), fun hp => h4 ((hprd _ _ (by omega)).1 hp),
      fun j' hj' => h5 j' (by rw [hrr] at hj'; exact hj')⟩
  · rw [hrr, ← hacr] at hm
    exact precedes_append_inv_iff.1 hm
  · rw [hpp]; exact hI.wr.resps_le hacc
  · exact other_apply (fun z hz => by simp at hz; subst hz; trivial) hI.other

/-! ### Reachable configurations -/

theorem inv_step {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) (hacc : Acc α C)
    (e : Event (Node 1) (register V v₀)) (he : EvOk e) :
    Inv ((alg v₀).step C e).1 (α ++ ((alg v₀).step C e).2) := by
  cases e with
  | invoke p o =>
    rcases hp : C.pend p with _ | o'
    · rcases he p o rfl with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
      · exact inv_invoke_wr hI hacc hp v
      · exact inv_invoke_rd hI hacc hp
    · have : (alg v₀).step C (.invoke p o) = (C, []) := by simp [Algorithm.step, hp]
      rw [this, List.append_nil]; exact hI
  | tick p c =>
    have : (alg v₀).step C (.tick p c) = (C, []) := by
      simp only [Algorithm.step, alg]; rw [handle_tick, apply_noop]
    rw [this, List.append_nil]; exact hI
  | deliver a b =>
    rcases hc : C.chan a b with _ | ⟨m, rest⟩
    · have : (alg v₀).step C (.deliver a b) = (C, []) := by simp [Algorithm.step, hc]
      rw [this, List.append_nil]; exact hI
    have hok : OkPair a b := by
      by_contra h; rw [hI.other a b h] at hc; simp at hc
    rcases node_cases a with rfl | rfl | rfl <;> rcases node_cases b with rfl | rfl | rfl <;>
      simp only [OkPair] at hok
    · exact inv_deliver_A hI hacc hc
    · exact inv_deliver_D hI hacc hc
    · exact inv_deliver_W hI hacc hc
    · exact inv_deliver_Q hI hc

/-- The invariant holds in every reachable configuration (SWSR environment). -/
theorem inv_reach (E : List (Event (Node 1) (register V v₀))) (hE : ∀ e ∈ E, EvOk e) :
    Inv ((alg v₀).run (alg v₀).initCfg E) ((alg v₀).hist (alg v₀).initCfg E) := by
  induction E using List.reverseRecOn with
  | nil => exact inv_init
  | append_singleton E e ih =>
    have ih' := ih (fun e' he' => hE e' (by simp [he']))
    rw [Algorithm.run_append, Algorithm.hist_append]
    have := inv_step ih' (acc_hist _ E) e (hE e (by simp))
    simpa [Algorithm.hist] using this

/-! ### Safety -/

theorem readsFrom (E : List (Event (Node 1) (register V v₀))) (hE : ∀ e ∈ E, EvOk e) :
    ∃ rf, SWSRReadsFrom ((alg v₀).hist (alg v₀).initCfg E) Node.wr Node.rd rf := by
  have hI := inv_reach E hE
  obtain ⟨rf, hrf, -⟩ := hI.rd
  refine ⟨rf, ⟨by simp, wellFormed_hist _ E, fun p o ho => ?_, fun j v x hop hres => ?_,
    fun k hk => (hrf k hk).1, fun k hk => (hrf k hk).2.2.1, fun k hk => (hrf k hk).2.2.2.1,
    fun k k' hkk' hk' _ => (hrf k (by simp only [R]; omega)).2.2.2.2 k' hk' hkk'.le⟩⟩
  · exact hE _ (mem_opsOf_hist _ ho) p o rfl
  · have hj : j < (respsOf ((alg v₀).hist (alg v₀).initCfg E) .wr).length := by
      by_contra h; simp [respOf, List.getElem?_eq_none (not_lt.1 h)] at hres
    rw [hI.wresp j hj] at hres
    simp only [Option.some.injEq] at hres
    rw [← hres]
    exact writeVal_succ hop

/-- The single-server algorithm is atomic. -/
theorem isAtomic (v₀ : V) : IsAtomic (alg v₀) := by
  intro E hE
  obtain ⟨rf, h⟩ := readsFrom E hE
  exact ⟨_, h.isLinearization⟩

/-- The single-server algorithm is regular. -/
theorem isRegular (v₀ : V) : IsRegular (alg v₀) := by
  intro E hE k hk
  obtain ⟨rf, h⟩ := readsFrom E hE
  exact ⟨rf k, h.read_val k hk, h.not_future k hk, h.not_overwritten k hk⟩

/-! ### Storage -/

/-- The server states: `(v₀, v)` for `v : V`. -/
def srvStates [Fintype V] (v₀ : V) : Fin 1 → Finset (LSt V) :=
  fun _ => Finset.univ.map ⟨fun v => (v₀, v), fun a b h => by simpa using h⟩

theorem card_srvStates [Fintype V] (v₀ : V) : (srvStates v₀ 0).card = Fintype.card V := by
  simp [srvStates]

theorem stateBound [Fintype V] (v₀ : V) : StateBound (alg v₀) (srvStates v₀) := by
  intro E hE i
  rw [Subsingleton.elim i 0]
  have h := (inv_reach E hE).sfst
  simp only [srvStates, Finset.mem_map, Finset.mem_univ, true_and]
  exact ⟨_, Prod.ext h.symm rfl⟩

/-! ### Liveness -/

lemma inv_at (ev : ℕ → Event (Node 1) (register V v₀)) (hev : ∀ t, EvOk (ev t)) (t : ℕ) :
    Inv ((alg v₀).cfgAt ev t) ((alg v₀).hist (alg v₀).initCfg (Algorithm.pre ev t)) := by
  rw [Algorithm.cfgAt_eq_run]
  exact inv_reach _ (fun e he => by
    simp only [Algorithm.pre, List.mem_map] at he; obtain ⟨u, -, rfl⟩ := he; exact hev u)

lemma chan_deliver_self (C : Cfg V v₀) {a b : Node 1} {m : Msg V} {rest : List (Msg V)}
    (hc : C.chan a b = m :: rest) (hab : a ≠ b) :
    ((alg v₀).step C (.deliver a b)).1.chan a b = rest := by
  rw [step_deliver_eq C hc]; simp [Config.apply, Config.pop, hab]

/-- A pending client has exactly one message in flight; once the server's message reaches it,
it returns. -/
lemma client_facts {C : Cfg V v₀} {α : Hist V v₀} (hI : Inv C α) {c : Node 1}
    (hc : c = .wr ∨ c = .rd) (hp : C.pend c ≠ none) :
    ((∃ m, C.chan c s0 = [m]) ∨ (C.chan c s0 = [] ∧ ∃ m, C.chan s0 c = [m])) ∧
      ∀ m rest, C.chan s0 c = m :: rest →
        ∃ x, Label.ret c x ∈ ((alg v₀).step C (.deliver s0 c)).2 := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
  rcases hc with rfl | rfl
  · rcases hI.wr with ⟨h, -⟩ | ⟨-, -, ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩⟩
    · exact absurd h hp
    · refine ⟨Or.inl ⟨_, h1⟩, fun m rest h => ?_⟩
      rw [h2] at h; simp at h
    · refine ⟨Or.inr ⟨h1, _, h2⟩, fun m rest h => ?_⟩
      rw [h2] at h; simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [step_deliver_eq C h2]
      exact ⟨(C.loc .wr).1, by simp [Config.apply, Config.pop, handle, respOut, ho]⟩
  · obtain ⟨rf, -, hrd⟩ := hI.rd
    rcases hrd with ⟨h, -⟩ | ⟨-, lb, -, ⟨h1, h2, -⟩ | ⟨h1, p', h2, -⟩⟩
    · exact absurd h hp
    · refine ⟨Or.inl ⟨_, h1⟩, fun m rest h => ?_⟩
      rw [h2] at h; simp at h
    · refine ⟨Or.inr ⟨h1, _, h2⟩, fun m rest h => ?_⟩
      rw [h2] at h; simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [step_deliver_eq C h2]
      exact ⟨wv α p', by simp [Config.apply, Config.pop, handle, respOut, ho]⟩

/-- The single-server algorithm is live (with no server failure). -/
theorem isLive (v₀ : V) : Live (alg v₀) 0 := by
  intro fp hch hfail ev hfair hev c hcr t₀ o hinv hpend
  have hs0 : ¬ Algorithm.Crashed fp ev s0 := by
    rintro ⟨h, -⟩
    have : (0 : Fin 1) ∈ srvFail fp := by
      classical
      simp only [srvFail, Finset.mem_filter, Finset.mem_univ, true_and]; convert h
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hfail)] at this
    simp at this
  have hnoch : ∀ a b, (a, b) ∉ fp.chans := by intro a b; rw [hch]; simp
  have hI := inv_at ev hev
  have hcfg : ∀ t, (alg v₀).cfgAt ev (t + 1) = ((alg v₀).step ((alg v₀).cfgAt ev t) (ev t)).1 :=
    fun t => rfl
  have hc : c = .wr ∨ c = .rd := by
    rcases hev t₀ c o hinv with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hcs : c ≠ s0 := by rcases hc with rfl | rfl <;> simp
  by_contra hnr
  have hnr' : ∀ t ≥ t₀, ∀ x, Label.ret c x ∉ (alg v₀).labAt ev t := by
    intro t ht x hx; exact hnr ⟨t, ht, x, hx⟩
  have hp1 : ((alg v₀).cfgAt ev (t₀ + 1)).pend c ≠ none := by
    rw [hcfg, hinv]
    simp only [Algorithm.step, hpend]
    rcases hc with rfl | rfl <;> rcases o with _ | v <;>
      simp [Config.apply, pendAfter, alg, handle]
  have hst : ∀ t ≥ t₀ + 1, ((alg v₀).cfgAt ev t).pend c ≠ none := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hp1
    | succ t ht ih =>
      rw [hcfg]; exact pend_step_of_no_ret _ ih (ev t) (hnr' t (by omega))
  obtain ⟨T, hT, m, hm⟩ : ∃ T ≥ t₀ + 1, ∃ m, ((alg v₀).cfgAt ev T).chan s0 c = [m] := by
    rcases (client_facts (hI (t₀ + 1)) hc (hst _ le_rfl)).1 with ⟨m, hm⟩ | ⟨-, m, hm⟩
    · obtain ⟨t, ht, he, hh⟩ := Algorithm.Fair.delivered hfair hcr hs0 (hnoch _ _) 0 (t₀ + 1) m
        (by rw [hm]; rfl)
      have hfc := (client_facts (hI t) hc (hst t ht)).1
      obtain ⟨m', hm'⟩ : ∃ m', ((alg v₀).cfgAt ev t).chan c s0 = [m'] := by
        rcases hfc with h | ⟨h, -⟩
        · exact h
        · rw [h] at hh; simp at hh
      have h1 : ((alg v₀).cfgAt ev (t + 1)).chan c s0 = [] := by
        rw [hcfg, he]; exact chan_deliver_self _ hm' hcs
      rcases (client_facts (hI (t + 1)) hc (hst _ (by omega))).1 with ⟨m'', h⟩ | ⟨-, m'', h⟩
      · rw [h1] at h; simp at h
      · exact ⟨t + 1, by omega, m'', h⟩
    · exact ⟨t₀ + 1, le_rfl, m, hm⟩
  obtain ⟨t, ht, he, hh⟩ := Algorithm.Fair.delivered hfair hs0 hcr (hnoch _ _) 0 T m
    (by rw [hm]; rfl)
  obtain ⟨m', rest, hm'⟩ : ∃ m' rest, ((alg v₀).cfgAt ev t).chan s0 c = m' :: rest := by
    cases h : ((alg v₀).cfgAt ev t).chan s0 c with
    | nil => rw [h] at hh; simp at hh
    | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨x, hx⟩ := (client_facts (hI t) hc (hst t (by omega))).2 m' rest hm'
  exact hnr' t (by omega) x (by simp only [Algorithm.labAt, he]; exact hx)

/-! ### The witness -/

/-- **Non-vacuity.** For every finite value set `V`, the single-server algorithm is a regular
(even atomic) SWSR register emulation that is live with `f = 0`, does not gossip, whose server
replies to the reader only, and whose server has `|V|` states. -/
theorem witness_hyps [Fintype V] (v₀ : V) :
    IsRegular (alg v₀) ∧ IsAtomic (alg v₀) ∧ Live (alg v₀) 0 ∧ NoGossip (alg v₀) ∧
      RepliesOnly (alg v₀) ∧ StateBound (alg v₀) (srvStates v₀) ∧
      (srvStates v₀ 0).card = Fintype.card V :=
  ⟨isRegular v₀, isAtomic v₀, isLive v₀, noGossip v₀, repliesOnly v₀, stateBound v₀,
    card_srvStates v₀⟩

end Podc.StorageCost.Witness
