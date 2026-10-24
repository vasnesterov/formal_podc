import Papers.PODC2016.StorageCostLowerBounds.Relay

/-!
# Safety of the relay algorithm

An inductive invariant `Inv` of the reachable configurations of `relay v₀ qs` (with history),
for quorum size `qs` with `qs ≤ n < 2 qs`. It gives atomicity (via CSLib's SWSR reads-from
criterion `SWSRReadsFrom.isLinearization`) and regularity.

Key facts (with `p i` = number of `W` messages server `i` has processed):
* the writer's channel to server `i` holds exactly `W (p i + 1) … W K` (FIFO);
* every `F t` sent by server `i` (`t ≤ p i`) was either received by the reader (`t ≤ best`)
  or is still in transit (`invF`);
* a completed write `c` was processed by `qs` servers (`wq`);
* the answer `D q` of server `i` to the current read can only be received after an `F t` with
  `t ≥ lb` (`DOk`), where `lb` bounds the writes completed before the read was invoked.
-/

namespace Podc.StorageCost.Relay

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n : ℕ} {V : Type} (v₀ : V) (qs : ℕ)

abbrev Cfg (n : ℕ) (V : Type) (v₀ : V) := Config (Node n) (register V v₀) (Msg V) (LSt n V)
abbrev Hist (n : ℕ) (V : Type) (v₀ : V) := List (Label (Node n) (register V v₀))

variable {v₀}

/-- Number of invoked writes. -/
abbrev K (α : Hist n V v₀) : ℕ := (opsOf α .wr).length

/-- Value of write `t`. -/
abbrev wv (α : Hist n V v₀) (t : ℕ) : V := writeVal v₀ (opsOf α .wr) t

/-- Number of `W` messages processed by server `i`. -/
abbrev pp (C : Cfg n V v₀) (i : Fin n) : ℕ := C.dlv .wr (.srv i)

/-- The expected contents of the channel writer → server `i`. -/
def wlist (α : Hist n V v₀) (p : ℕ) : List (Msg V) :=
  (List.range (K α - p)).map fun j => .W (p + 1 + j) (wv α (p + 1 + j))

/-- Pairs of nodes that may communicate. -/
def OkPair : Node n → Node n → Prop
  | .wr, .srv _ => True
  | .srv _, .wr => True
  | .rd, .srv _ => True
  | .srv _, .rd => True
  | _, _ => False

/-- The answer `D q` comes after an `F t` with `lb ≤ t` (if it is in the list). -/
def DOk (q lb : ℕ) : List (Msg V) → Prop
  | [] => True
  | .F t _ :: rest => lb ≤ t ∨ DOk q lb rest
  | .D j :: rest => j ≠ q ∧ DOk q lb rest
  | _ :: rest => DOk q lb rest

/-- Reads-from data for the completed reads. -/
def RFOk (C : Cfg n V v₀) (α : Hist n V v₀) (rf : ℕ → ℕ) : Prop :=
  ∀ j < (respsOf α .rd).length,
    respOf α (.rd, j) = some (wv α (rf j)) ∧ rf j ≤ (C.loc .rd).2.best ∧ rf j ≤ K α ∧
    (0 < rf j → ¬ Precedes α (.rd, j) (.wr, rf j - 1)) ∧ ¬ Precedes α (.wr, rf j) (.rd, j) ∧
    ∀ j' < (respsOf α .rd).length, j ≤ j' → rf j ≤ rf j'

/-- The current read: `lb` bounds the writes that completed before it was invoked. -/
def CurOk (C : Cfg n V v₀) (α : Hist n V v₀) : Prop :=
  (C.loc .rd).2.resp.card < qs ∧ ∃ lb,
    (∀ m, Precedes α (.wr, m) (.rd, (C.loc .rd).2.q - 1) → m < lb) ∧
    (lb = 0 ∨ ∃ G : Finset (Fin n), qs ≤ G.card ∧ ∀ i ∈ G, lb ≤ pp C i ∧
      (i ∈ (C.loc .rd).2.resp → lb ≤ (C.loc .rd).2.best) ∧
      (lb ≤ (C.loc .rd).2.best ∨ DOk (C.loc .rd).2.q lb (C.chan (.srv i) .rd)))

/-- The invariant. -/
structure Inv (C : Cfg n V v₀) (α : Hist n V v₀) : Prop where
  wk : (C.loc .wr).1.k = K α
  wbusy : (C.loc .wr).1.busy = true ↔ C.pend .wr ≠ none
  wcur : (C.loc .wr).1.busy = true → (C.loc .wr).1.cur = wv α (K α)
  wresp : ∀ j < (respsOf α .wr).length, respOf α (.wr, j) = some (wv α (j + 1))
  chW : ∀ i, pp C i ≤ K α ∧ C.chan .wr (.srv i) = wlist α (pp C i)
  chA : ∀ i, ∀ m ∈ C.chan (.srv i) .wr, ∃ t, m = .A t ∧ t ≤ pp C i
  wacked : (C.loc .wr).1.busy = true →
    (∀ i ∈ (C.loc .wr).1.acked, K α ≤ pp C i) ∧ (C.loc .wr).1.acked.card < qs
  wq : qs ≤ (Finset.univ.filter fun i => (respsOf α .wr).length ≤ pp C i).card
  chR : ∀ i, ∀ m ∈ C.chan (.srv i) .rd,
    (∃ t v, m = .F t v ∧ 1 ≤ t ∧ t ≤ pp C i ∧ v = wv α t) ∨
      ∃ j, m = .D j ∧ j ≤ (C.loc .rd).2.q
  invF : ∀ i t, 1 ≤ t → t ≤ pp C i →
    t ≤ (C.loc .rd).2.best ∨ ∃ v, Msg.F t v ∈ C.chan (.srv i) .rd
  rq : (C.loc .rd).2.q = (opsOf α .rd).length
  rbusy : (C.loc .rd).2.busy = true ↔ C.pend .rd ≠ none
  rbest : (C.loc .rd).2.best ≤ K α
  rval : (C.loc .rd).2.val = wv α (C.loc .rd).2.best
  chQ : ∀ i, ∀ m ∈ C.chan .rd (.srv i), ∃ j, m = .Q j ∧ j ≤ (C.loc .rd).2.q
  rcur : (C.loc .rd).2.busy = true → CurOk qs C α
  rf : ∃ rf, RFOk C α rf
  other : ∀ a b, ¬ OkPair a b → C.chan a b = []

/-! ### Helper lemmas -/

lemma msgsTo_toAll_srv (m : Msg V) (i : Fin n) :
    msgsTo (toAll (n := n) m) (.srv i) = [m] := by
  simp only [msgsTo, toAll, List.filter_map, List.map_map]
  have : ((List.finRange n).filter ((fun x : Node n × Msg V => decide (x.1 = .srv i)) ∘
      fun j => (Node.srv j, m))) = [i] := by
    have h : ((fun x : Node n × Msg V => decide (x.1 = .srv i)) ∘ fun j => (Node.srv j, m)) =
        fun j => decide (j = i) := by
      funext j; simp
    rw [h, List.filter_eq]
    simp [List.count_finRange]
  rw [this]; rfl

lemma msgsTo_toAll_wr (m : Msg V) : msgsTo (toAll (n := n) m) .wr = [] := by
  simp [msgsTo, toAll, List.filter_map]

lemma msgsTo_toAll_rd (m : Msg V) : msgsTo (toAll (n := n) m) .rd = [] := by
  simp [msgsTo, toAll, List.filter_map]

lemma wv_append_of_le {α β : Hist n V v₀} (hβ : ∀ l ∈ β, l.invOf .wr = none) (t : ℕ) :
    wv (α ++ β) t = wv α t := by
  have : opsOf β .wr = [] := by
    simp only [opsOf, List.filterMap_eq_nil_iff]; exact hβ
  simp [wv, opsOf_append, this]

lemma DOk.append_F {q lb : ℕ} {ch : List (Msg V)} (h : DOk q lb ch) (t : ℕ) (v : V) :
    DOk q lb (ch ++ [.F t v]) := by
  induction ch with
  | nil => simp [DOk]
  | cons m ch ih =>
    rcases m with _ | _ | ⟨t', v'⟩ | _ | j
    all_goals simp only [DOk, List.cons_append] at h ⊢
    all_goals first | exact ih h | exact ⟨h.1, ih h.2⟩ | exact h.imp_right ih

lemma DOk.append_D {q lb : ℕ} {ch : List (Msg V)} (h : DOk q lb ch) (j : ℕ)
    (hj : j = q → ∃ t v, Msg.F t v ∈ ch ∧ lb ≤ t) : DOk q lb (ch ++ [.D j]) := by
  induction ch with
  | nil =>
    simp only [List.nil_append, DOk, and_true]
    rintro rfl; obtain ⟨t, v, h, -⟩ := hj rfl; simp at h
  | cons m ch ih =>
    rcases m with _ | _ | ⟨t', v'⟩ | _ | j'
    all_goals simp only [DOk, List.cons_append, List.mem_cons] at h hj ⊢
    · exact ih h (fun hq => by obtain ⟨t, v, h1, h2⟩ := hj hq; simp at h1; exact ⟨t, v, h1, h2⟩)
    · exact ih h (fun hq => by obtain ⟨t, v, h1, h2⟩ := hj hq; simp at h1; exact ⟨t, v, h1, h2⟩)
    · rcases h with h | h
      · exact Or.inl h
      · by_cases hq : j = q
        · obtain ⟨t, v, h1, h2⟩ := hj hq
          rcases h1 with h1 | h1
          · simp only [Msg.F.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1; exact Or.inl h2
          · exact Or.inr (ih h (fun _ => ⟨t, v, h1, h2⟩))
        · exact Or.inr (ih h (fun h' => absurd h' hq))
    · exact ih h (fun hq => by obtain ⟨t, v, h1, h2⟩ := hj hq; simp at h1; exact ⟨t, v, h1, h2⟩)
    · exact ⟨h.1, ih h.2 (fun hq => by obtain ⟨t, v, h1, h2⟩ := hj hq; simp at h1; exact ⟨t, v, h1, h2⟩)⟩

lemma DOk.of_no_D {q lb : ℕ} {ch : List (Msg V)} (h : ∀ j, Msg.D j ∈ ch → j ≠ q) :
    DOk q lb ch := by
  induction ch with
  | nil => trivial
  | cons m ch ih =>
    have h' : ∀ j, Msg.D j ∈ ch → j ≠ q := fun j hj => h j (by simp [hj])
    rcases m with _ | _ | ⟨t', v'⟩ | _ | j'
    all_goals simp only [DOk]
    · exact ih h'
    · exact ih h'
    · exact Or.inr (ih h')
    · exact ih h'
    · exact ⟨h j' (by simp), ih h'⟩

lemma DOk.tail {q lb : ℕ} {m : Msg V} {ch : List (Msg V)} (h : DOk q lb (m :: ch)) :
    DOk q lb ch ∨ ∃ t v, m = .F t v ∧ lb ≤ t := by
  rcases m with _ | _ | ⟨t', v'⟩ | _ | j'
  all_goals simp only [DOk] at h
  · exact Or.inl h
  · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr ⟨t', v', rfl, h⟩
    · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h.2

lemma DOk.not_D {q lb : ℕ} {ch : List (Msg V)} (h : DOk q lb (.D q :: ch)) : False := by
  simp [DOk] at h

/-! ### The initial configuration -/

theorem inv_init (hqn : qs ≤ n) : Inv qs (relay v₀ qs).initCfg ([] : Hist n V v₀) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ⟨id, ?_⟩, ?_⟩
  all_goals simp [Algorithm.initCfg, relay, lInit, wlist, RFOk, pp, K]
  exact hqn

/-! ### Steps -/

lemma step_deliver_eq (C : Cfg n V v₀) {a b : Node n} {m : Msg V} {rest : List (Msg V)}
    (hc : C.chan a b = m :: rest) :
    (relay v₀ qs).step C (.deliver a b) =
      (C.pop a b rest).apply b (handle qs b (.recv a m) (C.loc b)) := by
  simp [Algorithm.step, hc, relay]

lemma wlist_cons {α : Hist n V v₀} {p : ℕ} (h : p < K α) :
    wlist α p = .W (p + 1) (wv α (p + 1)) :: wlist α (p + 1) := by
  simp only [wlist]
  obtain ⟨d, hd⟩ : ∃ d, K α - p = d + 1 := ⟨K α - p - 1, by omega⟩
  rw [hd, List.range_succ_eq_map]
  have : K α - (p + 1) = d := by omega
  rw [this]
  simp only [List.map_cons, List.map_map]
  congr 2
  funext j
  simp only [Function.comp, Nat.succ_eq_add_one]
  rw [show p + 1 + (j + 1) = p + 1 + 1 + j by omega]

lemma wlist_eq_nil {α : Hist n V v₀} {p : ℕ} (h : K α ≤ p) : wlist α p = [] := by
  simp [wlist, Nat.sub_eq_zero_of_le h]

/-- Delivery of `W t v` to server `i`. -/
theorem inv_deliver_W {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α) {i : Fin n}
    {t : ℕ} {v : V} {rest : List (Msg V)} (hc : C.chan .wr (.srv i) = .W t v :: rest) :
    Inv qs ((relay v₀ qs).step C (.deliver .wr (.srv i))).1
      (α ++ ((relay v₀ qs).step C (.deliver .wr (.srv i))).2) := by
  rw [step_deliver_eq qs C hc]
  obtain ⟨hpK, hW⟩ := hI.chW i
  have hlt : pp C i < K α := by
    by_contra h; rw [wlist_eq_nil (by omega)] at hW; rw [hW] at hc; simp at hc
  rw [wlist_cons hlt, hc] at hW
  simp only [List.cons.injEq, Msg.W.injEq] at hW
  obtain ⟨⟨rfl, rfl⟩, hrest⟩ := hW
  set C' := ((C.pop .wr (.srv i) rest).apply (.srv i)
    (handle qs (.srv i) (.recv .wr (.W (pp C i + 1) (wv α (pp C i + 1)))) (C.loc (.srv i)))).1
  have hl : ((C.pop .wr (.srv i) rest).apply (.srv i)
    (handle qs (.srv i) (.recv .wr (.W (pp C i + 1) (wv α (pp C i + 1)))) (C.loc (.srv i)))).2 = [] := by
    simp [Config.apply, handle, respOut]
  rw [hl, List.append_nil]
  have hloc : C'.loc = C.loc := by simp [C', Config.apply, Config.pop, handle]
  have hpend : C'.pend = C.pend := by
    funext x; by_cases hx : x = .srv i
    · subst hx; simp [C', Config.apply, Config.pop, handle, pendAfter]
    · simp [C', Config.apply, Config.pop, handle, Function.update_of_ne hx]
  have hdlv : ∀ x y, C'.dlv x y = if x = .wr ∧ y = .srv i then C.dlv x y + 1 else C.dlv x y := by
    intro x y; simp [C', Config.apply, Config.pop]
  have hpp : ∀ j, pp C' j = if j = i then pp C i + 1 else pp C j := by
    intro j; simp only [pp, hdlv]; by_cases hj : j = i <;> simp [hj]
  have hpp_le : ∀ j, pp C j ≤ pp C' j := by
    intro j; rw [hpp]; split_ifs with h
    · subst h; omega
    · omega
  have hch : ∀ x y, C'.chan x y =
      (if x = .wr ∧ y = .srv i then rest else C.chan x y) ++
        (if x = .srv i then
          (if y = .rd then [.F (pp C i + 1) (wv α (pp C i + 1))] else []) ++
          (if y = .wr then [.A (pp C i + 1)] else []) else []) := by
    intro x y
    by_cases hx : x = .srv i
    · subst hx
      rcases y with j | _ | _ <;> simp [C', Config.apply, Config.pop, handle, msgsTo]
    · simp [C', Config.apply, Config.pop, hx]
  refine ⟨?_, ?_, ?_, hI.wresp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc]; exact hI.wk
  · rw [hloc, hpend]; exact hI.wbusy
  · rw [hloc]; exact hI.wcur
  · intro j
    rw [hpp, hch]
    by_cases hj : j = i
    · subst hj; simp [hrest]; omega
    · simp [hj, (hI.chW j).2]; exact (hI.chW j).1
  · intro j m hm
    rw [hch] at hm
    by_cases hj : j = i
    · subst hj
      simp only [Node.srv.injEq, and_false, ite_false, ite_true, reduceCtorEq] at hm
      simp only [List.mem_append, List.mem_singleton, List.nil_append] at hm
      rcases hm with hm | rfl
      · obtain ⟨t, rfl, ht⟩ := hI.chA j m hm; exact ⟨t, rfl, by rw [hpp]; simp; omega⟩
      · exact ⟨_, rfl, by rw [hpp]; simp⟩
    · simp [hj] at hm
      obtain ⟨t, rfl, ht⟩ := hI.chA j m hm; exact ⟨t, rfl, by rw [hpp]; simp [hj]; exact ht⟩
  · intro hb; rw [hloc] at hb ⊢
    exact ⟨fun j hj => ((hI.wacked hb).1 j hj).trans (hpp_le j), (hI.wacked hb).2⟩
  · refine hI.wq.trans (Finset.card_le_card ?_)
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.trans (hpp_le j)
  · intro j m hm
    rw [hch] at hm
    rw [hloc]
    by_cases hj : j = i
    · subst hj
      simp only [Node.srv.injEq, and_false, ite_false, ite_true, reduceCtorEq] at hm
      simp only [List.mem_append, List.mem_singleton, List.append_nil] at hm
      rcases hm with hm | rfl
      · rcases hI.chR j m hm with ⟨t, v, rfl, h1, h2, h3⟩ | h
        · exact Or.inl ⟨t, v, rfl, h1, by rw [hpp]; simp; omega, h3⟩
        · exact Or.inr h
      · exact Or.inl ⟨_, _, rfl, by omega, by rw [hpp]; simp, rfl⟩
    · simp [hj] at hm
      rcases hI.chR j m hm with ⟨t, v, rfl, h1, h2, h3⟩ | h
      · exact Or.inl ⟨t, v, rfl, h1, by rw [hpp]; simp [hj]; exact h2, h3⟩
      · exact Or.inr h
  · intro j t h1 h2
    rw [hloc, hch]
    by_cases hj : j = i
    · subst hj
      simp only [Node.srv.injEq, and_false, ite_false, ite_true, reduceCtorEq, List.append_nil,
        List.mem_append, List.mem_singleton]
      rw [hpp] at h2; simp at h2
      rcases Nat.lt_or_ge t (pp C j + 1) with h | h
      · rcases hI.invF j t h1 (by omega) with h' | ⟨v, hv⟩
        · exact Or.inl h'
        · exact Or.inr ⟨v, Or.inl hv⟩
      · exact Or.inr ⟨_, Or.inr (by rw [show t = pp C j + 1 by omega])⟩
    · rw [hpp] at h2; simp [hj] at h2 ⊢; exact hI.invF j t h1 h2
  · rw [hloc]; exact hI.rq
  · rw [hloc, hpend]; exact hI.rbusy
  · rw [hloc]; exact hI.rbest
  · rw [hloc]; exact hI.rval
  · intro j m hm; rw [hch] at hm; rw [hloc]; simpa using hI.chQ j m (by simpa using hm)
  · intro hb; rw [hloc] at hb; unfold CurOk; rw [hloc]
    obtain ⟨hr, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hr, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun j hj => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG j hj
    refine ⟨g1.trans (hpp_le j), g2, g3.imp_right fun hd => ?_⟩
    rw [hch]
    by_cases hji : j = i
    · subst hji; simpa using hd.append_F _ _
    · simpa [hji] using hd
  · obtain ⟨rf, hrf⟩ := hI.rf; exact ⟨rf, by simpa [RFOk, hloc] using hrf⟩
  · intro x y hxy
    rw [hch]
    have := hI.other x y hxy
    rcases x with j | _ | _ <;> rcases y with j' | _ | _ <;> simp_all [OkPair]

/-- Delivery of the query `Q j` to server `i`. -/
theorem inv_deliver_Q {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α) {i : Fin n}
    {j : ℕ} {rest : List (Msg V)} (hc : C.chan .rd (.srv i) = .Q j :: rest) :
    Inv qs ((relay v₀ qs).step C (.deliver .rd (.srv i))).1
      (α ++ ((relay v₀ qs).step C (.deliver .rd (.srv i))).2) := by
  rw [step_deliver_eq qs C hc]
  have hjq : j ≤ (C.loc .rd).2.q := by
    obtain ⟨j', hj', hjq⟩ := hI.chQ i (.Q j) (by rw [hc]; simp)
    simp only [Msg.Q.injEq] at hj'; omega
  set C' := ((C.pop .rd (.srv i) rest).apply (.srv i)
    (handle qs (.srv i) (.recv .rd (.Q j)) (C.loc (.srv i)))).1
  have hl : ((C.pop .rd (.srv i) rest).apply (.srv i)
    (handle qs (.srv i) (.recv .rd (.Q j)) (C.loc (.srv i)))).2 = [] := by
    simp [Config.apply, handle, respOut]
  rw [hl, List.append_nil]
  have hloc : C'.loc = C.loc := by simp [C', Config.apply, Config.pop, handle]
  have hpend : C'.pend = C.pend := by
    funext x; by_cases hx : x = .srv i
    · subst hx; simp [C', Config.apply, Config.pop, handle, pendAfter]
    · simp [C', Config.apply, Config.pop, handle, Function.update_of_ne hx]
  have hpp : ∀ k, pp C' k = pp C k := by intro k; simp [C', pp, Config.apply, Config.pop]
  have hch : ∀ x y, C'.chan x y =
      (if x = .rd ∧ y = .srv i then rest else C.chan x y) ++
        (if x = .srv i ∧ y = .rd then [.D j] else []) := by
    intro x y
    by_cases hx : x = .srv i
    · subst hx
      rcases y with k | _ | _ <;> simp [C', Config.apply, Config.pop, handle, msgsTo]
    · simp [C', Config.apply, Config.pop, hx]
  refine ⟨?_, ?_, ?_, hI.wresp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc]; exact hI.wk
  · rw [hloc, hpend]; exact hI.wbusy
  · rw [hloc]; exact hI.wcur
  · intro k; rw [hpp, hch]; simpa using hI.chW k
  · intro k m hm; rw [hpp]; rw [hch] at hm; simpa using hI.chA k m (by simpa using hm)
  · intro hb; rw [hloc] at hb ⊢; simpa [hpp] using hI.wacked hb
  · simpa [hpp] using hI.wq
  · intro k m hm
    rw [hch] at hm
    rw [hloc, hpp]
    by_cases hk : k = i
    · subst hk
      simp only [true_and, List.mem_append, List.mem_ite_nil_right, List.mem_singleton,
        and_false, ite_false, reduceCtorEq] at hm
      rcases hm with hm | rfl
      · exact hI.chR k m hm
      · exact Or.inr ⟨_, rfl, hjq⟩
    · simp [hk] at hm; exact hI.chR k m hm
  · intro k t h1 h2
    rw [hloc, hch]; rw [hpp] at h2
    rcases hI.invF k t h1 h2 with h | ⟨v, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, by simp [hv]⟩
  · rw [hloc]; exact hI.rq
  · rw [hloc, hpend]; exact hI.rbusy
  · rw [hloc]; exact hI.rbest
  · rw [hloc]; exact hI.rval
  · intro k m hm; rw [hch] at hm; rw [hloc]
    by_cases hk : k = i
    · subst hk; simp only [and_self, ite_true, reduceCtorEq, and_false, ite_false,
        List.append_nil] at hm
      exact hI.chQ k m (by rw [hc]; simp [hm])
    · simpa [hk] using hI.chQ k m (by simpa [hk] using hm)
  · intro hb; rw [hloc] at hb; unfold CurOk; rw [hloc]
    obtain ⟨hr, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hr, lb, hlb, ?_⟩
    rcases hG with h0 | ⟨G, hGc, hG⟩
    · exact Or.inl h0
    · by_cases h0 : lb = 0
      · exact Or.inl h0
      refine Or.inr ⟨G, hGc, fun k hk => ?_⟩
      obtain ⟨g1, g2, g3⟩ := hG k hk
      refine ⟨by rw [hpp]; exact g1, g2, ?_⟩
      rcases g3 with g3 | hd
      · exact Or.inl g3
      rw [hch]
      by_cases hki : k = i
      · subst hki
        simp only [Node.srv.injEq, and_true, reduceCtorEq, and_false, ite_false, ite_true]
        rcases hI.invF k lb (by omega) g1 with h | ⟨v, hv⟩
        · exact Or.inl h
        · exact Or.inr (hd.append_D j (fun _ => ⟨lb, v, hv, le_rfl⟩))
      · right; simpa [hki] using hd
  · obtain ⟨rf, hrf⟩ := hI.rf; exact ⟨rf, by simpa [RFOk, hloc] using hrf⟩
  · intro x y hxy
    rw [hch]
    have := hI.other x y hxy
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;> simp_all [OkPair]

/-- Delivery of `F t v` from server `i` to the reader. -/
theorem inv_deliver_F {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α) {i : Fin n}
    {t : ℕ} {v : V} {rest : List (Msg V)} (hc : C.chan (.srv i) .rd = .F t v :: rest) :
    Inv qs ((relay v₀ qs).step C (.deliver (.srv i) .rd)).1
      (α ++ ((relay v₀ qs).step C (.deliver (.srv i) .rd)).2) := by
  rw [step_deliver_eq qs C hc]
  have hm := hI.chR i (.F t v) (by rw [hc]; simp)
  obtain ⟨ht1, htp, hv⟩ : 1 ≤ t ∧ t ≤ pp C i ∧ v = wv α t := by
    rcases hm with ⟨t', v', he, h1, h2, h3⟩ | ⟨j, he, -⟩
    · simp only [Msg.F.injEq] at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨h1, h2, h3⟩
    · simp at he
  set C' := ((C.pop (.srv i) .rd rest).apply .rd
    (handle qs .rd (.recv (.srv i) (.F t v)) (C.loc .rd))).1
  have hl : ((C.pop (.srv i) .rd rest).apply .rd
    (handle qs .rd (.recv (.srv i) (.F t v)) (C.loc .rd))).2 = [] := by
    simp only [Config.apply, handle]; split_ifs <;> simp [respOut]
  rw [hl, List.append_nil]
  set r := (C.loc .rd).2
  have hlocw : C'.loc .wr = C.loc .wr := by simp [C', Config.apply, Config.pop]
  have hlocrd : C'.loc .rd = ((C.loc .rd).1, ⟨r.q, r.busy, max r.best t,
      if r.best < t then v else r.val, r.resp⟩) := by
    simp only [C', Config.apply, Config.pop, Function.update_self, handle]
    split_ifs with h
    · simp [r, max_eq_right h.le]
    · simp [r, max_eq_left (not_lt.1 h)]
  have hpend : C'.pend = C.pend := by
    funext x; by_cases hx : x = .rd
    · subst hx; simp only [C', Config.apply, Config.pop, Function.update_self, handle]
      split_ifs <;> simp [pendAfter]
    · simp [C', Config.apply, Config.pop, Function.update_of_ne hx]
  have hpp : ∀ k, pp C' k = pp C k := by intro k; simp [C', pp, Config.apply, Config.pop]
  have hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .rd then rest else C.chan x y := by
    intro x y; simp only [C', Config.apply, Config.pop, handle]; split_ifs <;> simp_all [msgsTo]
  have hbest : r.best ≤ max r.best t := le_max_left _ _
  refine ⟨?_, ?_, ?_, hI.wresp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlocw]; exact hI.wk
  · rw [hlocw, hpend]; exact hI.wbusy
  · rw [hlocw]; exact hI.wcur
  · intro k; rw [hpp, hch]; simpa using hI.chW k
  · intro k m hm; rw [hpp]; rw [hch] at hm; simp at hm; exact hI.chA k m hm
  · intro hb; rw [hlocw] at hb ⊢; simpa [hpp] using hI.wacked hb
  · simpa [hpp] using hI.wq
  · intro k m hm
    rw [hch] at hm; rw [hlocrd, hpp]
    have hm' : m ∈ C.chan (.srv k) .rd := by
      by_cases hk : k = i
      · subst hk; simp only [and_self, ite_true] at hm; rw [hc]; simp [hm]
      · simpa [hk] using hm
    exact hI.chR k m hm'
  · intro k t' h1 h2
    rw [hlocrd, hch]; rw [hpp] at h2
    rcases hI.invF k t' h1 h2 with h | ⟨v', hv'⟩
    · exact Or.inl (h.trans hbest)
    · by_cases hk : k = i
      · subst hk
        rw [hc] at hv'
        simp only [List.mem_cons, Msg.F.injEq] at hv'
        rcases hv' with ⟨rfl, rfl⟩ | hv'
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr ⟨v', by simp [hv']⟩
      · exact Or.inr ⟨v', by simpa [hk] using hv'⟩
  · rw [hlocrd]; exact hI.rq
  · rw [hlocrd, hpend]; exact hI.rbusy
  · rw [hlocrd]; exact max_le hI.rbest (htp.trans (hI.chW i).1)
  · rw [hlocrd]
    simp only
    split_ifs with h
    · rw [max_eq_right h.le, hv]
    · rw [max_eq_left (not_lt.1 h)]; exact hI.rval
  · intro k m hm; rw [hch] at hm; rw [hlocrd]; simpa using hI.chQ k m (by simpa using hm)
  · intro hb; rw [hlocrd] at hb; unfold CurOk; rw [hlocrd]
    obtain ⟨hr, lb, hlb, hG⟩ := hI.rcur hb
    refine ⟨hr, lb, hlb, hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun k hk => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG k hk
    refine ⟨by rw [hpp]; exact g1, fun h => (g2 h).trans hbest, ?_⟩
    rcases g3 with g3 | hd
    · exact Or.inl (g3.trans hbest)
    rw [hch]
    by_cases hki : k = i
    · subst hki
      simp only [and_self, ite_true]
      rw [hc] at hd
      rcases hd.tail with hd | ⟨t', v', he, hlt⟩
      · exact Or.inr hd
      · simp only [Msg.F.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        exact Or.inl (hlt.trans (le_max_right _ _))
    · right; simpa [hki] using hd
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hrf j hj
    exact ⟨h1, by rw [hlocrd]; exact h2.trans hbest, h3⟩
  · intro x y hxy
    rw [hch]
    have := hI.other x y hxy
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;> simp_all [OkPair]

/-- Frame lemma for steps of the writer that receive an acknowledgement: the reader side of
the invariant carries over. -/
theorem inv_of_wr_change {C C' : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) {i : Fin n} {m : Msg V} {rest : List (Msg V)}
    (hc : C.chan (.srv i) .wr = m :: rest) (β : Hist n V v₀)
    (hβ : β = [] ∨ ∃ x, β = [.ret .wr x])
    (hlocrd : C'.loc .rd = C.loc .rd) (hpendrd : C'.pend .rd = C.pend .rd)
    (hpp : ∀ k, pp C' k = pp C k)
    (hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .wr then rest else C.chan x y)
    (wk : (C'.loc .wr).1.k = K (α ++ β))
    (wbusy : (C'.loc .wr).1.busy = true ↔ C'.pend .wr ≠ none)
    (wcur : (C'.loc .wr).1.busy = true → (C'.loc .wr).1.cur = wv (α ++ β) (K (α ++ β)))
    (wresp : ∀ j < (respsOf (α ++ β) .wr).length,
      respOf (α ++ β) (.wr, j) = some (wv (α ++ β) (j + 1)))
    (wacked : (C'.loc .wr).1.busy = true →
      (∀ k ∈ (C'.loc .wr).1.acked, K (α ++ β) ≤ pp C' k) ∧ (C'.loc .wr).1.acked.card < qs)
    (wq : qs ≤ (Finset.univ.filter fun k => (respsOf (α ++ β) .wr).length ≤ pp C' k).card) :
    Inv qs C' (α ++ β) := by
  have hβi : ∀ l ∈ β, ∀ p, l.invOf p = none := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.invOf]
  have hβr : ∀ l ∈ β, l.proc ≠ .rd := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.proc]
  have hops : ∀ p, opsOf (α ++ β) p = opsOf α p := by
    intro p
    have : opsOf β p = [] := by
      simp only [opsOf, List.filterMap_eq_nil_iff]; exact fun l hl => hβi l hl p
    simp [this]
  have hK : K (α ++ β) = K α := by simp [K, hops]
  have hwv : ∀ t, wv (α ++ β) t = wv α t := by intro t; simp [wv, hops]
  have hrr : respsOf (α ++ β) .rd = respsOf α .rd := by
    rw [respsOf_append, respsOf_eq_nil_of_proc_ne hβr, List.append_nil]
  have hrespOf : ∀ j, respOf (α ++ β) (.rd, j) = respOf α (.rd, j) := by
    intro j; simp [respOf, hrr]
  have hprec_rd : ∀ x j, j < (opsOf α .rd).length →
      (Precedes (α ++ β) x (.rd, j) ↔ Precedes α x (.rd, j)) :=
    fun x j hj => precedes_append_iff_of_invoked hj
  have hprec_wr : ∀ x j, j < K α →
      (Precedes (α ++ β) x (.wr, j) ↔ Precedes α x (.wr, j)) :=
    fun x j hj => precedes_append_iff_of_invoked hj
  refine ⟨wk, wbusy, wcur, wresp, ?_, ?_, wacked, wq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; rw [hpp, hch]
    simp only [reduceCtorEq, and_false, ite_false]
    obtain ⟨h1, h2⟩ := hI.chW k
    refine ⟨by rw [hK]; exact h1, ?_⟩
    rw [h2]; simp [wlist, hK, hwv]
  · intro k m' hm; rw [hpp]; rw [hch] at hm
    by_cases hk : k = i
    · subst hk; simp only [and_self, ite_true] at hm
      exact hI.chA k m' (by rw [hc]; simp [hm])
    · simp [hk] at hm; exact hI.chA k m' hm
  · intro k m' hm; rw [hch] at hm; simp at hm; rw [hlocrd, hpp]
    simpa [hwv] using hI.chR k m' hm
  · intro k t h1 h2; rw [hpp] at h2; rw [hlocrd, hch]; simpa using hI.invF k t h1 h2
  · rw [hlocrd, hops]; exact hI.rq
  · rw [hlocrd, hpendrd]; exact hI.rbusy
  · rw [hlocrd, hK]; exact hI.rbest
  · rw [hlocrd, hwv]; exact hI.rval
  · intro k m' hm; rw [hch] at hm; simp at hm; rw [hlocrd]; exact hI.chQ k m' hm
  · intro hb; rw [hlocrd] at hb; unfold CurOk; rw [hlocrd]
    obtain ⟨hr, lb, hlb, hG⟩ := hI.rcur hb
    have hq1 : (C.loc .rd).2.q - 1 < (opsOf α .rd).length := by
      have h1 := hacc .rd
      have h2 : C.pend .rd ≠ none := hI.rbusy.1 hb
      simp only [pendCount, Option.isNone_iff_eq_none, h2, ite_false] at h1
      rw [hI.rq]; omega
    refine ⟨hr, lb, fun m' hm => hlb m' ((hprec_rd _ _ hq1).1 hm), ?_⟩
    rcases hG with h0 | ⟨G, hGc, hG⟩
    · exact Or.inl h0
    · refine Or.inr ⟨G, hGc, fun k hk => ?_⟩
      obtain ⟨g1, g2, g3⟩ := hG k hk
      exact ⟨by rw [hpp]; exact g1, g2, by rw [hch]; simpa using g3⟩
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨by rw [hrespOf, hwv]; exact h1, by rw [hlocrd]; exact h2, by rw [hK]; exact h3,
      fun h0 hp => h4 h0 ((hprec_wr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprec_rd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
  · intro x y hxy
    rw [hch]
    have := hI.other x y hxy
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;> simp_all [OkPair]

/-- Delivery of an acknowledgement `A t` from server `i` to the writer. -/
theorem inv_deliver_A {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α) (hacc : Acc α C)
    {i : Fin n} {t : ℕ} {rest : List (Msg V)} (hc : C.chan (.srv i) .wr = .A t :: rest) :
    Inv qs ((relay v₀ qs).step C (.deliver (.srv i) .wr)).1
      (α ++ ((relay v₀ qs).step C (.deliver (.srv i) .wr)).2) := by
  rw [step_deliver_eq qs C hc]
  have htp : t ≤ pp C i := by
    obtain ⟨t', he, h⟩ := hI.chA i (.A t) (by rw [hc]; simp)
    simp only [Msg.A.injEq] at he; omega
  set w := (C.loc .wr).1 with hw
  set r := (C.loc .wr).2
  have hcl : C.loc .wr = (w, r) := rfl
  have hpp : ∀ k, pp ((C.pop (.srv i) .wr rest).apply .wr
      (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1 k = pp C k := by
    intro k; simp [pp, Config.apply, Config.pop]
  have hlocrd : ((C.pop (.srv i) .wr rest).apply .wr
      (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1.loc .rd = C.loc .rd := by
    simp [Config.apply, Config.pop]
  have hpendrd : ((C.pop (.srv i) .wr rest).apply .wr
      (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1.pend .rd = C.pend .rd := by
    simp [Config.apply, Config.pop]
  have hch : ∀ x y, ((C.pop (.srv i) .wr rest).apply .wr
      (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1.chan x y =
      if x = .srv i ∧ y = .wr then rest else C.chan x y := by
    have hout : (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr)).2.1 = [] := by
      rw [hcl]; simp only [handle]; split_ifs <;> rfl
    intro x y
    simp only [Config.apply, Config.pop, hout]
    by_cases hx : x = .wr
    · subst hx; simp [msgsTo]
    · simp [hx]
  by_cases hcond : w.busy = true ∧ t = w.k
  · obtain ⟨hb, rfl⟩ := hcond
    have hpw : C.pend .wr ≠ none := hI.wbusy.1 hb
    have hKc : K α = (respsOf α .wr).length + 1 := by
      have := hacc .wr
      simp only [pendCount, Option.isNone_iff_eq_none, hpw, ite_false] at this
      exact this
    by_cases hq : qs ≤ (insert i w.acked).card
    · -- the write returns
      have hstep : handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr) =
          ((⟨w.k, false, w.cur, insert i w.acked⟩, r), [], some w.cur) := by
        rw [hcl]; simp [handle, hb, hq]
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpw
      have hlab : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).2 = [.ret .wr w.cur] := by
        rw [hstep]; simp [Config.apply, Config.pop, respOut, ho]
      rw [hlab]
      have hlocw : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).1.loc .wr =
          (⟨w.k, false, w.cur, insert i w.acked⟩, r) := by
        rw [hstep]; simp [Config.apply]
      have hpendw : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).1.pend .wr = none := by
        rw [hstep]; simp [Config.apply, Config.pop, pendAfter, ho]
      have hK' : K (α ++ [.ret .wr w.cur]) = K α := by simp [K]
      have hwv' : ∀ s, wv (α ++ [.ret .wr w.cur]) s = wv α s := by intro s; simp [wv]
      have hrw : (respsOf (α ++ [.ret .wr w.cur]) .wr).length = K α := by simp [hKc]
      refine inv_of_wr_change qs hI hacc hc _ (Or.inr ⟨_, rfl⟩) hlocrd hpendrd hpp hch ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hlocw, hK']; exact hI.wk
      · rw [hlocw, hpendw]; simp
      · rw [hlocw]; simp
      · intro j hj
        rw [hrw] at hj
        rw [hwv']
        by_cases hjc : j < (respsOf α .wr).length
        · rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hjc)]
          exact hI.wresp j hjc
        · have hj' : j = (respsOf α .wr).length := by omega
          subst hj'
          simp only [respOf, respsOf_append, respsOf_cons, respsOf_nil, List.append_nil]
          rw [List.getElem?_append_right le_rfl]
          simp only [Label.retOf, ite_true, List.getElem?_cons_zero, Nat.sub_self,
            Option.toList_some, List.filterMap_cons, List.filterMap_nil, Option.some.injEq]
          rw [← hKc]; exact hI.wcur hb
      · rw [hlocw]; simp
      · rw [hrw]
        refine hq.trans (Finset.card_le_card ?_)
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpp]
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [← hI.wk]; exact htp
        · exact (hI.wacked hb).1 k hk
    · -- an acknowledgement is recorded
      have hstep : handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr) =
          ((⟨w.k, true, w.cur, insert i w.acked⟩, r), [], none) := by
        rw [hcl]; simp [handle, hb, hq]
      have hlab : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).2 = [] := by
        rw [hstep]; simp [Config.apply, respOut]
      rw [hlab]
      have hlocw : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).1.loc .wr =
          (⟨w.k, true, w.cur, insert i w.acked⟩, r) := by
        rw [hstep]; simp [Config.apply]
      have hpendw : ((C.pop (.srv i) .wr rest).apply .wr
          (handle qs .wr (.recv (.srv i) (.A w.k)) (C.loc .wr))).1.pend .wr = C.pend .wr := by
        rw [hstep]; rcases h : C.pend .wr <;> simp [Config.apply, Config.pop, pendAfter, h]
      refine inv_of_wr_change qs hI hacc hc _ (Or.inl rfl) hlocrd hpendrd hpp hch ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hlocw, List.append_nil]; exact hI.wk
      · rw [hlocw, hpendw]; simpa using hpw
      · rw [hlocw, List.append_nil]; intro _; exact hI.wcur hb
      · simpa using hI.wresp
      · rw [hlocw, List.append_nil]
        intro _
        refine ⟨fun k hk => ?_, by show (insert i w.acked).card < qs; omega⟩
        rw [hpp]
        rcases Finset.mem_insert.1 hk with rfl | hk
        · rw [← hI.wk]; exact htp
        · exact (hI.wacked hb).1 k hk
      · simpa [hpp] using hI.wq
  · -- ignored
    have hstep : handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr) = (C.loc .wr, [], none) := by
      rw [hcl]; simp only [handle]; rw [ite_eq_right hcond]
    have hlab : ((C.pop (.srv i) .wr rest).apply .wr
        (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).2 = [] := by
      rw [hstep]; simp [Config.apply, respOut]
    rw [hlab]
    have hlocw : ((C.pop (.srv i) .wr rest).apply .wr
        (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1.loc .wr = C.loc .wr := by
      rw [hstep]; simp [Config.apply]
    have hpendw : ((C.pop (.srv i) .wr rest).apply .wr
        (handle qs .wr (.recv (.srv i) (.A t)) (C.loc .wr))).1.pend .wr = C.pend .wr := by
      rw [hstep]; rcases h : C.pend .wr <;> simp [Config.apply, Config.pop, pendAfter, h]
    refine inv_of_wr_change qs hI hacc hc _ (Or.inl rfl) hlocrd hpendrd hpp hch ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hlocw, List.append_nil]; exact hI.wk
    · rw [hlocw, hpendw]; exact hI.wbusy
    · rw [hlocw, List.append_nil]; exact hI.wcur
    · simpa using hI.wresp
    · rw [hlocw, List.append_nil]; simpa [hpp] using hI.wacked
    · simpa [hpp] using hI.wq

/-- Frame lemma for steps of the reader that receive an answer `D j`: the writer side of the
invariant carries over. -/
theorem inv_of_rd_change {C C' : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) {i : Fin n} {j : ℕ} {rest : List (Msg V)}
    (hc : C.chan (.srv i) .rd = .D j :: rest) (β : Hist n V v₀)
    (hβ : β = [] ∨ ∃ x, β = [.ret .rd x])
    (hlocw : C'.loc .wr = C.loc .wr) (hpendw : C'.pend .wr = C.pend .wr)
    (hq : (C'.loc .rd).2.q = (C.loc .rd).2.q) (hbest : (C'.loc .rd).2.best = (C.loc .rd).2.best)
    (hval : (C'.loc .rd).2.val = (C.loc .rd).2.val)
    (hpp : ∀ k, pp C' k = pp C k)
    (hch : ∀ x y, C'.chan x y = if x = .srv i ∧ y = .rd then rest else C.chan x y)
    (rbusy : (C'.loc .rd).2.busy = true ↔ C'.pend .rd ≠ none)
    (rcur : (C'.loc .rd).2.busy = true → CurOk qs C' (α ++ β))
    (rf : ∃ rf, RFOk C' (α ++ β) rf) :
    Inv qs C' (α ++ β) := by
  have hβi : ∀ l ∈ β, ∀ p, l.invOf p = none := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.invOf]
  have hβw : ∀ l ∈ β, l.proc ≠ .wr := by
    rcases hβ with rfl | ⟨x, rfl⟩ <;> simp [Label.proc]
  have hops : ∀ p, opsOf (α ++ β) p = opsOf α p := by
    intro p
    have : opsOf β p = [] := by
      simp only [opsOf, List.filterMap_eq_nil_iff]; exact fun l hl => hβi l hl p
    simp [this]
  have hK : K (α ++ β) = K α := by simp [K, hops]
  have hwv : ∀ t, wv (α ++ β) t = wv α t := by intro t; simp [wv, hops]
  have hrw : respsOf (α ++ β) .wr = respsOf α .wr := by
    rw [respsOf_append, respsOf_eq_nil_of_proc_ne hβw, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rbusy, ?_, ?_, ?_, rcur, rf, ?_⟩
  · rw [hlocw, hK]; exact hI.wk
  · rw [hlocw, hpendw]; exact hI.wbusy
  · rw [hlocw, hK, hwv]; exact hI.wcur
  · intro k hk; rw [hrw] at hk
    simp only [respOf, hrw, hwv]; exact hI.wresp k hk
  · intro k; rw [hpp, hch]
    simp only [reduceCtorEq, and_false, false_and, ite_false]
    obtain ⟨h1, h2⟩ := hI.chW k
    refine ⟨by rw [hK]; exact h1, ?_⟩
    rw [h2]; simp [wlist, hK, hwv]
  · intro k m' hm; rw [hpp]; rw [hch] at hm; simp at hm; exact hI.chA k m' hm
  · intro hb; rw [hlocw, hK] at *; simpa [hpp] using hI.wacked hb
  · simpa [hpp, hrw] using hI.wq
  · intro k m' hm; rw [hch] at hm; rw [hq, hpp]
    have hm' : m' ∈ C.chan (.srv k) .rd := by
      by_cases hk : k = i
      · subst hk; simp only [and_self, ite_true] at hm; rw [hc]; simp [hm]
      · simpa [hk] using hm
    simpa [hwv] using hI.chR k m' hm'
  · intro k t h1 h2; rw [hpp] at h2; rw [hbest, hch]
    rcases hI.invF k t h1 h2 with h | ⟨v, hv⟩
    · exact Or.inl h
    · by_cases hk : k = i
      · subst hk; rw [hc] at hv; simp only [List.mem_cons, reduceCtorEq, false_or] at hv
        exact Or.inr ⟨v, by simp [hv]⟩
      · exact Or.inr ⟨v, by simpa [hk] using hv⟩
  · rw [hq, hops]; exact hI.rq
  · rw [hbest, hK]; exact hI.rbest
  · rw [hval, hbest, hwv]; exact hI.rval
  · intro k m' hm; rw [hch] at hm; simp at hm; rw [hq]; exact hI.chQ k m' hm
  · intro x y hxy
    rw [hch]
    have := hI.other x y hxy
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;> simp_all [OkPair]

lemma DOk.tail_D {q lb j : ℕ} {ch : List (Msg V)} (h : DOk q lb (.D j :: ch)) : DOk q lb ch :=
  (DOk.tail h).resolve_right (by rintro ⟨t, v, he, -⟩; simp at he)

/-- Delivery of an answer `D j` from server `i` to the reader. -/
theorem inv_deliver_D (hq2 : n < 2 * qs) {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) {i : Fin n} {j : ℕ} {rest : List (Msg V)}
    (hc : C.chan (.srv i) .rd = .D j :: rest) :
    Inv qs ((relay v₀ qs).step C (.deliver (.srv i) .rd)).1
      (α ++ ((relay v₀ qs).step C (.deliver (.srv i) .rd)).2) := by
  rw [step_deliver_eq qs C hc]
  set w := (C.loc .rd).1
  set r := (C.loc .rd).2 with hr
  have hcl : C.loc .rd = (w, r) := rfl
  have hout : (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd)).2.1 = [] := by
    rw [hcl]; simp only [handle]; split_ifs <;> rfl
  have hpp : ∀ k, pp ((C.pop (.srv i) .rd rest).apply .rd
      (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1 k = pp C k := by
    intro k; simp [pp, Config.apply, Config.pop]
  have hlocw : ((C.pop (.srv i) .rd rest).apply .rd
      (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1.loc .wr = C.loc .wr := by
    simp [Config.apply, Config.pop]
  have hpendw : ((C.pop (.srv i) .rd rest).apply .rd
      (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1.pend .wr = C.pend .wr := by
    simp [Config.apply, Config.pop]
  have hch : ∀ x y, ((C.pop (.srv i) .rd rest).apply .rd
      (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1.chan x y =
      if x = .srv i ∧ y = .rd then rest else C.chan x y := by
    intro x y
    simp only [Config.apply, Config.pop, hout]
    by_cases hx : x = .rd
    · subst hx; simp [msgsTo]
    · simp [hx]
  -- the current read is not completed in `α`
  have hcur : r.busy = true → (opsOf α .rd).length = (respsOf α .rd).length + 1 := by
    intro hb
    have := hacc .rd
    simp only [pendCount, Option.isNone_iff_eq_none, hI.rbusy.1 hb, ite_false] at this
    exact this
  by_cases hcond : r.busy = true ∧ j = r.q
  · obtain ⟨hb, rfl⟩ := hcond
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
    have hpr : C.pend .rd ≠ none := hI.rbusy.1 hb
    -- `lb ≤ best` once server `i` of `G` has answered
    have hi : ∀ G : Finset (Fin n), (∀ k ∈ G, lb ≤ pp C k ∧ (k ∈ r.resp → lb ≤ r.best) ∧
        (lb ≤ r.best ∨ DOk r.q lb (C.chan (.srv k) .rd))) → i ∈ G → lb ≤ r.best := by
      intro G hG hiG
      rcases (hG i hiG).2.2 with h | h
      · exact h
      · rw [hc] at h; exact h.not_D.elim
    by_cases hqc : qs ≤ (insert i r.resp).card
    · -- the read returns
      have hstep : handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd) =
          ((w, ⟨r.q, false, r.best, r.val, insert i r.resp⟩), [], some r.val) := by
        rw [hcl]; simp [handle, hb, hqc]
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpr
      have hlab : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).2 = [.ret .rd r.val] := by
        rw [hstep]; simp [Config.apply, Config.pop, respOut, ho]
      rw [hlab]
      have hlocr : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).1.loc .rd =
          (w, ⟨r.q, false, r.best, r.val, insert i r.resp⟩) := by
        rw [hstep]; simp [Config.apply]
      have hpendr : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).1.pend .rd = none := by
        rw [hstep]; simp [Config.apply, Config.pop, pendAfter, ho]
      -- quorum intersection
      have hlbb : lb ≤ r.best := by
        rcases hG with h0 | ⟨G, hGc, hG⟩
        · omega
        · obtain ⟨k, hk⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
            (Finset.subset_univ G) (Finset.subset_univ (insert i r.resp))
            (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
          rw [Finset.mem_inter] at hk
          rcases Finset.mem_insert.1 hk.2 with rfl | hk2
          · exact hi G hG hk.1
          · exact (hG k hk.1).2.1 hk2
      have hR := hcur hb
      set R := (respsOf α .rd).length
      have hRq : R = r.q - 1 := by rw [hr, hI.rq]; omega
      have hbK : r.best ≤ K α := hI.rbest
      have hKα : K (α ++ [.ret .rd r.val]) = K α := by simp [K]
      have hwv' : ∀ s, wv (α ++ [.ret .rd r.val]) s = wv α s := by intro s; simp [wv]
      have hRR : (respsOf (α ++ [.ret .rd r.val]) .rd).length = R + 1 := by simp [R]
      refine inv_of_rd_change qs hI hacc hc _ (Or.inr ⟨_, rfl⟩) hlocw hpendw
        (by rw [hlocr]) (by rw [hlocr]) (by rw [hlocr]) hpp hch ?_ ?_ ?_
      · rw [hlocr, hpendr]; simp
      · rw [hlocr]; simp
      · obtain ⟨rf, hrf⟩ := hI.rf
        refine ⟨Function.update rf R r.best, fun j hj => ?_⟩
        rw [hRR] at hj
        rw [hlocr]
        simp only [hwv', hKα]
        have hprd : ∀ x k, k < (opsOf α .rd).length →
            (Precedes (α ++ [.ret .rd r.val]) x (.rd, k) ↔ Precedes α x (.rd, k)) :=
          fun x k hk => precedes_append_iff_of_invoked hk
        have hpwr : ∀ x k, k < K α →
            (Precedes (α ++ [.ret .rd r.val]) x (.wr, k) ↔ Precedes α x (.wr, k)) :=
          fun x k hk => precedes_append_iff_of_invoked hk
        by_cases hjR : j < R
        · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hjR
          rw [Function.update_of_ne (by omega)]
          refine ⟨by rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j)
              from hjR)]; exact h1, h2, h3,
            fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
            fun hp => h5 ((hprd _ _ (by omega)).1 hp), fun j' hj' hjj' => ?_⟩
          rw [hRR] at hj'
          by_cases hj'R : j' = R
          · subst hj'R; rw [Function.update_self]; exact h2
          · rw [Function.update_of_ne hj'R]; exact h6 j' (by omega) hjj'
        · have hjR' : j = R := by omega
          subst hjR'
          rw [Function.update_self]
          refine ⟨?_, le_rfl, hbK, fun h0 hp => ?_, fun hp => ?_, fun j' hj' hjj' => ?_⟩
          · simp only [respOf, respsOf_append, respsOf_cons, respsOf_nil, List.append_nil]
            rw [List.getElem?_append_right le_rfl]
            simp only [Label.retOf, ite_true, List.getElem?_cons_zero, Nat.sub_self,
              Option.toList_some, List.filterMap_cons, List.filterMap_nil, Option.some.injEq]
            exact hI.rval
          · have := ((hpwr _ _ (by omega)).1 hp).completed
            simp [Completed, R] at this
          · rw [hprd _ _ (by omega), hRq] at hp
            have := hlb _ hp
            omega
          · rw [hRR] at hj'
            have : j' = R := by omega
            subst this; rw [Function.update_self]
    · -- the answer is recorded
      have hstep : handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd) =
          ((w, ⟨r.q, true, r.best, r.val, insert i r.resp⟩), [], none) := by
        rw [hcl]; simp [handle, hb, hqc]
      have hlab : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).2 = [] := by
        rw [hstep]; simp [Config.apply, respOut]
      rw [hlab]
      have hlocr : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).1.loc .rd =
          (w, ⟨r.q, true, r.best, r.val, insert i r.resp⟩) := by
        rw [hstep]; simp [Config.apply]
      have hpendr : ((C.pop (.srv i) .rd rest).apply .rd
          (handle qs .rd (.recv (.srv i) (.D r.q)) (C.loc .rd))).1.pend .rd = C.pend .rd := by
        rw [hstep]; rcases h : C.pend .rd <;> simp [Config.apply, Config.pop, pendAfter, h]
      refine inv_of_rd_change qs hI hacc hc _ (Or.inl rfl) hlocw hpendw
        (by rw [hlocr]) (by rw [hlocr]) (by rw [hlocr]) hpp hch ?_ ?_ ?_
      · rw [hlocr, hpendr]; simpa using hpr
      · intro _
        unfold CurOk
        rw [hlocr, List.append_nil]
        refine ⟨by simp only; omega, lb, hlb, hG.imp_right ?_⟩
        rintro ⟨G, hGc, hG'⟩
        refine ⟨G, hGc, fun k hk => ?_⟩
        obtain ⟨g1, g2, g3⟩ := hG' k hk
        refine ⟨by rw [hpp]; exact g1, fun hk' => ?_, ?_⟩
        · rcases Finset.mem_insert.1 hk' with rfl | hk'
          · exact hi G hG' hk
          · exact g2 hk'
        · rw [hch]
          by_cases hki : k = i
          · subst hki; exact Or.inl (hi G hG' hk)
          · simpa [hki] using g3
      · obtain ⟨rf, hrf⟩ := hI.rf
        exact ⟨rf, by simpa [RFOk, hlocr] using hrf⟩
  · -- ignored
    have hstep : handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd) = (C.loc .rd, [], none) := by
      rw [hcl]; simp only [handle]; rw [ite_eq_right hcond]
    have hlab : ((C.pop (.srv i) .rd rest).apply .rd
        (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).2 = [] := by
      rw [hstep]; simp [Config.apply, respOut]
    rw [hlab]
    have hlocr : ((C.pop (.srv i) .rd rest).apply .rd
        (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1.loc .rd = C.loc .rd := by
      rw [hstep]; simp [Config.apply]
    have hpendr : ((C.pop (.srv i) .rd rest).apply .rd
        (handle qs .rd (.recv (.srv i) (.D j)) (C.loc .rd))).1.pend .rd = C.pend .rd := by
      rw [hstep]; rcases h : C.pend .rd <;> simp [Config.apply, Config.pop, pendAfter, h]
    refine inv_of_rd_change qs hI hacc hc _ (Or.inl rfl) hlocw hpendw
      (by rw [hlocr]) (by rw [hlocr]) (by rw [hlocr]) hpp hch ?_ ?_ ?_
    · rw [hlocr, hpendr]; exact hI.rbusy
    · intro hb
      rw [hlocr] at hb
      unfold CurOk
      rw [hlocr, List.append_nil]
      obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb
      refine ⟨hrc, lb, hlb, hG.imp_right ?_⟩
      rintro ⟨G, hGc, hG'⟩
      refine ⟨G, hGc, fun k hk => ?_⟩
      obtain ⟨g1, g2, g3⟩ := hG' k hk
      refine ⟨by rw [hpp]; exact g1, g2, ?_⟩
      rw [hch]
      by_cases hki : k = i
      · subst hki
        simp only [and_self, ite_true]
        rw [hc] at g3
        exact g3.imp_right DOk.tail_D
      · simpa [hki] using g3
    · obtain ⟨rf, hrf⟩ := hI.rf
      exact ⟨rf, by simpa [RFOk, hlocr] using hrf⟩

lemma wlist_append_write {α : Hist n V v₀} {p : ℕ} (hp : p ≤ K α) (v : V) :
    wlist (α ++ [.inv .wr (.write v)]) p = wlist α p ++ [.W (K α + 1) v] := by
  have hops : opsOf (α ++ [.inv .wr (.write v)]) .wr = opsOf α .wr ++ [.write v] := by
    simp [Label.invOf]
  have hK : K (α ++ [.inv .wr (.write v)]) = K α + 1 := by simp [K, hops]
  have hwv : ∀ t, t ≤ K α → wv (α ++ [.inv .wr (.write v)]) t = wv α t := by
    intro t ht; simp only [wv, hops]; exact writeVal_append_of_le ht
  have hwvK : wv (α ++ [.inv .wr (.write v)]) (K α + 1) = v := by
    simp only [wv, hops]; exact writeVal_succ (by simp [K])
  simp only [wlist, hK]
  rw [show K α + 1 - p = (K α - p) + 1 by omega, List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left (fun j hj => ?_)
    simp only [List.mem_range] at hj
    rw [hwv _ (by omega)]
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [show p + 1 + (K α - p) = K α + 1 by omega, hwvK]

/-- Invocation of `write v` at the writer. -/
theorem inv_invoke_wr (hq0 : 0 < qs) {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) (hp : C.pend .wr = none) (v : V) :
    Inv qs ((relay v₀ qs).step C (.invoke .wr (.write v))).1
      (α ++ ((relay v₀ qs).step C (.invoke .wr (.write v))).2) := by
  set w := (C.loc .wr).1
  set r := (C.loc .wr).2
  have hcl : C.loc .wr = (w, r) := rfl
  have hb : w.busy = false := by
    have := hI.wbusy; simp only [hp, ne_eq, not_true_eq_false, iff_false] at this
    simpa using this
  have hstep : (relay v₀ qs).step C (.invoke .wr (.write v)) =
      ((({ C with pend := Function.update C.pend .wr (some (.write v)) } : Cfg n V v₀).apply .wr
        ((⟨w.k + 1, true, v, ∅⟩, r), toAll (.W (w.k + 1) v), none)).1, [.inv .wr (.write v)]) := by
    simp [Algorithm.step, hp, relay, hcl, handle, Config.apply, respOut]
  rw [hstep]
  set C' := (({ C with pend := Function.update C.pend .wr (some (.write v)) } : Cfg n V v₀).apply
    .wr ((⟨w.k + 1, true, v, ∅⟩, r), toAll (.W (w.k + 1) v), none)).1
  set α' := α ++ [.inv .wr (.write v)]
  have hcK : (respsOf α .wr).length = K α := by
    have := hacc .wr
    simp only [pendCount, hp, Option.isNone_none, ite_true, add_zero] at this
    exact this.symm
  have hops : opsOf α' .wr = opsOf α .wr ++ [.write v] := by simp [α', Label.invOf]
  have hopsr : opsOf α' .rd = opsOf α .rd := by simp [α', Label.invOf]
  have hK : K α' = K α + 1 := by simp [K, hops]
  have hwv : ∀ t, t ≤ K α → wv α' t = wv α t := by
    intro t ht; simp only [wv, hops]; exact writeVal_append_of_le ht
  have hwvK : wv α' (K α + 1) = v := by
    simp only [wv, hops]; exact writeVal_succ (by simp [K])
  have hrw : respsOf α' .wr = respsOf α .wr := by simp [α', Label.retOf]
  have hrr : respsOf α' .rd = respsOf α .rd := by simp [α', Label.retOf]
  have hlocw : C'.loc .wr = (⟨w.k + 1, true, v, ∅⟩, r) := by simp [C', Config.apply]
  have hlocr : C'.loc .rd = C.loc .rd := by simp [C', Config.apply]
  have hpendw : C'.pend .wr = some (.write v) := by simp [C', Config.apply, pendAfter]
  have hpendr : C'.pend .rd = C.pend .rd := by simp [C', Config.apply]
  have hpp : ∀ k, pp C' k = pp C k := by intro k; simp [C', pp, Config.apply]
  have hch : ∀ x y, C'.chan x y = C.chan x y ++
      (if x = .wr then msgsTo (toAll (n := n) (.W (w.k + 1) v)) y else []) := by
    intro x y; by_cases hx : x = .wr
    · subst hx; simp [C', Config.apply]
    · simp [C', Config.apply, hx]
  have hchs : ∀ x y, (x ≠ .wr ∨ ∀ k, y ≠ .srv k) → C'.chan x y = C.chan x y := by
    intro x y hxy; rw [hch]
    rcases hxy with hx | hy
    · simp [hx]
    · split_ifs with hx
      · rcases y with k | _ | _
        · exact absurd rfl (hy k)
        · simp [msgsTo_toAll_wr]
        · simp [msgsTo_toAll_rd]
      · simp
  have hprd : ∀ x k, k < (opsOf α .rd).length → (Precedes α' x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes α' x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hwk := hI.wk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlocw, hK]; simp only; rw [← hwk]
  · rw [hlocw, hpendw]; simp
  · rw [hlocw, hK, hwvK]; simp
  · intro j hj
    rw [hrw] at hj
    rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hj),
      hwv _ (by omega)]
    exact hI.wresp j hj
  · intro k
    rw [hpp, hch]
    obtain ⟨h1, h2⟩ := hI.chW k
    refine ⟨by rw [hK]; omega, ?_⟩
    simp only [ite_true, msgsTo_toAll_srv, h2]
    rw [wlist_append_write h1, ← hwk]
  · intro k m hm; rw [hpp]; rw [hchs _ _ (Or.inl (by simp))] at hm; exact hI.chA k m hm
  · intro _; rw [hlocw]; simpa using hq0
  · simpa [hrw, hpp] using hI.wq
  · intro k m hm
    rw [hchs _ _ (Or.inl (by simp))] at hm
    rw [hlocr, hpp]
    rcases hI.chR k m hm with ⟨t, v', rfl, h1, h2, h3⟩ | h
    · exact Or.inl ⟨t, v', rfl, h1, h2, by
        rw [hwv _ (h2.trans (hI.chW k).1)]; exact h3⟩
    · exact Or.inr h
  · intro k t h1 h2; rw [hpp] at h2; rw [hlocr, hchs _ _ (Or.inl (by simp))]
    exact hI.invF k t h1 h2
  · rw [hlocr, hopsr]; exact hI.rq
  · rw [hlocr, hpendr]; exact hI.rbusy
  · rw [hlocr, hK]; exact hI.rbest.trans (Nat.le_succ _)
  · rw [hlocr, hwv _ hI.rbest]; exact hI.rval
  · intro k m hm; rw [hchs _ _ (Or.inl (by simp))] at hm; rw [hlocr]; exact hI.chQ k m hm
  · intro hb'
    rw [hlocr] at hb'
    unfold CurOk
    rw [hlocr]
    obtain ⟨hrc, lb, hlb, hG⟩ := hI.rcur hb'
    have hq1 : (C.loc .rd).2.q - 1 < (opsOf α .rd).length := by
      have h1 := hacc .rd
      have h2 : C.pend .rd ≠ none := hI.rbusy.1 hb'
      simp only [pendCount, Option.isNone_iff_eq_none, h2, ite_false] at h1
      rw [hI.rq]; omega
    refine ⟨hrc, lb, fun m hm => hlb m ((hprd _ _ hq1).1 hm), hG.imp_right ?_⟩
    rintro ⟨G, hGc, hG⟩
    refine ⟨G, hGc, fun k hk => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hG k hk
    exact ⟨by rw [hpp]; exact g1, g2, by rw [hchs _ _ (Or.inl (by simp))]; exact g3⟩
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨by rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j) from hj),
        hwv _ h3]; exact h1, by rw [hlocr]; exact h2, by rw [hK]; omega,
      fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
  · intro x y hxy
    have := hI.other x y hxy
    rw [hch, this]
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;>
      simp_all [OkPair, msgsTo_toAll_wr, msgsTo_toAll_rd]

/-- Invocation of `read` at the reader. -/
theorem inv_invoke_rd (hq0 : 0 < qs) {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) (hp : C.pend .rd = none) :
    Inv qs ((relay v₀ qs).step C (.invoke .rd .read)).1
      (α ++ ((relay v₀ qs).step C (.invoke .rd .read)).2) := by
  set w := (C.loc .rd).1
  set r := (C.loc .rd).2
  have hcl : C.loc .rd = (w, r) := rfl
  have hstep : (relay v₀ qs).step C (.invoke .rd .read) =
      ((({ C with pend := Function.update C.pend .rd (some .read) } : Cfg n V v₀).apply .rd
        ((w, ⟨r.q + 1, true, r.best, r.val, ∅⟩), toAll (.Q (r.q + 1)), none)).1,
        [.inv .rd .read]) := by
    simp [Algorithm.step, hp, relay, hcl, handle, Config.apply, respOut]
  rw [hstep]
  set C' := (({ C with pend := Function.update C.pend .rd (some .read) } : Cfg n V v₀).apply
    .rd ((w, ⟨r.q + 1, true, r.best, r.val, ∅⟩), toAll (.Q (r.q + 1)), none)).1
  set α' := α ++ [.inv .rd (.read : RWOp V)]
  have hopsw : opsOf α' .wr = opsOf α .wr := by simp [α', Label.invOf]
  have hopsr : opsOf α' .rd = opsOf α .rd ++ [.read] := by simp [α', Label.invOf]
  have hK : K α' = K α := by simp [K, hopsw]
  have hwv : ∀ t, wv α' t = wv α t := by intro t; simp [wv, hopsw]
  have hrw : respsOf α' .wr = respsOf α .wr := by simp [α', Label.retOf]
  have hrr : respsOf α' .rd = respsOf α .rd := by simp [α', Label.retOf]
  have hlocw : C'.loc .wr = C.loc .wr := by simp [C', Config.apply]
  have hlocr : C'.loc .rd = (w, ⟨r.q + 1, true, r.best, r.val, ∅⟩) := by simp [C', Config.apply]
  have hpendw : C'.pend .wr = C.pend .wr := by simp [C', Config.apply]
  have hpendr : C'.pend .rd = some .read := by simp [C', Config.apply, pendAfter]
  have hpp : ∀ k, pp C' k = pp C k := by intro k; simp [C', pp, Config.apply]
  have hch : ∀ x y, C'.chan x y = C.chan x y ++
      (if x = .rd then msgsTo (toAll (n := n) (.Q (r.q + 1))) y else []) := by
    intro x y; by_cases hx : x = .rd
    · subst hx; simp [C', Config.apply]
    · simp [C', Config.apply, hx]
  have hchs : ∀ x y, x ≠ .rd → C'.chan x y = C.chan x y := by
    intro x y hx; rw [hch]; simp [hx]
  have hprd : ∀ x k, k < (opsOf α .rd).length → (Precedes α' x (.rd, k) ↔ Precedes α x (.rd, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hpwr : ∀ x k, k < K α → (Precedes α' x (.wr, k) ↔ Precedes α x (.wr, k)) :=
    fun x k hk => precedes_append_iff_of_invoked hk
  have hrq : r.q = (opsOf α .rd).length := hI.rq
  have hrq' : (C.loc .rd).2.q = (opsOf α .rd).length := hI.rq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlocw, hK]; exact hI.wk
  · rw [hlocw, hpendw]; exact hI.wbusy
  · rw [hlocw, hK, hwv]; exact hI.wcur
  · intro j hj
    rw [hrw] at hj
    rw [respOf_append_of_completed (show Completed α ((Node.wr : Node n), j) from hj), hwv]
    exact hI.wresp j hj
  · intro k
    rw [hpp, hchs _ _ (by simp)]
    obtain ⟨h1, h2⟩ := hI.chW k
    refine ⟨by rw [hK]; exact h1, ?_⟩
    rw [h2]; simp [wlist, hK, hwv]
  · intro k m hm; rw [hpp]; rw [hchs _ _ (by simp)] at hm; exact hI.chA k m hm
  · intro hb; rw [hlocw] at hb ⊢; rw [hK]; simpa [hpp] using hI.wacked hb
  · simpa [hrw, hpp] using hI.wq
  · intro k m hm
    rw [hchs _ _ (by simp)] at hm
    rw [hlocr, hpp]
    rcases hI.chR k m hm with ⟨t, v', rfl, h1, h2, h3⟩ | ⟨j, rfl, hj⟩
    · exact Or.inl ⟨t, v', rfl, h1, h2, by rw [hwv]; exact h3⟩
    · exact Or.inr ⟨j, rfl, by simp only; omega⟩
  · intro k t h1 h2; rw [hpp] at h2; rw [hlocr, hchs _ _ (by simp)]
    exact hI.invF k t h1 h2
  · rw [hlocr, hopsr]; simp [hrq]
  · rw [hlocr, hpendr]; simp
  · rw [hlocr, hK]; exact hI.rbest
  · rw [hlocr, hwv]; exact hI.rval
  · intro k m hm
    rw [hch] at hm
    rw [hlocr]
    simp only [ite_true, msgsTo_toAll_srv, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · obtain ⟨j, rfl, hj⟩ := hI.chQ k m hm; exact ⟨j, rfl, by simp only; omega⟩
    · exact ⟨_, rfl, le_rfl⟩
  · intro _
    unfold CurOk
    rw [hlocr]
    refine ⟨by simpa using hq0, (respsOf α .wr).length, fun m hm => ?_, Or.inr ?_⟩
    · simp only [Nat.add_sub_cancel] at hm
      rw [hrq] at hm
      exact (precedes_append_inv_iff.1 hm)
    · refine ⟨Finset.univ.filter fun k => (respsOf α .wr).length ≤ pp C k, hI.wq,
        fun k hk => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      refine ⟨by rw [hpp]; exact hk, by simp, Or.inr ?_⟩
      rw [hchs _ _ (by simp)]
      refine DOk.of_no_D (fun j hj => ?_)
      rcases hI.chR k _ hj with ⟨t, v', he, -⟩ | ⟨j', he, hj'⟩
      · simp at he
      · simp only [Msg.D.injEq] at he; subst he; simp only; omega
  · obtain ⟨rf, hrf⟩ := hI.rf
    refine ⟨rf, fun j hj => ?_⟩
    rw [hrr] at hj
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrf j hj
    have hjinv : j < (opsOf α .rd).length := by
      have h1 : (respsOf α .rd).length ≤ (opsOf α .rd).length := by
        rw [hacc .rd]; exact Nat.le_add_right _ _
      omega
    refine ⟨?_, by rw [hlocr]; exact h2, by rw [hK]; exact h3,
      fun h0 hp => h4 h0 ((hpwr _ _ (by omega)).1 hp),
      fun hp => h5 ((hprd _ _ hjinv).1 hp), fun j' hj' => h6 j' (by rw [hrr] at hj'; exact hj')⟩
    rw [respOf_append_of_completed (show Completed α ((Node.rd : Node n), j) from hj), hwv]
    exact h1
  · intro x y hxy
    have := hI.other x y hxy
    rw [hch, this]
    rcases x with k | _ | _ <;> rcases y with k' | _ | _ <;>
      simp_all [OkPair, msgsTo_toAll_wr, msgsTo_toAll_rd]

/-! ### The step lemma -/

lemma handle_tick (p : Node n) (c : ℕ) (l : LSt n V) :
    handle qs p (.tick c) l = (l, [], none) := by
  rcases p with _ | _ | _ <;> rfl

lemma apply_noop (C : Cfg n V v₀) (p : Node n) :
    C.apply p (C.loc p, [], none) = (C, []) := by
  rcases C with ⟨loc, pend, chan, sent, dlv⟩
  simp only [Config.apply, Function.update_eq_self, Prod.mk.injEq]
  refine ⟨?_, by simp [respOut]⟩
  have h1 : Function.update pend p (pendAfter (pend p) none) = pend := by
    have : pendAfter (pend p) none = pend p := by cases pend p <;> rfl
    rw [this, Function.update_eq_self]
  simp [h1, msgsTo]

theorem inv_step (hq2 : n < 2 * qs) {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hacc : Acc α C) (e : Event (Node n) (register V v₀)) (he : EvOk e) :
    Inv qs ((relay v₀ qs).step C e).1 (α ++ ((relay v₀ qs).step C e).2) := by
  have hq0 : 0 < qs := by omega
  cases e with
  | invoke p o =>
    rcases hp : C.pend p with _ | o'
    · rcases he p o rfl with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
      · exact inv_invoke_wr qs hq0 hI hacc hp v
      · exact inv_invoke_rd qs hq0 hI hacc hp
    · have : (relay v₀ qs).step C (.invoke p o) = (C, []) := by simp [Algorithm.step, hp]
      rw [this, List.append_nil]; exact hI
  | tick p c =>
    have : (relay v₀ qs).step C (.tick p c) = (C, []) := by
      simp only [Algorithm.step, relay]; rw [handle_tick, apply_noop]
    rw [this, List.append_nil]; exact hI
  | deliver a b =>
    rcases hc : C.chan a b with _ | ⟨m, rest⟩
    · have : (relay v₀ qs).step C (.deliver a b) = (C, []) := by simp [Algorithm.step, hc]
      rw [this, List.append_nil]; exact hI
    have hne : C.chan a b ≠ [] := by simp [hc]
    have hok : OkPair a b := by
      by_contra h; exact hne (hI.other a b h)
    rcases a with i | _ | _ <;> rcases b with j | _ | _ <;> simp only [OkPair] at hok
    · -- server → writer
      obtain ⟨t, rfl, -⟩ := hI.chA i m (by rw [hc]; simp)
      exact inv_deliver_A qs hI hacc hc
    · -- server → reader
      rcases hI.chR i m (by rw [hc]; simp) with ⟨t, v, rfl, -⟩ | ⟨j, rfl, -⟩
      · exact inv_deliver_F qs hI hc
      · exact inv_deliver_D qs hq2 hI hacc hc
    · -- writer → server
      obtain ⟨hpK, hW⟩ := hI.chW j
      have hlt : pp C j < K α := by
        by_contra h; rw [wlist_eq_nil (by omega)] at hW; exact hne hW
      rw [wlist_cons hlt] at hW
      rw [hW] at hc
      simp only [List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact inv_deliver_W qs hI hW
    · -- reader → server
      obtain ⟨j', rfl, -⟩ := hI.chQ j m (by rw [hc]; simp)
      exact inv_deliver_Q qs hI hc

/-- The invariant holds in every reachable configuration (SWSR environment). -/
theorem inv_reach (hq2 : n < 2 * qs) (hqn : qs ≤ n) (E : List (Event (Node n) (register V v₀)))
    (hE : ∀ e ∈ E, EvOk e) :
    Inv qs ((relay v₀ qs).run (relay v₀ qs).initCfg E) ((relay v₀ qs).hist (relay v₀ qs).initCfg E) := by
  induction E using List.reverseRecOn with
  | nil => exact inv_init qs hqn
  | append_singleton E e ih =>
    have ih' := ih (fun e' he' => hE e' (by simp [he']))
    rw [Algorithm.run_append, Algorithm.hist_append]
    have := inv_step qs hq2 ih' (acc_hist _ E) e (hE e (by simp))
    simpa [Algorithm.hist] using this

/-! ### Atomicity and regularity -/

theorem readsFrom (hq2 : n < 2 * qs) (hqn : qs ≤ n) (E : List (Event (Node n) (register V v₀)))
    (hE : ∀ e ∈ E, EvOk e) :
    ∃ rf, SWSRReadsFrom ((relay v₀ qs).hist (relay v₀ qs).initCfg E) Node.wr Node.rd rf := by
  have hI := inv_reach qs hq2 hqn E hE
  obtain ⟨rf, hrf⟩ := hI.rf
  refine ⟨rf, ⟨by simp, wellFormed_hist _ E, fun p o ho => ?_, fun j v x hop hres => ?_,
    fun k hk => (hrf k hk).1, fun k hk => (hrf k hk).2.2.2.1, fun k hk => (hrf k hk).2.2.2.2.1,
    fun k k' hkk' hk' _ => (hrf k (by omega)).2.2.2.2.2 k' hk' hkk'.le⟩⟩
  · exact hE _ (mem_opsOf_hist _ ho) p o rfl
  · have hj : j < (respsOf ((relay v₀ qs).hist (relay v₀ qs).initCfg E) .wr).length := by
      by_contra h; simp [respOf, List.getElem?_eq_none (not_lt.1 h)] at hres
    rw [hI.wresp j hj] at hres
    simp only [Option.some.injEq] at hres
    rw [← hres]
    exact writeVal_succ hop

/-- **The relay algorithm is atomic** (for `qs ≤ n < 2 qs`). -/
theorem isAtomic (hq2 : n < 2 * qs) (hqn : qs ≤ n) :
    IsAtomic (relay v₀ qs : Algorithm (Node n) (register V v₀) _ _) := by
  intro E hE
  obtain ⟨rf, h⟩ := readsFrom qs hq2 hqn E hE
  exact ⟨_, h.isLinearization⟩

/-- **The relay algorithm is regular** (for `qs ≤ n < 2 qs`). -/
theorem isRegular (hq2 : n < 2 * qs) (hqn : qs ≤ n) :
    IsRegular (relay v₀ qs : Algorithm (Node n) (register V v₀) _ _) := by
  intro E hE k hk
  obtain ⟨rf, h⟩ := readsFrom qs hq2 hqn E hE
  exact ⟨rf k, h.read_val k hk, h.not_future k hk, h.not_overwritten k hk⟩

end Podc.StorageCost.Relay
