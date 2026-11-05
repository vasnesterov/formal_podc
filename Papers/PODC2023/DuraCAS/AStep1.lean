import Papers.PODC2023.DuraCAS.AGlob

/-!
# Preservation of the global invariant: steps without shared-memory effect

`GInv.go`: a step that only moves the program counter of a process (the ghost state is unchanged).
`GInv.fin`: a step that ends an operation (return or completion of `RECOVER`), possibly adding
the operation to the linearization.
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem update_op_eq {a : AS P K V} {p : P} {st' : APS P K V} (h : st'.op = (a.ps p).op) (q : P) :
    (Function.update a.ps p st' q).op = (a.ps q).op := by
  by_cases hq : q = p
  · subst hq; simp [h]
  · simp [Function.update_of_ne hq]

/-- A step that only changes the local state of `p` (not its operation); ghost unchanged. -/
theorem GInv.go {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (st' : APS P K V) (hst : st'.op = some r)
    (hl : Loc p (view init a g r.k)
      ⟨st'.pc, r, st'.orph, a.ls (p, .crit), g.wit p, r.id ∈ g.L.map GE.id⟩) :
    GInv init { a with ps := Function.update a.ps p st' } g := by
  set a' : AS P K V := { a with ps := Function.update a.ps p st' }
  have hops : ∀ q, (a'.ps q).op = (a.ps q).op := update_op_eq (by rw [hst, hop])
  have hv : ∀ k, view init a' g k = view init a g k := fun _ => rfl
  have hpv : ∀ q s, q ≠ p → pview a' g q s = pview a g q s := by
    intro q s hq; simp [pview, a', Function.update_of_ne hq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨fun k => (hv k) ▸ h1 k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24⟩
  · intro q s hs
    rw [hops] at hs
    by_cases hq : q = p
    · subst hq
      rw [hop] at hs; cases hs
      have : pview a' g q r =
          ⟨st'.pc, r, st'.orph, a.ls (q, .crit), g.wit q, r.id ∈ g.L.map GE.id⟩ := by
        simp [pview, a']
      rw [this, hv]; exact hl
    · rw [hpv q s hq, hv]; exact h2 q s hs
  · intro q hq
    rw [hops] at hq
    by_cases hqp : q = p
    · subst hqp; rw [hop] at hq; cases hq
    · simp only [a', Function.update_of_ne hqp]; exact h3 q hq
  · intro k id hk
    obtain ⟨q, s, hs, h'⟩ := h4 k id hk
    exact ⟨q, s, by rw [hops]; exact hs, h'⟩
  · intro q q' s s' hs hs'; rw [hops] at hs hs'; exact h5 q q' s s' hs hs'
  · intro q s hs; rw [hops] at hs; exact h6 q s hs
  · intro q s hs; rw [hops] at hs; exact h7 q s hs
  · intro q s hs; rw [hops] at hs; exact h8 q s hs
  · intro q s hs; rw [hops] at hs; exact h9 q s hs
  · intro q s hs; rw [hops] at hs; exact h10 q s hs
  · intro q s hs; rw [hops] at hs; exact h11 q s hs

theorem getElem?_append_one_of_lt {α : Type*} {L : List α} {x : α} {i : ℕ} (hi : i < L.length) :
    (L ++ [x])[i]? = L[i]? := List.getElem?_append_left hi

theorem getElem?_append_one {α : Type*} {L : List α} {x y : α} {i : ℕ}
    (h : (L ++ [x])[i]? = some y) : (i < L.length ∧ L[i]? = some y) ∨ (i = L.length ∧ y = x) := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · left; exact ⟨hi, by rwa [List.getElem?_append_left hi] at h⟩
  · right
    rw [List.getElem?_append_right hi] at h
    rcases Nat.lt_or_ge (i - L.length) 1 with h1 | h1
    · have : i - L.length = 0 := by omega
      rw [this] at h; simp at h; exact ⟨by omega, h.symm⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at h; cases h

theorem lt_length_of_getElem? {α : Type*} {L : List α} {i : ℕ} {y : α} (h : L[i]? = some y) :
    i < L.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem Ev.ends_unique {e : Ev P K V} {a b : ℕ} (ha : e.Ends a) (hb : e.Ends b) : a = b := by
  cases e <;> simp only [Ev.Ends] at ha hb <;> omega

/-- The inv event of a busy process is unique: its `d` and operation are those of `r`. -/
theorem GInv.inv_of_busy {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {i : ℕ} {q : P} {k : K} {op : Op V} {d : ℕ}
    (hi : a.hist[i]? = some (Ev.inv r.id q k op d)) :
    q = p ∧ k = r.k ∧ op = r.op ∧ d = r.d1 ∧ g.evT i = g.it p := by
  obtain ⟨j, hj, hjt⟩ := h.busy_inv p r hop
  have := h.inv_idx _ _ _ _ _ _ _ _ _ _ _ hi hj
  subst this
  rw [hi] at hj; simp only [Option.some.injEq, Ev.inv.injEq] at hj
  exact ⟨hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2, hjt⟩

/-- The A-level state after `p` ends its operation with event `ev`. -/
def AS.fin (a : AS P K V) (p : P) (ev : Ev P K V) : AS P K V :=
  { a with ps := Function.update a.ps p ⟨.at .idle, none, (a.ps p).orph⟩, hist := a.hist ++ [ev] }

/-- Ghost update at a step that appends an event: tick the clock, record the event step. -/
def Gh.tick (g : Gh P K V) (len : ℕ) (L' : List (GE K V)) : Gh P K V :=
  { g with clk := g.clk + 1, evT := Function.update g.evT len g.clk, L := L' }

/-- A step that ends the operation `r` of `p` with event `ev` (a return or the completion of
`RECOVER`), with new linearization `L'`. -/
theorem GInv.fin {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) (horph : (a.ps p).orph = none)
    (hpw : g.pw r.k ≠ some r.id) (ev : Ev P K V) (L' : List (GE K V))
    (hev : ev.Ends r.id ∧ ev.dEnd = a.ls (p, .crit) ∧ ∀ id p k op d, ev ≠ Ev.inv id p k op d)
    (hLg : LGood init L' (g.clk + 1))
    (hsub : ∀ e ∈ g.L, e ∈ L')
    (hmem : ∀ e ∈ L', e ∈ g.L ∨ (e.id = r.id ∧ e.k = r.k ∧ e.op = r.op ∧
      4 * g.it p + 2 < e.key ∧ e.key ≤ 4 * g.clk + 2))
    (hcur : curSt init L' = curSt init g.L)
    (hst : ∀ t < g.clk, stAt init L' t = stAt init g.L t)
    (hret : ∀ id resp d, ev = Ev.ret id resp d → ∃ e ∈ L', e.id = r.id ∧ e.rsp = resp)
    (htook : r.d1 < a.ls (p, .crit) → ∃ e ∈ L', e.id = r.id ∧ e.rsp = .ok true)
    (hnoeff : ∀ id d, ev = Ev.rdone id d → r.d1 = a.ls (p, .crit) → r.id ∉ L'.map GE.id) :
    GInv init (a.fin p ev) (g.tick a.hist.length L') := by
  have hopp : ((a.fin p ev).ps p).op = none := by simp [AS.fin]
  have hops : ∀ q, q ≠ p → (a.fin p ev).ps q = a.ps q :=
    fun q hq => by simp [AS.fin, Function.update_of_ne hq]
  have hnew : ∀ e ∈ L', e ∉ g.L → e.id = r.id := fun e he hn => by
    rcases hmem e he with h' | h'
    · exact absurd h' hn
    · exact h'.1
  have hid_other : ∀ q s, (a.ps q).op = some s → q ≠ p → s.id ≠ r.id := fun q s hs hq e =>
    hq (h.uniq q p s r hs hop e)
  have hmemid : ∀ q s, (a.ps q).op = some s → q ≠ p →
      (s.id ∈ L'.map GE.id ↔ s.id ∈ g.L.map GE.id) := by
    intro q s hs hq
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, he, hid⟩
      by_cases hn : e ∈ g.L
      · exact ⟨e, hn, hid⟩
      · exact absurd (hid ▸ hnew e he hn) (hid_other q s hs hq)
    · rintro ⟨e, he, hid⟩; exact ⟨e, hsub e he, hid⟩
  have hv : ∀ k, view init (a.fin p ev) (g.tick a.hist.length L') k = view init a g k := by
    intro k; simp only [view, AS.fin, Gh.tick, hcur]
  have hpv : ∀ q s, (a.ps q).op = some s → q ≠ p →
      pview (a.fin p ev) (g.tick a.hist.length L') q s = pview a g q s := by
    intro q s hs hq
    simp only [pview, hops q hq, Gh.tick]
    congr 1
    exact propext (hmemid q s hs hq)
  have hget : ∀ i y, (a.fin p ev).hist[i]? = some y →
      (i < a.hist.length ∧ a.hist[i]? = some y) ∨ (i = a.hist.length ∧ y = ev) :=
    fun i y hy => getElem?_append_one hy
  have hevT : ∀ i, i < a.hist.length → (g.tick a.hist.length L').evT i = g.evT i :=
    fun i hi => by simp [Gh.tick, Function.update_of_ne (Nat.ne_of_lt hi)]
  have hmemH : ∀ y, y ∈ (a.fin p ev).hist ↔ y ∈ a.hist ∨ y = ev := by simp [AS.fin]
  have hinvH : ∀ id q k op d, Ev.inv id q k op d ∈ (a.fin p ev).hist ↔
      Ev.inv id q k op d ∈ a.hist := by
    intro id q k op d; rw [hmemH]
    constructor
    · rintro (h' | h')
      · exact h'
      · exact absurd h'.symm (hev.2.2 _ _ _ _ _)
    · exact Or.inl
  have hbusy : ∀ q s, ((a.fin p ev).ps q).op = some s → q ≠ p ∧ (a.ps q).op = some s := by
    intro q s hs
    by_cases hq : q = p
    · subst hq; rw [hopp] at hs; cases hs
    · exact ⟨hq, by rw [← hops q hq]; exact hs⟩
  have hends : ∀ id, ev.Ends id → id = r.id := fun id hid => Ev.ends_unique hid hev.1
  have hlen : (a.fin p ev).hist.length = a.hist.length + 1 := by simp [AS.fin]
  have hloc := h.loc p r hop
  have hd1 : r.d1 ≤ a.ls (p, .crit) := hloc.d1_le
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  refine ⟨fun k => by rw [hv]; exact h1 k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLg, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s hs
    obtain ⟨hq, hs⟩ := hbusy q s hs
    rw [hpv q s hs hq, hv]; exact h2 q s hs
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; simp [AS.fin, horph]
    · rw [hops q hqp] at hq ⊢; exact h3 q hq
  · intro k id hk
    obtain ⟨q, s, hs, rfl, rfl⟩ := h4 k id hk
    have hq : q ≠ p := fun e => by subst e; rw [hop] at hs; cases hs; exact hpw hk
    exact ⟨q, s, by rw [hops q hq]; exact hs, rfl, rfl⟩
  · intro q q' s s' hs hs'
    exact h5 q q' s s' (hbusy q s hs).2 (hbusy q' s' hs').2
  · intro q s hs; exact h6 q s (hbusy q s hs).2
  · intro q s hs
    obtain ⟨i, hi, ht⟩ := h7 q s (hbusy q s hs).2
    have hil := lt_length_of_getElem? hi
    exact ⟨i, by simp only [AS.fin]; rw [getElem?_append_one_of_lt hil]; exact hi,
      by rw [hevT i hil]; exact ht⟩
  · intro q s hs0 e he
    obtain ⟨hq, hs⟩ := hbusy q s hs0
    rcases (hmemH e).1 he with he | he
    · exact h8 q s hs e he
    · subst he; exact fun h' => hid_other q s hs hq (hends _ h')
  · intro q s hs; have := h9 q s (hbusy q s hs).2; simp only [Gh.tick]; omega
  · intro q s hs t ht
    obtain ⟨hq, hs⟩ := hbusy q s hs
    obtain ⟨a1, a2, a3, a4⟩ := h10 q s hs t ht
    refine ⟨a1, by simp only [Gh.tick]; omega, fun old new hop' => ?_, fun u hu => ?_⟩
    · simp only [Gh.tick]; rw [hst t a2]; exact a3 old new hop'
    · obtain ⟨b1, y, hy, hy'⟩ := a4 u hu
      exact ⟨b1, y, hsub y hy, hy'⟩
  · intro q s hs e he hid
    obtain ⟨hq, hs⟩ := hbusy q s hs
    by_cases hn : e ∈ g.L
    · exact h11 q s hs e hn hid
    · exact absurd (hid ▸ hnew e he hn) (hid_other q s hs hq)
  · intro i j hij hj
    rw [hlen] at hj
    have hil : i < a.hist.length := by omega
    rw [hevT i hil]
    rcases Nat.lt_or_ge j a.hist.length with hj' | hj'
    · rw [hevT j hj']; exact h13 i j hij hj'
    · have : j = a.hist.length := by omega
      subst this; simp only [Gh.tick, Function.update_self]; exact h14 i hil
  · intro i hi
    rw [hlen] at hi
    rcases Nat.lt_or_ge i a.hist.length with hi' | hi'
    · rw [hevT i hi']; have := h14 i hi'; simp only [Gh.tick]; omega
    · have : i = a.hist.length := by omega
      subst this; simp [Gh.tick]
  · intro id q k op d hm; exact h15 id q k op d ((hinvH _ _ _ _ _).1 hm)
  · intro e he id hid
    rcases (hmemH e).1 he with he | rfl
    · exact h16 e he id hid
    · rw [hends id hid]; exact h6 p r hop
  · intro i j id q k op d q' k' op' d' hi hj
    rcases hget i _ hi with ⟨_, hi'⟩ | ⟨_, he⟩
    · rcases hget j _ hj with ⟨_, hj'⟩ | ⟨_, he⟩
      · exact h17 i j id q k op d q' k' op' d' hi' hj'
      · exact absurd he.symm (hev.2.2 _ _ _ _ _)
    · exact absurd he.symm (hev.2.2 _ _ _ _ _)
  · intro e he
    rcases hmem e he with he' | ⟨hid, hk, hop', -⟩
    · obtain ⟨i, q, d, hi⟩ := h18 e he'
      exact ⟨i, q, d, by simp only [AS.fin]; rw [getElem?_append_one_of_lt
        (lt_length_of_getElem? hi)]; exact hi⟩
    · obtain ⟨i, hi, -⟩ := h7 p r hop
      refine ⟨i, p, r.d1, ?_⟩
      simp only [AS.fin]; rw [getElem?_append_one_of_lt (lt_length_of_getElem? hi), hid, hk, hop']
      exact hi
  · intro e he i q k op d hi
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨_, he'⟩
    · rw [hevT i hil]
      rcases hmem e he with he' | ⟨hid, -, -, hkey, -⟩
      · exact h19 e he' i q k op d hi'
      · rw [hid] at hi'
        have := (GInv.inv_of_busy ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ hop hi').2.2.2.2
        omega
    · exact absurd he'.symm (hev.2.2 _ _ _ _ _)
  · intro e he i y hi hy
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨hil, rfl⟩
    · rw [hevT i hil]
      rcases hmem e he with he' | ⟨hid, -⟩
      · exact h20 e he' i y hi' hy
      · rw [hid] at hy; exact absurd hy (h8 p r hop y (List.mem_of_getElem? hi'))
    · subst hil
      simp only [Gh.tick, Function.update_self]
      rcases hmem e he with he' | ⟨-, -, -, -, hkey⟩
      · have := h12.key_lt e he'; omega
      · exact hkey
  · intro id resp d hr
    rcases (hmemH _).1 hr with hr | hr
    · obtain ⟨e, he, h'⟩ := h21 id resp d hr
      exact ⟨e, hsub e he, h'⟩
    · obtain ⟨e, he, hid, hrsp⟩ := hret id resp d hr.symm
      exact ⟨e, he, by rw [hid, hends id (by rw [← hr]; rfl)], hrsp⟩
  · intro id q k op d hm y hy hyend
    have hm' := (hinvH _ _ _ _ _).1 hm
    rcases (hmemH y).1 hy with hy | rfl
    · exact h22 id q k op d hm' y hy hyend
    · have hid := hends id hyend; subst hid
      obtain ⟨i, hi⟩ := getElem?_of_mem hm'
      have := (GInv.inv_of_busy ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ hop hi).2.2.2.1
      rw [this, hev.2.1]; exact hd1
  · intro id q k op d hm y hy hyend hlt
    have hm' := (hinvH _ _ _ _ _).1 hm
    rcases (hmemH y).1 hy with hy | rfl
    · obtain ⟨e, he, h'⟩ := h23 id q k op d hm' y hy hyend hlt
      exact ⟨e, hsub e he, h'⟩
    · have hid := hends id hyend; subst hid
      obtain ⟨i, hi⟩ := getElem?_of_mem hm'
      have := (GInv.inv_of_busy ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ hop hi).2.2.2.1
      rw [this, hev.2.1] at hlt
      exact htook hlt
  · intro id q k op d hm hrd
    have hm' := (hinvH _ _ _ _ _).1 hm
    rcases (hmemH _).1 hrd with hrd | hrd
    · intro hin
      obtain ⟨e, he, hid⟩ := List.mem_map.1 hin
      rcases hmem e he with he' | ⟨hid', -⟩
      · exact h24 id q k op d hm' hrd (List.mem_map.2 ⟨e, he', hid⟩)
      · rw [← hid, hid'] at hrd
        exact h8 p r hop _ hrd rfl
    · have hid := hends id (by rw [← hrd]; rfl); subst hid
      obtain ⟨i, hi⟩ := getElem?_of_mem hm'
      have := (GInv.inv_of_busy ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ hop hi).2.2.2.1
      have hd : d = a.ls (p, .crit) := by rw [← hev.2.1, ← hrd]; rfl
      exact hnoeff _ _ hrd.symm (by rw [← this, hd])

end Podc.DuraCAS
