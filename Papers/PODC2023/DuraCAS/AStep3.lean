import Papers.PODC2023.DuraCAS.AStep2

/-!
# Preservation of the global invariant: invocation and crash
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem LGood.mono {init : K → V} {L : List (GE K V)} {c c' : ℕ} (h : LGood init L c)
    (hc : c ≤ c') : LGood init L c' :=
  ⟨h.sorted, h.nodup, fun e he => by have := h.key_lt e he; omega, h.resp, h.rank0, h.rank1⟩

theorem GInv.ent_lt {init : K → V} {a : AS P K V} {g : Gh P K V} (h : GInv init a g) :
    ∀ e ∈ g.L, e.id < a.nid := by
  intro e he
  obtain ⟨i, p, d, hi⟩ := h.ent_inv e he
  exact h.inv_lt _ _ _ _ _ (List.mem_of_getElem? hi)

/-- The initial witness of an operation: a `CAS(old, _)` invoked when the value is not `old`. -/
def invWit (init : K → V) (L : List (GE K V)) (k : K) (op : Op V) (t : ℕ) : Option ℕ :=
  match op with
  | .cas old _ => if curSt init L k = old then none else some t
  | _ => none

/-- Ghost update at an invocation. -/
def Gh.invk (g : Gh P K V) (p : P) (len : ℕ) (w : Option ℕ) : Gh P K V :=
  { g with clk := g.clk + 1, evT := Function.update g.evT len g.clk,
           it := Function.update g.it p g.clk, wit := Function.update g.wit p w }

theorem GInv.invoke {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} (k : K) (op : Op V)
    (h : GInv init a g) (hidle : (a.ps p).op = none) :
    GInv init (a.invoke p k op) (g.invk p a.hist.length (invWit init g.L k op g.clk)) := by
  set w := invWit init g.L k op g.clk
  set r0 : OpRec K V := ⟨a.nid, k, op, a.ls (p, .crit)⟩
  set ev : Ev P K V := Ev.inv a.nid p k op (a.ls (p, .crit))
  have hpsp : (a.invoke p k op).ps p = ⟨.at (firstPc op), some r0, (a.ps p).orph⟩ := by
    simp [AS.invoke, r0]
  have hpsq : ∀ q, q ≠ p → (a.invoke p k op).ps q = a.ps q := fun q hq => by
    simp [AS.invoke, Function.update_of_ne hq]
  have hbusy : ∀ q s, ((a.invoke p k op).ps q).op = some s →
      (q = p ∧ s = r0) ∨ (q ≠ p ∧ (a.ps q).op = some s) := by
    intro q s hs
    by_cases hq : q = p
    · subst hq; rw [hpsp] at hs; exact Or.inl ⟨rfl, (Option.some.inj hs).symm⟩
    · rw [hpsq q hq] at hs; exact Or.inr ⟨hq, hs⟩
  have hentlt := h.ent_lt
  have hninL : a.nid ∉ g.L.map GE.id := fun hm => by
    obtain ⟨e, he, hid⟩ := List.mem_map.1 hm; have := hentlt e he; omega
  have hhist : (a.invoke p k op).hist = a.hist ++ [ev] := rfl
  have hnid : (a.invoke p k op).nid = a.nid + 1 := rfl
  have hls : (a.invoke p k op).ls = a.ls := rfl
  have hclk : (g.invk p a.hist.length w).clk = g.clk + 1 := rfl
  have hL : (g.invk p a.hist.length w).L = g.L := rfl
  have hitp : (g.invk p a.hist.length w).it p = g.clk := by simp [Gh.invk]
  have hitq : ∀ q, q ≠ p → (g.invk p a.hist.length w).it q = g.it q := fun q hq => by
    simp [Gh.invk, Function.update_of_ne hq]
  have hwp : (g.invk p a.hist.length w).wit p = w := by simp [Gh.invk]
  have hwq : ∀ q, q ≠ p → (g.invk p a.hist.length w).wit q = g.wit q := fun q hq => by
    simp [Gh.invk, Function.update_of_ne hq]
  have hget : ∀ i y, (a.invoke p k op).hist[i]? = some y →
      (i < a.hist.length ∧ a.hist[i]? = some y) ∨ (i = a.hist.length ∧ y = ev) :=
    fun i y hy => getElem?_append_one hy
  have hevT : ∀ i, i < a.hist.length → (g.invk p a.hist.length w).evT i = g.evT i :=
    fun i hi => by simp [Gh.invk, Function.update_of_ne (Nat.ne_of_lt hi)]
  have hevTn : (g.invk p a.hist.length w).evT a.hist.length = g.clk := by simp [Gh.invk]
  have hmemH : ∀ y, y ∈ (a.invoke p k op).hist ↔ y ∈ a.hist ∨ y = ev := by
    intro y; rw [hhist]; simp
  have hlen : (a.invoke p k op).hist.length = a.hist.length + 1 := by simp [hhist]
  have hgetlt : ∀ i y, a.hist[i]? = some y → (a.invoke p k op).hist[i]? = some y :=
    fun i y hi => by rw [hhist, getElem?_append_one_of_lt (lt_length_of_getElem? hi)]; exact hi
  have hendnew : ∀ id, ¬ ev.Ends id := fun id h' => by simp [ev, Ev.Ends] at h'
  have hv : ∀ k', view init (a.invoke p k op) (g.invk p a.hist.length w) k' = view init a g k' :=
    fun _ => rfl
  have hidp : ∀ q s, (a.ps q).op = some s → s.id < a.nid := fun q s hs => h.busy_nid q s hs
  have horph : (a.ps p).orph = none := h.idle p hidle
  have hinvev : ∀ id q k' op' d, ev = Ev.inv id q k' op' d → id = a.nid := by
    intro id q k' op' d he; simp only [ev, Ev.inv.injEq] at he; exact he.1.symm
  refine ⟨fun k' => by rw [hv]; exact h.kinv k', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.lgood.mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s hs
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · rw [hv]
      apply invoke_loc (h.kinv k)
      · rfl
      · exact hninL
      · intro e
        obtain ⟨q, s, hs, hid, -⟩ := h.pw_ex _ _ e
        have := hidp q s hs; have hid' : s.id = a.nid := hid; omega
      · show ((a.invoke q k op).ps q).orph = none
        rw [hpsp]; exact horph
      · show ((a.invoke q k op).ps q).pc = _
        rw [hpsp]; rfl
      · intro old new hop hw
        have hw' : w = none := by rw [← hwp]; exact hw
        clear hw
        simp only [pview, r0] at hop; subst hop
        simp only [w, invWit] at hw'
        split_ifs at hw' with hc
        exact hc
    · have : pview (a.invoke p k op) (g.invk p a.hist.length w) q s = pview a g q s := by
        simp only [pview, hpsq q hq, hls, hwq q hq, hL]
      rw [this, hv]; exact h.loc q s hs
  · intro q hq
    by_cases hqp : q = p
    · subst hqp; rw [hpsp] at hq; cases hq
    · rw [hpsq q hqp] at hq ⊢; exact h.idle q hq
  · intro k' id hk
    obtain ⟨q, s, hs, h'⟩ := h.pw_ex k' id hk
    have hq : q ≠ p := fun e => by subst e; rw [hidle] at hs; cases hs
    exact ⟨q, s, by rw [hpsq q hq]; exact hs, h'⟩
  · intro q q' s s' hs hs' hid
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs1⟩ <;>
      rcases hbusy q' s' hs' with ⟨rfl, rfl⟩ | ⟨hq', hs1'⟩
    · rfl
    · have := hidp q' s' hs1'; have hid' : a.nid = s'.id := hid; omega
    · have := hidp q s hs1; have hid' : s.id = a.nid := hid; omega
    · exact h.uniq q q' s s' hs1 hs1' hid
  · intro q s hs
    rw [hnid]
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · simp [r0]
    · have := hidp q s hs; omega
  · intro q s hs
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · exact ⟨a.hist.length, by rw [hhist]; simp [ev, r0], by rw [hevTn, hitp]⟩
    · obtain ⟨i, hi, ht⟩ := h.busy_inv q s hs
      exact ⟨i, hgetlt i _ hi, by rw [hevT i (lt_length_of_getElem? hi), hitq q hq]; exact ht⟩
  · intro q s hs e he
    rcases (hmemH e).1 he with he1 | he1
    · rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs1⟩
      · intro hend; have := h.end_lt e he1 _ hend; simp only [r0] at this; omega
      · exact h.busy_end q s hs1 e he1
    · subst he1; exact hendnew _
  · intro q s hs
    rw [hclk]
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · rw [hitp]; omega
    · have := h.busy_it q s hs; rw [hitq q hq]; omega
  · intro q s hs t ht
    rw [hclk, hL]
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · rw [hwp] at ht; rw [hitp]
      cases op with
      | cas old new =>
        simp only [w, invWit] at ht
        split_ifs at ht with hc
        cases ht
        refine ⟨le_rfl, by omega, fun o n hop => ?_, fun u hu => by simp [r0] at hu⟩
        simp only [r0, Op.cas.injEq] at hop; obtain ⟨rfl, rfl⟩ := hop
        rw [stAt_eq_curSt _ _ _ (fun e he => by have := h.lgood.key_lt e he; omega)]; exact hc
      | read => simp [w, invWit] at ht
      | write u => simp [w, invWit] at ht
    · rw [hwq q hq] at ht; rw [hitq q hq]
      obtain ⟨a1, a2, a3, a4⟩ := h.wit q s hs t ht
      exact ⟨a1, by omega, a3, a4⟩
  · intro q s hs e he hid
    rw [hL] at he
    rcases hbusy q s hs with ⟨rfl, rfl⟩ | ⟨hq, hs⟩
    · have := hentlt e he; simp only [r0] at hid; omega
    · exact h.act_rsp q s hs e he hid
  · intro i j hij hj
    rw [hlen] at hj
    have hil : i < a.hist.length := by omega
    rw [hevT i hil]
    rcases Nat.lt_or_ge j a.hist.length with hj' | hj'
    · rw [hevT j hj']; exact h.evT_mono i j hij hj'
    · have : j = a.hist.length := by omega
      subst this; rw [hevTn]; exact h.evT_lt i hil
  · intro i hi
    rw [hlen] at hi; rw [hclk]
    rcases Nat.lt_or_ge i a.hist.length with hi' | hi'
    · rw [hevT i hi']; have := h.evT_lt i hi'; omega
    · have : i = a.hist.length := by omega
      subst this; rw [hevTn]; omega
  · intro id q k' op' d hm
    rw [hnid]
    rcases (hmemH _).1 hm with hm | hm
    · have := h.inv_lt id q k' op' d hm; omega
    · rw [hinvev _ _ _ _ _ hm.symm]; omega
  · intro e he id hid
    rw [hnid]
    rcases (hmemH e).1 he with he | he
    · have := h.end_lt e he id hid; omega
    · subst he; exact absurd hid (hendnew _)
  · intro i j id q k' op' d q' k'' op'' d' hi hj
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨hil, he⟩ <;>
      rcases hget j _ hj with ⟨hjl, hj'⟩ | ⟨hjl, he'⟩
    · exact h.inv_idx i j id q k' op' d q' k'' op'' d' hi' hj'
    · have := hinvev _ _ _ _ _ he'.symm
      have := h.inv_lt _ _ _ _ _ (List.mem_of_getElem? hi'); omega
    · have := hinvev _ _ _ _ _ he.symm
      have := h.inv_lt _ _ _ _ _ (List.mem_of_getElem? hj'); omega
    · omega
  · intro e he
    rw [hL] at he
    obtain ⟨i, q, d, hi⟩ := h.ent_inv e he
    exact ⟨i, q, d, hgetlt i _ hi⟩
  · intro e he i q k' op' d hi
    rw [hL] at he
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨hil, he'⟩
    · rw [hevT i hil]; exact h.ent_invT e he i q k' op' d hi'
    · have := hinvev _ _ _ _ _ he'.symm; have := hentlt e he; omega
  · intro e he i y hi hy
    rw [hL] at he
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨hil, he'⟩
    · rw [hevT i hil]; exact h.ent_endT e he i y hi' hy
    · subst he'; exact absurd hy (hendnew _)
  · intro id resp d hr
    rcases (hmemH _).1 hr with hr | hr
    · exact h.complete id resp d hr
    · simp [ev] at hr
  · intro id q k' op' d hm y hy hyend
    rcases (hmemH y).1 hy with hy | hy
    · rcases (hmemH _).1 hm with hm | hm
      · exact h.mono id q k' op' d hm y hy hyend
      · have := hinvev _ _ _ _ _ hm.symm; subst this
        have := h.end_lt y hy _ hyend; omega
    · subst hy; exact absurd hyend (hendnew _)
  · intro id q k' op' d hm y hy hyend hlt
    rcases (hmemH y).1 hy with hy | hy
    · rcases (hmemH _).1 hm with hm | hm
      · exact h.took id q k' op' d hm y hy hyend hlt
      · have := hinvev _ _ _ _ _ hm.symm; subst this
        have := h.end_lt y hy _ hyend; omega
    · subst hy; exact absurd hyend (hendnew _)
  · intro id q k' op' d hm hrd
    rcases (hmemH _).1 hrd with hrd | hrd
    · rcases (hmemH _).1 hm with hm | hm
      · exact h.noeff id q k' op' d hm hrd
      · have := hinvev _ _ _ _ _ hm.symm; subst this
        have := h.end_lt _ hrd _ rfl; omega
    · simp [ev] at hrd

/-- The new orphan at a crash. -/
def crashOrph (st : APS P K V) (p : P) (b : Bool) : Option (Orph P K V) :=
  match b, st.pc, st.op with
  | true, .at c, some r => scArgs p r.k r.op c
  | _, _, _ => none

theorem crash_eq (a : AS P K V) (p : P) (b : Bool) :
    a.crash p b = { a with ps := Function.update a.ps p ⟨.at (.recv 0), (a.ps p).op,
      (crashOrph (a.ps p) p b).orElse fun _ => (a.ps p).orph⟩, hist := a.hist ++ [.crash p] } := by
  rfl

theorem GInv.crash {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V} (b : Bool)
    (h : GInv init a g) (hop : (a.ps p).op = some r) :
    GInv init (a.crash p b) (g.tick a.hist.length g.L) := by
  rw [crash_eq]
  set st' : APS P K V := ⟨.at (.recv 0), (a.ps p).op,
      (crashOrph (a.ps p) p b).orElse fun _ => (a.ps p).orph⟩
  set g' : Gh P K V := g.tick a.hist.length g.L
  set ev : Ev P K V := Ev.crash p
  -- first the local change, then the event
  have hgo : GInv init { a with ps := Function.update a.ps p st' } g := by
    apply h.go hop st' (by simp [st', hop])
    have := crash_actor (crashOrph (a.ps p) p b) (h.loc p r hop) (h.kinv r.k) (by
      unfold crashOrph
      rcases b with _ | _
      · exact Or.inl rfl
      · rcases hpc : (a.ps p).pc with c | ⟨c, b'⟩
        · right; refine ⟨c, hpc, ?_⟩; simp [hop]; rfl
        · left; rfl)
    exact this
  set a1 : AS P K V := { a with ps := Function.update a.ps p st' }
  have hhist : a1.hist = a.hist := rfl
  have hget : ∀ i y, (a1.hist ++ [ev])[i]? = some y →
      (i < a.hist.length ∧ a.hist[i]? = some y) ∨ (i = a.hist.length ∧ y = ev) :=
    fun i y hy => getElem?_append_one hy
  have hevT : ∀ i, i < a.hist.length → g'.evT i = g.evT i :=
    fun i hi => by simp [g', Gh.invk, Gh.tick, Function.update_of_ne (Nat.ne_of_lt hi)]
  have hmemH : ∀ y, y ∈ a1.hist ++ [ev] ↔ y ∈ a.hist ∨ y = ev := by intro y; simp [hhist]
  have hgetlt : ∀ i y, a.hist[i]? = some y → (a1.hist ++ [ev])[i]? = some y :=
    fun i y hi => by rw [hhist, getElem?_append_one_of_lt (lt_length_of_getElem? hi)]; exact hi
  have hendnew : ∀ id, ¬ ev.Ends id := fun id h' => by simp [ev, Ev.Ends] at h'
  have hinvnew : ∀ id q k op d, ev ≠ Ev.inv id q k op d := by intros; simp [ev]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := hgo
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, h11, h12.mono (by simp [g', Gh.tick]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q s hs
    obtain ⟨i, hi, ht⟩ := h7 q s hs
    exact ⟨i, hgetlt i _ hi, by rw [hevT i (lt_length_of_getElem? hi)]; exact ht⟩
  · intro q s hs e he
    rcases (hmemH e).1 he with he | rfl
    · exact h8 q s hs e he
    · exact hendnew _
  · intro q s hs; have := h9 q s hs; simp only [g', Gh.invk, Gh.tick]; omega
  · intro q s hs t ht
    obtain ⟨a1', a2, a3, a4⟩ := h10 q s hs t ht
    exact ⟨a1', by simp only [g', Gh.invk, Gh.tick]; omega, a3, a4⟩
  · intro i j hij hj
    simp only [List.length_append, List.length_singleton, hhist] at hj
    have hil : i < a.hist.length := by omega
    rw [hevT i hil]
    rcases Nat.lt_or_ge j a.hist.length with hj' | hj'
    · rw [hevT j hj']; exact h13 i j hij hj'
    · have : j = a.hist.length := by omega
      subst this; simp only [g', Gh.invk, Gh.tick, Function.update_self]; exact h14 i hil
  · intro i hi
    simp only [List.length_append, List.length_singleton, hhist] at hi
    rcases Nat.lt_or_ge i a.hist.length with hi' | hi'
    · rw [hevT i hi']; have := h14 i hi'; simp only [g', Gh.invk, Gh.tick]; omega
    · have : i = a.hist.length := by omega
      subst this; simp [g', Gh.invk, Gh.tick]
  · intro id q k op d hm
    rcases (hmemH _).1 hm with hm | hm
    · exact h15 id q k op d hm
    · exact absurd hm.symm (hinvnew _ _ _ _ _)
  · intro e he id hid
    rcases (hmemH e).1 he with he | rfl
    · exact h16 e he id hid
    · exact absurd hid (hendnew _)
  · intro i j id q k op d q' k' op' d' hi hj
    rcases hget i _ hi with ⟨_, hi'⟩ | ⟨_, he⟩
    · rcases hget j _ hj with ⟨_, hj'⟩ | ⟨_, he⟩
      · exact h17 i j id q k op d q' k' op' d' hi' hj'
      · exact absurd he.symm (hinvnew _ _ _ _ _)
    · exact absurd he.symm (hinvnew _ _ _ _ _)
  · intro e he
    obtain ⟨i, q, d, hi⟩ := h18 e he
    exact ⟨i, q, d, hgetlt i _ hi⟩
  · intro e he i q k op d hi
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨_, he'⟩
    · rw [hevT i hil]; exact h19 e he i q k op d hi'
    · exact absurd he'.symm (hinvnew _ _ _ _ _)
  · intro e he i y hi hy
    rcases hget i _ hi with ⟨hil, hi'⟩ | ⟨_, rfl⟩
    · rw [hevT i hil]; exact h20 e he i y hi' hy
    · exact absurd hy (hendnew _)
  · intro id resp d hr
    rcases (hmemH _).1 hr with hr | hr
    · exact h21 id resp d hr
    · simp [ev] at hr
  · intro id q k op d hm y hy hyend
    rcases (hmemH _).1 hm with hm | hm
    · rcases (hmemH y).1 hy with hy | rfl
      · exact h22 id q k op d hm y hy hyend
      · exact absurd hyend (hendnew _)
    · exact absurd hm.symm (hinvnew _ _ _ _ _)
  · intro id q k op d hm y hy hyend hlt
    rcases (hmemH _).1 hm with hm | hm
    · rcases (hmemH y).1 hy with hy | rfl
      · exact h23 id q k op d hm y hy hyend hlt
      · exact absurd hyend (hendnew _)
    · exact absurd hm.symm (hinvnew _ _ _ _ _)
  · intro id q k op d hm hrd
    rcases (hmemH _).1 hm with hm | hm
    · rcases (hmemH _).1 hrd with hrd | hrd
      · exact h24 id q k op d hm hrd
      · simp [ev] at hrd
    · exact absurd hm.symm (hinvnew _ _ _ _ _)

end Podc.DuraCAS
