import Papers.PODC2018.JupiterListSpec.System

/-!
# Generic invariants of the client/server system

Everything here holds for every protocol (`Proto`) whose clients keep their list equal to the
list of their current vertex. The ghost state is related to a schedule `S` (`Compat`): the
server order fixes the ranks of the operations already processed by the server, the pending
operations of each client come after them in FIFO order. We use a *prophecy*: the schedule is the
one of the final configuration of the execution (`schedOf`), and every intermediate configuration
is compatible with it (`Compat.of_step`).

* `RF` — rank-free invariants (FIFO structure, freshness of identifiers);
* `GI` — the schedule axioms `Sched.WF` hold for the generated operations, the knowledge of a
  client is "own operations + a prefix of the server order", contexts are knowledge snapshots;
* `GI.vert_know` — the state of every client is a vertex of the global state space.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

/-! ### Local generation -/

theorem genOp_real {x : Oid n} {u : UOp} {l : List (Oid n)} (hx : x ∉ l) :
    Real (genOp x u l).1 (genOp x u l).1 l := by
  cases u with
  | ins k => simp [genOp, Real, hx]
  | del k =>
    unfold genOp
    cases hl : l[min k (l.length - 1)]? <;> simp [Real, hl]
  | read => simp [genOp, Real]

theorem genOp_ok {x a : Oid n} {u : UOp} {l : List (Oid n)} {p pr : ℕ}
    (h : (genOp x u l).1 = .ins a p pr) : a = x ∧ pr = x.1.val := by
  cases u with
  | ins k => simp only [genOp, LOp.ins.injEq] at h; exact ⟨h.1.symm, h.2.2.symm⟩
  | del k =>
    unfold genOp at h
    cases hl : l[min k (l.length - 1)]? <;> simp [hl] at h
  | read => simp [genOp] at h

theorem genOp_ins_iff {x a : Oid n} {u : UOp} {l : List (Oid n)} :
    (∃ k, (genOp x u l).2 = .ins a k) ↔ ∃ p pr, (genOp x u l).1 = .ins a p pr := by
  cases u with
  | ins k => simp [genOp, eq_comm]
  | del k =>
    unfold genOp
    cases hl : l[min k (l.length - 1)]? <;> simp [hl]
  | read => simp [genOp]

theorem genOp_del_iff {x a : Oid n} {u : UOp} {l : List (Oid n)} :
    (∃ k, (genOp x u l).2 = .del (some a) k) ↔ ∃ p, (genOp x u l).1 = .del a p := by
  cases u with
  | ins k => simp [genOp]
  | del k =>
    unfold genOp
    cases hl : l[min k (l.length - 1)]? <;> simp [hl]
  | read => simp [genOp]

theorem genOp_ret {x a : Oid n} {u : UOp} {l : List (Oid n)} {k : ℕ} (hx : x ∉ l)
    (h : (genOp x u l).2 = .ins a k) :
    ((genOp x u l).1.apply l)[min k (((genOp x u l).1.apply l).length - 1)]? = some a := by
  cases u with
  | ins k' =>
    simp only [genOp, Sig.ins.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    have hR : Real (LOp.ins x (min k' l.length) x.1.val) (LOp.ins x (min k' l.length) x.1.val) l :=
      by simp [Real, hx]
    have hlen : ((LOp.ins x (min k' l.length) x.1.val).apply l).length = l.length + 1 := by
      simp [LOp.apply, List.length_insertIdx]
    simp only [genOp]
    rw [hlen, Nat.add_sub_cancel]
    exact hR.getElem?_ins
  | del k' =>
    unfold genOp at h
    cases hl : l[min k' (l.length - 1)]? <;> simp [hl] at h
  | read => simp [genOp] at h

/-! ### Rank-free invariants -/

variable {P : Proto n}

namespace Cfg

/-- Rank-free invariants. -/
structure RF (cfg : Cfg P) : Prop where
  sv_nodup : cfg.sv.Nodup
  sv_sub : ∀ x ∈ cfg.sv, x ∈ cfg.D
  up : ∀ c, (cfg.up c).map P.oidOf =
    (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv))
  fresh : ∀ r ∈ cfg.log, r.oid.2 < cfg.seq r.oid.1
  lognd : (cfg.log.map Rec.oid).Nodup

theorem mem_D {cfg : Cfg P} {x : Oid n} : x ∈ cfg.D ↔ ∃ r ∈ cfg.log, r.oid = x := by
  simp [D]

theorem RF.init : (init P).RF := by
  refine ⟨by simp [Cfg.init], by simp [Cfg.init], fun c => by simp [Cfg.init], by simp [Cfg.init],
    by simp [Cfg.init]⟩

/-- The configuration after `do c u`. -/
def doCfg (g : Oid n → UOp → List (Oid n) → LOp (Oid n) × Sig (Oid n)) (cfg : Cfg P) (c : Fin n)
    (u : UOp) : Cfg P :=
  let x : Oid n := (c, cfg.seq c)
  let l := P.list (cfg.cs c)
  let og := g x u l
  let r := P.cdo c x og.1 (cfg.cs c)
  { cfg with
      cs := Function.update cfg.cs c r.1
      up := Function.update cfg.up c (cfg.up c ++ [r.2])
      seq := Function.update cfg.seq c (cfg.seq c + 1)
      log := cfg.log ++ [⟨x, og.1, cfg.know c, og.2, og.1.apply l⟩]
      know := Function.update cfg.know c (insert x (cfg.know c)) }

theorem step_do {g} {cfg cfg' : Cfg P} {c : Fin n} {u : UOp}
    (h : cfg.step g (.do c u) = some cfg') : cfg' = doCfg g cfg c u := by
  simp only [step, Option.some.injEq] at h; exact h.symm

theorem step_srv {g} {cfg cfg' : Cfg P} {c : Fin n} (h : cfg.step g (.srv c) = some cfg') :
    ∃ m rest s' m', cfg.up c = m :: rest ∧ P.srecv c m cfg.ss = some (s', m') ∧
      cfg' = { cfg with
          ss := s'
          up := Function.update cfg.up c rest
          down := fun j => if j = c then cfg.down j else cfg.down j ++ [m']
          sv := cfg.sv ++ [P.oidOf m] } := by
  simp only [step] at h
  split at h
  · cases h
  · rename_i m rest hup
    split at h
    · cases h
    · rename_i s' m' hs
      exact ⟨m, rest, s', m', hup, hs, (Option.some.inj h).symm⟩

theorem step_recv {g} {cfg cfg' : Cfg P} {c : Fin n} (h : cfg.step g (.recv c) = some cfg') :
    ∃ m rest s', cfg.down c = m :: rest ∧ P.crecv c m (cfg.cs c) = some s' ∧
      cfg' = { cfg with
          cs := Function.update cfg.cs c s'
          down := Function.update cfg.down c rest
          know := Function.update cfg.know c (insert (P.oidOf m) (cfg.know c)) } := by
  simp only [step] at h
  split at h
  · cases h
  · rename_i m rest hdown
    split at h
    · cases h
    · rename_i s' hs
      exact ⟨m, rest, s', hdown, hs, (Option.some.inj h).symm⟩

theorem RF.fresh_notMem {cfg : Cfg P} (h : cfg.RF) (c : Fin n) : (c, cfg.seq c) ∉ cfg.D := by
  intro hx
  obtain ⟨r, hr, hro⟩ := mem_D.1 hx
  have := h.fresh r hr
  rw [hro] at this
  simp at this

theorem RF.step {cfg cfg' : Cfg P} (h : cfg.RF) {e : Ev n} (hs : cfg.step genOp e = some cfg') :
    cfg'.RF := by
  cases e with
  | «do» c u =>
    obtain rfl := step_do hs
    have hxD := h.fresh_notMem c
    have hxsv : (c, cfg.seq c) ∉ cfg.sv := fun hx => hxD (h.sv_sub _ hx)
    refine ⟨h.sv_nodup, fun x hx => ?_, fun c' => ?_, fun r hr => ?_, ?_⟩
    · simp only [doCfg, D, List.map_append, List.toFinset_append, Finset.mem_union]
      exact Or.inl (h.sv_sub x hx)
    · simp only [doCfg]
      by_cases hc : c' = c
      · subst hc
        simp only [Function.update_self, List.map_append, List.map_cons, List.map_nil,
          List.filter_append, h.up c']
        simp [P.oidOf_cdo, hxsv]
        apply List.filter_congr; intro x _
        by_cases h1 : x.1 = c' <;> by_cases h2 : x ∈ cfg.sv <;> simp [h1, h2]
      · simp only [Function.update_of_ne hc, List.map_append, List.filter_append, h.up c']
        simp [Ne.symm hc]
        apply List.filter_congr; intro x _
        by_cases h1 : x.1 = c' <;> by_cases h2 : x ∈ cfg.sv <;> simp [h1, h2]
    · simp only [doCfg, List.mem_append, List.mem_singleton] at hr ⊢
      rcases hr with hr | rfl
      · have := h.fresh r hr
        by_cases hc : r.oid.1 = c
        · rw [hc, Function.update_self]; rw [hc] at this; omega
        · rw [Function.update_of_ne hc]; exact this
      · simp
    · simp only [doCfg, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨h.lognd, by simp, ?_⟩
      simp only [List.mem_singleton]
      rintro a ha b rfl rfl
      exact hxD (List.mem_toFinset.2 ha)
  | srv c =>
    obtain ⟨m, rest, s', m', hup, hsr, rfl⟩ := step_srv hs
    have hfil := h.up c
    rw [hup, List.map_cons] at hfil
    have hm : P.oidOf m ∈ (cfg.log.map Rec.oid).filter
        (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by rw [← hfil]; simp
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    obtain ⟨hmlog, hmc, hmsv⟩ := hm
    refine ⟨?_, ?_, fun c' => ?_, h.fresh, h.lognd⟩
    · rw [List.nodup_append]
      exact ⟨h.sv_nodup, by simp, by simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hmsv ha⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h.sv_sub x hx
      · simpa [D] using hmlog
    · simp only
      by_cases hc : c' = c
      · subst hc
        rw [Function.update_self]
        have hnd : ((cfg.log.map Rec.oid).filter
            (fun x => decide (x.1 = c' ∧ x ∉ cfg.sv))).Nodup := h.lognd.filter _
        rw [← hfil, List.nodup_cons] at hnd
        have : (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c' ∧ x ∉ cfg.sv ++ [P.oidOf m]))
            = ((cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c' ∧ x ∉ cfg.sv))).filter
              (fun x => decide (x ≠ P.oidOf m)) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro x _
          simp only [List.mem_append, List.mem_singleton, not_or]
          by_cases h1 : x.1 = c' <;> by_cases h2 : x ∈ cfg.sv <;>
            by_cases h3 : x = P.oidOf m <;> simp [h1, h2, h3]
        rw [this, ← hfil, List.filter_cons_of_neg (by simp)]
        rw [List.filter_eq_self.2]
        intro x hx
        simp only [decide_eq_true_eq]
        rintro rfl
        exact hnd.1 hx
      · rw [Function.update_of_ne hc, h.up c']
        apply List.filter_congr
        intro x _
        simp only [List.mem_append, List.mem_singleton, not_or, decide_eq_decide]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by rintro rfl; exact hc (h1.symm.trans hmc)⟩
        · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  | recv c =>
    obtain ⟨m, rest, s', hdown, hcr, rfl⟩ := step_recv hs
    exact ⟨h.sv_nodup, h.sv_sub, h.up, h.fresh, h.lognd⟩

/-- Reachable configurations, with the invariant carried along. -/
theorem run_induction {g} {Q : Cfg P → Prop} (h0 : Q (init P))
    (hs : ∀ cfg cfg' e, Q cfg → cfg.step g e = some cfg' → Q cfg') :
    ∀ {es : List (Ev n)} {cfg : Cfg P}, run g P es = some cfg → Q cfg := by
  intro es cfg h
  suffices ∀ (c0 : Cfg P), Q c0 → ∀ cfg, es.foldlM (step g) c0 = some cfg → Q cfg from
    this _ h0 _ h
  clear h cfg
  induction es with
  | nil => intro c0 hc0 cfg h; simp at h; exact h ▸ hc0
  | cons e es ih =>
    intro c0 hc0 cfg h
    simp only [List.foldlM_cons] at h
    cases hstep : step g c0 e with
    | none => rw [hstep] at h; cases h
    | some c1 =>
      rw [hstep] at h
      exact ih c1 (hs _ _ _ hc0 hstep) cfg h

theorem RF.run {es : List (Ev n)} {cfg : Cfg P} (h : run genOp P es = some cfg) : cfg.RF :=
  run_induction RF.init (fun _ _ _ hc hs => hc.step hs) h

end Cfg


/-! ### Schedules compatible with a configuration -/

namespace Cfg

/-- A schedule `S` is compatible with `cfg`: it agrees with the generated operations, ranks the
server's operations by their position in `sv`, and puts each client's pending operations after
them in FIFO order. -/
structure Compat (S : Sched (Oid n)) (cfg : Cfg P) : Prop where
  cl : ∀ x, S.cl x = x.1.val
  orig : ∀ r ∈ cfg.log, S.orig r.oid = r.lop
  ctx : ∀ r ∈ cfg.log, S.ctx r.oid = r.ctx
  rank_sv : ∀ i (h : i < cfg.sv.length), S.rank cfg.sv[i] = i
  sv_of_rank : ∀ x, S.rank x < cfg.sv.length → x ∈ cfg.sv
  rank_up : ∀ c, ∀ m ∈ cfg.up c, cfg.sv.length ≤ S.rank (P.oidOf m)
  up_sorted : ∀ c, ((cfg.up c).map fun m => S.rank (P.oidOf m)).Pairwise (· < ·)
  inj : Set.InjOn S.rank ↑cfg.D

theorem Compat.of_step {S : Sched (Oid n)} {cfg cfg' : Cfg P} (h : Compat S cfg') {e : Ev n}
    (hs : cfg.step genOp e = some cfg') : Compat S cfg := by
  cases e with
  | «do» c u =>
    obtain rfl := step_do hs
    refine ⟨h.cl, fun r hr => h.orig r ?_, fun r hr => h.ctx r ?_, h.rank_sv, h.sv_of_rank,
      fun c' m hm => h.rank_up c' m ?_, fun c' => ?_, h.inj.mono ?_⟩
    · simp [doCfg, hr]
    · simp [doCfg, hr]
    · by_cases hc : c' = c
      · subst hc; simp [doCfg, hm]
      · simpa [doCfg, Function.update_of_ne hc] using hm
    · have := h.up_sorted c'
      by_cases hc : c' = c
      · subst hc
        simp only [doCfg, Function.update_self, List.map_append] at this
        exact this.sublist (List.sublist_append_left _ _)
      · simpa [doCfg, Function.update_of_ne hc] using this
    · intro x hx
      simp only [doCfg, D, Finset.coe_sort_coe, Finset.mem_coe, List.mem_toFinset, List.map_append,
        List.mem_append] at hx ⊢
      exact Or.inl hx
  | srv c =>
    obtain ⟨m, rest, s', m', hup, hsr, rfl⟩ := step_srv hs
    have hrm : S.rank (P.oidOf m) = cfg.sv.length := by
      have := h.rank_sv cfg.sv.length (by simp)
      simpa using this
    refine ⟨h.cl, h.orig, h.ctx, fun i hi => ?_, fun x hx => ?_, fun c' m'' hm'' => ?_,
      fun c' => ?_, h.inj⟩
    · have := h.rank_sv i (by simp; omega)
      simpa [List.getElem_append_left hi] using this
    · have := h.sv_of_rank x (by simp; omega)
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h1 | rfl
      · exact h1
      · omega
    · by_cases hc : c' = c
      · subst hc
        rw [hup] at hm''
        rcases List.mem_cons.1 hm'' with rfl | hm''
        · omega
        · have := h.rank_up c' m'' (by simp [hm''])
          simp at this; omega
      · have := h.rank_up c' m'' (by simpa [Function.update_of_ne hc] using hm'')
        simp at this; omega
    · by_cases hc : c' = c
      · subst hc
        have h1 := h.up_sorted c'
        simp only [Function.update_self] at h1
        rw [hup, List.map_cons, List.pairwise_cons]
        refine ⟨fun a ha => ?_, h1⟩
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
        have := h.rank_up c' b (by simp [hb])
        simp at this; omega
      · simpa [Function.update_of_ne hc] using h.up_sorted c'
  | recv c =>
    obtain ⟨m, rest, s', hdown, hcr, rfl⟩ := step_recv hs
    exact ⟨h.cl, h.orig, h.ctx, h.rank_sv, h.sv_of_rank, h.rank_up, h.up_sorted, h.inj⟩

/-- The pending (not yet server-processed) operations in generation order. -/
def pend (cfg : Cfg P) : List (Oid n) := (cfg.log.map Rec.oid).filter (· ∉ cfg.sv)

/-- The prophesied server order: the processed operations, then the pending ones. -/
def order (cfg : Cfg P) : List (Oid n) := cfg.sv ++ cfg.pend

/-- The schedule of a configuration. -/
def schedOf (cfg : Cfg P) : Sched (Oid n) where
  rank x := cfg.order.idxOf x
  cl x := x.1.val
  orig x := ((cfg.log.find? fun r => r.oid = x).map Rec.lop).getD .nop
  ctx x := ((cfg.log.find? fun r => r.oid = x).map Rec.ctx).getD ∅

theorem _root_.List.idxOf_lt_of_pair_sublist {α : Type} [DecidableEq α] {l : List α}
    (hl : l.Nodup) {a b : α} (h : [a, b].Sublist l) : l.idxOf a < l.idxOf b := by
  induction l with
  | nil => simp at h
  | cons d t ih =>
    rw [List.nodup_cons] at hl
    rw [List.sublist_cons_iff] at h
    rcases h with h | ⟨r, hr, h⟩
    · have ha : a ≠ d := fun e => hl.1 (e ▸ h.subset (by simp))
      have hb : b ≠ d := fun e => hl.1 (e ▸ h.subset (by simp))
      rw [List.idxOf_cons_ne _ (Ne.symm ha), List.idxOf_cons_ne _ (Ne.symm hb)]
      exact Nat.succ_lt_succ (ih hl.2 h)
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hb : b ≠ a := fun e => hl.1 (e ▸ h.subset (by simp))
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hb)]
      exact Nat.succ_pos _

theorem RF.order_nodup {cfg : Cfg P} (h : cfg.RF) : cfg.order.Nodup := by
  rw [order, List.nodup_append]
  refine ⟨h.sv_nodup, h.lognd.filter _, ?_⟩
  intro a ha b hb rfl
  simp [pend] at hb
  exact hb.2 ha

theorem RF.mem_order {cfg : Cfg P} (h : cfg.RF) {x : Oid n} (hx : x ∈ cfg.D) : x ∈ cfg.order := by
  by_cases hs : x ∈ cfg.sv
  · simp [order, hs]
  · simp [order, pend, hs]; simpa [D] using hx

theorem RF.find_log {cfg : Cfg P} (h : cfg.RF) {r : Rec n} (hr : r ∈ cfg.log) :
    cfg.log.find? (fun r' => r'.oid = r.oid) = some r := by
  obtain ⟨r', hr'⟩ : ∃ r', cfg.log.find? (fun r' => r'.oid = r.oid) = some r' := by
    cases hf : cfg.log.find? (fun r' => r'.oid = r.oid) with
    | none => rw [List.find?_eq_none] at hf; exact absurd (hf r hr) (by simp)
    | some r' => exact ⟨r', rfl⟩
  have hmem := List.mem_of_find?_eq_some hr'
  have hp := List.find?_some hr'
  simp only [decide_eq_true_eq] at hp
  rw [hr', List.inj_on_of_nodup_map h.lognd hmem hr hp]

theorem RF.compat {cfg : Cfg P} (h : cfg.RF) : Compat (schedOf cfg) cfg := by
  have hnd := h.order_nodup
  refine ⟨fun x => rfl, fun r hr => ?_, fun r hr => ?_, fun i hi => ?_, fun x hx => ?_,
    fun c m hm => ?_, fun c => ?_, ?_⟩
  · simp [schedOf, h.find_log hr]
  · simp [schedOf, h.find_log hr]
  · show cfg.order.idxOf cfg.sv[i] = i
    rw [order, List.idxOf_append_of_mem (List.getElem_mem hi)]
    exact h.sv_nodup.idxOf_getElem i hi
  · by_contra hs
    have : (schedOf cfg).rank x = cfg.sv.length + cfg.pend.idxOf x := by
      simp [schedOf, order, List.idxOf_append_of_notMem hs]
    omega
  · have hfil := h.up c
    have hmem : P.oidOf m ∈ (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv))
      := by rw [← hfil]; exact List.mem_map_of_mem hm
    simp only [List.mem_filter, decide_eq_true_eq] at hmem
    show cfg.sv.length ≤ cfg.order.idxOf (P.oidOf m)
    rw [order, List.idxOf_append_of_notMem hmem.2.2]
    omega
  · rw [show ((cfg.up c).map fun m => (schedOf cfg).rank (P.oidOf m)) =
      ((cfg.up c).map P.oidOf).map cfg.order.idxOf by simp [schedOf]]
    rw [List.pairwise_map, h.up c]
    have hsub : ((cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv))).Sublist
        cfg.order := by
      refine List.Sublist.trans ?_ (List.sublist_append_right cfg.sv _)
      rw [pend]
      apply List.monotone_filter_right
      intro a ha
      simp only [decide_eq_true_eq] at ha ⊢
      exact ha.2
    exact List.pairwise_of_forall_sublist fun hab =>
      List.idxOf_lt_of_pair_sublist hnd (hab.trans hsub)
  · intro x hx y hy hxy
    exact List.idxOf_inj (h.mem_order hx) |>.1 hxy |> fun e => e
end Cfg

/-! ### The generic invariant -/

namespace Cfg

/-- The generic invariant w.r.t. a schedule `S`. -/
structure GI (S : Sched (Oid n)) (cfg : Cfg P) : Prop where
  compat : Compat S cfg
  rf : cfg.RF
  wf : S.WF ↑cfg.D
  know : ∀ c x, x ∈ cfg.know c ↔ (x ∈ cfg.D ∧ x.1 = c) ∨
    (x ∈ cfg.sv ∧ x.1 ≠ c ∧ ∀ m ∈ cfg.down c, S.rank x < S.rank (P.oidOf m))
  down : ∀ c, (cfg.down c).map P.oidOf =
    cfg.sv.filter (fun x => decide (x.1 ≠ c ∧ x ∉ cfg.know c))
  ctx_know : ∀ r ∈ cfg.log, r.ctx ⊆ cfg.know r.oid.1
  recs : ∀ r ∈ cfg.log, (∃ u, genOp r.oid u (S.L r.ctx) = (r.lop, r.sig)) ∧
    r.ret = r.lop.apply (S.L r.ctx)
  ctx_log : ∀ (i : ℕ) (r : Rec n), cfg.log[i]? = some r → ∀ y ∈ r.ctx, ∃ j < i, ∃ r' : Rec n,
    cfg.log[j]? = some r' ∧ r'.oid = y

variable {S : Sched (Oid n)} {cfg : Cfg P}

theorem Compat.rank_of_mem_sv (h : Compat S cfg) (hnd : cfg.sv.Nodup) {x : Oid n}
    (hx : x ∈ cfg.sv) : S.rank x = cfg.sv.idxOf x := by
  have hi := List.idxOf_lt_length_of_mem hx
  have := h.rank_sv _ hi
  rwa [List.getElem_idxOf hi] at this

theorem Compat.rank_lt_of_mem_sv (h : Compat S cfg) (hnd : cfg.sv.Nodup) {x : Oid n}
    (hx : x ∈ cfg.sv) : S.rank x < cfg.sv.length := by
  rw [h.rank_of_mem_sv hnd hx]; exact List.idxOf_lt_length_of_mem hx

theorem GI.sv_D (h : GI S cfg) {x : Oid n} (hx : x ∈ cfg.sv) : x ∈ cfg.D := h.rf.sv_sub x hx

theorem GI.know_D (h : GI S cfg) {c : Fin n} {x : Oid n} (hx : x ∈ cfg.know c) : x ∈ cfg.D := by
  rcases (h.know c x).1 hx with ⟨hx, -⟩ | ⟨hx, -⟩
  · exact hx
  · exact h.sv_D hx

theorem GI.down_sv (h : GI S cfg) {c : Fin n} {m : P.Msg} (hm : m ∈ cfg.down c) :
    P.oidOf m ∈ cfg.sv ∧ (P.oidOf m).1 ≠ c ∧ P.oidOf m ∉ cfg.know c := by
  have : P.oidOf m ∈ (cfg.down c).map P.oidOf := List.mem_map_of_mem hm
  rw [h.down c] at this
  simp only [List.mem_filter, decide_eq_true_eq] at this
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- Messages on a down channel are in increasing rank. -/
theorem GI.down_sorted (h : GI S cfg) (c : Fin n) :
    ((cfg.down c).map fun m => S.rank (P.oidOf m)).Pairwise (· < ·) := by
  have hm : ((cfg.down c).map fun m => S.rank (P.oidOf m)) =
      ((cfg.down c).map P.oidOf).map S.rank := by simp
  rw [hm, h.down c, List.pairwise_map]
  have hsub : (cfg.sv.filter fun x => decide (x.1 ≠ c ∧ x ∉ cfg.know c)).Sublist cfg.sv :=
    List.filter_sublist
  refine List.pairwise_of_forall_sublist fun {a b} hab => ?_
  have hab' := hab.trans hsub
  rw [h.compat.rank_of_mem_sv h.rf.sv_nodup (hab'.subset (by simp)),
    h.compat.rank_of_mem_sv h.rf.sv_nodup (hab'.subset (by simp))]
  exact List.idxOf_lt_of_pair_sublist h.rf.sv_nodup hab'

/-- Every operation of a client's context is in its knowledge, and the knowledge is causally
closed. -/
theorem GI.ctx_sub_know (h : GI S cfg) {c : Fin n} {j : Oid n} (hj : j ∈ cfg.know c) :
    S.ctx j ⊆ cfg.know c := by
  have hjD := h.know_D hj
  intro i hi
  rcases (h.know c j).1 hj with ⟨-, hjc⟩ | ⟨hjsv, hjc, hjdown⟩
  · obtain ⟨r, hr, rfl⟩ := mem_D.1 hjD
    rw [h.compat.ctx r hr] at hi
    exact hjc ▸ h.ctx_know r hr hi
  · have hlt := h.wf.ctx_lt j hjD i hi
    have hiD : i ∈ cfg.D := h.wf.ctx_sub j hjD hi
    have hisv : i ∈ cfg.sv := h.compat.sv_of_rank i
      (lt_trans hlt (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjsv))
    by_cases hic : i.1 = c
    · exact (h.know c i).2 (Or.inl ⟨hiD, hic⟩)
    · exact (h.know c i).2 (Or.inr ⟨hisv, hic, fun m hm => lt_trans hlt (hjdown m hm)⟩)

/-- The state of every client is a vertex of the global state space. -/
theorem GI.vert_know (h : GI S cfg) (c : Fin n) : S.Vert (cfg.know c) := by
  refine ⟨fun j hj => h.ctx_sub_know hj, ?_⟩
  let s := match cfg.down c with
    | [] => cfg.sv.length
    | m :: _ => S.rank (P.oidOf m)
  have hs_le : s ≤ cfg.sv.length := by
    simp only [s]; split
    · exact le_rfl
    · rename_i m _ hd
      exact (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup
        (h.down_sv (hd ▸ List.mem_cons_self)).1).le
  have hs_down : ∀ m ∈ cfg.down c, s ≤ S.rank (P.oidOf m) := by
    intro m hm
    have hsrt := h.down_sorted c
    simp only [s]; split
    · rename_i hd; rw [hd] at hm; simp at hm
    · rename_i m0 rest hd
      rw [hd] at hm hsrt
      rcases List.mem_cons.1 hm with rfl | hm
      · exact le_rfl
      · simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hsrt
        exact (hsrt.1 _ ⟨m, hm, rfl⟩).le
  refine ⟨s, c.val, fun x hx => ?_, fun x hx hxs => ?_⟩
  · have hxsv := h.compat.sv_of_rank x (lt_of_lt_of_le hx hs_le)
    by_cases hxc : x.1 = c
    · exact (h.know c x).2 (Or.inl ⟨h.sv_D hxsv, hxc⟩)
    · exact (h.know c x).2 (Or.inr ⟨hxsv, hxc, fun m hm => lt_of_lt_of_le hx (hs_down m hm)⟩)
  · rw [h.compat.cl]
    rcases (h.know c x).1 hx with ⟨-, hxc⟩ | ⟨hxsv, hxc, hxdown⟩
    · rw [hxc]
    · exfalso
      simp only [s] at hxs; split at hxs
      · have := h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hxsv; omega
      · rename_i m0 rest hd
        have := hxdown m0 (by rw [hd]; exact List.mem_cons_self); omega

/-- The server's state is a vertex. -/
theorem GI.vert_sv (h : GI S cfg) : S.Vert cfg.sv.toFinset := by
  refine ⟨fun j hj i hi => ?_, cfg.sv.length, 0, fun x hx => ?_, fun x hx hxs => ?_⟩
  · rw [List.mem_toFinset] at hj ⊢
    exact h.compat.sv_of_rank i (lt_trans (h.wf.ctx_lt j (h.sv_D hj) i hi)
      (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hj))
  · exact List.mem_toFinset.2 (h.compat.sv_of_rank x hx)
  · have := h.compat.rank_lt_of_mem_sv h.rf.sv_nodup (List.mem_toFinset.1 hx); omega

theorem GI.know_sub (h : GI S cfg) (c : Fin n) : ↑(cfg.know c) ⊆ (↑cfg.D : Set (Oid n)) :=
  fun _ hx => h.know_D hx

theorem GI.sv_sub (h : GI S cfg) : ↑cfg.sv.toFinset ⊆ (↑cfg.D : Set (Oid n)) :=
  fun _ hx => h.sv_D (List.mem_toFinset.1 hx)

end Cfg

namespace Cfg

variable {S : Sched (Oid n)}

theorem GI.init (h : Compat S (Cfg.init P)) : GI S (Cfg.init P) := by
  refine ⟨h, RF.init, ?_, fun c x => ?_, fun c => ?_, by simp [Cfg.init], by simp [Cfg.init],
    by simp [Cfg.init]⟩
  · have : ((Cfg.init P).D : Set (Oid n)) = ∅ := by simp [Cfg.init, D]
    rw [this]
    exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  · simp [Cfg.init, D]
  · simp [Cfg.init]

theorem doCfg_D (cfg : Cfg P) (c : Fin n) (u : UOp) :
    (doCfg genOp cfg c u).D = insert (c, cfg.seq c) cfg.D := by
  ext y; simp [doCfg, D, or_comm]

theorem GI.do {cfg : Cfg P} (h : GI S cfg) {c : Fin n} {u : UOp}
    (h' : Compat S (doCfg genOp cfg c u)) (hlist : P.list (cfg.cs c) = S.L (cfg.know c)) :
    GI S (doCfg genOp cfg c u) := by
  set x : Oid n := (c, cfg.seq c) with hx
  set K := cfg.know c with hK
  set og := genOp x u (S.L K) with hog
  have hxD : x ∉ cfg.D := h.rf.fresh_notMem c
  have hD' : (doCfg genOp cfg c u).D = insert x cfg.D := doCfg_D cfg c u
  have hrec : (⟨x, og.1, K, og.2, og.1.apply (S.L K)⟩ : Rec n) ∈ (doCfg genOp cfg c u).log := by
    simp [doCfg, hlist, x, K, og]
  have horig : S.orig x = og.1 := h'.orig _ hrec
  have hctx : S.ctx x = K := h'.ctx _ hrec
  have hcl : ∀ y : Oid n, S.cl y = S.cl x ↔ y.1 = c := by
    intro y; rw [h'.cl, h'.cl]; exact Fin.val_inj
  have hKV := h.vert_know c
  have hKD := h.know_sub c
  -- the new operation is the last of its client
  have hmsg : ∀ m ∈ (doCfg genOp cfg c u).up c, P.oidOf m = x ∨ m ∈ cfg.up c := by
    intro m hm
    simp only [doCfg, Function.update_self, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact Or.inr hm
    · exact Or.inl (P.oidOf_cdo _ _ _ _)
  have hsvx : cfg.sv.length ≤ S.rank x := by
    have := h'.rank_up c (P.cdo c x og.1 (cfg.cs c)).2 (by simp [doCfg, hlist, x, og, K])
    rwa [P.oidOf_cdo] at this
  have hown : ∀ j ∈ cfg.D, j.1 = c → S.rank j < S.rank x := by
    intro j hj hjc
    by_cases hjs : j ∈ cfg.sv
    · exact lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjs) hsvx
    · have : j ∈ (cfg.up c).map P.oidOf := by
        rw [h.rf.up c]; simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨by simpa [D] using hj, hjc, hjs⟩
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 this
      have hs := h'.up_sorted c
      simp only [doCfg, Function.update_self, List.map_append, List.map_cons, List.map_nil] at hs
      rw [List.pairwise_append] at hs
      have := hs.2.2 _ (List.mem_map_of_mem (f := fun m => S.rank (P.oidOf m)) hm) _
        List.mem_cons_self
      rwa [P.oidOf_cdo] at this
  have hlt : ∀ j ∈ K, S.rank j < S.rank x := by
    intro j hj
    rcases (h.know c j).1 hj with ⟨hjD, hjc⟩ | ⟨hjs, -, -⟩
    · exact hown j hjD hjc
    · exact lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjs) hsvx
  have hxK : x ∉ K := fun hxK => hxD (h.know_D hxK)
  have hxL : x ∉ S.L K := fun hxL =>
    hxK ((S.mem_L h.wf hKV hKD x).1 hxL).1
  have hwf : S.WF (↑(doCfg genOp cfg c u).D) := by
    rw [hD', Finset.coe_insert]
    refine h.wf.addOp (h'.inj.mono (by rw [hD', Finset.coe_insert])) (hctx ▸ hKD)
      (hctx ▸ hlt) (fun j hj hc hr => hctx ▸ (h.know c j).2 (Or.inl ⟨hj, (hcl j).1 hc⟩))
      (fun k hk hc => hown k hk ((hcl k).1 hc)) ?_ ?_ ?_ ?_
    · intro j hj hjc i hi
      rw [hctx] at hj ⊢
      rcases (h.know c j).1 hj with ⟨-, hc⟩ | ⟨hjs, -, hjdown⟩
      · exact absurd ((hcl j).2 hc) hjc
      · have his := h.compat.sv_of_rank i
          (lt_of_le_of_lt hi (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjs))
        by_cases hic : i.1 = c
        · exact (h.know c i).2 (Or.inl ⟨h.sv_D his, hic⟩)
        · exact (h.know c i).2 (Or.inr ⟨his, hic, fun m hm => lt_of_le_of_lt hi (hjdown m hm)⟩)
    · intro j hj; rw [hctx] at hj ⊢; exact h.ctx_sub_know hj
    · rw [horig, hctx]; exact genOp_real hxL
    · unfold Sched.OrigOk; rw [horig]
      split
      · rename_i a p pr he
        obtain ⟨rfl, rfl⟩ := genOp_ok he
        exact ⟨rfl, (h'.cl _).symm⟩
      · trivial
  refine ⟨h', h.rf.step (e := .do c u) (by simp [step, doCfg]), hwf, fun c' y => ?_, fun c' => ?_,
    fun r hr => ?_, fun r hr => ?_, fun i r hr y hy => ?_⟩
  · rw [hD']
    by_cases hc : c' = c
    · subst hc
      simp only [doCfg, Function.update_self, Finset.mem_insert, ← hK]
      rw [h.know c' y]
      constructor
      · rintro (rfl | hy)
        · exact Or.inl ⟨Or.inl rfl, rfl⟩
        · rcases hy with ⟨h1, h2⟩ | h1
          · exact Or.inl ⟨Or.inr h1, h2⟩
          · exact Or.inr h1
      · rintro (⟨rfl | h1, h2⟩ | h1)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr h1)
    · simp only [doCfg, Function.update_of_ne hc, Finset.mem_insert]
      rw [h.know c' y]
      constructor
      · rintro (⟨h1, h2⟩ | h1)
        · exact Or.inl ⟨Or.inr h1, h2⟩
        · exact Or.inr h1
      · rintro (⟨rfl | h1, h2⟩ | h1)
        · exact absurd h2.symm hc
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h1
  · simp only [doCfg]
    rw [h.down c']
    apply List.filter_congr
    intro y hy
    by_cases hc : c' = c
    · subst hc
      have hyx : y ≠ (c', cfg.seq c') := by
        rintro rfl; exact hxD (h.sv_D hy)
      simp only [Function.update_self, Finset.mem_insert]
      by_cases h1 : y.1 = c' <;> by_cases h2 : y ∈ cfg.know c' <;> simp [h1, h2, hyx]
    · simp [Function.update_of_ne hc]
  · simp only [doCfg, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · have := h.ctx_know r hr
      by_cases hc : r.oid.1 = c
      · simp only [doCfg, hc, Function.update_self]
        rw [hc] at this
        exact this.trans (Finset.subset_insert _ _)
      · simp only [doCfg, Function.update_of_ne hc]; exact this
    · simp [doCfg]
  · simp only [doCfg, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h.recs r hr
    · simp only [hlist]; exact ⟨⟨u, rfl⟩, rfl⟩
  · simp only [doCfg] at hr
    rcases lt_or_ge i cfg.log.length with hi | hi
    · rw [List.getElem?_append_left hi] at hr
      obtain ⟨j, hj, r', hr', rfl⟩ := h.ctx_log i r hr y hy
      refine ⟨j, hj, r', ?_, rfl⟩
      simp only [doCfg]
      rw [List.getElem?_append_left (lt_trans hj hi)]; exact hr'
    · rw [List.getElem?_append_right hi] at hr
      have hi' : i - cfg.log.length = 0 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hr; cases hr
      rw [hi'] at hr
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      obtain ⟨r', hr', rfl⟩ := mem_D.1 (h.know_D hy)
      obtain ⟨j, hjr⟩ := List.mem_iff_getElem?.1 hr'
      refine ⟨j, ?_, r', ?_, rfl⟩
      · have := (List.getElem?_eq_some_iff.1 hjr).1; omega
      · simp only [doCfg]; rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hjr).1]
        exact hjr

end Cfg

namespace Cfg

variable {S : Sched (Oid n)}

theorem GI.srv {cfg cfg' : Cfg P} (h : GI S cfg) {c : Fin n} (h' : Compat S cfg')
    (hs : cfg.step genOp (.srv c) = some cfg') : GI S cfg' := by
  have hrf' := h.rf.step hs
  obtain ⟨m, rest, s', m', hup, hsr, rfl⟩ := step_srv hs
  have hm'm := P.oidOf_srecv _ _ _ _ _ hsr
  set y := P.oidOf m with hy
  have hfil := h.rf.up c
  rw [hup, List.map_cons] at hfil
  have hmem : y ∈ (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
    rw [← hfil]; exact List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hmem
  obtain ⟨-, hyc, hysv⟩ := hmem
  have hry : S.rank y = cfg.sv.length := by
    have := h'.rank_sv cfg.sv.length (by simp)
    simpa using this
  refine ⟨h', hrf', h.wf, fun j x => ?_, fun j => ?_, h.ctx_know, h.recs, h.ctx_log⟩
  · simp only
    rw [h.know j x]
    by_cases hj : j = c
    · subst hj
      simp only [if_true]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨List.mem_append_left _ h1, h2, h3⟩
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨?_, h2, h3⟩
          rcases List.mem_append.1 h1 with h1 | h1
          · exact h1
          · rw [List.mem_singleton] at h1; exact absurd (h1 ▸ hyc) h2
    · simp only [hj, if_false]
      constructor
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · refine Or.inr ⟨List.mem_append_left _ h1, h2, fun m'' hm'' => ?_⟩
          rcases List.mem_append.1 hm'' with hm'' | hm''
          · exact h3 m'' hm''
          · rw [List.mem_singleton] at hm''; subst hm''
            rw [hm'm, hry]; exact h.compat.rank_lt_of_mem_sv h.rf.sv_nodup h1
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inl h1
        · have hlt := h3 m' (List.mem_append_right _ (List.mem_singleton_self _))
          rw [hm'm] at hlt
          refine Or.inr ⟨?_, h2, fun m'' hm'' => h3 m'' (List.mem_append_left _ hm'')⟩
          rcases List.mem_append.1 h1 with h1 | h1
          · exact h1
          · rw [List.mem_singleton] at h1; rw [h1] at hlt; exact absurd hlt (lt_irrefl _)
  · simp only
    by_cases hj : j = c
    · subst hj
      simp only [if_true, List.filter_append, h.down j]
      simp [hyc]
    · simp only [hj, if_false, List.map_append, h.down j, List.filter_append, List.map_cons,
        List.map_nil, hm'm]
      congr 1
      have hyk : y ∉ cfg.know j := by
        intro hk
        rcases (h.know j y).1 hk with ⟨-, h2⟩ | ⟨h1, -, -⟩
        · exact hj (h2 ▸ hyc)
        · exact hysv h1
      have hyj : y.1 ≠ j := fun e => hj (e ▸ hyc)
      simp [hyk, hyj]

theorem GI.recv {cfg cfg' : Cfg P} (h : GI S cfg) {c : Fin n} (h' : Compat S cfg')
    (hs : cfg.step genOp (.recv c) = some cfg') : GI S cfg' := by
  have hrf' := h.rf.step hs
  obtain ⟨m, rest, s', hdown, hcr, rfl⟩ := step_recv hs
  set y := P.oidOf m with hy
  obtain ⟨hysv, hyc, hyk⟩ := h.down_sv (hdown ▸ List.mem_cons_self)
  have hsrt := h.down_sorted c
  rw [hdown, List.map_cons, List.pairwise_cons] at hsrt
  have hfil := h.down c
  rw [hdown, List.map_cons] at hfil
  refine ⟨h', hrf', h.wf, fun j x => ?_, fun j => ?_, fun r hr => ?_, h.recs, h.ctx_log⟩
  · simp only
    by_cases hj : j = c
    · subst hj
      simp only [Function.update_self, Finset.mem_insert]
      rw [h.know j x]
      constructor
      · rintro (rfl | h1 | ⟨h1, h2, h3⟩)
        · exact Or.inr ⟨hysv, hyc, fun m'' hm'' => hsrt.1 _ (List.mem_map_of_mem hm'')⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2, fun m'' hm'' => h3 m'' (hdown ▸ List.mem_cons_of_mem _ hm'')⟩
      · rintro (h1 | ⟨h1, h2, h3⟩)
        · exact Or.inr (Or.inl h1)
        · by_cases hxk : x ∈ cfg.know j
          · exact Or.inr ((h.know j x).1 hxk)
          · have : x ∈ cfg.sv.filter (fun x => decide (x.1 ≠ j ∧ x ∉ cfg.know j)) := by
              simp [h1, h2, hxk]
            rw [← hfil, List.mem_cons] at this
            rcases this with rfl | this
            · exact Or.inl rfl
            · obtain ⟨m'', hm'', rfl⟩ := List.mem_map.1 this
              exact absurd (h3 m'' hm'') (lt_irrefl _)
    · simp only [Function.update_of_ne hj]
      exact h.know j x
  · by_cases hj : j = c
    · subst hj
      simp only [Function.update_self]
      have hnd : (y :: rest.map P.oidOf).Nodup := by
        rw [hfil]; exact h.rf.sv_nodup.filter _
      have : cfg.sv.filter (fun x => decide (x.1 ≠ j ∧ x ∉ insert y (cfg.know j))) =
          (cfg.sv.filter (fun x => decide (x.1 ≠ j ∧ x ∉ cfg.know j))).filter
            (fun x => decide (x ≠ y)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro x _
        by_cases h1 : x.1 = j <;> by_cases h2 : x ∈ cfg.know j <;> by_cases h3 : x = y <;>
          simp [h1, h2, h3]
      rw [this, ← hfil, List.filter_cons_of_neg (by simp [hy]), List.filter_eq_self.2]
      intro x hx
      simp only [decide_eq_true_eq]
      rintro rfl
      exact (List.nodup_cons.1 hnd).1 hx
    · simp only [Function.update_of_ne hj]
      exact h.down j
  · have := h.ctx_know r hr
    by_cases hc : r.oid.1 = c
    · simp only [hc, Function.update_self]
      rw [hc] at this
      exact this.trans (Finset.subset_insert _ _)
    · simp only [Function.update_of_ne hc]; exact this

/-- The generic invariant holds along every execution (for every compatible schedule), given a
protocol invariant `PI` that keeps the clients' lists equal to the lists of their vertices. -/
theorem reach {PI : Sched (Oid n) → Cfg P → Prop}
    (hlist : ∀ S (cfg : Cfg P), GI S cfg → PI S cfg → ∀ c, P.list (cfg.cs c) = S.L (cfg.know c))
    (h0 : ∀ S, Compat S (Cfg.init P) → PI S (Cfg.init P))
    (hstep : ∀ S (cfg cfg' : Cfg P) e, GI S cfg → PI S cfg → GI S cfg' →
      cfg.step genOp e = some cfg' → PI S cfg')
    {es : List (Ev n)} {cfg : Cfg P} (hr : run genOp P es = some cfg) :
    ∀ S, Compat S cfg → GI S cfg ∧ PI S cfg := by
  refine run_induction (Q := fun cfg => ∀ S, Compat S cfg → GI S cfg ∧ PI S cfg)
    (fun S hS => ⟨GI.init hS, h0 S hS⟩) ?_ hr
  intro cfg cfg' e ih hs S hS
  obtain ⟨hG, hP⟩ := ih S (hS.of_step hs)
  have hG' : GI S cfg' := by
    cases e with
    | «do» c u =>
      obtain rfl := step_do hs
      exact hG.do hS (hlist S cfg hG hP c)
    | srv c => exact hG.srv hS hs
    | recv c => exact hG.recv hS hs
  exact ⟨hG', hstep S cfg cfg' e hG hP hG' hs⟩

end Cfg

end Podc.JupiterListSpec
