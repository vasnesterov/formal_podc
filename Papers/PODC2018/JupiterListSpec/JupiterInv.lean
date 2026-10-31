import Papers.PODC2018.JupiterListSpec.JupiterLoop

/-!
# The invariant of Jupiter: its state spaces are parts of the global state space

Every edge of every 2D state space of Jupiter is labelled by `T x V` (`EOK`), the client and server
states are the lists of their vertices, and the edges that the next `xForm` will follow exist:

* at client `c`, for every own operation `q` that is `≺s`-after everything `c` received, the LOCAL
  edge labelled `q` from the vertex "received operations + own operations before `q`" (`C4`);
* at the server, in the state space for `c`, for every other client's operation `l` not yet known
  to `c` when it generated its next operation, the GLOBAL edge labelled `l` from the vertex
  "`c`'s processed operations + operations `≺s`-before `l`" (`S4`).

This is Propositions 14 and 16 of the paper (Jupiter's state spaces are parts of CJupiter's
global one) in invariant form.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

namespace Jup

open Cfg

variable {S : Sched (Oid n)}

/-- An edge of a state space owned by `c` is labelled by the global transformation, and records
what the next lookups need: LOCAL edges are causally after their context, GLOBAL edges are
`≺s`-after their whole context. -/
structure EOK (S : Sched (Oid n)) (c : Fin n) (D : Finset (Oid n)) (e : JOp n) : Prop where
  o : e.o = S.T e.oid e.ctx
  notMem : e.oid ∉ e.ctx
  sub : insert e.oid e.ctx ⊆ D
  loc : e.oid.1 = c → S.ctx e.oid ⊆ e.ctx
  glob : e.oid.1 ≠ c → ∀ y, S.rank y < S.rank e.oid → y ∈ e.ctx

theorem EOK.mono {c : Fin n} {D D' : Finset (Oid n)} {e : JOp n} (h : EOK S c D e)
    (hD : D ⊆ D') : EOK S c D' e :=
  ⟨h.o, h.notMem, h.sub.trans hD, h.loc, h.glob⟩

theorem EOK.eq_tE {c : Fin n} {D : Finset (Oid n)} {e : JOp n} (h : EOK S c D e) :
    e = tE S e.oid e.ctx := by
  cases e; simp only [tE, JOp.mk.injEq, and_true]; exact h.o

/-- `edgeFrom` returns the unique matching edge. -/
theorem edgeFrom_eq {c : Fin n} {E : List (JOp n)} {u : Finset (Oid n)} {d : Bool} {e0 : JOp n}
    (he0 : e0 ∈ E) (hctx : e0.ctx = u) (hd : decide (e0.oid.1 = c) = d)
    (huniq : ∀ e ∈ E, e.ctx = u → decide (e.oid.1 = c) = d → e = e0) :
    edgeFrom c E u d = some e0 := by
  unfold edgeFrom
  cases hf : E.find? (fun e => decide (e.ctx = u) && (decide (e.oid.1 = c) == d)) with
  | none =>
    rw [List.find?_eq_none] at hf
    have := hf e0 he0
    simp [hctx, hd] at this
  | some e =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    rw [huniq e hm hp.1 hp.2]

/-- Uniqueness of LOCAL edges. -/
theorem uniq_loc {D : Set (Oid n)} (hW : S.WF D) (hcl : ∀ x, S.cl x = x.1.val) {c : Fin n}
    {Dl : Finset (Oid n)} (hDl : ↑Dl ⊆ D) {e : JOp n} (he : EOK S c Dl e) (hec : e.oid.1 = c)
    {q : Oid n} (hqD : q ∈ D) (hqc : q.1 = c) (hqu : q ∉ e.ctx)
    (hbefore : ∀ y ∈ D, y.1 = c → S.rank y < S.rank q → y ∈ e.ctx) : e.oid = q := by
  have heD : e.oid ∈ D := hDl (he.sub (Finset.mem_insert_self _ _))
  have hc : S.cl e.oid = S.cl q := by rw [hcl, hcl, hec, hqc]
  rcases lt_trichotomy (S.rank q) (S.rank e.oid) with h | h | h
  · exact absurd (he.loc hec (hW.own _ heD q hqD hc.symm h)) hqu
  · exact hW.inj heD hqD h.symm
  · exact absurd (hbefore _ heD hec h) he.notMem

/-- Uniqueness of GLOBAL edges. -/
theorem uniq_glob {D : Set (Oid n)} (hW : S.WF D) {c : Fin n}
    {Dl : Finset (Oid n)} (hDl : ↑Dl ⊆ D) {e : JOp n} (he : EOK S c Dl e) (hec : e.oid.1 ≠ c)
    {l : Oid n} (hlD : l ∈ D) (hlu : l ∉ e.ctx)
    (hbefore : ∀ y ∈ D, y.1 ≠ c → S.rank y < S.rank l → y ∈ e.ctx) : e.oid = l := by
  have heD : e.oid ∈ D := hDl (he.sub (Finset.mem_insert_self _ _))
  rcases lt_trichotomy (S.rank l) (S.rank e.oid) with h | h | h
  · exact absurd (he.glob hec l h) hlu
  · exact hW.inj heD hlD h.symm
  · exact absurd (hbefore _ heD hec h) he.notMem

theorem mem_pre_iff {α : Type} {r : α → ℕ} {l pre rest : List α} {x : α}
    (hs : l.Pairwise fun a b => r a < r b) (hl : l = pre ++ x :: rest) (y : α) :
    y ∈ pre ↔ y ∈ l ∧ r y < r x := by
  subst hl
  rw [List.pairwise_append] at hs
  constructor
  · intro hy; exact ⟨by simp [hy], hs.2.2 y hy x (by simp)⟩
  · rintro ⟨hy, hr⟩
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hy
    · omega
    · have := (List.pairwise_cons.1 hs.2.1).1 y hy; omega

/-- The operations of one client appear in the log in `≺s` order. -/
theorem GI.rank_lt_of_idx {P : Proto n} {cfg : Cfg P} (h : GI S cfg) {i j : ℕ} {ri rj : Rec n}
    (hi : cfg.log[i]? = some ri) (hj : cfg.log[j]? = some rj) (hij : i < j)
    (hc : ri.oid.1 = rj.oid.1) : S.rank ri.oid < S.rank rj.oid := by
  have hri := List.mem_of_getElem? hi
  have hrj := List.mem_of_getElem? hj
  have hxi := h.mem_log_D hri
  have hxj := h.mem_log_D hrj
  have hcl : S.cl ri.oid = S.cl rj.oid := by rw [h.compat.cl, h.compat.cl, hc]
  rcases lt_trichotomy (S.rank ri.oid) (S.rank rj.oid) with hr | hr | hr
  · exact hr
  · have := h.idx_eq hi hj (h.wf.inj hxi hxj hr); omega
  · exfalso
    have hin := h.wf.own _ hxi _ hxj hcl.symm hr
    rw [h.compat.ctx _ hri] at hin
    obtain ⟨j', hj', r', hr', he⟩ := h.ctx_log i _ hi _ hin
    have := h.idx_eq hr' hj he
    omega

theorem GI.own_sorted {P : Proto n} {cfg : Cfg P} (h : GI S cfg) (c : Fin n) :
    ((cfg.log.map Rec.oid).filter fun y => decide (y.1 = c)).Pairwise
      fun a b => S.rank a < S.rank b := by
  refine List.pairwise_of_forall_sublist fun {a b} hab => ?_
  have hab' := hab.trans List.filter_sublist
  have ha := hab.subset (by simp : a ∈ [a, b])
  have hb := hab.subset (by simp : b ∈ [a, b])
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  have hlt := List.idxOf_lt_of_pair_sublist h.rf.lognd hab'
  have hget : ∀ y ∈ cfg.log.map Rec.oid, ∃ r : Rec n,
      cfg.log[(cfg.log.map Rec.oid).idxOf y]? = some r ∧ r.oid = y := by
    intro y hy
    have hlen := List.idxOf_lt_length_of_mem hy
    have hy' := List.getElem_idxOf hlen
    rw [List.getElem_map] at hy'
    simp only [List.length_map] at hlen
    exact ⟨cfg.log[(cfg.log.map Rec.oid).idxOf y], List.getElem?_eq_getElem hlen, hy'⟩
  obtain ⟨ra, hra, rfl⟩ := hget a ha.1
  obtain ⟨rb, hrb, rfl⟩ := hget b hb.1
  exact GI.rank_lt_of_idx h hra hrb hlt (ha.2.trans hb.2.symm)

/-- The set `R` of operations known to `c` when it generated its next operation (the head of its
up channel), or now if there is none. -/
def R (cfg : Cfg (jupiter n)) (c : Fin n) : Finset (Oid n) :=
  match cfg.up c with
  | [] => cfg.know c
  | m :: _ => m.ctx

/-- The invariant of Jupiter. -/
structure JPI (S : Sched (Oid n)) (cfg : Cfg (jupiter n)) : Prop where
  ccur : ∀ c, (cfg.cs c).dss.cur = cfg.know c
  clist : ∀ c, (cfg.cs c).list = S.L (cfg.know c)
  cedge : ∀ c, ∀ e ∈ (cfg.cs c).dss.edges, EOK S c cfg.D e
  cpath : ∀ c q, q ∈ cfg.D → q.1 = c → (∀ y ∈ cfg.know c, y.1 ≠ c → S.rank y < S.rank q) →
    tE S q ((cfg.know c).filter fun y => y.1 ≠ c ∨ S.rank y < S.rank q) ∈ (cfg.cs c).dss.edges
  down : ∀ c, ∀ m ∈ cfg.down c, m = tE S m.oid m.ctx ∧ ∀ y, y ∈ m.ctx ↔ S.rank y < S.rank m.oid
  up : ∀ c, ∀ m ∈ cfg.up c, m = ⟨S.orig m.oid, m.oid, S.ctx m.oid⟩
  scur : ∀ c, (cfg.ss.dss c).cur = cfg.sv.toFinset
  slist : cfg.ss.list = S.L cfg.sv.toFinset
  sedge : ∀ c, ∀ e ∈ (cfg.ss.dss c).edges, EOK S c cfg.D e
  spath : ∀ c l, l ∈ cfg.sv → l.1 ≠ c → l ∉ R cfg c →
    tE S l (cfg.sv.toFinset.filter fun y => y.1 = c ∨ S.rank y < S.rank l) ∈ (cfg.ss.dss c).edges

theorem JPI.init (S : Sched (Oid n)) : JPI S (Cfg.init (jupiter n)) := by
  refine ⟨fun c => rfl, fun c => ?_, fun c => by simp [Cfg.init, jupiter],
    fun c q hq => by simp [Cfg.init, D] at hq, fun c => by simp [Cfg.init],
    fun c => by simp [Cfg.init], fun c => rfl, ?_, fun c => by simp [Cfg.init, jupiter],
    fun c l hl => by simp [Cfg.init] at hl⟩
  · simp [Cfg.init, jupiter, S.L_empty]
  · simp [Cfg.init, jupiter, S.L_empty]

variable {cfg : Cfg (jupiter n)}

theorem JPI.do (h : GI S cfg) (hj : JPI S cfg) {c : Fin n} {u : UOp}
    (h' : GI S (doCfg genOp cfg c u)) : JPI S (doCfg genOp cfg c u) := by
  set x : Oid n := (c, cfg.seq c) with hx
  set K := cfg.know c with hK
  have hlist : (jupiter n).list (cfg.cs c) = S.L K := hj.clist c
  set og := genOp x u (S.L K) with hog
  have hxD : x ∉ cfg.D := h.rf.fresh_notMem c
  have hD' : (doCfg genOp cfg c u).D = insert x cfg.D := doCfg_D cfg c u
  have hxD' : x ∈ (doCfg genOp cfg c u).D := by rw [hD']; exact Finset.mem_insert_self _ _
  have hrec : (⟨x, og.1, K, og.2, og.1.apply (S.L K)⟩ : Rec n) ∈ (doCfg genOp cfg c u).log := by
    simp only [doCfg, List.mem_append, List.mem_singleton]
    right; simp only [x, K, og]; rw [show (cfg.cs c).list = S.L (cfg.know c) from hlist]
  have horig : S.orig x = og.1 := h'.compat.orig _ hrec
  have hctx : S.ctx x = K := h'.compat.ctx _ hrec
  have hlt : ∀ y ∈ K, S.rank y < S.rank x := fun y hy =>
    h'.wf.ctx_lt x hxD' y (hctx ▸ hy)
  have hxK : x ∉ K := fun hxK => hxD (h.know_D hxK)
  have hknow' : (doCfg genOp cfg c u).know c = insert x K := by simp [doCfg, K, x]
  have hT : S.T x K = og.1 := by rw [S.T_of_subset (by rw [hctx]), horig]
  have hsubD : cfg.D ⊆ (doCfg genOp cfg c u).D := by rw [hD']; exact Finset.subset_insert _ _
  have hcs : (doCfg genOp cfg c u).cs c =
      ⟨og.1.apply (cfg.cs c).list, ⟨⟨og.1, x, K⟩ :: (cfg.cs c).dss.edges, insert x K⟩⟩ := by
    simp only [doCfg, Function.update_self, jupiter, hj.ccur c, x, K, og]
    rw [show (cfg.cs c).list = S.L (cfg.know c) from hlist]
  have hcsne : ∀ c', c' ≠ c → (doCfg genOp cfg c u).cs c' = cfg.cs c' := by
    intro c' hc'; simp [doCfg, Function.update_of_ne hc']
  have hknowne : ∀ c', c' ≠ c → (doCfg genOp cfg c u).know c' = cfg.know c' := by
    intro c' hc'; simp [doCfg, Function.update_of_ne hc']
  refine ⟨fun c' => ?_, fun c' => ?_, fun c' e he => ?_, fun c' q hq hqc hall => ?_,
    fun c' => hj.down c', fun c' m hm => ?_, hj.scur, hj.slist,
    fun c' e he => (hj.sedge c' e he).mono hsubD, fun c' l hl hlc hlR => ?_⟩
  · by_cases hc : c' = c
    · subst hc; rw [hcs, hknow']
    · rw [hcsne c' hc, hknowne c' hc]; exact hj.ccur c'
  · by_cases hc : c' = c
    · subst hc
      rw [hcs, hknow']
      simp only
      rw [hj.clist c']
      obtain ⟨hL, -⟩ := S.edge h'.wf hxK (h.vert_know c') (hknow' ▸ h'.vert_know c')
        (by rw [← hknow']; exact h'.know_sub c')
      rw [hL, hT]
    · rw [hcsne c' hc, hknowne c' hc]; exact hj.clist c'
  · by_cases hc : c' = c
    · subst hc
      rw [hcs] at he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · refine ⟨hT.symm, hxK, ?_, fun _ => by rw [hctx], fun h => absurd rfl h⟩
        rw [hD']; exact Finset.insert_subset_insert _ (h.know_sub c')
      · exact (hj.cedge c' e he).mono hsubD
    · rw [hcsne c' hc] at he; exact (hj.cedge c' e he).mono hsubD
  · by_cases hc : c' = c
    · subst hc
      rw [hcs]
      by_cases hqx : q = x
      · subst hqx
        have : (insert x K).filter (fun y => y.1 ≠ x.1 ∨ S.rank y < S.rank x) = K := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, h2⟩
            · rcases h2 with h2 | h2
              · exact absurd rfl h2
              · exact absurd h2 (lt_irrefl _)
            · exact hy
          · intro hy; exact ⟨Or.inr hy, Or.inr (hlt y hy)⟩
        rw [hknow', this, ← hT]
        exact List.mem_cons_self
      · have hqD : q ∈ cfg.D := by rw [hD'] at hq; exact (Finset.mem_insert.1 hq).resolve_left hqx
        have hqx' : S.rank q < S.rank x := hlt q ((h.know c' q).2 (Or.inl ⟨hqD, hqc⟩))
        have : (insert x K).filter (fun y => y.1 ≠ c' ∨ S.rank y < S.rank q) =
            K.filter (fun y => y.1 ≠ c' ∨ S.rank y < S.rank q) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, h2⟩
            · rcases h2 with h2 | h2
              · exact absurd rfl h2
              · omega
            · exact ⟨hy, h2⟩
          · rintro ⟨hy, h2⟩; exact ⟨Or.inr hy, h2⟩
        rw [hknow', this]
        refine List.mem_cons_of_mem _ (hj.cpath c' q hqD hqc fun y hy hyc => hall y ?_ hyc)
        rw [hknow']; exact Finset.mem_insert_of_mem hy
    · rw [hcsne c' hc]
      have hqD : q ∈ cfg.D := by
        rw [hD'] at hq
        exact (Finset.mem_insert.1 hq).resolve_left fun e => hc (hqc ▸ e ▸ rfl)
      rw [hknowne c' hc] at hall ⊢
      exact hj.cpath c' q hqD hqc hall
  · by_cases hc : c' = c
    · subst hc
      simp only [doCfg, Function.update_self, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hj.up c' m hm
      · have e1 : S.orig (c', cfg.seq c') = (genOp (c', cfg.seq c') u (S.L (cfg.know c'))).1 :=
          horig
        have e2 : S.ctx (c', cfg.seq c') = cfg.know c' := hctx
        simp only [jupiter, hj.clist c', hj.ccur c', e1, e2]
    · simp only [doCfg, Function.update_of_ne hc] at hm; exact hj.up c' m hm
  · have hR : R (doCfg genOp cfg c u) c' = R cfg c' := by
      by_cases hc : c' = c
      · subst hc
        simp only [R, doCfg, Function.update_self]
        cases hu : cfg.up c' with
        | nil => simp only [jupiter, hj.ccur c']; rfl
        | cons m0 rest => simp
      · simp [R, doCfg, Function.update_of_ne hc]
    rw [hR] at hlR
    exact hj.spath c' l hl hlc hlR

/-- The own operations of `c` that are `≺s`-after `j`, in `≺s` order. -/
def cpathOf (S : Sched (Oid n)) (cfg : Cfg (jupiter n)) (c : Fin n) (j : Oid n) : List (Oid n) :=
  (cfg.log.map Rec.oid).filter fun y => decide (y.1 = c ∧ S.rank j < S.rank y)

theorem mem_cpathOf {c : Fin n} {j y : Oid n} :
    y ∈ cpathOf S cfg c j ↔ y ∈ cfg.D ∧ y.1 = c ∧ S.rank j < S.rank y := by
  simp [cpathOf, D]

theorem cpathOf_sorted (h : GI S cfg) (c : Fin n) (j : Oid n) :
    (cpathOf S cfg c j).Pairwise fun a b => S.rank a < S.rank b := by
  refine (GI.own_sorted h c).sublist ?_
  apply List.monotone_filter_right
  intro y hy; simp only [decide_eq_true_eq] at hy ⊢; exact hy.1

/-- Remote processing at a client succeeds and computes the global transformation. -/
theorem recv_ok (h : GI S cfg) (hj : JPI S cfg) {c : Fin n} {m : JOp n} {rest : List (JOp n)}
    (hdown : cfg.down c = m :: rest) :
    ∃ Ef, xForm c true (cfg.cs c).dss m =
        some (⟨Ef, insert m.oid (cfg.know c)⟩, tE S m.oid (cfg.know c)) ∧
      (∀ e ∈ Ef, EOK S c cfg.D e ∧ (e ∈ (cfg.cs c).dss.edges ∨ e = m ∨
        e ∈ New S m.oid (cpathOf S cfg c m.oid) m.ctx)) ∧
      ∀ q, q ∈ cpathOf S cfg c m.oid →
        tE S q (insert m.oid ((cfg.know c).filter fun y => y.1 ≠ c ∨ S.rank y < S.rank q)) ∈ Ef
  := by
  have hm : m ∈ cfg.down c := by rw [hdown]; exact List.mem_cons_self
  obtain ⟨hmT, hmctx⟩ := hj.down c m hm
  obtain ⟨hjsv, hjc, hjK⟩ : m.oid ∈ cfg.sv ∧ m.oid.1 ≠ c ∧ m.oid ∉ cfg.know c := h.down_sv hm
  set j := m.oid with hjdef
  set uj := m.ctx with hujdef
  set K := cfg.know c with hK
  set path := cpathOf S cfg c j with hpath
  have hjD : j ∈ cfg.D := h.sv_D hjsv
  have hsorted := cpathOf_sorted h c j
  have hDsub : ↑cfg.D ⊆ (↑cfg.D : Set (Oid n)) := le_rfl
  -- ranks of the down channel
  have hrank_down : ∀ m' ∈ cfg.down c, S.rank j ≤ S.rank m'.oid := by
    intro m' hm'
    rw [hdown] at hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact le_rfl
    · have hsrt : ((cfg.down c).map fun m : JOp n => S.rank m.oid).Pairwise (· < ·) :=
        h.down_sorted c
      rw [hdown, List.map_cons, List.pairwise_cons] at hsrt
      exact (hsrt.1 _ (List.mem_map_of_mem (f := fun m : JOp n => S.rank m.oid) hm')).le
  have hothers : ∀ y ∈ K, y.1 ≠ c → S.rank y < S.rank j := by
    intro y hy hyc
    rcases (h.know c y).1 hy with ⟨-, h2⟩ | ⟨-, -, h3⟩
    · exact absurd h2 hyc
    · exact h3 m hm
  have hujK : ∀ y ∈ uj, y ∈ K := by
    intro y hy
    have hlt := (hmctx y).1 hy
    have hysv := h.compat.sv_of_rank y (lt_trans hlt (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjsv))
    by_cases hyc : y.1 = c
    · exact (h.know c y).2 (Or.inl ⟨h.sv_D hysv, hyc⟩)
    · exact (h.know c y).2 (Or.inr ⟨hysv, hyc, fun m' hm' => lt_of_lt_of_le hlt (hrank_down m' hm')⟩)
  have hrank_ne : ∀ y ∈ cfg.D, y ≠ j → S.rank y ≠ S.rank j := fun y hy hne e =>
    hne (h.wf.inj hy hjD e)
  have hpathK : ∀ y ∈ path, y ∈ K := by
    intro y hy
    obtain ⟨hyD, hyc, -⟩ := mem_cpathOf.1 hy
    exact (h.know c y).2 (Or.inl ⟨hyD, hyc⟩)
  have hKsplit : ∀ y ∈ K, y ∈ uj ∨ y ∈ path := by
    intro y hy
    by_cases hyc : y.1 = c
    · have hyD := h.know_D hy
      rcases lt_or_gt_of_ne (hrank_ne y hyD (fun e => hjK (e ▸ hy))) with hlt | hlt
      · exact Or.inl ((hmctx y).2 hlt)
      · exact Or.inr (mem_cpathOf.2 ⟨hyD, hyc, hlt⟩)
    · exact Or.inl ((hmctx y).2 (hothers y hy hyc))
  have hcur : uj ∪ path.toFinset = K := by
    ext y
    simp only [Finset.mem_union, List.mem_toFinset]
    constructor
    · rintro (hy | hy)
      · exact hujK y hy
      · exact hpathK y hy
    · exact hKsplit y
  have hdisj : ∀ l ∈ path, l ∉ uj := by
    intro l hl hlu
    have := (hmctx l).1 hlu
    have := (mem_cpathOf.1 hl).2.2
    omega
  have hnd : path.Nodup := h.rf.lognd.filter _
  have hlen : path.length ≤ K.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card (fun y hy => hpathK y (List.mem_toFinset.1 hy))
  -- membership in a prefix of the path
  have hpre : ∀ pre l rest', path = pre ++ l :: rest' → ∀ y,
      y ∈ uj ∪ pre.toFinset ↔ y ∈ K ∧ (y.1 ≠ c ∨ S.rank y < S.rank l) := by
    intro pre l rest' hp y
    have hl : l ∈ path := by rw [hp]; simp
    obtain ⟨hlD, hlc, hjl⟩ := mem_cpathOf.1 hl
    rw [Finset.mem_union, List.mem_toFinset, mem_pre_iff hsorted hp]
    constructor
    · rintro (hy | ⟨hy, hyl⟩)
      · refine ⟨hujK y hy, ?_⟩
        by_cases hyc : y.1 = c
        · exact Or.inr (lt_trans ((hmctx y).1 hy) hjl)
        · exact Or.inl hyc
      · exact ⟨hpathK y hy, Or.inr hyl⟩
    · rintro ⟨hy, hyc | hyl⟩
      · exact Or.inl ((hmctx y).2 (hothers y hy hyc))
      · rcases hKsplit y hy with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨h1, hyl⟩
  -- the edges of `New` are EOK
  have hnewOK : ∀ e ∈ New S j path uj, EOK S c cfg.D e := by
    rintro e ⟨pre, l, rest', hp, he⟩
    have hl : l ∈ path := by rw [hp]; simp
    obtain ⟨hlD, hlc, hjl⟩ := mem_cpathOf.1 hl
    have hlU : l ∉ uj ∪ pre.toFinset := by
      intro hlU
      rw [hpre pre l rest' hp] at hlU
      rcases hlU.2 with h1 | h1
      · exact h1 hlc
      · exact lt_irrefl _ h1
    have hjU : j ∉ uj ∪ pre.toFinset := by
      intro hjU
      rw [hpre pre l rest' hp] at hjU
      exact hjK hjU.1
    have hUD : uj ∪ pre.toFinset ⊆ cfg.D := by
      intro y hy
      rw [hpre pre l rest' hp] at hy
      exact h.know_D hy.1
    rcases he with rfl | rfl
    · refine ⟨rfl, ?_, ?_, fun h1 => absurd h1 hjc, fun _ y hy => ?_⟩
      · simp only [tE, Finset.mem_insert, not_or]
        exact ⟨fun e => hjc (e ▸ hlc), hjU⟩
      · simp only [tE]
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | rfl | hy
        · exact hjD
        · exact hlD
        · exact hUD hy
      · simp only [tE]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hmctx y).2 hy))
    · refine ⟨rfl, ?_, ?_, fun _ => ?_, fun h1 => absurd hlc h1⟩
      · simp only [tE, Finset.mem_insert, not_or]
        exact ⟨fun e => hjc (e ▸ hlc), hlU⟩
      · simp only [tE]
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | rfl | hy
        · exact hlD
        · exact hjD
        · exact hUD hy
      · simp only [tE]
        intro y hy
        have hyl := h.wf.ctx_lt l hlD y hy
        obtain ⟨r, hr, hro⟩ := mem_D.1 hlD
        have hyK : y ∈ K := by
          have := h.ctx_know r hr
          rw [hro, hlc, ← h.compat.ctx r hr, hro] at this
          exact this hy
        by_cases hyj : y = j
        · rw [hyj]; exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ((hpre pre l rest' hp y).2 ⟨hyK, Or.inr hyl⟩)
  have hmOK : EOK S c cfg.D m := by
    refine ⟨by rw [hmT]; rfl, fun hj' => lt_irrefl _ ((hmctx j).1 hj'), ?_,
      fun h1 => absurd h1 hjc, fun _ y hy => (hmctx y).2 hy⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hjD
    · exact h.know_D (hujK y hy)
  have hUeq : ∀ pre l rest', path = pre ++ l :: rest' →
      uj ∪ pre.toFinset = K.filter fun y => y.1 ≠ c ∨ S.rank y < S.rank l := by
    intro pre l rest' hp
    ext y; rw [hpre pre l rest' hp y, Finset.mem_filter]
  have hctxl : ∀ l ∈ path, S.ctx l ⊆ K := by
    intro l hl
    obtain ⟨hlD, hlc, -⟩ := mem_cpathOf.1 hl
    obtain ⟨r, hr, hro⟩ := mem_D.1 hlD
    have := h.ctx_know r hr
    rw [hro, hlc, ← h.compat.ctx r hr, hro] at this
    exact this
  obtain ⟨Ef, hloop, -, hback, hall⟩ := xLoop_spec S (c := c) (d := true) (cur := K) (x := j)
    path uj (m :: (cfg.cs c).dss.edges) K.card hlen hcur hdisj hnd (by
      intro pre l rest' hp
      have hl : l ∈ path := by rw [hp]; simp
      obtain ⟨hlD, hlc, hjl⟩ := mem_cpathOf.1 hl
      have hlU : l ∉ uj ∪ pre.toFinset := by
        intro hlU
        rw [hpre pre l rest' hp] at hlU
        rcases hlU.2 with h1 | h1
        · exact h1 hlc
        · exact lt_irrefl _ h1
      have hjU : j ∉ uj ∪ pre.toFinset := by
        intro hjU
        rw [hpre pre l rest' hp] at hjU
        exact hjK hjU.1
      refine ⟨(S.T_insert hlU (fun hl' => by have := h.wf.ctx_lt j hjD l hl'; omega) ?_).symm,
        (S.T_insert hjU (fun hj' => hjK (hctxl l hl hj')) ?_).symm, ?_⟩
      · intro y hy _
        rw [hpre pre l rest' hp] at hy
        rcases hy.2 with h1 | h1
        · exact lt_trans (hothers y hy.1 h1) hjl
        · exact h1
      · intro y hy hyl
        rw [hpre pre l rest' hp] at hy
        rcases hy.2 with h1 | h1
        · exact hothers y hy.1 h1
        · by_cases hyc : y.1 = c
          · exact absurd (h.wf.own l hlD y (h.know_D hy.1)
              (by rw [h.compat.cl, h.compat.cl, hyc, hlc]) h1) hyl
          · exact hothers y hy.1 hyc
      · intro E' hE hE'
        have he0 : tE S l (uj ∪ pre.toFinset) ∈ E' := by
          apply hE
          refine List.mem_cons_of_mem _ ?_
          rw [hUeq pre l rest' hp]
          exact hj.cpath c l hlD hlc fun y hy hyc => lt_trans (hothers y hy hyc) hjl
        refine edgeFrom_eq he0 rfl (by simp [tE, hlc]) fun e he hctx hd => ?_
        have heOK : EOK S c cfg.D e := by
          rcases hE' e he with he | he
          · rcases List.mem_cons.1 he with rfl | he
            · exact hmOK
            · exact hj.cedge c e he
          · exact hnewOK e he
        have hec : e.oid.1 = c := by simpa using hd
        have := uniq_loc h.wf h.compat.cl le_rfl heOK hec hlD hlc (hctx ▸ hlU)
          (fun y hy hyc hyl => hctx ▸ (hpre pre l rest' hp y).2
            ⟨(h.know c y).2 (Or.inl ⟨hy, hyc⟩), Or.inr hyl⟩)
        rw [heOK.eq_tE, this, hctx])
  rw [← hmT] at hloop
  refine ⟨Ef, ?_, fun e he => ?_, fun q hq => ?_⟩
  · simp only [xForm, hj.ccur c, ← hK, hloop, ← hjdef]
  · rcases hback e he with he | he
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hmOK, Or.inr (Or.inl rfl)⟩
      · exact ⟨hj.cedge c e he, Or.inl he⟩
    · exact ⟨hnewOK e he, Or.inr (Or.inr he)⟩
  · obtain ⟨pre, rest', hp⟩ := List.append_of_mem hq
    rw [← hUeq pre q rest' hp]
    exact hall _ ⟨pre, q, rest', hp, Or.inr rfl⟩

theorem JPI.recv (h : GI S cfg) (hj : JPI S cfg) {c : Fin n} {cfg' : Cfg (jupiter n)}
    (hs : cfg.step genOp (.recv c) = some cfg') (h' : GI S cfg') : JPI S cfg' := by
  obtain ⟨m, rest, s', hdown, hcr, rfl⟩ := step_recv hs
  obtain ⟨Ef, hx, hEf, hq⟩ := recv_ok h hj hdown
  have hm : m ∈ cfg.down c := by rw [hdown]; exact List.mem_cons_self
  obtain ⟨hjsv, hjc, hjK⟩ : m.oid ∈ cfg.sv ∧ m.oid.1 ≠ c ∧ m.oid ∉ cfg.know c := h.down_sv hm
  have hs' : s' = ⟨(S.T m.oid (cfg.know c)).apply (cfg.cs c).list,
      ⟨Ef, insert m.oid (cfg.know c)⟩⟩ := by
    simp only [jupiter, hx, Option.some.injEq] at hcr
    rw [← hcr]; rfl
  subst hs'
  set j := m.oid with hjdef
  have hknow' : ∀ c', (Function.update cfg.know c (insert m.oid (cfg.know c))) c' =
      if c' = c then insert j (cfg.know c) else cfg.know c' := by
    intro c'; by_cases hc : c' = c
    · subst hc; simp [j]
    · simp [Function.update_of_ne hc, hc]
  refine ⟨fun c' => ?_, fun c' => ?_, fun c' e he => ?_, fun c' q hq' hqc hall => ?_,
    fun c' m' hm' => ?_, hj.up, hj.scur, hj.slist, hj.sedge, fun c' l hl hlc hlR => ?_⟩
  · simp only [hknow']
    by_cases hc : c' = c
    · subst hc; simp
    · simp [Function.update_of_ne hc, hc, hj.ccur c']
  · simp only [hknow']
    by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self, if_true]
      rw [hj.clist c']
      have hV' := h'.vert_know c'
      have hsub' := h'.know_sub c'
      simp only [hknow', if_true] at hV' hsub'
      exact (S.edge h.wf hjK (h.vert_know c') hV' hsub').1.symm
    · simp [Function.update_of_ne hc, hc, hj.clist c']
  · by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self] at he
      exact (hEf e he).1
    · simp only [Function.update_of_ne hc] at he
      exact hj.cedge c' e he
  · simp only [hknow'] at hall ⊢
    by_cases hc : c' = c
    · subst hc
      simp only [if_true] at hall ⊢
      simp only [Function.update_self]
      have hjq : S.rank j < S.rank q := hall j (Finset.mem_insert_self _ _) hjc
      have hfil : (insert j (cfg.know c')).filter (fun y => y.1 ≠ c' ∨ S.rank y < S.rank q) =
          insert j ((cfg.know c').filter fun y => y.1 ≠ c' ∨ S.rank y < S.rank q) := by
        rw [Finset.filter_insert, if_pos (Or.inl hjc)]
      rw [hfil]
      exact hq q (mem_cpathOf.2 ⟨hq', hqc, hjq⟩)
    · simp only [hc, if_false] at hall ⊢
      simp only [Function.update_of_ne hc]
      exact hj.cpath c' q hq' hqc hall
  · by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self] at hm'
      exact hj.down c' m' (by rw [hdown]; exact List.mem_cons_of_mem _ hm')
    · simp only [Function.update_of_ne hc] at hm'
      exact hj.down c' m' hm'
  · apply hj.spath c' l hl hlc
    intro hlR'
    apply hlR
    simp only [R] at hlR' ⊢
    by_cases hc : c' = c
    · subst hc
      cases hu : cfg.up c' with
      | nil =>
        rw [hu] at hlR'
        simp only [Function.update_self]
        exact Finset.mem_insert_of_mem hlR'
      | cons m0 rest0 =>
        rw [hu] at hlR'
        exact hlR'
    · simp only [Function.update_of_ne hc]
      exact hlR'

theorem GI.sv_sorted {P : Proto n} {cfg : Cfg P} (h : GI S cfg) :
    cfg.sv.Pairwise fun a b => S.rank a < S.rank b := by
  refine List.pairwise_of_forall_sublist fun {a b} hab => ?_
  rw [h.compat.rank_of_mem_sv h.rf.sv_nodup (hab.subset (by simp)),
    h.compat.rank_of_mem_sv h.rf.sv_nodup (hab.subset (by simp))]
  exact List.idxOf_lt_of_pair_sublist h.rf.sv_nodup hab

/-- The other clients' operations processed by the server and unknown to `q`, in `≺s` order. -/
def spathOf (S : Sched (Oid n)) (cfg : Cfg (jupiter n)) (c : Fin n) (q : Oid n) : List (Oid n) :=
  cfg.sv.filter fun y => decide (y.1 ≠ c ∧ y ∉ S.ctx q)

/-- Server processing succeeds and computes the global transformation. -/
theorem srv_ok (h : GI S cfg) (hj : JPI S cfg) {c : Fin n} {m : JOp n} {rest : List (JOp n)}
    (hup : cfg.up c = m :: rest) :
    ∃ Ef, xForm c false (cfg.ss.dss c) m =
        some (⟨Ef, insert m.oid cfg.sv.toFinset⟩, tE S m.oid cfg.sv.toFinset) ∧
      (∀ e ∈ Ef, EOK S c cfg.D e) ∧
      ∀ l, l ∈ spathOf S cfg c m.oid →
        tE S l (insert m.oid (cfg.sv.toFinset.filter fun y => y.1 = c ∨ S.rank y < S.rank l)) ∈ Ef
  := by
  have hm : m ∈ cfg.up c := by rw [hup]; exact List.mem_cons_self
  have hmeq := hj.up c m hm
  set q := m.oid with hqdef
  set P := cfg.sv.toFinset with hP
  set path := spathOf S cfg c q with hpath
  -- basic facts about `q`
  have hfil := h.rf.up c
  rw [hup, List.map_cons] at hfil
  have hqmem : q ∈ (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
    rw [← hfil]; exact List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hqmem
  obtain ⟨hqlog, hqc, hqsv⟩ := hqmem
  have hqD : q ∈ cfg.D := by simpa [D] using hqlog
  have hqrank : cfg.sv.length ≤ S.rank q := h.compat.rank_up c m hm
  have hsvq : ∀ y ∈ cfg.sv, S.rank y < S.rank q := fun y hy =>
    lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hy) hqrank
  have hrest : ∀ m' ∈ rest, S.rank q < S.rank m'.oid := by
    have hs : ((cfg.up c).map fun m : JOp n => S.rank m.oid).Pairwise (· < ·) := h.compat.up_sorted c
    rw [hup, List.map_cons, List.pairwise_cons] at hs
    exact fun m' hm' => hs.1 _ (List.mem_map_of_mem (f := fun m : JOp n => S.rank m.oid) hm')
  -- `ctx q ⊆ sv` and the own operations of `sv` are in `ctx q`
  have hctxsv : ∀ y ∈ S.ctx q, y ∈ cfg.sv := by
    intro y hy
    have hyl := h.wf.ctx_lt q hqD y hy
    have hyD : y ∈ cfg.D := h.wf.ctx_sub q hqD hy
    by_contra hysv
    by_cases hyc : y.1 = c
    · have : y ∈ (cfg.up c).map (jupiter n).oidOf := by
        rw [h.rf.up c]; simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨by simpa [D] using hyD, hyc, hysv⟩
      rw [hup, List.map_cons, List.mem_cons] at this
      rcases this with rfl | this
      · exact lt_irrefl _ hyl
      · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 this
        exact absurd (lt_trans hyl (hrest m' hm')) (lt_irrefl _)
    · obtain ⟨r, hr, hro⟩ := mem_D.1 hqD
      have hk := h.ctx_know r hr
      rw [hro, hqc, ← h.compat.ctx r hr, hro] at hk
      rcases (h.know c y).1 (hk hy) with ⟨-, h2⟩ | ⟨h1, -, -⟩
      · exact hyc h2
      · exact hysv h1
  have hownsv : ∀ y ∈ cfg.sv, y.1 = c → y ∈ S.ctx q := by
    intro y hy hyc
    exact h.wf.own q hqD y (h.sv_D hy) (by rw [h.compat.cl, h.compat.cl, hyc, hqc]) (hsvq y hy)
  have hsorted : path.Pairwise fun a b => S.rank a < S.rank b :=
    (GI.sv_sorted h).sublist List.filter_sublist
  have mem_path : ∀ y, y ∈ path ↔ y ∈ cfg.sv ∧ y.1 ≠ c ∧ y ∉ S.ctx q := by
    intro y; simp [hpath, spathOf]
  have hcur : S.ctx q ∪ path.toFinset = P := by
    ext y
    simp only [Finset.mem_union, List.mem_toFinset, hP, mem_path]
    constructor
    · rintro (hy | hy)
      · exact hctxsv y hy
      · exact hy.1
    · intro hy
      by_cases hyq : y ∈ S.ctx q
      · exact Or.inl hyq
      · refine Or.inr ⟨hy, fun hyc => hyq (hownsv y hy hyc), hyq⟩
  have hdisj : ∀ l ∈ path, l ∉ S.ctx q := fun l hl => ((mem_path l).1 hl).2.2
  have hnd : path.Nodup := h.rf.sv_nodup.filter _
  have hlen : path.length ≤ P.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card (fun y hy => by
      rw [hP, List.mem_toFinset]; exact ((mem_path y).1 (List.mem_toFinset.1 hy)).1)
  have hpre : ∀ pre l rest', path = pre ++ l :: rest' → ∀ y,
      y ∈ S.ctx q ∪ pre.toFinset ↔ y ∈ cfg.sv ∧ (y.1 = c ∨ S.rank y < S.rank l) := by
    intro pre l rest' hp y
    have hl : l ∈ path := by rw [hp]; simp
    obtain ⟨hlsv, hlc, hlq⟩ := (mem_path l).1 hl
    rw [Finset.mem_union, List.mem_toFinset, mem_pre_iff hsorted hp]
    constructor
    · rintro (hy | ⟨hy, hyl⟩)
      · refine ⟨hctxsv y hy, ?_⟩
        by_cases hyc : y.1 = c
        · exact Or.inl hyc
        · right
          by_contra hle
          push_neg at hle
          have hcl : S.cl y ≠ S.cl q := by
            rw [h.compat.cl, h.compat.cl]
            intro e
            exact hyc ((Fin.ext e).trans hqc)
          exact hlq (h.wf.pref q hqD y hy hcl l hle)
      · exact ⟨((mem_path y).1 hy).1, Or.inr hyl⟩
    · rintro ⟨hy, hyc | hyl⟩
      · exact Or.inl (hownsv y hy hyc)
      · by_cases hyq : y ∈ S.ctx q
        · exact Or.inl hyq
        · by_cases hyc : y.1 = c
          · exact absurd (hownsv y hy hyc) hyq
          · exact Or.inr ⟨(mem_path y).2 ⟨hy, hyc, hyq⟩, hyl⟩
  have hUsv : ∀ pre l rest', path = pre ++ l :: rest' → ∀ y ∈ S.ctx q ∪ pre.toFinset,
      y ∈ cfg.sv := fun pre l rest' hp y hy => ((hpre pre l rest' hp y).1 hy).1
  have hlU : ∀ pre l rest', path = pre ++ l :: rest' → l ∉ S.ctx q ∪ pre.toFinset := by
    intro pre l rest' hp hlU
    have hl : l ∈ path := by rw [hp]; simp
    rcases ((hpre pre l rest' hp l).1 hlU).2 with h1 | h1
    · exact ((mem_path l).1 hl).2.1 h1
    · exact lt_irrefl _ h1
  have hqU : ∀ pre l rest', path = pre ++ l :: rest' → q ∉ S.ctx q ∪ pre.toFinset :=
    fun pre l rest' hp hq => hqsv (hUsv pre l rest' hp q hq)
  have hnewOK : ∀ e ∈ New S q path (S.ctx q), EOK S c cfg.D e := by
    rintro e ⟨pre, l, rest', hp, he⟩
    have hl : l ∈ path := by rw [hp]; simp
    obtain ⟨hlsv, hlc, -⟩ := (mem_path l).1 hl
    have hlD := h.sv_D hlsv
    have hUD : ∀ y ∈ S.ctx q ∪ pre.toFinset, y ∈ cfg.D := fun y hy =>
      h.sv_D (hUsv pre l rest' hp y hy)
    rcases he with rfl | rfl
    · refine ⟨rfl, ?_, ?_, fun _ => ?_, fun h1 => absurd hqc h1⟩
      · simp only [tE, Finset.mem_insert, not_or]
        exact ⟨fun e => hlc (e ▸ hqc), hqU pre l rest' hp⟩
      · simp only [tE]
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | rfl | hy
        · exact hqD
        · exact hlD
        · exact hUD y hy
      · simp only [tE]
        exact fun y hy => Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)
    · refine ⟨rfl, ?_, ?_, fun h1 => absurd h1 hlc, fun _ y hy => ?_⟩
      · simp only [tE, Finset.mem_insert, not_or]
        exact ⟨fun e => hlc (e ▸ hqc), hlU pre l rest' hp⟩
      · simp only [tE]
        intro y hy
        simp only [Finset.mem_insert] at hy
        rcases hy with rfl | rfl | hy
        · exact hlD
        · exact hqD
        · exact hUD y hy
      · simp only [tE]
        refine Finset.mem_insert_of_mem ((hpre pre l rest' hp y).2 ⟨?_, Or.inr hy⟩)
        exact h.compat.sv_of_rank y
          (lt_trans hy (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hlsv))
  have hTq : S.T q (S.ctx q) = S.orig q := S.T_of_subset le_rfl
  have hmOK : EOK S c cfg.D m := by
    rw [hmeq]
    refine ⟨hTq.symm, fun hq => lt_irrefl _ (h.wf.ctx_lt q hqD q hq), ?_, fun _ => le_rfl,
      fun h1 => absurd hqc h1⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hqD
    · exact h.wf.ctx_sub q hqD hy
  have hUeq : ∀ pre l rest', path = pre ++ l :: rest' →
      S.ctx q ∪ pre.toFinset = P.filter fun y => y.1 = c ∨ S.rank y < S.rank l := by
    intro pre l rest' hp
    ext y; rw [hpre pre l rest' hp y, Finset.mem_filter, hP, List.mem_toFinset]
  obtain ⟨Ef, hloop, -, hback, hall⟩ := xLoop_spec S (c := c) (d := false) (cur := P) (x := q)
    path (S.ctx q) (m :: (cfg.ss.dss c).edges) P.card hlen hcur hdisj hnd (by
      intro pre l rest' hp
      have hl : l ∈ path := by rw [hp]; simp
      obtain ⟨hlsv, hlc, hlq⟩ := (mem_path l).1 hl
      have hlD := h.sv_D hlsv
      refine ⟨(S.T_insert (hlU pre l rest' hp) hlq ?_).symm,
        (S.T_insert (hqU pre l rest' hp) (fun hq' => ?_) ?_).symm, ?_⟩
      · intro y hy hyq
        rcases ((hpre pre l rest' hp y).1 hy).2 with h1 | h1
        · exact absurd (hownsv y ((hpre pre l rest' hp y).1 hy).1 h1) hyq
        · exact h1
      · have := h.wf.ctx_lt l hlD q hq'
        have := hsvq l hlsv
        omega
      · intro y hy _
        exact hsvq y (hUsv pre l rest' hp y hy)
      · intro E' hE hE'
        have he0 : tE S l (S.ctx q ∪ pre.toFinset) ∈ E' := by
          apply hE
          refine List.mem_cons_of_mem _ ?_
          rw [hUeq pre l rest' hp]
          apply hj.spath c l hlsv hlc
          simp only [R, hup]
          rw [hmeq]; exact hlq
        refine edgeFrom_eq he0 rfl (by simp [tE, hlc]) fun e he hctx hd => ?_
        have heOK : EOK S c cfg.D e := by
          rcases hE' e he with he | he
          · rcases List.mem_cons.1 he with rfl | he
            · exact hmOK
            · exact hj.sedge c e he
          · exact hnewOK e he
        have hec : e.oid.1 ≠ c := by simpa using hd
        have := uniq_glob h.wf le_rfl heOK hec hlD (hctx ▸ hlU pre l rest' hp)
          (fun y hy hyc hyl => hctx ▸ (hpre pre l rest' hp y).2
            ⟨h.compat.sv_of_rank y (lt_trans hyl (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hlsv)),
              Or.inr hyl⟩)
        rw [heOK.eq_tE, this, hctx])
  have hm' : m = tE S q (S.ctx q) := by rw [hmeq, tE, hTq]
  rw [← hm'] at hloop
  refine ⟨Ef, ?_, fun e he => ?_, fun l hl => ?_⟩
  · simp only [xForm, hj.scur c, ← hP, hloop, ← hqdef]
  · rcases hback e he with he | he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hmOK
      · exact hj.sedge c e he
    · exact hnewOK e he
  · obtain ⟨pre, rest', hp⟩ := List.append_of_mem hl
    rw [← hUeq pre l rest' hp]
    exact hall _ ⟨pre, l, rest', hp, Or.inr rfl⟩

theorem ctx_sub_R (h : GI S cfg) {c : Fin n} (hupc : ∀ m ∈ cfg.up c, m.ctx = S.ctx m.oid)
    {q : Oid n} (hqD : q ∈ cfg.D) (hqc : q.1 = c) (hqsv : q ∈ cfg.sv) : S.ctx q ⊆ R cfg c := by
  unfold R
  split
  · obtain ⟨r, hr, hro⟩ := mem_D.1 hqD
    have := h.ctx_know r hr
    rw [hro, hqc, ← h.compat.ctx r hr, hro] at this
    exact this
  · rename_i m2 rest2 hup2
    have hm2 : m2 ∈ cfg.up c := by rw [hup2]; exact List.mem_cons_self
    have hfil2 := h.rf.up c
    have hmem : m2.oid ∈ (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
      rw [← hfil2]; exact List.mem_map_of_mem hm2
    simp only [List.mem_filter, decide_eq_true_eq] at hmem
    obtain ⟨hm2log, hm2c, hm2sv⟩ := hmem
    have hm2D : m2.oid ∈ cfg.D := by simpa [D] using hm2log
    have hq2 : S.rank q < S.rank m2.oid :=
      lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hqsv) (h.compat.rank_up c m2 hm2)
    have hqin : q ∈ S.ctx m2.oid := h.wf.own _ hm2D q hqD
      (by rw [h.compat.cl, h.compat.cl, hqc, hm2c]) hq2
    rw [hupc m2 hm2]
    exact h.wf.trans _ hm2D q hqin

theorem R_congr {cfg' : Cfg (jupiter n)} {j : Fin n} (h1 : cfg'.up j = cfg.up j)
    (h2 : cfg'.know j = cfg.know j) : R cfg' j = R cfg j := by
  unfold R; rw [h1, h2]

theorem JPI.srv (h : GI S cfg) (hj : JPI S cfg) {c : Fin n} {cfg' : Cfg (jupiter n)}
    (hs : cfg.step genOp (.srv c) = some cfg') (h' : GI S cfg') : JPI S cfg' := by
  obtain ⟨m, rest, s', m', hup, hsr, rfl⟩ := step_srv hs
  obtain ⟨Ef, hx, hEf, hpathE⟩ := srv_ok h hj hup
  have hm : m ∈ cfg.up c := by rw [hup]; exact List.mem_cons_self
  have hfil := h.rf.up c
  rw [hup, List.map_cons] at hfil
  have hqmem : m.oid ∈ (cfg.log.map Rec.oid).filter
      (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
    rw [← hfil]; exact List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hqmem
  obtain ⟨hqlog, hqc, hqsv⟩ := hqmem
  have hqD : m.oid ∈ cfg.D := by simpa [D] using hqlog
  have hsr' : s' = ⟨(S.T m.oid cfg.sv.toFinset).apply cfg.ss.list, fun j => if j = c then
      ⟨Ef, insert m.oid cfg.sv.toFinset⟩ else
      ⟨tE S m.oid cfg.sv.toFinset :: (cfg.ss.dss j).edges,
        insert m.oid (cfg.ss.dss j).cur⟩⟩ ∧ m' = tE S m.oid cfg.sv.toFinset := by
    simp only [jupiter, hx, Option.some.injEq, Prod.mk.injEq] at hsr
    obtain ⟨h1, h2⟩ := hsr
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨rfl, rfl⟩ := hsr'
  set q := m.oid with hqdef
  set P := cfg.sv.toFinset with hP
  have hrq : S.rank q = cfg.sv.length := by
    have := h'.compat.rank_sv cfg.sv.length (by simp)
    simpa using this
  have hPq : ∀ y, y ∈ P ↔ S.rank y < S.rank q := by
    intro y
    rw [hP, List.mem_toFinset, hrq]
    exact ⟨h.compat.rank_lt_of_mem_sv h.rf.sv_nodup, h.compat.sv_of_rank y⟩
  have hqP : q ∉ P := by rw [hP, List.mem_toFinset]; exact hqsv
  have hsv' : (cfg.sv ++ [q]).toFinset = insert q P := by
    ext y; simp [hP, or_comm]
  have hopOK : ∀ j, j ≠ c → EOK S j cfg.D (tE S q P) := by
    intro j hj'
    refine ⟨rfl, hqP, ?_, fun h1 => absurd (h1.symm.trans hqc) hj', fun _ y hy => (hPq y).2 hy⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hqD
    · simp only [tE] at hy; exact h.sv_D (List.mem_toFinset.1 hy)
  refine ⟨hj.ccur, hj.clist, hj.cedge, hj.cpath, fun j m'' hm'' => ?_, fun j m'' hm'' => ?_,
    fun j => ?_, ?_, fun j e he => ?_, fun j l hl hlc hlR => ?_⟩
  · simp only at hm''
    split_ifs at hm'' with hjc
    · exact hj.down j m'' hm''
    · rcases List.mem_append.1 hm'' with hm'' | hm''
      · exact hj.down j m'' hm''
      · rw [List.mem_singleton] at hm''
        subst hm''
        exact ⟨rfl, hPq⟩
  · by_cases hjc : j = c
    · subst hjc
      simp only [Function.update_self] at hm''
      exact hj.up j m'' (by rw [hup]; exact List.mem_cons_of_mem _ hm'')
    · simp only [Function.update_of_ne hjc] at hm''
      exact hj.up j m'' hm''
  · simp only
    split_ifs with hjc
    · exact hsv'.symm
    · rw [hj.scur j]; exact hsv'.symm
  · simp only
    rw [hsv', hj.slist]
    exact (S.edge h.wf hqP h.vert_sv (hsv' ▸ h'.vert_sv) (hsv' ▸ h'.sv_sub)).1.symm
  · simp only at he
    split_ifs at he with hjc
    · subst hjc; exact hEf e he
    · rcases List.mem_cons.1 he with rfl | he
      · exact hopOK j hjc
      · exact hj.sedge j e he
  · simp only at hl ⊢
    rw [hsv']
    have hlsv : l ∈ cfg.sv ∨ l = q := by simpa using hl
    by_cases hjc : j = c
    · subst hjc
      simp only [if_true]
      have hlsv' : l ∈ cfg.sv := hlsv.resolve_right (fun e => hlc (e ▸ hqc))
      have hRq := ctx_sub_R (S := S) (cfg := ⟨cfg.cs, _, Function.update cfg.up j rest, _, cfg.seq,
          cfg.log, cfg.know, cfg.sv ++ [(jupiter n).oidOf m]⟩) h'
        (fun m'' hm'' => by
          simp only [Function.update_self] at hm''
          have := hj.up j m'' (by rw [hup]; exact List.mem_cons_of_mem _ hm'')
          rw [this])
        (q := q) hqD hqc (by simp [q])
      have hlq : l ∉ S.ctx q := fun hlq => hlR (hRq hlq)
      have hlpath : l ∈ spathOf S cfg j q := by
        simp only [spathOf, List.mem_filter, decide_eq_true_eq]; exact ⟨hlsv', hlc, hlq⟩
      have := hpathE l hlpath
      have hfil' : (insert q P).filter (fun y => y.1 = j ∨ S.rank y < S.rank l) =
          insert q (P.filter fun y => y.1 = j ∨ S.rank y < S.rank l) := by
        rw [Finset.filter_insert, if_pos (Or.inl hqc)]
      rw [hfil']; exact this
    · simp only [hjc, if_false]
      replace hlR : l ∉ R cfg j := by
        unfold R at hlR ⊢
        simp only [Function.update_of_ne hjc] at hlR
        exact hlR
      rcases hlsv with hlsv | rfl
      · have hfil' : (insert q P).filter (fun y => y.1 = j ∨ S.rank y < S.rank l) =
            P.filter fun y => y.1 = j ∨ S.rank y < S.rank l := by
          rw [Finset.filter_insert, if_neg]
          rintro (h1 | h1)
          · exact hjc (h1.symm.trans hqc)
          · have := (hPq l).1 (by rw [hP, List.mem_toFinset]; exact hlsv); omega
        rw [hfil']
        exact List.mem_cons_of_mem _ (hj.spath j l hlsv hlc hlR)
      · have hfil' : (insert q P).filter (fun y => y.1 = j ∨ S.rank y < S.rank q) = P := by
          rw [Finset.filter_insert, if_neg (by
            rintro (h1 | h1)
            · exact hjc (h1.symm.trans hqc)
            · exact lt_irrefl _ h1)]
          exact Finset.filter_true_of_mem fun y hy => Or.inr ((hPq y).1 hy)
        rw [hfil']
        exact List.mem_cons_self

end Jup

end Podc.JupiterListSpec
