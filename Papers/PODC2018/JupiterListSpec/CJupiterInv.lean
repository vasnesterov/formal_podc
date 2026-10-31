import Papers.PODC2018.JupiterListSpec.CJupiterWalk

/-!
# The invariant of CJupiter: every replica holds the global state space restricted to what it
processed (Proposition 9)

The state space of every replica is *sound* (every edge is labelled by the global transformation
`T`, with the server context the replica can know: the true one for operations that went through
the server, `∅` for a client's own operations) and *complete* (from every vertex `u` below the
current vertex there is an edge labelled with the `≺s`-first missing operation). Hence every
`xForm` follows the `≺s`-ordered path (Lemma 5) and computes `T` (Lemma 7), and each replica's list
is the list of its vertex of the global state space.
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

namespace CJup

open Cfg

variable {S : Sched (Oid n)}

/-- The server context of an operation of the server order: the operations before it. -/
def spre {P : Proto n} (S : Sched (Oid n)) (cfg : Cfg P) (y : Oid n) : Finset (Oid n) :=
  cfg.sv.toFinset.filter fun z => S.rank z < S.rank y

/-- The server contexts known at a replica (`none` = the server): a client does not know the
server contexts of its own operations. -/
def sig {P : Proto n} (S : Sched (Oid n)) (cfg : Cfg P) (r : Option (Fin n)) (y : Oid n) :
    Finset (Oid n) :=
  match r with
  | none => spre S cfg y
  | some c => if y.1 = c then ∅ else spre S cfg y

/-- The invariant of CJupiter. -/
structure CPI (S : Sched (Oid n)) (cfg : Cfg (cjupiter n)) : Prop where
  ccur : ∀ c, (cfg.cs c).css.cur = cfg.know c
  clist : ∀ c, (cfg.cs c).list = S.L (cfg.know c)
  cedge : ∀ c, ∀ e ∈ (cfg.cs c).css.edges, CEOK S (sig S cfg (some c)) (cfg.know c) e
  ccomp : ∀ c, Comp S (cfg.know c) (cfg.cs c).css.edges
  up : ∀ c, ∀ m ∈ cfg.up c, m = ⟨S.orig m.oid, m.oid, S.ctx m.oid, ∅⟩
  down : ∀ c, ∀ m ∈ cfg.down c, m = ⟨S.orig m.oid, m.oid, S.ctx m.oid, spre S cfg m.oid⟩
  scur : cfg.ss.css.cur = cfg.sv.toFinset
  slist : cfg.ss.list = S.L cfg.sv.toFinset
  soids : cfg.ss.soids = cfg.sv.toFinset
  sedge : ∀ e ∈ cfg.ss.css.edges, CEOK S (sig S cfg none) cfg.sv.toFinset e
  scomp : Comp S cfg.sv.toFinset cfg.ss.css.edges

theorem CPI.init (S : Sched (Oid n)) : CPI S (Cfg.init (cjupiter n)) := by
  refine ⟨fun c => rfl, fun c => ?_, fun c => by simp [Cfg.init], fun c u _ hu hne => ?_,
    fun c => by simp [Cfg.init], fun c => by simp [Cfg.init], rfl, ?_, rfl,
    by simp [Cfg.init], fun u _ hu hne => ?_⟩
  · simp [Cfg.init, S.L_empty]
  · exact absurd (Finset.subset_empty.1 (by simpa [Cfg.init] using hu))
      (by simpa [Cfg.init] using hne)
  · simp [Cfg.init, S.L_empty]
  · exact absurd (Finset.subset_empty.1 (by simpa [Cfg.init] using hu))
      (by simpa [Cfg.init] using hne)

section generic

variable {P : Proto n} {cfg : Cfg P}

theorem mem_spre {y z : Oid n} : z ∈ spre S cfg y ↔ z ∈ cfg.sv ∧ S.rank z < S.rank y := by
  simp [spre]

/-- At the server, `Compare` agrees with `≺s`. -/
theorem cmpOK_srv (h : GI S cfg) : CmpOK S none (sig S cfg none) cfg.sv.toFinset := by
  intro l y u o₁ o₂ hl _ _ _ _ hlt
  have hl_in : l ∈ spre S cfg y := mem_spre.2 ⟨List.mem_toFinset.1 hl, hlt⟩
  have hy_notin : y ∉ spre S cfg l := fun hy => absurd (mem_spre.1 hy).2 (by omega)
  simp [cmp, sig, hl_in, hy_notin]

/-- At a client, `Compare` agrees with `≺s` on edges from a common vertex. -/
theorem cmpOK_cl (h : GI S cfg) (c : Fin n) :
    CmpOK S (some c) (sig S cfg (some c)) (cfg.know c) := by
  intro l y u o₁ o₂ hl hy hlu hyu hyctx hlt
  have hlD := h.know_D hl
  have hyD := h.know_D hy
  have hsv : ∀ z ∈ cfg.know c, z.1 ≠ c → z ∈ cfg.sv := fun z hz hzc => by
    rcases (h.know c z).1 hz with ⟨-, h2⟩ | ⟨h1, -, -⟩
    · exact absurd h2 hzc
    · exact h1
  by_cases hlc : l.1 = c <;> by_cases hyc : y.1 = c
  · exfalso
    exact hlu (hyctx (h.wf.own y hyD l hlD (by rw [h.compat.cl, h.compat.cl, hlc, hyc]) hlt))
  · have hysv := hsv y hy hyc
    have hlsv : l ∈ cfg.sv := h.compat.sv_of_rank l
      (lt_trans hlt (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hysv))
    have hl_in : l ∈ spre S cfg y := mem_spre.2 ⟨hlsv, hlt⟩
    simp [cmp, sig, hlc, hyc, hl_in]
  · have hy_notin : y ∉ spre S cfg l := fun hy' => absurd (mem_spre.1 hy').2 (by omega)
    simp [cmp, sig, hlc, hyc, hy_notin, Ne.symm hlc]
  · have hl_in : l ∈ spre S cfg y := mem_spre.2 ⟨hsv l hl hlc, hlt⟩
    have hy_notin : y ∉ spre S cfg l := fun hy' => absurd (mem_spre.1 hy').2 (by omega)
    simp [cmp, sig, hlc, hyc, hl_in, hy_notin]

/-- The context of the next operation the server processes is in the server's state. -/
theorem ctx_head_up (h : GI S cfg) {c : Fin n} {m : P.Msg} {rest : List P.Msg}
    (hup : cfg.up c = m :: rest) : S.ctx (P.oidOf m) ⊆ cfg.sv.toFinset := by
  have hm : m ∈ cfg.up c := by rw [hup]; exact List.mem_cons_self
  set q := P.oidOf m with hqdef
  have hfil := h.rf.up c
  rw [hup, List.map_cons] at hfil
  have hqmem : q ∈ (cfg.log.map Rec.oid).filter (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
    rw [← hfil]; exact List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hqmem
  obtain ⟨hqlog, hqc, hqsv⟩ := hqmem
  have hqD : q ∈ cfg.D := by simpa [D] using hqlog
  have hrest : ∀ m' ∈ rest, S.rank q < S.rank (P.oidOf m') := by
    have hs := h.compat.up_sorted c
    rw [hup, List.map_cons, List.pairwise_cons] at hs
    exact fun m' hm' => hs.1 _ (List.mem_map_of_mem (f := fun m => S.rank (P.oidOf m)) hm')
  intro y hy
  rw [List.mem_toFinset]
  have hyl := h.wf.ctx_lt q hqD y hy
  have hyD : y ∈ cfg.D := h.wf.ctx_sub q hqD hy
  by_contra hysv
  by_cases hyc : y.1 = c
  · have : y ∈ (cfg.up c).map P.oidOf := by
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

/-- Operations of other clients known to `c` precede everything on its down channel. -/
theorem others_lt_down (h : GI S cfg) {c : Fin n} {y : Oid n} (hy : y ∈ cfg.know c)
    (hyc : y.1 ≠ c) {m : P.Msg} (hm : m ∈ cfg.down c) : S.rank y < S.rank (P.oidOf m) := by
  rcases (h.know c y).1 hy with ⟨-, h2⟩ | ⟨-, -, h3⟩
  · exact absurd h2 hyc
  · exact h3 m hm

/-- The context of the next operation a client receives is in its state. -/
theorem ctx_head_down (h : GI S cfg) {c : Fin n} {m : P.Msg} {rest : List P.Msg}
    (hdown : cfg.down c = m :: rest) : S.ctx (P.oidOf m) ⊆ cfg.know c := by
  have hm : m ∈ cfg.down c := by rw [hdown]; exact List.mem_cons_self
  obtain ⟨hjsv, -, -⟩ := h.down_sv hm
  have hjD := h.sv_D hjsv
  have hsrt := h.down_sorted c
  rw [hdown, List.map_cons, List.pairwise_cons] at hsrt
  intro y hy
  have hyl := h.wf.ctx_lt _ hjD y hy
  have hysv := h.compat.sv_of_rank y
    (lt_trans hyl (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hjsv))
  by_cases hyc : y.1 = c
  · exact (h.know c y).2 (Or.inl ⟨h.sv_D hysv, hyc⟩)
  · refine (h.know c y).2 (Or.inr ⟨hysv, hyc, fun m' hm' => ?_⟩)
    rw [hdown] at hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · exact hyl
    · exact lt_trans hyl (hsrt.1 _ (List.mem_map_of_mem (f := fun m => S.rank (P.oidOf m)) hm'))

end generic

variable {cfg : Cfg (cjupiter n)}

theorem CPI.do (h : GI S cfg) (hj : CPI S cfg) {c : Fin n} {u : UOp}
    (h' : GI S (doCfg genOp cfg c u)) : CPI S (doCfg genOp cfg c u) := by
  set x : Oid n := (c, cfg.seq c) with hx
  set K := cfg.know c with hK
  have hlist : (cjupiter n).list (cfg.cs c) = S.L K := hj.clist c
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
  have hcs : (doCfg genOp cfg c u).cs c =
      ⟨og.1.apply (cfg.cs c).list, ⟨⟨og.1, x, K, ∅⟩ :: (cfg.cs c).css.edges, insert x K⟩⟩ := by
    simp only [doCfg, Function.update_self, cjupiter, hj.ccur c, x, K, og]
    rw [show (cfg.cs c).list = S.L (cfg.know c) from hlist]
  have hcsne : ∀ c', c' ≠ c → (doCfg genOp cfg c u).cs c' = cfg.cs c' := by
    intro c' hc'; simp [doCfg, Function.update_of_ne hc']
  have hknowne : ∀ c', c' ≠ c → (doCfg genOp cfg c u).know c' = cfg.know c' := by
    intro c' hc'; simp [doCfg, Function.update_of_ne hc']
  have hsig : ∀ r, sig S (doCfg genOp cfg c u) r = sig S cfg r := fun r => rfl
  have hopOK : CEOK S (sig S cfg (some c)) (insert x K) ⟨og.1, x, K, ∅⟩ := by
    refine ⟨?_, hxK, le_rfl, by rw [hctx]⟩
    simp [hT, sig, x]
  refine ⟨fun c' => ?_, fun c' => ?_, fun c' e he => ?_, fun c' => ?_, fun c' m hm => ?_,
    fun c' m hm => hj.down c' m hm, hj.scur, hj.slist, hj.soids, hj.sedge, hj.scomp⟩
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
  · rw [hsig]
    by_cases hc : c' = c
    · subst hc
      rw [hcs] at he
      rw [hknow']
      rcases List.mem_cons.1 he with rfl | he
      · exact hopOK
      · exact (hj.cedge c' e he).mono (Finset.subset_insert _ _)
    · rw [hcsne c' hc] at he; rw [hknowne c' hc]; exact hj.cedge c' e he
  · by_cases hc : c' = c
    · subst hc
      rw [hcs, hknow']
      intro v hv hvQ hne
      by_cases hxv : x ∈ v
      · exfalso; apply hne
        refine le_antisymm hvQ (Finset.insert_subset hxv ?_)
        rw [← hctx]; exact hv.1 x hxv
      · have hvK : v ⊆ K := fun y hy =>
          (Finset.mem_insert.1 (hvQ hy)).resolve_left (fun e => hxv (e ▸ hy))
        by_cases hvK' : v = K
        · refine ⟨⟨og.1, x, K, ∅⟩, List.mem_cons_self, hvK'.symm, Finset.mem_insert_self _ _,
            hxv, fun y hy hyv => ?_⟩
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact le_rfl
          · exact absurd (hvK' ▸ hy) hyv
        · obtain ⟨e, he, hctx', heQ, hev, hemin⟩ := hj.ccomp c' v hv hvK hvK'
          refine ⟨e, List.mem_cons_of_mem _ he, hctx', Finset.mem_insert_of_mem heQ, hev,
            fun y hy hyv => ?_⟩
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact (hlt _ heQ).le
          · exact hemin y hy hyv
    · rw [hcsne c' hc, hknowne c' hc]; exact hj.ccomp c'
  · by_cases hc : c' = c
    · subst hc
      simp only [doCfg, Function.update_self, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact hj.up c' m hm
      · have e1 : S.orig (c', cfg.seq c') = (genOp (c', cfg.seq c') u (S.L (cfg.know c'))).1 :=
          horig
        have e2 : S.ctx (c', cfg.seq c') = cfg.know c' := hctx
        simp only [cjupiter, hj.clist c', hj.ccur c', e1, e2]
    · simp only [doCfg, Function.update_of_ne hc] at hm; exact hj.up c' m hm

/-- Server contexts of operations before `q` do not change when `q` is appended to `sv`. -/
theorem spre_snoc {P : Proto n} {cfg cfg' : Cfg P} {q : Oid n} (hsv : cfg'.sv = cfg.sv ++ [q])
    {y : Oid n} (hy : S.rank y ≤ S.rank q) : spre S cfg' y = spre S cfg y := by
  ext z
  simp only [mem_spre, hsv, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hz | rfl, hzy⟩
    · exact ⟨hz, hzy⟩
    · omega
  · rintro ⟨hz, hzy⟩; exact ⟨Or.inl hz, hzy⟩

/-- Server processing succeeds and computes the global transformation. -/
theorem csrv_ok (h : GI S cfg) (hj : CPI S cfg) {c : Fin n} {m : COp n} {rest : List (COp n)}
    (hup : cfg.up c = m :: rest) :
    ∃ Ef, cxForm none cfg.ss.css { m with sctx := cfg.ss.soids } =
        some (⟨Ef, insert m.oid cfg.sv.toFinset⟩,
          opE S m.oid (sig S cfg none m.oid) cfg.sv.toFinset) ∧
      (∀ e ∈ Ef, CEOK S (sig S cfg none) (insert m.oid cfg.sv.toFinset) e) ∧
      Comp S (insert m.oid cfg.sv.toFinset) Ef ∧
      sig S cfg none m.oid = cfg.sv.toFinset ∧ m.oid ∉ cfg.sv ∧ m.oid.1 = c ∧ m.oid ∈ cfg.D := by
  have hm : m ∈ cfg.up c := by rw [hup]; exact List.mem_cons_self
  have hmeq := hj.up c m hm
  have hfil := h.rf.up c
  rw [hup, List.map_cons] at hfil
  have hqmem : m.oid ∈ (cfg.log.map Rec.oid).filter
      (fun x => decide (x.1 = c ∧ x ∉ cfg.sv)) := by
    rw [← hfil]; exact List.mem_cons_self
  simp only [List.mem_filter, decide_eq_true_eq] at hqmem
  obtain ⟨hqlog, hqc, hqsv⟩ := hqmem
  have hqD : m.oid ∈ cfg.D := by simpa [D] using hqlog
  have hqrank : cfg.sv.length ≤ S.rank m.oid := h.compat.rank_up c m hm
  have hsvq : ∀ y ∈ cfg.sv, S.rank y < S.rank m.oid := fun y hy =>
    lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hy) hqrank
  have hσq : sig S cfg none m.oid = cfg.sv.toFinset := by
    ext z
    simp only [sig, mem_spre, List.mem_toFinset]
    exact ⟨fun hz => hz.1, fun hz => ⟨hz, hsvq z hz⟩⟩
  have hm' : ({ m with sctx := cfg.ss.soids } : COp n) =
      opE S m.oid (sig S cfg none m.oid) (S.ctx m.oid) := by
    rw [hσq, ← hj.soids]
    conv_lhs => rw [hmeq]
    simp [opE, S.T_of_subset (le_refl (S.ctx m.oid))]
  have hcss : cfg.ss.css = ⟨cfg.ss.css.edges, cfg.sv.toFinset⟩ := by rw [← hj.scur]
  obtain ⟨Ef, hx, hEf, hcomp⟩ := walk h (r := none) (σ := sig S cfg none)
    (Q := cfg.sv.toFinset) (E := cfg.ss.css.edges) (j := m.oid) h.vert_sv h.sv_sub hqD
    (by rw [List.mem_toFinset]; exact hqsv) (ctx_head_up h hup)
    (fun y hy z hz hz1 _ => absurd hz1 (not_lt.2 (hsvq z (List.mem_toFinset.1 hz)).le))
    (fun y hy _ => hsvq y (List.mem_toFinset.1 hy)) hj.sedge hj.scomp (cmpOK_srv h)
  refine ⟨Ef, ?_, hEf, hcomp, hσq, hqsv, hqc, hqD⟩
  rw [hm', hcss]; exact hx

theorem CPI.srv (h : GI S cfg) (hj : CPI S cfg) {c : Fin n} {cfg' : Cfg (cjupiter n)}
    (hs : cfg.step genOp (.srv c) = some cfg') (h' : GI S cfg') : CPI S cfg' := by
  obtain ⟨m, rest, s', m', hup, hsr, rfl⟩ := step_srv hs
  obtain ⟨Ef, hx, hEf, hcomp, hσq, hqsv, hqc, hqD⟩ := csrv_ok h hj hup
  have hm : m ∈ cfg.up c := by rw [hup]; exact List.mem_cons_self
  have hsr' : s' = ⟨(S.T m.oid cfg.sv.toFinset).apply cfg.ss.list, insert m.oid cfg.ss.soids,
      ⟨Ef, insert m.oid cfg.sv.toFinset⟩⟩ ∧ m' = { m with sctx := cfg.ss.soids } := by
    simp only [cjupiter, hx, Option.some.injEq, Prod.mk.injEq] at hsr
    obtain ⟨h1, h2⟩ := hsr
    exact ⟨by rw [← h1]; rfl, h2.symm⟩
  obtain ⟨rfl, rfl⟩ := hsr'
  set q := m.oid with hqdef
  set P := cfg.sv.toFinset with hP
  have hsvq : ∀ y ∈ cfg.sv, S.rank y < S.rank q := fun y hy =>
    lt_of_lt_of_le (h.compat.rank_lt_of_mem_sv h.rf.sv_nodup hy) (h.compat.rank_up c m hm)
  have hsv' : (cfg.sv ++ [q]).toFinset = insert q P := by ext y; simp [hP, or_comm]
  have hqP : q ∉ P := by rw [hP, List.mem_toFinset]; exact hqsv
  have hmeq := hj.up c m hm
  refine ⟨hj.ccur, hj.clist, fun c' e he => ?_, hj.ccomp, fun c' m'' hm'' => ?_,
    fun c' m'' hm'' => ?_, ?_, ?_, ?_, fun e he => ?_, ?_⟩
  · refine (hj.cedge c' e he).congr fun y hy => ?_
    simp only [sig]
    split_ifs with hyc
    · rfl
    · have hysv : y ∈ cfg.sv := by
        rcases (h.know c' y).1 hy with ⟨-, h2⟩ | ⟨h1, -, -⟩
        · exact absurd h2 hyc
        · exact h1
      exact (spre_snoc rfl (hsvq y hysv).le).symm
  · by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self] at hm''
      exact hj.up c' m'' (by rw [hup]; exact List.mem_cons_of_mem _ hm'')
    · simp only [Function.update_of_ne hc] at hm''
      exact hj.up c' m'' hm''
  · have hold : ∀ m₀ ∈ cfg.down c', m₀ = ⟨S.orig m₀.oid, m₀.oid, S.ctx m₀.oid,
        spre S cfg m₀.oid⟩ ∧ S.rank m₀.oid ≤ S.rank q := fun m₀ hm₀ =>
      ⟨hj.down c' m₀ hm₀, (hsvq _ (h.down_sv hm₀).1).le⟩
    simp only at hm''
    split_ifs at hm'' with hc
    · obtain ⟨h1, h2⟩ := hold m'' hm''
      rw [spre_snoc rfl h2]; exact h1
    · rcases List.mem_append.1 hm'' with hm'' | hm''
      · obtain ⟨h1, h2⟩ := hold m'' hm''
        rw [spre_snoc rfl h2]; exact h1
      · rw [List.mem_singleton] at hm''
        subst hm''
        rw [spre_snoc rfl le_rfl]
        have : spre S cfg q = P := hσq
        simp only [this, hj.soids]
        conv_lhs => rw [hmeq]
  · exact hsv'.symm
  · simp only
    rw [hsv', hj.slist]
    exact (S.edge h.wf hqP h.vert_sv (hsv' ▸ h'.vert_sv) (hsv' ▸ h'.sv_sub)).1.symm
  · simp only; rw [hj.soids, hsv']
  · simp only at he
    rw [hsv']
    refine (hEf e he).congr fun y hy => ?_
    have hyq : S.rank y ≤ S.rank q := by
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact le_rfl
      · exact (hsvq y (List.mem_toFinset.1 hy)).le
    exact (spre_snoc rfl hyq).symm
  · simp only; rw [hsv']; exact hcomp

/-- Remote processing at a client succeeds and computes the global transformation. -/
theorem crecv_ok (h : GI S cfg) (hj : CPI S cfg) {c : Fin n} {m : COp n} {rest : List (COp n)}
    (hdown : cfg.down c = m :: rest) :
    ∃ Ef, cxForm (some c) (cfg.cs c).css m =
        some (⟨Ef, insert m.oid (cfg.know c)⟩,
          opE S m.oid (sig S cfg (some c) m.oid) (cfg.know c)) ∧
      (∀ e ∈ Ef, CEOK S (sig S cfg (some c)) (insert m.oid (cfg.know c)) e) ∧
      Comp S (insert m.oid (cfg.know c)) Ef := by
  have hm : m ∈ cfg.down c := by rw [hdown]; exact List.mem_cons_self
  have hmeq := hj.down c m hm
  obtain ⟨hjsv, hjc, hjK⟩ : m.oid ∈ cfg.sv ∧ m.oid.1 ≠ c ∧ m.oid ∉ cfg.know c := h.down_sv hm
  have hσj : sig S cfg (some c) m.oid = spre S cfg m.oid := by simp [sig, hjc]
  have hm' : m = opE S m.oid (sig S cfg (some c) m.oid) (S.ctx m.oid) := by
    rw [hσj]
    conv_lhs => rw [hmeq]
    simp [opE, S.T_of_subset (le_refl (S.ctx m.oid))]
  have hcss : (cfg.cs c).css = ⟨(cfg.cs c).css.edges, cfg.know c⟩ := by rw [← hj.ccur c]
  have hown : ∀ y ∈ cfg.know c, S.rank m.oid < S.rank y → y.1 = c := by
    intro y hy hlt
    by_contra hyc
    exact absurd (others_lt_down h hy hyc hm) (not_lt.2 hlt.le)
  obtain ⟨Ef, hx, hEf, hcomp⟩ := walk h (r := some c) (σ := sig S cfg (some c))
    (Q := cfg.know c) (E := (cfg.cs c).css.edges) (j := m.oid) (h.vert_know c) (h.know_sub c)
    (h.sv_D hjsv) hjK (ctx_head_down h hdown)
    (fun y hy z hz hjz hzy => h.wf.own y (h.know_D hy) z (h.know_D hz)
      (by rw [h.compat.cl, h.compat.cl, hown z hz hjz, hown y hy (lt_trans hjz hzy)]) hzy)
    (fun y hy hcly => others_lt_down h hy (fun hyc => hjc (by
      rw [h.compat.cl, h.compat.cl] at hcly
      exact (Fin.ext hcly).symm.trans hyc)) hm)
    (hj.cedge c) (hj.ccomp c) (cmpOK_cl h c)
  refine ⟨Ef, ?_, hEf, hcomp⟩
  conv_lhs => rw [hcss, hm']
  exact hx

theorem CPI.recv (h : GI S cfg) (hj : CPI S cfg) {c : Fin n} {cfg' : Cfg (cjupiter n)}
    (hs : cfg.step genOp (.recv c) = some cfg') (h' : GI S cfg') : CPI S cfg' := by
  obtain ⟨m, rest, s', hdown, hcr, rfl⟩ := step_recv hs
  obtain ⟨Ef, hx, hEf, hcomp⟩ := crecv_ok h hj hdown
  have hm : m ∈ cfg.down c := by rw [hdown]; exact List.mem_cons_self
  obtain ⟨hjsv, hjc, hjK⟩ : m.oid ∈ cfg.sv ∧ m.oid.1 ≠ c ∧ m.oid ∉ cfg.know c := h.down_sv hm
  have hs' : s' = ⟨(S.T m.oid (cfg.know c)).apply (cfg.cs c).list,
      ⟨Ef, insert m.oid (cfg.know c)⟩⟩ := by
    simp only [cjupiter, hx, Option.some.injEq] at hcr
    rw [← hcr]; rfl
  subst hs'
  have hknow' : ∀ c', (Function.update cfg.know c (insert m.oid (cfg.know c))) c' =
      if c' = c then insert m.oid (cfg.know c) else cfg.know c' := by
    intro c'; by_cases hc : c' = c
    · subst hc; simp
    · simp [Function.update_of_ne hc, hc]
  refine ⟨fun c' => ?_, fun c' => ?_, fun c' e he => ?_, fun c' => ?_, hj.up,
    fun c' m'' hm'' => ?_, hj.scur, hj.slist, hj.soids, hj.sedge, hj.scomp⟩
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
  · simp only [hknow']
    by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self, if_true] at he ⊢
      exact hEf e he
    · simp only [Function.update_of_ne hc, hc, if_false] at he ⊢
      exact hj.cedge c' e he
  · simp only [hknow']
    by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self, if_true]
      exact hcomp
    · simp only [Function.update_of_ne hc, hc, if_false]
      exact hj.ccomp c'
  · by_cases hc : c' = c
    · subst hc
      simp only [Function.update_self] at hm''
      exact hj.down c' m'' (by rw [hdown]; exact List.mem_cons_of_mem _ hm'')
    · simp only [Function.update_of_ne hc] at hm''
      exact hj.down c' m'' hm''

end CJup

end Podc.JupiterListSpec
