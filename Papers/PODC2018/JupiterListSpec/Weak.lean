import Papers.PODC2018.JupiterListSpec.Generic

/-!
# From the generic invariant to the weak list specification (Theorem 18)

If every `do` event returned the list of its vertex of the global state space (`GI`), then the
abstract execution of the configuration (with `vis` = "was known to the replica") is well formed
and belongs to `A_weak`; the list order is the paper's Definition 19 ("`a` precedes `b` in some
returned list"), and its irreflexivity is the pairwise compatibility of states (Lemma 21,
Theorem 26).
-/

namespace Podc.JupiterListSpec

variable {n : ℕ} {P : Proto n}

namespace Cfg

variable {S : Sched (Oid n)} {cfg : Cfg P}

/-- The vertex reached by the `do` event `r`. -/
def Rec.V (r : Rec n) : Finset (Oid n) := insert r.oid r.ctx

theorem GI.mem_log_D (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) : r.oid ∈ cfg.D :=
  mem_D.2 ⟨r, hr, rfl⟩

theorem GI.vert_V (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) : S.Vert (Rec.V r) := by
  have := h.wf.vert_insert_ctx (h.mem_log_D hr)
  rwa [h.compat.ctx r hr] at this

theorem GI.V_sub (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) :
    ↑(Rec.V r) ⊆ (↑cfg.D : Set (Oid n)) := by
  intro y hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact h.mem_log_D hr
  · have := h.wf.ctx_sub _ (h.mem_log_D hr)
    rw [h.compat.ctx r hr] at this
    exact this hy

theorem GI.oid_notMem_ctx (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) : r.oid ∉ r.ctx := by
  intro hx
  rw [← h.compat.ctx r hr] at hx
  exact lt_irrefl _ (h.wf.ctx_lt _ (h.mem_log_D hr) _ hx)

/-- Every `do` event returns the list of its vertex. -/
theorem GI.ret_eq (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) : r.ret = S.L (Rec.V r) := by
  have hctxV : S.Vert r.ctx := by
    have := h.wf.vert_ctx (h.mem_log_D hr); rwa [h.compat.ctx r hr] at this
  obtain ⟨hL, -⟩ := S.edge h.wf (h.oid_notMem_ctx hr) hctxV (h.vert_V hr) (h.V_sub hr)
  rw [Rec.V, hL, (h.recs r hr).2, S.T_of_subset (by rw [h.compat.ctx r hr]),
    h.compat.orig r hr]

theorem GI.idx_eq (h : GI S cfg) {i j : ℕ} {ri rj : Rec n} (hi : cfg.log[i]? = some ri)
    (hj : cfg.log[j]? = some rj) (he : ri.oid = rj.oid) : i = j := by
  have h1 : (cfg.log.map Rec.oid)[i]? = some ri.oid := by simp [hi]
  have h2 : (cfg.log.map Rec.oid)[j]? = some rj.oid := by simp [hj]
  rw [he] at h1
  have hil : i < (cfg.log.map Rec.oid).length := by
    simpa using (List.getElem?_eq_some_iff.1 hi).1
  exact (List.Nodup.getElem?_inj hil h.rf.lognd).1 (h1.trans h2.symm)

/-- `≤vis` is "the operation is in the vertex of the later event". -/
theorem GI.visLe_iff (h : GI S cfg) {i : ℕ} {ri : Rec n} (hi : cfg.log[i]? = some ri) (j : ℕ) :
    (absExec cfg).visLe j i ↔ ∃ rj : Rec n, cfg.log[j]? = some rj ∧ rj.oid ∈ Rec.V ri := by
  constructor
  · rintro (rfl | ⟨-, r1, r2, h1, h2, hmem⟩)
    · exact ⟨ri, hi, Finset.mem_insert_self _ _⟩
    · rw [hi] at h2; cases h2
      exact ⟨r1, h1, Finset.mem_insert_of_mem hmem⟩
  · rintro ⟨rj, hj, hmem⟩
    rcases Finset.mem_insert.1 hmem with he | hmem
    · exact Or.inl (h.idx_eq hj hi he)
    · obtain ⟨j', hj', r', hr', he⟩ := h.ctx_log i ri hi _ hmem
      have := h.idx_eq hr' hj he
      subst this
      exact Or.inr ⟨hj', r', ri, hr', hi, he ▸ hmem⟩

theorem GI.exists_log (h : GI S cfg) {y : Oid n} (hy : y ∈ cfg.D) :
    ∃ j : ℕ, ∃ rj : Rec n, cfg.log[j]? = some rj ∧ rj.oid = y := by
  obtain ⟨r, hr, rfl⟩ := mem_D.1 hy
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hr
  exact ⟨j, r, hj, rfl⟩

theorem GI.sig_ins_iff (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) (a : Oid n) :
    (∃ k, r.sig = .ins a k) ↔ ∃ p pr, S.orig r.oid = .ins a p pr := by
  obtain ⟨⟨u, hu⟩, -⟩ := h.recs r hr
  rw [h.compat.orig r hr]
  have := genOp_ins_iff (x := r.oid) (a := a) (u := u) (l := S.L r.ctx)
  rw [hu] at this
  exact this

theorem GI.sig_del_iff (h : GI S cfg) {r : Rec n} (hr : r ∈ cfg.log) (a : Oid n) :
    (∃ k, r.sig = .del (some a) k) ↔ ∃ p, S.orig r.oid = .del a p := by
  obtain ⟨⟨u, hu⟩, -⟩ := h.recs r hr
  rw [h.compat.orig r hr]
  have := genOp_del_iff (x := r.oid) (a := a) (u := u) (l := S.L r.ctx)
  rw [hu] at this
  exact this

theorem GI.ins_self (h : GI S cfg) {y a : Oid n} (hy : y ∈ cfg.D) {p pr : ℕ}
    (he : S.orig y = .ins a p pr) : a = y := by
  have := h.wf.origOk y hy
  unfold Sched.OrigOk at this
  rw [he] at this
  exact this.1

theorem absExec_H_getElem? (cfg : Cfg P) (i : ℕ) :
    (absExec cfg).H[i]? = cfg.log[i]?.map fun r => ⟨r.oid.1, r.sig, r.ret⟩ := by
  simp [absExec]

/-- Condition 1(a) of the weak list specification, in terms of the log. -/
theorem GI.cond_1a (h : GI S cfg) {i : ℕ} {ri : Rec n} (hi : cfg.log[i]? = some ri) (a : Oid n) :
    a ∈ ri.ret ↔
      (∃ j, (absExec cfg).visLe j i ∧ ∃ e ∈ (absExec cfg).H[j]?, ∃ k, e.sig = .ins a k) ∧
        ¬ ∃ j, (absExec cfg).visLe j i ∧ ∃ e ∈ (absExec cfg).H[j]?, ∃ k,
          e.sig = .del (some a) k := by
  have hri : ri ∈ cfg.log := List.mem_of_getElem? hi
  rw [h.ret_eq hri, S.mem_L h.wf (h.vert_V hri) (h.V_sub hri)]
  simp only [absExec_H_getElem?, Option.mem_def, Option.map_eq_some_iff, h.visLe_iff hi]
  constructor
  · rintro ⟨haV, ⟨p, pr, hins⟩, hdel⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨j, rj, hj, rfl⟩ := h.exists_log (h.V_sub hri haV)
      refine ⟨j, ⟨rj, hj, haV⟩, _, ⟨rj, hj, rfl⟩, ?_⟩
      exact (h.sig_ins_iff (List.mem_of_getElem? hj) _).2 ⟨p, pr, hins⟩
    · rintro ⟨j, ⟨rj, hj, hV⟩, e, ⟨rj', hj', rfl⟩, hk⟩
      rw [hj] at hj'; cases hj'
      obtain ⟨p', hp'⟩ := (h.sig_del_iff (List.mem_of_getElem? hj) a).1 hk
      exact hdel _ hV p' hp'
  · rintro ⟨⟨j, ⟨rj, hj, hV⟩, e, ⟨rj', hj', rfl⟩, hk⟩, hn⟩
    rw [hj] at hj'; cases hj'
    have hrj := List.mem_of_getElem? hj
    obtain ⟨p, pr, hins⟩ := (h.sig_ins_iff hrj a).1 hk
    have hay := h.ins_self (h.mem_log_D hrj) hins
    subst hay
    refine ⟨hV, ⟨p, pr, hins⟩, fun y hy q hq => hn ?_⟩
    obtain ⟨j', ry, hjy, rfl⟩ := h.exists_log (h.V_sub hri hy)
    exact ⟨j', ⟨ry, hjy, hy⟩, _, ⟨ry, hjy, rfl⟩,
      (h.sig_del_iff (List.mem_of_getElem? hjy) _).2 ⟨q, hq⟩⟩

/-- **Theorem 18 (generic part).** Under the generic invariant, the abstract execution of the
configuration is well formed and satisfies the weak list specification. -/
theorem GI.weak (h : GI S cfg) : (absExec cfg).WF ∧ (absExec cfg).Weak := by
  have hlen : (absExec cfg).H.length = cfg.log.length := by simp [absExec]
  have hget : ∀ i (hi : i < (absExec cfg).H.length),
      (absExec cfg).H[i] = ⟨cfg.log[i].oid.1, cfg.log[i].sig, cfg.log[i].ret⟩ := by
    intro i hi; simp [absExec]
  have hmemi : ∀ i (hi : i < cfg.log.length), cfg.log[i] ∈ cfg.log := fun i hi =>
    List.getElem_mem hi
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- per-replica order
    intro i j hi hj hij hrep
    rw [hget, hget] at hrep
    simp only at hrep
    rw [hlen] at hi hj
    refine ⟨hij, cfg.log[i], cfg.log[j], List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, ?_⟩
    have hxi := h.mem_log_D (hmemi i hi)
    have hxj := h.mem_log_D (hmemi j hj)
    rw [← h.compat.ctx _ (hmemi j hj)]
    have hcl : S.cl cfg.log[i].oid = S.cl cfg.log[j].oid := by
      rw [h.compat.cl, h.compat.cl, hrep]
    rcases lt_trichotomy (S.rank cfg.log[i].oid) (S.rank cfg.log[j].oid) with hr | hr | hr
    · exact h.wf.own _ hxj _ hxi hcl hr
    · have := h.idx_eq (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj)
        (h.wf.inj hxi hxj hr)
      omega
    · exfalso
      have hin := h.wf.own _ hxi _ hxj hcl.symm hr
      rw [h.compat.ctx _ (hmemi i hi)] at hin
      obtain ⟨j', hj', r', hr', he⟩ := h.ctx_log i _ (List.getElem?_eq_getElem hi) _ hin
      have := h.idx_eq hr' (List.getElem?_eq_getElem hj) he
      omega
  · rintro i j ⟨hij, ri, rj, hi, hj, -⟩
    exact ⟨hij, by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hj).1⟩
  · rintro i j k ⟨hij, ri, rj, hi, hj, hmem⟩ ⟨hjk, rj', rk, hj', hk, hmem'⟩
    rw [hj] at hj'; cases hj'
    refine ⟨lt_trans hij hjk, ri, rk, hi, hk, ?_⟩
    have hrj := List.mem_of_getElem? hj
    have hrk := List.mem_of_getElem? hk
    have := h.wf.trans _ (h.mem_log_D hrk) _ (by rw [h.compat.ctx _ hrk]; exact hmem')
    rw [h.compat.ctx _ hrj, h.compat.ctx _ hrk] at this
    exact this hmem
  · -- the weak list specification
    let lo : Oid n → Oid n → Prop := fun a b =>
      ∃ i : ℕ, ∃ ri : Rec n, cfg.log[i]? = some ri ∧ [a, b].Sublist ri.ret
    have hnd : ∀ (i : ℕ) (ri : Rec n), cfg.log[i]? = some ri → ri.ret.Nodup := by
      intro i ri hi
      have hri := List.mem_of_getElem? hi
      rw [h.ret_eq hri]; exact S.L_nodup h.wf (h.vert_V hri) (h.V_sub hri)
    have hcompat : ∀ (i j : ℕ) (ri rj : Rec n), cfg.log[i]? = some ri → cfg.log[j]? = some rj →
        Sched.Compatible ri.ret rj.ret := by
      intro i j ri rj hi hj
      have hri := List.mem_of_getElem? hi
      have hrj := List.mem_of_getElem? hj
      rw [h.ret_eq hri, h.ret_eq hrj]
      exact S.compatible h.wf (h.vert_V hri) (h.vert_V hrj) (h.V_sub hri) (h.V_sub hrj)
    -- the order in a returned list agrees with `lo`
    have hord : ∀ (i : ℕ) (ri : Rec n), cfg.log[i]? = some ri → ∀ a b, a ∈ ri.ret → b ∈ ri.ret → lo a b →
        [a, b].Sublist ri.ret := by
      rintro i ri hi a b ha hb ⟨j, rj, hj, hab⟩
      have hne : a ≠ b := by
        rintro rfl; exact List.nodup_iff_sublist.1 (hnd j rj hj) a hab
      rcases List.pair_sublist_total ha hb hne with h1 | h1
      · exact h1
      · exact (hcompat j i rj ri hj hi a b hab h1).elim
    refine ⟨lo, ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · rintro a b ⟨i, ri, hi, hab⟩
      have hel : ∀ c ∈ ri.ret, c ∈ (absExec cfg).elems := by
        intro c hc
        have := (h.cond_1a hi c).1 hc
        obtain ⟨⟨j, -, e, he, k, hk⟩, -⟩ := this
        exact ⟨e, List.mem_of_getElem? he, k, hk⟩
      exact ⟨hel a (hab.subset (by simp)), hel b (hab.subset (by simp))⟩
    · rw [hlen] at hi
      have hi' := List.getElem?_eq_getElem hi
      rw [hget]
      simp only
      refine ⟨fun a => h.cond_1a hi' a, List.pairwise_of_forall_sublist fun hab =>
        ⟨i, _, hi', hab⟩, fun a k hk => ?_⟩
      have hri := hmemi i hi
      obtain ⟨⟨u, hu⟩, hret⟩ := h.recs _ hri
      have hxL : cfg.log[i].oid ∉ S.L cfg.log[i].ctx := by
        intro hx
        have hctxV : S.Vert cfg.log[i].ctx := by
          have := h.wf.vert_ctx (h.mem_log_D hri); rwa [h.compat.ctx _ hri] at this
        have hsub : ↑cfg.log[i].ctx ⊆ (↑cfg.D : Set (Oid n)) := fun y hy =>
          h.V_sub hri (Finset.mem_insert_of_mem hy)
        exact h.oid_notMem_ctx hri ((S.mem_L h.wf hctxV hsub _).1 hx).1
      have := genOp_ret hxL (u := u) (k := k) (a := a) (by rw [hu]; exact hk)
      rw [hu] at this
      rw [hret]; exact this
    · rintro a ⟨i, ri, hi, haa⟩
      exact List.nodup_iff_sublist.1 (hnd i ri hi) a haa
    · intro i hi a b c ha hb hc hab hbc
      rw [hlen] at hi
      rw [hget] at ha hb hc
      simp only at ha hb hc
      have hi' := List.getElem?_eq_getElem hi
      exact ⟨i, _, hi', List.pair_sublist_trans (hnd i _ hi') (hord i _ hi' a b ha hb hab)
        (hord i _ hi' b c hb hc hbc)⟩
    · intro i hi a b ha hb hne
      rw [hlen] at hi
      rw [hget] at ha hb
      simp only at ha hb
      have hi' := List.getElem?_eq_getElem hi
      rcases List.pair_sublist_total ha hb hne with h1 | h1
      · exact Or.inl ⟨i, _, hi', h1⟩
      · exact Or.inr ⟨i, _, hi', h1⟩

end Cfg

end Podc.JupiterListSpec
