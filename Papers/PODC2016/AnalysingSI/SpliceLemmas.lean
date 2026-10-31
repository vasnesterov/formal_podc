import Papers.PODC2016.AnalysingSI.Chopping

/-!
# Splicing a dependency graph (Cerone–Gotsman, PODC 2016, §5 and §A.4–A.5)

For a chopped history `C` and a dependency graph `G = (H_C, WR, WW)` in `GraphSI` whose dynamic
chopping graph has no critical cycle, we define `splice(G)` by lifting read and write dependencies
to sessions (equation (2)) and prove:

* Lemma 26: `splice(G)` is a dependency graph;
* Lemma 27: `𝒯_{splice(G)} ⊨ INT`;
* Lemma 17: anti-dependencies of `splice(G)` come from anti-dependencies of `G`.
-/

namespace Podc.AnalysingSI

open Relation

set_option linter.unusedSectionVars false

variable {Obj V : Type*} [DecidableEq Obj] {ι : Type*}

namespace Chopped

variable {C : Chopped ι Obj V}

/-- Lifting a relation on transactions to sessions as in equation (2):
`T^G —R'→ S^G ⟺ T^G ≠ S^G ∧ T (≈ ; R ; ≈) S`. -/
def liftRel (R : Obj → C.Tid → C.Tid → Prop) (x : Obj) (s t : ι) : Prop :=
  s ≠ t ∧ ∃ p q : C.Tid, p.1.1 = s ∧ q.1.1 = t ∧ R x p q

variable (C) in
/-- `splice(G)` (equation (2)). -/
def spliceGraph (WR WW : Obj → C.Tid → C.Tid → Prop) : DepGraph ι Obj V :=
  { toHistory := C.splice, WR := liftRel WR, WW := liftRel WW }

variable {WR WW : Obj → C.Tid → C.Tid → Prop}

/-- The hypotheses of Theorem 16: `G ∈ GraphSI` and `DCG(G)` has no critical cycle. -/
structure Hyp (C : Chopped ι Obj V) (WR WW : Obj → C.Tid → C.Tid → Prop) : Prop where
  dg : (C.graph WR WW).IsDepGraph
  int : (C.graph WR WW).IntAll
  acyc : Acyclic (Comp (C.graph WR WW).B (ReflGen (C.graph WR WW).RWu))
  crit : ∀ w, ¬ IsCritical (C.graph WR WW) w

/-! ### Basic facts -/

theorem so_iff {p q : C.Tid} : (C.graph WR WW).SO p q ↔ p.1.1 = q.1.1 ∧ p.1.2 < q.1.2 :=
  Iff.rfl

theorem tid_ext {p q : C.Tid} (h1 : p.1.1 = q.1.1) (h2 : p.1.2 = q.1.2) : p = q :=
  Subtype.ext (Prod.ext h1 h2)

theorem tid_trich {p q : C.Tid} (h : p.1.1 = q.1.1) :
    p = q ∨ (C.graph WR WW).SO p q ∨ (C.graph WR WW).SO q p := by
  rcases lt_trichotomy p.1.2 q.1.2 with h' | h' | h'
  · exact Or.inr (Or.inl ⟨h, h'⟩)
  · exact Or.inl (tid_ext h h')
  · exact Or.inr (Or.inr ⟨h.symm, h'⟩)

theorem ne_of_sess_ne {p q : C.Tid} (h : p.1.1 ≠ q.1.1) : p ≠ q := by
  rintro rfl; exact h rfl

theorem ne_of_so {p q : C.Tid} (h : (C.graph WR WW).SO p q) : p ≠ q := by
  rintro rfl; exact lt_irrefl _ h.2

theorem so_trans {p q r : C.Tid} (h1 : (C.graph WR WW).SO p q) (h2 : (C.graph WR WW).SO q r) :
    (C.graph WR WW).SO p r :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- The transaction at position `j` of session `s`. -/
def tid (C : Chopped ι Obj V) (s : ι) (j : ℕ) (hj : j < (C.sess s).length) : C.Tid := ⟨(s, j), hj⟩

@[simp] theorem tid_sess (s : ι) (j : ℕ) (hj : j < (C.sess s).length) : (C.tid s j hj).1.1 = s :=
  rfl
@[simp] theorem tid_idx (s : ι) (j : ℕ) (hj : j < (C.sess s).length) : (C.tid s j hj).1.2 = j :=
  rfl

theorem graph_txn (p : C.Tid) : (C.graph WR WW).txn p = (C.sess p.1.1)[p.1.2]'p.2 := rfl

theorem rw_irrefl' {p : C.Tid} {x : Obj} : ¬ (C.graph WR WW).RW x p p := fun h => h.1 rfl

/-! ### Small critical cycles -/

theorem isCritical_of {w : List (CLbl × C.Tid)} (hc : IsCycle (dcg (C.graph WR WW)) w)
    (hs : IsSimple w)
    (hcpc : ∃ k c₁ c₂ rest, (labels w).rotate k = c₁ :: .pred :: c₂ :: rest ∧
      c₁.IsConflict ∧ c₂.IsConflict)
    (hrw : (labels w).count .rw ≤ 1) : IsCritical (C.graph WR WW) w := by
  refine ⟨hc, hs, hcpc, ?_⟩
  intro k mid rest h
  have hc' : ((labels w).rotate k).count CLbl.rw = (labels w).count CLbl.rw :=
    (List.rotate_perm _ _).count_eq _
  rw [h] at hc'
  simp at hc'
  omega

namespace Hyp

theorem no_crit3 (h : Hyp C WR WW) {l₁ l₂ l₃ : CLbl} {a b c : C.Tid}
    (h₁ : dcg (C.graph WR WW) l₁ a b) (h₂ : dcg (C.graph WR WW) l₂ b c)
    (h₃ : dcg (C.graph WR WW) l₃ c a) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hcpc : ∃ k c₁ c₂ rest, [l₁, l₂, l₃].rotate k = c₁ :: .pred :: c₂ :: rest ∧
      c₁.IsConflict ∧ c₂.IsConflict)
    (hrw : [l₁, l₂, l₃].count .rw ≤ 1) : False := by
  refine h.crit [(l₁, b), (l₂, c), (l₃, a)] (isCritical_of ?_ ?_ hcpc hrw)
  · exact ⟨by simp, a, .cons h₁ (.cons h₂ (.cons h₃ (.nil a)))⟩
  · simp [IsSimple]
    exact ⟨⟨hbc, hab.symm⟩, hca⟩

theorem no_crit4 (h : Hyp C WR WW) {l₁ l₂ l₃ l₄ : CLbl} {a b c d : C.Tid}
    (h₁ : dcg (C.graph WR WW) l₁ a b) (h₂ : dcg (C.graph WR WW) l₂ b c)
    (h₃ : dcg (C.graph WR WW) l₃ c d) (h₄ : dcg (C.graph WR WW) l₄ d a)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcpc : ∃ k c₁ c₂ rest, [l₁, l₂, l₃, l₄].rotate k = c₁ :: .pred :: c₂ :: rest ∧
      c₁.IsConflict ∧ c₂.IsConflict)
    (hrw : [l₁, l₂, l₃, l₄].count .rw ≤ 1) : False := by
  refine h.crit [(l₁, b), (l₂, c), (l₃, d), (l₄, a)] (isCritical_of ?_ ?_ hcpc hrw)
  · exact ⟨by simp, a, .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.nil a))))⟩
  · simp [IsSimple]
    exact ⟨⟨hbc, hbd, hab.symm⟩, ⟨hcd, hac.symm⟩, had.symm⟩

/-! ### Short cycles excluded by `G ∈ GraphSI` -/

section GraphSI

variable (h : Hyp C WR WW)
include h

theorem cyc_B {a b : C.Tid} (hab : (C.graph WR WW).B a b) :
    TransGen (Comp (C.graph WR WW).B (ReflGen (C.graph WR WW).RWu)) a b :=
  TransGen.single ⟨b, hab, ReflGen.refl⟩

theorem cyc_BR {a b c : C.Tid} (hab : (C.graph WR WW).B a b) (hbc : (C.graph WR WW).RWu b c) :
    TransGen (Comp (C.graph WR WW).B (ReflGen (C.graph WR WW).RWu)) a c :=
  TransGen.single ⟨b, hab, ReflGen.single hbc⟩

/-- `p —SO→ q —WW→ p` is impossible. -/
theorem F1 {p q : C.Tid} {x : Obj} (h1 : (C.graph WR WW).SO p q) (h2 : WW x q p) : False :=
  h.acyc p ((h.cyc_B (Or.inl h1)).trans (h.cyc_B (Or.inr (Or.inr ⟨x, h2⟩))))

/-- `p —SO→ q —WR→ p` is impossible. -/
theorem F2 {p q : C.Tid} {x : Obj} (h1 : (C.graph WR WW).SO p q) (h2 : WR x q p) : False :=
  h.acyc p ((h.cyc_B (Or.inl h1)).trans (h.cyc_B (Or.inr (Or.inl ⟨x, h2⟩))))

/-- `p —SO→ q —RW→ p` is impossible. -/
theorem F3 {p q : C.Tid} {x : Obj} (h1 : (C.graph WR WW).SO p q)
    (h2 : (C.graph WR WW).RW x q p) : False :=
  h.acyc p (h.cyc_BR (Or.inl h1) ⟨x, h2⟩)

/-- `c —SO→ a —RW→ b —WR→ c` is impossible. -/
theorem F4 {a b c : C.Tid} {x y : Obj} (h1 : (C.graph WR WW).SO c a)
    (h2 : (C.graph WR WW).RW x a b) (h3 : WR y b c) : False :=
  h.acyc c ((h.cyc_BR (Or.inl h1) ⟨x, h2⟩).trans (h.cyc_B (Or.inr (Or.inl ⟨y, h3⟩))))

theorem writeTx_of_wr {p q : C.Tid} {x : Obj} (hpq : WR x p q) :
    (C.graph WR WW).WriteTx x p := by
  obtain ⟨n, -, hw, -⟩ := h.dg.wr_val p q x hpq
  exact ⟨n, hw⟩

theorem readsObj_of_wr {p q : C.Tid} {x : Obj} (hpq : WR x p q) :
    (C.graph WR WW).ReadsObj x q := by
  obtain ⟨n, -, -, hr⟩ := h.dg.wr_val p q x hpq
  exact ⟨n, hr⟩

theorem ne_of_wr {p q : C.Tid} {x : Obj} (hpq : WR x p q) : p ≠ q :=
  (h.dg.wr_val p q x hpq).choose_spec.1

/-- No later transaction of the session of a `WR`-source writes the same object
(proof of Lemma 26, first bullet, (i)). -/
theorem no_later_writer {p q p' : C.Tid} {x : Obj} (hpq : WR x p q) (hs : p.1.1 ≠ q.1.1)
    (hpp' : (C.graph WR WW).SO p p') (hw : (C.graph WR WW).WriteTx x p') : False := by
  have hne : p ≠ p' := ne_of_so hpp'
  rcases h.dg.ww_total x p p' (h.writeTx_of_wr hpq) hw hne with h' | h'
  · have hrw : (C.graph WR WW).RW x q p' :=
      ⟨ne_of_sess_ne (by rw [← hpp'.1]; exact hs.symm), p, hpq, h'⟩
    exact h.no_crit3 (l₁ := .wr) (l₂ := .rw) (l₃ := .pred) ⟨⟨x, hpq⟩, hs⟩
      ⟨⟨x, hrw⟩, by rw [← hpp'.1]; exact hs.symm⟩ hpp' (ne_of_sess_ne hs)
      (ne_of_sess_ne (by rw [← hpp'.1]; exact hs.symm)) hne.symm
      ⟨1, .rw, .wr, [], rfl, trivial, trivial⟩ (by decide)
  · exact h.F1 hpp' h'

/-- No earlier transaction of the session of a `WR`-target writes the same object
(proof of Lemma 26, first bullet, (ii)). -/
theorem no_earlier_writer {p q q' : C.Tid} {x : Obj} (hpq : WR x p q) (hs : p.1.1 ≠ q.1.1)
    (hq'q : (C.graph WR WW).SO q' q) (hw : (C.graph WR WW).WriteTx x q') : False := by
  have hs' : p.1.1 ≠ q'.1.1 := by rw [hq'q.1]; exact hs
  rcases h.dg.ww_total x p q' (h.writeTx_of_wr hpq) hw (ne_of_sess_ne hs') with h' | h'
  · exact h.F3 hq'q ⟨(ne_of_so hq'q).symm, p, hpq, h'⟩
  · exact h.no_crit3 (l₁ := .ww) (l₂ := .wr) (l₃ := .pred) ⟨⟨x, h'⟩, hs'.symm⟩
      ⟨⟨x, hpq⟩, hs⟩ hq'q (ne_of_sess_ne hs'.symm) (ne_of_sess_ne hs) (ne_of_so hq'q).symm
      ⟨1, .wr, .ww, [], rfl, trivial, trivial⟩ (by decide)

/-- If `p —WR(x)→ q`, `q' —SO→ q` and `p' —WR(x)→ q'`, then `p —WW(x)→ p'` is impossible. -/
theorem no_ww_of_wr_wr {p q p' q' : C.Tid} {x : Obj} (hpq : WR x p q)
    (hq'q : (C.graph WR WW).SO q' q) (hp'q' : WR x p' q') (hww : WW x p p') : False := by
  by_cases hp'q : p' = q
  · subst hp'q
    exact h.F2 hq'q hp'q'
  · exact h.F4 hq'q ⟨Ne.symm hp'q, p, hpq, hww⟩ hp'q'

/-- If `p —WR(x)→ q` with `p` in another session, `q' —SO→ q` and `p' —WR(x)→ q'`, then
`p = p'` (proof of Lemma 26, first bullet (ii) and third bullet). -/
theorem wr_src_eq {p q p' q' : C.Tid} {x : Obj} (hpq : WR x p q) (hs : p.1.1 ≠ q.1.1)
    (hq'q : (C.graph WR WW).SO q' q) (hp'q' : WR x p' q') : p = p' := by
  by_contra hne
  rcases h.dg.ww_total x p p' (h.writeTx_of_wr hpq) (h.writeTx_of_wr hp'q') hne with h' | h'
  · exact h.no_ww_of_wr_wr hpq hq'q hp'q' h'
  · have hs' : q'.1.1 ≠ p.1.1 := by rw [hq'q.1]; exact hs.symm
    have hrw : (C.graph WR WW).RW x q' p := ⟨ne_of_sess_ne hs', p', hp'q', h'⟩
    exact h.no_crit3 (l₁ := .rw) (l₂ := .wr) (l₃ := .pred) ⟨⟨x, hrw⟩, hs'⟩ ⟨⟨x, hpq⟩, hs⟩
      hq'q (ne_of_sess_ne hs') (ne_of_sess_ne hs) (ne_of_so hq'q).symm
      ⟨1, .wr, .rw, [], rfl, trivial, trivial⟩ (by decide)

end GraphSI

end Hyp

/-! ### Lemma 26: `splice(G)` is a dependency graph -/

/-- A session containing a writer of `x` writes `x` when spliced. -/
theorem exists_writes_flatten {s : ι} {x : Obj} {j : ℕ} (hj : j < (C.sess s).length) {m : V}
    (hw : ((C.sess s)[j]).Writes x m) : ∃ n, Txn.Writes (C.sess s).flatten x n := by
  classical
  let P : ℕ → Prop := fun k => ∃ hk : k < (C.sess s).length, ∃ n, ((C.sess s)[k]).Writes x n
  obtain ⟨hk, n, hn⟩ := Nat.findGreatest_spec (P := P) hj.le ⟨hj, m, hw⟩
  refine ⟨n, (Txn.writes_flatten_iff _).2 ⟨_, hk, hn, fun j' hj' hkj' m' hm' => ?_⟩⟩
  exact Nat.findGreatest_is_greatest hkj' hj'.le ⟨hj', m', hm'⟩

namespace Hyp

variable (h : Hyp C WR WW)
include h

/-- Lemma 26, first bullet. -/
theorem splice_wr_val {s t : ι} {x : Obj} (hst : liftRel WR x s t) :
    ∃ n, s ≠ t ∧ Txn.Writes (C.sess s).flatten x n ∧ Txn.Reads (C.sess t).flatten x n := by
  obtain ⟨hne, p, q, rfl, rfl, hpq⟩ := hst
  obtain ⟨n, -, hw, hr⟩ := h.dg.wr_val p q x hpq
  refine ⟨n, hne, ?_, ?_⟩
  · refine (Txn.writes_flatten_iff _).2 ⟨p.1.2, p.2, hw, fun j' hj' hlt m hm => ?_⟩
    exact h.no_later_writer hpq hne (p' := C.tid p.1.1 j' hj') ⟨rfl, hlt⟩ ⟨m, hm⟩
  · classical
    obtain ⟨⟨t, k⟩, hk⟩ := q
    let P : ℕ → Prop := fun j => ∃ hj : j < (C.sess t).length, ((C.sess t)[j]).Accesses x
    have hPk : P k := ⟨hk, Txn.Reads.accesses hr⟩
    have hex : ∃ j, P j := ⟨k, hPk⟩
    obtain ⟨⟨hj, hacc⟩, hmin⟩ : P (Nat.find hex) ∧ ∀ j' < Nat.find hex, ¬ P j' :=
      ⟨Nat.find_spec hex, fun j' => Nat.find_min hex⟩
    set j := Nat.find hex
    have hjk : j ≤ k := Nat.find_min' hex hPk
    refine (Txn.reads_flatten_iff _).2 ⟨j, hj, ?_, fun j' hj' hacc' => hmin j' hj' ⟨_, hacc'⟩⟩
    rcases hjk.lt_or_eq with hlt | heq
    · have hq'q : (C.graph WR WW).SO (C.tid t j hj) ⟨(t, k), hk⟩ := ⟨rfl, hlt⟩
      have hnw : ∀ m, ¬ ((C.sess t)[j]).Writes x m := fun m hm =>
        h.no_earlier_writer hpq hne hq'q ⟨m, hm⟩
      obtain ⟨m, hm⟩ := Txn.exists_reads_of_accesses hacc hnw
      obtain ⟨p', hp'q'⟩ := h.dg.wr_exists (C.tid t j hj) x ⟨m, hm⟩
      have hpp' := h.wr_src_eq hpq hne hq'q hp'q'
      subst hpp'
      obtain ⟨n', -, hw', hr'⟩ := h.dg.wr_val p (C.tid t j hj) x hp'q'
      have e1 : n' = m := Txn.Reads.unique hr' hm
      have e2 : n = n' := Txn.Writes.unique hw hw'
      subst e1 e2
      exact hm
    · subst heq
      exact hr

/-- Lemma 26, second bullet. -/
theorem splice_wr_exists {t : ι} {x : Obj} {n : V} (hr : Txn.Reads (C.sess t).flatten x n) :
    ∃ s, liftRel WR x s t := by
  obtain ⟨j, hj, hrj, hmin⟩ := (Txn.reads_flatten_iff _).1 hr
  obtain ⟨p, hpq⟩ := h.dg.wr_exists (C.tid t j hj) x ⟨n, hrj⟩
  by_cases hs : p.1.1 = t
  · exfalso
    obtain ⟨⟨s', i⟩, hi⟩ := p
    simp only at hs
    subst hs
    rcases tid_trich (WR := WR) (WW := WW) (p := ⟨(s', i), hi⟩) (q := C.tid s' j hj) rfl with
      e | hso | hso
    · exact h.ne_of_wr hpq e
    · obtain ⟨m, hm⟩ := h.writeTx_of_wr hpq
      exact hmin i hso.2 (Txn.Writes.accesses hm)
    · exact h.F2 hso hpq
  · exact ⟨p.1.1, hs, p, _, rfl, rfl, hpq⟩

/-- Lemma 26, third bullet. -/
theorem splice_wr_unique {s s' t : ι} {x : Obj} (h1 : liftRel WR x s t)
    (h2 : liftRel WR x s' t) : s = s' := by
  obtain ⟨hne, p, q, rfl, rfl, hpq⟩ := h1
  obtain ⟨hne', p', q', rfl, hq', hp'q'⟩ := h2
  rcases tid_trich (WR := WR) (WW := WW) (p := q) (q := q') hq'.symm with e | hso | hso
  · subst e
    rw [h.dg.wr_unique p p' q x hpq hp'q']
  · have hs' : p'.1.1 ≠ q'.1.1 := by rw [hq']; exact hne'
    rw [h.wr_src_eq hp'q' hs' hso hpq]
  · rw [h.wr_src_eq hpq hne hso hp'q']

/-- Lemma 26, fourth bullet: `WW_{splice(G)}` is transitive. -/
theorem splice_ww_trans {s u t : ι} {x : Obj} (h1 : liftRel WW x s u) (h2 : liftRel WW x u t) :
    liftRel WW x s t := by
  obtain ⟨hsu, p, v', rfl, rfl, hpv⟩ := h1
  obtain ⟨hut, v'', q, hv'', rfl, hvq⟩ := h2
  have wv' := (h.dg.ww_writeTx x p v' hpv).2
  have wv'' := (h.dg.ww_writeTx x v'' q hvq).1
  have hs1 : p.1.1 ≠ v''.1.1 := by rw [hv'']; exact hsu
  have hs2 : v''.1.1 ≠ q.1.1 := by rw [hv'']; exact hut
  have key : v' = v'' ∨ ((C.graph WR WW).SO v' v'' ∧ WW x v' v'') ∨
      ((C.graph WR WW).SO v'' v' ∧ WW x v'' v') := by
    rcases tid_trich (WR := WR) (WW := WW) (p := v') (q := v'') hv''.symm with e | so | so
    · exact Or.inl e
    · refine Or.inr (Or.inl ⟨so, ?_⟩)
      rcases h.dg.ww_total x v' v'' wv' wv'' (ne_of_so so) with h' | h'
      · exact h'
      · exact (h.F1 so h').elim
    · refine Or.inr (Or.inr ⟨so, ?_⟩)
      rcases h.dg.ww_total x v'' v' wv'' wv' (ne_of_so so) with h' | h'
      · exact h'
      · exact (h.F1 so h').elim
  have hst : p.1.1 ≠ q.1.1 := by
    intro hst
    rcases key with e | ⟨so, hvv⟩ | ⟨so, hvv⟩
    · subst e
      have hpq : WW x p q := h.dg.ww_trans x p v' q hpv hvq
      rcases tid_trich (WR := WR) (WW := WW) (p := p) (q := q) hst with e | so' | so'
      · subst e; exact h.dg.ww_irrefl x p hpq
      · exact h.no_crit3 (l₁ := .ww) (l₂ := .ww) (l₃ := .pred) ⟨⟨x, hpv⟩, hsu⟩ ⟨⟨x, hvq⟩, hut⟩
          so' (ne_of_sess_ne hsu) (ne_of_sess_ne hut) (ne_of_so so').symm
          ⟨1, .ww, .ww, [], rfl, trivial, trivial⟩ (by decide)
      · exact h.F1 so' hpq
    · have hpq : WW x p q := h.dg.ww_trans x p v' q hpv (h.dg.ww_trans x v' v'' q hvv hvq)
      rcases tid_trich (WR := WR) (WW := WW) (p := p) (q := q) hst with e | so' | so'
      · subst e; exact h.dg.ww_irrefl x p hpq
      · exact h.no_crit4 (l₁ := .ww) (l₂ := .succ) (l₃ := .ww) (l₄ := .pred) ⟨⟨x, hpv⟩, hsu⟩
          so ⟨⟨x, hvq⟩, hs2⟩ so' (ne_of_sess_ne hsu) (ne_of_sess_ne hs1) (ne_of_so so')
          (ne_of_so so) (ne_of_sess_ne hut) (ne_of_sess_ne hs2)
          ⟨2, .ww, .ww, [.succ], rfl, trivial, trivial⟩ (by decide)
      · exact h.F1 so' hpq
    · rcases tid_trich (WR := WR) (WW := WW) (p := p) (q := q) hst with e | so' | so'
      · subst e
        exact h.no_crit3 (l₁ := .ww) (l₂ := .pred) (l₃ := .ww) ⟨⟨x, hpv⟩, hsu⟩ so
          ⟨⟨x, hvq⟩, hs2⟩ (ne_of_sess_ne hsu) (ne_of_so so).symm (ne_of_sess_ne hs1).symm
          ⟨0, .ww, .ww, [], rfl, trivial, trivial⟩ (by decide)
      · exact h.no_crit4 (l₁ := .ww) (l₂ := .pred) (l₃ := .ww) (l₄ := .pred) ⟨⟨x, hpv⟩, hsu⟩
          so ⟨⟨x, hvq⟩, hs2⟩ so' (ne_of_sess_ne hsu) (ne_of_sess_ne hs1) (ne_of_so so')
          (ne_of_so so).symm (ne_of_sess_ne hut) (ne_of_sess_ne hs2)
          ⟨0, .ww, .ww, [.pred], rfl, trivial, trivial⟩ (by decide)
      · exact h.no_crit4 (l₁ := .ww) (l₂ := .pred) (l₃ := .ww) (l₄ := .succ) ⟨⟨x, hpv⟩, hsu⟩
          so ⟨⟨x, hvq⟩, hs2⟩ so' (ne_of_sess_ne hsu) (ne_of_sess_ne hs1) (ne_of_so so').symm
          (ne_of_so so).symm (ne_of_sess_ne hut) (ne_of_sess_ne hs2)
          ⟨0, .ww, .ww, [.succ], rfl, trivial, trivial⟩ (by decide)
  refine ⟨hst, p, q, rfl, rfl, ?_⟩
  rcases key with e | ⟨so, hvv⟩ | ⟨so, hvv⟩
  · subst e; exact h.dg.ww_trans x p v' q hpv hvq
  · exact h.dg.ww_trans x p v' q hpv (h.dg.ww_trans x v' v'' q hvv hvq)
  · rcases h.dg.ww_total x p q (h.dg.ww_writeTx x p v' hpv).1 (h.dg.ww_writeTx x v'' q hvq).2
      (ne_of_sess_ne hst) with h' | h'
    · exact h'
    · exact (h.no_crit4 (l₁ := .ww) (l₂ := .pred) (l₃ := .ww) (l₄ := .ww) ⟨⟨x, hpv⟩, hsu⟩
        so ⟨⟨x, hvq⟩, hs2⟩ ⟨⟨x, h'⟩, Ne.symm hst⟩ (ne_of_sess_ne hsu) (ne_of_sess_ne hs1)
        (ne_of_sess_ne hst) (ne_of_so so).symm (ne_of_sess_ne hut) (ne_of_sess_ne hs2)
        ⟨0, .ww, .ww, [.ww], rfl, trivial, trivial⟩ (by decide)).elim

/-- **Lemma 26** of Cerone–Gotsman: if `G ∈ GraphSI` and `DCG(G)` has no critical cycle, then
`splice(G)` is a dependency graph. -/
theorem lemma26 : (C.spliceGraph WR WW).IsDepGraph where
  wr_val T S x hTS := h.splice_wr_val hTS
  wr_exists S x := by
    rintro ⟨n, hn⟩
    exact h.splice_wr_exists hn
  wr_unique T T' S x h1 h2 := h.splice_wr_unique h1 h2
  ww_writeTx x T S hTS := by
    obtain ⟨-, p, q, rfl, rfl, hpq⟩ := hTS
    obtain ⟨⟨m, hm⟩, ⟨m', hm'⟩⟩ := h.dg.ww_writeTx x p q hpq
    exact ⟨exists_writes_flatten p.2 hm, exists_writes_flatten q.2 hm'⟩
  ww_trans x T S U h1 h2 := h.splice_ww_trans h1 h2
  ww_irrefl x T hT := hT.1 rfl
  ww_total x T S hT hS hne := by
    obtain ⟨n, hn⟩ := hT
    obtain ⟨m, hm⟩ := hS
    obtain ⟨j, hj, hjw, -⟩ := (Txn.writes_flatten_iff _).1 hn
    obtain ⟨k, hk, hkw, -⟩ := (Txn.writes_flatten_iff _).1 hm
    rcases h.dg.ww_total x (C.tid T j hj) (C.tid S k hk) ⟨n, hjw⟩ ⟨m, hkw⟩
      (ne_of_sess_ne hne) with h' | h'
    · exact Or.inl ⟨hne, _, _, rfl, rfl, h'⟩
    · exact Or.inr ⟨Ne.symm hne, _, _, rfl, rfl, h'⟩

/-- **Lemma 27** of Cerone–Gotsman: if `G ∈ GraphSI` and `DCG(G)` has no critical cycle, then
`𝒯_{splice(G)} ⊨ INT`. -/
theorem lemma27 : (C.spliceGraph WR WW).IntAll := by
  intro s
  refine Txn.int_flatten _ (fun j hj => h.int (C.tid s j hj)) ?_
  intro j hj x n hr j' hj' hacc hbetween
  have hj'' : j' < (C.sess s).length := by omega
  set q := C.tid s j hj
  set q' := C.tid s j' hj''
  have hq'q : (C.graph WR WW).SO q' q := ⟨rfl, hj'⟩
  obtain ⟨p, hpq⟩ := h.dg.wr_exists q x ⟨n, hr⟩
  obtain ⟨n0, -, hpw, hpr⟩ := h.dg.wr_val p q x hpq
  have e0 : n0 = n := Txn.Reads.unique hpr hr
  subst e0
  -- a writer of `x` in the session cannot lie strictly between `q'` and `q`
  have hbtw : ∀ r : C.Tid, r.1.1 = s → (C.graph WR WW).SO q' r → (C.graph WR WW).SO r q →
      (C.graph WR WW).WriteTx x r → False := by
    rintro ⟨⟨s', i⟩, hi⟩ hrs h1 h2 ⟨m, hm⟩
    simp only at hrs
    subst hrs
    exact hbetween i h1.2 h2.2 (Txn.Writes.accesses hm)
  have hps_cases : p.1.1 = s → (C.graph WR WW).SO p q' ∨
      ((C.graph WR WW).SO q' p ∧ False) ∨ p = q' := by
    intro hps
    rcases tid_trich (WR := WR) (WW := WW) (p := p) (q := q') hps with e | so | so
    · exact Or.inr (Or.inr e)
    · exact Or.inl so
    · exfalso
      rcases tid_trich (WR := WR) (WW := WW) (p := p) (q := q) hps with e | so2 | so2
      · exact h.ne_of_wr hpq e
      · exact hbtw p hps so so2 (h.writeTx_of_wr hpq)
      · exact h.F2 so2 hpq
  by_cases hw : ∃ m, ((C.sess s)[j']).Writes x m
  · obtain ⟨m, hm⟩ := hw
    rw [show ((C.sess s)[j']).finalVal x = some m from Txn.Int.finalVal_of_writes (h.int q') hm]
    by_cases hpq' : p = q'
    · subst hpq'
      rw [Txn.Writes.unique hm hpw]
    have hs : p.1.1 ≠ s := by
      intro hps
      rcases hps_cases hps with so | ⟨-, hf⟩ | e
      · rcases h.dg.ww_total x p q' (h.writeTx_of_wr hpq) ⟨m, hm⟩ hpq' with h' | h'
        · exact h.F3 hq'q ⟨(ne_of_so hq'q).symm, p, hpq, h'⟩
        · exact h.F1 so h'
      · exact hf
      · exact hpq' e
    exact (h.no_earlier_writer hpq hs hq'q ⟨m, hm⟩).elim
  · push Not at hw
    obtain ⟨m, hm⟩ := Txn.exists_reads_of_accesses hacc hw
    rw [show ((C.sess s)[j']).finalVal x = some m from
      Txn.Int.finalVal_of_reads (h.int q') hm hw]
    obtain ⟨p', hp'q'⟩ := h.dg.wr_exists q' x ⟨m, hm⟩
    obtain ⟨m', -, hp'w, hp'r⟩ := h.dg.wr_val p' q' x hp'q'
    have e1 : m' = m := Txn.Reads.unique hp'r hm
    subst e1
    by_cases hpp : p = p'
    · subst hpp
      rw [Txn.Writes.unique hpw hp'w]
    exfalso
    rcases h.dg.ww_total x p p' (h.writeTx_of_wr hpq) ⟨m', hp'w⟩ hpp with h' | h'
    · exact h.no_ww_of_wr_wr hpq hq'q hp'q' h'
    · have hq'p : q' ≠ p := by
        rintro e
        exact hw n0 (by rw [show (C.sess s)[j'] = (C.graph WR WW).txn p from by rw [← e]; rfl]
                        exact hpw)
      have hrw : (C.graph WR WW).RW x q' p := ⟨hq'p, p', hp'q', h'⟩
      by_cases hps : p.1.1 = s
      · rcases hps_cases hps with so | ⟨-, hf⟩ | e
        · exact h.F3 so hrw
        · exact hf
        · exact hq'p e.symm
      · have hs' : q'.1.1 ≠ p.1.1 := Ne.symm hps
        exact h.no_crit3 (l₁ := .rw) (l₂ := .wr) (l₃ := .pred) ⟨⟨x, hrw⟩, hs'⟩
          ⟨⟨x, hpq⟩, hps⟩ hq'q hq'p (ne_of_sess_ne hps) (ne_of_so hq'q).symm
          ⟨1, .wr, .rw, [], rfl, trivial, trivial⟩ (by decide)

/-- **Lemma 17** of Cerone–Gotsman: if `G ∈ GraphSI` and `DCG(G)` has no critical cycle, then
every anti-dependency `T^G —RW_{splice(G)}(x)→ S^G` comes from an anti-dependency
`T' —RW_G(x)→ S'` with `T' ≈ T`, `S' ≈ S`. -/
theorem lemma17 {s t : ι} {x : Obj} (hst : (C.spliceGraph WR WW).RW x s t) :
    s ≠ t ∧ ∃ p q : C.Tid, p.1.1 = s ∧ q.1.1 = t ∧ (C.graph WR WW).RW x p q := by
  obtain ⟨hst, u, ⟨hus, v', p, rfl, rfl, hv'p⟩, ⟨hut, v'', q, hv'', rfl, hv''q⟩⟩ := hst
  refine ⟨hst, p, q, rfl, rfl, ne_of_sess_ne hst, v', hv'p, ?_⟩
  have wv' := h.writeTx_of_wr hv'p
  have wv'' := (h.dg.ww_writeTx x v'' q hv''q).1
  have wq := (h.dg.ww_writeTx x v'' q hv''q).2
  have hs2 : v''.1.1 ≠ q.1.1 := by rw [hv'']; exact hut
  rcases tid_trich (WR := WR) (WW := WW) (p := v') (q := v'') hv''.symm with e | so | so
  · subst e; exact hv''q
  · rcases h.dg.ww_total x v' v'' wv' wv'' (ne_of_so so) with h' | h'
    · exact h.dg.ww_trans x v' v'' q h' hv''q
    · exact (h.F1 so h').elim
  · rcases h.dg.ww_total x v' q wv' wq (ne_of_sess_ne hut) with h' | h'
    · exact h'
    · exact (h.no_crit3 (l₁ := .ww) (l₂ := .pred) (l₃ := .ww) ⟨⟨x, h'⟩, Ne.symm hut⟩ so
        ⟨⟨x, hv''q⟩, hs2⟩ (ne_of_sess_ne hut).symm (ne_of_so so).symm (ne_of_sess_ne hs2)
        ⟨0, .ww, .ww, [], rfl, trivial, trivial⟩ (by decide)).elim

end Hyp

end Chopped

end Podc.AnalysingSI
