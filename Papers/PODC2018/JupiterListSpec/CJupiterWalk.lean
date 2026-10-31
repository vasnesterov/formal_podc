import Papers.PODC2018.JupiterListSpec.CJupiterLoop
import Papers.PODC2018.JupiterListSpec.JupiterInv

/-!
# One `xForm` of CJupiter, generically

`walk`: let `Q` be the vertex reached by a replica (all the operations it processed) and assume its
state space is *sound* (every edge is labelled by the global transformation, `CEOK`) and
*complete* (from every vertex `u ⊊ Q` there is an edge labelled with the `≺s`-first operation
of `Q \ u`, `Comp`), and that `Compare` agrees with `≺s` on the labels (`CmpOK`). Then `xForm`
of a new operation `j` follows the `≺s`-ordered path from `ctx j` to `Q` (this is Lemma 5,
"CJupiter's First Rule", and Lemma 7), returns `T j Q`, and leaves a sound and complete state
space for `Q ∪ {j}` (the core of Proposition 9).
-/

namespace Podc.JupiterListSpec

variable {n : ℕ}

namespace CJup

open Cfg

variable {S : Sched (Oid n)}

/-- Soundness of an edge of a CJupiter state space whose server contexts are given by `σ`. -/
structure CEOK (S : Sched (Oid n)) (σ : Oid n → Finset (Oid n)) (Q : Finset (Oid n))
    (e : COp n) : Prop where
  eq : e = ⟨S.T e.oid e.ctx, e.oid, e.ctx, σ e.oid⟩
  notMem : e.oid ∉ e.ctx
  sub : insert e.oid e.ctx ⊆ Q
  cl : S.ctx e.oid ⊆ e.ctx

theorem CEOK.mono {σ : Oid n → Finset (Oid n)} {Q Q' : Finset (Oid n)} {e : COp n}
    (h : CEOK S σ Q e) (hQ : Q ⊆ Q') : CEOK S σ Q' e :=
  ⟨h.eq, h.notMem, h.sub.trans hQ, h.cl⟩

theorem CEOK.congr {σ σ' : Oid n → Finset (Oid n)} {Q : Finset (Oid n)} {e : COp n}
    (h : CEOK S σ Q e) (hσ : ∀ y ∈ Q, σ y = σ' y) : CEOK S σ' Q e := by
  refine ⟨?_, h.notMem, h.sub, h.cl⟩
  rw [← hσ e.oid (h.sub (Finset.mem_insert_self _ _))]; exact h.eq

/-- Completeness: from every vertex `u ⊊ Q` there is an edge labelled with the `≺s`-first
operation of `Q \ u`. -/
def Comp (S : Sched (Oid n)) (Q : Finset (Oid n)) (E : List (COp n)) : Prop :=
  ∀ u, S.Vert u → u ⊆ Q → u ≠ Q →
    ∃ e ∈ E, e.ctx = u ∧ e.oid ∈ Q ∧ e.oid ∉ u ∧ ∀ y ∈ Q, y ∉ u → S.rank e.oid ≤ S.rank y

/-- `Compare` agrees with `≺s` on edges from a common vertex. -/
def CmpOK (S : Sched (Oid n)) (r : Option (Fin n)) (σ : Oid n → Finset (Oid n))
    (Q : Finset (Oid n)) : Prop :=
  ∀ (l y : Oid n) (u : Finset (Oid n)) (o₁ o₂ : LOp (Oid n)), l ∈ Q → y ∈ Q → l ∉ u → y ∉ u →
    S.ctx y ⊆ u → S.rank l < S.rank y →
    cmp r ⟨o₁, l, u, σ l⟩ ⟨o₂, y, u, σ y⟩ = true ∧ cmp r ⟨o₂, y, u, σ y⟩ ⟨o₁, l, u, σ l⟩ = false

/-- `firstEdge` returns the edge that is `Compare`-smaller than all other edges from `u`. -/
theorem firstEdge_eq {r : Option (Fin n)} {E : List (COp n)} {u : Finset (Oid n)} {e0 : COp n}
    (he0 : e0 ∈ E) (hctx : e0.ctx = u)
    (hcmp : ∀ e ∈ E, e.ctx = u → e.oid ≠ e0.oid → cmp r e0 e = true ∧ cmp r e e0 = false)
    (huniq : ∀ e ∈ E, e.ctx = u → e.oid = e0.oid → e = e0) :
    firstEdge r E u = some e0 := by
  unfold firstEdge
  simp only
  set Eu := E.filter fun e => decide (e.ctx = u) with hEu
  have hmemEu : ∀ e, e ∈ Eu ↔ e ∈ E ∧ e.ctx = u := by intro e; simp [hEu]
  have hp0 : (Eu.all fun e' => e'.oid == e0.oid || cmp r e0 e') = true := by
    rw [List.all_eq_true]
    intro e' he'
    obtain ⟨he', hc⟩ := (hmemEu e').1 he'
    by_cases ho : e'.oid = e0.oid
    · simp [ho]
    · simp [(hcmp e' he' hc ho).1]
  cases hf : Eu.find? (fun e => Eu.all fun e' => e'.oid == e.oid || cmp r e e') with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd hp0 (hf e0 ((hmemEu e0).2 ⟨he0, hctx⟩))
  | some e =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    obtain ⟨heE, hec⟩ := (hmemEu e).1 hm
    by_cases ho : e.oid = e0.oid
    · rw [huniq e heE hec ho]
    · rw [List.all_eq_true] at hp
      have := hp e0 ((hmemEu e0).2 ⟨he0, hctx⟩)
      simp [Ne.symm ho, (hcmp e heE hec ho).2] at this

/-- Every finite set has a duplicate-free `≺s`-sorted enumeration. -/
theorem exists_sorted (D : Set (Oid n)) (hinj : Set.InjOn S.rank D) :
    ∀ (A : Finset (Oid n)), ↑A ⊆ D → ∃ l : List (Oid n), l.Nodup ∧ (∀ y, y ∈ l ↔ y ∈ A) ∧
      l.Pairwise fun a b => S.rank a < S.rank b := by
  intro A
  induction hk : A.card generalizing A with
  | zero =>
    intro _
    rw [Finset.card_eq_zero] at hk; subst hk
    exact ⟨[], by simp, by simp, by simp⟩
  | succ k ih =>
    intro hAD
    have hne : A.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨m, hm, hmax⟩ := A.exists_max_image S.rank hne
    obtain ⟨l, hnd, hmem, hsort⟩ := ih (A.erase m) (by rw [Finset.card_erase_of_mem hm]; omega)
      (fun y hy => hAD (Finset.mem_of_mem_erase hy))
    refine ⟨l ++ [m], ?_, fun y => ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      simp only [List.mem_singleton]
      rintro a ha b rfl rfl
      exact (Finset.notMem_erase a A) ((hmem a).1 ha)
    · rw [List.mem_append, hmem, List.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨-, h⟩ | rfl)
        · exact h
        · exact hm
      · intro hy
        by_cases hym : y = m
        · exact Or.inr hym
        · exact Or.inl ⟨hym, hy⟩
    · rw [List.pairwise_append]
      refine ⟨hsort, by simp, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb; subst hb
      have haA := Finset.mem_erase.1 ((hmem a).1 ha)
      rcases (hmax a haA.2).lt_or_eq with h | h
      · exact h
      · exact absurd (hinj (hAD haA.2) (hAD hm) h) haA.1

/-- A downward closed part of a list is a prefix. -/
theorem exists_prefix {α : Type} : ∀ (path : List α) (A : α → Prop),
    (∀ z y, [z, y].Sublist path → A y → A z) →
    ∃ pre rest, path = pre ++ rest ∧ (∀ x ∈ pre, A x) ∧ ∀ x ∈ rest, ¬ A x
  | [], _, _ => ⟨[], [], rfl, by simp, by simp⟩
  | a :: t, A, hdc => by
    by_cases ha : A a
    · obtain ⟨pre, rest, hp, h1, h2⟩ := exists_prefix t A
        (fun z y hzy hy => hdc z y (hzy.cons a) hy)
      refine ⟨a :: pre, rest, by simp [hp], ?_, h2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact h1 x hx
    · refine ⟨[], a :: t, rfl, by simp, ?_⟩
      intro x hx hAx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha hAx
      · exact ha (hdc a x (List.cons_sublist_cons.2 (List.singleton_sublist.2 hx)) hAx)

/-- One `xForm` of CJupiter at a sound and complete state space (Lemmas 5 and 7,
Proposition 9). -/
theorem walk {P' : Proto n} {cfg : Cfg P'} (h : GI S cfg) {r : Option (Fin n)}
    {σ : Oid n → Finset (Oid n)} {Q : Finset (Oid n)} {E : List (COp n)} {j : Oid n}
    (hQ : S.Vert Q) (hQD : ↑Q ⊆ (↑cfg.D : Set (Oid n))) (hjD : j ∈ cfg.D) (hjQ : j ∉ Q)
    (hC : S.ctx j ⊆ Q)
    (hhigh : ∀ y ∈ Q, ∀ z ∈ Q, S.rank j < S.rank z → S.rank z < S.rank y → z ∈ S.ctx y)
    (hcl : ∀ y ∈ Q, S.cl y = S.cl j → S.rank y < S.rank j)
    (hE : ∀ e ∈ E, CEOK S σ Q e) (hcomp : Comp S Q E) (hcmp : CmpOK S r σ Q) :
    ∃ Ef, cxForm r ⟨E, Q⟩ (opE S j (σ j) (S.ctx j)) =
        some (⟨Ef, insert j Q⟩, opE S j (σ j) Q) ∧
      (∀ e ∈ Ef, CEOK S σ (insert j Q) e) ∧ Comp S (insert j Q) Ef := by
  set C := S.ctx j with hCdef
  have hW := h.wf
  have hinjQ : ∀ a ∈ Q, ∀ b ∈ Q, S.rank a = S.rank b → a = b := fun a ha b hb e =>
    hW.inj (hQD ha) (hQD hb) e
  obtain ⟨path, hnd, hmem, hsort⟩ := exists_sorted (S := S) _ hW.inj (Q \ C)
    (fun y hy => hQD (Finset.mem_sdiff.1 hy).1)
  have hpathQ : ∀ y, y ∈ path ↔ y ∈ Q ∧ y ∉ C := fun y => by rw [hmem, Finset.mem_sdiff]
  have hcur : C ∪ path.toFinset = Q := by
    ext y
    rw [Finset.mem_union, List.mem_toFinset, hpathQ]
    constructor
    · rintro (hy | hy)
      · exact hC hy
      · exact hy.1
    · intro hy; by_cases hyC : y ∈ C
      · exact Or.inl hyC
      · exact Or.inr ⟨hy, hyC⟩
  have hdisj : ∀ l ∈ path, l ∉ C := fun l hl => ((hpathQ l).1 hl).2
  have hlen : path.length ≤ Q.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact Finset.card_le_card fun y hy => ((hpathQ y).1 (List.mem_toFinset.1 hy)).1
  have hpre : ∀ pre l rest, path = pre ++ l :: rest → ∀ y,
      y ∈ C ∪ pre.toFinset ↔ y ∈ Q ∧ (y ∈ C ∨ S.rank y < S.rank l) := by
    intro pre l rest hp y
    rw [Finset.mem_union, List.mem_toFinset, Jup.mem_pre_iff hsort hp]
    constructor
    · rintro (hy | ⟨hy, hyl⟩)
      · exact ⟨hC hy, Or.inl hy⟩
      · exact ⟨((hpathQ y).1 hy).1, Or.inr hyl⟩
    · rintro ⟨hy, hyC | hyl⟩
      · exact Or.inl hyC
      · by_cases hyC : y ∈ C
        · exact Or.inl hyC
        · exact Or.inr ⟨(hpathQ y).2 ⟨hy, hyC⟩, hyl⟩
  have hlmem : ∀ pre l rest, path = pre ++ l :: rest → l ∈ Q ∧ l ∉ C := fun pre l rest hp =>
    (hpathQ l).1 (by rw [hp]; simp)
  have hlU : ∀ pre l rest, path = pre ++ l :: rest → l ∉ C ∪ pre.toFinset := by
    intro pre l rest hp hl
    rcases ((hpre pre l rest hp l).1 hl).2 with h1 | h1
    · exact (hlmem pre l rest hp).2 h1
    · exact lt_irrefl _ h1
  have hmin : ∀ pre l rest, path = pre ++ l :: rest → ∀ y ∈ Q, y ∉ C ∪ pre.toFinset →
      S.rank l ≤ S.rank y := by
    intro pre l rest hp y hy hyU
    by_contra hlt
    push_neg at hlt
    exact hyU ((hpre pre l rest hp y).2 ⟨hy, Or.inr hlt⟩)
  have hUsub : ∀ pre l rest, path = pre ++ l :: rest → C ∪ pre.toFinset ⊆ Q :=
    fun pre l rest hp y hy => ((hpre pre l rest hp y).1 hy).1
  have hUvert : ∀ pre l rest, path = pre ++ l :: rest → S.Vert (C ∪ pre.toFinset) := by
    intro pre l rest hp
    obtain ⟨hlQ, hlC⟩ := hlmem pre l rest hp
    refine ⟨fun y hy z hz => ?_, ?_⟩
    · obtain ⟨hyQ, hyC | hyl⟩ := (hpre pre l rest hp y).1 hy
      · exact Finset.mem_union_left _ (hW.trans j hjD y hyC hz)
      · refine (hpre pre l rest hp z).2 ⟨hQ.1 y hyQ hz, Or.inr ?_⟩
        exact lt_trans (hW.ctx_lt y (hQD hyQ) z hz) hyl
    · obtain ⟨sQ, cQ, hpreQ, hclQ⟩ := hQ.2
      refine ⟨min sQ (S.rank l), if sQ ≤ S.rank l then cQ else S.cl j, fun x hx => ?_,
        fun x hx hxs => ?_⟩
      · exact (hpre pre l rest hp x).2 ⟨hpreQ x (by omega), Or.inr (by omega)⟩
      · obtain ⟨hxQ, hxC | hxl⟩ := (hpre pre l rest hp x).1 hx
        · split_ifs with hs
          · exact hclQ x hxQ (by omega)
          · by_contra hne
            exact hlC (hW.pref j hjD x hxC hne l (by omega))
        · split_ifs with hs
          · exact hclQ x hxQ (by omega)
          · omega
  have hUne : ∀ pre l rest, path = pre ++ l :: rest → C ∪ pre.toFinset ≠ Q := by
    intro pre l rest hp hU
    exact hlU pre l rest hp (hU ▸ (hlmem pre l rest hp).1)
  let fe : Oid n → Finset (Oid n) → COp n := fun l V => ⟨S.T l V, l, V, σ l⟩
  have hfe : ∀ l V, (fe l V).o = S.T l V ∧ (fe l V).oid = l ∧ (fe l V).ctx = V :=
    fun l V => ⟨rfl, rfl, rfl⟩
  -- the edge from `C ∪ pre` labelled `l`
  have hedge : ∀ pre l rest, path = pre ++ l :: rest → fe l (C ∪ pre.toFinset) ∈ E := by
    intro pre l rest hp
    obtain ⟨e, he, hctx, heQ, heU, hemin⟩ := hcomp _ (hUvert pre l rest hp)
      (hUsub pre l rest hp) (hUne pre l rest hp)
    have hl := hlmem pre l rest hp
    have h1 := hemin l hl.1 (hlU pre l rest hp)
    have h2 := hmin pre l rest hp e.oid heQ heU
    have heq : e.oid = l := hinjQ _ heQ _ hl.1 (le_antisymm h1 h2)
    have := (hE e he).eq
    rw [heq, hctx] at this
    have h3 : fe l (C ∪ pre.toFinset) = e := this.symm
    rw [h3]; exact he
  have hxQ : j ∉ C ∪ path.toFinset := by rw [hcur]; exact hjQ
  have hI2 : ∀ pre l rest, path = pre ++ l :: rest →
      xf (S.T l (C ∪ pre.toFinset)) (S.T j (C ∪ pre.toFinset)) =
        S.T l (insert j (C ∪ pre.toFinset)) := by
    intro pre l rest hp
    obtain ⟨hlQ, hlC⟩ := hlmem pre l rest hp
    have hjU : j ∉ C ∪ pre.toFinset := fun hj => hjQ (hUsub pre l rest hp hj)
    refine (S.T_insert hjU (fun hj => hjQ (hQ.1 l hlQ hj)) ?_).symm
    intro y hy hyl
    obtain ⟨hyQ, hyC | hyl'⟩ := (hpre pre l rest hp y).1 hy
    · exact hW.ctx_lt j hjD y hyC
    · rcases lt_trichotomy (S.rank y) (S.rank j) with h1 | h1 | h1
      · exact h1
      · exact absurd (hW.inj (hQD hyQ) hjD h1 ▸ hyQ) hjQ
      · exact absurd (hhigh l hlQ y hyQ h1 hyl') hyl
  obtain ⟨Ef, hloop, hsub, hback, hall⟩ := cLoop_spec S fe hfe (r := r) (cur := Q) (x := j)
    (sx := σ j) path C E Q.card hlen hcur hdisj hnd hjQ (by
      intro pre l rest hp
      obtain ⟨hlQ, hlC⟩ := hlmem pre l rest hp
      refine ⟨(S.T_insert (hlU pre l rest hp) hlC ?_).symm, hI2 pre l rest hp, ?_⟩
      · intro y hy hyC
        rcases ((hpre pre l rest hp y).1 hy).2 with h1 | h1
        · exact absurd h1 hyC
        · exact h1
      · intro E' hEE hE'
        refine firstEdge_eq (hEE _ (hedge pre l rest hp)) rfl ?_ ?_
        · intro e he hctx hne
          have heE : e ∈ E := by
            rcases hE' e he with he | ⟨-, hc⟩
            · exact he
            · exact absurd hctx hc
          have hok := hE e heE
          have heQ : e.oid ∈ Q := hok.sub (Finset.mem_insert_self _ _)
          have heU : e.oid ∉ C ∪ pre.toFinset := hctx ▸ hok.notMem
          have hlt : S.rank l < S.rank e.oid := by
            rcases (hmin pre l rest hp e.oid heQ heU).lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (hinjQ _ hlQ _ heQ h1).symm hne
          have := hcmp l e.oid (C ∪ pre.toFinset) (S.T l (C ∪ pre.toFinset))
            (S.T e.oid (C ∪ pre.toFinset)) hlQ heQ (hlU pre l rest hp) heU (hctx ▸ hok.cl) hlt
          rw [hok.eq, hctx]
          exact this
        · intro e he hctx hoid
          have heE : e ∈ E := by
            rcases hE' e he with he | ⟨-, hc⟩
            · exact he
            · exact absurd hctx hc
          rw [(hE e heE).eq, hctx, hoid])
  refine ⟨Ef, ?_, ?_, ?_⟩
  · simp only [cxForm, hloop]; rfl
  · intro e he
    rcases hback e he with he | he
    · exact (hE e he).mono (Finset.subset_insert _ _)
    · rcases he with rfl | ⟨pre, l, rest, hp, rfl | rfl⟩
      · refine ⟨rfl, ?_, ?_, ?_⟩
        · simp only [opE, hcur]; exact hjQ
        · simp only [opE, hcur]; exact le_rfl
        · simp only [opE, hcur]; exact hC
      · refine ⟨rfl, ?_, ?_, ?_⟩
        · exact fun hj => hjQ (hUsub pre l rest hp hj)
        · exact Finset.insert_subset_insert _ (hUsub pre l rest hp)
        · exact Finset.subset_union_left
      · have hok := hE _ (hedge pre l rest hp)
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [COp.xf, opE, fe, hI2 pre l rest hp]
        · simp only [COp.xf, opE, fe, Finset.mem_insert, not_or]
          exact ⟨fun e => hjQ (e ▸ (hlmem pre l rest hp).1), hlU pre l rest hp⟩
        · simp only [COp.xf, opE, fe]
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          rcases hy with h1 | h1 | hy
          · rw [h1]; exact Or.inr (hlmem pre l rest hp).1
          · exact Or.inl h1
          · exact Or.inr (hUsub pre l rest hp hy)
        · simp only [COp.xf, opE, fe]
          exact hok.cl.trans (Finset.subset_insert _ _)
  · -- completeness of the new state space
    have hrank_ne : ∀ y ∈ Q, S.rank y ≠ S.rank j := fun y hy e =>
      hjQ (hW.inj (hQD hy) hjD e ▸ hy)
    -- `u ∩ path` is a prefix of `path` when it is downward closed
    have hsplit : ∀ u : Finset (Oid n), C ⊆ u → u ⊆ Q → u ≠ Q →
        (∀ z y, [z, y].Sublist path → y ∈ u → z ∈ u) →
        ∃ pre l rest, path = pre ++ l :: rest ∧ u = C ∪ pre.toFinset := by
      intro u hCu huQ hne hdc
      obtain ⟨pre, rest, hp, hin, hout⟩ := exists_prefix path (· ∈ u) hdc
      have hu_eq : ∀ y, y ∈ u ↔ y ∈ C ∨ y ∈ pre := by
        intro y
        constructor
        · intro hy
          by_cases hyC : y ∈ C
          · exact Or.inl hyC
          · have hyp : y ∈ path := (hpathQ y).2 ⟨huQ hy, hyC⟩
            rw [hp, List.mem_append] at hyp
            rcases hyp with hyp | hyp
            · exact Or.inr hyp
            · exact absurd hy (hout y hyp)
        · rintro (hy | hy)
          · exact hCu hy
          · exact hin y hy
      cases rest with
      | nil =>
        exfalso; apply hne
        ext y; rw [hu_eq, ← hcur, Finset.mem_union, List.mem_toFinset, hp, List.append_nil]
      | cons l rest' =>
        refine ⟨pre, l, rest', hp, ?_⟩
        ext y; rw [hu_eq, Finset.mem_union, List.mem_toFinset]
    intro u hu huQ' hne
    by_cases hju : j ∈ u
    · -- `u = w ∪ {j}` with `w` on the path
      set w := u.erase j with hwdef
      have hwQ : w ⊆ Q := by
        intro y hy
        rcases Finset.mem_insert.1 (huQ' (Finset.mem_of_mem_erase hy)) with h1 | h1
        · exact absurd h1 (Finset.ne_of_mem_erase hy)
        · exact h1
      have hCw : C ⊆ w := fun y hy => Finset.mem_erase.2
        ⟨fun e => lt_irrefl _ (e ▸ hW.ctx_lt j hjD y hy), hu.1 j hju hy⟩
      have hwne : w ≠ Q := fun hw => hne (by rw [← Finset.insert_erase hju, ← hwdef, hw])
      obtain ⟨hucl, s, cu, hpreu, hclu⟩ := hu
      obtain ⟨pre, l, rest, hp, hwU⟩ := hsplit w hCw hwQ hwne (by
        intro z y hzy hyw
        have hzQ := ((hpathQ z).1 (hzy.subset (by simp))).1
        have hyp := (hpathQ y).1 (hzy.subset (by simp))
        have hzy' : S.rank z < S.rank y := hsort.forall_sublist hzy
        have hyu := Finset.mem_of_mem_erase hyw
        refine Finset.mem_erase.2 ⟨fun e => hjQ (e ▸ hzQ), ?_⟩
        by_cases hzs : S.rank z < s
        · exact hpreu z hzs
        · push_neg at hzs
          have hcly := hclu y hyu (by omega)
          by_cases hjs : s ≤ S.rank j
          · have hclj := hclu j hju hjs
            have hyj := hcl y hyp.1 (hcly.trans hclj.symm)
            exact absurd (hW.own j hjD y (hQD hyp.1) (hcly.trans hclj.symm) hyj) hyp.2
          · push_neg at hjs
            exact hucl y hyu (hhigh y hyp.1 z hzQ (by omega) hzy'))
      refine ⟨(fe l w).xf (opE S j (σ j) w),
        hall _ (Or.inr ⟨pre, l, rest, hp, Or.inr (by rw [hwU])⟩), ?_, ?_, ?_, ?_⟩
      · simp only [COp.xf, opE, fe]; rw [hwdef, Finset.insert_erase hju]
      · simp only [COp.xf, fe]; exact Finset.mem_insert_of_mem (hlmem pre l rest hp).1
      · simp only [COp.xf, fe]
        intro hlu
        have hlw : l ∈ w := Finset.mem_erase.2 ⟨fun e => hjQ (e ▸ (hlmem pre l rest hp).1), hlu⟩
        rw [hwU] at hlw; exact hlU pre l rest hp hlw
      · simp only [COp.xf, fe]
        intro y hy hyu
        rcases Finset.mem_insert.1 hy with rfl | hyQ
        · exact absurd hju hyu
        · apply hmin pre l rest hp y hyQ
          rw [← hwU]; intro hyw; exact hyu (Finset.mem_of_mem_erase hyw)
    · have huQ : u ⊆ Q := fun y hy =>
        (Finset.mem_insert.1 (huQ' hy)).resolve_left (fun e => hju (e ▸ hy))
      by_cases huq : u = Q
      · refine ⟨opE S j (σ j) Q, hall _ (Or.inl (by rw [hcur])), ?_,
          Finset.mem_insert_self _ _, ?_, ?_⟩
        · simp only [opE]; exact huq.symm
        · exact hju
        · intro y hy hyu
          rcases Finset.mem_insert.1 hy with rfl | hyQ
          · exact le_rfl
          · exact absurd (huq ▸ hyQ) hyu
      · obtain ⟨e, he, hctx, heQ, heu, hemin⟩ := hcomp u hu huQ huq
        rcases lt_or_gt_of_ne (hrank_ne e.oid heQ) with hlt | hgt
        · refine ⟨e, hsub e he, hctx, Finset.mem_insert_of_mem heQ, heu, ?_⟩
          intro y hy hyu
          rcases Finset.mem_insert.1 hy with rfl | hyQ
          · exact hlt.le
          · exact hemin y hyQ hyu
        · have hbelow : ∀ y ∈ Q, S.rank y < S.rank j → y ∈ u := by
            intro y hy hyl
            by_contra hyu
            have := hemin y hy hyu
            omega
          have hCu : C ⊆ u := fun y hy => hbelow y (hC hy) (hW.ctx_lt j hjD y hy)
          obtain ⟨pre, l, rest, hp, huU⟩ := hsplit u hCu huQ huq (by
            intro z y hzy hyu
            have hzQ := ((hpathQ z).1 (hzy.subset (by simp))).1
            have hyp := (hpathQ y).1 (hzy.subset (by simp))
            have hzy' : S.rank z < S.rank y := hsort.forall_sublist hzy
            by_contra hzu
            have := hemin z hzQ hzu
            exact hzu (hu.1 y hyu (hhigh y hyp.1 z hzQ (by omega) hzy')))
          refine ⟨opE S j (σ j) u, hall _ (Or.inr ⟨pre, l, rest, hp, Or.inl (by rw [huU])⟩), rfl,
            Finset.mem_insert_self _ _, hju, ?_⟩
          intro y hy hyu
          rcases Finset.mem_insert.1 hy with rfl | hyQ
          · exact le_rfl
          · have := hemin y hyQ hyu
            simp only [opE]
            omega

end CJup

end Podc.JupiterListSpec
