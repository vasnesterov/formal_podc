import Papers.PODC2018.PartialReplicationCausal.Necessity.Model

/-!
# Theorem 1: basic invariants of reachable states of a metadata algorithm

Field lemmas for `St.write` / `St.apply`, the invariant `T1.Inv` of reachable states, extension of
states along steps (`T1.Ext`) and the corresponding stability of happened-before.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

/-! ### Field lemmas -/

section fields

variable (s : St ι Reg M) (i : ι) (x : Reg) (ℓ : ℕ) (a : ℕ)

@[simp] lemma write_n : (s.write A i x ℓ).n = s.n + 1 := rfl
@[simp] lemma apply_n : (s.apply A i a).n = s.n := rfl
@[simp] lemma apply_log : (s.apply A i a).log = s.log := rfl

lemma write_log_lt {c : ℕ} (hc : c < s.n) : (s.write A i x ℓ).log c = s.log c := by
  simp [St.write, Function.update, hc.ne]

@[simp] lemma write_log_n : (s.write A i x ℓ).log s.n = ⟨i, x, ℓ, A.write i (s.md i) x, s.app i⟩ := by
  simp [St.write]

lemma write_md (r : ι) :
    (s.write A i x ℓ).md r = if r = i then A.write i (s.md i) x else s.md r := by
  simp [St.write, Function.update]

lemma write_app (r : ι) :
    (s.write A i x ℓ).app r = if r = i then insert s.n (s.app i) else s.app r := by
  simp [St.write, Function.update]

@[simp] lemma write_md_self : (s.write A i x ℓ).md i = A.write i (s.md i) x := by simp [write_md]
@[simp] lemma write_app_self : (s.write A i x ℓ).app i = insert s.n (s.app i) := by
  simp [write_app]

lemma write_md_ne {r : ι} (h : r ≠ i) : (s.write A i x ℓ).md r = s.md r := by simp [write_md, h]
lemma write_app_ne {r : ι} (h : r ≠ i) : (s.write A i x ℓ).app r = s.app r := by
  simp [write_app, h]

lemma apply_md (r : ι) :
    (s.apply A i a).md r =
      if r = i then A.merge i (s.md i) (s.log a).src (s.log a).reg (s.log a).ts else s.md r := by
  simp [St.apply, Function.update]

lemma apply_app (r : ι) :
    (s.apply A i a).app r = if r = i then insert a (s.app i) else s.app r := by
  simp [St.apply, Function.update]

@[simp] lemma apply_md_self :
    (s.apply A i a).md i = A.merge i (s.md i) (s.log a).src (s.log a).reg (s.log a).ts := by
  simp [apply_md]
@[simp] lemma apply_app_self : (s.apply A i a).app i = insert a (s.app i) := by simp [apply_app]
lemma apply_md_ne {r : ι} (h : r ≠ i) : (s.apply A i a).md r = s.md r := by simp [apply_md, h]
lemma apply_app_ne {r : ι} (h : r ≠ i) : (s.apply A i a).app r = s.app r := by
  simp [apply_app, h]

lemma subset_apply_app (r : ι) : s.app r ⊆ (s.apply A i a).app r := by
  rw [apply_app]; split_ifs with h
  · subst h; exact Set.subset_insert _ _
  · exact le_rfl

lemma subset_write_app (r : ι) : s.app r ⊆ (s.write A i x ℓ).app r := by
  rw [write_app]; split_ifs with h
  · subst h; exact Set.subset_insert _ _
  · exact le_rfl

lemma hb_apply : HB (s.apply A i a) = HB s := rfl

end fields

/-! ### Invariants -/

/-- Basic invariants of reachable states. -/
structure Inv (X : ι → Set Reg) (s : St ι Reg M) : Prop where
  app_lt : ∀ r a, a ∈ s.app r → a < s.n
  app_reg : ∀ r a, a ∈ s.app r → (s.log a).reg ∈ X r
  own : ∀ a < s.n, a ∈ s.app (s.log a).src
  pre_lt : ∀ a < s.n, ∀ c ∈ (s.log a).pre, c < a
  lab_inj : ∀ a < s.n, ∀ b < s.n, (s.log a).lab = (s.log b).lab → a = b

lemma inv_init {s : St ι Reg M} (h : IsInit A s) : Inv X s := by
  obtain ⟨hn, -, happ⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hn, happ]

lemma Inv.step {s s' : St ι Reg M} (h : Inv X s) (hs : Step X A s s') : Inv X s' := by
  cases hs with
  | write i x ℓ hx hℓ =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r a ha
      rw [write_app] at ha
      split_ifs at ha with hr
      · rcases ha with rfl | ha
        · simp
        · have := h.app_lt _ _ ha; simp; omega
      · have := h.app_lt _ _ ha; simp; omega
    · intro r a ha
      rw [write_app] at ha
      split_ifs at ha with hr
      · subst hr
        rcases ha with rfl | ha
        · simpa using hx
        · rw [write_log_lt _ _ _ _ (h.app_lt _ _ ha)]; exact h.app_reg _ _ ha
      · rw [write_log_lt _ _ _ _ (h.app_lt _ _ ha)]; exact h.app_reg _ _ ha
    · intro a ha
      simp only [write_n] at ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · rw [write_log_lt _ _ _ _ ha]; exact subset_write_app _ _ _ _ _ (h.own a ha)
      · simp
    · intro a ha c hc
      simp only [write_n] at ha
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · rw [write_log_lt _ _ _ _ ha] at hc; exact h.pre_lt a ha c hc
      · simp only [write_log_n] at hc; exact h.app_lt _ _ hc
    · intro a ha b hb hab
      simp only [write_n] at ha hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
      · rw [write_log_lt _ _ _ _ ha, write_log_lt _ _ _ _ hb] at hab; exact h.lab_inj a ha b hb hab
      · rw [write_log_lt _ _ _ _ ha, write_log_n] at hab; exact absurd hab (hℓ a ha)
      · rw [write_log_lt _ _ _ _ hb, write_log_n] at hab; exact absurd hab.symm (hℓ b hb)
      · rfl
  | apply i a he =>
    obtain ⟨ha, -, hreg, -, -⟩ := he
    refine ⟨?_, ?_, ?_, h.pre_lt, h.lab_inj⟩
    · intro r c hc
      rw [apply_app] at hc
      split_ifs at hc with hr
      · rcases hc with rfl | hc
        · exact ha
        · exact h.app_lt _ _ hc
      · exact h.app_lt _ _ hc
    · intro r c hc
      rw [apply_app] at hc
      split_ifs at hc with hr
      · subst hr
        rcases hc with rfl | hc
        · exact hreg
        · exact h.app_reg _ _ hc
      · exact h.app_reg _ _ hc
    · intro c hc; exact subset_apply_app _ _ _ _ (h.own c hc)

lemma Inv.rtg {s s' : St ι Reg M} (h : Inv X s) (hs : Relation.ReflTransGen (Step X A) s s') :
    Inv X s' := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => exact ih.step hst

lemma Reachable.inv {s : St ι Reg M} (h : Reachable X A s) : Inv X s := by
  obtain ⟨s₀, h₀, hs⟩ := h
  exact (inv_init h₀).rtg hs

lemma Reachable.rtg {s s' : St ι Reg M} (h : Reachable X A s)
    (hs : Relation.ReflTransGen (Step X A) s s') : Reachable X A s' := by
  obtain ⟨s₀, h₀, h0⟩ := h
  exact ⟨s₀, h₀, h0.trans hs⟩

lemma Reachable.step {s s' : St ι Reg M} (h : Reachable X A s) (hs : Step X A s s') :
    Reachable X A s' := Reachable.rtg h (.single hs)

/-! ### Extension of states -/

/-- `s'` extends `s`: more updates, the same log prefix, larger applied sets. -/
structure Ext (s s' : St ι Reg M) : Prop where
  n_le : s.n ≤ s'.n
  log_eq : ∀ a < s.n, s'.log a = s.log a
  app_sub : ∀ r, s.app r ⊆ s'.app r

lemma Ext.refl (s : St ι Reg M) : Ext s s := ⟨le_rfl, fun _ _ => rfl, fun _ => le_rfl⟩

lemma Ext.trans {s s' s'' : St ι Reg M} (h : Ext s s') (h' : Ext s' s'') : Ext s s'' :=
  ⟨h.n_le.trans h'.n_le, fun a ha => by rw [h'.log_eq a (lt_of_lt_of_le ha h.n_le), h.log_eq a ha],
    fun r => (h.app_sub r).trans (h'.app_sub r)⟩

lemma ext_write (s : St ι Reg M) (i : ι) (x : Reg) (ℓ : ℕ) : Ext s (s.write A i x ℓ) :=
  ⟨by simp, fun _ ha => write_log_lt _ _ _ _ ha, subset_write_app _ _ _ _⟩

lemma ext_apply (s : St ι Reg M) (i : ι) (a : ℕ) : Ext s (s.apply A i a) :=
  ⟨le_rfl, fun _ _ => rfl, subset_apply_app _ _ _⟩

lemma Ext.of_step {s s' : St ι Reg M} (hs : Step X A s s') : Ext s s' := by
  cases hs with
  | write => exact ext_write _ _ _ _
  | apply => exact ext_apply _ _ _

lemma Ext.of_rtg {s s' : St ι Reg M} (hs : Relation.ReflTransGen (Step X A) s s') : Ext s s' := by
  induction hs with
  | refl => exact Ext.refl _
  | tail _ hst ih => exact ih.trans (Ext.of_step hst)

/-! ### Happened-before -/

lemma hb_lt_n {s : St ι Reg M} {a b : ℕ} (hab : HB s a b) : b < s.n := by
  induction hab with
  | single h => exact h.1
  | tail _ h _ => exact h.1

lemma Inv.hb_lt {s : St ι Reg M} (h : Inv X s) {a b : ℕ} (hab : HB s a b) : a < b := by
  induction hab with
  | single h' => exact h.pre_lt _ h'.1 _ h'.2
  | tail _ h' ih => exact ih.trans (h.pre_lt _ h'.1 _ h'.2)

lemma Ext.hb {s s' : St ι Reg M} (he : Ext s s') {a b : ℕ} (hab : HB s a b) : HB s' a b := by
  unfold HB at *
  refine Relation.TransGen.mono ?_ _ _ hab
  rintro x y ⟨hy, hx⟩
  exact ⟨lt_of_lt_of_le hy he.n_le, by rwa [he.log_eq y hy]⟩

lemma Ext.hb_back {s s' : St ι Reg M} (he : Ext s s') (h : Inv X s) {a b : ℕ}
    (hab : HB s' a b) (hb : b < s.n) : HB s a b := by
  induction hab with
  | single h' =>
    refine .single ⟨hb, ?_⟩
    rw [← he.log_eq _ hb]; exact h'.2
  | @tail y z _ h' ih =>
    have hc : y ∈ (s.log z).pre := by rw [← he.log_eq _ hb]; exact h'.2
    exact .tail (ih ((h.pre_lt _ hb _ hc).trans hb)) ⟨hb, hc⟩

lemma Ext.hb_iff {s s' : St ι Reg M} (he : Ext s s') (h : Inv X s) {a b : ℕ} (hb : b < s.n) :
    HB s' a b ↔ HB s a b := ⟨fun h' => he.hb_back h h' hb, he.hb⟩

lemma hb_single {s : St ι Reg M} {a b : ℕ} (hb : b < s.n) (ha : a ∈ (s.log b).pre) : HB s a b :=
  .single ⟨hb, ha⟩

lemma hb_cases {s : St ι Reg M} {a b : ℕ} (hab : HB s a b) :
    b < s.n ∧ ∃ c ∈ (s.log b).pre, a = c ∨ HB s a c := by
  rcases Relation.TransGen.tail'_iff.1 hab with ⟨c, hac, hcb⟩
  refine ⟨hcb.1, c, hcb.2, ?_⟩
  rcases Relation.ReflTransGen.cases_tail hac with rfl | h
  · exact .inl rfl
  · exact .inr (Relation.TransGen.tail'_iff.2 h)

/-- If `pre b = insert c (pre c)`, then the predecessors of `b` are `c` and those of `c`. -/
lemma hb_insert {s : St ι Reg M} {b c x : ℕ} (hb : b < s.n) (hc : c < s.n)
    (hpre : (s.log b).pre = insert c (s.log c).pre) : HB s x b ↔ x = c ∨ HB s x c := by
  constructor
  · intro h
    obtain ⟨-, y, hy, hxy⟩ := hb_cases h
    rw [hpre] at hy
    rcases hy with rfl | hy
    · exact hxy
    · right
      rcases hxy with rfl | hxy
      · exact hb_single hc hy
      · exact hxy.tail ⟨hc, hy⟩
  · rintro (rfl | h)
    · exact hb_single hb (by rw [hpre]; exact Set.mem_insert _ _)
    · exact h.tail ⟨hb, by rw [hpre]; exact Set.mem_insert _ _⟩

lemma Inv.cp_lt {s : St ι Reg M} (h : Inv X s) {i : ι} {a : ℕ} (ha : a ∈ CP s i) : a < s.n := by
  rcases ha with ha | ⟨b, -, hab⟩
  · exact h.app_lt _ _ ha
  · exact (h.hb_lt hab).trans (hb_lt_n hab)

lemma exists_lab_bound (s : St ι Reg M) : ∃ N, ∀ a < s.n, (s.log a).lab < N := by
  refine ⟨(Finset.range s.n).sup (fun a => (s.log a).lab) + 1, fun a ha => ?_⟩
  have := Finset.le_sup (f := fun a => (s.log a).lab) (Finset.mem_range.2 ha)
  omega

end T1

end Podc.PartialReplicationCausal.Necessity
