import Papers.PODC2016.CollaborativeListSpec.Encoding

/-!
# Generic consequences of the list specifications used in the lower-bound proof
-/

namespace Podc.CollaborativeListSpec

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U]
  {P : Protocol Rep (LOp U) (List U) Q M}

/-- `hist` only depends on the prefix up to the position. -/
theorem hist_prefix {α β : List (Act Rep (LOp U))} (h : α <+: β) {p : ℕ} (hp : p < α.length) :
    P.hist α p = P.hist β p := by
  have h1 : α[p]? = β[p]? := List.IsPrefix.getElem?_of_lt h hp
  have h2 : α.take p = β.take p := by
    obtain ⟨t, rfl⟩ := h; rw [List.take_append_of_le_length hp.le]
  simp only [Protocol.hist, Protocol.stBefore, h1, h2]

theorem hist_pre {g : ℕ → Act Rep (LOp U)} {m n p : ℕ} (hm : p < m) (hn : p < n) :
    P.hist (pre g m) p = P.hist (pre g n) p := by
  rcases le_total m n with h | h
  · exact hist_prefix (pre_prefix g h) (by simp; omega)
  · exact (hist_prefix (pre_prefix g h) (by simp; omega)).symm

/-- The response of the `do` event at position `p` of `pre g n`. -/
def rval (P : Protocol Rep (LOp U) (List U) Q M) (g : ℕ → Act Rep (LOp U)) (p : ℕ) : List U :=
  match g p with
  | .doOp r op => P.resp r ((P.exec (pre g p)).st r) op
  | _ => []

theorem hist_pre_eq {g : ℕ → Act Rep (LOp U)} {n p : ℕ} (hp : p < n) {r : Rep} {op : LOp U}
    (hg : g p = .doOp r op) : P.hist (pre g n) p = some (r, op, rval P g p) := by
  rw [hist_of_getElem? (by rw [pre_getElem?_of_lt g hp, hg])]
  simp [rval, hg, Protocol.stBefore, pre_take, min_eq_left hp.le]

theorem hist_pre_eq_some {g : ℕ → Act Rep (LOp U)} {n p : ℕ} {r : Rep} {op : LOp U} {v : List U}
    (h : P.hist (pre g n) p = some (r, op, v)) : p < n ∧ g p = .doOp r op ∧ v = rval P g p := by
  obtain ⟨h1, -⟩ := hist_eq_some h
  rw [pre_getElem?] at h1
  split_ifs at h1 with hp
  · have hg := Option.some.inj h1
    refine ⟨hp, hg, ?_⟩
    rw [hist_pre_eq hp hg] at h; simp at h; exact h.symm

theorem rval_congr {g g' : ℕ → Act Rep (LOp U)} {p : ℕ} (h : ∀ q ≤ p, g q = g' q) :
    rval P g p = rval P g' p := by
  have := pre_congr (g := g) (g' := g') (n := p) (fun q hq => h q hq.le)
  simp only [rval, h p le_rfl, this]

/-- Well-formedness of prefixes, step by step. -/
theorem WF_pre_succ {g : ℕ → Act Rep (LOp U)} {n : ℕ} :
    P.WF (pre g (n + 1)) ↔ P.WF (pre g n) ∧ Enabled (pre g (n + 1)) (P.exec (pre g n)) n (g n) := by
  have get : ∀ m, m ≤ n + 1 → ∀ p (hp : p < m), (pre g m)[p]'(by simp; omega) = g p := by
    intro m _ p hp; simp [pre]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, ?_⟩
    · have := h p (by simp at hp ⊢; omega)
      simp only [length_pre] at hp
      rw [pre_take] at this ⊢
      rw [get _ le_rfl p (by omega)] at this
      rw [get _ (by omega) p hp]
      rcases hg : g p with ⟨r, op⟩ | r | ⟨r, src⟩ <;> rw [hg] at this
      · trivial
      · simpa [Enabled, min_eq_left (show p ≤ n + 1 by omega), min_eq_left (show p ≤ n by omega)]
          using this
      · obtain ⟨h1, r', h2⟩ := this
        refine ⟨h1, r', ?_⟩
        rw [pre_getElem?_of_lt g (by omega)] at h2 ⊢; exact h2
    · have := h n (by simp)
      rw [pre_take, min_eq_left (by omega), get _ le_rfl n (by omega)] at this
      exact this
  · rintro ⟨h, he⟩ p hp
    simp only [length_pre] at hp
    rw [pre_take, min_eq_left (by omega), get _ le_rfl p hp]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · have := h p (by simpa)
      rw [pre_take, min_eq_left hp.le, get _ (by omega) p hp] at this
      rcases hg : g p with ⟨r, op⟩ | r | ⟨r, src⟩ <;> rw [hg] at this
      · trivial
      · exact this
      · obtain ⟨h1, r', h2⟩ := this
        refine ⟨h1, r', ?_⟩
        rw [pre_getElem?_of_lt g (by omega)] at h2 ⊢; exact h2
    · exact he

/-! ### Single-replica executions: visibility is the replica order -/

/-- In an execution where all events are at one replica, `≤vis` between `do` events is `≤`. -/
theorem visLe_iff_of_single {α : List (Act Rep (LOp U))} {r : Rep}
    (hrep : ∀ (p : ℕ) (a : Act Rep (LOp U)), α[p]? = some a → a.rep = r) {vis : ℕ → ℕ → Prop}
    (hwf : AbsWF (P.hist α) vis) {q p : ℕ} (hq : (P.hist α q).isSome) (hp : (P.hist α p).isSome) :
    VisLe vis q p ↔ q ≤ p := by
  obtain ⟨⟨rq, opq, vq⟩, hq'⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨⟨rp, opp, vp⟩, hp'⟩ := Option.isSome_iff_exists.1 hp
  have hrq := hrep q _ (hist_eq_some hq').1
  have hrp := hrep p _ (hist_eq_some hp').1
  simp only [Act.rep_doOp] at hrq hrp
  constructor
  · rintro (rfl | h)
    · exact le_rfl
    · by_contra hc
      exact hwf.irrefl q (hwf.trans _ _ _ h (hwf.ro p q _ _ (by omega) hp' hq' (by simp [hrq, hrp])))
  · intro h
    rcases h.lt_or_eq with h | rfl
    · exact Or.inr (hwf.ro q p _ _ h hq' hp' (by simp [hrq, hrp]))
    · exact Or.inl rfl

/-- Condition (1a) in a single-replica prefix: the response contains exactly the elements inserted
and not deleted at or before the event. -/
theorem mem_rval_of_single {g : ℕ → Act Rep (LOp U)} {n : ℕ} {r : Rep}
    (hrep : ∀ p < n, (g p).rep = r) {vis : ℕ → ℕ → Prop} {lo : U → U → Prop}
    (hwf : AbsWF (P.hist (pre g n)) vis) (hc : ListCond (P.hist (pre g n)) vis lo)
    {p : ℕ} (hp : p < n) {op : LOp U} (hg : g p = .doOp r op) (x : U) :
    x ∈ rval P g p ↔ (∃ q ≤ p, ∃ k, g q = .doOp r (.ins x k)) ∧ ¬ ∃ q ≤ p, g q = .doOp r (.del x) := by
  have hrep' : ∀ (q : ℕ) (a : Act Rep (LOp U)), (pre g n)[q]? = some a → a.rep = r := by
    intro q a h; rw [pre_getElem?] at h; split_ifs at h with hq
    · cases h; exact hrep q hq
  have hh := hist_pre_eq (P := P) hp hg
  rw [((hc p r op _ hh).1 x)]
  have key : ∀ q, VisLe vis q p → (P.hist (pre g n) q).isSome → q ≤ p := fun q hv hq =>
    (visLe_iff_of_single hrep' hwf hq (by simp [hh])).1 hv
  have key' : ∀ q ≤ p, (P.hist (pre g n) q).isSome → VisLe vis q p := fun q hqp hq =>
    (visLe_iff_of_single hrep' hwf hq (by simp [hh])).2 hqp
  apply and_congr
  · constructor
    · rintro ⟨q, r', k, v, hv, hq⟩
      obtain ⟨hqn, hgq, -⟩ := hist_pre_eq_some hq
      have := hrep q hqn; rw [hgq] at this; simp at this; subst this
      exact ⟨q, key q hv (by simp [hq]), k, hgq⟩
    · rintro ⟨q, hqp, k, hgq⟩
      have hh' := hist_pre_eq (P := P) (show q < n by omega) hgq
      exact ⟨q, r, k, _, key' q hqp (by simp [hh']), hh'⟩
  · apply not_congr
    constructor
    · rintro ⟨q, r', v, hv, hq⟩
      obtain ⟨hqn, hgq, -⟩ := hist_pre_eq_some hq
      have := hrep q hqn; rw [hgq] at this; simp at this; subst this
      exact ⟨q, key q hv (by simp [hq]), hgq⟩
    · rintro ⟨q, hqp, hgq⟩
      have hh' := hist_pre_eq (P := P) (show q < n by omega) hgq
      exact ⟨q, r, _, key' q hqp (by simp [hh']), hh'⟩

/-- The step lemma: a response with the members of an earlier `lo`-ordered response plus a fresh
inserted element `a` is the earlier list with `a` inserted at `min k n`. -/
theorem eq_insertIdx_of_weak {lo : U → U → Prop} {l l' : List U} {a : U} {k : ℕ}
    (hl : l.Pairwise lo) (hl' : l'.Pairwise lo) (hirr : ∀ a, ¬ lo a a)
    (htr : ∀ a ∈ l', ∀ b ∈ l', ∀ c ∈ l', lo a b → lo b c → lo a c)
    (hmem : ∀ x, x ∈ l' ↔ x ∈ l ∨ x = a) (ha : a ∉ l)
    (hk : l'[min k (l'.length - 1)]? = some a) : l' = l.insertIdx (min k l.length) a :=
  eq_insertIdx (nodup_of_pairwise hl' hirr)
    (sublist_of_pairwise hl hl' hirr htr (fun x hx => (hmem x).2 (Or.inl hx))) ha hmem hk

end Podc.CollaborativeListSpec
