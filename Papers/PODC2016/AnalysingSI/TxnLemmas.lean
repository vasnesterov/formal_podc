import Papers.PODC2016.AnalysingSI.Model

/-!
# Transactions as operation lists: accesses, final values, splicing

List-level facts about transactions used for transaction chopping (§5 and §A.5 of
Cerone–Gotsman): Proposition 25 (what a spliced transaction `T^G` reads and writes) and the
internal consistency INT of a spliced transaction, for the concatenation `ts.flatten` of the
transactions `ts` of a session in session order.
-/

namespace Podc.AnalysingSI

variable {Obj V : Type*} [DecidableEq Obj]

namespace Txn

/-- `T ⊢ _(x, _)`: `T` performs some operation on `x`. -/
def Accesses (T : Txn Obj V) (x : Obj) : Prop := ∃ o ∈ T, o.obj = x

/-- The value of the last operation of `T` on `x` (read or write), if any. -/
def finalVal (T : Txn Obj V) (x : Obj) : Option V :=
  ((T.filter (fun o => decide (o.obj = x))).getLast?).map Op.val

variable {T : Txn Obj V} {x : Obj} {n m : V}

/-! ### Helper lemmas: accesses, reads, writes and final values of an append -/

theorem find?_eq_none_iff_not_accesses :
    T.find? (fun o => decide (o.obj = x)) = none ↔ ¬ T.Accesses x := by
  simp [Accesses, List.find?_eq_none]

theorem finalVal_eq_none_iff : T.finalVal x = none ↔ ¬ T.Accesses x := by
  simp [finalVal, Accesses]

theorem accesses_iff_finalVal_isSome : T.Accesses x ↔ (T.finalVal x).isSome := by
  rw [← not_iff_not, Option.not_isSome_iff_eq_none, finalVal_eq_none_iff]

omit [DecidableEq Obj] in
@[simp] theorem accesses_nil : ¬ Accesses ([] : Txn Obj V) x := by
  simp [Accesses]

omit [DecidableEq Obj] in
@[simp] theorem accesses_append {l₁ l₂ : Txn Obj V} :
    (l₁ ++ l₂).Accesses x ↔ l₁.Accesses x ∨ l₂.Accesses x := by
  simp only [Accesses, List.mem_append]
  constructor
  · rintro ⟨o, ho | ho, rfl⟩
    · exact Or.inl ⟨o, ho, rfl⟩
    · exact Or.inr ⟨o, ho, rfl⟩
  · rintro (⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩)
    · exact ⟨o, Or.inl ho, rfl⟩
    · exact ⟨o, Or.inr ho, rfl⟩

theorem finalVal_append {l₁ l₂ : Txn Obj V} :
    (l₁ ++ l₂).finalVal x = (l₂.finalVal x).or (l₁.finalVal x) := by
  simp [finalVal, List.filter_append, List.getLast?_append, Option.map_or]

theorem finalVal_append_of_accesses {l₁ l₂ : Txn Obj V} (h : l₂.Accesses x) :
    (l₁ ++ l₂).finalVal x = l₂.finalVal x := by
  rw [finalVal_append]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (accesses_iff_finalVal_isSome.mp h)
  simp [hv]

theorem finalVal_append_of_not_accesses {l₁ l₂ : Txn Obj V} (h : ¬ l₂.Accesses x) :
    (l₁ ++ l₂).finalVal x = l₁.finalVal x := by
  rw [finalVal_append, finalVal_eq_none_iff.mpr h]
  simp

theorem reads_append {l₁ l₂ : Txn Obj V} :
    (l₁ ++ l₂).Reads x n ↔ l₁.Reads x n ∨ (¬ l₁.Accesses x ∧ l₂.Reads x n) := by
  simp only [Reads, List.find?_append, Option.or_eq_some_iff, find?_eq_none_iff_not_accesses]

theorem writes_eq_none_iff :
    (T.filter (fun o => o.isWrite && decide (o.obj = x))).getLast? = none ↔
      ∀ m, ¬ T.Writes x m := by
  constructor
  · intro h m hm
    rw [Writes, h] at hm
    exact absurd hm (by simp)
  · intro h
    cases ho : (T.filter (fun o => o.isWrite && decide (o.obj = x))).getLast? with
    | none => rfl
    | some o =>
      exfalso
      have hm := List.mem_of_getLast? ho
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨-, hw, hx⟩ := hm
      cases o with
      | read y k => simp at hw
      | write y k =>
        simp only [Op.obj_write] at hx
        subst hx
        exact h k ho

theorem writes_append {l₁ l₂ : Txn Obj V} :
    (l₁ ++ l₂).Writes x n ↔ l₂.Writes x n ∨ (l₁.Writes x n ∧ ∀ m, ¬ l₂.Writes x m) := by
  simp only [Writes, List.filter_append, List.getLast?_append, Option.or_eq_some_iff]
  rw [writes_eq_none_iff]
  simp only [Writes]
  tauto

theorem Int.of_append_left {l₁ l₂ : Txn Obj V} (h : (l₁ ++ l₂).Int) : l₁.Int := by
  intro pre suf x n o hT ho
  exact h pre (suf ++ l₂) x n o (by simp [hT]) ho

theorem Reads.accesses (h : T.Reads x n) : T.Accesses x := by
  have hm := List.mem_of_find?_eq_some h
  exact ⟨_, hm, rfl⟩

theorem Writes.accesses (h : T.Writes x n) : T.Accesses x := by
  have hm := List.mem_of_getLast? h
  simp only [List.mem_filter] at hm
  exact ⟨_, hm.1, rfl⟩

/-- A transaction accessing `x` without writing it reads `x` (its first operation on `x` is a
read). -/
theorem exists_reads_of_accesses (h : T.Accesses x) (hw : ∀ n, ¬ T.Writes x n) :
    ∃ n, T.Reads x n := by
  have hnone := writes_eq_none_iff.mpr hw
  rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hnone
  cases hf : T.find? (fun o => decide (o.obj = x)) with
  | none => exact absurd h (find?_eq_none_iff_not_accesses.mp hf)
  | some o =>
    have hmem := List.mem_of_find?_eq_some hf
    have hx : o.obj = x := by simpa using List.find?_some hf
    cases o with
    | read y k =>
      simp only [Op.obj_read] at hx
      subst hx
      exact ⟨k, hf⟩
    | write y k =>
      simp only [Op.obj_write] at hx
      subst hx
      exact absurd (hnone _ hmem) (by simp)

omit [DecidableEq Obj] in
theorem accesses_singleton {o : Op Obj V} : Accesses [o] x ↔ o.obj = x := by
  simp [Accesses]

/-- Common generalisation of `Int.finalVal_of_writes` and `Int.finalVal_of_reads`. -/
theorem Int.finalVal_eq (hT : T.Int) (h : T.Writes x m ∨ (T.Reads x m ∧ ∀ n, ¬ T.Writes x n)) :
    T.finalVal x = some m := by
  induction T using List.reverseRecOn with
  | nil => simp [Writes, Reads] at h
  | append_singleton T' o ih =>
    have hT' := hT.of_append_left
    cases o with
    | read y k =>
      have hnw : ∀ j, ¬ Writes [Op.read y k] x j := by simp [Writes]
      by_cases hy : y = x
      · subst hy
        rw [finalVal_append_of_accesses (by simp [accesses_singleton])]
        simp only [finalVal, List.filter_cons, Op.obj_read, decide_true, ite_true,
          List.filter_nil, List.getLast?_singleton, Option.map_some, Op.val_read,
          Option.some.injEq]
        by_cases hacc : Accesses T' y
        · have ih' : finalVal T' y = some m := by
            refine ih hT' ?_
            rcases h with h | ⟨h, hw⟩
            · left
              rcases writes_append.mp h with h | h
              · exact absurd h (hnw m)
              · exact h.1
            · right
              refine ⟨?_, fun j hj => hw j (writes_append.mpr (Or.inr ⟨hj, hnw⟩))⟩
              rcases reads_append.mp h with h | h
              · exact h
              · exact absurd hacc h.1
          simp only [finalVal, Option.map_eq_some_iff] at ih'
          obtain ⟨v, hv, rfl⟩ := ih'
          exact (hT T' [] y k v (by simp) hv).symm
        · rcases h with h | ⟨h, -⟩
          · rcases writes_append.mp h with h | h
            · exact absurd h (hnw m)
            · exact absurd h.1.accesses hacc
          · rcases reads_append.mp h with h | h
            · exact absurd h.accesses hacc
            · simpa [Reads] using h.2
      · have hna : ¬ Accesses [Op.read y k] x := by simp [accesses_singleton, hy]
        rw [finalVal_append_of_not_accesses hna]
        refine ih hT' ?_
        rcases h with h | ⟨h, hw⟩
        · left
          rcases writes_append.mp h with h | h
          · exact absurd h (hnw m)
          · exact h.1
        · right
          refine ⟨?_, fun j hj => hw j (writes_append.mpr (Or.inr ⟨hj, hnw⟩))⟩
          rcases reads_append.mp h with h | h
          · exact h
          · exact absurd h.2.accesses hna
    | write y k =>
      by_cases hy : y = x
      · subst hy
        rw [finalVal_append_of_accesses (by simp [accesses_singleton])]
        have hk : Writes (T' ++ [Op.write y k]) y k :=
          writes_append.mpr (Or.inl (by simp [Writes]))
        rcases h with h | ⟨-, hw⟩
        · rcases writes_append.mp h with h | h
          · simpa [finalVal, Writes] using h
          · exact absurd (by simp [Writes]) (h.2 k)
        · exact absurd hk (hw k)
      · have hna : ¬ Accesses [Op.write y k] x := by simp [accesses_singleton, hy]
        have hnw : ∀ j, ¬ Writes [Op.write y k] x j := fun j hj => hna hj.accesses
        rw [finalVal_append_of_not_accesses hna]
        refine ih hT' ?_
        rcases h with h | ⟨h, hw⟩
        · left
          rcases writes_append.mp h with h | h
          · exact absurd h (hnw m)
          · exact h.1
        · right
          refine ⟨?_, fun j hj => hw j (writes_append.mpr (Or.inr ⟨hj, hnw⟩))⟩
          rcases reads_append.mp h with h | h
          · exact h
          · exact absurd h.2.accesses hna

/-- Under INT, the last operation on `x` returns the last value written to `x`. -/
theorem Int.finalVal_of_writes (hT : T.Int) (h : T.Writes x m) : T.finalVal x = some m :=
  hT.finalVal_eq (Or.inl h)

/-- Under INT, in a transaction that reads but does not write `x`, every read of `x` returns the
value of the first one. -/
theorem Int.finalVal_of_reads (hT : T.Int) (h : T.Reads x m) (hw : ∀ n, ¬ T.Writes x n) :
    T.finalVal x = some m :=
  hT.finalVal_eq (Or.inr ⟨h, hw⟩)

/-- INT of an append: both parts are internally consistent and every read of `x` by `l₂` that is
not preceded in `l₂` by an operation on `x` returns the final value of `x` in `l₁`, if `l₁`
accesses `x`. -/
theorem Int.append {l₁ l₂ : Txn Obj V} (h₁ : l₁.Int) (h₂ : l₂.Int)
    (h : ∀ x n, l₂.Reads x n → l₁.Accesses x → l₁.finalVal x = some n) : Txn.Int (l₁ ++ l₂) := by
  intro pre suf y k o hT ho
  have key : ∀ a', pre = l₁ ++ a' → l₂ = a' ++ Op.read y k :: suf → o.val = k := by
    intro a' hpre hl₂
    subst hpre
    rw [List.filter_append, List.getLast?_append, Option.or_eq_some_iff] at ho
    rcases ho with ho | ⟨hnone, ho⟩
    · exact h₂ a' suf y k o hl₂ ho
    · rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hnone
      have hna : ¬ Accesses a' y := by
        rintro ⟨o', ho', rfl⟩
        exact hnone o' ho' (by simp)
      have hr : l₂.Reads y k := by
        rw [hl₂, reads_append]
        exact Or.inr ⟨hna, by simp [Reads]⟩
      have hacc : l₁.Accesses y := by
        have hm := List.mem_of_getLast? ho
        simp only [List.mem_filter, decide_eq_true_eq] at hm
        exact ⟨o, hm.1, hm.2⟩
      have hfv := h y k hr hacc
      simp only [finalVal, ho, Option.map_some, Option.some.injEq] at hfv
      exact hfv
  rcases List.append_eq_append_iff.mp hT with ⟨a', hpre, hl₂⟩ | ⟨c', hl₁, hc⟩
  · exact key a' hpre hl₂
  · cases c' with
    | nil =>
      simp only [List.append_nil, List.nil_append] at hl₁ hc
      exact key [] (by simp [hl₁]) (by simp [hc])
    | cons c c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact h₁ pre c'' y k o hl₁ ho

/-- The last transaction of `ts` accessing `x` determines the final value of `x` in
`ts.flatten`. -/
theorem exists_last_accesses (ts : List (Txn Obj V)) (h : Accesses ts.flatten x) :
    ∃ j, ∃ hj : j < ts.length, ts[j].Accesses x ∧
      (∀ j'', j < j'' → ∀ (h2 : j'' < ts.length), ¬ ts[j''].Accesses x) ∧
      finalVal ts.flatten x = ts[j].finalVal x := by
  induction ts using List.reverseRecOn with
  | nil => simp at h
  | append_singleton ts t ih =>
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] at h ⊢
    by_cases ht : t.Accesses x
    · refine ⟨ts.length, by simp, by simpa using ht, fun j'' h1 h2 => by simp at h2; omega, ?_⟩
      rw [finalVal_append_of_accesses ht]
      simp
    · have hL : Accesses ts.flatten x := by
        rcases accesses_append.mp h with h | h
        · exact h
        · exact absurd h ht
      obtain ⟨j, hj, hacc, hlast, hfv⟩ := ih hL
      refine ⟨j, by simp; omega, by simpa [List.getElem_append_left hj] using hacc, ?_, ?_⟩
      · intro j'' h1 h2
        simp only [List.length_append, List.length_singleton] at h2
        rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
        · simpa [List.getElem_append_left h2] using hlast j'' h1 h2
        · simpa using ht
      · rw [finalVal_append_of_not_accesses ht, hfv]
        simp [List.getElem_append_left hj]

/-- **Proposition 25 (i)** of Cerone–Gotsman: the concatenation of `ts` reads `n` from `x` iff the
first transaction of `ts` that accesses `x` reads `n` from it. -/
theorem reads_flatten_iff (ts : List (Txn Obj V)) :
    Txn.Reads ts.flatten x n ↔ ∃ j, ∃ hj : j < ts.length, ts[j].Reads x n ∧
      ∀ j' (hj' : j' < j), ¬ (ts[j']'(by omega)).Accesses x := by
  induction ts with
  | nil => simp [Reads]
  | cons t ts ih =>
    rw [List.flatten_cons, reads_append, ih]
    constructor
    · rintro (hr | ⟨hna, j, hj, hr, hb⟩)
      · exact ⟨0, by simp, by simpa using hr, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
      · refine ⟨j + 1, by simp; omega, by simpa using hr, fun j' hj' => ?_⟩
        cases j' with
        | zero => simpa using hna
        | succ j' => simpa using hb j' (by omega)
    · rintro ⟨j, hj, hr, hb⟩
      cases j with
      | zero => exact Or.inl (by simpa using hr)
      | succ j =>
        exact Or.inr ⟨by simpa using hb 0 (by omega), j, by simpa using hj, by simpa using hr,
          fun j' hj' => by simpa using hb (j' + 1) (by omega)⟩

/-- **Proposition 25 (ii)** of Cerone–Gotsman: the concatenation of `ts` writes `n` to `x` last
iff the last transaction of `ts` that writes `x` writes `n` last. -/
theorem writes_flatten_iff (ts : List (Txn Obj V)) :
    Txn.Writes ts.flatten x n ↔ ∃ j, ∃ hj : j < ts.length, ts[j].Writes x n ∧
      ∀ j' (hj' : j' < ts.length), j < j' → ∀ m, ¬ ts[j'].Writes x m := by
  induction ts using List.reverseRecOn with
  | nil => simp [Writes]
  | append_singleton ts t ih =>
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [writes_append, ih]
    constructor
    · rintro (hw | ⟨⟨j, hj, hw, hb⟩, hnt⟩)
      · exact ⟨ts.length, by simp, by simpa using hw,
          fun j' hj' h1 => by simp at hj'; omega⟩
      · refine ⟨j, by simp; omega, by simpa [List.getElem_append_left hj] using hw, ?_⟩
        intro j' hj' h1
        simp only [List.length_append, List.length_singleton] at hj'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
        · simpa [List.getElem_append_left hj'] using hb j' hj' h1
        · simpa using hnt
    · rintro ⟨j, hj, hw, hb⟩
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · refine Or.inr ⟨⟨j, hj, by simpa [List.getElem_append_left hj] using hw, ?_⟩, ?_⟩
        · intro j' hj' h1
          have := hb j' (by simp; omega) h1
          rwa [List.getElem_append_left hj'] at this
        · simpa using hb ts.length (by simp) hj
      · exact Or.inl (by simpa using hw)

/-- Internal consistency of a concatenation: each transaction is internally consistent, and
whenever `ts[j] ⊢ read(x, n)` and an earlier transaction accesses `x`, the last such transaction
`ts[j']` ends with value `n` on `x`. -/
theorem int_flatten (ts : List (Txn Obj V)) (hint : ∀ j (hj : j < ts.length), ts[j].Int)
    (hrd : ∀ j (hj : j < ts.length) x n, ts[j].Reads x n →
      ∀ j' (hj' : j' < j), (ts[j']'(by omega)).Accesses x →
        (∀ j'' (_h1 : j' < j'') (h2 : j'' < j), ¬ (ts[j'']'(by omega)).Accesses x) →
        (ts[j']'(by omega)).finalVal x = some n) :
    Txn.Int ts.flatten := by
  induction ts using List.reverseRecOn with
  | nil =>
    intro pre suf y k o hT
    simp at hT
  | append_singleton ts t ih =>
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    refine Int.append ?_ ?_ ?_
    · refine ih (fun j hj => ?_) (fun j hj y k hr j' hj' ha hb => ?_)
      · have := hint j (by simp; omega)
        rwa [List.getElem_append_left hj] at this
      · have hj'' : j' < ts.length := by omega
        have := hrd j (by simp; omega) y k (by rwa [List.getElem_append_left hj])
          j' hj' (by rwa [List.getElem_append_left hj''])
          (fun j'' h1 h2 => by rw [List.getElem_append_left (by omega)]; exact hb j'' h1 h2)
        rwa [List.getElem_append_left hj''] at this
    · simpa using hint ts.length (by simp)
    · intro y k hr ha
      obtain ⟨j', hj', hacc, hlast, hfv⟩ := exists_last_accesses ts ha
      rw [hfv]
      have := hrd ts.length (by simp) y k (by simpa using hr) j' hj'
        (by simpa [List.getElem_append_left hj'] using hacc)
        (fun j'' h1 h2 => by simpa [List.getElem_append_left h2] using hlast j'' h1 h2)
      simpa [List.getElem_append_left hj'] using this

end Txn

end Podc.AnalysingSI
