import Papers.PODC2023.MBroadcast.Spec

/-!
# Trace lemmas for Algorithm 2 (MBroadcast on top of SWMR registers)

Two projections of an MBroadcast trace: `bcs tr p`, the messages mbroadcast by `p` (in trace
order), and `dls tr q p`, the messages mdelivered by `q` from `p` (in trace order).

Two trace invariants imply the safety properties of (fifo-)MBroadcast:

* `PrefixInv tr`: in every prefix of the trace, the messages mdelivered by `q` from `p` form a
  prefix of the messages mbroadcast by `p`. With `UniqueBc`, it implies `Validity`,
  `NoDuplication` and `FifoOrdering`.
* `MOInv tr`: when `p` mdelivers its own `m`, it has already mdelivered every message mbroadcast
  by another process before `p` mbroadcast `m`. It implies `MutualOrdering`.
-/

namespace Podc.MBroadcast.FromRegisters

variable {P M : Type} [DecidableEq P] [DecidableEq M]

set_option linter.unusedSectionVars false

/-- The messages mbroadcast by `p`, in trace order. -/
def bcs (tr : List (Ev P M)) (p : P) : List M :=
  tr.filterMap fun
    | .bc q m => if q = p then some m else none
    | .dl .. => none

/-- The messages mdelivered by `q` from `p`, in trace order. -/
def dls (tr : List (Ev P M)) (q p : P) : List M :=
  tr.filterMap fun
    | .bc .. => none
    | .dl q' p' m => if q' = q ∧ p' = p then some m else none

section Proj

variable {tr tr' : List (Ev P M)} {p q : P} {m : M}

@[simp] lemma bcs_nil : bcs ([] : List (Ev P M)) p = [] := rfl
@[simp] lemma dls_nil : dls ([] : List (Ev P M)) q p = [] := rfl

@[simp] lemma bcs_append : bcs (tr ++ tr') p = bcs tr p ++ bcs tr' p := List.filterMap_append
@[simp] lemma dls_append : dls (tr ++ tr') q p = dls tr q p ++ dls tr' q p := List.filterMap_append

@[simp] lemma bcs_cons_bc (q' : P) (m : M) (tr : List (Ev P M)) :
    bcs (.bc q' m :: tr) p = (if q' = p then [m] else []) ++ bcs tr p := by
  by_cases h : q' = p <;> simp [bcs, h]

@[simp] lemma bcs_cons_dl (q' p' : P) (m : M) (tr : List (Ev P M)) :
    bcs (.dl q' p' m :: tr) p = bcs tr p := by
  simp [bcs]

@[simp] lemma dls_cons_bc (q' : P) (m : M) (tr : List (Ev P M)) :
    dls (.bc q' m :: tr) q p = dls tr q p := by
  simp [dls]

@[simp] lemma dls_cons_dl (q' p' : P) (m : M) (tr : List (Ev P M)) :
    dls (.dl q' p' m :: tr) q p = (if q' = q ∧ p' = p then [m] else []) ++ dls tr q p := by
  by_cases h : q' = q ∧ p' = p <;> simp [dls, h]

@[simp] lemma bcs_map_dl (q' p' : P) (L : List M) :
    bcs (L.map (Ev.dl q' p')) p = [] := by
  induction L <;> simp_all

lemma dls_map_dl (q' p' : P) (L : List M) :
    dls (L.map (Ev.dl q' p')) q p = if q' = q ∧ p' = p then L else [] := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : q' = q ∧ p' = p
    · simp_all
    · simp only [List.map_cons, dls_cons_dl, ih, h, ite_false, List.append_nil]

lemma mem_bcs : m ∈ bcs tr p ↔ .bc p m ∈ tr := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc q' m' => by_cases h : q' = p <;> simp [h, ih]; aesop
    | dl q' p' m' => simp [ih]

lemma mem_dls : m ∈ dls tr q p ↔ .dl q p m ∈ tr := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc q' m' => simp [ih]
    | dl q' p' m' => by_cases h : q' = q ∧ p' = p <;> simp [h, ih, eq_comm]; aesop

lemma count_bcs : (bcs tr p).count m = tr.count (.bc p m) := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc q' m' =>
      by_cases h : q' = p
      · subst h; by_cases h' : m' = m <;> simp [h', ih]
      · simp [h, ih]
    | dl q' p' m' => simp [ih]

lemma count_dls : (dls tr q p).count m = tr.count (.dl q p m) := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc q' m' => simp [ih]
    | dl q' p' m' =>
      by_cases h : q' = q ∧ p' = p
      · obtain ⟨rfl, rfl⟩ := h; by_cases h' : m' = m <;> simp [h', ih]
      · simp only [dls_cons_dl, h, ite_false, List.nil_append, ih, List.count_cons]
        simp only [beq_iff_eq, Ev.dl.injEq]; aesop

lemma uniqueBc_iff : UniqueBc tr ↔ ∀ p, (bcs tr p).Nodup := by
  simp only [UniqueBc, List.nodup_iff_count_le_one, count_bcs]

end Proj

/-! ## The prefix invariant -/

/-- In every prefix of the trace, the messages mdelivered by `q` from `p` form a prefix of the
messages mbroadcast by `p`. -/
def PrefixInv (tr : List (Ev P M)) : Prop :=
  ∀ i q p, dls (tr.take i) q p <+: bcs (tr.take i) p

section PrefixInv

variable {tr : List (Ev P M)}

lemma PrefixInv.nil : PrefixInv ([] : List (Ev P M)) := by
  intro i q p; simp

lemma PrefixInv.prefix (h : PrefixInv tr) (q p : P) : dls tr q p <+: bcs tr p := by
  simpa using h tr.length q p

lemma PrefixInv.snoc {e : Ev P M} (h : PrefixInv tr)
    (he : ∀ q p x, e = .dl q p x → dls tr q p ++ [x] <+: bcs tr p) :
    PrefixInv (tr ++ [e]) := by
  intro i q p
  by_cases hi : i ≤ tr.length
  · rw [List.take_append_of_le_length hi]; exact h i q p
  · rw [List.take_of_length_le (by simp; omega)]
    cases e with
    | bc q' m =>
      simpa using (h.prefix q p).trans (List.prefix_append _ _)
    | dl q' p' x =>
      by_cases hqp : q' = q ∧ p' = p
      · obtain ⟨rfl, rfl⟩ := hqp; simpa using he q' p' x rfl
      · simpa [hqp] using h.prefix q p

lemma PrefixInv.append_map_dl {q p : P} {L : List M} (h : PrefixInv tr)
    (hL : dls tr q p ++ L <+: bcs tr p) : PrefixInv (tr ++ L.map (Ev.dl q p)) := by
  induction L generalizing tr with
  | nil => simpa using h
  | cons a L ih =>
    have h1 : PrefixInv (tr ++ [Ev.dl q p a]) := by
      refine h.snoc fun q' p' x he => ?_
      simp only [Ev.dl.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact (List.prefix_append (dls tr q p ++ [a]) L).trans (by simpa using hL)
    have := ih h1 (by simpa using hL)
    simpa using this

lemma PrefixInv.validity (h : PrefixInv tr) : Validity tr := by
  intro i p q m hi
  have hil : i < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have ht : tr.take (i + 1) = tr.take i ++ [.dl p q m] := by
    rw [List.take_add_one, hi]; rfl
  have := h (i + 1) p q
  rw [ht] at this
  simp only [dls_append, bcs_append, dls_cons_dl, and_self, ite_true, dls_nil, bcs_cons_dl,
    bcs_nil, List.append_nil] at this
  rw [← mem_bcs]
  exact this.subset (by simp)

lemma PrefixInv.noDup (h : PrefixInv tr) (hu : UniqueBc tr) : NoDuplication tr := by
  intro q p m
  rw [← count_dls]
  exact ((h.prefix q p).sublist.count_le m).trans (by rw [count_bcs]; exact hu p m)

/-- In a duplicate-free list, the prefix that ends with a given element is unique. -/
lemma eq_of_prefix_of_nodup {α : Type} {B D X : List α} {a : α} (hB : B.Nodup)
    (hD : D ++ [a] <+: B) (hX : X ++ [a] <+: B) : D = X := by
  -- CSLib candidate (list lemma)
  obtain ⟨Z, hZ⟩ := hD
  obtain ⟨Y, hY⟩ := hX
  subst hZ
  have key : ∀ {D X Z Y : List α}, (D ++ [a] ++ Z).Nodup → D ++ [a] ++ Z = X ++ [a] ++ Y →
      D.length ≤ X.length → D = X := by
    intro D X Z Y hB hY hle
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exfalso
      -- `a` occurs at positions `D.length` and `X.length`
      have h1 : (D ++ [a] ++ Z)[D.length]? = some a := by simp
      have h2 : (D ++ [a] ++ Z)[X.length]? = some a := by rw [hY]; simp
      have hn := List.nodup_iff_injective_get.1 hB
      have hX' : X.length < (D ++ [a] ++ Z).length := by
        rw [hY]; simp
      have := @hn ⟨D.length, by simp⟩ ⟨X.length, hX'⟩ (by
        simp only [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem (by simp)] at h1
        rw [List.getElem?_eq_getElem hX'] at h2
        simp only [Option.some.injEq] at h1 h2; rw [h1, h2])
      simp only [Fin.mk.injEq] at this; omega
    · have := congrArg (List.take D.length) hY
      simp only [List.append_assoc, List.take_left', heq] at this
      exact this
  rcases le_total D.length X.length with hle | hle
  · exact key hB hY.symm hle
  · exact (key (hY ▸ hB) hY hle).symm

lemma PrefixInv.fifo (h : PrefixInv tr) (hu : UniqueBc tr) : FifoOrdering tr := by
  intro p m m' i j hi hj hij q k hk
  obtain ⟨j', hj'k, hj'⟩ := exists_lt_of_mem_take (h.validity k q p m' hk)
  have hjj := eq_of_count_le_one (hu p m') hj' hj
  subst hjj
  have hkl : k < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hk; cases hk
  -- the prefix `tr.take (k+1)`
  have ht : tr.take (k + 1) = tr.take k ++ [.dl q p m'] := by
    rw [List.take_add_one, hk]; rfl
  have hpre := h (k + 1) q p
  rw [ht] at hpre
  simp only [dls_append, bcs_append, dls_cons_dl, and_self, ite_true, dls_nil, bcs_cons_dl,
    bcs_nil, List.append_nil] at hpre
  -- `bcs (tr.take k) p = bcs (tr.take j') p ++ [m'] ++ _`
  have htk : tr.take k = tr.take j' ++ [.bc p m'] ++ (tr.take k).drop (j' + 1) := by
    have h1 : (tr.take k).take (j' + 1) = tr.take j' ++ [.bc p m'] := by
      rw [List.take_take, min_eq_left (by omega), List.take_add_one, hj']; rfl
    rw [← h1, List.take_append_drop]
  have hnd : (bcs (tr.take k) p).Nodup := by
    rw [List.nodup_iff_count_le_one]; intro x
    rw [count_bcs]
    exact ((List.take_sublist k tr).count_le _).trans (hu p x)
  have hX : bcs (tr.take j') p ++ [m'] <+: bcs (tr.take k) p := by
    rw [htk]; simp only [bcs_append, bcs_cons_bc, ite_true, bcs_nil, List.append_nil]
    exact List.prefix_append _ _
  have hDX := eq_of_prefix_of_nodup hnd hpre hX
  rw [← mem_dls, hDX, mem_bcs]
  exact mem_take_of_getElem? hi hij

end PrefixInv

/-! ## The mutual-ordering invariant -/

/-- When `p` mdelivers its own `m` (position `i`), it has already mdelivered every message
mbroadcast by another process before `p` mbroadcast `m` (position `b`). -/
def MOInv (tr : List (Ev P M)) : Prop :=
  ∀ i p m, tr[i]? = some (.dl p p m) → ∃ b, tr[b]? = some (.bc p m) ∧
    ∀ q, q ≠ p → ∀ m', .bc q m' ∈ tr.take b → .dl p q m' ∈ tr.take i

section MOInv

variable {tr : List (Ev P M)}

lemma MOInv.nil : MOInv ([] : List (Ev P M)) := by
  intro i p m h; simp at h

lemma MOInv.append {L : List (Ev P M)} (h : MOInv tr)
    (hL : ∀ p m, .dl p p m ∈ L → ∃ b, tr[b]? = some (.bc p m) ∧
      ∀ q, q ≠ p → ∀ m', .bc q m' ∈ tr.take b → .dl p q m' ∈ tr) :
    MOInv (tr ++ L) := by
  intro i p m hi
  have hb_left : ∀ {b : ℕ} {e : Ev P M}, tr[b]? = some e → (tr ++ L)[b]? = some e ∧
      (tr ++ L).take b = tr.take b := by
    intro b e hb
    have hbl : b < tr.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
    exact ⟨by rw [List.getElem?_append_left hbl]; exact hb,
      List.take_append_of_le_length hbl.le⟩
  by_cases hil : i < tr.length
  · rw [List.getElem?_append_left hil] at hi
    obtain ⟨b, hb, hb'⟩ := h i p m hi
    refine ⟨b, (hb_left hb).1, ?_⟩
    intro q hq m' hm'
    rw [(hb_left hb).2] at hm'
    rw [List.take_append_of_le_length hil.le]
    exact hb' q hq m' hm'
  · rw [List.getElem?_append_right (by omega)] at hi
    obtain ⟨b, hb, hb'⟩ := hL p m (List.mem_of_getElem? hi)
    refine ⟨b, (hb_left hb).1, ?_⟩
    intro q hq m' hm'
    rw [(hb_left hb).2] at hm'
    rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.mem_append_left _ (hb' q hq m' hm')

lemma MOInv.mutualOrdering (h : MOInv tr) : MutualOrdering tr := by
  rintro p m p' m' hne ⟨⟨i, hi, hi'⟩, ⟨i', hi2, hi2'⟩⟩
  by_cases hpp : p = p'
  · subst hpp
    have hmm : m ≠ m' := fun h => hne (by rw [h])
    exact not_delivBefore_same hmm ⟨⟨i, hi, hi'⟩, ⟨i', hi2, hi2'⟩⟩
  obtain ⟨b, hb, hb'⟩ := h i p m hi
  obtain ⟨b', hb2, hb2'⟩ := h i' p' m' hi2
  have h1 : Ev.bc p' m' ∉ tr.take b := fun hm => hi' (hb' p' (Ne.symm hpp) m' hm)
  have h2 : Ev.bc p m ∉ tr.take b' := fun hm => hi2' (hb2' p hpp m hm)
  rcases lt_trichotomy b b' with hlt | heq | hlt
  · exact h2 (mem_take_of_getElem? hb hlt)
  · subst heq; rw [hb] at hb2; simp only [Option.some.injEq, Ev.bc.injEq] at hb2
    exact hpp hb2.1
  · exact h1 (mem_take_of_getElem? hb2 hlt)

end MOInv

end Podc.MBroadcast.FromRegisters
