import Papers.PODC2014.EventualLinParadox.Defs

/-!
# Basic properties of `t`-linearizability and weak consistency (Section 3.2)

* `IsTLin.mono`, `TLinearizable.mono` — **Lemma 5**.
* `TLinearizable.prefix` — **Lemma 6** (prefixes), for types with total operations.
* `tLinearizable_take_self` — a finite history is `t`-linearizable when `t` is its length.
* `weaklyConsistent_isSafety` — **Lemma 10** (weak consistency is a safety property).
* `Legal.extend` — appending operations with responses chosen by a total specification.
-/

namespace Podc.EventualLinParadox

variable {P X Op Res Q : Type}

section Lemma5

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

/-- **Lemma 5.** A `t`-linearization is a `t'`-linearization for every `t' ≥ t`. -/
lemma IsTLin.mono {t t' : ℕ} {S : SeqHist Res} (h : IsTLin spec H t S) (htt' : t ≤ t') :
    IsTLin spec H t' S where
  nodup := h.nodup
  legal := h.legal
  complete := h.complete
  rt a b j r hj htj := h.rt a b j r hj (htt'.trans htj)
  resp a j r hj htj := h.resp a j r hj (htt'.trans htj)

/-- **Lemma 5.** If `H` is `t`-linearizable then it is `t'`-linearizable for any `t' > t`. -/
theorem TLinearizable.mono {t t' : ℕ} (h : TLinearizable spec H t) (htt' : t ≤ t') :
    TLinearizable spec H t' :=
  let ⟨S, hS⟩ := h; ⟨S, hS.mono htt'⟩

end Lemma5

section Take

variable (H : History P X Op Res)

lemma take_apply {m i : ℕ} : take H m i = if i < m then H i else none := rfl

lemma take_of_lt {m i : ℕ} (h : i < m) : take H m i = H i := ite_eq_left h

lemma take_of_le {m i : ℕ} (h : m ≤ i) : take H m i = none := ite_eq_right (by omega)

lemma take_eq_some {m i : ℕ} {e : Ev P X Op Res} : take H m i = some e ↔ i < m ∧ H i = some e := by
  unfold take; split_ifs with h <;> simp [h]

lemma invoked_take {m a : ℕ} : Invoked (take H m) a ↔ a < m ∧ Invoked H a := by
  simp only [Invoked, take_eq_some]; constructor
  · rintro ⟨p, x, op, h1, h2⟩; exact ⟨h1, p, x, op, h2⟩
  · rintro ⟨h1, p, x, op, h2⟩; exact ⟨p, x, op, h1, h2⟩

lemma onObj_take {m a : ℕ} {x : X} (ha : a < m) : OnObj (take H m) x a ↔ OnObj H x a := by
  simp [OnObj, take_of_lt H ha]

lemma wellFormed_take {H : History P X Op Res} (h : WellFormed H) (m : ℕ) :
    WellFormed (take H m) where
  res_inv a j r hj := by
    rw [take_eq_some] at hj
    obtain ⟨h1, h2⟩ := h.res_inv a j r hj.2
    exact ⟨h1, (invoked_take H).2 ⟨by omega, h2⟩⟩
  res_unique a j j' r r' hj hj' := by
    rw [take_eq_some] at hj hj'; exact h.res_unique a j j' r r' hj.2 hj'.2
  seq a b p x x' op op' ha hb hab := by
    rw [take_eq_some] at ha hb
    obtain ⟨j, r, hj, hjr⟩ := h.seq a b p x x' op op' ha.2 hb.2 hab
    exact ⟨j, r, hj, (take_eq_some H).2 ⟨by omega, hjr⟩⟩

end Take

section Legal

variable {spec : X → ObjType Q Op Res}

/-- Legality only depends on the invocations of the operations of `S`. -/
lemma Legal.congr {H H' : History P X Op Res} {S : SeqHist Res} (h : Legal spec H S)
    (hHH' : ∀ k a r, S k = some (a, r) → H' a = H a) : Legal spec H' S := by
  obtain ⟨hinv, hq⟩ := h
  refine ⟨fun k a r hk => ?_, fun x => ?_⟩
  · obtain ⟨p, x, op, h⟩ := hinv k a r hk; exact ⟨p, x, op, (hHH' k a r hk).trans h⟩
  · obtain ⟨q, hq0, hqs⟩ := hq x
    refine ⟨q, hq0, fun k => ?_⟩
    have := hqs k
    cases hk : S k with
    | none => simpa [SeqStep, hk] using this
    | some e =>
      obtain ⟨a, r⟩ := e
      rw [hk] at this
      simpa [SeqStep, OnObj, hHH' k a r hk] using this

lemma SeqStep.onObj {T : ObjType Q Op Res} {H : History P X Op Res} {x : X} {a : ℕ} {r : Res}
    {q q' : Q} (h : SeqStep T H x (some (a, r)) q q') (hx : OnObj H x a) :
    ∃ p op, H a = some (.inv p x op) ∧ T.δ q op r q' := by
  rcases h with h | h
  · exact h
  · exact absurd hx h.1

lemma SeqStep.not_onObj {T : ObjType Q Op Res} {H : History P X Op Res} {x : X} {a : ℕ} {r : Res}
    {q q' : Q} (h : SeqStep T H x (some (a, r)) q q') (hx : ¬ OnObj H x a) : q' = q := by
  rcases h with ⟨p, op, h1, -⟩ | h
  · exact absurd ⟨p, op, h1⟩ hx
  · exact h.2

lemma onObj_unique {H : History P X Op Res} {x y : X} {a : ℕ} (hx : OnObj H x a)
    (hy : OnObj H y a) : x = y := by
  obtain ⟨p, op, h⟩ := hx; obtain ⟨p', op', h'⟩ := hy
  rw [h] at h'; cases h'; rfl

/-- The sequential history `S` truncated to its positions `< K`. -/
def SeqHist.trunc (S : SeqHist Res) (K : ℕ) : SeqHist Res := fun k => if k < K then S k else none

lemma Legal.trunc {H : History P X Op Res} {S : SeqHist Res} (h : Legal spec H S) (K : ℕ) :
    Legal spec H (S.trunc K) := by
  obtain ⟨hinv, hq⟩ := h
  refine ⟨fun k a r hk => ?_, fun x => ?_⟩
  · unfold SeqHist.trunc at hk; split_ifs at hk; exact hinv k a r hk
  · obtain ⟨q, hq0, hqs⟩ := hq x
    refine ⟨fun k => q (min k K), by simpa using hq0, fun k => ?_⟩
    unfold SeqHist.trunc
    dsimp only
    split_ifs with hk
    · rw [min_eq_left hk.le, min_eq_left (by omega)]; exact hqs k
    · rw [min_eq_right (by omega), min_eq_right (by omega)]; rfl

/-- Appending one operation at an empty tail of a legal sequential history, with a response
chosen by a total specification. -/
lemma Legal.snoc {H : History P X Op Res} (hT : ∀ x, (spec x).Total) {S : SeqHist Res}
    (h : Legal spec H S) {K : ℕ} (hK : ∀ k, K ≤ k → S k = none) {a : ℕ} (ha : Invoked H a) :
    ∃ r, Legal spec H (Function.update S K (some (a, r))) := by
  classical
  obtain ⟨p, x, op, hax⟩ := ha
  obtain ⟨hinv, hq⟩ := h
  obtain ⟨q, hq0, hqs⟩ := hq x
  obtain ⟨r, q', hδ⟩ := hT x (q K) op
  refine ⟨r, fun k a' r' hk => ?_, fun y => ?_⟩
  · rw [Function.update_apply] at hk
    split_ifs at hk
    · cases hk; exact ⟨p, x, op, hax⟩
    · exact hinv k a' r' hk
  · by_cases hy : y = x
    · subst hy
      refine ⟨fun k => if k ≤ K then q k else q', by simpa using hq0, fun k => ?_⟩
      rw [Function.update_apply]
      dsimp only
      by_cases h1 : k = K
      · subst h1; rw [if_pos rfl, ite_eq_left le_rfl, ite_eq_right (by omega)]
        exact Or.inl ⟨p, op, hax, hδ⟩
      · rw [if_neg h1]
        by_cases h2 : k < K
        · rw [ite_eq_left h2.le, ite_eq_left (by omega)]; exact hqs k
        · rw [hK k (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; rfl
    · obtain ⟨qy, hqy0, hqys⟩ := hq y
      have hny : ¬ OnObj H y a := fun h => hy (onObj_unique h ⟨p, op, hax⟩)
      refine ⟨fun k => qy (min k K), by simpa using hqy0, fun k => ?_⟩
      rw [Function.update_apply]
      dsimp only
      split_ifs with h1
      · subst h1
        rw [min_eq_left le_rfl, min_eq_right (by omega)]
        exact Or.inr ⟨hny, rfl⟩
      · by_cases hk : k < K
        · rw [min_eq_left hk.le, min_eq_left (by omega)]; exact hqys k
        · rw [hK k (by omega), min_eq_right (by omega), min_eq_right (by omega)]; rfl

/-- The sequential history `S` (on positions `< K`) followed by the entries of `L`. -/
def SeqHist.appendList (S : SeqHist Res) (K : ℕ) (L : List (ℕ × Res)) : SeqHist Res :=
  fun k => if k < K then S k else L[k - K]?

/-- Appending a list of operations of `H` to a legal sequential history, with responses chosen
by a total specification. -/
lemma Legal.extend {H : History P X Op Res} (hT : ∀ x, (spec x).Total) (L : List ℕ)
    (hL : ∀ a ∈ L, Invoked H a) :
    ∀ {S : SeqHist Res} {K : ℕ}, Legal spec H S → (∀ k, K ≤ k → S k = none) →
      ∃ L' : List (ℕ × Res), L'.map Prod.fst = L ∧ Legal spec H (S.appendList K L') := by
  classical
  induction L with
  | nil =>
    intro S K hS hK
    refine ⟨[], rfl, ?_⟩
    have : S.appendList K [] = S := by
      funext k; unfold SeqHist.appendList; split_ifs with h
      · rfl
      · simp [hK k (by omega)]
    rw [this]; exact hS
  | cons a L ih =>
    intro S K hS hK
    obtain ⟨r, hr⟩ := hS.snoc hT hK (hL a (by simp))
    have hK1 : ∀ k, K + 1 ≤ k → Function.update S K (some (a, r)) k = none := fun k hk => by
      rw [Function.update_of_ne (by omega)]; exact hK k (by omega)
    obtain ⟨L', hL', hleg⟩ := ih (fun b hb => hL b (by simp [hb])) hr hK1
    refine ⟨(a, r) :: L', by simp [hL'], ?_⟩
    convert hleg using 1
    funext k
    unfold SeqHist.appendList
    rcases lt_trichotomy k K with h | h | h
    · rw [ite_eq_left h, ite_eq_left (by omega), Function.update_of_ne (by omega)]
    · subst h; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      obtain ⟨i, rfl⟩ : ∃ i, k = K + 1 + i := ⟨k - K - 1, by omega⟩
      rw [show K + 1 + i - K = i + 1 by omega, show K + 1 + i - (K + 1) = i by omega]
      simp

lemma appendList_of_lt {S : SeqHist Res} {K k : ℕ} {L' : List (ℕ × Res)} (h : k < K) :
    S.appendList K L' k = S k := ite_eq_left h

lemma appendList_of_ge {S : SeqHist Res} {K k : ℕ} {L' : List (ℕ × Res)} (h : K ≤ k) :
    S.appendList K L' k = L'[k - K]? := ite_eq_right (by omega)

lemma mem_appendList {S : SeqHist Res} {K : ℕ} {L' : List (ℕ × Res)}
    (hK : ∀ k, K ≤ k → S k = none) {a : ℕ} :
    (S.appendList K L').Mem a ↔ S.Mem a ∨ a ∈ L'.map Prod.fst := by
  constructor
  · rintro ⟨k, r, hk⟩
    by_cases h : k < K
    · rw [appendList_of_lt h] at hk; exact Or.inl ⟨k, r, hk⟩
    · rw [appendList_of_ge (by omega)] at hk
      exact Or.inr (List.mem_map.2 ⟨(a, r), List.mem_of_getElem? hk, rfl⟩)
  · rintro (⟨k, r, hk⟩ | h)
    · have : k < K := by by_contra h'; rw [hK k (by omega)] at hk; cases hk
      exact ⟨k, r, by rw [appendList_of_lt this]; exact hk⟩
    · obtain ⟨⟨a', r⟩, he, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
      refine ⟨K + i, r, ?_⟩
      rw [appendList_of_ge (by omega), show K + i - K = i by omega, List.getElem?_eq_getElem hi, hie]

lemma nodup_appendList {S : SeqHist Res} {K : ℕ} {L' : List (ℕ × Res)} (hS : S.Nodup)
    (hK : ∀ k, K ≤ k → S k = none) (hL : (L'.map Prod.fst).Nodup)
    (hdis : ∀ e ∈ L', ¬ S.Mem e.1) : (S.appendList K L').Nodup := by
  intro k k' a r r' hk hk'
  by_cases h1 : k < K <;> by_cases h2 : k' < K
  · rw [appendList_of_lt h1] at hk; rw [appendList_of_lt h2] at hk'; exact hS k k' a r r' hk hk'
  · rw [appendList_of_lt h1] at hk; rw [appendList_of_ge (by omega)] at hk'
    exact absurd ⟨k, r, hk⟩ (hdis _ (List.mem_of_getElem? hk'))
  · rw [appendList_of_lt h2] at hk'; rw [appendList_of_ge (by omega)] at hk
    exact absurd ⟨k', r', hk'⟩ (hdis _ (List.mem_of_getElem? hk))
  · rw [appendList_of_ge (by omega)] at hk hk'
    have e1 : (L'.map Prod.fst)[k - K]? = some a := by simp [hk]
    have e2 : (L'.map Prod.fst)[k' - K]? = some a := by simp [hk']
    have hlt : k - K < (L'.map Prod.fst).length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at e1; cases e1
    have := hL.eq_of_getElem?_eq hlt (e1.trans e2.symm)
    omega

end Legal

section Lemma6

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

lemma SeqHist.Nodup.trunc {S : SeqHist Res} (h : S.Nodup) (K : ℕ) : (S.trunc K).Nodup := by
  intro k k' a r r' hk hk'
  unfold SeqHist.trunc at hk hk'
  split_ifs at hk hk'
  exact h k k' a r r' hk hk'

lemma trunc_of_ge {S : SeqHist Res} {K k : ℕ} (h : K ≤ k) : S.trunc K k = none :=
  ite_eq_right (by omega)

lemma trunc_of_lt {S : SeqHist Res} {K k : ℕ} (h : k < K) : S.trunc K k = S k := ite_eq_left h

lemma legal_empty (hI : ∀ x, (spec x).init.Nonempty) {H : History P X Op Res} :
    Legal spec H (fun _ => none) := by
  refine ⟨fun _ _ _ h => (by cases h), fun x => ?_⟩
  obtain ⟨q₀, hq₀⟩ := hI x
  exact ⟨fun _ => q₀, hq₀, fun _ => rfl⟩

/-- The completed operations of a prefix, as a list. -/
noncomputable def completedList (H : History P X Op Res) (m : ℕ) (Excl : ℕ → Prop) : List ℕ := by
  classical
  exact ((Finset.range m).filter fun c => Completed (take H m) c ∧ ¬ Excl c).toList

lemma mem_completedList {m : ℕ} {Excl : ℕ → Prop} {c : ℕ} :
    c ∈ completedList H m Excl ↔ c < m ∧ Completed (take H m) c ∧ ¬ Excl c := by
  classical
  simp [completedList]

lemma completedList_nodup {m : ℕ} {Excl : ℕ → Prop} : (completedList H m Excl).Nodup := by
  classical
  simp [completedList, Finset.nodup_toList]

lemma completed_take_lt (hH : WellFormed H) {m c : ℕ} (h : Completed (take H m) c) :
    c < m ∧ Invoked H c := by
  obtain ⟨j, r, hj⟩ := h
  rw [take_eq_some] at hj
  obtain ⟨h1, h2⟩ := hH.res_inv c j r hj.2
  exact ⟨by omega, h2⟩

/-- Every finite prefix ending at `t` is trivially `t`-linearizable (for total specifications):
any order of its completed operations, with responses chosen by the specification, is a
`t`-linearization. This is the paper's remark that "a prefix of `H` of length at most `t` is
trivially `t`-linearizable" and that being `t`-linearizable for some `t` is a liveness
property. -/
theorem tLinearizable_take_self (hI : ∀ x, (spec x).init.Nonempty) (hT : ∀ x, (spec x).Total)
    (hH : WellFormed H) (t : ℕ) : TLinearizable spec (take H t) t := by
  classical
  set L := completedList H t (fun _ => False)
  have hL : ∀ a ∈ L, Invoked (take H t) a := fun a ha => by
    obtain ⟨h1, h2, -⟩ := mem_completedList.1 ha
    exact (invoked_take H).2 ⟨h1, (completed_take_lt hH h2).2⟩
  obtain ⟨L', hL', hleg⟩ := Legal.extend hT L hL (legal_empty hI (H := take H t)) (K := 0)
    (fun _ _ => rfl)
  refine ⟨_, ⟨nodup_appendList (fun _ _ _ _ _ h => by cases h) (fun _ _ => rfl)
    (by rw [hL']; exact completedList_nodup) (fun _ _ ⟨_, _, h⟩ => by cases h), hleg,
    fun a j r hj => ?_, fun a b j r hj htj => ?_, fun a j r hj htj => ?_⟩⟩
  · rw [mem_appendList (fun _ _ => rfl), hL']
    right
    exact mem_completedList.2 ⟨(completed_take_lt hH ⟨j, r, hj⟩).1, ⟨j, r, hj⟩, id⟩
  · rw [take_eq_some] at hj; omega
  · rw [take_eq_some] at hj; omega

/-- **Lemma 6.** If `H` is `t`-linearizable then so is every prefix of `H` (for types with
total operations; the paper's proof completes operations "with the responses they would have
if executed in that order", which needs totality). -/
theorem TLinearizable.prefix (hT : ∀ x, (spec x).Total) (hH : WellFormed H) {t : ℕ}
    (h : TLinearizable spec H t) (m : ℕ) : TLinearizable spec (take H m) t := by
  classical
  obtain ⟨S, hS⟩ := h
  -- the operations with a response in `[t, m)`
  let R : ℕ → Prop := fun a => ∃ j r, H j = some (.res a r) ∧ t ≤ j ∧ j < m
  have hbound : ∀ n, ∃ K, ∀ a j r, H j = some (.res a r) → t ≤ j → j < n →
      ∃ k < K, S k = some (a, r) := by
    intro n
    induction n with
    | zero => exact ⟨0, fun a j r _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨K, hK⟩ := ih
      by_cases hn : ∃ a r, H n = some (.res a r) ∧ t ≤ n
      · obtain ⟨a₀, r₀, hn1, hn2⟩ := hn
        obtain ⟨k₀, hk₀⟩ := hS.resp a₀ n r₀ hn1 hn2
        refine ⟨max K (k₀ + 1), fun a j r hj htj hjn => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with h | h
        · obtain ⟨k, hk, hk'⟩ := hK a j r hj htj h; exact ⟨k, by omega, hk'⟩
        · subst h; rw [hn1] at hj; cases hj; exact ⟨k₀, by omega, hk₀⟩
      · refine ⟨K, fun a j r hj htj hjn => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with h | h
        · exact hK a j r hj htj h
        · subst h; exact absurd ⟨a, r, hj, htj⟩ hn
  have hex : ∃ K, ∀ a j r, H j = some (.res a r) → t ≤ j → j < m → ∃ k < K, S k = some (a, r) :=
    hbound m
  set K := Nat.find hex with hKdef
  have hKspec := Nat.find_spec hex
  -- positions of late-responding operations are `< K`
  have hpos : ∀ a j r k r', H j = some (.res a r) → t ≤ j → j < m → S k = some (a, r') →
      k < K ∧ r' = r := by
    intro a j r k r' hj htj hjm hk
    obtain ⟨k', hk'K, hk'⟩ := hKspec a j r hj htj hjm
    have := hS.nodup k k' a r' r hk hk'
    subst this; rw [hk] at hk'; cases hk'; exact ⟨hk'K, rfl⟩
  -- the last position `K - 1` holds a late-responding operation
  have hlast : 0 < K → ∃ a j r, H j = some (.res a r) ∧ t ≤ j ∧ j < m ∧ S (K - 1) = some (a, r) := by
    intro hK0
    have hmin := Nat.find_min hex (show K - 1 < K by omega)
    push_neg at hmin
    obtain ⟨a, j, r, hj, htj, hjm, hno⟩ := hmin
    obtain ⟨k, hkK, hk⟩ := hKspec a j r hj htj hjm
    have : k = K - 1 := by
      by_contra hne; exact hno k (by omega) hk
    exact ⟨a, j, r, hj, htj, hjm, this ▸ hk⟩
  -- the entries of `S.trunc K` are invoked before `m`
  have hentries : ∀ k c r, S.trunc K k = some (c, r) → c < m := by
    intro k c r hk
    have hkK : k < K := by
      by_contra h; rw [trunc_of_ge (by omega)] at hk; cases hk
    rw [trunc_of_lt hkK] at hk
    obtain ⟨a, j, ra, hj, htj, hjm, ha⟩ := hlast (by omega)
    by_cases hca : c = a
    · subst hca; have := (hH.res_inv c j ra hj).1; omega
    · by_contra hcm; push_neg at hcm
      have hcinv : Invoked H c := hS.legal.1 k c r hk
      obtain ⟨k1, k2, r1, r2, hk12, h1, h2⟩ := hS.rt a c j ra hj htj (by omega) hcinv ⟨k, r, hk⟩
      have e1 := hS.nodup k1 (K-1) a r1 ra h1 ha
      have e2 := hS.nodup k2 k c r2 r h2 hk
      have : k ≠ K - 1 := fun h => hca (by subst h; rw [hk] at ha; cases ha; rfl)
      omega
  set S1 := S.trunc K with hS1
  have hS1K : ∀ k, K ≤ k → S1 k = none := fun k hk => trunc_of_ge hk
  have hS1leg : Legal spec (take H m) S1 :=
    (hS.legal.trunc K).congr (fun k a r hk => take_of_lt H (hentries k a r hk))
  set L := completedList H m (fun c => S1.Mem c) with hLdef
  have hL : ∀ a ∈ L, Invoked (take H m) a := fun a ha => by
    obtain ⟨h1, h2, -⟩ := mem_completedList.1 ha
    exact (invoked_take H).2 ⟨h1, (completed_take_lt hH h2).2⟩
  obtain ⟨L', hL', hleg⟩ := Legal.extend hT L hL hS1leg hS1K
  refine ⟨S1.appendList K L', nodup_appendList (hS.nodup.trunc K) hS1K
    (by rw [hL']; exact completedList_nodup) (fun e he => ?_), hleg, fun a j r hj => ?_,
    fun a b j r hj htj hjb hbinv hbmem => ?_, fun a j r hj htj => ?_⟩
  · have : e.1 ∈ L := hL' ▸ List.mem_map.2 ⟨e, he, rfl⟩
    exact (mem_completedList.1 this).2.2
  · rw [mem_appendList hS1K, hL']
    by_cases hm : S1.Mem a
    · exact Or.inl hm
    · exact Or.inr (mem_completedList.2 ⟨(completed_take_lt hH ⟨j, r, hj⟩).1, ⟨j, r, hj⟩, hm⟩)
  · rw [take_eq_some] at hj
    obtain ⟨ka, hkaK, hka⟩ := hKspec a j r hj.2 htj hj.1
    obtain ⟨kb, rb, hkb⟩ := hbmem
    by_cases hkbK : kb < K
    · rw [appendList_of_lt hkbK, hS1, trunc_of_lt hkbK] at hkb
      obtain ⟨k1, k2, r1, r2, hk12, h1, h2⟩ :=
        hS.rt a b j r hj.2 htj hjb ((invoked_take H).1 hbinv).2 ⟨kb, rb, hkb⟩
      have e1 := hS.nodup k1 ka a r1 r h1 hka
      have e2 := hS.nodup k2 kb b r2 rb h2 hkb
      refine ⟨ka, kb, r, rb, by omega, ?_, ?_⟩
      · rw [appendList_of_lt hkaK, hS1, trunc_of_lt hkaK, hka]
      · rw [appendList_of_lt hkbK, hS1, trunc_of_lt hkbK, hkb]
    · refine ⟨ka, kb, r, rb, by omega, ?_, hkb⟩
      rw [appendList_of_lt hkaK, hS1, trunc_of_lt hkaK, hka]
  · rw [take_eq_some] at hj
    obtain ⟨ka, hkaK, hka⟩ := hKspec a j r hj.2 htj hj.1
    exact ⟨ka, by rw [appendList_of_lt hkaK, hS1, trunc_of_lt hkaK, hka]⟩
end Lemma6

section Lemma10

variable {spec : X → ObjType Q Op Res} {H : History P X Op Res}

/-- A **safety property** (of well-formed histories): non-empty, prefix-closed, limit-closed. -/
def IsSafety (Φ : History P X Op Res → Prop) : Prop :=
  (∃ H, WellFormed H ∧ Φ H) ∧ (∀ H, WellFormed H → Φ H → ∀ m, Φ (take H m)) ∧
  (∀ H, WellFormed H → (∀ m, Φ (take H m)) → Φ H)

/-- A **liveness property**: every finite (well-formed) history is a prefix of a history in the
set. -/
def IsLiveness (Φ : History P X Op Res → Prop) : Prop :=
  ∀ H, WellFormed H → ∀ m, ∃ H', WellFormed H' ∧ take H' m = take H m ∧ Φ H'

lemma take_take (H : History P X Op Res) (m : ℕ) : take (take H m) m = take H m := by
  funext i; simp only [take_apply]; split_ifs <;> rfl

lemma WeaklyConsistent.take (h : WeaklyConsistent spec H) (m : ℕ) :
    WeaklyConsistent spec (take H m) := by
  intro a j r hj
  rw [take_eq_some] at hj
  obtain ⟨S, hnd, hleg, hlt, hproc, hend⟩ := h a j r hj.2
  refine ⟨S, hnd, hleg.congr (fun k b rb hk => take_of_lt H (by
    have := hlt b ⟨k, rb, hk⟩; omega)), hlt, fun b hb hpre => hproc b ?_ ?_, hend⟩
  · obtain ⟨p, x, x', op, op', h1, h2⟩ := hb
    rw [take_eq_some] at h1 h2
    exact ⟨p, x, x', op, op', h1.2, h2.2⟩
  · obtain ⟨j', r', h1, h2, h3⟩ := hpre
    rw [take_eq_some] at h1
    exact ⟨j', r', h1.2, h2, ((invoked_take H).1 h3).2⟩

lemma weaklyConsistent_of_take (hH : WellFormed H) (h : ∀ m, WeaklyConsistent spec (take H m)) :
    WeaklyConsistent spec H := by
  intro a j r hj
  have haj := (hH.res_inv a j r hj).1
  obtain ⟨S, hnd, hleg, hlt, hproc, hend⟩ :=
    h (j + 1) a j r (by rw [take_eq_some]; exact ⟨by omega, hj⟩)
  refine ⟨S, hnd, hleg.congr (fun k b rb hk => (take_of_lt H (by
    have := hlt b ⟨k, rb, hk⟩; omega)).symm), hlt, fun b hb hpre => hproc b ?_ ?_, hend⟩
  · obtain ⟨j', r', h1, h2, h3⟩ := hpre
    have := (hH.res_inv b j' r' h1).1
    obtain ⟨p, x, x', op, op', h4, h5⟩ := hb
    exact ⟨p, x, x', op, op', by rw [take_of_lt H (by omega)]; exact h4,
      by rw [take_of_lt H (by omega)]; exact h5⟩
  · obtain ⟨j', r', h1, h2, h3⟩ := hpre
    exact ⟨j', r', by rw [take_of_lt H (by omega)]; exact h1, h2,
      (invoked_take H).2 ⟨by omega, h3⟩⟩

/-- **Lemma 10.** Weak consistency is a safety property. -/
theorem weaklyConsistent_isSafety : IsSafety (WeaklyConsistent spec (P := P)) := by
  refine ⟨⟨fun _ => none, ⟨fun _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h),
    fun _ _ _ _ _ _ _ h => (by cases h)⟩, fun _ _ _ h => (by cases h)⟩, fun H _ h m => h.take m,
    fun H hH h => weaklyConsistent_of_take hH h⟩

/-- Section 3.2: being `t`-linearizable for some `t` is a liveness property (for types with
total operations and initial states). -/
theorem exists_tLinearizable_isLiveness (hI : ∀ x, (spec x).init.Nonempty)
    (hT : ∀ x, (spec x).Total) : IsLiveness (fun H : History P X Op Res => ∃ t, TLinearizable spec H t) :=
  fun H hH m => ⟨take H m, wellFormed_take hH m, take_take H m, m, tLinearizable_take_self hI hT hH m⟩

end Lemma10

end Podc.EventualLinParadox
