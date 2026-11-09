import Papers.PODC2020.SelfStabHighDynamics.Alg2.Defs

/-!
# Algorithm 2: one round, for every processing order

Lemmas about the macro `insert`, line 6 (`incr`), and one round `round Δ me s mb`, for an
arbitrary list `mb` of received pairs (any order, duplicates allowed).

The key notion is `Tail V l k B`: the queue `l` splits as `l₁ ++ l₂` where all identifiers of
`l₂` are in `V` (real identifiers) and `l₂` contains a pair `⟨k, t⟩` with `t ≤ B`. When only real
identifiers are inserted (rounds after `Δ`, Corollary 7), such a suffix is never cut: the head of
the queue is removed (line i5) only if the queue is full, and a full queue consisting of real
identifiers only already contains all of `V`, so no new identifier can be inserted. This is the
corrected form of the counting argument of Lemma 6.
-/

namespace Podc.SelfStabHighDynamics.Alg2

variable {ι : Type*} [LinearOrder ι]

omit [LinearOrder ι] in
theorem mem_keys {l : List (ι × ℕ)} {k : ι} : k ∈ keys l ↔ ∃ t, (k, t) ∈ l := by
  simp [keys]

theorem lookup_none {q : List (ι × ℕ)} {a : ι} (h : q.lookup a = none) : a ∉ keys q := by
  rw [List.lookup_eq_none_iff] at h
  intro ha
  obtain ⟨t, ht⟩ := mem_keys.1 ha
  simpa using h _ ht

theorem lookup_some {q : List (ι × ℕ)} {a : ι} {t : ℕ} (h : q.lookup a = some t) :
    (a, t) ∈ q := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  simp

/-- Well-formedness of a queue: at most `n` pairs, distinct identifiers. -/
def Inv (n : ℕ) (q : List (ι × ℕ)) : Prop := q.length ≤ n ∧ (keys q).Nodup

omit [LinearOrder ι] in
theorem eq_of_nodup {q : List (ι × ℕ)} (h : (keys q).Nodup) {k : ι} {t t' : ℕ}
    (ht : (k, t) ∈ q) (ht' : (k, t') ∈ q) : t = t' := by
  have := List.inj_on_of_nodup_map h ht ht' rfl
  simpa using this

/-! ### The macro `insert` -/

section insert

variable {n : ℕ} {q : List (ι × ℕ)} {x y : ι × ℕ}

theorem mem_insert (h : y ∈ insert n q x) :
    y ∈ q ∨ y = x ∨ ∃ t', (x.1, t') ∈ q ∧ y = (x.1, min x.2 t') := by
  unfold insert at h
  split at h
  · rename_i t' ht'
    rcases List.mem_append.1 h with h | h
    · exact Or.inl (List.mem_of_mem_filter h)
    · simp only [List.mem_singleton] at h
      exact Or.inr (Or.inr ⟨t', lookup_some ht', h⟩)
  · rcases List.mem_append.1 h with h | h
    · split_ifs at h
      · exact Or.inl (List.mem_of_mem_tail h)
      · exact Or.inl h
    · simp only [List.mem_singleton] at h
      exact Or.inr (Or.inl h)

/-- A predicate on pairs closed under the combination of line i3. -/
def MinClosed (P : ι × ℕ → Prop) : Prop := ∀ x t', P x → P (x.1, t') → P (x.1, min x.2 t')

theorem insert_mem_of {P : ι × ℕ → Prop} (hP : MinClosed P) (hq : ∀ y ∈ q, P y) (hx : P x) :
    ∀ y ∈ insert n q x, P y := by
  intro y hy
  rcases mem_insert hy with h | rfl | ⟨t', h, rfl⟩
  · exact hq y h
  · exact hx
  · exact hP x t' hx (hq _ h)

theorem inv_insert (hn : 0 < n) (h : Inv n q) : Inv n (insert n q x) := by
  obtain ⟨hl, hnd⟩ := h
  unfold insert
  split
  · rename_i t' ht'
    have hm := lookup_some ht'
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      have : (q.filter fun y => y.1 != x.1).length < q.length :=
        List.length_filter_lt_length_iff_exists.2 ⟨_, hm, by simp⟩
      omega
    · have h1 : (keys (q.filter fun y => y.1 != x.1)).Nodup :=
        hnd.sublist (List.filter_sublist.map _)
      have h2 : x.1 ∉ keys (q.filter fun y => y.1 != x.1) := by
        simp [keys]
      simp only [keys, List.map_append, List.map_singleton] at h1 h2 ⊢
      exact List.nodup_append.2 ⟨h1, List.nodup_singleton _, by
        intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact h2 ha⟩
  · rename_i hnone
    have hx := lookup_none hnone
    refine ⟨?_, ?_⟩
    · split_ifs with h
      · simp only [List.length_append, List.length_tail, List.length_singleton]; omega
      · simp only [List.length_append, List.length_singleton]; omega
    · have hsub : (if q.length = n then q.tail else q).Sublist q := by
        split_ifs
        · exact List.tail_sublist q
        · exact List.Sublist.refl q
      have h1 : (keys (if q.length = n then q.tail else q)).Nodup := hnd.sublist (hsub.map _)
      have h2 : x.1 ∉ keys (if q.length = n then q.tail else q) :=
        fun h => hx ((hsub.map _).subset h)
      simp only [keys, List.map_append, List.map_singleton] at h1 h2 ⊢
      exact List.nodup_append.2 ⟨h1, List.nodup_singleton _, by
        intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact h2 ha⟩

end insert

/-! ### Suffixes of real identifiers -/

/-- `Tail V l k B`: `l = l₁ ++ l₂`, all identifiers of `l₂` are in `V`, and `⟨k, t⟩ ∈ l₂` for some
`t ≤ B`. -/
def Tail (V : Finset ι) (l : List (ι × ℕ)) (k : ι) (B : ℕ) : Prop :=
  ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (∀ y ∈ l₂, y.1 ∈ V) ∧ ∃ t ≤ B, (k, t) ∈ l₂

section tail

variable {V : Finset ι} {n : ℕ} {q : List (ι × ℕ)} {x : ι × ℕ} {k : ι} {B : ℕ}

omit [LinearOrder ι] in
theorem Tail.mem_keys (h : Tail V q k B) : k ∈ keys q := by
  obtain ⟨l₁, l₂, rfl, -, t, -, h⟩ := h
  exact Alg2.mem_keys.2 ⟨t, List.mem_append_right _ h⟩

omit [LinearOrder ι] in
theorem Tail.exists (h : Tail V q k B) : ∃ t ≤ B, (k, t) ∈ q := by
  obtain ⟨l₁, l₂, rfl, -, t, ht, h⟩ := h
  exact ⟨t, ht, List.mem_append_right _ h⟩

omit [LinearOrder ι] in
theorem Tail.mono (h : Tail V q k B) {B' : ℕ} (hB : B ≤ B') : Tail V q k B' := by
  obtain ⟨l₁, l₂, h1, h2, t, ht, h⟩ := h
  exact ⟨l₁, l₂, h1, h2, t, ht.trans hB, h⟩

omit [LinearOrder ι] in
/-- A queue of real identifiers only. -/
theorem tail_of_forall (hq : ∀ y ∈ q, y.1 ∈ V) {t : ℕ} (h : (k, t) ∈ q) : Tail V q k t :=
  ⟨[], q, rfl, hq, t, le_rfl, h⟩

theorem tail_insert_self (hx : x.1 ∈ V) : Tail V (insert n q x) x.1 x.2 := by
  unfold insert
  split
  · rename_i t' _
    exact ⟨_, [(x.1, min x.2 t')], rfl, by simp [hx], min x.2 t', min_le_left _ _, by simp⟩
  · exact ⟨_, [x], rfl, by simp [hx], x.2, le_rfl, by simp⟩

/-- Inserting a real identifier into a queue with distinct identifiers (capacity `n = |V|`) never
cuts a suffix of real identifiers (corrected Lemma 6). -/
theorem Tail.insert (h : Tail V q k B) (hx : x.1 ∈ V) (hnd : (keys q).Nodup) (hn : n = V.card) :
    Tail V (insert n q x) k B := by
  obtain ⟨l₁, l₂, rfl, hV, t, htB, hk⟩ := h
  unfold insert
  split
  · rename_i t' ht'
    by_cases hkx : k = x.1
    · subst hkx
      have : t' = t := eq_of_nodup hnd (lookup_some ht') (List.mem_append_right _ hk)
      exact ⟨_, [(x.1, min x.2 t')], rfl, by simp [hx], min x.2 t',
        (min_le_right _ _).trans (this ▸ htB), by simp⟩
    · refine ⟨l₁.filter (fun y => y.1 != x.1),
        l₂.filter (fun y => y.1 != x.1) ++ [(x.1, min x.2 t')], by simp [List.filter_append],
        ?_, t, htB, ?_⟩
      · intro y hy
        simp only [List.mem_append, List.mem_filter, List.mem_singleton] at hy
        rcases hy with ⟨hy, -⟩ | rfl
        · exact hV _ hy
        · exact hx
      · simp [hk, hkx]
  · rename_i hnone
    have hxq := lookup_none hnone
    split_ifs with hlen
    · cases l₁ with
      | nil =>
        exfalso
        apply hxq
        have hsub : (keys l₂).toFinset ⊆ V := by
          intro a ha
          obtain ⟨b, hb⟩ := Alg2.mem_keys.1 (List.mem_toFinset.1 ha)
          exact hV _ hb
        have hcard : V.card ≤ (keys l₂).toFinset.card := by
          rw [List.toFinset_card_of_nodup (by simpa using hnd)]
          simp only [List.nil_append] at hlen
          simp [keys]; omega
        have := Finset.eq_of_subset_of_card_le hsub hcard
        have hx' : x.1 ∈ (keys l₂).toFinset := this ▸ hx
        simpa using hx'
      | cons a l₁ =>
        refine ⟨l₁, l₂ ++ [x], by simp, ?_, t, htB, by simp [hk]⟩
        intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hV _ hy
        · exact hx
    · refine ⟨l₁, l₂ ++ [x], by simp, ?_, t, htB, by simp [hk]⟩
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hV _ hy
      · exact hx

end tail

/-! ### Line 6 -/

section incr

variable {Δ : ℕ} {V : Finset ι} {q : List (ι × ℕ)} {k : ι} {B : ℕ}

omit [LinearOrder ι] in
theorem mem_incr {y : ι × ℕ} :
    y ∈ incr Δ q ↔ ∃ z ∈ q, y = if z.2 < Δ then (z.1, z.2 + 1) else z := by
  simp only [incr, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

omit [LinearOrder ι] in
theorem keys_incr : keys (incr Δ q) = keys q := by
  simp only [keys, incr, List.map_map]
  apply List.map_congr_left
  intro z _
  simp only [Function.comp_apply]
  split_ifs <;> rfl

omit [LinearOrder ι] in
theorem length_incr : (incr Δ q).length = q.length := by simp [incr]

omit [LinearOrder ι] in
theorem inv_incr {n : ℕ} (h : Inv n q) : Inv n (incr Δ q) := by
  rw [Inv, keys_incr, length_incr]; exact h

omit [LinearOrder ι] in
theorem Tail.incr (h : Tail V q k B) : Tail V (incr Δ q) k (B + 1) := by
  obtain ⟨l₁, l₂, rfl, hV, t, htB, hk⟩ := h
  refine ⟨Alg2.incr Δ l₁, Alg2.incr Δ l₂, by simp [Alg2.incr], ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_incr.1 hy
    split_ifs
    · exact hV z hz
    · exact hV z hz
  · refine ⟨if t < Δ then t + 1 else t, by split_ifs <;> omega, mem_incr.2 ⟨_, hk, ?_⟩⟩
    split_ifs <;> rfl

end incr

/-! ### Lines 4–5 -/

section foldl

variable {n : ℕ} {me : ι} {V : Finset ι} {k : ι} {B : ℕ}

/-- Processing the received pairs (lines 4–5). -/
abbrev recvAll (n : ℕ) (me : ι) (mb : List (ι × ℕ)) (q : List (ι × ℕ)) : List (ι × ℕ) :=
  mb.foldl (fun q x => if x.1 ≠ me then insert n q x else q) q

theorem recvAll_cons (x : ι × ℕ) (mb q : List (ι × ℕ)) :
    recvAll n me (x :: mb) q = recvAll n me mb (if x.1 ≠ me then insert n q x else q) := rfl

theorem inv_recvAll (hn : 0 < n) (mb : List (ι × ℕ)) {q : List (ι × ℕ)} (h : Inv n q) :
    Inv n (recvAll n me mb q) := by
  induction mb generalizing q with
  | nil => exact h
  | cons x mb ih =>
    rw [recvAll_cons]
    apply ih
    split_ifs
    · exact inv_insert hn h
    · exact h

theorem recvAll_mem_of {P : ι × ℕ → Prop} (hP : MinClosed P) (mb : List (ι × ℕ))
    {q : List (ι × ℕ)} (hq : ∀ y ∈ q, P y) (hmb : ∀ x ∈ mb, x.1 ≠ me → P x) :
    ∀ y ∈ recvAll n me mb q, P y := by
  induction mb generalizing q with
  | nil => exact hq
  | cons x mb ih =>
    rw [recvAll_cons]
    apply ih _ (fun x hx => hmb x (List.mem_cons_of_mem _ hx))
    split_ifs with h
    · exact insert_mem_of hP hq (hmb x List.mem_cons_self h)
    · exact hq

theorem Tail.recvAll (hn : n = V.card) (hpos : 0 < n) (mb : List (ι × ℕ))
    (hmb : ∀ x ∈ mb, x.1 ≠ me → x.1 ∈ V) {q : List (ι × ℕ)} (hq : Inv n q)
    (h : Tail V q k B) : Tail V (recvAll n me mb q) k B := by
  induction mb generalizing q with
  | nil => exact h
  | cons x mb ih =>
    rw [recvAll_cons]
    have hmb' := fun x hx => hmb x (List.mem_cons_of_mem _ hx)
    split_ifs with hx
    · exact ih hmb' (inv_insert hpos hq) (h.insert (hmb x List.mem_cons_self hx) hq.2 hn)
    · exact ih hmb' hq h

theorem tail_recvAll_mem (hn : n = V.card) (hpos : 0 < n) {mb : List (ι × ℕ)}
    (hmb : ∀ x ∈ mb, x.1 ≠ me → x.1 ∈ V) {q : List (ι × ℕ)} (hq : Inv n q) {x : ι × ℕ}
    (hx : x ∈ mb) (hxme : x.1 ≠ me) : Tail V (recvAll n me mb q) x.1 x.2 := by
  induction mb generalizing q with
  | nil => simp at hx
  | cons y mb ih =>
    rw [recvAll_cons]
    have hmb' := fun x hx => hmb x (List.mem_cons_of_mem _ hx)
    have hq' : Inv n (if y.1 ≠ me then insert n q y else q) := by
      split_ifs
      · exact inv_insert hpos hq
      · exact hq
    rcases List.mem_cons.1 hx with rfl | hx
    · simp only [ne_eq, hxme, not_false_eq_true, ite_true]
      exact (tail_insert_self (hmb _ List.mem_cons_self hxme)).recvAll hn hpos mb hmb'
        (inv_insert hpos hq)
    · exact ih hmb' hq' hx

end foldl

/-! ### One round (lines 4–8) -/

section round

variable {Δ : ℕ} {me : ι} {s : MSt ι} {mb : List (ι × ℕ)} {V : Finset ι} {k : ι} {B : ℕ}

theorem round_n : (round Δ me s mb).n = s.n := rfl

theorem round_mem :
    (round Δ me s mb).mem = insert s.n (incr Δ (recvAll s.n me mb s.mem)) (me, 0) := rfl

theorem round_lid : (round Δ me s mb).lid = minKey (round Δ me s mb).mem me := rfl

/-- After line 7, `⟨id(p), 0⟩ ∈ members(p)`. -/
theorem round_self : (me, 0) ∈ (round Δ me s mb).mem := by
  rw [round_mem]
  unfold insert
  split
  · simp
  · simp

theorem round_mem_of {P Q : ι × ℕ → Prop} (hP : MinClosed P) (hQ : MinClosed Q)
    (hPQ : ∀ z, P z → Q (if z.2 < Δ then (z.1, z.2 + 1) else z)) (hme : Q (me, 0))
    (hs : ∀ y ∈ s.mem, P y) (hmb : ∀ x ∈ mb, x.1 ≠ me → P x) :
    ∀ y ∈ (round Δ me s mb).mem, Q y := by
  rw [round_mem]
  refine insert_mem_of hQ ?_ hme
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_incr.1 hy
  exact hPQ z (recvAll_mem_of hP mb hs hmb z hz)

theorem inv_round (hpos : 0 < s.n) (h : Inv s.n s.mem) : Inv s.n (round Δ me s mb).mem := by
  rw [round_mem]
  exact inv_insert hpos (inv_incr (inv_recvAll hpos mb h))

/-- Timestamps stay `≤ Δ`. -/
theorem round_le (hs : ∀ y ∈ s.mem, y.2 ≤ Δ) (hmb : ∀ x ∈ mb, x.1 ≠ me → x.2 ≤ Δ) :
    ∀ y ∈ (round Δ me s mb).mem, y.2 ≤ Δ := by
  refine round_mem_of (P := fun y => y.2 ≤ Δ) (Q := fun y => y.2 ≤ Δ) ?_ ?_ ?_ (by simp) hs hmb
  · intro x t' hx _; exact (min_le_left _ _).trans hx
  · intro x t' hx _; exact (min_le_left _ _).trans hx
  · intro z hz; split_ifs with h
    · exact h
    · exact hz

/-- The identifiers stay in `V` if all received identifiers are in `V`. -/
theorem round_keys (hme : me ∈ V) (hs : ∀ y ∈ s.mem, y.1 ∈ V)
    (hmb : ∀ x ∈ mb, x.1 ≠ me → x.1 ∈ V) : ∀ y ∈ (round Δ me s mb).mem, y.1 ∈ V := by
  refine round_mem_of (P := fun y => y.1 ∈ V) (Q := fun y => y.1 ∈ V) ?_ ?_ ?_ hme hs hmb
  · intro x t' hx _; exact hx
  · intro x t' hx _; exact hx
  · intro z hz; split_ifs
    · exact hz
    · exact hz

/-- Lemma 5, one round: lower bounds on the timestamps of an identifier `f ≠ id(p)`. -/
theorem round_ge {f : ι} (hf : f ≠ me) {L : ℕ} (hs : ∀ y ∈ s.mem, y.1 = f → L ≤ y.2)
    (hmb : ∀ x ∈ mb, x.1 = f → L ≤ x.2) :
    ∀ y ∈ (round Δ me s mb).mem, y.1 = f → min Δ (L + 1) ≤ y.2 := by
  refine round_mem_of (P := fun y => y.1 = f → L ≤ y.2)
    (Q := fun y => y.1 = f → min Δ (L + 1) ≤ y.2) ?_ ?_ ?_ ?_ hs (fun x hx _ => hmb x hx)
  · intro x t' hx ht' h; exact le_min (hx h) (ht' h)
  · intro x t' hx ht' h; exact le_min (hx h) (ht' h)
  · intro z hz h
    split_ifs at h ⊢ with h'
    · have := hz h; simp only; omega
    · have := hz h; omega
  · intro h; exact absurd h.symm hf

/-- Lemma 6, one round: suffixes of real identifiers are never cut. -/
theorem Tail.round (h : Tail V s.mem k B) (hme : me ∈ V) (hn : s.n = V.card)
    (hinv : Inv s.n s.mem) (hmb : ∀ x ∈ mb, x.1 ≠ me → x.1 ∈ V) :
    Tail V (round Δ me s mb).mem k (B + 1) := by
  have hpos : 0 < s.n := hn ▸ Finset.card_pos.2 ⟨me, hme⟩
  rw [round_mem]
  exact ((h.recvAll hn hpos mb hmb hinv).incr).insert hme
    (inv_incr (inv_recvAll hpos mb hinv)).2 hn

/-- Lemma 6, one round: a received real identifier is in a suffix of real identifiers. -/
theorem tail_round_recv (hme : me ∈ V) (hn : s.n = V.card) (hinv : Inv s.n s.mem)
    (hmb : ∀ x ∈ mb, x.1 ≠ me → x.1 ∈ V) {x : ι × ℕ} (hx : x ∈ mb) (hxme : x.1 ≠ me) :
    Tail V (round Δ me s mb).mem x.1 (x.2 + 1) := by
  have hpos : 0 < s.n := hn ▸ Finset.card_pos.2 ⟨me, hme⟩
  rw [round_mem]
  exact ((tail_recvAll_mem hn hpos hmb hinv hx hxme).incr).insert hme
    (inv_incr (inv_recvAll hpos mb hinv)).2 hn

theorem tail_round_self (hme : me ∈ V) : Tail V (round Δ me s mb).mem me 0 := by
  rw [round_mem]
  exact tail_insert_self (x := (me, 0)) hme

end round

/-! ### `minKey` (line 8) -/

section minKey

theorem minKey_cons (x : ι × ℕ) (l : List (ι × ℕ)) (d : ι) :
    minKey (x :: l) d = minKey l (min d x.1) := rfl

theorem minKey_le_self (l : List (ι × ℕ)) (d : ι) : minKey l d ≤ d := by
  induction l generalizing d with
  | nil => exact le_rfl
  | cons x l ih => rw [minKey_cons]; exact (ih _).trans (min_le_left _ _)

theorem minKey_le (l : List (ι × ℕ)) (d : ι) : ∀ k ∈ keys l, minKey l d ≤ k := by
  induction l generalizing d with
  | nil => simp [keys]
  | cons x l ih =>
    intro k hk
    rw [minKey_cons]
    simp only [keys, List.map_cons, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact (minKey_le_self _ _).trans (min_le_right _ _)
    · exact ih _ k hk

theorem minKey_mem (l : List (ι × ℕ)) (d : ι) : minKey l d = d ∨ minKey l d ∈ keys l := by
  induction l generalizing d with
  | nil => exact Or.inl rfl
  | cons x l ih =>
    rw [minKey_cons]
    simp only [keys, List.map_cons, List.mem_cons] at ih ⊢
    rcases ih (min d x.1) with h | h
    · rw [h]
      rcases min_choice d x.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h)

/-- If the identifiers of `l` are exactly `V` and `d ∈ V`, line 8 computes `min V`. -/
theorem minKey_eq_min' {V : Finset ι} {l : List (ι × ℕ)} {d : ι} (hd : d ∈ V)
    (hl : ∀ k, k ∈ keys l ↔ k ∈ V) : minKey l d = V.min' ⟨d, hd⟩ := by
  apply le_antisymm
  · exact minKey_le l d _ ((hl _).2 (V.min'_mem _))
  · rcases minKey_mem l d with h | h
    · rw [h]; exact V.min'_le _ hd
    · exact V.min'_le _ ((hl _).1 h)

end minKey

end Podc.SelfStabHighDynamics.Alg2
