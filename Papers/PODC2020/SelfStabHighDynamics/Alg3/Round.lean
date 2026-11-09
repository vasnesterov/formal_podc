import Papers.PODC2020.SelfStabHighDynamics.Alg3.Defs

/-!
# Algorithm 3: one round of one process

Lemmas about `insert` (macros `max`/`insert`) and `round` (lines 4–8), for every processing
order `mb` of the received pairs (duplicates allowed) and every tie-break in `max(p)`.

Notation: `V` is the set of processes, the capacity is `n = |V|`; an identifier is *fake* if it is
not in `V`. `FakeGe V B q`: every fake entry of `q` has timestamp `≥ B`.

The key counting fact (`mem_keys_of_full`), used where the paper says "by Lemma 10, `id(p)`
cannot be removed": a full map (`n = |V|` entries, distinct keys) all of whose timestamps are
`< B`, while fake timestamps are `≥ B`, contains every identifier of `V`; hence no new identifier
can arrive and nothing is evicted.
-/

namespace Podc.SelfStabHighDynamics.Alg3

variable {ι : Type*} [LinearOrder ι]

/-! ### `List.lookup` on maps -/

theorem lookup_mem {q : List (ι × ℕ)} {a : ι} {b : ℕ} (h : q.lookup a = some b) : (a, b) ∈ q := by
  induction q with
  | nil => simp at h
  | cons y q ih =>
    obtain ⟨y1, y2⟩ := y
    by_cases hy : a = y1
    · subst hy; simp at h; simp [h]
    · simp only [List.lookup, show (a == y1) = false by simpa using hy] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_eq_none {q : List (ι × ℕ)} {a : ι} : q.lookup a = none ↔ a ∉ keys q := by
  simp [keys, List.lookup_eq_none_iff, bne_iff_ne]
  constructor
  · intro h b hb; exact h a b hb rfl
  · intro h x y hxy hax; subst hax; exact h y hxy

theorem lookup_of_mem {q : List (ι × ℕ)} (hq : (keys q).Nodup) {a : ι} {b : ℕ} (h : (a, b) ∈ q) :
    q.lookup a = some b := by
  induction q with
  | nil => simp at h
  | cons y q ih =>
    obtain ⟨y1, y2⟩ := y
    simp only [keys, List.map_cons, List.nodup_cons] at hq
    rcases List.mem_cons.mp h with h' | h'
    · cases h'; simp
    · have hne : a ≠ y1 := by
        rintro rfl; exact hq.1 (List.mem_map.mpr ⟨(a, b), h', rfl⟩)
      simp only [List.lookup, show (a == y1) = false by simpa using hne]
      exact ih hq.2 h'

omit [LinearOrder ι] in
theorem mem_keys {q : List (ι × ℕ)} {a : ι} : a ∈ keys q ↔ ∃ b, (a, b) ∈ q := by
  simp only [keys, List.mem_map]
  constructor
  · rintro ⟨⟨a', b⟩, h, rfl⟩; exact ⟨b, h⟩
  · rintro ⟨b, h⟩; exact ⟨_, h, rfl⟩

omit [LinearOrder ι] in
theorem keys_map_of_fst {q : List (ι × ℕ)} (g : ι × ℕ → ι × ℕ) (hg : ∀ y, (g y).1 = y.1) :
    keys (q.map g) = keys q := by
  simp only [keys, List.map_map]
  congr 1; funext y; exact hg y

omit [LinearOrder ι] in
theorem keys_map_snd (q : List (ι × ℕ)) (f : ι × ℕ → ℕ) :
    keys (q.map fun x => (x.1, f x)) = keys q := by
  simp [keys, Function.comp_def]

/-! ### The counting fact -/

/-- A map with distinct keys, `|V|` entries, and only keys of `V` contains every key of `V`. -/
theorem mem_keys_of_full {V : Finset ι} {q : List (ι × ℕ)} (hnd : (keys q).Nodup)
    (hlen : V.card ≤ q.length) (hV : ∀ y ∈ q, y.1 ∈ V) {v : ι} (hv : v ∈ V) : v ∈ keys q := by
  have hsub : (keys q).toFinset ⊆ V := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hV y hy
  have hcard : V.card ≤ (keys q).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, keys, List.length_map]; exact hlen
  have := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← List.mem_toFinset, this]; exact hv

/-- Every fake entry of `q` has timestamp `≥ B`. -/
def FakeGe (V : Finset ι) (B : ℕ) (q : List (ι × ℕ)) : Prop := ∀ y ∈ q, y.1 ∉ V → B ≤ y.2

/-- If all timestamps of a full map are `< B` and fake timestamps are `≥ B`, it contains `V`. -/
theorem mem_keys_of_full_lt {V : Finset ι} {B : ℕ} {q : List (ι × ℕ)} (hnd : (keys q).Nodup)
    (hlen : V.card ≤ q.length) (hf : FakeGe V B q) (hlt : ∀ y ∈ q, y.2 < B) {v : ι}
    (hv : v ∈ V) : v ∈ keys q :=
  mem_keys_of_full hnd hlen (fun y hy => by
    by_contra h; exact absurd (hf y hy h) (by have := hlt y hy; omega)) hv

/-! ### `insert` -/

/-- Well-formed map of capacity `n`: distinct keys, at most `n` entries. -/
def WF (n : ℕ) (q : List (ι × ℕ)) : Prop := (keys q).Nodup ∧ q.length ≤ n

theorem insert_wf {n : ℕ} {q : List (ι × ℕ)} (hq : WF n q) (x : ι × ℕ) : WF n (insert n q x) := by
  unfold insert
  split
  · refine ⟨?_, by simpa using hq.2⟩
    rw [keys_map_of_fst _ (fun y => by split <;> rfl)]; exact hq.1
  · rename_i hnone
    have hx : x.1 ∉ keys q := lookup_eq_none.mp hnone
    split
    · refine ⟨?_, by simp; omega⟩
      simp only [keys, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hq.1, List.nodup_singleton _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hx ha
    · split
      · rename_i y hy
        split
        · have hym : y ∈ q := List.argmax_mem hy
          refine ⟨?_, ?_⟩
          · simp only [keys, List.map_append, List.map_cons, List.map_nil]
            refine List.nodup_append.mpr ⟨?_, List.nodup_singleton _, ?_⟩
            · exact (List.erase_sublist.map _).nodup hq.1
            · intro a ha b hb
              simp only [List.mem_singleton] at hb; subst hb
              rintro rfl
              exact hx ((List.erase_sublist.map _).subset ha)
          · rw [List.length_append, List.length_erase_of_mem hym]
            have := List.length_pos_of_mem hym; have := hq.2; simp only [List.length_singleton]
            omega
        · exact hq
      · exact hq

/-- Every entry after `insert` is an old entry or carries the inserted key, with the inserted
timestamp or the old timestamp of that key. -/
theorem mem_insert {n : ℕ} {q : List (ι × ℕ)} {x y : ι × ℕ} (hy : y ∈ insert n q x) :
    y ∈ q ∨ (y.1 = x.1 ∧ (y.2 = x.2 ∨ (x.1, y.2) ∈ q)) := by
  unfold insert at hy
  split at hy
  · rename_i t' ht'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    split
    · rename_i hzx
      right
      refine ⟨hzx, ?_⟩
      rcases min_choice x.2 t' with h | h <;> simp only [h]
      · simp
      · exact Or.inr (lookup_mem ht')
    · exact Or.inl hz
  · split at hy
    · rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · simp at h; subst h; simp
    · split at hy
      · split at hy
        · rcases List.mem_append.mp hy with h | h
          · exact Or.inl (List.mem_of_mem_erase h)
          · simp at h; subst h; simp
        · exact Or.inl hy
      · exact Or.inl hy

theorem insert_fakeGe {V : Finset ι} {B n : ℕ} {q : List (ι × ℕ)} {x : ι × ℕ} (hq : FakeGe V B q)
    (hx : x.1 ∉ V → B ≤ x.2) : FakeGe V B (insert n q x) := by
  intro y hy hyV
  rcases mem_insert hy with h | ⟨h1, h | h⟩
  · exact hq y h hyV
  · rw [h]; exact hx (h1 ▸ hyV)
  · exact hq (x.1, y.2) h (by rw [← h1]; exact hyV)

/-- An entry with a timestamp `< B` is never evicted (it may only decrease). -/
theorem insert_keep {V : Finset ι} {B : ℕ} {q : List (ι × ℕ)} (hq : WF V.card q)
    (hf : FakeGe V B q) {x : ι × ℕ} (hx : x.1 ∉ V → B ≤ x.2) {p : ι} {t : ℕ} (hp : (p, t) ∈ q)
    (ht : t < B) : ∃ t' ≤ t, (p, t') ∈ insert V.card q x := by
  unfold insert
  split
  · rename_i t' ht'
    refine ⟨if p = x.1 then min x.2 t' else t, ?_, List.mem_map.mpr ⟨(p, t), hp, ?_⟩⟩
    · split
      · rename_i hpx; subst hpx
        have := lookup_of_mem hq.1 hp
        rw [this] at ht'; cases ht'; exact min_le_right _ _
      · exact le_rfl
    · simp only; split <;> rfl
  · rename_i hnone
    have hxk : x.1 ∉ keys q := lookup_eq_none.mp hnone
    split
    · exact ⟨t, le_rfl, List.mem_append_left _ hp⟩
    · rename_i hfull
      split
      · rename_i y hy
        split
        · rename_i hlt
          refine ⟨t, le_rfl, List.mem_append_left _ (List.mem_erase_of_ne ?_ |>.mpr hp)⟩
          rintro rfl
          have hall : ∀ z ∈ q, z.2 < B := fun z hz =>
            lt_of_le_of_lt (List.le_of_mem_argmax hz hy) ht
          by_cases hxV : x.1 ∈ V
          · exact hxk (mem_keys_of_full_lt hq.1 (by omega) hf hall hxV)
          · have := hx hxV; simp at hlt; omega
        · exact ⟨t, le_rfl, hp⟩
      · exact ⟨t, le_rfl, hp⟩

/-- A received pair with a real key and a timestamp `< B` is inserted (or lowers the stored
timestamp). -/
theorem insert_add {V : Finset ι} {B : ℕ} {q : List (ι × ℕ)} (hq : WF V.card q)
    (hf : FakeGe V B q) {x : ι × ℕ} (hxV : x.1 ∈ V) (hxB : x.2 < B) :
    ∃ t' ≤ x.2, (x.1, t') ∈ insert V.card q x := by
  unfold insert
  split
  · rename_i t' ht'
    refine ⟨min x.2 t', min_le_left _ _, List.mem_map.mpr ⟨(x.1, t'), lookup_mem ht', ?_⟩⟩
    simp
  · rename_i hnone
    have hxk : x.1 ∉ keys q := lookup_eq_none.mp hnone
    split
    · exact ⟨x.2, le_rfl, List.mem_append_right _ (by simp)⟩
    · rename_i hfull
      split
      · rename_i y hy
        split
        · exact ⟨x.2, le_rfl, List.mem_append_right _ (by simp)⟩
        · rename_i hlt
          have hall : ∀ z ∈ q, z.2 < B := fun z hz => by
            have := List.le_of_mem_argmax hz hy; simp at hlt; omega
          exact absurd (mem_keys_of_full_lt hq.1 (by omega) hf hall hxV) hxk
      · rename_i hnone'
        rw [List.argmax_eq_none] at hnone'
        subst hnone'
        have := Finset.card_pos.mpr ⟨_, hxV⟩
        simp only [List.length_nil, not_lt] at hfull; omega

/-- `insert` with a key already present keeps the keys. -/
theorem keys_insert_of_mem {n : ℕ} {q : List (ι × ℕ)} {x : ι × ℕ} (hx : x.1 ∈ keys q) :
    keys (insert n q x) = keys q := by
  unfold insert
  split
  · exact keys_map_of_fst _ (fun y => by split <;> rfl)
  · rename_i hnone
    exact absurd hx (lookup_eq_none.mp hnone)

/-! ### Lines 4–5: the fold over the received pairs -/

/-- Lines 4–5: insert the received pairs (other than one's own identifier) in the order `mb`. -/
def fold (me : ι) (n : ℕ) (mb : List (ι × ℕ)) (q : List (ι × ℕ)) : List (ι × ℕ) :=
  mb.foldl (fun q x => if x.1 ≠ me then insert n q x else q) q

/-- Line 6: increment all timestamps. -/
def incr (q : List (ι × ℕ)) : List (ι × ℕ) := q.map fun x => (x.1, x.2 + 1)

theorem round_mem (me : ι) (s : MSt ι) (mb : List (ι × ℕ)) :
    (round me s mb).mem = insert s.n (incr (fold me s.n mb s.mem)) (me, 0) := rfl

theorem round_n (me : ι) (s : MSt ι) (mb : List (ι × ℕ)) : (round me s mb).n = s.n := rfl

theorem round_lid (me : ι) (s : MSt ι) (mb : List (ι × ℕ)) :
    (round me s mb).lid = minKey (round me s mb).mem me := rfl

theorem fold_cons (me : ι) (n : ℕ) (x : ι × ℕ) (mb q : List (ι × ℕ)) :
    fold me n (x :: mb) q = fold me n mb (if x.1 ≠ me then insert n q x else q) := rfl

theorem fold_wf {me : ι} {n : ℕ} (mb : List (ι × ℕ)) {q : List (ι × ℕ)} (hq : WF n q) :
    WF n (fold me n mb q) := by
  induction mb generalizing q with
  | nil => exact hq
  | cons x mb ih => rw [fold_cons]; split <;> [exact ih (insert_wf hq x); exact ih hq]

theorem fold_fakeGe {V : Finset ι} {B : ℕ} {me : ι} {n : ℕ} {mb : List (ι × ℕ)}
    (hmb : FakeGe V B mb) {q : List (ι × ℕ)} (hq : FakeGe V B q) :
    FakeGe V B (fold me n mb q) := by
  induction mb generalizing q with
  | nil => exact hq
  | cons x mb ih =>
    rw [fold_cons]
    have hmb' : FakeGe V B mb := fun y hy => hmb y (List.mem_cons_of_mem _ hy)
    split
    · exact ih hmb' (insert_fakeGe hq (hmb x List.mem_cons_self))
    · exact ih hmb' hq

theorem fold_keep {V : Finset ι} {B : ℕ} {me : ι} {mb : List (ι × ℕ)} (hmb : FakeGe V B mb)
    {q : List (ι × ℕ)} (hq : WF V.card q) (hf : FakeGe V B q) {p : ι} {t : ℕ} (hp : (p, t) ∈ q)
    (ht : t < B) : ∃ t' ≤ t, (p, t') ∈ fold me V.card mb q := by
  induction mb generalizing q t with
  | nil => exact ⟨t, le_rfl, hp⟩
  | cons x mb ih =>
    rw [fold_cons]
    have hmb' : FakeGe V B mb := fun y hy => hmb y (List.mem_cons_of_mem _ hy)
    split
    · obtain ⟨t1, ht1, hp1⟩ := insert_keep hq hf (hmb x List.mem_cons_self) hp ht
      obtain ⟨t2, ht2, hp2⟩ := ih hmb' (insert_wf hq x)
        (insert_fakeGe hf (hmb x List.mem_cons_self)) hp1 (by omega)
      exact ⟨t2, by omega, hp2⟩
    · exact ih hmb' hq hf hp ht

theorem fold_add {V : Finset ι} {B : ℕ} {me : ι} {mb : List (ι × ℕ)} (hmb : FakeGe V B mb)
    {q : List (ι × ℕ)} (hq : WF V.card q) (hf : FakeGe V B q) {x : ι × ℕ} (hx : x ∈ mb)
    (hxV : x.1 ∈ V) (hxme : x.1 ≠ me) (hxB : x.2 < B) :
    ∃ t' ≤ x.2, (x.1, t') ∈ fold me V.card mb q := by
  induction mb generalizing q with
  | nil => simp at hx
  | cons y mb ih =>
    rw [fold_cons]
    have hmb' : FakeGe V B mb := fun y hy => hmb y (List.mem_cons_of_mem _ hy)
    have hq' : WF V.card (if y.1 ≠ me then insert V.card q y else q) := by
      split; exact insert_wf hq y; exact hq
    have hf' : FakeGe V B (if y.1 ≠ me then insert V.card q y else q) := by
      split; exact insert_fakeGe hf (hmb y List.mem_cons_self); exact hf
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [ne_eq, hxme, not_false_eq_true, ↓reduceIte] at hq' hf' ⊢
      obtain ⟨t1, ht1, hp1⟩ := insert_add hq hf hxV hxB
      obtain ⟨t2, ht2, hp2⟩ := fold_keep hmb' hq' hf' hp1 (by omega)
      exact ⟨t2, by omega, hp2⟩
    · exact ih hmb' hq' hf' hx

theorem keys_fold {V : Finset ι} {me : ι} {n : ℕ} {mb : List (ι × ℕ)} (hmb : ∀ x ∈ mb, x.1 ∈ V)
    {q : List (ι × ℕ)} (hq : ∀ v, v ∈ keys q ↔ v ∈ V) : keys (fold me n mb q) = keys q := by
  induction mb generalizing q with
  | nil => rfl
  | cons x mb ih =>
    rw [fold_cons]
    have hmb' : ∀ x ∈ mb, x.1 ∈ V := fun y hy => hmb y (List.mem_cons_of_mem _ hy)
    split
    · have hk := keys_insert_of_mem (n := n) ((hq _).mpr (hmb x List.mem_cons_self))
      rw [ih hmb' (fun v => by rw [hk]; exact hq v), hk]
    · exact ih hmb' hq

/-! ### Line 6 -/

omit [LinearOrder ι] in
theorem incr_wf {n : ℕ} {q : List (ι × ℕ)} (hq : WF n q) : WF n (incr q) :=
  ⟨by rw [incr, keys_map_snd]; exact hq.1, by simpa [incr] using hq.2⟩

omit [LinearOrder ι] in
theorem keys_incr (q : List (ι × ℕ)) : keys (incr q) = keys q := keys_map_snd q _

omit [LinearOrder ι] in
theorem mem_incr {q : List (ι × ℕ)} {y : ι × ℕ} : y ∈ incr q ↔ ∃ t, (y.1, t) ∈ q ∧ y.2 = t + 1 := by
  obtain ⟨y1, y2⟩ := y
  simp only [incr, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl, rfl⟩; exact ⟨b, h, rfl⟩
  · rintro ⟨t, h, rfl⟩; exact ⟨_, h, rfl, rfl⟩

omit [LinearOrder ι] in
theorem incr_fakeGe {V : Finset ι} {B : ℕ} {q : List (ι × ℕ)} (hq : FakeGe V B q) :
    FakeGe V (B + 1) (incr q) := by
  intro y hy hyV
  obtain ⟨t, ht, he⟩ := mem_incr.mp hy
  have := hq _ ht hyV; simp only at this; omega

/-! ### One round -/

theorem round_wf (me : ι) {s : MSt ι} (hs : WF s.n s.mem) (mb : List (ι × ℕ)) :
    WF (round me s mb).n (round me s mb).mem := by
  rw [round_mem, round_n]
  exact insert_wf (incr_wf (fold_wf mb hs)) _

/-- After line 7, `⟨id(p), 0⟩ ∈ members(p)`. -/
theorem round_self (me : ι) {s : MSt ι} (hn : 1 ≤ s.n) (mb : List (ι × ℕ)) :
    (me, 0) ∈ (round me s mb).mem := by
  rw [round_mem]
  have hpos : ∀ y ∈ incr (fold me s.n mb s.mem), 1 ≤ y.2 := fun y hy => by
    obtain ⟨t, -, he⟩ := mem_incr.mp hy; omega
  generalize incr (fold me s.n mb s.mem) = q at hpos
  unfold insert
  split
  · rename_i t' ht'
    exact List.mem_map.mpr ⟨(me, t'), lookup_mem ht', by simp⟩
  · split
    · simp
    · rename_i hfull
      split
      · rename_i y hy
        have h0 : 0 < y.2 := by have := hpos y (List.argmax_mem hy); omega
        simp only [h0, ↓reduceIte]
        simp
      · rename_i hnone'
        rw [List.argmax_eq_none] at hnone'
        subst hnone'; simp at hfull; omega

/-- Lemma 10, one round: fake timestamps grow by one each round. -/
theorem round_fakeGe {V : Finset ι} {B : ℕ} {me : ι} (hme : me ∈ V) {s : MSt ι}
    {mb : List (ι × ℕ)} (hs : FakeGe V B s.mem) (hmb : FakeGe V B mb) :
    FakeGe V (B + 1) (round me s mb).mem := by
  rw [round_mem]
  exact insert_fakeGe (incr_fakeGe (fold_fakeGe hmb hs)) (fun h => absurd hme h)

/-- An entry with timestamp `< B` survives the round, with timestamp at most one more. -/
theorem round_keep {V : Finset ι} {B : ℕ} {me : ι} (hme : me ∈ V) {s : MSt ι}
    (hn : s.n = V.card) (hwf : WF s.n s.mem) {mb : List (ι × ℕ)} (hs : FakeGe V B s.mem)
    (hmb : FakeGe V B mb) {p : ι} {t : ℕ} (hp : (p, t) ∈ s.mem) (ht : t < B) :
    ∃ t' ≤ t + 1, (p, t') ∈ (round me s mb).mem := by
  rw [round_mem, hn]
  rw [hn] at hwf
  obtain ⟨t1, ht1, hp1⟩ := fold_keep (me := me) hmb hwf hs hp ht
  have hp2 : (p, t1 + 1) ∈ incr (fold me V.card mb s.mem) := mem_incr.mpr ⟨t1, hp1, rfl⟩
  obtain ⟨t2, ht2, hp3⟩ := insert_keep (incr_wf (fold_wf mb hwf))
    (incr_fakeGe (fold_fakeGe hmb hs)) (x := (me, 0)) (fun h => absurd hme h) hp2 (by omega)
  exact ⟨t2, by omega, hp3⟩

/-- A received pair `⟨id, t⟩` with a real `id ≠ id(p)` and `t < B` ends the round in the map,
with timestamp at most `t + 1`. -/
theorem round_add {V : Finset ι} {B : ℕ} {me : ι} (hme : me ∈ V) {s : MSt ι}
    (hn : s.n = V.card) (hwf : WF s.n s.mem) {mb : List (ι × ℕ)} (hs : FakeGe V B s.mem)
    (hmb : FakeGe V B mb) {x : ι × ℕ} (hx : x ∈ mb) (hxV : x.1 ∈ V) (hxme : x.1 ≠ me)
    (hxB : x.2 < B) : ∃ t' ≤ x.2 + 1, (x.1, t') ∈ (round me s mb).mem := by
  rw [round_mem, hn]
  rw [hn] at hwf
  obtain ⟨t1, ht1, hp1⟩ := fold_add hmb hwf hs hx hxV hxme hxB
  have hp2 : (x.1, t1 + 1) ∈ incr (fold me V.card mb s.mem) := mem_incr.mpr ⟨t1, hp1, rfl⟩
  obtain ⟨t2, ht2, hp3⟩ := insert_keep (incr_wf (fold_wf mb hwf))
    (incr_fakeGe (fold_fakeGe hmb hs)) (x := (me, 0)) (fun h => absurd hme h) hp2 (by omega)
  exact ⟨t2, by omega, hp3⟩

/-- In a legitimate state receiving only real identifiers, the keys do not change. -/
theorem keys_round {V : Finset ι} {me : ι} (hme : me ∈ V) {s : MSt ι}
    (hs : ∀ v, v ∈ keys s.mem ↔ v ∈ V) {mb : List (ι × ℕ)} (hmb : ∀ x ∈ mb, x.1 ∈ V) :
    keys (round me s mb).mem = keys s.mem := by
  rw [round_mem]
  have h1 := keys_fold (me := me) (n := s.n) hmb hs
  have h2 : keys (incr (fold me s.n mb s.mem)) = keys s.mem := by rw [keys_incr, h1]
  rw [keys_insert_of_mem (by rw [h2]; exact (hs me).mpr hme), h2]

/-! ### Line 8 -/

theorem minKey_spec (l : List (ι × ℕ)) (d : ι) :
    (minKey l d = d ∨ minKey l d ∈ keys l) ∧ minKey l d ≤ d ∧ ∀ k ∈ keys l, minKey l d ≤ k := by
  induction l generalizing d with
  | nil => simp [minKey, keys]
  | cons x l ih =>
    have he : minKey (x :: l) d = minKey l (min d x.1) := rfl
    obtain ⟨h1, h2, h3⟩ := ih (min d x.1)
    rw [he]
    refine ⟨?_, h2.trans (min_le_left _ _), ?_⟩
    · rcases h1 with h | h
      · rw [h]; rcases min_choice d x.1 with h' | h' <;> rw [h']
        · exact Or.inl rfl
        · exact Or.inr (by simp [keys])
      · exact Or.inr (by simp only [keys, List.map_cons, List.mem_cons] at h ⊢; exact Or.inr h)
    · intro k hk
      simp only [keys, List.map_cons, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact h2.trans (min_le_right _ _)
      · exact h3 k hk

/-- If the keys are exactly `V` and `d ∈ V`, line 8 elects `min V`. -/
theorem minKey_eq_min' {V : Finset ι} (hV : V.Nonempty) {l : List (ι × ℕ)}
    (hl : ∀ v, v ∈ keys l ↔ v ∈ V) {d : ι} (hd : d ∈ V) : minKey l d = V.min' hV := by
  obtain ⟨h1, h2, h3⟩ := minKey_spec l d
  apply le_antisymm
  · exact h3 _ ((hl _).mpr (V.min'_mem hV))
  · apply Finset.min'_le
    rcases h1 with h | h
    · rw [h]; exact hd
    · exact (hl _).mp h

end Podc.SelfStabHighDynamics.Alg3
