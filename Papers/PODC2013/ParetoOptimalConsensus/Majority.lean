import Papers.PODC2013.ParetoOptimalConsensus.Consensus

/-!
# Majority consensus: the protocol `OptMaj`, Lemmas 7–8, Theorem 3 (§3.1, Appendix A.1)

"`Maj = 0`" holds if more than `n/2` inputs are `0`, "`Maj = 1`" if at least `n/2` inputs are `1`.
`K_i(Maj = v)` holds iff the inputs seen by `⟨i, m⟩` already decide the majority
(`knows_maj_iff`): `n < 2 · #(seen zeros)`, resp. `n ≤ 2 · #(seen ones)`. `Maj⟨i, m⟩` is `0` if
more than half of the seen inputs are `0`, and `1` otherwise.

**Protocol `OptMaj`** (for an undecided process `i` at time `m`):

  if `K_i(Maj = 0)` then decide(0) elseif `K_i(Maj = 1)` then decide(1)
  elseif no hidden path w.r.t. `⟨i, m⟩` then decide(`Maj⟨i, m⟩`).

* `optMaj_solves`: `OptMaj` solves consensus (the paper leaves this "to the reader").
* `optMaj_majorityValidity`: Majority Validity.
* **Lemma 7** (`lemma7`), **Lemma 8** (`lemma8`), for `n > 2`, `t > 0`.
* **Theorem 3** (`theorem3`): for `t > 0`, `OptMaj` is unbeatable (all `n ≥ 1`).
-/

namespace Podc.ParetoOptimalConsensus

open Cslib Finset Podc.UnbeatableSetConsensus

variable {P : Type*} [Fintype P] {t : ℕ}

/-! ### Majorities -/

/-- The threshold for "`Maj = v`" on a count `c` of `v`'s: `n < 2c` for `v = 0`, `n ≤ 2c` for
`v = 1`. -/
def Thr (n v c : ℕ) : Prop := if v = 0 then n < 2 * c else n ≤ 2 * c

lemma Thr.mono {n v c c' : ℕ} (h : Thr n v c) (hc : c ≤ c') : Thr n v c' := by
  unfold Thr at *; split_ifs at * <;> omega

open Classical in
/-- The processes with input `v`. -/
noncomputable def withInput (r : Run P) (v : ℕ) : Finset P := univ.filter fun q => r.input q = v

open Classical in
/-- The processes with input `v` seen (at time `0`) by `⟨i, m⟩`. -/
noncomputable def seenWith (r : Run P) (i : P) (m v : ℕ) : Finset P :=
  univ.filter fun q => Seen r q 0 i m ∧ r.input q = v

open Classical in
/-- The processes seen (at time `0`) by `⟨i, m⟩`. -/
noncomputable def seenAll (r : Run P) (i : P) (m : ℕ) : Finset P :=
  univ.filter fun q => Seen r q 0 i m

/-- The fact "`Maj = v`". -/
def Maj (v : ℕ) (r : Run P) : Prop := Thr (Fintype.card P) v (withInput r v).card

/-- `K_i(Maj = v)` in its explicit form (see `knows_maj_iff`). -/
def KMaj (r : Run P) (i : P) (m v : ℕ) : Prop := Thr (Fintype.card P) v (seenWith r i m v).card

open Classical in
/-- `Maj⟨i, m⟩`. -/
noncomputable def majv (r : Run P) (i : P) (m : ℕ) : ℕ :=
  if (seenAll r i m).card < 2 * (seenWith r i m 0).card then 0 else 1

section Basic

variable {r r' : Run P} {i j : P} {m : ℕ}

omit [Fintype P] in
lemma mem_seenWith {q : P} {v : ℕ} [Fintype P] :
    q ∈ seenWith r i m v ↔ Seen r q 0 i m ∧ r.input q = v := by
  classical simp [seenWith]

lemma mem_seenAll {q : P} : q ∈ seenAll r i m ↔ Seen r q 0 i m := by
  classical simp [seenAll]

lemma SameView.seenWith_eq (h : SameView r r' i m) (v : ℕ) :
    seenWith r i m v = seenWith r' i m v := by
  ext q
  rw [mem_seenWith, mem_seenWith]
  constructor
  · rintro ⟨hs, hv⟩
    exact ⟨h.seen hs, ((h.of_seen hs).input_eq).symm.trans hv⟩
  · rintro ⟨hs, hv⟩
    exact ⟨h.symm.seen hs, ((h.symm.of_seen hs).input_eq).symm.trans hv⟩

lemma SameView.seenAll_eq (h : SameView r r' i m) : seenAll r i m = seenAll r' i m := by
  ext q; rw [mem_seenAll, mem_seenAll]; exact h.seen_iff

lemma SameView.kMaj_iff (h : SameView r r' i m) {v : ℕ} : KMaj r i m v ↔ KMaj r' i m v := by
  unfold KMaj; rw [SameView.seenWith_eq h]

lemma SameView.majv_eq (h : SameView r r' i m) : majv r i m = majv r' i m := by
  unfold majv; rw [SameView.seenWith_eq h, SameView.seenAll_eq h]

lemma seenWith_subset_withInput (v : ℕ) : seenWith r i m v ⊆ withInput r v := by
  classical
  intro q hq; simp [withInput, (mem_seenWith.1 hq).2]

lemma seenWith_mono_of_seen {ℓ : ℕ} (hs : Seen r j ℓ i m) (v : ℕ) :
    seenWith r j ℓ v ⊆ seenWith r i m v := by
  intro q hq; rw [mem_seenWith] at hq ⊢; exact ⟨hq.1.trans hs, hq.2⟩

lemma KMaj.of_seen {ℓ v : ℕ} (hk : KMaj r j ℓ v) (hs : Seen r j ℓ i m) : KMaj r i m v :=
  Thr.mono hk (card_le_card (seenWith_mono_of_seen hs v))

lemma seenWith_nonempty {v : ℕ} (hk : KMaj r i m v) : (seenWith r i m v).Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro he
  unfold KMaj Thr at hk
  rw [he] at hk
  have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨i⟩
  split_ifs at hk <;> simp at hk <;> omega

lemma mem_vals_of_kMaj {v : ℕ} (hk : KMaj r i m v) : v ∈ vals r i m := by
  obtain ⟨q, hq⟩ := seenWith_nonempty hk
  rw [mem_seenWith] at hq
  exact mem_vals.2 ⟨q, hq.1, hq.2⟩

/-- In a binary run, the seen processes are the seen `0`s and the seen `1`s. -/
lemma card_seenAll (hr : Adm t bin r) :
    (seenAll r i m).card = (seenWith r i m 0).card + (seenWith r i m 1).card := by
  classical
  rw [← card_union_of_disjoint]
  · congr 1; ext q
    rw [mem_seenAll, mem_union, mem_seenWith, mem_seenWith]
    rcases mem_bin.1 (hr.2 q) with h | h <;> simp [h]
  · rw [disjoint_left]; intro q h1 h2
    rw [mem_seenWith] at h1 h2; rw [h1.2] at h2; exact absurd h2.2 zero_ne_one

lemma card_withInput (hr : Adm t bin r) :
    (withInput r 0).card + (withInput r 1).card = Fintype.card P := by
  classical
  rw [← card_union_of_disjoint, ← card_univ]
  · congr 1; ext q
    rcases mem_bin.1 (hr.2 q) with h | h <;> simp [withInput, h]
  · rw [disjoint_left]; intro q h1 h2
    simp only [withInput, mem_filter] at h1 h2; rw [h1.2] at h2; exact absurd h2.2 zero_ne_one

/-- `K_i(Maj = 0)` and `K_i(Maj = 1)` exclude each other. -/
lemma not_kMaj_both (hr : Adm t bin r) {j : P} {m' : ℕ} (h0 : KMaj r i m 0) (h1 : KMaj r j m' 1) :
    False := by
  have := card_withInput hr
  have a := card_le_card (seenWith_subset_withInput (r := r) (i := i) (m := m) 0)
  have b := card_le_card (seenWith_subset_withInput (r := r) (i := j) (m := m') 1)
  unfold KMaj Thr at h0 h1
  simp only [ite_true, one_ne_zero, ite_false] at h0 h1
  omega

lemma majv_mem_vals (hr : Adm t bin r) : majv r i m ∈ vals r i m := by
  unfold majv
  split_ifs with h
  · obtain ⟨q, hq⟩ : (seenWith r i m 0).Nonempty := by
      rw [nonempty_iff_ne_empty]; intro he; rw [he] at h; simp at h
    rw [mem_seenWith] at hq; exact mem_vals.2 ⟨q, hq.1, hq.2⟩
  · have hc := card_seenAll (i := i) (m := m) hr
    have hpos : 0 < (seenAll r i m).card := card_pos.2 ⟨i, mem_seenAll.2 (seen_self (Nat.zero_le m))⟩
    obtain ⟨q, hq⟩ : (seenWith r i m 1).Nonempty := by
      rw [nonempty_iff_ne_empty]; intro he; rw [he] at hc; simp at hc; omega
    rw [mem_seenWith] at hq; exact mem_vals.2 ⟨q, hq.1, hq.2⟩

/-- **`K_i(Maj = v)`** (semantic knowledge, binary inputs) holds iff the seen inputs decide the
majority. -/
theorem knows_maj_iff (hr : Adm t bin r) (hal : r.Alive i m) {v : ℕ} (hv : v ∈ bin) :
    Knows t bin r i m (Maj v) ↔ KMaj r i m v := by
  classical
  constructor
  · intro hk
    set r' := replaceUnseen r i m (1 - v)
    have hsv : SameView r r' i m := replaceUnseen_sameView r i m (1 - v)
    have hr' : Adm t bin r' := by
      refine ⟨hr.1, fun p => ?_⟩
      simp only [r', replaceUnseen]; split_ifs
      · exact hr.2 p
      · exact one_sub_mem_bin hv
    have hmaj := hk r' hr' hsv hal
    unfold Maj at hmaj
    unfold KMaj
    refine Thr.mono hmaj (card_le_card fun q hq => ?_)
    simp only [withInput, mem_filter, mem_univ, true_and, r', replaceUnseen] at hq
    rw [mem_seenWith]
    split_ifs at hq with hs
    · exact ⟨hs, hq⟩
    · exact absurd hq (one_sub_ne hv)
  · intro hk r' _ hsv _
    unfold Maj
    rw [SameView.kMaj_iff hsv] at hk
    exact Thr.mono hk (card_le_card (seenWith_subset_withInput v))

/-- If `⟨i, m⟩` has no hidden path, it sees every input any correct process ever sees. -/
lemma seenWith_subset_of_not_hiddenPath (hnp : ¬ HiddenPath r i m) (hj : ¬ r.Faulty j)
    (m' v : ℕ) : seenWith r j m' v ⊆ seenWith r i m v := by
  obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 hnp
  intro q hq; rw [mem_seenWith] at hq ⊢
  exact ⟨seen_of_not_hidden hℓ hnh hj hq.1 (Nat.zero_le ℓ), hq.2⟩

lemma seenAll_subset_of_not_hiddenPath (hnp : ¬ HiddenPath r i m) (hj : ¬ r.Faulty j)
    (m' : ℕ) : seenAll r j m' ⊆ seenAll r i m := by
  obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 hnp
  intro q hq; rw [mem_seenAll] at hq ⊢
  exact seen_of_not_hidden hℓ hnh hj hq (Nat.zero_le ℓ)

end Basic

/-! ### The protocol -/

open Classical in
/-- **Protocol `OptMaj`** (§3.1). -/
noncomputable def optMaj : Protocol P where
  dec r i m := if KMaj r i m 0 then some 0 else if KMaj r i m 1 then some 1
    else if ¬ HiddenPath r i m then some (majv r i m) else none
  dec_congr r r' i m h := by
    simp only [SameView.kMaj_iff h, hiddenPath_iff_of_sameView h, SameView.majv_eq h]

section Protocol

variable {r : Run P} {i : P} {m v : ℕ}

lemma optMaj_dec_eq_none :
    optMaj.dec r i m = none ↔ ¬ KMaj r i m 0 ∧ ¬ KMaj r i m 1 ∧ HiddenPath r i m := by
  unfold optMaj; simp only
  split_ifs <;> simp_all

lemma decidesAt_optMaj (h : DecidesAt optMaj r i m v) :
    (KMaj r i m 0 ∧ v = 0) ∨ (¬ KMaj r i m 0 ∧ KMaj r i m 1 ∧ v = 1) ∨
      (¬ KMaj r i m 0 ∧ ¬ KMaj r i m 1 ∧ ¬ HiddenPath r i m ∧ v = majv r i m) := by
  have h2 := h.2.1
  unfold UnbeatableSetConsensus.Protocol.dec optMaj at h2
  simp only at h2
  split_ifs at h2 with h3 h4 h5 <;> cases h2
  · exact Or.inl ⟨h3, rfl⟩
  · exact Or.inr (Or.inl ⟨h3, h4, rfl⟩)
  · exact Or.inr (Or.inr ⟨h3, h4, h5, rfl⟩)

lemma optMaj_dec_ne_none_of_kMaj (hv : v ∈ bin) (hk : KMaj r i m v) : optMaj.dec r i m ≠ none := by
  rw [Ne, optMaj_dec_eq_none]
  rcases hv with rfl | rfl <;> tauto

lemma optMaj_dec_ne_none_of_not_hiddenPath (hh : ¬ HiddenPath r i m) : optMaj.dec r i m ≠ none := by
  rw [Ne, optMaj_dec_eq_none]; tauto

lemma optMaj_decidesAt_mem (hr : Adm t bin r) (h : DecidesAt optMaj r i m v) : v ∈ vals r i m := by
  rcases decidesAt_optMaj h with ⟨h1, rfl⟩ | ⟨-, h1, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact mem_vals_of_kMaj h1
  · exact mem_vals_of_kMaj h1
  · exact majv_mem_vals hr

/-- **`OptMaj` solves consensus** (for every `t`), with decisions by `f + 1`. -/
theorem optMaj_solves : SolvesSetConsensus 1 t bin (optMaj : Protocol P) where
  decision r _ i hi := by
    obtain ⟨m', -, v, hv⟩ := decidesBy_of_dec (SyncCrash.Run.alive_of_not_faulty hi _)
      (optMaj_dec_ne_none_of_not_hiddenPath (r := r) (i := i) not_hiddenPath_faulty)
    exact ⟨m', v, hv⟩
  validity r hr i m v hv := by
    obtain ⟨j, -, hj⟩ := mem_vals.1 (optMaj_decidesAt_mem hr hv); exact ⟨j, hj⟩
  agreement r hr := by
    classical
    rw [Nat.cast_one, Set.encard_le_one_iff]
    rintro v w ⟨i, m, hi, hv⟩ ⟨j, m', hj, hw⟩
    -- a decision by the hidden-path rule excludes a `K(Maj)` decision of a correct process
    have key : ∀ {i j : P} {m m' u u' : ℕ}, ¬ r.Faulty j → DecidesAt optMaj r i m u →
        ¬ KMaj r i m 0 → ¬ KMaj r i m 1 → ¬ HiddenPath r i m → DecidesAt optMaj r j m' u' →
        ¬ KMaj r j m' 0 ∧ ¬ KMaj r j m' 1 := by
      intro i j m m' u u' hj _ h0 h1 hnp _
      refine ⟨fun h => h0 (Thr.mono h ?_), fun h => h1 (Thr.mono h ?_)⟩ <;>
        exact card_le_card (seenWith_subset_of_not_hiddenPath hnp hj m' _)
    rcases decidesAt_optMaj hv with ⟨hi0, rfl⟩ | ⟨hi0, hi1, rfl⟩ | ⟨hi0, hi1, hip, rfl⟩ <;>
    rcases decidesAt_optMaj hw with ⟨hj0, rfl⟩ | ⟨hj0, hj1, rfl⟩ | ⟨hj0, hj1, hjp, rfl⟩
    · rfl
    · exact (not_kMaj_both hr hi0 hj1).elim
    · exact ((key hi hw hj0 hj1 hjp hv).1 hi0).elim
    · exact (not_kMaj_both hr hj0 hi1).elim
    · rfl
    · exact ((key hi hw hj0 hj1 hjp hv).2 hi1).elim
    · exact ((key hj hv hi0 hi1 hip hw).1 hj0).elim
    · exact ((key hj hv hi0 hi1 hip hw).2 hj1).elim
    · -- both by the hidden-path rule: they have seen the same inputs
      have e1 := Subset.antisymm (seenAll_subset_of_not_hiddenPath hip hj m')
        (seenAll_subset_of_not_hiddenPath hjp hi m)
      have e2 := Subset.antisymm (seenWith_subset_of_not_hiddenPath hip hj m' 0)
        (seenWith_subset_of_not_hiddenPath hjp hi m 0)
      unfold majv; rw [e1, e2]

open Classical in
/-- **Majority Validity**: if more than half of the processes are correct and have input `v`,
every process that decides decides `v`. -/
theorem optMaj_majorityValidity {r : Run P} (hr : Adm t bin r) {v : ℕ} (hv : v ∈ bin)
    (hmaj : Fintype.card P < 2 * (univ.filter fun q => ¬ r.Faulty q ∧ r.input q = v).card)
    {i : P} {m u : ℕ} (hd : DecidesAt optMaj r i m u) : u = v := by
  classical
  set C := univ.filter fun q => ¬ r.Faulty q ∧ r.input q = v
  have hCw : C ⊆ withInput r v := by
    intro q hq; simp only [C, mem_filter] at hq; simp [withInput, hq.2.2]
  -- the majority of correct `v`s rules out `K_i(Maj = 1 - v)`
  have hnot : ∀ {j m'}, ¬ KMaj r j m' (1 - v) := by
    intro j m' hk
    have h1 := card_withInput hr
    have h2 := card_le_card hCw
    have h3 := card_le_card (seenWith_subset_withInput (r := r) (i := j) (m := m') (1 - v))
    unfold KMaj Thr at hk
    rcases hv with rfl | rfl
    · simp only [Nat.sub_zero, one_ne_zero, ite_false] at hk h3; omega
    · simp only [Nat.sub_self, ite_true] at hk h3; omega
  -- a process that heard from all correct processes knows `Maj = v`
  have hsee : ∀ {m'}, 1 ≤ m' → r.Alive i m' → KMaj r i m' v := by
    intro m' hm' hal
    unfold KMaj Thr
    have hsub : C ⊆ seenWith r i m' v := by
      intro q hq
      simp only [C, mem_filter, mem_univ, true_and] at hq
      rw [mem_seenWith]
      refine ⟨?_, hq.2⟩
      by_cases hqi : q = i
      · subst hqi; exact seen_self (Nat.zero_le _)
      · exact (seen_of_deliv hqi (SyncCrash.Run.deliv_of_not_faulty hq.1 i 0)).mono_right hm'
    have := card_le_card hsub
    split_ifs <;> omega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- at time `0` a decision needs `n ≤ 2`
    have hn : Fintype.card P ≤ 2 * (seenWith r i 0 u).card := by
      rcases decidesAt_optMaj hd with ⟨h1, rfl⟩ | ⟨-, h1, rfl⟩ | ⟨-, -, hnp, rfl⟩
      · unfold KMaj Thr at h1; simp at h1; omega
      · unfold KMaj Thr at h1; simpa using h1
      · obtain ⟨ℓ, hℓ, hnh⟩ := not_hiddenPath_iff.1 hnp
        obtain rfl : ℓ = 0 := by omega
        have hall : ∀ q, q = i := fun q => by
          by_contra hq; exact hnh q (hidden_zero_iff.2 fun hs => hq (seen_same_time hs))
        have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (hall x).trans (hall y).symm
        have : 0 < (seenWith r i 0 (majv r i 0)).card := card_pos.2 ⟨i, by
          rw [mem_seenWith]; refine ⟨seen_self le_rfl, ?_⟩
          have := majv_mem_vals (i := i) (m := 0) hr
          rw [vals_zero, mem_singleton] at this; exact this.symm⟩
        omega
    have hs1 : (seenWith r i 0 u).card ≤ 1 := by
      refine card_le_one.2 fun x hx y hy => ?_
      rw [mem_seenWith] at hx hy
      exact (seen_same_time hx.1).trans (seen_same_time hy.1).symm
    have hC1 : 0 < C.card := by omega
    obtain ⟨q, hq⟩ := card_pos.1 hC1
    simp only [C, mem_filter, mem_univ, true_and] at hq
    -- `n ≤ 2` and more than half of the processes have `v`, so `i` has `v`
    by_contra huv
    have hiu : r.input i = u := by
      obtain ⟨x, hx⟩ := card_pos.1 (show 0 < (seenWith r i 0 u).card by
        have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨i⟩; omega)
      rw [mem_seenWith] at hx; rw [← seen_same_time hx.1]; exact hx.2
    have hCi : i ∉ C := by simp [C, hiu, huv]
    have : C ⊆ univ.erase i := fun q hq => mem_erase.2 ⟨fun h => hCi (h ▸ hq), mem_univ _⟩
    have := card_le_card this
    rw [card_erase_of_mem (mem_univ i), card_univ] at this
    omega
  · -- later decisions: `i` knows `Maj = v`
    have hk := hsee hm hd.1
    rcases decidesAt_optMaj hd with ⟨h1, rfl⟩ | ⟨h0, h1, rfl⟩ | ⟨h0, h1, -, rfl⟩
    · rcases hv with rfl | rfl
      · rfl
      · exact absurd h1 hnot
    · rcases hv with rfl | rfl
      · exact absurd hk h0
      · rfl
    · rcases hv with rfl | rfl
      · exact absurd hk h0
      · exact absurd hk h1

end Protocol

end Podc.ParetoOptimalConsensus
