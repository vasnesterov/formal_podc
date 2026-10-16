import Papers.PODC2019.AutomaticSpeedup.Lemma2

/-!
# Lemma 3 of Brandt (PODC 2019, §5.1): auxiliary material

The node-local map turning a solution of `Π'_1` (trit description `tritOne k`) into a superweak
`k'`-colouring, `k' = 2^(2^(5^k))`:
* `rb`: the pair `(Q_i, β(i))` of port `i` (`β(i) = none` iff `Q_i = P∞`), `Rv`: the multiset `R^v`;
* `encR`, `col`: an injective colouring of the possible `R^v` (`col_inj`);
* `GoodS`, `sel`: a sub-multiset of `R^v` with the properties of Lemma 2, chosen as a function of
  `R^v` (port-order independence), and `Jset`: ports realizing it (the paper's `J*`);
* `ptr`: `→` on `J*`, `⊸` on `N(J*)`, `•` elsewhere.
-/

namespace AutomaticSpeedup

open Problem

variable {k : ℕ}

/-- The labels `(Q_i, β(i))` of the proof of Lemma 3. -/
abbrev PLabel (k : ℕ) := Set (Trit k) × Option Bool

/-- `P∞` of a configuration (Lemma 1), or `∅` if there is none. -/
noncomputable def pinf (k Δ : ℕ) (m : Multiset (Set (Trit k))) : Set (Trit k) := by
  classical
  exact if h : ∃ P, Δ - 2 ^ (4 ^ k) ≤ m.count P ∧ ones k ∈ P then h.choose else ∅

theorem pinf_spec {Δ : ℕ} {m : Multiset (Set (Trit k))}
    (h : ∃ P, Δ - 2 ^ (4 ^ k) ≤ m.count P ∧ ones k ∈ P) :
    Δ - 2 ^ (4 ^ k) ≤ m.count (pinf k Δ m) ∧ ones k ∈ pinf k Δ m := by
  unfold pinf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- A multiset below `t.map f` is the image of a multiset below `t`. -/
theorem exists_le_map_eq {α β : Type*} [DecidableEq α] (f : β → α) (t : Multiset β) :
    ∀ {s : Multiset α}, s ≤ t.map f → ∃ u ≤ t, u.map f = s := by
  induction t using Multiset.induction_on with
  | empty =>
    intro s hs
    exact ⟨0, le_rfl, by simpa using (Multiset.le_zero.1 (by simpa using hs)).symm⟩
  | cons b t ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases hb : f b ∈ s
    · obtain ⟨u, hu, hu'⟩ := ih (s := s.erase (f b)) (Multiset.erase_le_iff_le_cons.2 hs)
      refine ⟨b ::ₘ u, Multiset.cons_le_cons b hu, ?_⟩
      rw [Multiset.map_cons, hu', Multiset.cons_erase hb]
    · obtain ⟨u, hu, hu'⟩ := ih ((Multiset.le_cons_of_notMem hb).1 hs)
      exact ⟨u, hu.trans (Multiset.le_cons_self _ _), hu'⟩

/-- If at least `Δ - M` of the ports carry `P`, at most `M` do not. -/
theorem card_filter_ne_le {Δ M : ℕ} {Qf : ℕ → Set (Trit k)} {P : Set (Trit k)}
    (h : Δ - M ≤ ((Multiset.range Δ).map Qf).count P) :
    Multiset.card ((Multiset.range Δ).filter fun i => Qf i ≠ P) ≤ M := by
  have h1 := congrArg Multiset.card (Multiset.filter_add_not (fun i => Qf i = P)
    (Multiset.range Δ))
  rw [Multiset.card_add, Multiset.card_range] at h1
  rw [Multiset.count_map] at h
  have h2 : Multiset.filter (fun a => P = Qf a) (Multiset.range Δ) =
      Multiset.filter (fun a => Qf a = P) (Multiset.range Δ) :=
    Multiset.filter_congr fun _ _ => eq_comm
  rw [h2] at h
  simp only [ne_eq]
  omega

section
variable (Δ : ℕ)

/-- The pair `(Q_i, β(i))` of port `i`. -/
noncomputable def rb (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool) (i : ℕ) : PLabel k :=
  (Qf i, if Qf i = pinf k Δ ((Multiset.range Δ).map Qf) then none else some (α i))

/-- The multiset `R^v`. -/
noncomputable def Rv (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool) : Multiset (PLabel k) :=
  (Multiset.range Δ).map (rb Δ Qf α)

/-- The relation behind `N(J)`, in terms of pairs `(Q, β)`. -/
def Nrel (y x : PLabel k) : Prop :=
  ({y.1, x.1} : Multiset _) ∈ (tritOne k).g Δ ∧ y.2 ≠ x.2 ∧ y.2 ≠ none ∧ x.2 ≠ none

open Classical in
/-- `S ⊆ R` has the properties of `J*` in Lemma 2. -/
def GoodS (R S : Multiset (PLabel k)) : Prop :=
  S ≤ R ∧
  (∀ x ∈ S, ({x.1, pinf k Δ (R.map Prod.fst)} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ x.1) ∧
  Multiset.card (R.filter fun y => ∃ x ∈ S, Nrel Δ y x) < Multiset.card S ∧
  ∀ x ∈ S, ∀ y ∈ R, (∃ x' ∈ S, Nrel Δ y x') → x.2 ≠ y.2

open Classical in
/-- The selected `J*`, as a multiset of pairs (a function of `R^v` only). -/
noncomputable def sel (R : Multiset (PLabel k)) : Multiset (PLabel k) :=
  if h : ∃ S, GoodS Δ R S then h.choose else 0

open Classical in
/-- The ports realizing `sel R^v` (the paper's `J*`). -/
noncomputable def Jset (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool) : Finset ℕ :=
  if h : ∃ J : Finset ℕ, J ⊆ Finset.range Δ ∧ J.val.map (rb Δ Qf α) = sel Δ (Rv Δ Qf α)
  then h.choose else ∅

open Classical in
/-- The pointer output at port `i`. -/
noncomputable def ptr (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool) (i : ℕ) : Ptr :=
  if i ∈ Jset Δ Qf α then .demand
  else if ∃ x ∈ sel Δ (Rv Δ Qf α), Nrel Δ (rb Δ Qf α i) x then .accept else .none

/-- The code of `R^v`: `P∞` and the multiplicities, capped at `2^(4^k)`. -/
noncomputable def encR (R : Multiset (PLabel k)) :
    Set (Trit k) × (PLabel k → Fin (2 ^ (4 ^ k) + 1)) :=
  (pinf k Δ (R.map Prod.fst),
    fun x => ⟨min (R.count x) (2 ^ (4 ^ k)), Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- The possible values of `R^v`. -/
def VR (R : Multiset (PLabel k)) : Prop :=
  Multiset.card R = Δ ∧ (∀ x ∈ R, x.2 = none ↔ x.1 = pinf k Δ (R.map Prod.fst)) ∧
  Multiset.card (R.filter fun x => x.1 ≠ pinf k Δ (R.map Prod.fst)) ≤ 2 ^ (4 ^ k)

variable {Δ}

theorem VR.decomp {R : Multiset (PLabel k)} (h : VR Δ R) :
    R = R.filter (fun x => x.1 ≠ pinf k Δ (R.map Prod.fst)) +
      Multiset.replicate (Δ - Multiset.card (R.filter fun x => x.1 ≠ pinf k Δ (R.map Prod.fst)))
        (pinf k Δ (R.map Prod.fst), none) := by
  set P := pinf k Δ (R.map Prod.fst)
  have hs := Multiset.filter_add_not (fun x : PLabel k => x.1 ≠ P) R
  have hc := congrArg Multiset.card hs
  rw [Multiset.card_add, h.1] at hc
  conv_lhs => rw [← hs]
  congr 1
  rw [Multiset.eq_replicate]
  refine ⟨by omega, fun b hb => ?_⟩
  rw [Multiset.mem_filter, not_not] at hb
  exact Prod.ext hb.2 ((h.2.1 b hb.1).2 hb.2)

theorem encR_inj {R R' : Multiset (PLabel k)} (h : VR Δ R) (h' : VR Δ R')
    (he : encR Δ R = encR Δ R') : R = R' := by
  simp only [encR, Prod.mk.injEq] at he
  obtain ⟨hP, hf⟩ := he
  have hfilt : R.filter (fun x => x.1 ≠ pinf k Δ (R'.map Prod.fst)) =
      R'.filter (fun x => x.1 ≠ pinf k Δ (R'.map Prod.fst)) := by
    ext x
    rw [Multiset.count_filter, Multiset.count_filter]
    split_ifs with hx
    · have e := congrArg Fin.val (congrFun hf x)
      simp only at e
      have b1 : R.count x ≤ 2 ^ (4 ^ k) := by
        refine le_trans ?_ h.2.2
        rw [← hP] at hx
        rw [← Multiset.count_filter_of_pos (p := fun x : PLabel k => x.1 ≠ pinf k Δ (R.map Prod.fst)) hx]
        exact Multiset.count_le_card _ _
      have b2 : R'.count x ≤ 2 ^ (4 ^ k) := by
        refine le_trans ?_ h'.2.2
        rw [← Multiset.count_filter_of_pos (p := fun x : PLabel k => x.1 ≠ pinf k Δ (R'.map Prod.fst)) hx]
        exact Multiset.count_le_card _ _
      omega
    · rfl
  calc R = _ := h.decomp
    _ = _ := by rw [hP, hfilt]
    _ = R' := h'.decomp.symm

theorem map_fst_Rv (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool) :
    (Rv Δ Qf α).map Prod.fst = (Multiset.range Δ).map Qf := by
  simp [Rv, rb, Multiset.map_map, Function.comp_def]

theorem rb_snd_eq_none_iff {Qf : ℕ → Set (Trit k)} {α : ℕ → Bool} {i : ℕ} :
    (rb Δ Qf α i).2 = none ↔ Qf i = pinf k Δ ((Multiset.range Δ).map Qf) := by
  unfold rb
  split_ifs with h <;> simp [h]

theorem rb_snd_of_ne {Qf : ℕ → Set (Trit k)} {α : ℕ → Bool} {i : ℕ}
    (h : Qf i ≠ pinf k Δ ((Multiset.range Δ).map Qf)) : (rb Δ Qf α i).2 = some (α i) := by
  simp [rb, h]

theorem pinf_valid (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Qf : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Qf ∈ (tritOne k).h Δ) :
    Δ - 2 ^ (4 ^ k) ≤ ((Multiset.range Δ).map Qf).count (pinf k Δ ((Multiset.range Δ).map Qf)) ∧
      ones k ∈ pinf k Δ ((Multiset.range Δ).map Qf) := by
  obtain ⟨P, hP, -⟩ := lemma_1_card hk hΔ hQ (by simp)
  exact pinf_spec ⟨P, hP⟩

theorem rv_valid (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Qf : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Qf ∈ (tritOne k).h Δ) (α : ℕ → Bool) : VR Δ (Rv Δ Qf α) := by
  have hP := pinf_valid hk hΔ hQ
  refine ⟨by simp [Rv], ?_, ?_⟩ <;> rw [map_fst_Rv]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
    exact rb_snd_eq_none_iff
  · rw [Rv, Multiset.filter_map, Multiset.card_map]
    exact card_filter_ne_le hP.1

theorem sel_spec {R : Multiset (PLabel k)} (h : ∃ S, GoodS Δ R S) : GoodS Δ R (sel Δ R) := by
  unfold sel
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

theorem jset_spec (Qf : ℕ → Set (Trit k)) (α : ℕ → Bool)
    (h : GoodS Δ (Rv Δ Qf α) (sel Δ (Rv Δ Qf α))) :
    Jset Δ Qf α ⊆ Finset.range Δ ∧ (Jset Δ Qf α).val.map (rb Δ Qf α) = sel Δ (Rv Δ Qf α) := by
  have hex : ∃ J : Finset ℕ, J ⊆ Finset.range Δ ∧ J.val.map (rb Δ Qf α) = sel Δ (Rv Δ Qf α) := by
    obtain ⟨u, hu, hu'⟩ := exists_le_map_eq (rb Δ Qf α) (Multiset.range Δ) h.1
    refine ⟨⟨u, Multiset.nodup_of_le hu (Multiset.nodup_range Δ)⟩, fun x hx => ?_, hu'⟩
    exact Finset.mem_range.2 (Multiset.mem_range.1 (Multiset.mem_of_le hu hx))
  unfold Jset
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

/-- Lemma 2 provides a selection `J*` with the required properties. -/
theorem exists_goodS (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Qf : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Qf ∈ (tritOne k).h Δ) (α : ℕ → Bool) :
    ∃ S, GoodS Δ (Rv Δ Qf α) S := by
  classical
  have hP := pinf_valid hk hΔ hQ
  set P := pinf k Δ ((Multiset.range Δ).map Qf) with hPdef
  obtain ⟨J, hJI, hJc, hJα⟩ := lemma_2_aux hΔ hQ hP α
  have hJI' : ∀ j ∈ J, j < Δ ∧ ({Qf j, P} : Multiset _) ∉ (tritOne k).g Δ ∧ ones k ∉ Qf j :=
    fun j hj => by
      have := Finset.mem_filter.1 (hJI hj)
      exact ⟨Finset.mem_range.1 this.1, this.2⟩
  have hJne : ∀ j ∈ J, Qf j ≠ P := fun j hj h => (hJI' j hj).2.2 (h ▸ hP.2)
  have hN : ∀ i, (∃ x ∈ J.val.map (rb Δ Qf α), Nrel Δ (rb Δ Qf α i) x) ↔
      ∃ j ∈ J, ({Qf i, Qf j} : Multiset _) ∈ (tritOne k).g Δ ∧ α i ≠ α j := by
    intro i
    constructor
    · rintro ⟨x, hx, hg, hne, hn1, -⟩
      obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
      have hi : Qf i ≠ P := fun h => hn1 (rb_snd_eq_none_iff.2 h)
      refine ⟨j, hj, hg, fun he => hne ?_⟩
      rw [rb_snd_of_ne (hJne j hj), rb_snd_of_ne hi, he]
    · rintro ⟨j, hj, hg, hne⟩
      have hi : Qf i ≠ P := by
        intro h
        apply (hJI' j hj).2.1
        rw [← h, Multiset.pair_comm]
        exact hg
      refine ⟨rb Δ Qf α j, Multiset.mem_map_of_mem _ hj, hg, ?_, ?_, ?_⟩
      · rw [rb_snd_of_ne hi, rb_snd_of_ne (hJne j hj)]; simpa using hne
      · rw [rb_snd_of_ne hi]; simp
      · rw [rb_snd_of_ne (hJne j hj)]; simp
  refine ⟨J.val.map (rb Δ Qf α), ?_, ?_, ?_, ?_⟩
  · refine Multiset.map_le_map ?_
    have := Finset.val_le_iff.2 (hJI.trans (Finset.filter_subset _ _))
    simpa using this
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
    rw [map_fst_Rv]
    exact (hJI' j hj).2
  · rw [Rv, Multiset.filter_map, Multiset.card_map, Multiset.card_map, Finset.card_val]
    convert hJc using 1
    rw [← Finset.card_val, Finset.filter_val, Finset.range_val]
    congr 1
    exact Multiset.filter_congr fun i _ => hN i
  · intro x hx y hy hy'
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hy
    have hαne := hJα j hj i
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 (Multiset.mem_range.1 hi), (hN i).1 hy'⟩)
    obtain ⟨x', -, -, -, hn1, -⟩ := hy'
    have hi' : Qf i ≠ P := fun h => hn1 (rb_snd_eq_none_iff.2 h)
    rw [rb_snd_of_ne (hJne j hj), rb_snd_of_ne hi']
    simpa using hαne

end

/-! ### Colours -/

theorem exp_bound (hk : 2 ≤ k) : 3 ^ k + 2 * k + 2 ≤ 5 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ, pow_succ]; omega

theorem card_code_le (hk : 2 ≤ k) :
    Fintype.card (Set (Trit k) × (PLabel k → Fin (2 ^ (4 ^ k) + 1))) ≤ 2 ^ 2 ^ 5 ^ k := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_set, Fintype.card_option,
    Fintype.card_bool, Fintype.card_fin]
  have hB : 4 ≤ 4 ^ k := by
    calc 4 = 4 ^ 1 := rfl
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 3 ^ k < 2 ^ 3 ^ k := Nat.lt_two_pow_self
  have h1 : 2 ^ 4 ^ k + 1 ≤ 2 ^ (4 ^ k + 1) := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := 4 ^ k); omega
  have hexp : 3 ^ k + (4 ^ k + 1) * (2 ^ 3 ^ k * (2 + 1)) ≤ 2 ^ 5 ^ k := by
    have e1 : 3 ^ k + (4 ^ k + 1) * (2 ^ 3 ^ k * (2 + 1)) ≤ 2 ^ 3 ^ k * 4 ^ (k + 1) := by
      rw [pow_succ]
      have := Nat.mul_le_mul_left (2 ^ 3 ^ k) hB
      nlinarith
    have e2 : 2 ^ 3 ^ k * 4 ^ (k + 1) = 2 ^ (3 ^ k + 2 * (k + 1)) := by
      rw [show 2 ^ (3 ^ k + 2 * (k + 1)) = 2 ^ 3 ^ k * (2 ^ 2) ^ (k + 1) by
        rw [pow_add, pow_mul]]
      norm_num
    rw [e2] at e1
    exact e1.trans (Nat.pow_le_pow_right (by norm_num) (by have := exp_bound hk; omega))
  calc 2 ^ 3 ^ k * (2 ^ 4 ^ k + 1) ^ (2 ^ 3 ^ k * (2 + 1))
      ≤ 2 ^ 3 ^ k * (2 ^ (4 ^ k + 1)) ^ (2 ^ 3 ^ k * (2 + 1)) := by gcongr
    _ = 2 ^ (3 ^ k + (4 ^ k + 1) * (2 ^ 3 ^ k * (2 + 1))) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

/-- An injection of the codes into the `k'` colours. -/
noncomputable def codeEmb (hk : 2 ≤ k) :
    (Set (Trit k) × (PLabel k → Fin (2 ^ (4 ^ k) + 1))) ↪ Fin (2 ^ 2 ^ 5 ^ k) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin]; exact card_code_le hk))

/-- The colour `c(R^v)`. -/
noncomputable def col (hk : 2 ≤ k) (Δ : ℕ) (R : Multiset (PLabel k)) : Fin (2 ^ 2 ^ 5 ^ k) :=
  codeEmb hk (encR Δ R)

theorem col_inj (hk : 2 ≤ k) {Δ : ℕ} {R R' : Multiset (PLabel k)} (h : VR Δ R) (h' : VR Δ R')
    (he : col hk Δ R = col hk Δ R') : R = R' :=
  encR_inj h h' ((codeEmb hk).injective he)

/-! ### Correctness of the post-processing -/

section
variable {Δ : ℕ}

theorem mem_jset_of_ptr {Qf : ℕ → Set (Trit k)} {α : ℕ → Bool} {i : ℕ}
    (h : ptr Δ Qf α i = .demand) : i ∈ Jset Δ Qf α := by
  unfold ptr at h
  split_ifs at h with h1 h2
  exact h1

/-- Node condition: one colour; `#⊸ < #→` and `#⊸ ≤ 2^(4^k) < k' + 1`. -/
theorem node_ok (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Qf : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Qf ∈ (tritOne k).h Δ) (α : ℕ → Bool) :
    (Multiset.range Δ).map (fun i => (col hk Δ (Rv Δ Qf α), ptr Δ Qf α i)) ∈
      (superweak (2 ^ 2 ^ 5 ^ k)).h Δ := by
  classical
  have hS := sel_spec (exists_goodS hk hΔ hQ α)
  obtain ⟨hJsub, hJmap⟩ := jset_spec Qf α hS
  have hP := pinf_valid hk hΔ hQ
  refine ⟨by simp, ⟨col hk Δ (Rv Δ Qf α), by simp⟩, ?_⟩
  simp only [Multiset.filter_map, Multiset.card_map, Function.comp_def]
  have hdem : Multiset.card ((Multiset.range Δ).filter fun i => ptr Δ Qf α i = .demand) =
      Multiset.card (sel Δ (Rv Δ Qf α)) := by
    rw [← hJmap, Multiset.card_map]
    congr 1
    refine (Multiset.Nodup.ext (Multiset.Nodup.filter _ (Multiset.nodup_range Δ))
      (Jset Δ Qf α).nodup).2 fun i => ?_
    rw [Multiset.mem_filter, Finset.mem_val]
    constructor
    · exact fun h => mem_jset_of_ptr h.2
    · intro h
      refine ⟨Multiset.mem_range.2 (Finset.mem_range.1 (hJsub h)), ?_⟩
      simp [ptr, h]
  have hacc_N : ∀ i, ptr Δ Qf α i = .accept →
      ∃ x ∈ sel Δ (Rv Δ Qf α), Nrel Δ (rb Δ Qf α i) x := by
    intro i h
    unfold ptr at h
    split_ifs at h with h1 h2
    exact h2
  have hacc1 : Multiset.card ((Multiset.range Δ).filter fun i => ptr Δ Qf α i = .accept) ≤
      Multiset.card ((Rv Δ Qf α).filter fun y => ∃ x ∈ sel Δ (Rv Δ Qf α), Nrel Δ y x) := by
    rw [Rv, Multiset.filter_map, Multiset.card_map]
    exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun i h => hacc_N i h)
  have hacc2 : Multiset.card ((Multiset.range Δ).filter fun i => ptr Δ Qf α i = .accept) ≤
      2 ^ (4 ^ k) := by
    refine le_trans (Multiset.card_le_card (Multiset.monotone_filter_right _
      (q := fun i => Qf i ≠ pinf k Δ ((Multiset.range Δ).map Qf)) fun i h => ?_))
      (card_filter_ne_le hP.1)
    obtain ⟨x, -, -, -, hn, -⟩ := hacc_N i h
    exact fun he => hn (rb_snd_eq_none_iff.2 he)
  have hlt := hS.2.2.1
  have hk' : 2 ^ (4 ^ k) ≤ 2 ^ 2 ^ 5 ^ k := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    calc 4 ^ k ≤ 5 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ ≤ 2 ^ 5 ^ k := Nat.lt_two_pow_self.le
  refine lt_min (by omega) ?_
  rw [hdem]
  exact lt_of_le_of_lt hacc1 (by convert hlt using 3)

/-- Edge condition: if `u` demands on an edge and `R^u = R^v`, then `v` accepts on it. -/
theorem edge_ok (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) {Qf Qf' : ℕ → Set (Trit k)}
    (hQ : (Multiset.range Δ).map Qf ∈ (tritOne k).h Δ)
    (hQ' : (Multiset.range Δ).map Qf' ∈ (tritOne k).h Δ) {α α' : ℕ → Bool}
    (hR : Rv Δ Qf α = Rv Δ Qf' α') {a b : ℕ} (hb : b < Δ)
    (hg : ({Qf a, Qf' b} : Multiset _) ∈ (tritOne k).g Δ) (hα : α a ≠ α' b)
    (ha : a ∈ Jset Δ Qf α) : ptr Δ Qf' α' b = .accept := by
  classical
  have hS := sel_spec (exists_goodS hk hΔ hQ α)
  obtain ⟨-, hJmap⟩ := jset_spec Qf α hS
  have hS' := sel_spec (exists_goodS hk hΔ hQ' α')
  obtain ⟨-, hJmap'⟩ := jset_spec Qf' α' hS'
  have hPP : pinf k Δ ((Multiset.range Δ).map Qf) = pinf k Δ ((Multiset.range Δ).map Qf') := by
    rw [← map_fst_Rv (α := α), ← map_fst_Rv (α := α'), hR]
  have hP := pinf_valid hk hΔ hQ
  have hxa : rb Δ Qf α a ∈ sel Δ (Rv Δ Qf α) := by
    rw [← hJmap]; exact Multiset.mem_map_of_mem _ ha
  have hI := hS.2.1 _ hxa
  rw [map_fst_Rv] at hI
  have ha' : Qf a ≠ pinf k Δ ((Multiset.range Δ).map Qf) := fun h =>
    hI.2 (by show ones k ∈ Qf a; rw [h]; exact hP.2)
  have hb' : Qf' b ≠ pinf k Δ ((Multiset.range Δ).map Qf') := by
    intro h
    apply hI.1
    rw [hPP, ← h]
    exact hg
  have hN : Nrel Δ (rb Δ Qf' α' b) (rb Δ Qf α a) := by
    refine ⟨by rw [Multiset.pair_comm]; exact hg, ?_, ?_, ?_⟩
    · rw [rb_snd_of_ne hb', rb_snd_of_ne ha']; simpa using hα.symm
    · rw [rb_snd_of_ne hb']; simp
    · rw [rb_snd_of_ne ha']; simp
  rw [hR] at hxa
  have hex : ∃ x ∈ sel Δ (Rv Δ Qf' α'), Nrel Δ (rb Δ Qf' α' b) x := ⟨_, hxa, hN⟩
  have hnot : b ∉ Jset Δ Qf' α' := by
    intro hbJ
    have hy : rb Δ Qf' α' b ∈ sel Δ (Rv Δ Qf' α') := by
      rw [← hJmap']; exact Multiset.mem_map_of_mem _ hbJ
    exact hS'.2.2.2 _ hy _ (Multiset.mem_map_of_mem _ (Multiset.mem_range.2 hb)) hex rfl
  unfold ptr
  simp only [hnot, hex, ↓reduceIte]

end

/-- The orientation bit of port `i`, read from the node's input labels. -/
def alpha {I : Type} (o : I → Bool) (l : List I) (i : ℕ) : Bool := (l.map o).getD i false

theorem alpha_inputs {I : Type} {n : ℕ} (o : I → Bool) (G : LGraph I n) (v : Fin n) {i : ℕ}
    (hi : i < G.deg v) : alpha o (G.inputs v) i = o (G.inp v i) := by
  simp [alpha, LGraph.inputs, List.getD_eq_getElem?_getD, hi]

/-- Lemma 3 (same statement as `lemma_3` in `Lemmas123.lean`). -/
theorem lemma_3_aux (hk : 2 ≤ k) {I : Type} {n Δ t : ℕ} {𝒢 : Set (LGraph I n)}
    (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) {o : I → Bool}
    (hor : HasOrientation 𝒢 o) (h : SolvableIn 𝒢 (tritOne k) Δ t) :
    SolvableIn 𝒢 (superweak (2 ^ 2 ^ 5 ^ k)) Δ t := by
  refine h.post (fun l Qf i => (col hk Δ (Rv Δ Qf (alpha o l)), ptr Δ Qf (alpha o l) i)) ?_
  intro G hG out hout
  have hQv : ∀ v, (Multiset.range Δ).map (out v) ∈ (tritOne k).h Δ := fun v => by
    have := hout.2.2 v
    rwa [hreg G hG v] at this
  refine ⟨fun _ _ _ => trivial, fun v i hi => ?_, fun v => ?_⟩
  · have hj : G.rport v i < Δ := hreg G hG (G.nbr v i) ▸ G.G.rport_lt hi
    have hi' : i < Δ := hreg G hG v ▸ hi
    have hg := hout.2.1 v i hi
    have hor' := hor G hG v i hi
    rw [← alpha_inputs o G v hi, ← alpha_inputs o G (G.nbr v i) (hreg G hG (G.nbr v i) ▸ hj)]
      at hor'
    refine ⟨_, _, rfl, ?_⟩
    simp only
    by_cases hc : col hk Δ (Rv Δ (out v) (alpha o (G.inputs v))) =
        col hk Δ (Rv Δ (out (G.nbr v i)) (alpha o (G.inputs (G.nbr v i))))
    · have hR := col_inj hk (rv_valid hk hΔ (hQv v) _) (rv_valid hk hΔ (hQv _) _) hc
      right
      by_cases h1 : ptr Δ (out v) (alpha o (G.inputs v)) i = .demand
      · right; right
        exact edge_ok hk hΔ (hQv v) (hQv _) hR hj hg hor'.symm (mem_jset_of_ptr h1)
      by_cases h2 : ptr Δ (out (G.nbr v i)) (alpha o (G.inputs (G.nbr v i))) (G.rport v i) =
          .demand
      · right; left
        exact edge_ok hk hΔ (hQv _) (hQv v) hR.symm hi'
          (by rw [Multiset.pair_comm]; exact hg) hor' (mem_jset_of_ptr h2)
      cases hp1 : ptr Δ (out v) (alpha o (G.inputs v)) i <;>
        cases hp2 : ptr Δ (out (G.nbr v i)) (alpha o (G.inputs (G.nbr v i))) (G.rport v i) <;>
        simp_all
    · left; exact hc
  · rw [hreg G hG v]
    exact node_ok hk hΔ (hQv v) _

end AutomaticSpeedup
