import Papers.PODC2013.CongestedCliqueRouting.SortAlg3

/-!
# Correctness of Algorithm 3 (Lemmas 4.2–4.4)
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

variable {I V M : Type*} [Fintype V] [DecidableEq V] [LinearOrder M] [Nonempty V] {s : ℕ}
  [NeZero s] (e : V ≃ Fin s × Fin s)

namespace Alg3

variable {A : I → V → Finset M}

lemma sel_eq (d : I) (v : V) : sel e A d v = samples (A d v) (3 * s) := rfl

section Pure

/-- Hypotheses on the holdings: at most `3 s²` keys per node, disjoint. -/
structure Hyp (s : ℕ) (A : I → V → Finset M) : Prop where
  card_le : ∀ d v, (A d v).card ≤ 3 * (s * s)
  disj : ∀ d u v, u ≠ v → Disjoint (A d u) (A d v)

lemma card_sel_le (hH : Hyp s A) (d : I) (v : V) : (sel e A d v).card ≤ s := by
  rw [sel_eq, card_samples _ (by have := one_le_s (s := s); omega)]
  exact Nat.div_le_of_le_mul (by have := hH.card_le d v; nlinarith)

lemma rk_sel_lt (hH : Hyp s A) {d : I} {v : V} {x : M} (hx : x ∈ sel e A d v) :
    rk (sel e A d v) x < s :=
  lt_of_lt_of_le (rk_lt_card hx) (card_sel_le e hH d v)

lemma selAt_eq_some_iff {d : I} {v : V} {j : Fin s} {x : M} :
    selAt e A d v j = some x ↔ x ∈ sel e A d v ∧ rk (sel e A d v) x = j := by
  constructor
  · intro h
    have := pick_mem h
    simpa using this
  · rintro ⟨hx, hj⟩
    apply pick_eq_some_of_card_le_one _ (by simp [hx, hj])
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact rk_injOn _ ha.1 hb.1 (ha.2.trans hb.2.symm)

lemma exists_selAt (hH : Hyp s A) {d : I} {v : V} {x : M} :
    (∃ j, selAt e A d v j = some x) ↔ x ∈ sel e A d v := by
  constructor
  · rintro ⟨j, h⟩; exact ((selAt_eq_some_iff e).1 h).1
  · intro hx
    exact ⟨⟨_, rk_sel_lt e hH hx⟩, (selAt_eq_some_iff e).2 ⟨hx, rfl⟩⟩

lemma card_U3_le (hH : Hyp s A) (d : I) (a : Fin s) : (U3 e A d a).card ≤ s * s := by
  calc (U3 e A d a).card ≤ ∑ b, (sel e A d (node e a b)).card := card_biUnion_le
    _ ≤ ∑ _b : Fin s, s := sum_le_sum fun b _ => card_sel_le e hH d _
    _ = s * s := by simp

lemma bk_mono (d : I) (a : Fin s) : Monotone (bk e A d a) := fun _ _ h => bucketOf_mono _ h

lemma disj_group (hH : Hyp s A) (d : I) (a : Fin s) :
    ∀ b b' : Fin s, b ≠ b' → Disjoint (A d (node e a b)) (A d (node e a b')) := by
  intro b b' h
  apply hH.disj
  intro h'
  apply h
  have := congrArg (mem e) h'
  simpa using this

/-- Lemma 4.3: every bucket of group `a` has fewer than `6 s²` keys. -/
lemma sum_bucket (hH : Hyp s A) (d : I) (a : Fin s) (y : ℕ) :
    ∑ b, ((A d (node e a b)).filter fun x => bk e A d a x = y).card + s ≤ 6 * (s * s) := by
  have hs := one_le_s (s := s)
  have h1 := sum_bucket_le (ι := Fin s) (H := fun b => A d (node e a b)) (disj_group e hH d a)
    (p := 3 * s) (by omega) (bk_mono e (A := A) d a) y
  have h2 : ((univ.biUnion fun b => samples (A d (node e a b)) (3 * s)).filter
      fun x => bk e A d a x = y).card ≤ s :=
    card_fiber_bucketOf_delims (by omega) (card_U3_le e hH d a) y
  simp only [Fintype.card_fin] at h1
  calc _ ≤ 3 * s * (((univ.biUnion fun b => samples (A d (node e a b)) (3 * s)).filter
        fun x => bk e A d a x = y).card + s) := h1
    _ ≤ 3 * s * (s + s) := Nat.mul_le_mul_left _ (by omega)
    _ = 6 * (s * s) := by ring

lemma Cm_row (hH : Hyp s A) (d : I) (a b : Fin s) : ∑ y, Cm e A d a b y = (A d (node e a b)).card := by
  unfold Cm cnt
  rw [card_eq_sum_card_fiberwise (f := fun x => (⟨bk e A d a x, bk_lt e A d a x⟩ : Fin s))
    (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  refine filter_congr fun x _ => ?_
  simp [Fin.ext_iff]

lemma Cm_col (hH : Hyp s A) (d : I) (a y : Fin s) : ∑ b, Cm e A d a b y ≤ 6 * (s * s) := by
  have := sum_bucket e hH d a y
  unfold Cm cnt
  simp only [grp_node]
  omega

lemma Rp_spec (hH : Hyp s A) (d : I) (a : Fin s) :
    (∀ b y, ∑ c, Rp e A d a c b y = Cm e A d a b y) ∧ (∀ c b, ∑ y, Rp e A d a c b y ≤ 6) ∧
      (∀ c y, ∑ b, Rp e A d a c b y ≤ 6) := by
  refine splitParts_spec (ι := V) (fun b => ?_) (fun y => ?_)
  · rw [Cm_row e hH, card_V e]
    have := hH.card_le d (node e a b)
    nlinarith
  · rw [card_V e]
    have := Cm_col e hH d a y
    nlinarith

lemma via_cap (hH : Hyp s A) (d : I) (v : V) (y : ℕ) :
    ((A d v).filter fun x => bk e A d (grp e v) x = y).card ≤
      ∑ c, (if h : y < s then Rp e A d (grp e v) c (mem e v) ⟨y, h⟩ else 0) := by
  by_cases h : y < s
  · simp only [h, dif_pos]
    rw [(Rp_spec e hH d _).1]
    simp [Cm, cnt]
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · rw [filter_eq_empty_iff]
      intro x _ hx
      have := bk_lt e A d (grp e v) x
      omega

lemma card_via_le (hH : Hyp s A) (d : I) (v c : V) :
    ((A d v).filter fun x => via e A d v x = c).card ≤ 6 := by
  rw [card_filter_eq_sum_fiber (A d v) (via e A d v)
    (fun x => (⟨bk e A d (grp e v) x, bk_lt e A d _ x⟩ : Fin s)) c]
  refine le_trans (sum_le_sum fun y _ => ?_) ((Rp_spec e hH d (grp e v)).2.1 c (mem e v))
  have := assign_le (via_cap e hH d v) (y : ℕ) c
  simp only [Fin.is_lt, dif_pos] at this
  refine le_trans (le_of_eq (congrArg card (filter_congr fun x _ => ?_))) this
  simp only [via, Fin.ext_iff]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma tg_eq_iff {d : I} {v w : V} {x : M} :
    tg e A d v x = w ↔ grp e v = grp e w ∧ bk e A d (grp e v) x = mem e w := by
  unfold tg
  rw [node_eq_iff]
  simp [Fin.ext_iff, eq_comm]

lemma len_Q4 (hH : Hyp s A) (d : I) (v c : V) :
    2 * ((A d v).filter fun x => via e A d v x = c).card ≤ SB := by
  have := card_via_le e hH d v c
  simp only [SB]; omega

lemma mem_fwd_Q4 (hH : Hyp s A) {d : I} {c w : V} {x : M} :
    x ∈ fwd (enc e) (fun u => Q4 e A d u c) w ↔
      ∃ u, x ∈ A d u ∧ via e A d u x = c ∧ tg e A d u x = w :=
  mem_fwd_rr1 (enc_inj e) (fun u => len_Q4 e hH d u c)

lemma card_fwd_Q4 (hH : Hyp s A) (d : I) (c w : V) :
    (fwd (enc e) (fun u => Q4 e A d u c) w).card ≤ 6 := by
  have hsub : fwd (enc e) (fun u => Q4 e A d u c) w ⊆ univ.biUnion fun b =>
      (A d (node e (grp e w) b)).filter fun x =>
        bk e A d (grp e w) x = mem e w ∧ via e A d (node e (grp e w) b) x = c := by
    intro x hx
    obtain ⟨u, hu, hc, ht⟩ := (mem_fwd_Q4 e hH).1 hx
    rw [tg_eq_iff e] at ht
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    refine ⟨mem e u, ?_⟩
    rw [← ht.1, node_grp_mem]
    exact ⟨hu, ht.2, hc⟩
  refine le_trans (card_le_card hsub) (le_trans card_biUnion_le ?_)
  refine le_trans (sum_le_sum fun b _ => ?_) ((Rp_spec e hH d (grp e w)).2.2 c (mem e w))
  have := assign_le (via_cap e hH d (node e (grp e w) b)) (mem e w : ℕ) c
  simp only [Fin.is_lt, dif_pos, grp_node, mem_node] at this
  refine le_trans (le_of_eq (congrArg card (filter_congr fun x _ => ?_))) this
  simp [via]

/-- What member `w` holds at the end. -/
lemma mem_Bk (hH : Hyp s A) {d : I} {w : V} {x : M} :
    x ∈ Bk e A d w ↔ ∃ u, x ∈ A d u ∧ tg e A d u x = w := by
  unfold Bk
  rw [mem_rcvd]
  constructor
  · rintro ⟨c, hc⟩
    rw [Q5, msgsOf_rr2 (by simp only [SB]; have := card_fwd_Q4 e hH d c w; omega),
      mem_fwd_Q4 e hH] at hc
    obtain ⟨u, hu, -, ht⟩ := hc
    exact ⟨u, hu, ht⟩
  · rintro ⟨u, hu, ht⟩
    refine ⟨via e A d u x, ?_⟩
    rw [Q5, msgsOf_rr2 (by simp only [SB]; have := card_fwd_Q4 e hH d (via e A d u x) w; omega),
      mem_fwd_Q4 e hH]
    exact ⟨u, hu, rfl, ht⟩

lemma mem_Bk' (hH : Hyp s A) {d : I} {w : V} {x : M} :
    x ∈ Bk e A d w ↔ x ∈ GA e A d (grp e w) ∧ bk e A d (grp e w) x = mem e w := by
  rw [mem_Bk e hH]
  simp only [GA, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨u, hu, ht⟩
    rw [tg_eq_iff e] at ht
    refine ⟨⟨mem e u, ?_⟩, ht.1 ▸ ht.2⟩
    rw [← ht.1, node_grp_mem]; exact hu
  · rintro ⟨⟨b, hb⟩, hk⟩
    exact ⟨_, hb, (tg_eq_iff e).2 ⟨by simp, by simpa using hk⟩⟩

lemma card_Bk_lt (hH : Hyp s A) (d : I) (w : V) : (Bk e A d w).card < 6 * (s * s) := by
  have hsub : Bk e A d w ⊆ univ.biUnion fun b =>
      (A d (node e (grp e w) b)).filter fun x => bk e A d (grp e w) x = mem e w := by
    intro x hx
    rw [mem_Bk' e hH] at hx
    simp only [GA, mem_biUnion, mem_univ, true_and] at hx
    obtain ⟨⟨b, hb⟩, hk⟩ := hx
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    exact ⟨b, hb, hk⟩
  have := sum_bucket e hH d (grp e w) (mem e w)
  have := one_le_s (s := s)
  exact lt_of_le_of_lt (le_trans (card_le_card hsub) card_biUnion_le) (by omega)

lemma card_GA_filter (hH : Hyp s A) (d : I) (a y : Fin s) :
    ((GA e A d a).filter fun x => bk e A d a x = y).card = ∑ b, Cm e A d a b y := by
  unfold GA
  rw [filter_biUnion, card_biUnion]
  · simp [Cm, cnt]
  · intro b _ b' _ hb
    exact Finset.disjoint_filter_filter (disj_group e hH d a b b' hb)

/-- Lemma 4.2: member `w` knows the rank of each of its keys among all keys of its group. -/
lemma rk_GA (hH : Hyp s A) {d : I} {w : V} {x : M} (hx : x ∈ Bk e A d w) :
    rk (GA e A d (grp e w)) x =
      (∑ y ∈ univ.filter (· < mem e w), ∑ b, Cm e A d (grp e w) b y) + rk (Bk e A d w) x := by
  obtain ⟨hxG, hbk⟩ := (mem_Bk' e hH).1 hx
  rw [rk_eq_add (bk_mono e (A := A) d (grp e w)) hxG]
  congr 1
  · rw [card_eq_sum_card_fiberwise (f := fun x => (⟨bk e A d (grp e w) x, bk_lt e A d _ x⟩ : Fin s))
      (t := univ.filter (· < mem e w))]
    · refine sum_congr rfl fun y hy => ?_
      rw [← card_GA_filter e hH d (grp e w) y, filter_filter]
      congr 1
      refine filter_congr fun z _ => ?_
      simp only [mem_filter, mem_univ, true_and] at hy
      simp only [Fin.ext_iff, hbk]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact hy, h⟩
    · intro z hz
      simp only [coe_filter, mem_filter, Set.mem_setOf_eq, mem_univ, true_and] at hz ⊢
      rw [hbk] at hz
      exact hz.2
  · congr 1
    ext z
    rw [mem_Bk' e hH, mem_filter, hbk]

end Pure

/-! ### The run -/

section Spec

variable {K : Type*} {inpS : I → V → K} {msgs : I → V → Finset M} {S : Run I V M SB} {t0 : ℕ}
  (hS : ∀ d k, k < 6 → S d (t0 + k) = pkt e A d k)
  (hA : ∀ v, Determined inpS S t0 v fun d => A d v)
  (hH : Hyp s A)
  (hAh : ∀ d v x, x ∈ A d v → HoldsS msgs S d t0 v x)

include hS in
lemma S_eq (d : I) :
    S d t0 = Q0 e A d ∧ S d (t0 + 1) = Q1 e A d ∧ S d (t0 + 2) = Q2 e A d ∧
      S d (t0 + 3) = Q3 e A d ∧ S d (t0 + 4) = Q4 e A d ∧ S d (t0 + 5) = Q5 e A d :=
  ⟨by simpa [pkt] using hS d 0 (by norm_num), hS d 1 (by norm_num), hS d 2 (by norm_num),
    hS d 3 (by norm_num), hS d 4 (by norm_num), hS d 5 (by norm_num)⟩

include hS hH in
lemma U3_known (w : V) : Determined inpS S (t0 + 2) w fun d => U3 e A d (grp e w) := by
  refine ((determined_received (r := t0 + 1) (by omega) w).congr fun d => ?_)
  ext x
  show x ∈ U3 e A d (grp e w) ↔ x ∈ rcvd (S d (t0 + 1)) w
  rw [(S_eq e hS d).2.1, Q1, Q0, rcvd_fwdP_gak1 e (by simp [SB])]
  simp only [U3, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨j, hj⟩ := (exists_selAt e hH).2 hb
    exact ⟨b, j, hj⟩
  · rintro ⟨b, j, hj⟩
    exact ⟨b, (exists_selAt e hH).1 ⟨j, hj⟩⟩

include hS in
lemma Cm_known (w : V) : Determined inpS S (t0 + 4) w fun d => Cm e A d (grp e w) := by
  refine ((determined_recv (r := t0 + 3) (by omega) w).map
    (fun f => fun b y => numOfL (f (node e y b)))).congr fun d => ?_
  funext b y
  show Cm e A d (grp e w) b y = numOfL (S d (t0 + 3) (node e y b) w)
  rw [(S_eq e hS d).2.2.2.1, Q3, Q2, fwdP_gan1, numOfL_num (by simp [SB])]
  rfl

include hS in
lemma Bk_known (w : V) : Determined inpS S (t0 + 6) w fun d => Bk e A d w := by
  refine ((determined_received (r := t0 + 5) (by omega) w).congr fun d => ?_)
  show rcvd (Q5 e A d) w = rcvd (S d (t0 + 5)) w
  rw [(S_eq e hS d).2.2.2.2.2]

lemma via_congr {d d' : I} {v : V} (h1 : A d v = A d' v)
    (h2 : U3 e A d (grp e v) = U3 e A d' (grp e v))
    (h3 : Cm e A d (grp e v) = Cm e A d' (grp e v)) : via e A d v = via e A d' v := by
  unfold via Rp bk
  rw [h1, h2, h3]

lemma tg_congr {d d' : I} {v : V} (h2 : U3 e A d (grp e v) = U3 e A d' (grp e v)) :
    tg e A d v = tg e A d' v := by
  funext x
  unfold tg
  congr 2
  simp only [bk, h2]

include hS hA hH in
theorem isLocal_alg3 {k : ℕ} (hk : k < 6) (v : V) :
    Determined inpS S (t0 + k) v fun d => S d (t0 + k) v := by
  interval_cases k
  · intro d d' hv
    have h1 := (hA v) d d' hv
    simp only at h1
    simp only [Nat.add_zero, (S_eq e hS d).1, (S_eq e hS d').1, Q0]
    have : selAt e A d v = selAt e A d' v := by
      funext j; unfold selAt; rw [sel_eq, sel_eq, h1]
    funext w
    unfold gak1
    rw [this]
  · intro d d' hv
    funext w
    simp only [(S_eq e hS d).2.1, (S_eq e hS d').2.1, Q1, fwdP]
    rw [← (S_eq e hS d).1, ← (S_eq e hS d').1]
    exact hv.2 t0 (by omega) _
  · intro d d' hv
    have h1 := ((hA v).mono (by omega)) d d' hv
    have h2 := (U3_known e hS hH v) d d' hv
    simp only at h1 h2
    simp only [(S_eq e hS d).2.2.1, (S_eq e hS d').2.2.1, Q2]
    have : cnt e A d v = cnt e A d' v := by
      funext y; unfold cnt bk; rw [h1, h2]
    funext w
    unfold gan1
    rw [this]
  · intro d d' hv
    funext w
    simp only [(S_eq e hS d).2.2.2.1, (S_eq e hS d').2.2.2.1, Q3, fwdP]
    rw [← (S_eq e hS d).2.2.1, ← (S_eq e hS d').2.2.1]
    exact hv.2 (t0 + 2) (by omega) _
  · intro d d' hv
    have h1 := ((hA v).mono (by omega)) d d' hv
    have h2 := ((U3_known e hS hH v).mono (by omega)) d d' hv
    have h3 := (Cm_known e hS v) d d' hv
    simp only at h1 h2 h3
    simp only [(S_eq e hS d).2.2.2.2.1, (S_eq e hS d').2.2.2.2.1]
    funext c
    simp only [Q4]
    rw [h1, via_congr e h1 h2 h3, tg_congr e h2]
  · intro d d' hv
    funext w
    simp only [(S_eq e hS d).2.2.2.2.2, (S_eq e hS d').2.2.2.2.2, Q5]
    have : (fun u => Q4 e A d u v) = fun u => Q4 e A d' u v := by
      funext u
      rw [← (S_eq e hS d).2.2.2.2.1, ← (S_eq e hS d').2.2.2.2.1]
      exact hv.2 (t0 + 4) (by omega) u
    rw [this]

include hS hH hAh in
theorem valid_alg3 {d : I} {k : ℕ} (hk : k < 6) {u v : V} {i : Fin SB} {x : M}
    (h : S d (t0 + k) u v i = some (Item.msg x)) : HoldsS msgs S d (t0 + k) u x := by
  have hm : x ∈ msgsOf (S d (t0 + k) u v) := mem_msgsOf.2 ⟨i, h⟩
  interval_cases k
  · rw [Nat.add_zero, (S_eq e hS d).1, Q0] at hm
    obtain ⟨j, hj⟩ := msgsOf_gak1_sub e hm
    have := ((selAt_eq_some_iff e).1 hj).1
    rw [sel_eq] at this
    simpa using hAh d u x (mem_filter.1 this).1
  · rw [(S_eq e hS d).2.1, Q1, fwdP, ← (S_eq e hS d).1] at hm
    exact holdsS_of_mem_received (r := t0) (mem_biUnion.2 ⟨_, mem_univ _, hm⟩) (by omega)
  · rw [(S_eq e hS d).2.2.1, Q2, msgsOf_gan1] at hm; simp at hm
  · rw [(S_eq e hS d).2.2.2.1, Q3, fwdP, Q2, msgsOf_gan1] at hm; simp at hm
  · rw [(S_eq e hS d).2.2.2.2.1, Q4] at hm
    exact (hAh d u x (msgsOf_rr1_sub hm)).mono (by omega)
  · rw [(S_eq e hS d).2.2.2.2.2, Q5] at hm
    obtain ⟨u', hu'⟩ := fwd_sub (msgsOf_rr2_sub hm)
    rw [← (S_eq e hS d).2.2.2.2.1] at hu'
    exact holdsS_of_mem_received (r := t0 + 4) (mem_biUnion.2 ⟨_, mem_univ _, hu'⟩) (by omega)

include hS hH in
theorem nums_alg3 {d : I} {k : ℕ} (hk : k < 6) {u v : V} {i : Fin SB} {n : ℕ}
    (h : S d (t0 + k) u v i = some (Item.num n)) : n ≤ 3 * (s * s) := by
  interval_cases k
  · rw [Nat.add_zero, (S_eq e hS d).1, Q0] at h; exact (nums_gak1 e h).elim
  · rw [(S_eq e hS d).2.1, Q1, fwdP, Q0] at h; exact (nums_gak1 e h).elim
  · rw [(S_eq e hS d).2.2.1, Q2] at h
    obtain ⟨j, rfl⟩ := nums_gan1 e h
    exact le_trans (card_filter_le _ _) (hH.card_le d u)
  · rw [(S_eq e hS d).2.2.2.1, Q3, fwdP, Q2] at h
    obtain ⟨j, rfl⟩ := nums_gan1 e h
    exact le_trans (card_filter_le _ _) (hH.card_le d _)
  · rw [(S_eq e hS d).2.2.2.2.1, Q4] at h
    obtain ⟨x, rfl⟩ := nums_rr1 h
    have := enc_lt e (tg e A d u x)
    have := one_le_s (s := s)
    nlinarith
  · rw [(S_eq e hS d).2.2.2.2.2, Q5] at h; exact (nums_rr2 h).elim

include hS in
lemma holds_Bk {d : I} {w : V} {x : M} (hx : x ∈ Bk e A d w) :
    HoldsS msgs S d (t0 + 6) w x := by
  refine holdsS_of_mem_received (r := t0 + 5) ?_ (by omega)
  show x ∈ rcvd (S d (t0 + 5)) w
  rw [(S_eq e hS d).2.2.2.2.2]; exact hx

end Spec

end Alg3

end CongestedCliqueRouting
