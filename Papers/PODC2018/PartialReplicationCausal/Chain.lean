import Papers.PODC2018.PartialReplicationCausal.Inv

/-!
# The chain argument (core of Lemma 5)

When replica `i` applies an update `u` (the predicate of Step 4 holds), every update `a ↪ u` on a
register of `X_i` has already been applied at `i`. The paper argues via Lemma 4 (which is false,
see `Lemma4.lean`). We argue on a causal chain `a ↪ v₀ ↪ v₁ ↪ ⋯ ↪ v_m = u` of direct links, by
strong induction on its length `m`:

* if a replica occurs twice on the chain, or some intermediate update of the chain writes a
  register stored at `i`, the chain can be shortened (using safety of earlier steps);
* otherwise either every replica of the chain has `e_ji` (`j` the issuer of `a`) in its timestamp
  graph — then the counter `τ[e_ji]` carries the information about `a` along the chain up to `u`'s
  timestamp, and the predicate of Step 4 forces `a` to be applied first — or some replica `p_q` of
  the chain does not; the chain then forms a simple loop
  `(p_q, p_{q+1}, …, p_m, i, j = p_0, p_1, …, p_{q-1})` which is not a `(p_q, e_ji)`-loop, and each
  of the three failing conditions of Definition 6 yields a shorter chain.
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*} {X : ι → Set Reg} {s : State ι Reg}

/-- `v 0 ↪ v 1 ↪ ⋯ ↪ v m` by direct links (condition 1 of Definition 4). -/
def IsChainF (s : State ι Reg) (v : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ q < m, v (q + 1) < s.n ∧ v q ∈ (s.log (v (q + 1))).pre

lemma exists_chain_of_hb {a b : ℕ} (hab : HB s a b) :
    ∃ m, 0 < m ∧ ∃ v, v 0 = a ∧ v m = b ∧ IsChainF s v m := by
  induction hab with
  | @single b hb =>
    refine ⟨1, by omega, fun q => if q = 0 then a else b, by simp, by simp, ?_⟩
    intro q hq
    obtain rfl : q = 0 := by omega
    simpa using hb
  | @tail c b _ hcb ih =>
    obtain ⟨m, hm, v, hv0, hvm, hv⟩ := ih
    refine ⟨m + 1, by omega, fun q => if q ≤ m then v q else b, by simp [hv0], by simp, ?_⟩
    intro q hq
    by_cases hqm : q + 1 ≤ m
    · simp only [hqm, ite_true, show q ≤ m by omega]
      exact hv q (by omega)
    · obtain rfl : q = m := by omega
      simp only [le_refl, ite_true, show ¬ q + 1 ≤ q by omega, ite_false, hvm]
      exact hcb

/-- The update `a` is the first update of the chain, or an earlier update of the same replica. -/
def Start (s : State ι Reg) (a w : ℕ) : Prop :=
  a = w ∨ ((s.log w).src = (s.log a).src ∧ a ∈ (s.log w).pre)

section chain

variable (h : Inv X s) {v : ℕ → ℕ} {m : ℕ} (hv : IsChainF s v m) (hvn : v m < s.n)
include h hv hvn

lemma IsChainF.lt_n {q : ℕ} (hq : q ≤ m) : v q < s.n := by
  rcases Nat.lt_or_ge q m with hlt | hge
  · exact h.pre_lt_n (hv q hlt).1 (hv q hlt).2
  · obtain rfl : q = m := by omega
    exact hvn

omit h hvn in
lemma IsChainF.hb {x y : ℕ} (hxy : x < y) (hy : y ≤ m) : HB s (v x) (v y) := by
  induction y with
  | zero => omega
  | succ y ih =>
    have hl := hv y (by omega)
    rcases Nat.lt_or_ge x y with hlt | hge
    · exact .tail (ih hlt (by omega)) hl
    · obtain rfl : x = y := by omega
      exact .single hl

omit h hvn in
lemma IsChainF.drop (y : ℕ) : IsChainF s (fun q => v (q + y)) (m - y) := by
  intro q hq
  have := hv (q + y) (by omega)
  simpa [show q + 1 + y = q + y + 1 by omega] using this

/-- Remove `v (x+1), …, v (y-1)` from the chain, given a direct link `v x ↪ v y`. -/
lemma IsChainF.splice {x y : ℕ} (hxy : x < y) (hy : y ≤ m) (hlink : v x ∈ (s.log (v y)).pre) :
    IsChainF s (fun q => if q ≤ x then v q else v (q + (y - x - 1))) (m - (y - x - 1)) := by
  intro q hq
  by_cases hqx : q + 1 ≤ x
  · simp only [hqx, ite_true, show q ≤ x by omega]
    exact hv q (by omega)
  · by_cases hq' : q = x
    · subst hq'
      simp only [le_refl, ite_true, show ¬ q + 1 ≤ q by omega, ite_false,
        show q + 1 + (y - q - 1) = y by omega]
      exact ⟨IsChainF.lt_n h hv hvn hy, hlink⟩
    · simp only [hqx, ite_false, show ¬ q ≤ x by omega,
        show q + 1 + (y - x - 1) = q + (y - x - 1) + 1 by omega]
      exact hv _ (by omega)

/-- Replace the prefix `v 0, …, v (y-1)` of the chain by `a`, given a direct link `a ↪ v y`. -/
lemma IsChainF.restart {a y : ℕ} (hy : y ≤ m) (hlink : a ∈ (s.log (v y)).pre) :
    IsChainF s (fun q => if q = 0 then a else v (q - 1 + y)) (m - y + 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · subst hq0
    simp only [ite_true, show ¬ (0 + 1 = 0) by omega, ite_false, show 0 + 1 - 1 + y = y by omega]
    exact ⟨IsChainF.lt_n h hv hvn hy, hlink⟩
  · simp only [hq0, ite_false, show ¬ (q + 1 = 0) by omega,
      show q + 1 - 1 + y = q - 1 + y + 1 by omega]
    exact hv _ (by omega)

lemma Start.hb {a : ℕ} (hst : Start s a (v 0)) {y : ℕ} (hy0 : 0 < y) (hy : y ≤ m) :
    HB s a (v y) := by
  rcases hst with rfl | ⟨_, hpre⟩
  · exact IsChainF.hb hv hy0 hy
  · exact .head ⟨IsChainF.lt_n h hv hvn (Nat.zero_le _), hpre⟩ (IsChainF.hb hv hy0 hy)

end chain

/-! ### The loop formed by a simple chain -/

lemma map_range_shift (f : ℕ → ι) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map fun t => f (t + 1) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

/-- A simple chain of replicas `p 0, …, p m` (consecutive ones adjacent, `p m` adjacent to `i`,
`i` adjacent to `p 0`), seen from `p q`, is the simple loop
`(p q, p (q+1), …, p m, i, p 0, p 1, …, p (q-1))`; if the three conditions of Definition 6 hold for
it, it is a `(p q, e_{p 0, i})`-loop. -/
lemma isLoop_of_chain (p : ℕ → ι) {m q : ℕ} (i : ι) (hq1 : 1 ≤ q) (hqm : q ≤ m)
    (hinj : ∀ x ≤ m, ∀ y ≤ m, p x = p y → x = y) (hpi : ∀ x ≤ m, p x ≠ i)
    (hadj : ∀ t < m, Adj X (p t) (p (t + 1))) (hmi : Adj X (p m) i) (hij : Adj X i (p 0))
    (h1 : ∃ x ∈ X (p 0) ∩ X i, ∀ y, q < y → y ≤ m → x ∉ X (p y))
    (h2 : ∃ x ∈ X (p 0) ∩ X (p 1), ∀ y, q < y → y ≤ m → x ∉ X (p y))
    (h3 : ∀ b, 1 ≤ b → b < q → ∃ x ∈ X (p b) ∩ X (p (b + 1)), x ∉ X i ∧
      ∀ y, q < y → y ≤ m → x ∉ X (p y)) :
    IsLoop X (p q) (p 0) i ((List.range (m - q)).map fun t => p (q + 1 + t))
      ((List.range (q - 1)).map fun t => p (t + 1)) := by
  have hL : ∀ z, z ∈ (List.range (m - q)).map (fun t => p (q + 1 + t)) ↔
      ∃ y, q < y ∧ y ≤ m ∧ p y = z := by
    intro z
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨q + 1 + t, by omega, by omega, rfl⟩
    · rintro ⟨y, hy1, hy2, rfl⟩; exact ⟨y - q - 1, by omega, by congr 1; omega⟩
  have hR : (List.range (q - 1)).map (fun t => p (t + 1)) ++ [p q] =
      (List.range q).map fun t => p (t + 1) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [List.range_succ, List.map_append]; simp
  have hA : p q :: (List.range (m - q)).map (fun t => p (q + 1 + t)) =
      (List.range (m - q + 1)).map fun t => p (q + t) := by
    rw [map_range_shift]; simp only [Nat.add_zero]
    congr 1; apply List.map_congr_left; intro t _; congr 1; omega
  have hB : p 0 :: (List.range q).map (fun t => p (t + 1)) = (List.range (q + 1)).map p := by
    rw [map_range_shift]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the loop is simple
    have hB' : p 0 :: (List.range (q - 1)).map (fun t => p (t + 1)) = (List.range q).map p := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [map_range_shift]; rfl
    have : p q :: ((List.range (m - q)).map (fun t => p (q + 1 + t)) ++
        i :: p 0 :: (List.range (q - 1)).map fun t => p (t + 1)) =
        (List.range (m - q + 1)).map (fun t => p (q + t)) ++ i :: (List.range q).map p := by
      rw [← hA, ← hB']; simp
    rw [this, List.nodup_append, List.nodup_cons]
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro x hx y hy hxy
      simp only [List.mem_range] at hx hy
      have := hinj _ (by omega) _ (by omega) hxy; omega
    · simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro x hx hxi; exact hpi x (by omega) hxi
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro x hx y hy hxy
      simp only [List.mem_range] at hx hy
      exact hinj _ (by omega) _ (by omega) hxy
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_map, List.mem_range] at ha
      obtain ⟨t, ht, rfl⟩ := ha
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hb
      rcases hb with hb | ⟨t', ht', hb⟩
      · exact hpi _ (by omega) hb
      · have := hinj _ (by omega) _ (by omega) hb; omega
  · -- consecutive replicas are adjacent
    have : p q :: ((List.range (m - q)).map (fun t => p (q + 1 + t)) ++
        i :: p 0 :: (List.range (q - 1)).map fun t => p (t + 1)) ++ [p q] =
        (List.range (m - q + 1)).map (fun t => p (q + t)) ++ i :: (List.range (q + 1)).map p := by
      rw [← hA, ← hB, ← hR]; simp
    rw [this, List.isChain_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.isChain_map, List.isChain_range_succ]
      intro t ht
      have := hadj (q + t) (by omega)
      simpa [show q + (t + 1) = q + t + 1 by omega] using this
    · rw [List.isChain_cons]
      refine ⟨?_, ?_⟩
      · intro y hy
        rw [map_range_shift] at hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy; exact hij
      · rw [List.isChain_map, List.isChain_range_succ]
        intro t ht; exact hadj t (by omega)
    · intro x hx y hy
      rw [List.getLast?_map, List.getLast?_range] at hx
      simp only [Option.mem_def] at hx
      simp [show q + (m - q) = m by omega] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hx hy; exact hmi
  · obtain ⟨x, hx, hx'⟩ := h1
    refine ⟨x, hx, fun z hz => ?_⟩
    obtain ⟨y, hy1, hy2, rfl⟩ := (hL z).1 hz
    exact hx' y hy1 hy2
  · obtain ⟨x, hx, hx'⟩ := h2
    have hhd : ((List.range (q - 1)).map fun t => p (t + 1)).headD (p q) = p 1 := by
      obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      subst hq'
      cases q' with
      | zero => simp
      | succ q'' => rw [show q'' + 1 + 1 - 1 = q'' + 1 by omega, map_range_shift]; simp
    rw [hhd]
    refine ⟨x, hx, fun z hz => ?_⟩
    obtain ⟨y, hy1, hy2, rfl⟩ := (hL z).1 hz
    exact hx' y hy1 hy2
  · rw [hR, List.isChain_map, List.isChain_range]
    intro t ht
    obtain ⟨x, hx, hxi, hx'⟩ := h3 (t + 1) (by omega) (by omega)
    refine ⟨x, hx, hxi, fun z hz => ?_⟩
    obtain ⟨y, hy1, hy2, rfl⟩ := (hL z).1 hz
    exact hx' y hy1 hy2

/-! ### The main induction -/

/-- The chain argument: if replica `i` may apply `u` (Step 4), then every update `a` on a
register of `X_i`, issued by another replica, that reaches `u` by a causal chain
`v 0 ↪ ⋯ ↪ v m = u` (with `a` the first update of the chain or an earlier update of its issuer)
has already been applied at `i`. -/
theorem chain_main (h : Inv X s) {i : ι} {u : ℕ} (hu : Enabled X s i u) (m : ℕ) :
    ∀ a v, a < u → (s.log a).src ≠ i → (s.log a).reg ∈ X i → v m = u → IsChainF s v m →
      Start s a (v 0) → a ∈ s.app i := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a v hau hai hax hvm hv hst
  obtain ⟨hun, hki, hux, hunapp, hready⟩ := hu
  have hvn : v m < s.n := hvm ▸ hun
  have hlt : ∀ {q}, q ≤ m → v q < s.n := fun hq => IsChainF.lt_n h hv hvn hq
  have han : a < s.n := hau.trans hun
  -- the issuer of `v 0` is the issuer of `a`
  have hsrc0 : (s.log (v 0)).src = (s.log a).src := by
    rcases hst with rfl | ⟨h', _⟩
    · rfl
    · exact h'
  -- `a` is on an edge `e_ji` with `j ≠ i`
  have hadj_a : Adj X (s.log a).src i := adj_of_mem hai (h.reg_src han) hax
  -- Case `m = 0`: `a` is an earlier update of `u`'s issuer `k` on `e_ki`
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases hst with rfl | ⟨hsrc, hpre⟩
    · omega
    · rw [hvm] at hsrc hpre
      rw [h.count i _ hai hadj_a a han rfl hax]
      have h1 := h.ts_own u hun i (hsrc ▸ hadj_a) hux
      rw [hsrc] at h1
      have h2 := cnt_lt_of_lt s (X := X) hau ⟨hsrc, hux⟩
      have h3 := hready.1
      rw [hsrc] at h3
      omega
  -- Case: a replica occurs twice on the chain
  by_cases hrep : ∃ x y, x < y ∧ y ≤ m ∧ (s.log (v x)).src = (s.log (v y)).src
  · obtain ⟨x, y, hxy, hym, hp⟩ := hrep
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · -- restart the chain at `v y`, an update of `a`'s issuer
      refine ih (m - y) (by omega) a (fun q => v (q + y)) hau hai hax
        (by simp [show m - y + y = m by omega, hvm]) (IsChainF.drop hv y) ?_
      right
      refine ⟨by simp [← hp, hsrc0], ?_⟩
      simp only [Nat.zero_add]
      rcases hst with rfl | ⟨_, hpre⟩
      · exact h.pre_own _ (hlt hym) _ (IsChainF.hb hv hxy hym |> h.hb_lt) hp
      · exact h.pre_mono _ (hlt hym) _ (IsChainF.hb hv hxy hym |> h.hb_lt) hp hpre
    · -- splice `v (x-1) ↪ v y`
      have hlink : v (x - 1) ∈ (s.log (v y)).pre := by
        have h1 := (hv (x - 1) (by omega))
        rw [show x - 1 + 1 = x by omega] at h1
        exact h.pre_mono _ (hlt hym) _ (IsChainF.hb hv hxy hym |> h.hb_lt) hp h1.2
      refine ih (m - (y - (x - 1) - 1)) (by omega) a _ hau hai hax ?_
        (IsChainF.splice h hv hvn (show x - 1 < y by omega) hym hlink) (by simpa using hst)
      simp only [show ¬ m - (y - (x - 1) - 1) ≤ x - 1 by omega, ite_false,
        show m - (y - (x - 1) - 1) + (y - (x - 1) - 1) = m by omega, hvm]
  push Not at hrep
  have hinj : ∀ x ≤ m, ∀ y ≤ m, (s.log (v x)).src = (s.log (v y)).src → x = y := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with hlt' | heq | hgt
    · exact absurd hxy (hrep x y hlt' hy)
    · exact heq
    · exact absurd hxy.symm (hrep y x hgt hx)
  -- Case: an intermediate update of the chain writes a register of `X_i`
  by_cases hmid : ∃ q, 1 ≤ q ∧ q < m ∧ (s.log (v q)).reg ∈ X i
  · obtain ⟨q, hq1, hqm, hqx⟩ := hmid
    have hvq : v q ∈ s.app i := by
      by_cases hqi : (s.log (v q)).src = i
      · rw [← hqi]; exact h.own _ (hlt hqm.le)
      · exact ih (m - q) (by omega) (v q) (fun t => v (t + q))
          (by rw [← hvm]; exact h.hb_lt (IsChainF.hb hv hqm le_rfl)) hqi hqx
          (by simp [show m - q + q = m by omega, hvm]) (IsChainF.drop hv q) (Or.inl (by simp))
    exact h.safe i (v q) hvq a hax (Start.hb h hv hvn hst (by omega) hqm.le)
  push Not at hmid
  -- The remaining case: a simple chain avoiding `i`
  set j := (s.log a).src with hj
  have hpi : ∀ x ≤ m, (s.log (v x)).src ≠ i := by
    intro x hx hxi
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · exact hai (hsrc0 ▸ hxi)
    rcases Nat.lt_or_ge x m with hxm | hxm
    · exact hmid x hx0 hxm (hxi ▸ h.reg_src (hlt hx))
    · obtain rfl : x = m := by omega
      rw [hvm] at hxi; exact hki hxi
  by_cases htrack : ∀ q, 1 ≤ q → q ≤ m → TsEdge X (s.log (v q)).src j i
  · -- the counter `τ[e_ji]` carries `a` along the chain
    have hcarry : ∀ q ≤ m, cnt X s j i (a + 1) ≤ (s.log (v q)).ts j i := by
      intro q hq
      induction q with
      | zero =>
        rcases hst with rfl | ⟨hsrc, hpre⟩
        · exact (h.ts_own _ han i hadj_a hax).ge
        · rw [← h.ts_own _ han i hadj_a hax]
          exact h.ts_pre _ (hlt (Nat.zero_le _)) _ hpre j i
            (by rw [hsrc]; exact tsEdge_self_iff.2 hadj_a) (tsEdge_self_iff.2 hadj_a)
      | succ q ihq =>
        refine (ihq (by omega)).trans ?_
        have hl := hv q (by omega)
        refine h.ts_pre _ hl.1 _ hl.2 j i (htrack _ (by omega) hq) ?_
        rcases Nat.eq_zero_or_pos q with rfl | hq0
        · rw [hsrc0]; exact tsEdge_self_iff.2 hadj_a
        · exact htrack q hq0 (by omega)
    have hjk : j ≠ (s.log u).src := by
      intro hjk; rw [← hvm] at hjk
      exact absurd (hinj 0 (Nat.zero_le _) m le_rfl (hsrc0.trans hjk)) (by omega)
    have h1 := hready.2 j hai hjk (tsEdge_in_iff.2 hadj_a) (hvm ▸ htrack m hm le_rfl)
    rw [h.count i j hai hadj_a a han rfl hax]
    have h2 := hcarry m le_rfl
    rw [hvm] at h2
    omega
  push Not at htrack
  obtain ⟨q, hq1, hqm, hnot⟩ := htrack
  -- the chain forms a simple loop through `p q`, which is not a `(p q, e_ji)`-loop
  set p : ℕ → ι := fun t => (s.log (v t)).src with hp
  have hp0 : p 0 = j := hsrc0
  have hnotloop : ¬ IsLoop X (p q) (p 0) i ((List.range (m - q)).map fun t => p (q + 1 + t))
      ((List.range (q - 1)).map fun t => p (t + 1)) := by
    intro hl
    apply hnot
    rw [hp0] at hl
    exact ⟨hadj_a, Or.inr (Or.inr ⟨_, _, hl⟩)⟩
  -- adjacency along the chain
  have hadj : ∀ t < m, Adj X (p t) (p (t + 1)) := by
    intro t ht
    have hl := hv t ht
    exact adj_of_mem (fun h' => absurd (hinj t (by omega) (t + 1) (by omega) h') (by omega))
      (h.reg_src (hlt (by omega))) (h.pre_reg hl.1 hl.2)
  have hmi : Adj X (p m) i := by
    show Adj X (s.log (v m)).src i
    rw [hvm]; exact adj_of_mem hki (h.reg_src hun) hux
  have hij : Adj X i (p 0) := by rw [hp0]; exact adj_symm hadj_a
  -- useful: a link from a chain update or from `a` into `v y` (`q < y ≤ m`)
  have hjump : ∀ w y, q < y → y ≤ m → (s.log w).reg ∈ X (p y) →
      (∃ z, z < y - 1 ∧ (w = v z ∨ (z = 0 ∧ Start s w (v 0)))) → w ∈ (s.log (v y)).pre := by
    intro w y hqy hym hw ⟨z, hz, hwz⟩
    have hl := hv (y - 1) (by omega)
    rw [show y - 1 + 1 = y by omega] at hl
    refine h.pre_safe _ hl.1 _ hl.2 w hw ?_
    rcases hwz with rfl | ⟨rfl, hst'⟩
    · exact IsChainF.hb hv hz (by omega)
    · exact Start.hb h hv hvn hst' (by omega) (by omega)
  by_contra hna
  apply hnotloop
  refine isLoop_of_chain p i hq1 hqm hinj hpi hadj hmi hij ?_ ?_ ?_
  · -- condition (i): otherwise `a` itself is sent to some `p y`, `y > q`
    refine ⟨(s.log a).reg, ⟨hp0 ▸ h.reg_src han, hax⟩, fun y hqy hym hy => hna ?_⟩
    have hlink := hjump a y hqy hym hy ⟨0, by omega, Or.inr ⟨rfl, hst⟩⟩
    refine ih (m - y + 1) (by omega) a _ hau hai hax ?_ (IsChainF.restart h hv hvn hym hlink)
      (Or.inl (by simp))
    simp only [show ¬ m - y + 1 = 0 by omega, ite_false, show m - y + 1 - 1 + y = m by omega, hvm]
  · -- condition (ii): otherwise `v 0` is sent to some `p y`, `y > q`
    refine ⟨(s.log (v 0)).reg, ⟨h.reg_src (hlt (Nat.zero_le _)), ?_⟩, fun y hqy hym hy => hna ?_⟩
    · exact h.pre_reg (hv 0 hm).1 (hv 0 hm).2
    have hlink := hjump (v 0) y hqy hym hy ⟨0, by omega, Or.inl rfl⟩
    refine ih (m - (y - 0 - 1)) (by omega) a _ hau hai hax ?_
      (IsChainF.splice h hv hvn (show 0 < y by omega) hym hlink) (by simpa using hst)
    simp only [show ¬ m - (y - 0 - 1) ≤ 0 by omega, ite_false,
      show m - (y - 0 - 1) + (y - 0 - 1) = m by omega, hvm]
  · -- condition (iii): otherwise some `v b` (`1 ≤ b < q`) is sent to some `p y`, `y > q`
    intro b hb1 hbq
    have hl := hv b (by omega)
    refine ⟨(s.log (v b)).reg, ⟨h.reg_src (hlt (by omega)), h.pre_reg hl.1 hl.2⟩,
      hmid b hb1 (by omega), fun y hqy hym hy => hna ?_⟩
    have hlink := hjump (v b) y hqy hym hy ⟨b, by omega, Or.inl rfl⟩
    refine ih (m - (y - b - 1)) (by omega) a _ hau hai hax ?_
      (IsChainF.splice h hv hvn (show b < y by omega) hym hlink) (by simpa using hst)
    simp only [show ¬ m - (y - b - 1) ≤ b by omega, ite_false,
      show m - (y - b - 1) + (y - b - 1) = m by omega, hvm]

/-- **Core of Lemma 5.** If replica `i` may apply update `u` (Step 4), then every update `a ↪ u`
on a register of `X_i` has already been applied at `i`. -/
theorem deps_applied (h : Inv X s) {i : ι} {u : ℕ} (hu : Enabled X s i u) {a : ℕ}
    (hax : (s.log a).reg ∈ X i) (hau : HB s a u) : a ∈ s.app i := by
  by_cases hai : (s.log a).src = i
  · rw [← hai]; exact h.own a ((h.hb_lt hau).trans hu.1)
  obtain ⟨m, _, v, hv0, hvm, hv⟩ := exists_chain_of_hb hau
  exact chain_main h hu m a v (h.hb_lt hau) hai hax hvm hv (Or.inl hv0.symm)

end Podc.PartialReplicationCausal
