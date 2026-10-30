import Papers.PODC2019.HubLabelingHardness.Basic

/-!
# Lemma 2.2 of Kosowski–Uznański–Viennot (PODC 2019), for the weighted graph `H_{b,ℓ}`

For `x, z ∈ [0, s-1]^ℓ` with all `z_k - x_k` even, the walk of `H_{b,ℓ}` from `v_{0,x}` to `v_{2ℓ,z}`
of minimum weight is unique, has weight `Lopt x z = 2ℓA + 2 Σ_k ((z_k - x_k)/2)²`, and passes through
`v_{ℓ,(x+z)/2}`.

Proof (the paper's argument, made rigorous):
1. every edge has weight `≥ A`, and `Lopt < (2ℓ+1)A`, so a walk of weight `≤ Lopt` has at most `2ℓ`
   edges; since levels change by exactly one along an edge, it has exactly `2ℓ` edges and its `i`-th
   vertex is on level `i`;
2. for such a walk, coordinate `k` changes only at steps `k` and `2ℓ-1-k` (by `a_k` and `b_k`, with
   `a_k + b_k = z_k - x_k = 2m_k`), and its weight is `2ℓA + Σ_k (a_k² + b_k²)`;
3. `wlen - Lopt = Σ_k ((a_k - m_k)² + (b_k - m_k)²) ≥ 0`, with equality iff `a_k = b_k = m_k` for all
   `k`, which pins down every vertex of the walk (`canon`).
-/

namespace Podc.HubLabelingHardness

open SimpleGraph Finset

variable {b ℓ : ℕ}

/-! ## Walks as sequences of vertices -/

lemma wlen_eq_sum_getVert {u v : Main b ℓ} (p : (H b ℓ).Walk u v) :
    wlen p = ∑ i ∈ range p.length, hw b ℓ (p.getVert i) (p.getVert (i + 1)) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [wlen_cons, ih, Walk.length_cons, Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ, Walk.getVert_zero, zero_add]; rw [add_comm]

lemma bigA_le_hw (u v : Main b ℓ) : bigA b ℓ ≤ hw b ℓ u v := Nat.le_add_right _ _

lemma length_mul_le_wlen {u v : Main b ℓ} (p : (H b ℓ).Walk u v) :
    p.length * bigA b ℓ ≤ wlen p := by
  rw [wlen_eq_sum_getVert]
  calc p.length * bigA b ℓ = ∑ _i ∈ range p.length, bigA b ℓ := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => bigA_le_hw _ _

lemma sqd_lt (a c : Fin (side b)) : sqd a c < side b ^ 2 := by
  have ha := a.2; have hc := c.2
  have : ((sqd a c : ℕ) : ℤ) < ((side b ^ 2 : ℕ) : ℤ) := by
    rw [sqd_cast]; push_cast
    nlinarith
  exact_mod_cast this

lemma Lopt_lt (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) : Lopt x z < (2 * ℓ + 1) * bigA b ℓ := by
  have h1 : ∑ k, sqd (x k) (midpt x z k) ≤ ℓ * side b ^ 2 := by
    calc ∑ k, sqd (x k) (midpt x z k) ≤ ∑ _k : Fin ℓ, side b ^ 2 :=
          Finset.sum_le_sum fun k _ => (sqd_lt _ _).le
      _ = ℓ * side b ^ 2 := by simp
  have hs : 1 ≤ side b ^ 2 := Nat.one_le_pow _ _ (one_le_side b)
  unfold Lopt bigA
  nlinarith

/-- Adjacent vertices are on consecutive levels. -/
lemma level_adj {u v : Main b ℓ} (h : (H b ℓ).Adj u v) :
    v.1.val = u.1.val + 1 ∨ u.1.val = v.1.val + 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

lemma level_getVert_lip {u v : Main b ℓ} (p : (H b ℓ).Walk u v) (i : ℕ) :
    ∀ j, i ≤ j → j ≤ p.length →
      (p.getVert j).1.val ≤ (p.getVert i).1.val + (j - i) ∧
      (p.getVert i).1.val ≤ (p.getVert j).1.val + (j - i) := by
  intro j hij hj
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have := level_adj (p.adj_getVert_succ (show j < p.length by omega))
    have := ih (by omega)
    omega

/-- A walk from level `0` to level `2ℓ` is *monotone* if it has `2ℓ` edges (then its `i`-th vertex is
on level `i`). -/
def Mono {u v : Main b ℓ} (q : (H b ℓ).Walk u v) : Prop :=
  q.length = 2 * ℓ ∧ ∀ i ≤ 2 * ℓ, (q.getVert i).1.val = i

lemma mono_of_length_le {x z : Vec b ℓ} (q : (H b ℓ).Walk (bot x) (top z))
    (h : q.length ≤ 2 * ℓ) : Mono q := by
  have a0 : (q.getVert 0).1.val = 0 := by rw [Walk.getVert_zero]; rfl
  have a1 : (q.getVert q.length).1.val = 2 * ℓ := by rw [Walk.getVert_length]; rfl
  have h0 := level_getVert_lip q 0 q.length (Nat.zero_le _) le_rfl
  have hlen : q.length = 2 * ℓ := by omega
  refine ⟨hlen, fun i hi => ?_⟩
  have h1 := level_getVert_lip q 0 i (Nat.zero_le _) (by omega)
  have h2 := level_getVert_lip q i q.length (by omega) le_rfl
  omega

lemma Mono.step {u v : Main b ℓ} {q : (H b ℓ).Walk u v} (hq : Mono q) {i : ℕ} (hi : i < 2 * ℓ)
    (k : Fin ℓ) (hk : k.val ≠ cnat ℓ i) : (q.getVert (i + 1)).2 k = (q.getVert i).2 k := by
  have hadj := q.adj_getVert_succ (show i < q.length by rw [hq.1]; exact hi)
  have h1 := hq.2 i hi.le
  have h2 := hq.2 (i + 1) hi
  rcases hadj with ⟨_, h⟩ | ⟨h, _⟩
  · exact h k (by rw [h1]; exact hk)
  · omega

lemma cnat_eq_iff {i : ℕ} {k : ℕ} (hi : i < 2 * ℓ) (hk : k < ℓ) :
    cnat ℓ i = k ↔ i = k ∨ i = 2 * ℓ - 1 - k := by
  unfold cnat; split_ifs <;> omega

/-- Coordinate `k` of the `i`-th vertex of `q`, as an integer. -/
def J {u v : Main b ℓ} (q : (H b ℓ).Walk u v) (i : ℕ) (k : Fin ℓ) : ℤ := ((q.getVert i).2 k : ℕ)

/-- The change of coordinate `k` at step `k` (first half). -/
def da {u v : Main b ℓ} (q : (H b ℓ).Walk u v) (k : Fin ℓ) : ℤ := J q (k + 1) k - J q k k

/-- The change of coordinate `k` at step `2ℓ-1-k` (second half). -/
def db {u v : Main b ℓ} (q : (H b ℓ).Walk u v) (k : Fin ℓ) : ℤ :=
  J q (2 * ℓ - k) k - J q (2 * ℓ - 1 - k) k

lemma sum_two {g : ℕ → ℤ} (k : Fin ℓ)
    (hg : ∀ i < 2 * ℓ, i ≠ k.val → i ≠ 2 * ℓ - 1 - k → g i = 0) :
    ∑ i ∈ range (2 * ℓ), g i = g k + g (2 * ℓ - 1 - k) := by
  have hk := k.2
  apply Finset.sum_eq_add
  · omega
  · intro c hc hne
    exact hg c (Finset.mem_range.1 hc) hne.1 hne.2
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma Mono.J_succ {u v : Main b ℓ} {q : (H b ℓ).Walk u v} (hq : Mono q) (k : Fin ℓ) {i : ℕ}
    (hi : i < 2 * ℓ) (h1 : i ≠ k.val) (h2 : i ≠ 2 * ℓ - 1 - k) : J q (i + 1) k = J q i k := by
  unfold J
  rw [hq.step hi k (fun h => by rcases (cnat_eq_iff hi k.2).1 h.symm with h | h <;> contradiction)]

lemma Mono.da_add_db {x z : Vec b ℓ} {q : (H b ℓ).Walk (bot x) (top z)} (hq : Mono q) (k : Fin ℓ) :
    da q k + db q k = (z k : ℤ) - x k := by
  have hk := k.2
  have htel := Finset.sum_range_sub (fun i => J q i k) (2 * ℓ)
  rw [sum_two k (fun i hi h1 h2 => by simp only [hq.J_succ k hi h1 h2, sub_self])] at htel
  have e1 : 2 * ℓ - 1 - k.val + 1 = 2 * ℓ - k := by omega
  have hz : J q (2 * ℓ) k = z k := by
    have : q.getVert (2 * ℓ) = top z := by rw [← hq.1, Walk.getVert_length]
    unfold J; rw [this]; rfl
  have hx : J q 0 k = x k := by unfold J; rw [Walk.getVert_zero]; rfl
  simp only [e1] at htel
  unfold da db
  rw [← hz, ← hx, ← htel]

/-- The weight of a monotone walk: `2ℓA + Σ_k (a_k² + b_k²)`. -/
lemma Mono.wlen_eq {u v : Main b ℓ} {q : (H b ℓ).Walk u v} (hq : Mono q) :
    (wlen q : ℤ) = 2 * ℓ * bigA b ℓ + ∑ k, (da q k ^ 2 + db q k ^ 2) := by
  rw [wlen_eq_sum_getVert, hq.1]
  push_cast
  simp only [hw, Nat.cast_add, Nat.cast_sum, sqd_cast, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  push_cast
  rw [Finset.sum_comm]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := k.2
  rw [sum_two k (fun i hi h1 h2 => by
    show ((((q.getVert i).2 k : ℕ) : ℤ) - (((q.getVert (i + 1)).2 k : ℕ) : ℤ)) ^ 2 = 0
    have := hq.J_succ k hi h1 h2; unfold J at this; rw [this, sub_self]; ring)]
  have e1 : 2 * ℓ - 1 - k.val + 1 = 2 * ℓ - k := by omega
  unfold da db J
  rw [e1]; ring

/-! ## The lower bound and the equality case -/

/-- Half of the difference: `m_k = (z_k - x_k)/2`. -/
def mh (x z : Vec b ℓ) (k : Fin ℓ) : ℤ := ((midpt x z k : ℕ) : ℤ) - (x k : ℕ)

lemma two_midpt {x z : Vec b ℓ} (hxz : EvenDiff x z) (k : Fin ℓ) :
    2 * (midpt x z k : ℕ) = (x k : ℕ) + z k := by
  obtain ⟨r, hr⟩ := hxz k
  show 2 * (((x k : ℕ) + z k) / 2) = _
  omega

lemma Lopt_cast (x z : Vec b ℓ) :
    (Lopt x z : ℤ) = 2 * ℓ * bigA b ℓ + 2 * ∑ k, mh x z k ^ 2 := by
  unfold Lopt mh
  push_cast [sqd_cast]
  congr 2
  refine Finset.sum_congr rfl fun k _ => by ring

/-- `wlen q - Lopt = Σ_k ((a_k - m_k)² + (b_k - m_k)²)` for monotone walks. -/
lemma Mono.wlen_sub_Lopt {x z : Vec b ℓ} (hxz : EvenDiff x z) {q : (H b ℓ).Walk (bot x) (top z)}
    (hq : Mono q) :
    (wlen q : ℤ) - Lopt x z = ∑ k, ((da q k - mh x z k) ^ 2 + (db q k - mh x z k) ^ 2) := by
  rw [hq.wlen_eq, Lopt_cast, Finset.mul_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := hq.da_add_db k
  have h2 : (2 : ℤ) * mh x z k = (z k : ℕ) - (x k : ℕ) := by
    have := two_midpt hxz k; unfold mh; omega
  have h3 : db q k = 2 * mh x z k - da q k := by linarith
  rw [h3]; ring

/-! ## The canonical walk -/

/-- The vector of the `i`-th vertex `m_i` of the canonical walk: coordinate `k` is `z_k` once both of
its changes are done (`2ℓ - i ≤ k`), `(x_k + z_k)/2` after its first change (`k < i`), and `x_k`
before. -/
def canonVec (x z : Vec b ℓ) (i : ℕ) : Vec b ℓ := fun k =>
  if 2 * ℓ ≤ k.val + i then z k else if k.val < i then midpt x z k else x k

/-- The `i`-th vertex of the canonical walk (level `i`, for `i ≤ 2ℓ`). -/
def canon (x z : Vec b ℓ) (i : ℕ) : Main b ℓ := (⟨min i (2 * ℓ), by omega⟩, canonVec x z i)

lemma canon_zero (x z : Vec b ℓ) : canon x z 0 = bot x := by
  refine Prod.ext (Fin.ext (by simp [canon, bot])) (funext fun k => ?_)
  have := k.2
  simp only [canon, canonVec, bot]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma canon_two_mul (x z : Vec b ℓ) : canon x z (2 * ℓ) = top z := by
  refine Prod.ext (Fin.ext (by simp [canon, top])) (funext fun k => ?_)
  simp only [canon, canonVec, top]
  rw [ite_eq_left (by omega)]

lemma canon_ell (x z : Vec b ℓ) : canon x z ℓ = midl (midpt x z) := by
  refine Prod.ext (Fin.ext (by simp [canon, midl]; omega)) (funext fun k => ?_)
  have := k.2
  simp only [canon, canonVec, midl]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

lemma canonVec_succ_of_ne (x z : Vec b ℓ) {i : ℕ} (hi : i < 2 * ℓ) (k : Fin ℓ)
    (hk : k.val ≠ cnat ℓ i) : canonVec x z (i + 1) k = canonVec x z i k := by
  have hk' : ¬ (i = k.val ∨ i = 2 * ℓ - 1 - k.val) := fun h => hk ((cnat_eq_iff hi k.2).2 h).symm
  have := k.2
  simp only [canonVec]
  by_cases h1 : 2 * ℓ ≤ k.val + i
  · rw [ite_eq_left (by omega), ite_eq_left h1]
  · rw [ite_eq_right (by omega), ite_eq_right h1]
    by_cases h2 : k.val < i
    · rw [ite_eq_left (by omega), ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2]

lemma canonVec_succ_cnat {x z : Vec b ℓ} (hxz : EvenDiff x z) {i : ℕ} (hi : i < 2 * ℓ) (k : Fin ℓ)
    (hk : k.val = cnat ℓ i) :
    ((canonVec x z (i + 1) k : ℕ) : ℤ) = (canonVec x z i k : ℕ) + mh x z k := by
  have hk' := (cnat_eq_iff hi k.2).1 hk.symm
  have := k.2
  have hm := two_midpt hxz k
  simp only [canonVec, mh]
  rcases hk' with h | h
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    omega

/-- A walk of weight `≤ Lopt` visits exactly the canonical vertices. -/
lemma getVert_eq_canon {x z : Vec b ℓ} (hxz : EvenDiff x z) {q : (H b ℓ).Walk (bot x) (top z)}
    (hq : Mono q) (hab : ∀ k, da q k = mh x z k ∧ db q k = mh x z k) :
    ∀ i ≤ 2 * ℓ, q.getVert i = canon x z i := by
  intro i hi
  induction i with
  | zero => rw [Walk.getVert_zero, canon_zero]
  | succ i ih =>
    have ih := ih (by omega)
    refine Prod.ext (Fin.ext ?_) (funext fun k => ?_)
    · rw [hq.2 (i + 1) hi]; simp [canon]; omega
    · by_cases hk : k.val = cnat ℓ i
      · apply Fin.ext
        have e := canonVec_succ_cnat hxz (by omega) k hk
        have hk' := (cnat_eq_iff (show i < 2 * ℓ by omega) k.2).1 hk.symm
        have hJ : J q (i + 1) k = J q i k + mh x z k := by
          rcases hk' with h | h
          · have := (hab k).1; unfold da at this; subst h; linarith
          · have := (hab k).2; unfold db at this
            have e1 : 2 * ℓ - k.val = i + 1 := by omega
            rw [e1, ← h] at this; linarith
        unfold J at hJ
        rw [ih] at hJ
        show ((q.getVert (i + 1)).2 k : ℕ) = (canonVec x z (i + 1) k : ℕ)
        have : (((q.getVert (i + 1)).2 k : ℕ) : ℤ) = (canonVec x z (i + 1) k : ℕ) := by
          rw [hJ, e]; rfl
        exact_mod_cast this
      · rw [hq.step (by omega) k hk, ih]
        exact (canonVec_succ_of_ne x z (by omega) k hk).symm

lemma canon_adj (x z : Vec b ℓ) {i : ℕ} (hi : i < 2 * ℓ) :
    (H b ℓ).Adj (canon x z i) (canon x z (i + 1)) := by
  left
  refine ⟨by simp [canon]; omega, fun k hk => ?_⟩
  have : min i (2 * ℓ) = i := by omega
  simp only [canon, this] at hk
  exact canonVec_succ_of_ne x z hi k hk

lemma exists_canon_walk (x z : Vec b ℓ) : ∀ n ≤ 2 * ℓ,
    ∃ p : (H b ℓ).Walk (canon x z (2 * ℓ - n)) (canon x z (2 * ℓ)),
      p.length = n ∧ ∀ i ≤ n, p.getVert i = canon x z (2 * ℓ - n + i) := by
  intro n hn
  induction n with
  | zero => exact ⟨Walk.nil, rfl, fun i hi => by simp [show i = 0 by omega]⟩
  | succ n ih =>
    obtain ⟨p, hp, hpv⟩ := ih (by omega)
    have hadj := canon_adj x z (i := 2 * ℓ - (n + 1)) (by omega)
    rw [show 2 * ℓ - (n + 1) + 1 = 2 * ℓ - n by omega] at hadj
    refine ⟨Walk.cons hadj p, by simp [hp], fun i hi => ?_⟩
    rcases i with _ | i
    · simp
    · rw [Walk.getVert_cons_succ, hpv i (by omega)]
      congr 1; omega

/-- The canonical walk from `v_{0,x}` to `v_{2ℓ,z}`, through the vertices `canon x z i`. -/
lemma exists_canon_walk' (x z : Vec b ℓ) :
    ∃ p : (H b ℓ).Walk (bot x) (top z), p.length = 2 * ℓ ∧ ∀ i ≤ 2 * ℓ, p.getVert i = canon x z i := by
  obtain ⟨p, hp, hpv⟩ := exists_canon_walk x z (2 * ℓ) le_rfl
  have e0 : canon x z (2 * ℓ - 2 * ℓ) = bot x := by rw [Nat.sub_self, canon_zero]
  refine ⟨p.copy e0 (canon_two_mul x z), by simp [hp], fun i hi => ?_⟩
  rw [Walk.getVert_copy, hpv i hi, Nat.sub_self, zero_add]

lemma mono_of_getVert_eq_canon {x z : Vec b ℓ} {q : (H b ℓ).Walk (bot x) (top z)}
    (hl : q.length = 2 * ℓ) (hq : ∀ i ≤ 2 * ℓ, q.getVert i = canon x z i) : Mono q :=
  ⟨hl, fun i hi => by rw [hq i hi]; simp [canon]; omega⟩

lemma da_db_of_getVert_eq_canon {x z : Vec b ℓ} (hxz : EvenDiff x z)
    {q : (H b ℓ).Walk (bot x) (top z)} (hq : ∀ i ≤ 2 * ℓ, q.getVert i = canon x z i) (k : Fin ℓ) :
    da q k = mh x z k ∧ db q k = mh x z k := by
  have hk := k.2
  constructor
  · unfold da J
    rw [hq _ (by omega), hq _ (by omega)]
    simp only [canon]
    rw [canonVec_succ_cnat hxz (i := k) (by omega) k (by unfold cnat; rw [ite_eq_left hk])]
    ring
  · unfold db J
    rw [hq _ (by omega), hq _ (by omega)]
    have e : 2 * ℓ - k.val = 2 * ℓ - 1 - k + 1 := by omega
    rw [e]
    simp only [canon]
    rw [canonVec_succ_cnat hxz (i := 2 * ℓ - 1 - k) (by omega) k
      (by unfold cnat; rw [ite_eq_right (by omega)]; omega)]
    ring

/-- A walk is a path if its `i`-th vertex is on level `level u + i`. -/
lemma isPath_of_level {u v : Main b ℓ} (p : (H b ℓ).Walk u v)
    (h : ∀ i ≤ p.length, (p.getVert i).1.val = u.1.val + i) : p.IsPath := by
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons u' v' w' hadj q ih =>
    have hv : v'.1.val = u'.1.val + 1 := by
      have := h 1 (by simp); simpa using this
    rw [Walk.cons_isPath_iff]
    refine ⟨ih fun i hi => ?_, fun hu => ?_⟩
    · have := h (i + 1) (by simp; omega)
      rw [Walk.getVert_cons_succ] at this; omega
    · obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hu
      have := h (n + 1) (by simp; omega)
      rw [Walk.getVert_cons_succ, hn] at this; omega

/-! ## Lemma 2.2 for `H_{b,ℓ}` -/

/-- Existence of the canonical (point-symmetric) walk of weight `Lopt x z`. -/
theorem exists_walk_wlen_eq_Lopt (x z : Vec b ℓ) (hxz : EvenDiff x z) :
    ∃ p : (H b ℓ).Walk (bot x) (top z), wlen p = Lopt x z := by
  obtain ⟨p, hl, hp⟩ := exists_canon_walk' x z
  refine ⟨p, ?_⟩
  have := (mono_of_getVert_eq_canon hl hp).wlen_sub_Lopt hxz
  simp only [da_db_of_getVert_eq_canon hxz hp, sub_self] at this
  simp at this
  omega

/-- Every walk from `v_{0,x}` to `v_{2ℓ,z}` has weight at least `Lopt x z`. -/
theorem Lopt_le_wlen (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z)
    (q : (H b ℓ).Walk (bot x) (top z)) : Lopt x z ≤ wlen q := by
  by_cases hl : q.length ≤ 2 * ℓ
  · have := (mono_of_length_le q hl).wlen_sub_Lopt hxz
    have h0 : (0 : ℤ) ≤ ∑ k, ((da q k - mh x z k) ^ 2 + (db q k - mh x z k) ^ 2) :=
      Finset.sum_nonneg fun k _ => by positivity
    omega
  · have h1 := length_mul_le_wlen q
    have h2 := Lopt_lt hℓ x z
    have h3 : (2 * ℓ + 1) * bigA b ℓ ≤ q.length * bigA b ℓ := Nat.mul_le_mul_right _ (by omega)
    omega

/-- A walk of weight `≤ Lopt x z` visits exactly the canonical vertices. -/
theorem getVert_eq_canon_of_wlen_le (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z)
    (q : (H b ℓ).Walk (bot x) (top z)) (h : wlen q ≤ Lopt x z) :
    q.length = 2 * ℓ ∧ ∀ i ≤ 2 * ℓ, q.getVert i = canon x z i := by
  have hl : q.length ≤ 2 * ℓ := by
    by_contra hl
    have h1 := length_mul_le_wlen q
    have h2 := Lopt_lt hℓ x z
    have h3 : (2 * ℓ + 1) * bigA b ℓ ≤ q.length * bigA b ℓ := Nat.mul_le_mul_right _ (by omega)
    omega
  have hq := mono_of_length_le q hl
  refine ⟨hq.1, getVert_eq_canon hxz hq fun k => ?_⟩
  have e := hq.wlen_sub_Lopt hxz
  have h0 : ∑ k, ((da q k - mh x z k) ^ 2 + (db q k - mh x z k) ^ 2) = 0 := by
    have : (0 : ℤ) ≤ ∑ k, ((da q k - mh x z k) ^ 2 + (db q k - mh x z k) ^ 2) :=
      Finset.sum_nonneg fun k _ => by positivity
    omega
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)] at h0
  have := h0 k (Finset.mem_univ _)
  constructor <;> nlinarith [sq_nonneg (da q k - mh x z k), sq_nonneg (db q k - mh x z k)]

/-- Every walk of weight `≤ Lopt x z` passes through `v_{ℓ,(x+z)/2}`. -/
theorem midl_mem_support_of_wlen_le (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z)
    (q : (H b ℓ).Walk (bot x) (top z)) (h : wlen q ≤ Lopt x z) : midl (midpt x z) ∈ q.support := by
  obtain ⟨_, hq⟩ := getVert_eq_canon_of_wlen_le hℓ x z hxz q h
  rw [← canon_ell, ← hq ℓ (by omega)]
  exact Walk.getVert_mem_support _ _

/-- Lemma 2.2 of [KUV19], `H_{b,ℓ}` part: the shortest `v_{0,x}`–`v_{2ℓ,z}` walk is unique. -/
theorem lemma_2_2_H (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z) :
    ∃! p : (H b ℓ).Walk (bot x) (top z), ∀ q : (H b ℓ).Walk (bot x) (top z), wlen p ≤ wlen q := by
  obtain ⟨p, hp⟩ := exists_walk_wlen_eq_Lopt x z hxz
  refine ⟨p, fun q => hp ▸ Lopt_le_wlen hℓ x z hxz q, fun q hq => ?_⟩
  have hqle : wlen q ≤ Lopt x z := hp ▸ hq p
  obtain ⟨hl1, h1⟩ := getVert_eq_canon_of_wlen_le hℓ x z hxz q hqle
  obtain ⟨hl2, h2⟩ := getVert_eq_canon_of_wlen_le hℓ x z hxz p hp.le
  refine Walk.ext_getVert_le_length (hl1.trans hl2.symm) fun i hi => ?_
  rw [h1 i (by omega), h2 i (by omega)]

/-- The weighted distance from `v_{0,x}` to `v_{2ℓ,z}` in `H_{b,ℓ}` is `Lopt x z`. -/
theorem wdist_eq_Lopt (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z) :
    (H b ℓ).wdist (fun e => (hwS b ℓ e : NNReal)) (bot x) (top z) = Lopt x z := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := exists_walk_wlen_eq_Lopt x z hxz
    calc _ ≤ p.wlength (fun e => (hwS b ℓ e : NNReal)) := wdist_le p
      _ = Lopt x z := by rw [← wlen_eq_wlength, hp]
  · refine le_iInf fun q => ?_
    rw [← wlen_eq_wlength]
    exact_mod_cast Lopt_le_wlen hℓ x z hxz q

/-- **Lemma 2.2 of [KUV19], for `H_{b,ℓ}`.** If `z_k - x_k` is even for all `k`, there is a unique
walk `p` of minimum weight from `v_{0,x}` to `v_{2ℓ,z}`; it is a path, it passes through
`v_{ℓ,(x+z)/2}`, and its weight is `Lopt x z = 2ℓA + 2 Σ_k ((z_k - x_k)/2)²`. -/
theorem lemma_2_2 (hℓ : 1 ≤ ℓ) (x z : Vec b ℓ) (hxz : EvenDiff x z) :
    ∃! p : (H b ℓ).Walk (bot x) (top z),
      (∀ q : (H b ℓ).Walk (bot x) (top z), wlen p ≤ wlen q) ∧
      p.IsPath ∧ midl (midpt x z) ∈ p.support ∧ wlen p = Lopt x z := by
  obtain ⟨p, hp, huniq⟩ := lemma_2_2_H hℓ x z hxz
  have hpL : wlen p = Lopt x z := by
    obtain ⟨p', hp'⟩ := exists_walk_wlen_eq_Lopt x z hxz
    exact le_antisymm (hp' ▸ hp p') (Lopt_le_wlen hℓ x z hxz p)
  obtain ⟨hl, hv⟩ := getVert_eq_canon_of_wlen_le hℓ x z hxz p hpL.le
  refine ⟨p, ⟨hp, isPath_of_level p fun i hi => ?_,
    midl_mem_support_of_wlen_le hℓ x z hxz p hpL.le, hpL⟩, fun q hq => huniq q hq.1⟩
  rw [hv i (by omega)]; simp [canon, bot]; omega

end Podc.HubLabelingHardness
