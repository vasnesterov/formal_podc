import Papers.PODC2013.EarlyDecidingExpensive.Critical

/-!
# The Byzantine message lower bound (Dolev–Lenzen, PODC 2013, Lemmas 3.7, 3.8, Theorem 3.2)

Throughout, `A` is a binary consensus algorithm tolerating `t` Byzantine faults (`n > 3t`) that
is `(f+2)`-deciding (Definition 3.1 with `d(f) = f + 2`).

* `lemma_3_7`: in round `r + 1` of an `r`-critical pair (`1 ≤ r ≤ t/2`), the non-faulty nodes
  other than the critical node send at least `n t / 11` messages in the two executions together.
  (The paper states `nt/22` messages "by non-faulty nodes" in one of them, which may include the
  critical node; Lemma 3.8 needs the version without it, which the paper's proof gives.)
* `lemma_3_8`: an `(r+1)`-critical pair whose non-faulty nodes other than the new critical node
  send at least `t² / 44` messages in round `r + 1` of both executions.
* `theorem_3_2`: some execution with exactly `f` faults (`1 ≤ f ≤ t/2`) in which the non-faulty
  nodes send at least `t² f / 44` messages.
-/

namespace Podc.EarlyDecidingExpensive

open Finset

variable {V M : Type*} [DecidableEq V] {A : Algorithm V M}

lemma msg_addFaults_of_faultyAt {E : Execution V M} {S : Finset V} {k₀ : ℕ}
    {γ : ℕ → V → V → Option M} {k : ℕ} {p : V} (hp : p ∉ S) (hf : E.FaultyAt k p) (q : V) :
    msg A (addFaults E S k₀ γ) k p q = msg A E k p q := by
  by_cases hpq : p = q
  · subst hpq; simp [msg_self]
  rw [msg_of_faultyAt ((faultyAt_addFaults_of_not_mem hp).2 hf) hpq, msg_of_faultyAt hf hpq]
  simp [addFaults, hp]

section Pivot

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

lemma pivot_faultyAt {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    {W : Finset V} {p : V} (hp : p ∈ (pivot A E₀ E₁ v r W).F) {k : ℕ} (hk : r ≤ k) :
    (pivot A E₀ E₁ v r W).FaultyAt k p := by
  refine ⟨hp, ?_⟩
  rw [pivot_fr]
  split_ifs with hpv
  · exact hk
  · simp only [pivot, addFaults_F, mem_union, mem_singleton, hpv, or_false] at hp
    have := h.fr_lt p hp; omega

lemma pivot_hist_r_congr {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (hr : 1 ≤ r) {W W' : Finset V} {q : V} (hqv : q ≠ v) (hW : q ∈ W ↔ q ∈ W') :
    hist A (pivot A E₀ E₁ v r W) r q = hist A (pivot A E₀ E₁ v r W') r q := by
  by_cases hq : q ∈ W
  · rw [pivot_hist_r_mem h W hqv hq hr, pivot_hist_r_mem h W' hqv (hW.1 hq) hr]
  · rw [pivot_hist_r_not_mem h W hqv hq hr, pivot_hist_r_not_mem h W' hqv (hW.not.1 hq) hr]

lemma pivot_msg_succ_congr {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (hr : 1 ≤ r) {W W' : Finset V} {p q : V} (hqv : q ≠ v) (hqW : q ∈ W ↔ q ∈ W')
    (hpW : p ∈ W ↔ p ∈ W') :
    msg A (pivot A E₀ E₁ v r W) (r + 1) p q = msg A (pivot A E₀ E₁ v r W') (r + 1) p q := by
  by_cases hpv : p = v
  · subst hpv
    rw [pivot_msg_v h W (by omega) hqv, pivot_msg_v h W' (by omega) hqv]
    simp [hqW]
  by_cases hpF : p ∈ E₀.F
  · rw [pivot_msg_F h W (by omega) hpF, pivot_msg_F h W' (by omega) hpF]
  by_cases hp : p ∈ W
  · rw [pivot_msg_succ_mem h W hpF hpv hp hr, pivot_msg_succ_mem h W' hpF hpv (hpW.1 hp) hr]
  · rw [pivot_msg_succ_not_mem h W hpF hpv hp hr,
      pivot_msg_succ_not_mem h W' hpF hpv (hpW.not.1 hp) hr]

end Pivot

/-! ### Lemma 3.7 -/

variable [Fintype V]

lemma card_filter_product_le (S : Finset V) (P : V → V → Prop) [DecidableRel P] :
    ((S ×ˢ S).filter fun pq => P pq.1 pq.2).card ≤
      ∑ p ∈ S, (univ.filter fun q => P p q).card := by
  calc ((S ×ˢ S).filter fun pq => P pq.1 pq.2).card
      ≤ (S.biUnion fun p => (univ.filter fun q => P p q).image fun q => (p, q)).card := by
        apply card_le_card
        intro pq hpq
        simp only [mem_filter, mem_product] at hpq
        simp only [mem_biUnion, mem_image, mem_filter, mem_univ, true_and]
        exact ⟨pq.1, hpq.1.1, pq.2, hpq.2, rfl⟩
    _ ≤ ∑ p ∈ S, ((univ.filter fun q => P p q).image fun q => (p, q)).card := card_biUnion_le
    _ ≤ ∑ p ∈ S, (univ.filter fun q => P p q).card := sum_le_sum fun _ _ => card_image_le

section Lemma37

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- **Lemma 3.7** (in the form used by Lemma 3.8). Let `A` be correct against `t` Byzantine
faults with `n > 3t`, deciding within `r + 1` rounds in executions with `r - 1` faults. In round
`r + 1` of an `r`-critical pair with `1 ≤ r ≤ t/2`, the nodes that are non-faulty in `E(W)` (all
non-faulty nodes except the critical node) send at least `n t / 11` messages in the two
executions together; so at least `n t / 22` in one of them. -/
theorem lemma_3_7 (hA : Correct A (byzAdm t)) (hnt : 3 * t < Fintype.card V) (hr : 1 ≤ r)
    (hrt : 2 * r ≤ t) (hd : DecidingAt A (byzAdm t) (r - 1) (r + 1))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v b) :
    Fintype.card V * t ≤
      11 * (roundCount A E₀ (r + 1) (honest E₀ v) + roundCount A E₁ (r + 1) (honest E₀ v)) := by
  set S₀ := honest E₀ v with hS₀
  set n := Fintype.card V
  by_contra hcon
  push Not at hcon
  let D : Finset (V × V) := (S₀ ×ˢ S₀).filter fun pq =>
    (msg A E₀ (r + 1) pq.1 pq.2).isSome ∨ (msg A E₁ (r + 1) pq.1 pq.2).isSome
  have hD : D.card ≤ roundCount A E₀ (r + 1) S₀ + roundCount A E₁ (r + 1) S₀ := by
    have h1 : D ⊆ ((S₀ ×ˢ S₀).filter fun pq => (msg A E₀ (r + 1) pq.1 pq.2).isSome) ∪
        ((S₀ ×ˢ S₀).filter fun pq => (msg A E₁ (r + 1) pq.1 pq.2).isSome) := by
      intro pq hpq
      simp only [D, mem_filter] at hpq
      rcases hpq.2 with h' | h'
      · exact mem_union_left _ (mem_filter.2 ⟨hpq.1, h'⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hpq.1, h'⟩)
    refine (card_le_card h1).trans ((card_union_le _ _).trans (add_le_add ?_ ?_))
    · exact card_filter_product_le S₀ fun p q => (msg A E₀ (r + 1) p q).isSome
    · exact card_filter_product_le S₀ fun p q => (msg A E₁ (r + 1) p q).isSome
  have hcard : S₀.card = n - r := card_honest h hr
  obtain ⟨x, hx, y, hy, hxy, hDxy, hDyx, hlight⟩ :=
    exists_light_pair S₀ D (n := n) (t := t) (by omega) hnt (by omega)
  have hx' := mem_honest.1 hx
  have hy' := mem_honest.1 hy
  -- the senders to `x` or `y` among the honest nodes
  let S : Finset V := (S₀.filter fun p => (p, x) ∈ D) ∪ (S₀.filter fun p => (p, y) ∈ D)
  have hSc : 2 * S.card ≤ t := (Nat.mul_le_mul_left 2 (card_union_le _ _)).trans hlight
  have hSS₀ : S ⊆ S₀ := union_subset (filter_subset _ _) (filter_subset _ _)
  have hnotS : ∀ p ∈ S₀, p ∉ S → (msg A E₀ (r + 1) p x = none ∧ msg A E₁ (r + 1) p x = none) ∧
      (msg A E₀ (r + 1) p y = none ∧ msg A E₁ (r + 1) p y = none) := by
    intro p hp hpS
    simp only [S, mem_union, mem_filter, not_or, not_and, D, mem_product] at hpS
    have h1 := hpS.1 hp ⟨hp, hx⟩
    have h2 := hpS.2 hp ⟨hp, hy⟩
    simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
      at h1 h2
    exact ⟨h1, h2⟩
  have hxS : x ∉ S := by
    intro hxS'
    simp only [S, mem_union, mem_filter] at hxS'
    rcases hxS' with ⟨_, h'⟩ | ⟨_, h'⟩
    · simp [D, msg_self] at h'
    · exact hDxy h'
  have hyS : y ∉ S := by
    intro hyS'
    simp only [S, mem_union, mem_filter] at hyS'
    rcases hyS' with ⟨_, h'⟩ | ⟨_, h'⟩
    · exact hDyx h'
    · simp [D, msg_self] at h'
  let P := pivot A E₀ E₁ v r {x}
  have hdisj : Disjoint P.F S := by
    rw [disjoint_right]
    intro p hp
    exact not_mem_pivot_F.2 (hSS₀ hp)
  let E' := addFaults P S (r + 1) fun k p q => if q = x then msg A E₀ k p q else msg A E₁ k p q
  have hE' : byzAdm t E' := by
    simp only [byzAdm, E', card_addFaults hdisj, P, card_pivot h]; omega
  have hxF : x ∉ E'.F := by simp [E', not_mem_pivot_F.2 hx, P, hxS]
  have hyF : y ∉ E'.F := by simp [E', not_mem_pivot_F.2 hy, P, hyS]
  have hxy' : y ∉ ({x} : Finset V) := by simpa using hxy.symm
  -- `x` sees `E₀`, `y` sees `E₁`
  have hhx : hist A E' (r + 1) x = hist A E₀ (r + 1) x := by
    rw [hist_succ, hist_succ, hist_addFaults_of_lt hdisj (by omega),
      pivot_hist_r_mem h {x} hx'.2 (mem_singleton_self x) hr]
    congr 2; funext p
    by_cases hpS : p ∈ S
    · rw [msg_addFaults_of_mem (q := x) le_rfl hpS (by rintro rfl; exact hxS hpS)]; simp
    rw [msg_addFaults_of_not_mem hdisj le_rfl hpS]
    by_cases hpv : p = v
    · subst hpv; rw [pivot_msg_v h _ (by omega) hx'.2]; simp
    by_cases hpF : p ∈ E₀.F
    · rw [pivot_msg_F h _ (by omega) hpF, h.silent₀ p hpF _ (by omega)]
    by_cases hpx : p = x
    · subst hpx; simp [msg_self]
    rw [pivot_msg_succ_not_mem h _ hpF hpv (by simpa using hpx) hr]
    have := hnotS p (mem_honest.2 ⟨hpF, hpv⟩) hpS
    rw [this.1.1, this.1.2]
  have hhy : hist A E' (r + 1) y = hist A E₁ (r + 1) y := by
    rw [hist_succ, hist_succ, hist_addFaults_of_lt hdisj (by omega),
      pivot_hist_r_not_mem h {x} hy'.2 hxy' hr]
    congr 2; funext p
    by_cases hpS : p ∈ S
    · rw [msg_addFaults_of_mem (q := y) le_rfl hpS (by rintro rfl; exact hyS hpS)]; simp [hxy.symm]
    rw [msg_addFaults_of_not_mem hdisj le_rfl hpS]
    by_cases hpv : p = v
    · subst hpv; rw [pivot_msg_v h _ (by omega) hy'.2]; simp [hxy.symm]
    by_cases hpF : p ∈ E₀.F
    · rw [pivot_msg_F h _ (by omega) hpF, h.silent₁ p hpF _ (by omega)]
    by_cases hpx : p = x
    · subst hpx
      rw [pivot_msg_succ_mem h _ hpF hpv (mem_singleton_self _) hr]
      have := hnotS p hx hpS
      rw [this.2.1, this.2.2]
    rw [pivot_msg_succ_not_mem h _ hpF hpv (by simpa using hpx) hr]
  have h0 : DecidedBy A E' x (r + 1) b :=
    decidedBy_of_hist hd h.adm₀ h.card h.out₀ hx'.1 rfl hhx.symm
  have h1 : DecidedBy A E' y (r + 1) (!b) :=
    decidedBy_of_hist hd h.adm₁ (h.F_eq ▸ h.card) h.out₁ (h.F_eq ▸ hy'.1) (h.input_eq y hy'.2)
      hhy.symm
  have := hA.agreement E' hE' x hxF y hyF _ _ h0.decides h1.decides
  cases b <;> simp at this

end Lemma37

/-! ### Lemma 3.8 -/

section Lemma38

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- In round `r + 1`, honest nodes outside `W` receive in `E(W)` from nodes outside `W` what
they receive in `E₁`. -/
lemma pivot_msg_succ_E₁ {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (hr : 1 ≤ r) {W : Finset V} {p q : V} (hqv : q ≠ v) (hqW : q ∉ W) (hpW : p ∉ W) :
    msg A (pivot A E₀ E₁ v r W) (r + 1) p q = msg A E₁ (r + 1) p q := by
  by_cases hpv : p = v
  · subst hpv; rw [pivot_msg_v h W (by omega) hqv]; simp [hqW]
  by_cases hpF : p ∈ E₀.F
  · rw [pivot_msg_F h W (by omega) hpF, h.silent₁ p hpF _ (by omega)]
  exact pivot_msg_succ_not_mem h W hpF hpv hpW hr q

/-- **Lemma 3.8, core.** Let `W₀` be a set of `⌈t/2⌉` (at least one, at most `(t+1)/2`) honest
nodes of an `r`-critical pair with `1 ≤ r ≤ t/2`. Then `E(W₀)` outputs the value of `E₁`. -/
theorem out_pivot_of_small (hA : Correct A (byzAdm t)) (hnt : 3 * t < Fintype.card V)
    (hr : 1 ≤ r) (hrt : 2 * r ≤ t) (hd : Deciding A (byzAdm t) (· + 2))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v b) {W₀ : Finset V} (hW₀ : W₀ ⊆ honest E₀ v)
    (hk : 2 * W₀.card ≤ t + 1) (hk1 : 1 ≤ W₀.card) :
    Out A (pivot A E₀ E₁ v r W₀) (!b) := by
  set n := Fintype.card V
  let P := pivot A E₀ E₁ v r W₀
  have hadmP : byzAdm t P := by simp only [P, byzAdm, card_pivot h]; omega
  have hcP : P.F.card = r := by simp only [P, card_pivot h]; omega
  by_contra hcon
  have hP : Out A P b := by simpa using hA.out_not hadmP hcon
  have hcard : (honest E₀ v \ W₀).card = n - r - W₀.card := by
    rw [card_sdiff_of_subset hW₀, card_honest h hr]
  obtain ⟨x, hx, u, hu, hxu⟩ := Finset.one_lt_card.1 (show 1 < (honest E₀ v \ W₀).card by
    rw [hcard]; omega)
  rw [mem_sdiff, mem_honest] at hx hu
  obtain ⟨⟨hxF, hxv⟩, hxW⟩ := hx
  obtain ⟨⟨huF, huv⟩, huW⟩ := hu
  have hxP : x ∉ P.F := not_mem_pivot_F.2 (mem_honest.2 ⟨hxF, hxv⟩)
  have huP : u ∉ P.F := not_mem_pivot_F.2 (mem_honest.2 ⟨huF, huv⟩)
  have hWP : ∀ p ∈ W₀, p ∉ P.F := fun p hp => not_mem_pivot_F.2 (hW₀ hp)
  have hdisj1 : Disjoint P.F W₀ := disjoint_right.2 fun p hp => hWP p hp
  have hdisj0 : Disjoint P.F {x} := by simpa using hxP
  -- `E₁'`: the nodes of `W₀` fail in round `r + 1`, showing `E(∅)` to `x`
  let E1 := addFaults P W₀ (r + 1) fun k p q =>
    if k = r + 1 ∧ q = x then msg A (pivot A E₀ E₁ v r ∅) (r + 1) p x else msg A P k p q
  -- `E₀'`: `x` fails in round `r + 2`, showing `E(W₀)` to `W₀` and `E₁'` to the others
  let E0 := addFaults P {x} (r + 2) fun k _ q =>
    if q ∈ W₀ then msg A P k x q else msg A E1 k x q
  have hadm1 : byzAdm t E1 := by simp only [E1, byzAdm, card_addFaults hdisj1, hcP]; omega
  have hadm0 : byzAdm t E0 := by simp only [E0, byzAdm, card_addFaults hdisj0, hcP]; simp; omega
  have nfP : ∀ p, p ∉ P.F → ∀ k, ¬ P.FaultyAt k p := fun p hpF k h' => hpF h'.1
  have nf0 : ∀ p, p ∉ P.F → p ≠ x → ∀ k, ¬ E0.FaultyAt k p := fun p hpF hpx k h' => by
    rw [faultyAt_addFaults_of_not_mem (by simpa using hpx)] at h'; exact hpF h'.1
  have nf1 : ∀ p, p ∉ P.F → p ∉ W₀ → ∀ k, ¬ E1.FaultyAt k p := fun p hpF hpW k h' => by
    rw [faultyAt_addFaults_of_not_mem hpW] at h'; exact hpF h'.1
  have hd1 : DecidingAt A (byzAdm t) (r - 1) (r + 1) := by
    have := hd (r - 1); simp only at this; rwa [show r - 1 + 2 = r + 1 by omega] at this
  have hx1 : x ∉ E1.F := by simp [E1, hxP, hxW]
  have hu1 : u ∉ E1.F := by simp [E1, huP, huW]
  have hu0 : u ∉ E0.F := by simp [E0, huP, Ne.symm hxu]
  -- (a) `x` cannot distinguish `E₁'` from `E₁` before round `r + 2`
  have ha : hist A E1 (r + 1) x = hist A E₁ (r + 1) x := by
    rw [hist_succ, hist_succ, hist_addFaults_of_lt hdisj1 (by omega),
      pivot_hist_r_not_mem h W₀ hxv hxW hr]
    congr 2; funext p
    by_cases hpW : p ∈ W₀
    · rw [msg_addFaults_of_mem (q := x) le_rfl hpW (by rintro rfl; exact hxW hpW)]
      simp only [and_self, if_true]
      exact pivot_msg_succ_E₁ h hr hxv (by simp) (by simp)
    · rw [msg_addFaults_of_not_mem hdisj1 le_rfl hpW]
      exact pivot_msg_succ_E₁ h hr hxv hxW hpW
  have hxdec : DecidedBy A E1 x (r + 1) (!b) :=
    decidedBy_of_hist (E' := E1) hd1 h.adm₁ (h.F_eq ▸ h.card) h.out₁ (h.F_eq ▸ hxF)
      (h.input_eq x hxv) ha.symm
  -- (b) the nodes of `W₀` cannot distinguish `E₀'` from `E(W₀)` before round `r + 3`
  have hb : ∀ w ∈ W₀, hist A E0 (r + 2) w = hist A P (r + 2) w := by
    intro w hw
    rw [hist_succ (A := A) E0 (r + 1) w, hist_succ (A := A) P (r + 1) w,
      hist_addFaults_of_lt hdisj0 (by omega)]
    congr 2; funext p
    by_cases hpx : p = x
    · subst hpx
      rw [msg_addFaults_of_mem (q := w) le_rfl (mem_singleton_self _)
        (by rintro rfl; exact hxW hw)]
      simp [hw]
    · exact msg_addFaults_of_not_mem hdisj0 le_rfl (by simpa using hpx) w
  obtain ⟨w₀, hw₀⟩ := card_pos.1 (show 0 < W₀.card by omega)
  have hw₀dec : Decides A E0 w₀ b :=
    (decidedBy_of_hist (E' := E0) (hd r) hadmP hcP hP (hWP w₀ hw₀) rfl (hb w₀ hw₀).symm).decides
  -- (c) nodes other than `x` cannot distinguish `E₁'` from `E(W₀)` before round `r + 2`
  have hc : ∀ q, q ≠ x → hist A E1 (r + 1) q = hist A P (r + 1) q := by
    intro q hqx
    rw [hist_succ (A := A) E1 r q, hist_succ (A := A) P r q,
      hist_addFaults_of_lt hdisj1 (by omega)]
    congr 2; funext p
    by_cases hpq : p = q
    · subst hpq; simp [msg_self]
    by_cases hpW : p ∈ W₀
    · rw [msg_addFaults_of_mem le_rfl hpW hpq]; simp [hqx]
    · exact msg_addFaults_of_not_mem hdisj1 le_rfl hpW q
  -- (d) in round `r + 2`, nodes outside `W₀ ∪ {x}` send in `E₁'` what they send in `E(W₀)`
  have hd' : ∀ p, p ∉ W₀ → p ≠ x → ∀ q, msg A E1 (r + 2) p q = msg A P (r + 2) p q := by
    intro p hpW hpx q
    by_cases hpF : p ∈ P.F
    · exact msg_addFaults_of_faultyAt hpW (pivot_faultyAt h hpF (by omega)) q
    · exact msg_congr (E := E1) (E' := P) (k := r + 2) (nf1 p hpF hpW _) (nfP p hpF _) rfl
        (hc p hpx) q
  -- (e) nodes of `U` cannot distinguish `E₀'` and `E₁'` before round `r + 3` …
  have he : ∀ q, q ∉ P.F → q ∉ W₀ → q ≠ x → hist A E0 (r + 2) q = hist A E1 (r + 2) q := by
    intro q hqP hqW hqx
    have h0 := hist_eq_iff.1 (hist_addFaults_of_lt (A := A) hdisj0
      (γ := fun k _ q => if q ∈ W₀ then msg A P k x q else msg A E1 k x q)
      (show r + 1 < r + 2 by omega) q)
    have h1 := hist_eq_iff.1 (hc q hqx)
    refine hist_eq_iff.2 fun k hk1 hk2 p => ?_
    rcases Nat.lt_or_ge k (r + 2) with hk | hk
    · rw [h0 k hk1 (by omega) p, h1 k hk1 (by omega) p]
    obtain rfl : k = r + 2 := by omega
    by_cases hpx : p = x
    · subst hpx
      rw [msg_addFaults_of_mem (q := q) le_rfl (mem_singleton_self _) (Ne.symm hqx)]
      simp [hqW]
    rw [msg_addFaults_of_not_mem hdisj0 le_rfl (by simpa using hpx)]
    by_cases hpW : p ∈ W₀
    · rw [msg_addFaults_of_mem (by omega) hpW (by rintro rfl; exact hqW hpW)]
      simp
    · exact (hd' p hpW hpx q).symm
  -- … nor before round `r + 4`
  have hf : hist A E0 (r + 3) u = hist A E1 (r + 3) u := by
    rw [hist_succ (A := A) E0 (r + 2) u, hist_succ (A := A) E1 (r + 2) u,
      he u huP huW (Ne.symm hxu)]
    congr 2; funext p
    by_cases hpx : p = x
    · subst hpx
      rw [msg_addFaults_of_mem (q := u) (by omega) (mem_singleton_self _) hxu]
      simp [huW]
    by_cases hpF : p ∈ P.F
    · have hfa := pivot_faultyAt h hpF (show r ≤ r + 3 by omega)
      rw [msg_addFaults_of_faultyAt (by simpa using hpx) hfa,
        msg_addFaults_of_faultyAt (fun hpW => hWP p hpW hpF) hfa]
    by_cases hpW : p ∈ W₀
    · rw [msg_addFaults_of_mem (by omega) hpW (by rintro rfl; exact huW hpW)]
      simp only [show ¬ (r + 3 = r + 1 ∧ u = x) by omega, if_false]
      exact msg_congr (E := E0) (E' := P) (k := r + 3) (nf0 p hpF hpx _) (nfP p hpF _) rfl
        (hb p hpW) u
    · exact msg_congr (E := E0) (E' := E1) (k := r + 3) (nf0 p hpF hpx _) (nf1 p hpF hpW _) rfl
        (he p hpF hpW hpx) u
  -- `u` decides `b` in `E₀'` within `r + 3` rounds, hence also in `E₁'`, where `x` decides `!b`
  obtain ⟨c, hcu⟩ := hd (r + 1) E0 hadm0
    (show E0.F.card = r + 1 by simp only [E0]; rw [card_addFaults hdisj0, hcP, card_singleton])
    u hu0
  replace hcu : DecidedBy A E0 u (r + 3) c := hcu
  have hw₀0 : w₀ ∉ E0.F := by simp [E0, hWP w₀ hw₀]; rintro rfl; exact hxW hw₀
  obtain rfl : c = b := hcu.decides.unique (hA.decides_of_decides hadm0 hw₀0 hu0 hw₀dec)
  have hu1dec := hcu.transfer (E' := E1) rfl hf
  have := hA.agreement E1 hadm1 u hu1 x hx1 _ _ hu1dec.decides hxdec.decides
  cases c <;> simp at this

end Lemma38

/-! ### Counting messages along the induction -/

section Count

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- The senders counted in round `k` of an `r`-critical execution with critical node `v`: the
nodes that are non-faulty in round `k`, without `v` in round `r` (it may fail in round `r` of the
next pair). -/
def sendersAt (E : Execution V M) (r k : ℕ) (v : V) : Finset V :=
  if k = r then (nonfaulty E k).erase v else nonfaulty E k

/-- The induction invariant of Theorem 3.2: in each round `2, …, r`, the counted senders send at
least `t² / 44` messages. -/
def Heavy (A : Algorithm V M) (t : ℕ) (E : Execution V M) (v : V) (r : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ r → t ^ 2 ≤ 44 * roundCount A E k (sendersAt E r k v)

lemma sentTo_congr {E E' : Execution V M} {k : ℕ} {p : V}
    (h : ∀ q, msg A E k p q = msg A E' k p q) : sentTo A E k p = sentTo A E' k p := by
  simp [sentTo, h]

/-- The messages of the nodes of `W₀ ⊆ W'` in round `r + 1` of `E(W')` are those of `E₀`. -/
lemma sum_le_roundCount_pivot {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b)
    (hr : 1 ≤ r) {W₀ W' : Finset V} (hW₀ : W₀ ⊆ honest E₀ v) (hW₀W : W₀ ⊆ W') {v' : V}
    (hv' : v' ∉ W₀) :
    ∑ p ∈ W₀, (sentTo A E₀ (r + 1) p).card ≤
      roundCount A (pivot A E₀ E₁ v r W') (r + 1)
        ((nonfaulty (pivot A E₀ E₁ v r W') (r + 1)).erase v') := by
  unfold roundCount
  calc ∑ p ∈ W₀, (sentTo A E₀ (r + 1) p).card
      = ∑ p ∈ W₀, (sentTo A (pivot A E₀ E₁ v r W') (r + 1) p).card := by
        refine sum_congr rfl fun p hp => ?_
        have hp' := mem_honest.1 (hW₀ hp)
        rw [sentTo_congr (pivot_msg_succ_mem h W' hp'.1 hp'.2 (hW₀W hp) hr)]
    _ ≤ _ := by
        refine sum_le_sum_of_subset fun p hp => ?_
        have hp' := mem_honest.1 (hW₀ hp)
        simp only [mem_erase, nonfaulty, mem_filter, mem_univ, true_and]
        refine ⟨fun e => hv' (e ▸ hp), fun hf => ?_⟩
        exact (not_mem_pivot_F (A := A) (E₁ := E₁) (r := r) (W := W')).2 (hW₀ hp) hf.1

/-- The invariant is inherited by `E(W')` from `E₀`. -/
lemma heavy_pivot {Adm : Execution V M → Prop} (h : IsCritical A Adm r E₀ E₁ v b) (hr : 1 ≤ r)
    (hH : Heavy A t E₀ v r) (W' : Finset V) (v' : V)
    (hlast : t ^ 2 ≤ 44 * roundCount A (pivot A E₀ E₁ v r W') (r + 1)
      ((nonfaulty (pivot A E₀ E₁ v r W') (r + 1)).erase v')) :
    Heavy A t (pivot A E₀ E₁ v r W') v' (r + 1) := by
  intro k hk2 hk
  rcases Nat.lt_or_ge k (r + 1) with hk' | hk'
  · have hfault : ∀ p, (pivot A E₀ E₁ v r W').FaultyAt k p ↔ E₀.FaultyAt k p ∨ (k = r ∧ p = v) := by
      intro p
      by_cases hpv : p = v
      · subst hpv
        unfold pivot
        rw [faultyAt_addFaults_of_mem (mem_singleton_self _)]
        have := h.not_mem
        simp only [Execution.FaultyAt, this, false_and, false_or, and_true]
        omega
      · unfold pivot
        rw [faultyAt_addFaults_of_not_mem (by simpa using hpv)]
        simp [hpv]
    have hset : sendersAt (pivot A E₀ E₁ v r W') (r + 1) k v' = sendersAt E₀ r k v := by
      ext p
      simp only [sendersAt, if_neg (show k ≠ r + 1 by omega)]
      split_ifs with hkr
      · subst hkr
        simp only [nonfaulty, mem_filter, mem_univ, true_and, mem_erase, hfault]
        tauto
      · simp only [nonfaulty, mem_filter, mem_univ, true_and, hfault]
        tauto
    have hmsg : ∀ p ∈ sendersAt E₀ r k v,
        sentTo A (pivot A E₀ E₁ v r W') k p = sentTo A E₀ k p := by
      intro p hp
      apply sentTo_congr
      intro q
      rcases Nat.lt_or_ge k r with hkr | hkr
      · exact pivot_msg_lt h W' (by omega) hkr p q
      · obtain rfl : k = r := by omega
        have : p ≠ v := by simp [sendersAt] at hp; exact hp.1
        exact pivot_msg_r h W' this q
    unfold roundCount
    rw [hset, sum_congr rfl fun p hp => by rw [hmsg p hp]]
    exact hH k hk2 (by omega)
  · obtain rfl : k = r + 1 := by omega
    simpa [sendersAt] using hlast

end Count

section Lemma38Main

variable {t r : ℕ} {E₀ E₁ : Execution V M} {v : V} {b : Bool}

/-- Lemma 3.8, the construction: if the honest nodes other than `v` send many messages in round
`r + 1` of `E₀`, the `⌈t/2⌉` busiest of them form `W₀`, `E(W₀)` outputs `!b`, and the chain
from `W₀` yields an `(r+1)`-critical pair in which `W₀` sends at least `t² / 44` messages. -/
theorem exists_heavy_critical (hA : Correct A (byzAdm t)) (hnt : 3 * t < Fintype.card V)
    (hr : 1 ≤ r) (hrt : 2 * r ≤ t) (hd : Deciding A (byzAdm t) (· + 2))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v b)
    (hmany : Fintype.card V * t ≤ 22 * roundCount A E₀ (r + 1) (honest E₀ v)) :
    ∃ W₀ W v', W₀ ⊆ W ∧ W ⊆ honest E₀ v ∧ v' ∈ honest E₀ v ∧ v' ∉ W ∧
      t ^ 2 ≤ 44 * ∑ p ∈ W₀, (sentTo A E₀ (r + 1) p).card ∧
      IsCritical A (byzAdm t) (r + 1) (pivot A E₀ E₁ v r (insert v' W))
        (pivot A E₀ E₁ v r W) v' b := by
  set n := Fintype.card V
  have hd1 : DecidingAt A (byzAdm t) (r - 1) (r + 1) := by
    have := hd (r - 1); simp only at this; rwa [show r - 1 + 2 = r + 1 by omega] at this
  have hN : (honest E₀ v).card = n - r := card_honest h hr
  obtain ⟨W₀, hW₀, hW₀c, hW₀s⟩ := exists_subset_card_sum_ge (honest E₀ v)
    (fun p => (sentTo A E₀ (r + 1) p).card) (k := (t + 1) / 2) (by rw [hN]; omega)
  have hbig : t ^ 2 ≤ 44 * ∑ p ∈ W₀, (sentTo A E₀ (r + 1) p).card := by
    set c := roundCount A E₀ (r + 1) (honest E₀ v)
    set S := ∑ p ∈ W₀, (sentTo A E₀ (r + 1) p).card
    have hc : (t + 1) / 2 * c ≤ (n - r) * S := by rw [← hN]; exact hW₀s
    have h2k : t ≤ 2 * ((t + 1) / 2) := by omega
    have hpos : 0 < n - r := by omega
    have : t ^ 2 * (n - r) ≤ 44 * S * (n - r) := by
      calc t ^ 2 * (n - r) ≤ t * (n * t) := by
            rw [sq, mul_assoc]
            exact Nat.mul_le_mul_left t (by rw [mul_comm n t]; exact Nat.mul_le_mul_left t (Nat.sub_le n r))
        _ ≤ 2 * ((t + 1) / 2) * (22 * c) := Nat.mul_le_mul h2k hmany
        _ = 44 * ((t + 1) / 2 * c) := by ring
        _ ≤ 44 * ((n - r) * S) := Nat.mul_le_mul_left 44 hc
        _ = 44 * S * (n - r) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hout := out_pivot_of_small hA hnt hr hrt hd h hW₀ (by omega) (by omega)
  obtain ⟨W, v', hW₀W, hW, hv', hv'W, hc⟩ :=
    exists_pivot_isCritical hA h hr (by omega) (by omega) hd1 hW₀ hout
  exact ⟨W₀, W, v', hW₀W, hW, hv', hv'W, hbig, hc⟩

/-- Lemma 3.8 with the induction invariant of Theorem 3.2. -/
theorem lemma_3_8_heavy (hA : Correct A (byzAdm t)) (hnt : 3 * t < Fintype.card V)
    (hr : 1 ≤ r) (hrt : 2 * r ≤ t) (hd : Deciding A (byzAdm t) (· + 2))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v b) (hH₀ : Heavy A t E₀ v r)
    (hH₁ : Heavy A t E₁ v r) :
    ∃ E₀' E₁' v', IsCritical A (byzAdm t) (r + 1) E₀' E₁' v' false ∧
      Heavy A t E₀' v' (r + 1) ∧ Heavy A t E₁' v' (r + 1) := by
  have hd1 : DecidingAt A (byzAdm t) (r - 1) (r + 1) := by
    have := hd (r - 1); simp only at this; rwa [show r - 1 + 2 = r + 1 by omega] at this
  have h37 := lemma_3_7 hA hnt hr hrt hd1 h
  -- the generic step, for a critical pair whose first execution has many messages
  have step : ∀ (F₀ F₁ : Execution V M) (c : Bool), IsCritical A (byzAdm t) r F₀ F₁ v c →
      Heavy A t F₀ v r → Fintype.card V * t ≤ 22 * roundCount A F₀ (r + 1) (honest F₀ v) →
      ∃ E₀' E₁' v', IsCritical A (byzAdm t) (r + 1) E₀' E₁' v' false ∧
        Heavy A t E₀' v' (r + 1) ∧ Heavy A t E₁' v' (r + 1) := by
    intro F₀ F₁ c hc hH hmany
    obtain ⟨W₀, W, v', hW₀W, hW, hv', hv'W, hbig, hcrit⟩ :=
      exists_heavy_critical hA hnt hr hrt hd hc hmany
    have hv'W₀ : v' ∉ W₀ := fun e => hv'W (hW₀W e)
    have hW₀ : W₀ ⊆ honest F₀ v := hW₀W.trans hW
    have hH' : ∀ W', W₀ ⊆ W' → Heavy A t (pivot A F₀ F₁ v r W') v' (r + 1) := fun W' hW' =>
      heavy_pivot hc hr hH W' v'
        (hbig.trans (Nat.mul_le_mul_left 44 (sum_le_roundCount_pivot hc hr hW₀ hW' hv'W₀)))
    have h0 := hH' (insert v' W) (hW₀W.trans (subset_insert _ _))
    have h1 := hH' W hW₀W
    cases c
    · exact ⟨_, _, _, hcrit, h0, h1⟩
    · exact ⟨_, _, _, by simpa using hcrit.swap, h1, h0⟩
  by_cases hmany : Fintype.card V * t ≤ 22 * roundCount A E₀ (r + 1) (honest E₀ v)
  · exact step E₀ E₁ b h hH₀ hmany
  · have hhon : honest E₁ v = honest E₀ v := by simp [honest, h.F_eq]
    exact step E₁ E₀ (!b) h.swap hH₁ (by rw [hhon]; omega)

/-- **Lemma 3.8.** Let `A` be correct against `t` Byzantine faults (`n > 3t`) and
`(f+2)`-deciding. From an `r`-critical pair with `1 ≤ r ≤ t/2` one obtains an `(r+1)`-critical
pair in which the non-faulty nodes other than the new critical node send at least `t² / 44`
messages in round `r + 1` of both executions. -/
theorem lemma_3_8 (hA : Correct A (byzAdm t)) (hnt : 3 * t < Fintype.card V)
    (hr : 1 ≤ r) (hrt : 2 * r ≤ t) (hd : Deciding A (byzAdm t) (· + 2))
    (h : IsCritical A (byzAdm t) r E₀ E₁ v false) :
    ∃ E₀' E₁' v', IsCritical A (byzAdm t) (r + 1) E₀' E₁' v' false ∧
      t ^ 2 ≤ 44 * roundCount A E₀' (r + 1) ((nonfaulty E₀' (r + 1)).erase v') ∧
      t ^ 2 ≤ 44 * roundCount A E₁' (r + 1) ((nonfaulty E₁' (r + 1)).erase v') := by
  have hd1 : DecidingAt A (byzAdm t) (r - 1) (r + 1) := by
    have := hd (r - 1); simp only at this; rwa [show r - 1 + 2 = r + 1 by omega] at this
  have h37 := lemma_3_7 hA hnt hr hrt hd1 h
  have step : ∀ (F₀ F₁ : Execution V M) (c : Bool), IsCritical A (byzAdm t) r F₀ F₁ v c →
      Fintype.card V * t ≤ 22 * roundCount A F₀ (r + 1) (honest F₀ v) →
      ∃ E₀' E₁' v', IsCritical A (byzAdm t) (r + 1) E₀' E₁' v' false ∧
        t ^ 2 ≤ 44 * roundCount A E₀' (r + 1) ((nonfaulty E₀' (r + 1)).erase v') ∧
        t ^ 2 ≤ 44 * roundCount A E₁' (r + 1) ((nonfaulty E₁' (r + 1)).erase v') := by
    intro F₀ F₁ c hc hmany
    obtain ⟨W₀, W, v', hW₀W, hW, hv', hv'W, hbig, hcrit⟩ :=
      exists_heavy_critical hA hnt hr hrt hd hc hmany
    have hv'W₀ : v' ∉ W₀ := fun e => hv'W (hW₀W e)
    have hW₀ : W₀ ⊆ honest F₀ v := hW₀W.trans hW
    have h0 := hbig.trans (Nat.mul_le_mul_left 44
      (sum_le_roundCount_pivot hc hr hW₀ (hW₀W.trans (subset_insert v' W)) hv'W₀))
    have h1 := hbig.trans (Nat.mul_le_mul_left 44 (sum_le_roundCount_pivot hc hr hW₀ hW₀W hv'W₀))
    cases c
    · exact ⟨_, _, _, hcrit, h0, h1⟩
    · exact ⟨_, _, _, by simpa using hcrit.swap, h1, h0⟩
  by_cases hmany : Fintype.card V * t ≤ 22 * roundCount A E₀ (r + 1) (honest E₀ v)
  · exact step E₀ E₁ false h hmany
  · have hhon : honest E₁ v = honest E₀ v := by simp [honest, h.F_eq]
    exact step E₁ E₀ true h.swap (by rw [hhon]; omega)

end Lemma38Main

/-! ### Theorem 3.2 -/

/-- **Theorem 3.2.** Let `A` be an `(f+2)`-deciding binary consensus algorithm tolerating `t`
Byzantine faults, `n > 3t`, and `1 ≤ f ≤ t/2`. Then some execution with exactly `f` faulty nodes
has the non-faulty nodes send at least `t² f / 44` messages (in its first `f + 1` rounds). -/
theorem theorem_3_2 {t : ℕ} (hnt : 3 * t < Fintype.card V) (hA : Correct A (byzAdm t))
    (hd : Deciding A (byzAdm t) (· + 2)) {f : ℕ} (hf1 : 1 ≤ f) (hft : 2 * f ≤ t) :
    ∃ E : Execution V M, byzAdm t E ∧ E.F.card = f ∧ t ^ 2 * f ≤ 44 * msgCount A E (f + 1) := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have key : ∀ r, 1 ≤ r → r ≤ f + 1 → ∃ E₀ E₁ v, IsCritical A (byzAdm t) r E₀ E₁ v false ∧
      Heavy A t E₀ v r ∧ Heavy A t E₁ v r := by
    intro r hr hrf
    induction r, hr using Nat.le_induction with
    | base =>
      obtain ⟨E₀, E₁, v, h⟩ := exists_critical_one hA fun x => by simp [byzAdm, faultFree]
      exact ⟨E₀, E₁, v, h, fun k hk2 hk => by omega, fun k hk2 hk => by omega⟩
    | succ r hr ih =>
      obtain ⟨E₀, E₁, v, h, h0, h1⟩ := ih (by omega)
      exact lemma_3_8_heavy hA hnt hr (by omega) hd h h0 h1
  obtain ⟨E₀, E₁, v, h, hH, -⟩ := key (f + 1) (by omega) le_rfl
  refine ⟨E₀, h.adm₀, by rw [h.card]; rfl, ?_⟩
  unfold msgCount
  calc t ^ 2 * f = ∑ k ∈ Icc 2 (f + 1), t ^ 2 := by simp; ring
    _ ≤ ∑ k ∈ Icc 2 (f + 1), 44 * roundCount A E₀ k (sendersAt E₀ (f + 1) k v) :=
        sum_le_sum fun k hk => by rw [mem_Icc] at hk; exact hH k hk.1 hk.2
    _ ≤ ∑ k ∈ Icc 2 (f + 1), 44 * roundCount A E₀ k (nonfaulty E₀ k) := by
        refine sum_le_sum fun k _ => Nat.mul_le_mul_left 44 ?_
        refine sum_le_sum_of_subset ?_
        unfold sendersAt; split_ifs
        · exact erase_subset _ _
        · exact subset_rfl
    _ ≤ ∑ k ∈ Icc 1 (f + 1), 44 * roundCount A E₀ k (nonfaulty E₀ k) :=
        sum_le_sum_of_subset (Icc_subset_Icc (by omega) le_rfl)
    _ = 44 * ∑ k ∈ Icc 1 (f + 1), roundCount A E₀ k (nonfaulty E₀ k) := by rw [mul_sum]

end Podc.EarlyDecidingExpensive
