import Papers.PODC2024.ListDefectiveColoring.Section41

/-!
# Runs of the Section 4.1 algorithm exist (non-vacuity of Theorem 1.4 of [FK24])

Fuchs, Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective
Coloring Algorithms* (PODC 2024; arXiv:2405.04648), cited as [FK24].

`IsRun` (see `Section41.lean`) quantifies over all possible outputs of the arbdefective subroutine.
Here we show that, on a finite graph and for `S ≥ 1`, runs always exist, so Theorem 1.4 is not
vacuous:

* `exists_listArbdefective_greedy` (CSLib candidate): every list arbdefective colouring instance on
  a finite vertex set `U` with `∑_{x ∈ L_v} (d_v(x) + 1) > deg_U(v)` is solvable (greedy colouring
  with edges oriented towards earlier nodes).
* `Sec41.exists_isRun`: a run exists for all parameters with `S ≥ 1` (built iteration by iteration
  from `top` down to `0`; `H_i` only depends on the iterations `> i`).
* `Sec41.theorem_1_4_exists`: under the hypotheses of Theorem 1.4 a list defective colouring
  exists.
-/

open Finset SimpleGraph
open scoped Classical

namespace FK24

-- CSLib candidate
/-- Greedy list arbdefective colouring: if every node `v` of the finite set `U` satisfies
`deg_U(v) < ∑_{x ∈ L_v} (d_v(x) + 1)`, then there is a colouring `col` of `U` from the lists and an
orientation `O` of the monochromatic edges inside `U` such that each `u ∈ U` has at most
`d_u(col u)` out-neighbours in `U` of its own colour. -/
theorem exists_listArbdefective_greedy {V α : Type*} [Nonempty α] (G : SimpleGraph V)
    (L : V → Finset α) (d : V → α → ℕ) (U : Finset V)
    (h : ∀ v ∈ U, #{w ∈ U | G.Adj v w} < ∑ x ∈ L v, (d v x + 1)) :
    ∃ (col : V → α) (O : V → V → Prop), (∀ v ∈ U, col v ∈ L v) ∧
      (∀ u ∈ U, ∀ w ∈ U, G.Adj u w → col u = col w → O u w ∨ O w u) ∧
      ∀ u ∈ U, #{w ∈ U | G.Adj u w ∧ O u w ∧ col w = col u} ≤ d u (col u) := by
  induction U using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary α, fun _ _ => False, by simp, by simp, by simp⟩
  | insert a U ha ih =>
    obtain ⟨col, O, hL, hor, hout⟩ := ih fun v hv =>
      lt_of_le_of_lt (card_le_card (filter_subset_filter _ (subset_insert _ _)))
        (h v (mem_insert_of_mem hv))
    -- a colour for `a` with few earlier neighbours of that colour
    have hex : ∃ x ∈ L a, #{w ∈ U | G.Adj a w ∧ col w = x} ≤ d a x := by
      by_contra hcon
      push Not at hcon
      have h1 : ∑ x ∈ L a, (d a x + 1) ≤ ∑ x ∈ L a, #{w ∈ U | G.Adj a w ∧ col w = x} :=
        sum_le_sum fun x hx => hcon x hx
      have h2 := Sec41.sum_card_filter_and_eq_le U (L a) (G.Adj a) col
      have h3 : #{w ∈ U | G.Adj a w} ≤ #{w ∈ insert a U | G.Adj a w} :=
        card_le_card (filter_subset_filter _ (subset_insert _ _))
      have h4 := h a (mem_insert_self _ _)
      omega
    obtain ⟨x, hxL, hx⟩ := hex
    have hne : ∀ v ∈ U, v ≠ a := fun v hv h => ha (h ▸ hv)
    refine ⟨Function.update col a x, fun u w => (u ≠ a ∧ w ≠ a ∧ O u w) ∨ (u = a ∧ w ∈ U),
      ?_, ?_, ?_⟩
    · intro v hv
      rcases mem_insert.1 hv with rfl | hv
      · simpa using hxL
      · simpa [hne v hv] using hL v hv
    · intro u hu w hw hadj hcol
      rcases mem_insert.1 hu with rfl | hu' <;> rcases mem_insert.1 hw with rfl | hw'
      · exact absurd hadj (G.loopless.irrefl _)
      · exact Or.inl (Or.inr ⟨rfl, hw'⟩)
      · exact Or.inr (Or.inr ⟨rfl, hu'⟩)
      · simp only [Function.update_of_ne (hne u hu'), Function.update_of_ne (hne w hw')] at hcol
        rcases hor u hu' w hw' hadj hcol with h' | h'
        · exact Or.inl (Or.inl ⟨hne u hu', hne w hw', h'⟩)
        · exact Or.inr (Or.inl ⟨hne w hw', hne u hu', h'⟩)
    · intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · refine le_trans (card_le_card fun w hw => ?_) (by simpa using hx)
        simp only [mem_filter, mem_insert] at hw ⊢
        obtain ⟨hw, hadj, -, hcol⟩ := hw
        have hwu : w ≠ u := fun h => G.loopless.irrefl _ (h ▸ hadj)
        rcases hw with rfl | hw
        · exact absurd rfl hwu
        · simp only [Function.update_of_ne hwu, Function.update_self] at hcol
          exact ⟨hw, hadj, hcol⟩
      · refine le_trans (card_le_card fun w hw => ?_) (by simpa [hne u hu] using hout u hu)
        simp only [mem_filter, mem_insert] at hw ⊢
        obtain ⟨hw, hadj, hO, hcol⟩ := hw
        rcases hO with ⟨-, hwa, hO⟩ | ⟨hua, -⟩
        · rcases hw with rfl | hw
          · exact absurd rfl hwa
          · simp only [Function.update_of_ne hwa, Function.update_of_ne (hne u hu)] at hcol
            exact ⟨hw, hadj, hO, hcol⟩
        · exact absurd hua (hne u hu)

namespace Sec41

variable {V α : Type*} {G : SimpleGraph V} [G.LocallyFinite] {I : ListInstance V α}
  {d' : V → α → ℤ} {S : ℝ} {top : ℕ}

/-! ### Locality: everything in iteration `i` depends only on iterations `> i` -/

/-- Two partial runs agree on everything that happened before iteration `i`. -/
def AgreeAbove (it it' : V → Option ℕ) (col col' : V → α) (i : ℕ) : Prop :=
  (∀ u k, i < k → (it u = some k ↔ it' u = some k)) ∧
    ∀ u, ColoredBefore it u i → col u = col' u

variable {it it' : V → Option ℕ} {col col' : V → α} {i : ℕ}

omit [G.LocallyFinite] in
theorem AgreeAbove.mono (h : AgreeAbove it it' col col' i) {j : ℕ} (hij : i ≤ j) :
    AgreeAbove it it' col col' j :=
  ⟨fun u k hk => h.1 u k (by omega), fun u ⟨k, hk, hjk⟩ => h.2 u ⟨k, hk, by omega⟩⟩

omit [G.LocallyFinite] in
theorem AgreeAbove.coloredBefore_iff (h : AgreeAbove it it' col col' i) (u : V) :
    ColoredBefore it u i ↔ ColoredBefore it' u i :=
  ⟨fun ⟨k, hk, hik⟩ => ⟨k, (h.1 u k hik).1 hk, hik⟩,
    fun ⟨k, hk, hik⟩ => ⟨k, (h.1 u k hik).2 hk, hik⟩⟩

theorem AgreeAbove.aCount_eq (h : AgreeAbove it it' col col' i) (v : V) (x : α) :
    aCount G it col v x i = aCount G it' col' v x i := by
  unfold aCount
  congr 1
  refine filter_congr fun u _ => ⟨fun ⟨hcb, hc⟩ => ⟨(h.coloredBefore_iff u).1 hcb, ?_⟩,
    fun ⟨hcb, hc⟩ => ⟨(h.coloredBefore_iff u).2 hcb, ?_⟩⟩
  · rw [← h.2 u hcb]; exact hc
  · rw [h.2 u ((h.coloredBefore_iff u).2 hcb)]; exact hc

theorem AgreeAbove.uncolCount_eq (h : AgreeAbove it it' col col' i) (v : V) :
    uncolCount G it v i = uncolCount G it' v i := by
  unfold uncolCount
  congr 1
  exact filter_congr fun u _ => not_congr (h.coloredBefore_iff u)

theorem AgreeAbove.cond_iff (h : AgreeAbove it it' col col' i) (v : V) (x : α) :
    Cond G d' it col v x i ↔ Cond G d' it' col' v x i := by
  simp only [Cond, h.aCount_eq]

theorem AgreeAbove.inL_iff (h : AgreeAbove it it' col col' i) (v : V) (x : α) :
    InL G I d' top it col v x i ↔ InL G I d' top it' col' v x i := by
  have hj : ∀ j, i < j → (Cond G d' it col v x j ↔ Cond G d' it' col' v x j) :=
    fun j hj => (h.mono hj.le).cond_iff v x
  unfold InL
  rw [h.cond_iff]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' fun j => imp_congr_right fun hij => imp_congr_right fun _ => not_congr (hj j hij)

theorem AgreeAbove.listAt_eq (h : AgreeAbove it it' col col' i) (v : V) :
    listAt G I d' top it col v i = listAt G I d' top it' col' v i :=
  filter_congr fun x _ => h.inL_iff v x

theorem AgreeAbove.inH_iff (h : AgreeAbove it it' col col' i) (v : V) :
    InH G I d' S top it col v i ↔ InH G I d' S top it' col' v i := by
  unfold InH
  rw [h.coloredBefore_iff, h.uncolCount_eq, h.listAt_eq]

/-! ### Partial runs -/

variable (G I d' S top) in
/-- A partial run in which the iterations `top, …, m` have been executed. -/
structure IsPartialRun (m : ℕ) (it : V → Option ℕ) (col : V → α) : Prop where
  colored_spec : ∀ v i, it v = some i →
    m ≤ i ∧ i ≤ top ∧ InH G I d' S top it col v i ∧ InL G I d' top it col v (col v) i
  colored_of_inH : ∀ v i, m ≤ i → i ≤ top → InH G I d' S top it col v i → it v = some i
  arbdefective : ∀ i, ∃ O : V → V → Prop,
    (∀ ⦃u w⦄, G.Adj u w → it u = some i → it w = some i → col u = col w → O u w ∨ O w u) ∧
    ∀ u, it u = some i →
      #{w ∈ G.neighborFinset u | O u w ∧ it w = some i ∧ col w = col u} ≤ dI i

theorem IsPartialRun.isRun (h : IsPartialRun G I d' S top 0 it col) :
    IsRun G I d' S top it col where
  colored_spec v i hv := (h.colored_spec v i hv).2
  colored_of_inH v i hi hH := h.colored_of_inH v i (Nat.zero_le _) hi hH
  arbdefective := h.arbdefective

theorem isPartialRun_init (col : V → α) :
    IsPartialRun G I d' S top (top + 1) (fun _ => none) col where
  colored_spec v i h := by simp at h
  colored_of_inH v i h1 h2 _ := by omega
  arbdefective i := ⟨fun _ _ => False, fun _ _ _ h => by simp at h, fun u h => by simp at h⟩

/-- One iteration (`m`) of the algorithm: colour `H_m` greedily. -/
theorem IsPartialRun.step [Fintype V] [Nonempty α] (hS : 1 ≤ S) {m : ℕ} (hm : m ≤ top)
    (hP : IsPartialRun G I d' S top (m + 1) it col) :
    ∃ it' col', IsPartialRun G I d' S top m it' col' := by
  set H : Finset V := univ.filter (fun v => InH G I d' S top it col v m) with hHdef
  have hmemH : ∀ v, v ∈ H ↔ InH G I d' S top it col v m := by simp [H]
  have hgreedy : ∀ v ∈ H, #{w ∈ H | G.Adj v w} <
      ∑ x ∈ listAt G I d' top it col v m, (dI m + 1) := by
    intro v hv
    obtain ⟨-, hlt⟩ := (hmemH v).1 hv
    have h1 : #{w ∈ H | G.Adj v w} ≤ uncolCount G it v m := by
      unfold uncolCount
      refine card_le_card fun w hw => ?_
      simp only [mem_filter, mem_neighborFinset] at hw ⊢
      exact ⟨hw.2, ((hmemH w).1 hw.1).1⟩
    have h2 : (#{w ∈ H | G.Adj v w} : ℝ) ≤ S * uncolCount G it v m := by
      have : (#{w ∈ H | G.Adj v w} : ℝ) ≤ uncolCount G it v m := by exact_mod_cast h1
      have h0 : (0 : ℝ) ≤ uncolCount G it v m := Nat.cast_nonneg _
      nlinarith
    have h3 := lt_of_le_of_lt h2 hlt
    rw [sum_const, nsmul_eq_mul] at h3
    rw [sum_const, smul_eq_mul]
    exact_mod_cast h3
  obtain ⟨colH, O, hcolL, hor, hout⟩ := exists_listArbdefective_greedy G
    (fun v => listAt G I d' top it col v m) (fun _ _ => dI m) H hgreedy
  -- nodes coloured before are not in `H`
  have hnotH : ∀ v i, it v = some i → v ∉ H := by
    intro v i hv hvH
    have := (hP.colored_spec v i hv).1
    exact ((hmemH v).1 hvH).1 ⟨i, hv, by omega⟩
  have hnot_m : ∀ v, it v ≠ some m := fun v hv => by
    have := (hP.colored_spec v m hv).1
    omega
  refine ⟨fun v => if v ∈ H then some m else it v,
    fun v => if v ∈ H then colH v else col v, ?_⟩
  set it' : V → Option ℕ := fun v => if v ∈ H then some m else it v with hit'
  set col' : V → α := fun v => if v ∈ H then colH v else col v with hcol'
  have hagree : ∀ i, m ≤ i → AgreeAbove it it' col col' i := by
    intro i hi
    refine ⟨fun u k hk => ?_, fun u ⟨k, hk, _⟩ => ?_⟩
    · by_cases hu : u ∈ H
      · simp only [it', hu, ite_true, Option.some.injEq]
        constructor
        · intro h; exact absurd hu (hnotH u k h)
        · intro h; omega
      · simp [it', hu]
    · simp [col', hnotH u k hk]
  have hit'_ne : ∀ u j, j ≠ m → (it' u = some j ↔ it u = some j) := by
    intro u j hj
    by_cases hu : u ∈ H
    · simp only [it', hu, ite_true, Option.some.injEq]
      constructor
      · intro h; exact absurd h.symm hj
      · intro h; exact absurd hu (hnotH u j h)
    · simp [it', hu]
  have hit'_m : ∀ u, it' u = some m ↔ u ∈ H := by
    intro u
    by_cases hu : u ∈ H
    · simp [it', hu]
    · simp [it', hu, hnot_m u]
  refine ⟨?_, ?_, ?_⟩
  · intro v i hv
    by_cases hvH : v ∈ H
    · have him : i = m := by simpa [it', hvH] using hv.symm
      subst him
      refine ⟨le_rfl, hm, ((hagree i le_rfl).inH_iff v).1 ((hmemH v).1 hvH), ?_⟩
      have := hcolL v hvH
      simp only [listAt, mem_filter] at this
      simpa [col', hvH] using ((hagree i le_rfl).inL_iff v (colH v)).1 this.2
    · have hv' : it v = some i := by simpa [it', hvH] using hv
      obtain ⟨h1, h2, h3, h4⟩ := hP.colored_spec v i hv'
      refine ⟨by omega, h2, ((hagree i (by omega)).inH_iff v).1 h3, ?_⟩
      simpa [col', hvH] using ((hagree i (by omega)).inL_iff v (col v)).1 h4
  · intro v i hmi hi hH'
    have hH := ((hagree i hmi).inH_iff v).2 hH'
    rcases hmi.lt_or_eq with hmi | rfl
    · have hv := hP.colored_of_inH v i hmi hi hH
      simp [it', hnotH v i hv, hv]
    · exact (hit'_m v).2 ((hmemH v).2 hH)
  · intro i
    by_cases him : i = m
    · subst him
      refine ⟨O, fun u w hadj hu hw hc => ?_, fun u hu => ?_⟩
      · have hu' := (hit'_m u).1 hu
        have hw' := (hit'_m w).1 hw
        simp only [col', hu', hw', ite_true] at hc
        exact hor u hu' w hw' hadj hc
      · have hu' := (hit'_m u).1 hu
        refine le_trans (card_le_card fun w hw => ?_) (by simpa [col', hu'] using hout u hu')
        simp only [mem_filter, mem_neighborFinset] at hw ⊢
        obtain ⟨hadj, hO, hw, hc⟩ := hw
        have hw' := (hit'_m w).1 hw
        simp only [col', hu', hw', ite_true] at hc
        exact ⟨hw', hadj, hO, hc⟩
    · obtain ⟨O', hor', hout'⟩ := hP.arbdefective i
      have hcol_eq : ∀ u, it u = some i → col' u = col u := fun u hu => by
        simp [col', hnotH u i hu]
      refine ⟨O', fun u w hadj hu hw hc => ?_, fun u hu => ?_⟩
      · rw [hit'_ne u i him] at hu
        rw [hit'_ne w i him] at hw
        rw [hcol_eq u hu, hcol_eq w hw] at hc
        exact hor' hadj hu hw hc
      · rw [hit'_ne u i him] at hu
        refine le_trans (card_le_card fun w hw => ?_) (hout' u hu)
        simp only [mem_filter] at hw ⊢
        obtain ⟨hwN, hO, hw, hc⟩ := hw
        rw [hit'_ne w i him] at hw
        rw [hcol_eq u hu, hcol_eq w hw] at hc
        exact ⟨hwN, hO, hw, hc⟩

/-- On a finite graph, for every slack parameter `S ≥ 1` (and arbitrary instance, defects `d'` and
number of iterations), the algorithm of Section 4.1 of [FK24] has a run: the arbdefective
subroutine can always succeed, because every node `v ∈ H_i` has
`∑_{x ∈ L_{v,i}} (d_i + 1) > S (deg(v) - deg~(v, i)) ≥ deg_{H_i}(v)`. -/
theorem exists_isRun [Fintype V] [Nonempty α] (hS : 1 ≤ S) :
    ∃ it col, IsRun G I d' S top it col := by
  have key : ∀ k, k ≤ top + 1 → ∃ it col, IsPartialRun G I d' S top (top + 1 - k) it col := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨_, _, by simpa using isPartialRun_init (Classical.arbitrary _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨it, col, hP⟩ := ih (by omega)
      have hk' : top + 1 - k = (top + 1 - (k + 1)) + 1 := by omega
      rw [hk'] at hP
      exact hP.step hS (by omega)
  obtain ⟨it, col, hP⟩ := key (top + 1) le_rfl
  rw [Nat.sub_self] at hP
  exact ⟨it, col, hP.isRun⟩

/-- Non-vacuity of Theorem 1.4 of [FK24]: under its hypotheses (finite graph), the algorithm has a
run, hence a list defective colouring exists. -/
theorem theorem_1_4_exists [Fintype V] [Nonempty α] {θ Δ : ℕ} (hθ : G.NeighborhoodIndepLE θ)
    (hθ1 : 1 ≤ θ) (hS : 1 ≤ S) (hΔ : 2 ≤ Δ) (hdΔ : ∀ v, ∀ x ∈ I.L v, I.d v x ≤ Δ)
    (hslack : HasSlack G I (21 * θ * (Nat.clog 2 Δ + 1) * S)) :
    ∃ it col, IsRun G I (dPrime I θ) S (Nat.clog 2 Δ) it col ∧ IsListDefective G I col := by
  obtain ⟨it, col, hrun⟩ := exists_isRun (G := G) (I := I) (d' := dPrime I θ)
    (top := Nat.clog 2 Δ) hS
  exact ⟨it, col, hrun, (theorem_1_4 hθ hθ1 hS hΔ hdΔ hslack hrun).2⟩

end Sec41

end FK24
