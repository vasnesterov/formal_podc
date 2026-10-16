import Papers.PODC2022.ConsensusFromSwap.Alg1AgreeLemma5

/-!
# Algorithm 1 satisfies k-agreement (Lemma 6)

Lemma 6 of Ovens (PODC 2022): with `n ≤ N + k` processes (the paper: `N = n − k` objects) and
`k ≥ 1`, at most `k` distinct values are decided in every execution of Algorithm 1.
-/

namespace ConsensusFromSwap.Alg1.Agree

open ConsensusFromSwap

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

lemma le_lead (U : Lap m) (j : Fin m) : U j ≤ U (lead U) := by
  unfold lead
  have := Finset.min'_mem (Finset.univ.filter fun j => ∀ j', U j' ≤ U j) (by
    obtain ⟨j, hj⟩ := (Finset.univ : Finset (Fin m)).exists_max_image U
      ⟨0, Finset.mem_univ _⟩
    exact ⟨j, by simpa using fun j' => hj.2 j' (Finset.mem_univ _)⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this j

/-- The index of the last object. -/
def lastIdx : Fin N := ⟨N - 1, by have := NeZero.pos N; omega⟩

lemma le_at {U V : Lap m} (h : U ≤ V) (j : Fin m) : U j ≤ V j := h j

lemma eq_lastIdx {i : Fin N} (h : i.val + 1 = N) : i = lastIdx := Fin.ext (by simp [lastIdx]; omega)

namespace Sched

variable (E : Sched P m N)

/-- A process deciding `x`, with the data of Observation 2 for its deciding step: it decides at
time `τ` with (final) lap counter `V = U_p(τ)`, the configuration at time `s ≤ τ` is
`⟨V, p⟩`-total, and nobody swaps the last object during `[s, τ)`. -/
structure DecData (x : Fin m) where
  /-- The time of the deciding step. -/
  τ : ℕ
  /-- The deciding process. -/
  p : P
  /-- The start of the deciding iteration. -/
  s : ℕ
  /-- The lap counter with which `p` decides. -/
  V : Lap m
  /-- `p` takes step `τ`. -/
  σ_eq : E.σ τ = p
  V_eq : (E.st τ p).U = V
  /-- `p` is undecided before step `τ`. -/
  dec_none : (E.st τ p).dec = none
  /-- `p` has decided `x` after step `τ`. -/
  dec_some : (E.st (τ + 1) p).dec = some x
  s_le : s ≤ τ
  /-- Observation 2: the configuration at time `s` is `⟨V, p⟩`-total. -/
  total : E.Total s V p
  /-- Nobody swaps the last object during `[s, τ)`. -/
  noWr : ∀ t', s ≤ t' → t' < τ → ¬ E.Wr t' lastIdx
  /-- The deciding step swaps the last object. -/
  wr : E.Wr τ lastIdx
  /-- The condition on line 16. -/
  gap : ∀ y, y ≠ x → V y + 2 ≤ V x
  /-- `V` is the final lap counter of `p` (Observation 3). -/
  U_le : ∀ t, (E.st t p).U ≤ V

namespace DecData

variable {E} {x x' : Fin m} (D : E.DecData x) (D' : E.DecData x')

lemma dec_of_le {t : ℕ} (ht : t ≤ D.τ) : (E.st t D.p).dec = none :=
  E.dec_none_of_le ht D.dec_none

lemma dec_of_gt {t : ℕ} (ht : D.τ < t) : (E.st t D.p).dec ≠ none := by
  rw [E.st_eq_of_dec ht (by rw [D.dec_some]; simp), D.dec_some]
  simp

/-- `W1`: a process deciding before `D.τ` decides before the deciding iteration of `D.p` starts
(both deciding steps swap the last object). -/
lemma lt_s (h : D'.τ < D.τ) : D'.τ < D.s := by
  by_contra h'
  exact D.noWr D'.τ (by omega) h D'.wr

lemma eq_of_τ_eq (h : D.τ = D'.τ) : x = x' := by
  have hp : D.p = D'.p := by rw [← D.σ_eq, ← D'.σ_eq, h]
  have := D.dec_some
  rw [h, hp, D'.dec_some] at this
  exact (Option.some.inj this).symm

lemma eq_of_p_eq (h : D.p = D'.p) : x = x' := by
  rcases lt_trichotomy D.τ D'.τ with hlt | heq | hlt
  · exact absurd (D'.dec_none) (h ▸ D.dec_of_gt hlt)
  · exact D.eq_of_τ_eq D' heq
  · exact absurd (D.dec_none) (h.symm ▸ D'.dec_of_gt hlt)

end DecData

/-- Every decided value has a `DecData`. -/
noncomputable def decData {T : ℕ} {q : P} {x : Fin m} (h : (E.st T q).dec = some x) :
    E.DecData x := by
  classical
  have hex : ∃ t, (E.st t q).dec ≠ none := ⟨T, by rw [h]; simp⟩
  let t0 := Nat.find hex
  have ht0 : (E.st t0 q).dec ≠ none := Nat.find_spec hex
  have ht0T : t0 ≤ T := Nat.find_min' hex (by rw [h]; simp)
  have ht0pos : t0 ≠ 0 := by
    intro h0
    rw [h0] at ht0
    exact ht0 rfl
  let τ := t0 - 1
  have hτ : τ + 1 = t0 := by omega
  have hdn : (E.st τ q).dec = none := by
    by_contra h'
    exact Nat.find_min hex (show τ < t0 by omega) h'
  have hds : (E.st (τ + 1) q).dec = some x := by
    rw [← h, hτ, E.st_eq_of_dec ht0T ht0]
  have hstep := E.decStep hdn hds
  have hcl := hstep.1
  have hσ : E.σ τ = q := hcl.1
  have hlast : (E.st τ q).idx = lastIdx := eq_lastIdx hcl.2.2.1
  have hs := E.obs2 hcl
  let s := Classical.choose hs
  have hs' := Classical.choose_spec hs
  exact
  { τ := τ, p := q, s := s, V := (E.st τ q).U
    σ_eq := hσ
    V_eq := rfl
    dec_none := hdn
    dec_some := hds
    s_le := hs'.1
    total := hs'.2.1
    noWr := fun t' h1 h2 => hlast ▸ hs'.2.2 t' h1 h2
    wr := ⟨hσ ▸ hdn, hσ ▸ hlast⟩
    gap := fun y hy => by
      have := hstep.2.2.1 y (by rw [← hstep.2.1]; exact hy)
      rwa [← hstep.2.1] at this
    U_le := fun t => by
      rcases le_or_gt t τ with ht | ht
      · exact E.st_U_mono ht q
      · rw [E.st_eq_of_dec (show τ + 1 ≤ t by omega) (by rw [hds]; simp), hstep.2.2.2] }

/-- Pigeonhole: an injective `d : Fin N → P` hits every set of more than `card P - N`
processes. -/
lemma exists_mem_of_card [Fintype P] {d : Fin N → P} (hd : Function.Injective d)
    (F : Finset P) (h : Fintype.card P < N + F.card) : ∃ i, d i ∈ F := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  have hdisj : Disjoint (Finset.univ.image d) F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact hcon i haF
  have := Finset.card_le_univ (Finset.univ.image d ∪ F)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hd,
    Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The core of Lemma 6: there are no `k + 1` processes deciding `k + 1` distinct values. -/
theorem not_decData [Fintype P] {k : ℕ} (hP : Fintype.card P ≤ N + k) (hk : 1 ≤ k)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = k + 1) (val : ι → Fin m)
    (hval : Function.Injective val) (D : ∀ j, E.DecData (val j)) : False := by
  classical
  have hpinj : Function.Injective fun j => (D j).p :=
    fun j j' h => hval ((D j).eq_of_p_eq (D j') h)
  have hτinj : ∀ j j', (D j).τ = (D j').τ → j = j' :=
    fun j j' h => hval ((D j).eq_of_τ_eq (D j') h)
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ, hι]; omega
  obtain ⟨last, -, hlast⟩ := Finset.exists_max_image Finset.univ (fun j => (D j).τ) hne
  have hτlt : ∀ j, j ≠ last → (D j).τ < (D last).τ := fun j hj =>
    lt_of_le_of_ne (hlast j (Finset.mem_univ _)) (fun h => hj (hτinj _ _ h))
  -- Step 1: `ℓ_last` is maximal.
  have step1 : ∀ j, (D j).V (val j) ≤ (D last).V (val last) := by
    by_contra hcon
    simp only [not_forall, not_le] at hcon
    obtain ⟨j, hjS, hjmax⟩ := (Finset.univ.filter fun j =>
        (D last).V (val last) < (D j).V (val j)).exists_max_image (fun j => (D j).τ)
      (by obtain ⟨j, hj⟩ := hcon; exact ⟨j, by simpa using hj⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS hjmax
    have hjl : j ≠ last := by rintro rfl; omega
    have h1 := (D last).lt_s (D j) (hτlt j hjl)
    have hV : ¬ (D j).V ≤ (D last).V := by
      intro hle
      have := (D last).gap (val j) (fun h => hjl (hval h))
      have := le_at hle (val j)
      omega
    obtain ⟨d, hdinj, hd⟩ :=
      E.lemma5 (D j).total (D last).total (by have := (D j).s_le; omega) hV
    have hcard : Fintype.card P < N + (Finset.univ.image fun j => (D j).p).card := by
      rw [Finset.card_image_of_injective _ hpinj, Finset.card_univ, hι]; omega
    obtain ⟨i, hi⟩ := exists_mem_of_card hdinj _ hcard
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨j', hj'⟩ := hi
    obtain ⟨hd1, hd2, hd3, hd4, -⟩ := hd i
    have hj'j : j' ≠ j := by rintro rfl; exact hd1 hj'.symm
    have hτ' : (D j).τ < (D j').τ := by
      rcases lt_trichotomy (D j').τ (D j).τ with h | h | h
      · have := (D j).lt_s (D j') h
        exact absurd (hj' ▸ hd4) ((D j').dec_of_gt this)
      · exact absurd (hτinj _ _ h) hj'j
      · exact h
    have hVV : (D j).V ≤ (D j').V := hd3.trans (hj' ▸ (D j').U_le _)
    have hgap := (D j').gap (val j) (fun h => hj'j (hval h).symm)
    have h2 := le_at hVV (val j)
    have := hjmax j' (by omega)
    omega
  -- Step 2.
  have hne2 : (Finset.univ.erase last).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hι]
    omega
  obtain ⟨t, ht, htmax⟩ := (Finset.univ.erase last).exists_max_image (fun j => (D j).V (val j))
    hne2
  have htl : t ≠ last := Finset.ne_of_mem_erase ht
  have hgt := (D t).gap (val last) (fun h => htl (hval h).symm)
  have hbig : E.Big (D last).τ (val last) ((D t).V (val t)) :=
    Or.inl ⟨(D last).p, by rw [(D last).V_eq]; exact step1 t⟩
  obtain ⟨t', -, hcl, hlead, hinc⟩ := E.obs1 (by omega) hbig
  obtain ⟨s', -, hT', -⟩ := E.obs2 hcl
  have hWmax : ∀ y, (E.st t' (E.σ t')).U y ≤ (E.st t' (E.σ t')).U (val last) :=
    fun y => hlead ▸ le_lead _ y
  have hqne : ∀ j, j ≠ last → E.σ t' ≠ (D j).p := by
    intro j hj hq
    have h1 : (E.st t' (E.σ t')).U ≤ (D j).V := hq ▸ (D j).U_le t'
    have h2 := (D j).gap (val last) (fun h => hj (hval h).symm)
    have h3 := htmax j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
    have := le_at h1 (val last)
    omega
  have hcard2 : Fintype.card P <
      N + (insert (E.σ t') ((Finset.univ.erase last).image fun j => (D j).p)).card := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hpinj,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hι]
    · omega
    · simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, not_exists,
        not_and]
      exact fun j hj h => hqne j hj h.symm
  have pick : ∀ d : Fin N → P, Function.Injective d →
      (∀ i, d i ≠ E.σ t' ∧ d i ≠ (D t).p) → ∃ i j', j' ≠ last ∧ j' ≠ t ∧ (D j').p = d i := by
    intro d hd hdq
    obtain ⟨i, hi⟩ := exists_mem_of_card hd _ hcard2
    rw [Finset.mem_insert, Finset.mem_image] at hi
    rcases hi with hi | ⟨j', hj', hj'i⟩
    · exact absurd hi (hdq i).1
    · exact ⟨i, j', Finset.ne_of_mem_erase hj', by rintro rfl; exact (hdq i).2 hj'i.symm, hj'i⟩
  rcases lt_trichotomy s' (D t).s with hlt | heq | hlt
  · have hV : ¬ (E.st t' (E.σ t')).U ≤ (D t).V := fun h => by have := le_at h (val last); omega
    obtain ⟨d, hdinj, hd⟩ := E.lemma5 hT' (D t).total hlt.le hV
    obtain ⟨i, j', hj'l, -, hj'i⟩ := pick d hdinj (fun i => ⟨(hd i).1, (hd i).2.1⟩)
    have h1 : (E.st t' (E.σ t')).U ≤ (D j').V := (hd i).2.2.1.trans (hj'i ▸ (D j').U_le _)
    have h2 := (D j').gap (val last) (fun h => hj'l (hval h).symm)
    have h3 := htmax j' (Finset.mem_erase.2 ⟨hj'l, Finset.mem_univ _⟩)
    have := le_at h1 (val last)
    omega
  · have h1 := hT'.1 0
    rw [heq, (D t).total.1 0] at h1
    exact hqne t htl (Option.some.inj (congrArg Prod.snd h1)).symm
  · have hV : ¬ (D t).V ≤ (E.st t' (E.σ t')).U := fun h => by
      have := le_at h (val t); have := hWmax (val t); omega
    obtain ⟨d, hdinj, hd⟩ := E.lemma5 (D t).total hT' hlt.le hV
    obtain ⟨i, j', hj'l, hj't, hj'i⟩ := pick d hdinj (fun i => ⟨(hd i).2.1, (hd i).1⟩)
    have h1 : (D t).V ≤ (D j').V := (hd i).2.2.1.trans (hj'i ▸ (D j').U_le _)
    have h2 := (D j').gap (val t) (fun h => hj't (hval h).symm)
    have h3 := htmax j' (Finset.mem_erase.2 ⟨hj'l, Finset.mem_univ _⟩)
    have := le_at h1 (val t)
    omega

/-- A finite execution is a prefix of an infinite one. -/
lemma run_eq_cfg (α : List P) (h : ∀ i (hi : i < α.length), α[i] = E.σ i) :
    run (initCfg (alg P m N) E.x) α = E.cfg α.length := by
  induction α using List.reverseRecOn with
  | nil => rfl
  | append_singleton α p ih =>
    rw [run_concat, ih (fun i hi => by
      have := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at this)]
    have := h α.length (by simp)
    simp only [List.getElem_concat_length] at this
    rw [List.length_append, List.length_singleton, this]
    rfl

end Sched

end Agree

open Agree

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

/-- **Lemma 6** of [Ovens, PODC 2022] (k-agreement): if there are at most `N + k` processes
(the paper: `N = n − k` swap objects) and `k ≥ 1`, then in every execution of Algorithm 1 at
most `k` distinct values are decided. -/
theorem lemma6_agreement [Fintype P] {k : ℕ} (hk : 1 ≤ k) (hN : Fintype.card P ≤ N + k)
    (x : P → Fin m) (α : List P) :
    (run (initCfg (alg P m N) x) α).decSet.encard ≤ k := by
  classical
  rcases α with _ | ⟨p0, α'⟩
  · have : (initCfg (alg P m N) x).decSet = ∅ := by
      ext v
      simp only [Cfg.decSet, out_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_exists]
      intro p h
      cases h
    rw [run_nil, this, Set.encard_empty]
    exact zero_le
  let E : Sched P m N := ⟨x, fun t => (p0 :: α').getD t p0⟩
  have hrun : run (initCfg (alg P m N) x) (p0 :: α') = E.cfg (p0 :: α').length :=
    E.run_eq_cfg (p0 :: α') (fun i hi => by simp only [E, List.getD_eq_getElem _ _ hi])
  rw [hrun]
  by_contra hcon
  rw [not_le] at hcon
  have hfin : (E.cfg (p0 :: α').length).decSet.Finite := Set.toFinite _
  have hcard : k + 1 ≤ hfin.toFinset.card := by
    rw [Set.Finite.encard_eq_coe_toFinset_card] at hcon
    exact_mod_cast Order.add_one_le_of_lt hcon
  obtain ⟨X, hXS, hXcard⟩ := Finset.exists_subset_card_eq hcard
  have hD : ∀ j : X, Nonempty (E.DecData j.1) := by
    intro j
    obtain ⟨q, hq⟩ := hfin.mem_toFinset.1 (hXS j.2)
    exact ⟨E.decData ((out_iff _ _ _).1 hq)⟩
  exact E.not_decData hN hk (by simp [hXcard]) (fun j : X => j.1) Subtype.val_injective
    (fun j => (hD j).some)

/-- The hypothesis `1 ≤ k` of `lemma6_agreement` is necessary: for `k = 0` (one process, one
object, `m = 1`) a process running solo decides after two steps. -/
example : ¬ (run (initCfg (alg Unit 1 1) (fun _ => 0)) [(), ()]).decSet.encard ≤ 0 := by
  have : (0 : Fin 1) ∈ (run (initCfg (alg Unit 1 1) (fun _ => 0)) [(), ()]).decSet := by
    refine ⟨(), (out_iff _ _ _).2 ?_⟩
    decide
  intro h
  rw [nonpos_iff_eq_zero, Set.encard_eq_zero] at h
  rw [h] at this
  exact this

/-- Observation 4 of the paper (`V[x] ≥ 2` for the decided value `x`) fails for `m = 1`: the
only value is decided with lap counter `1`. (It holds for `m ≥ 2`; Lemma 6 only needs it when at
least two values are decided, where it follows from the condition on line 16.) -/
example : (Agree.ls (run (initCfg (alg Unit 1 1) (fun _ => 0)) [(), ()]) ()).dec = some 0 ∧
    (Agree.ls (run (initCfg (alg Unit 1 1) (fun _ => 0)) [(), ()]) ()).U 0 = 1 := by
  decide

end ConsensusFromSwap.Alg1
