import Papers.PODC2015.KAtomicityVerification.Characterization

/-!
# Section 5: the configuration-graph-search algorithm CGS

Golab, Li, López-Ortiz, Nishimura, *Computing k-Atomicity in Polynomial Time*,
SIAM J. Comput. 47(2), 2018, Section 5.

* Definition 5.1: the write concurrency `m = H.writeConcurrency`;
* Definition 5.2: `(m, k)`-configurations `H.IsConfig k C` (lists of `max m k` values);
* Definition 5.3: `Extends H C C'` (the edges of the configuration graph `G_C`);
* Definition 5.4: the sequence `induced P` of values induced by a path `P` of `G_C`;
* Algorithm 3: `H.CGS k` (the output YES as a proposition);
* Lemma 5.5, Corollary 5.6, Lemma 5.7, Theorem 5.8 (correctness of CGS);
* Lemma 5.9, Lemma 5.10 (size of `G_C`).

A path of `G_C` is a nonempty list of configurations, consecutive ones related by `Extends`
(`H.IsPath k P`); its number of edges is `P.length - 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.KAtomicityVerification

open Finset

variable {V R : Type*} [Fintype V] [DecidableEq V]

namespace History

variable (H : History V R)

/-! ### Definitions -/

open Classical in
/-- The writes overlapping `w(v)` (neither happens before the other), including `w(v)` itself. -/
noncomputable def overlap (v : V) : Finset V :=
  univ.filter (fun u => ¬ H.EW u v ∧ ¬ H.EW v u)

/-- Definition 5.1: the write concurrency of `H` is the maximum number of writes that any one
write overlaps with (not necessarily at a common point), including itself. -/
noncomputable def writeConcurrency : ℕ := univ.sup (fun v => (H.overlap v).card)

/-- Definition 5.2: an `(m, k)`-configuration (`m` = the write concurrency of `H`) is a sequence
`C = v₁ … v_ℓ` of `ℓ = max(m, k)` values such that
(a) `C` is a contiguous subsequence of some topological ordering of `G_W`;
(b) if `(vᵢ, vⱼ) ∈ E_R` with both values in `C`, then `j > i - k` (stated as `i < j + k`);
(c) if `(v, v') ∈ E_R` where `v` is the last value of `C` and `v' ∉ C`, then `C` contains a
value `v''` with `(v'', v') ∈ E_W`. -/
structure IsConfig (k : ℕ) (C : List V) : Prop where
  length : C.length = max H.writeConcurrency k
  topo : ∃ T, H.IsTopoOrder T ∧ C <:+: T
  back : ∀ (i j : ℕ) (hi : i < C.length) (hj : j < C.length), H.ER C[i] C[j] → i < j + k
  last : ∀ v v', C.getLast? = some v → H.ER v v' → v' ∉ C → ∃ v'' ∈ C, H.EW v'' v'

/-- Definition 5.3: `C'` extends `C` iff `C'` is obtained from `C` by removing the first value `v`
and appending a value `v' ≠ v` with `(v', v) ∉ E_W`. -/
def Extends (C C' : List V) : Prop :=
  ∃ v v' t, C = v :: t ∧ C' = t ++ [v'] ∧ v' ≠ v ∧ ¬ H.EW v' v

/-- A (finite, nonempty) path `P = C₁, …, C_ℓ` in the configuration graph `G_C`: every `Cᵢ` is a
configuration and `Cᵢ₊₁` extends `Cᵢ`. It has `ℓ - 1` edges. -/
structure IsPath (k : ℕ) (P : List (List V)) : Prop where
  ne_nil : P ≠ []
  config : ∀ C ∈ P, H.IsConfig k C
  chain : P.IsChain H.Extends

end History

/-- Definition 5.4: the sequence of values induced by a path `C₁, …, C_ℓ`: `C₁` followed by the
last values of `C₂, …, C_ℓ`. -/
def induced : List (List V) → List V
  | [] => []
  | C :: P => C ++ P.filterMap List.getLast?

namespace History

variable (H : History V R)

open Classical in
/-- Algorithm 3 (CGS), as the proposition "CGS outputs YES on input `(H, k)`":
line 3: if `|V| ≤ k` answer YES; line 5: else if some `v` has at least `k` values `v'` with
`(v', v) ∈ E_W` and `(v, v') ∈ E_R` answer NO; lines 8–15: else answer YES iff the configuration
graph `G_C` is nonempty and contains a path with `|V| - max(m, k)` edges. -/
def CGS (k : ℕ) : Prop :=
  if Fintype.card V ≤ k then True
  else if ∃ v : V, k ≤ (univ.filter (fun v' => H.EW v' v ∧ H.ER v v')).card then False
  else (∃ C, H.IsConfig k C) ∧
    ∃ P, H.IsPath k P ∧ P.length - 1 = Fintype.card V - max H.writeConcurrency k

/-! ### Write concurrency -/

variable {H}

lemma mem_overlap {u v : V} : u ∈ H.overlap v ↔ ¬ H.EW u v ∧ ¬ H.EW v u := by
  classical
  simp [overlap]

lemma self_mem_overlap (v : V) : v ∈ H.overlap v := mem_overlap.2 ⟨EW_irrefl v, EW_irrefl v⟩

lemma card_overlap_le (v : V) : (H.overlap v).card ≤ H.writeConcurrency :=
  Finset.le_sup (f := fun v => (H.overlap v).card) (mem_univ v)

lemma writeConcurrency_le_card : H.writeConcurrency ≤ Fintype.card V :=
  Finset.sup_le fun _ _ => card_le_univ _

lemma one_le_writeConcurrency (v : V) : 1 ≤ H.writeConcurrency :=
  le_trans (Finset.card_pos.2 ⟨v, self_mem_overlap v⟩) (card_overlap_le v)

/-- The key consequence of Definition 5.1: a value outside a set of at least `m` values is
ordered by `<_H` with respect to one of them. -/
lemma exists_EW_of_le_length {l : List V} (hl : l.Nodup) (hm : H.writeConcurrency ≤ l.length)
    {u : V} (hu : u ∉ l) : ∃ c ∈ l, H.EW c u ∨ H.EW u c := by
  by_contra h
  push Not at h
  have hsub : insert u l.toFinset ⊆ H.overlap u := by
    intro x hx
    rw [mem_insert, List.mem_toFinset] at hx
    rcases hx with rfl | hx
    · exact self_mem_overlap x
    · exact mem_overlap.2 (h x hx)
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simpa using hu), List.toFinset_card_of_nodup hl] at this
  have := card_overlap_le (H := H) u
  omega

/-! ### Configurations and induced sequences -/

variable {k : ℕ}

/-- A sequence without repetitions and without `G_W` inversions (no later value happens before an
earlier one). -/
def Good (H : History V R) (S : List V) : Prop := S.Pairwise (fun a b => a ≠ b ∧ ¬ H.EW b a)

lemma IsTopoOrder.good {T : List V} (hT : H.IsTopoOrder T) : H.Good T := by
  unfold Good
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (List.Nodup.getElem_inj_iff hT.nodup).1 h; omega
  · have := hT.topo j i hj hi h; omega

lemma IsConfig.good {C : List V} (hC : H.IsConfig k C) : H.Good C := by
  obtain ⟨T, hT, hCT⟩ := hC.topo
  exact List.Pairwise.sublist hCT.sublist hT.good

lemma IsConfig.nodup {C : List V} (hC : H.IsConfig k C) : C.Nodup :=
  List.Pairwise.imp (fun h => h.1) hC.good

lemma induced_cons_cons {C C' : List V} (P : List (List V)) {v v' : V} {t : List V}
    (hC : C = v :: t) (hC' : C' = t ++ [v']) :
    induced (C :: C' :: P) = v :: induced (C' :: P) := by
  subst hC hC'
  simp [induced]

lemma mem_induced {P : List (List V)} (hP : P.IsChain H.Extends) {D : List V} (hD : D ∈ P)
    {x : V} (hx : x ∈ D) : x ∈ induced P := by
  induction P with
  | nil => simp at hD
  | cons C P ih =>
    rcases List.mem_cons.1 hD with rfl | hD
    · simp [induced, hx]
    · cases P with
      | nil => simp at hD
      | cons C' P =>
        obtain ⟨v, v', t, hC, hC', -, -⟩ := List.isChain_cons_cons.1 hP |>.1
        rw [induced_cons_cons P hC hC']
        exact List.mem_cons_of_mem _ (ih (List.isChain_cons_cons.1 hP).2 hD)

/-- Lemma 5.5 of [Golab–Li–López-Ortiz–Nishimura], core of the proof. The sequence `S` induced
by any finite path of the configuration graph `G_C` is a subsequence of some topological ordering of
`G_W`, in the form the proof establishes: (i) the values of `S` are distinct and (ii) if `vᵢ`
precedes `vⱼ` in `S` then `vⱼ ≮_H vᵢ`. (See `IsPath.exists_topoOrder_sublist` for the literal
statement.) -/
theorem IsPath.good {P : List (List V)} (hP : H.IsPath k P) : H.Good (induced P) := by
  obtain ⟨hne, hcfg, hch⟩ := hP
  induction P with
  | nil => exact absurd rfl hne
  | cons C P ih =>
    cases P with
    | nil => simpa [induced] using (hcfg C (by simp)).good
    | cons C' P =>
      obtain ⟨hext, hch'⟩ := List.isChain_cons_cons.1 hch
      obtain ⟨v, v', t, hC, hC', hne', hEW'⟩ := hext
      have hS' := ih (by simp) (fun D hD => hcfg D (List.mem_cons_of_mem _ hD)) hch'
      have hCg := (hcfg C (by simp)).good
      have hC'c := hcfg C' (by simp)
      rw [induced_cons_cons P hC hC']
      unfold Good
      refine List.Pairwise.cons ?_ hS'
      intro u hu
      have hS'' := hS'
      unfold Good at hS'' hCg
      simp only [induced] at hu hS''
      rw [List.pairwise_append] at hS''
      rw [hC] at hCg
      rw [List.pairwise_cons] at hCg
      rcases List.mem_append.1 hu with hu | hu
      · rw [hC', List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact hCg.1 u hu
        · exact ⟨hne'.symm, hEW'⟩
      · by_contra hbad
        have hbad' : v = u ∨ H.EW u v := by tauto
        have huC' : u ∉ C' := fun h => (hS''.2.2 u h u hu).1 rfl
        obtain ⟨c, hc, hcu⟩ := exists_EW_of_le_length hC'c.nodup
          (by rw [hC'c.length]; exact le_max_left _ _) huC'
        have hcu : H.EW c u := hcu.resolve_right (hS''.2.2 c hc u hu).2
        have hcv : H.EW c v := by
          rcases hbad' with rfl | h
          · exact hcu
          · exact EW_trans hcu h
        rw [hC', List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact (hCg.1 c hc).2 hcv
        · exact hEW' hcv

lemma IsPath.length_induced {P : List (List V)} (hP : H.IsPath k P) :
    (induced P).length = max H.writeConcurrency k + (P.length - 1) := by
  obtain ⟨hne, hcfg, hch⟩ := hP
  induction P with
  | nil => exact absurd rfl hne
  | cons C P ih =>
    cases P with
    | nil => simp [induced, (hcfg C (by simp)).length]
    | cons C' P =>
      obtain ⟨hext, hch'⟩ := List.isChain_cons_cons.1 hch
      obtain ⟨v, v', t, hC, hC', -, -⟩ := hext
      rw [induced_cons_cons P hC hC', List.length_cons,
        ih (by simp) (fun D hD => hcfg D (List.mem_cons_of_mem _ hD)) hch']
      simp only [List.length_cons]
      omega

/-- **Corollary 5.6** (length bound) of [Golab–Li–López-Ortiz–Nishimura]. Every path of the
configuration graph has at most `n_w - max(m, k)` edges. (The paper assumes `n_w ≥ k`; the bound
holds without it, in truncated subtraction, since then `G_C` has no vertices.) -/
theorem IsPath.length_sub_one_le {P : List (List V)} (hP : H.IsPath k P) :
    P.length - 1 ≤ Fintype.card V - max H.writeConcurrency k := by
  have h1 := hP.length_induced
  have h2 := List.Nodup.length_le_card
    (List.Pairwise.imp (fun h => h.1) hP.good : (induced P).Nodup)
  omega

lemma prefix_induced {C : List V} (P : List (List V)) : C <+: induced (C :: P) := by
  simp [induced]

lemma getLast_suffix_induced {P : List (List V)} (hP : P.IsChain H.Extends) (hne : P ≠ []) :
    P.getLast hne <:+ induced P := by
  induction P with
  | nil => exact absurd rfl hne
  | cons C P ih =>
    cases P with
    | nil => simp [induced]
    | cons C' P =>
      obtain ⟨hext, hch'⟩ := List.isChain_cons_cons.1 hP
      obtain ⟨v, v', t, hC, hC', -, -⟩ := hext
      rw [induced_cons_cons P hC hC', List.getLast_cons (by simp)]
      exact (ih hch' (by simp)).trans (List.suffix_cons _ _)

/-- **Corollary 5.6** (acyclicity) of [Golab–Li–López-Ortiz–Nishimura]. The configuration graph
`G_C` is acyclic: no path with at least one edge starts and ends at the same configuration. -/
theorem IsPath.head_ne_getLast {P : List (List V)} (hP : H.IsPath k P) (h2 : 2 ≤ P.length) :
    P.head hP.ne_nil ≠ P.getLast hP.ne_nil := by
  intro heq
  have hg := hP.good
  obtain ⟨hne, hcfg, hch⟩ := hP
  rcases P with _ | ⟨C, _ | ⟨C', P⟩⟩
  · simp at h2
  · simp at h2
  · obtain ⟨hext, hch'⟩ := List.isChain_cons_cons.1 hch
    obtain ⟨v, v', t, hC, hC', -, -⟩ := hext
    have hsuf := getLast_suffix_induced hch' (by simp)
    rw [List.getLast_cons (by simp)] at heq
    simp only [List.head_cons] at heq
    rw [← heq, hC] at hsuf
    unfold Good at hg
    rw [induced_cons_cons P hC hC', List.pairwise_cons] at hg
    exact (hg.1 v (hsuf.subset (by simp))).1 rfl

/-! ### Backward `G_R` edges along a sequence -/

/-- Every `G_R` edge `(x, v)` from a later value `x` to an earlier value `v` of the sequence reaches
back by fewer than `k` positions. -/
def BackOK (H : History V R) (k : ℕ) : List V → Prop
  | [] => True
  | v :: S => (∀ x ∈ S.drop (k - 1), ¬ H.ER x v) ∧ BackOK H k S

lemma backOK_iff (hk : 0 < k) {S : List V} :
    H.BackOK k S ↔
      ∀ (i j : ℕ) (hi : i < S.length) (hj : j < S.length), H.ER S[i] S[j] → i < j + k := by
  induction S with
  | nil => simp [BackOK]
  | cons v S ih =>
    simp only [BackOK, ih]
    constructor
    · rintro ⟨h0, h⟩ i j hi hj hij
      rcases i with _ | i
      · omega
      rcases j with _ | j
      · by_contra hik
        have hi' : i < S.length := by simpa using hi
        apply h0 (S[i]'hi') _ (by simpa using hij)
        rw [List.mem_iff_getElem]
        exact ⟨i - (k - 1), by simp; omega, by simp; congr 1; omega⟩
      · have := h i j (by simpa using hi) (by simpa using hj) hij
        omega
    · intro h
      refine ⟨fun x hx hxv => ?_, fun i j hi hj hij => ?_⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
        simp only [List.length_drop, List.getElem_drop] at hp hxv
        have := h (k - 1 + p + 1) 0 (by simp; omega) (by simp) (by simpa using hxv)
        omega
      · have := h (i + 1) (j + 1) (by simpa using hi) (by simpa using hj) (by simpa using hij)
        omega

/-- The induced sequence of every path has all backward `G_R` edges shorter than `k` (the second
half of the proof of Lemma 5.7). -/
theorem IsPath.backOK (hk : 0 < k) {P : List (List V)} (hP : H.IsPath k P) :
    H.BackOK k (induced P) := by
  obtain ⟨hne, hcfg, hch⟩ := hP
  induction P with
  | nil => exact absurd rfl hne
  | cons C P ih =>
    cases P with
    | nil => simpa [induced, backOK_iff hk] using (hcfg C (by simp)).back
    | cons C' P =>
      obtain ⟨hext, hch'⟩ := List.isChain_cons_cons.1 hch
      obtain ⟨v, v', t, hC, hC', hne', hEW'⟩ := hext
      have hCc := hcfg C (by simp)
      have hg' : H.Good (induced (C :: C' :: P)) := IsPath.good ⟨hne, hcfg, hch⟩
      unfold Good at hg'
      rw [induced_cons_cons P hC hC', List.pairwise_cons] at hg'
      rw [induced_cons_cons P hC hC']
      refine ⟨fun x hx hxv => ?_, ih (by simp) (fun D hD => hcfg D (List.mem_cons_of_mem _ hD))
        hch'⟩
      have htl : t.length = max H.writeConcurrency k - 1 := by
        have := hCc.length; rw [hC] at this; simp at this; omega
      have hS' : induced (C' :: P) = t ++ (C' :: P).filterMap List.getLast? := by
        simp [induced, hC']
      rw [hS', List.drop_append_of_le_length (by omega), List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
        simp only [List.length_drop, List.getElem_drop] at hp hxv
        have := hCc.back (k - 1 + p + 1) 0 (by rw [hC]; simp; omega) (by rw [hC]; simp)
          (by simpa [hC] using hxv)
        omega
      · obtain ⟨D, hD, hDx⟩ := List.mem_filterMap.1 hx
        have hDc := hcfg D (List.mem_cons_of_mem _ hD)
        have hDS : ∀ y ∈ D, y ∈ induced (C' :: P) := fun y hy => mem_induced hch' hD hy
        have hvD : v ∉ D := fun h => (hg'.1 v (hDS v h)).1 rfl
        obtain ⟨c, hc, hcv⟩ := hDc.last x v hDx hxv hvD
        exact (hg'.1 c (hDS c hc)).2 hcv

/-- A path with `|V| - max(m, k)` edges induces a `k`-atomic value order (Lemma 5.7, "if"). -/
theorem IsPath.isKAtomicValueOrder (hk : 0 < k) {P : List (List V)} (hP : H.IsPath k P)
    (hlen : P.length - 1 = Fintype.card V - max H.writeConcurrency k)
    (hn : k ≤ Fintype.card V) : H.IsKAtomicValueOrder k (induced P) := by
  have hg := hP.good
  have hb := (backOK_iff hk).1 (hP.backOK hk)
  have hl := hP.length_induced
  have hm := writeConcurrency_le_card (H := H)
  have hnd : (induced P).Nodup := List.Pairwise.imp (fun h => h.1) hg
  have hlen' : (induced P).length = Fintype.card V := by
    rw [hl, hlen]; omega
  have hcomp : ∀ v, v ∈ induced P := by
    have : (induced P).toFinset = univ := Finset.eq_univ_of_card _
      (by rw [List.toFinset_card_of_nodup hnd, hlen'])
    intro v
    rw [← List.mem_toFinset, this]
    exact mem_univ v
  refine ⟨hnd, hcomp, fun i j hi hj hij => ?_, hb⟩
  unfold Good at hg
  rw [List.pairwise_iff_getElem] at hg
  by_contra hji
  rcases (not_lt.1 hji).lt_or_eq with h | h
  · exact (hg j i hj hi h).2 hij
  · subst h; exact EW_irrefl _ hij

lemma IsKAtomicValueOrder.length_eq {T : List V} (hT : H.IsKAtomicValueOrder k T) :
    T.length = Fintype.card V := by
  rw [← List.toFinset_card_of_nodup hT.nodup, ← Finset.card_univ]
  congr 1
  ext v
  simp [hT.complete v]

lemma IsKAtomicValueOrder.isTopoOrder {T : List V} (hT : H.IsKAtomicValueOrder k T) :
    H.IsTopoOrder T := ⟨hT.nodup, hT.complete, hT.topo⟩

/-- The windows `v_ℓ, …, v_{ℓ + max(m,k) - 1}` of a `k`-atomic value order are configurations
(Lemma 5.7, "only if"). -/
lemma IsKAtomicValueOrder.window_isConfig {T : List V} (hT : H.IsKAtomicValueOrder k T) {ℓ : ℕ}
    (hℓ : ℓ + max H.writeConcurrency k ≤ Fintype.card V) :
    H.IsConfig k ((T.drop ℓ).take (max H.writeConcurrency k)) := by
  set L := max H.writeConcurrency k with hL
  have hTl := hT.length_eq
  have hmL : H.writeConcurrency ≤ L := le_max_left _ _
  have hkL : k ≤ L := le_max_right _ _
  set C := (T.drop ℓ).take L with hCdef
  have hCl : C.length = L := by simp [C]; omega
  have hCget : ∀ i (hi : i < C.length), C[i] = T[ℓ + i]'(by omega) := by
    intro i hi; simp [C]
  refine ⟨hCl, ⟨T, hT.isTopoOrder, (List.take_prefix _ _).isInfix.trans
    (List.drop_suffix _ _).isInfix⟩, fun i j hi hj h => ?_, fun x v' hx hER hv' => ?_⟩
  · rw [hCget, hCget] at h
    have := hT.back (ℓ + i) (ℓ + j) _ _ h
    omega
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at hx
    obtain ⟨hxl, rfl⟩ := hx
    rw [hCget] at hER
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (hT.complete v')
    have hb := hT.back _ j _ hj hER
    have hjL : ℓ + L ≤ j := by
      by_contra hjL
      apply hv'
      rw [List.mem_iff_getElem]
      exact ⟨j - ℓ, by omega, by rw [hCget]; congr 1; omega⟩
    have hCnd : C.Nodup := hT.nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    obtain ⟨c, hc, hcv⟩ := exists_EW_of_le_length (H := H) hCnd (by omega) hv'
    refine ⟨c, hc, hcv.resolve_right fun h => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    rw [hCget] at h
    have := hT.topo _ _ _ _ h
    omega

/-- A `k`-atomic value order yields a path with `|V| - max(m, k)` edges in `G_C` (Lemma 5.7,
"only if"). -/
lemma IsKAtomicValueOrder.exists_path {T : List V} (hT : H.IsKAtomicValueOrder k T)
    (hk : 0 < k) (hn : k ≤ Fintype.card V) :
    ∃ P, H.IsPath k P ∧ P.length - 1 = Fintype.card V - max H.writeConcurrency k := by
  set L := max H.writeConcurrency k with hL
  have hTl := hT.length_eq
  have hm := writeConcurrency_le_card (H := H)
  have hLn : L ≤ Fintype.card V := max_le hm hn
  have hkL : k ≤ L := le_max_right _ _
  refine ⟨(List.range (Fintype.card V - L + 1)).map (fun ℓ => (T.drop ℓ).take L),
    ⟨by simp, ?_, ?_⟩, by simp⟩
  · intro C hC
    simp only [List.mem_map, List.mem_range] at hC
    obtain ⟨ℓ, hℓ, rfl⟩ := hC
    exact hT.window_isConfig (by omega)
  · rw [List.isChain_map, List.isChain_range_succ]
    intro ℓ hℓ
    refine ⟨T[ℓ]'(by omega), T[ℓ + L]'(by omega), (T.drop (ℓ + 1)).take (L - 1), ?_, ?_, ?_, ?_⟩
    · rw [List.drop_eq_getElem_cons (by omega)]
      obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      rw [hL', List.take_succ_cons]
      simp
    · obtain ⟨L', hL'⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      have hT' : T[ℓ + L]'(by omega) = T[ℓ + 1 + L']'(by omega) := by congr 1; omega
      rw [hT', hL', Nat.add_sub_cancel, List.take_add_one, List.getElem?_drop,
        List.getElem?_eq_getElem (by omega)]
      simp
    · intro h
      have := (List.Nodup.getElem_inj_iff hT.nodup).1 h
      omega
    · intro h
      have := hT.topo _ _ _ _ h
      omega

/-- **Lemma 5.7** of [Golab–Li–López-Ortiz–Nishimura]. Suppose (Assumption 3.4 and) `H` has
`n_w ≥ k ≥ 1` writes. Then `H` is `k`-atomic iff the configuration graph `G_C` is nonempty and
has a path with exactly `n_w - max(m, k)` edges. -/
theorem kAtomic_iff_exists_path [Fintype R] (hA : H.Assumption34) (hk : 0 < k)
    (hn : k ≤ Fintype.card V) :
    H.KAtomic k ↔ (∃ C, H.IsConfig k C) ∧
      ∃ P, H.IsPath k P ∧ P.length - 1 = Fintype.card V - max H.writeConcurrency k := by
  rw [kAtomic_iff_exists_valueOrder hA hk]
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨P, hP, hlen⟩ := hT.exists_path hk hn
    obtain ⟨C, hC⟩ := List.exists_mem_of_ne_nil P hP.ne_nil
    exact ⟨⟨C, hP.config C hC⟩, P, hP, hlen⟩
  · rintro ⟨-, P, hP, hlen⟩
    exact ⟨_, hP.isKAtomicValueOrder hk hlen hn⟩

/-- **Theorem 5.8** of [Golab–Li–López-Ortiz–Nishimura]. Under Assumption 3.4 and for `k ≥ 1`,
algorithm CGS (Algorithm 3) returns YES iff `H` is `k`-atomic. -/
theorem cgs_iff_kAtomic [Fintype R] (hA : H.Assumption34) (hk : 0 < k) :
    H.CGS k ↔ H.KAtomic k := by
  classical
  unfold CGS
  split_ifs with h1 h2
  · -- line 4: `|V| ≤ k`, any topological ordering of `G_W` works
    simp only [true_iff]
    rw [kAtomic_iff_exists_valueOrder hA hk]
    obtain ⟨T, hT⟩ := exists_topoOrder (H := H)
    refine ⟨T, hT.nodup, hT.complete, hT.topo, fun i j hi hj _ => ?_⟩
    have : T.length ≤ Fintype.card V := hT.nodup.length_le_card
    omega
  · -- line 6: `k` backward `G_R` edges out of `v` cannot all be shorter than `k`
    simp only [false_iff]
    rw [kAtomic_iff_exists_valueOrder hA hk, exists_valueOrder_iff_rank]
    rintro ⟨p, hinj, hEW, hER⟩
    obtain ⟨v, hv⟩ := h2
    have hsub := Finset.card_le_card_of_injOn (s := univ.filter fun v' => H.EW v' v ∧ H.ER v v')
      (t := Finset.Ico (p v + 1 - k) (p v)) p
      (fun v' hv' => by
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv'
        have h1 := hEW _ _ hv'.1
        have h2 := hER _ _ hv'.2
        simp only [coe_Ico, Set.mem_Ico]
        omega) hinj.injOn
    simp only [Nat.card_Ico] at hsub
    omega
  · exact (kAtomic_iff_exists_path hA hk (by omega)).symm

/-! ### Size of the configuration graph (Lemmas 5.9 and 5.10) -/

variable (H) in
open Classical in
/-- The values that can immediately follow `v` in some topological ordering of `G_W`
(the set `Succ(v)` of the proof of Theorem 5.11). -/
noncomputable def succSet (v : V) : Finset V :=
  univ.filter fun u => ∃ T, H.IsTopoOrder T ∧ [v, u] <:+: T

lemma mem_succSet {u v : V} : u ∈ H.succSet v ↔ ∃ T, H.IsTopoOrder T ∧ [v, u] <:+: T := by
  classical
  simp [succSet]

lemma exists_getElem_of_pair_infix {T : List V} {a b : V} (h : [a, b] <:+: T) :
    ∃ i, ∃ hi : i + 1 < T.length, T[i] = a ∧ T[i + 1] = b := by
  obtain ⟨s, t, rfl⟩ := h
  refine ⟨s.length, by simp, ?_, ?_⟩
  · simp [List.getElem_append_right]
  · rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
    simp

lemma ne_and_not_EW_of_mem_succSet {u v : V} (h : u ∈ H.succSet v) : u ≠ v ∧ ¬ H.EW u v := by
  obtain ⟨T, hT, hvu⟩ := mem_succSet.1 h
  have := List.Pairwise.sublist hvu.sublist hT.good
  simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true] at this
  exact ⟨this.1.symm, this.2⟩

lemma isChain_pair_infix : ∀ l : List V, l.IsChain (fun x y => [x, y] <:+: l)
  | [] => .nil
  | [a] => .singleton a
  | a :: b :: l => by
    rw [List.isChain_cons_cons]
    refine ⟨(List.prefix_append [a, b] l).isInfix, ?_⟩
    exact (isChain_pair_infix (b :: l)).imp fun _ _ h => h.trans (List.suffix_cons _ _).isInfix

/-- Consecutive values of a configuration are related by `succSet`. -/
lemma IsConfig.isChain_succSet {C : List V} (hC : H.IsConfig k C) :
    C.IsChain (fun x y => y ∈ H.succSet x) := by
  obtain ⟨T, hT, hCT⟩ := hC.topo
  exact (isChain_pair_infix C).imp fun _ _ h => mem_succSet.2 ⟨T, hT, h.trans hCT⟩

open Classical in
/-- In the proof of Lemma 5.9: the successors of `v` overlapping `w(v)` (the set `W₁`) are at most
`m - 1`. -/
lemma card_succSet_concurrent_le (v : V) :
    ((H.succSet v).filter fun u => ¬ H.EW v u).card ≤ H.writeConcurrency - 1 := by
  have hsub : (H.succSet v).filter (fun u => ¬ H.EW v u) ⊆ (H.overlap v).erase v := by
    intro u hu
    rw [mem_filter] at hu
    have := ne_and_not_EW_of_mem_succSet hu.1
    exact mem_erase.2 ⟨this.1, mem_overlap.2 ⟨this.2, hu.2⟩⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (self_mem_overlap v)] at this
  have := card_overlap_le (H := H) v
  omega

open Classical in
/-- In the proof of Lemma 5.9: the successors `u` of `v` with `w(v) <_H w(u)` (the set `W₂`) are
at most `m`, since no two of them are ordered by `<_H`. -/
lemma card_succSet_after_le (v : V) :
    ((H.succSet v).filter fun u => H.EW v u).card ≤ H.writeConcurrency := by
  rcases Finset.eq_empty_or_nonempty ((H.succSet v).filter fun u => H.EW v u) with h | ⟨x, hx⟩
  · rw [h]; simp
  have key : ∀ x ∈ (H.succSet v).filter (fun u => H.EW v u),
      ∀ y ∈ (H.succSet v).filter (fun u => H.EW v u), ¬ H.EW x y := by
    intro x hx y hy hxy
    rw [mem_filter] at hx hy
    obtain ⟨T, hT, hvy⟩ := mem_succSet.1 hy.1
    obtain ⟨i, hi, hTi, hTi'⟩ := exists_getElem_of_pair_infix hvy
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 (hT.complete x)
    have h1 := hT.topo i p hi.le hp (by rw [hTi]; exact hx.2)
    have h2 := hT.topo p (i + 1) hp hi (by rw [hTi']; exact hxy)
    omega
  refine le_trans (card_le_card fun y hy => mem_overlap.2 ⟨key y hy x hx, key x hx y hy⟩)
    (card_overlap_le x)

/-- **Lemma 5.9** of [Golab–Li–López-Ortiz–Nishimura]. A value `v` can be immediately followed
in a topological ordering of `G_W` (in particular, in a configuration) by at most `2m - 1`
values: at most `m - 1` overlapping `w(v)` and at most `m` after `w(v)`. -/
theorem card_succSet_le (v : V) : (H.succSet v).card ≤ 2 * H.writeConcurrency - 1 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := H.succSet v) (fun u => H.EW v u)
  have h1 := card_succSet_concurrent_le (H := H) v
  have h2 := card_succSet_after_le (H := H) v
  have h3 := one_le_writeConcurrency (H := H) v
  omega

open Classical in
/-- **Lemma 5.9** of [Golab–Li–López-Ortiz–Nishimura], as stated: for a fixed value `v`, the
values `u` that can follow `v` immediately in an `(m, k)`-configuration are at most `2m - 1`. -/
theorem card_config_successors_le (v : V) :
    (univ.filter fun u => ∃ C, H.IsConfig k C ∧ [v, u] <:+: C).card
      ≤ 2 * H.writeConcurrency - 1 := by
  classical
  refine le_trans (card_le_card fun u hu => ?_) (card_succSet_le v)
  simp only [mem_filter, mem_univ, true_and] at hu
  obtain ⟨C, hC, hvu⟩ := hu
  obtain ⟨T, hT, hCT⟩ := hC.topo
  exact mem_succSet.2 ⟨T, hT, hvu.trans hCT⟩

/-- Counting lists of length `n + 1` in which each element is followed by one of at most `b`
successors. -/
lemma card_le_of_isChain (F : V → Finset V) (b : ℕ) (hF : ∀ v, (F v).card ≤ b) :
    ∀ (n : ℕ) (S : Finset (List V)),
      (∀ l ∈ S, l.length = n + 1 ∧ l.IsChain (fun x y => y ∈ F x)) →
        S.card ≤ Fintype.card V * b ^ n := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have := Finset.card_le_card_of_injOn (s := S)
      (t := (univ : Finset V).map ⟨some, Option.some_injective _⟩)
      List.head? (fun l hl => by
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (hS l hl).1
        simp) (fun l₁ hl₁ l₂ hl₂ h => by
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (hS l₁ hl₁).1
        obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 (hS l₂ hl₂).1
        simpa using h)
    simpa using this
  | succ n ih =>
    intro S hS
    have himg : (S.image List.dropLast).card ≤ Fintype.card V * b ^ n := by
      apply ih
      intro l hl
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 hl
      refine ⟨by simp [(hS l' hl').1], (hS l' hl').2.infix (List.dropLast_prefix l').isInfix⟩
    have hfib : ∀ a ∈ S.image List.dropLast, (S.filter fun l => l.dropLast = a).card ≤ b := by
      intro a ha
      obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 ha
      have hne : l₀.dropLast ≠ [] := by
        intro h; have := congrArg List.length h; simp [(hS l₀ hl₀).1] at this
      refine le_trans (Finset.card_le_card_of_injOn (t := (F (l₀.dropLast.getLast hne)).map
          ⟨some, Option.some_injective _⟩) List.getLast? (fun l hl => ?_)
          (fun l₁ hl₁ l₂ hl₂ h => ?_))
          (by simpa using hF _)
      · rw [Finset.mem_coe, Finset.mem_filter] at hl
        have hlne : l ≠ [] := by
          intro h; have := (hS l hl.1).1; simp [h] at this
        have hl' := List.dropLast_append_getLast hlne
        have hch := (hS l hl.1).2
        rw [← hl', List.isChain_append] at hch
        have := hch.2.2 (l.dropLast.getLast (by rw [hl.2]; exact hne))
          (List.getLast?_eq_some_getLast _)
          (l.getLast hlne) (by simp)
        rw [Finset.mem_coe, Finset.mem_map]
        refine ⟨_, ?_, (List.getLast?_eq_some_getLast hlne).symm⟩
        convert this using 2
        simp [hl.2]
      · rw [Finset.mem_coe, Finset.mem_filter] at hl₁ hl₂
        have h₁ : l₁ ≠ [] := by intro h; have := (hS l₁ hl₁.1).1; simp [h] at this
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (List.getLast?_isSome.2 h₁)
        have e1 := List.dropLast_append_getLast? (l := l₁) y hy
        have e2 := List.dropLast_append_getLast? (l := l₂) y (by rw [← h]; exact hy)
        calc l₁ = l₁.dropLast ++ [y] := e1.symm
          _ = l₂.dropLast ++ [y] := by rw [hl₁.2, hl₂.2]
          _ = l₂ := e2
    have := Finset.card_le_mul_card_image (f := List.dropLast) S b hfib
    calc S.card ≤ b * (S.image List.dropLast).card := this
      _ ≤ b * (Fintype.card V * b ^ n) := Nat.mul_le_mul_left _ himg
      _ = Fintype.card V * b ^ (n + 1) := by ring

lemma card_configs_le' (hL : 0 < max H.writeConcurrency k) (S : Finset (List V))
    (hS : ∀ C ∈ S, H.IsConfig k C) :
    S.card ≤ Fintype.card V * (2 * H.writeConcurrency - 1) ^ (max H.writeConcurrency k - 1) :=
  card_le_of_isChain _ _ card_succSet_le _ S fun C hC =>
    ⟨by rw [(hS C hC).length]; omega, (hS C hC).isChain_succSet⟩

/-- **Lemma 5.10** (vertices) of [Golab–Li–López-Ortiz–Nishimura]. There are at most
`n_w · (2m - 1)^(max(m,k) - 1)` configurations. (We count any finite set of configurations.) -/
theorem card_configs_le (hk : 0 < k) (S : Finset (List V)) (hS : ∀ C ∈ S, H.IsConfig k C) :
    S.card ≤ Fintype.card V * (2 * H.writeConcurrency - 1) ^ (max H.writeConcurrency k - 1) :=
  card_configs_le' (lt_of_lt_of_le hk (le_max_right _ _)) S hS

/-- **Lemma 5.10** (edges) of [Golab–Li–López-Ortiz–Nishimura]. There are at most
`n_w · (2m - 1)^max(m,k)` edges in `G_C`. This needs `max(m, k) ≥ 2` (implied by the paper's
input restriction `k ≥ 2`): for `m = k = 1` the bound fails (a history with `n_w` sequential writes
and no reads has `n_w(n_w - 1)/2` edges). -/
theorem card_edges_le (h2 : 2 ≤ max H.writeConcurrency k) (S : Finset (List V × List V))
    (hS : ∀ e ∈ S, H.IsConfig k e.1 ∧ H.IsConfig k e.2 ∧ H.Extends e.1 e.2) :
    S.card ≤ Fintype.card V * (2 * H.writeConcurrency - 1) ^ max H.writeConcurrency k := by
  set b := 2 * H.writeConcurrency - 1
  set L := max H.writeConcurrency k
  have himg : (S.image Prod.fst).card ≤ Fintype.card V * b ^ (L - 1) :=
    card_configs_le' (by omega) _ fun C hC => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hC
      exact (hS e he).1
  have hfib : ∀ C ∈ S.image Prod.fst, (S.filter fun e => e.1 = C).card ≤ b := by
    intro C hC
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨x, hx⟩ : ∃ x, e₀.1.getLast? = some x := by
      rcases h : e₀.1.getLast? with _ | x
      · have := (hS e₀ he₀).1.length; simp at h; simp [h] at this; omega
      · exact ⟨x, rfl⟩
    have hform : ∀ e ∈ S, e.1 = e₀.1 → ∃ v', e.2 = e₀.1.tail ++ [v'] ∧ v' ∈ H.succSet x := by
      intro e he he1
      obtain ⟨hc1, hc2, v, v', t, hC, hC', -, -⟩ := hS e he
      have ht : t ≠ [] := by
        intro h; have := hc1.length; rw [hC, h] at this; simp at this; omega
      obtain ⟨a, t', rfl⟩ := List.exists_cons_of_ne_nil ht
      rw [← he1, hC] at hx ⊢
      simp only [List.getLast?_cons_cons] at hx
      have hch := hc2.isChain_succSet
      rw [hC', List.isChain_append] at hch
      exact ⟨v', by simp [hC'], hch.2.2 x hx v' (by simp)⟩
    refine le_trans (Finset.card_le_card_of_injOn (t := (H.succSet x).map
        ⟨some, Option.some_injective _⟩) (fun e => e.2.getLast?) (fun e he => ?_)
        (fun e₁ he₁ e₂ he₂ h => ?_)) (by simpa using card_succSet_le x)
    · rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨v', h2, hv'⟩ := hform e he.1 he.2
      simp [h2, hv']
    · rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      obtain ⟨v₁, h₁, -⟩ := hform e₁ he₁.1 he₁.2
      obtain ⟨v₂, h₂, -⟩ := hform e₂ he₂.1 he₂.2
      simp only [h₁, h₂, List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at h
      exact Prod.ext (he₁.2.trans he₂.2.symm) (by rw [h₁, h₂, h])
  have := Finset.card_le_mul_card_image (f := Prod.fst) S b hfib
  calc S.card ≤ b * (S.image Prod.fst).card := this
    _ ≤ b * (Fintype.card V * b ^ (L - 1)) := Nat.mul_le_mul_left _ himg
    _ = Fintype.card V * b ^ L := by
      rw [← mul_assoc, mul_comm b, mul_assoc, ← pow_succ']
      congr 2
      omega

/-! ### Lemma 5.5, literal form: extending a good sequence to a topological ordering -/

/-- Sorting the values by an injective key into a linear order. -/
lemma exists_sorted_list_lt {β : Type*} [LinearOrder β] (p : V → β) (hp : Function.Injective p) :
    ∃ T : List V, (∀ v, v ∈ T) ∧ T.Pairwise (fun a b => p a < p b) := by
  set T := (Finset.univ : Finset V).toList.mergeSort (fun a b => decide (p a ≤ p b))
  have hperm : T.Perm (Finset.univ : Finset V).toList := List.mergeSort_perm _ _
  have hnd : T.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hpw : T.Pairwise (fun a b => decide (p a ≤ p b) = true) := by
    apply List.pairwise_mergeSort
    · intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact hab.trans hbc
    · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _
  refine ⟨T, fun v => hperm.mem_iff.2 (by simp), (hpw.and hnd).imp ?_⟩
  intro a b ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  exact lt_of_le_of_ne h1 fun h => h2 (hp h)

/-- A sequence of distinct values without `G_W` inversions is a subsequence of some topological
ordering of `G_W`. -/
theorem Good.exists_topoOrder_sublist {S : List V} (hS : H.Good S) :
    ∃ T, H.IsTopoOrder T ∧ S.Sublist T := by
  classical
  unfold Good at hS
  have hSpw := List.pairwise_iff_getElem.1 hS
  -- `g v - 1` is the last position of `S` holding `v` or a value that happens before `v`
  let A : V → Finset ℕ := fun v =>
    (Finset.range S.length).filter (fun i => ∃ x ∈ S[i]?, x = v ∨ H.EW x v)
  let g : V → ℕ := fun v => (A v).sup (fun i => i + 1)
  have hA : ∀ v i, i ∈ A v ↔ ∃ hi : i < S.length, S[i] = v ∨ H.EW S[i] v := by
    intro v i
    simp only [A, mem_filter, mem_range]
    constructor
    · rintro ⟨hi, x, hx, h⟩
      rw [List.getElem?_eq_getElem hi, Option.mem_some_iff] at hx
      exact ⟨hi, hx ▸ h⟩
    · rintro ⟨hi, h⟩
      exact ⟨hi, S[i], by simp [hi], h⟩
  have g_ge : ∀ v i (hi : i < S.length), (S[i] = v ∨ H.EW S[i] v) → i + 1 ≤ g v :=
    fun v i hi h => Finset.le_sup (f := (fun i => i + 1)) ((hA v i).2 ⟨hi, h⟩)
  have g_mono : ∀ a b, H.EW a b → g a ≤ g b := by
    intro a b hab
    refine Finset.sup_le fun i hi => ?_
    obtain ⟨hi, h⟩ := (hA a i).1 hi
    refine g_ge b i hi (Or.inr ?_)
    rcases h with h | h
    · rw [h]; exact hab
    · exact EW_trans h hab
  have g_S : ∀ i (hi : i < S.length), g S[i] = i + 1 := by
    intro i hi
    refine le_antisymm (Finset.sup_le fun j hj => ?_) (g_ge _ i hi (Or.inl rfl))
    obtain ⟨hj, h⟩ := (hA _ j).1 hj
    show j + 1 ≤ i + 1
    by_contra hij
    have := hSpw i j hi hj (by omega)
    rcases h with h | h
    · exact this.1 h.symm
    · exact this.2 h
  have g_lt : ∀ a i (hi : i < S.length), H.EW a S[i] → g a < g S[i] := by
    intro a i hi hab
    have hle := g_mono _ _ hab
    rw [g_S i hi] at hle ⊢
    refine lt_of_le_of_ne hle fun heq => ?_
    have hne : (A a).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [g, h] at heq
    obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_sup _ hne (fun i => i + 1)
    obtain ⟨hj, h⟩ := (hA a j).1 hj
    have hji : j = i := by simp only [g] at heq; omega
    subst hji
    rcases h with h | h
    · rw [h] at hab; exact EW_irrefl _ hab
    · exact EW_asymm h hab
  let key : V → ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) := fun v =>
    toLex (g v, toLex (if v ∈ S then 0 else 1, toLex (H.f (.inl v), (Fintype.equivFin V v : ℕ))))
  have hkey : Function.Injective key := by
    intro a b h
    simp only [key, toLex_inj, Prod.mk.injEq] at h
    exact (Fintype.equivFin V).injective (Fin.ext h.2.2.2)
  have hkEW : ∀ a b, H.EW a b → key a < key b := by
    intro a b hab
    simp only [key, Prod.Lex.toLex_lt_toLex]
    rcases (g_mono a b hab).lt_or_eq with h | h
    · exact Or.inl h
    refine Or.inr ⟨h, ?_⟩
    have hb : b ∉ S := by
      intro hb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
      exact absurd h (g_lt a i hi hab).ne
    by_cases ha : a ∈ S
    · simp [ha, hb]
    · refine Or.inr ⟨by simp [ha, hb], Or.inl ?_⟩
      exact lt_trans hab (H.s_lt_f _)
  have hkS : S.Pairwise (fun a b => key a < key b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [key, Prod.Lex.toLex_lt_toLex, g_S i hi, g_S j hj]
    exact Or.inl (by omega)
  obtain ⟨T, hcomp, hT⟩ := exists_sorted_list_lt key hkey
  have hTnd : T.Nodup := hT.imp fun h heq => (heq ▸ h).ne rfl
  have hTpw := List.pairwise_iff_getElem.1 hT
  refine ⟨T, ⟨hTnd, hcomp, fun i j hi hj h => ?_⟩, ?_⟩
  · by_contra hij
    rcases (not_lt.1 hij).lt_or_eq with hji | hji
    · exact absurd (hTpw j i hj hi hji) (not_lt.2 (hkEW _ _ h).le)
    · subst hji; exact EW_irrefl _ h
  · have : Std.Antisymm (fun a b : V => key a < key b) :=
      ⟨fun _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
    exact List.sublist_of_subperm_of_pairwise
      (List.subperm_of_subset (hS.imp fun h => h.1) fun x _ => hcomp x) hkS hT

/-- **Lemma 5.5** of [Golab–Li–López-Ortiz–Nishimura]. For any finite path `P` of the
configuration graph `G_C`, the sequence of values induced by `P` is a subsequence of some
topological ordering of `G_W`. -/
theorem IsPath.exists_topoOrder_sublist {P : List (List V)} (hP : H.IsPath k P) :
    ∃ T, H.IsTopoOrder T ∧ (induced P).Sublist T :=
  hP.good.exists_topoOrder_sublist

end History

end Podc.KAtomicityVerification
