import Papers.PODC2011.TimestampSpace.OneShot

/-!
# Theorem 1.2: facts about the schedule of Lemma 4.1

`SD` bundles the output of Lemma 4.1 applied in a configuration `C` (reached by `α`) with
covered set `R` and the idle processes `U`; `SD.ms` is the schedule as a list of moves
`πc₀ M₀ πc₁ M₁`. We prove the facts about the configurations `cfgAt I C ms t` after `t` moves
that the step of the construction needs.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

variable (I) in
/-- The output of Lemma 4.1 in the construction of Section 4. -/
structure SD (α : List (Label P (tsObj T))) (C : Config (tsObj T) B P L) (R : Finset ι)
    (U : List P) (c₀ c₁ : List (P × ι)) (M₀ M₁ : List (P × List (Label P (tsObj T)))) : Prop where
  run : I.run α = some C
  adm : Adm true α
  Umem : ∀ p, p ∈ U ↔ opsOf α p = []
  Und : U.Nodup
  ccov : ∀ x ∈ c₀ ++ c₁, I.Covers C x.1 x.2 ∧ x.2 ∈ R
  cnd : (c₀.map Prod.fst ++ c₁.map Prod.fst).Nodup
  s₀ : (c₀.map Prod.snd).Nodup
  s₁ : (c₁.map Prod.snd).Nodup
  Mnd : ((M₀ ++ M₁).map Prod.fst).Nodup
  MU : ∀ m ∈ M₀ ++ M₁, m.1 ∈ U
  len : M₀.length + M₁.length + 1 = U.length
  half : U.length / 2 ≤ M₀.length
  own : ∀ m ∈ M₀ ++ M₁, ∀ ℓ ∈ m.2, ℓ.proc = m.1
  cnt : ∀ p, getTSCount (flat (M₀ ++ M₁)) p ≤ ((M₀ ++ M₁).map Prod.fst).count p
  runs : ∃ X, I.runFrom C (bw c₀ ++ flat M₀ ++ bw c₁ ++ flat M₁) = some X
  cov₀ : ∀ M' m M'', M₀ = M' ++ m :: M'' →
    ∃ Y, I.runFrom C (bw c₀ ++ flat (M' ++ [m])) = some Y ∧ ∃ r ∉ (↑R : Set ι), I.Covers Y m.1 r
  cov₁ : ∀ M' m M'', M₁ = M' ++ m :: M'' →
    ∃ Y, I.runFrom C (bw c₀ ++ flat M₀ ++ bw c₁ ++ flat (M' ++ [m])) = some Y ∧
      ∃ r ∉ (↑R : Set ι), I.Covers Y m.1 r

variable {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Finset ι} {U : List P}
  {c₀ c₁ : List (P × ι)} {M₀ M₁ : List (P × List (Label P (tsObj T)))}

/-- The schedule as a list of moves. -/
abbrev SD.ms (_ : SD I α C R U c₀ c₁ M₀ M₁) : List (P × List (Label P (tsObj T))) :=
  bm c₀ ++ M₀ ++ bm c₁ ++ M₁

lemma flat_append (a b : List (P × List (Label P (tsObj T)))) : flat (a ++ b) = flat a ++ flat b :=
  List.flatMap_append

namespace SD

variable (D : SD I α C R U c₀ c₁ M₀ M₁)
include D

lemma flat_ms : flat D.ms = bw c₀ ++ flat M₀ ++ bw c₁ ++ flat M₁ := by
  simp only [SD.ms, flat_append, flat_bm]

lemma run_ms : ∃ X, I.runFrom C (flat D.ms) = some X := by
  rw [D.flat_ms]; exact D.runs

lemma owned : Owned D.ms := by
  intro m hm
  simp only [SD.ms, List.mem_append] at hm
  rcases hm with ((h | h) | h) | h
  · exact bm_owned c₀ m h
  · exact D.own m (List.mem_append_left _ h)
  · exact bm_owned c₁ m h
  · exact D.own m (List.mem_append_right _ h)

lemma map_fst : D.ms.map Prod.fst =
    c₀.map Prod.fst ++ M₀.map Prod.fst ++ c₁.map Prod.fst ++ M₁.map Prod.fst := by
  simp [SD.ms]

lemma c_pend {p : P} (hp : p ∈ c₀.map Prod.fst ++ c₁.map Prod.fst) : C.pend p ≠ none := by
  rw [← List.map_append] at hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  exact (D.ccov x hx).1.1

lemma c_not_U {p : P} (hp : p ∈ c₀.map Prod.fst ++ c₁.map Prod.fst) : p ∉ U := by
  intro hU
  exact D.c_pend hp (pend_none_of_opsOf_nil D.run ((D.Umem p).1 hU))

lemma M_U {p : P} (hp : p ∈ (M₀ ++ M₁).map Prod.fst) : p ∈ U := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
  exact D.MU x hx

lemma nodup_ms : (D.ms.map Prod.fst).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  have h1 := List.nodup_iff_count_le_one.1 D.cnd a
  have h2 := List.nodup_iff_count_le_one.1 D.Mnd a
  rw [D.map_fst]
  simp only [List.count_append, List.map_append] at h1 h2 ⊢
  by_cases hc : a ∈ c₀.map Prod.fst ++ c₁.map Prod.fst
  · have : a ∉ (M₀ ++ M₁).map Prod.fst := fun h => D.c_not_U hc (D.M_U h)
    simp only [List.map_append, List.mem_append, not_or] at this
    rw [List.count_eq_zero_of_not_mem this.1, List.count_eq_zero_of_not_mem this.2]
    omega
  · simp only [List.mem_append, not_or] at hc
    rw [List.count_eq_zero_of_not_mem hc.1, List.count_eq_zero_of_not_mem hc.2]
    omega

lemma length_ms : D.ms.length = c₀.length + M₀.length + c₁.length + M₁.length := by
  simp [SD.ms]; omega

/-- Covering after a move of `M`, by indices. -/
lemma cov_region {ms A M Z : List (P × List (Label P (tsObj T)))} {pre : List (Label P (tsObj T))}
    (hms : ms = A ++ (M ++ Z)) (hpre : flat A = pre)
    (hcov : ∀ M' m M'', M = M' ++ m :: M'' →
      ∃ Y, I.runFrom C (pre ++ flat (M' ++ [m])) = some Y ∧ ∃ r ∉ (↑R : Set ι), I.Covers Y m.1 r)
    {s : ℕ} (hs : s < ms.length) (hs1 : A.length ≤ s) (hs2 : s < A.length + M.length) :
    ∃ r ∉ (↑R : Set ι), I.Covers (cfgAt I C ms (s + 1)) (ms[s]).1 r := by
  subst hms
  set s' := s - A.length with hs'
  have hs'M : s' < M.length := by omega
  have hM : M = M.take s' ++ M[s'] :: M.drop (s' + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  obtain ⟨Y, hY, hcov'⟩ := hcov _ _ _ hM
  have htake : (A ++ (M ++ Z)).take (s + 1) = A ++ (M.take s' ++ [M[s']]) := by
    rw [List.take_append, List.take_of_length_le (by omega),
      List.take_append_of_le_length (by omega), show s + 1 - A.length = s' + 1 by omega,
      List.take_succ_eq_append_getElem hs'M]
  have hget : (A ++ (M ++ Z))[s] = M[s'] := by
    rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
  have hcfg : cfgAt I C (A ++ (M ++ Z)) (s + 1) = Y := by
    unfold cfgAt
    rw [htake]
    rw [flat_append, hpre, hY]; rfl
  rw [hcfg, hget]; exact hcov'

/-- Every process of `U` that moved covers an object outside `R` right after its move. -/
lemma Uidx (s : ℕ) (hs : s < D.ms.length) (hU : (D.ms[s]).1 ∈ U) :
    ∃ r ∉ (↑R : Set ι), I.Covers (cfgAt I C D.ms (s + 1)) (D.ms[s]).1 r := by
  have hlen := D.length_ms
  -- which region
  rcases Nat.lt_or_ge s c₀.length with h1 | h1
  · exfalso
    have hget : (D.ms[s]).1 = (c₀[s]'h1).1 := by
      simp only [SD.ms, List.append_assoc]
      rw [List.getElem_append_left (by simpa using h1)]
      simp [bm]
    have : (D.ms[s]).1 ∈ c₀.map Prod.fst := by
      rw [hget]; exact List.mem_map_of_mem (List.getElem_mem _)
    exact D.c_not_U (List.mem_append_left _ this) hU
  rcases Nat.lt_or_ge s (c₀.length + M₀.length) with h2 | h2
  · exact D.cov_region (A := bm c₀) (M := M₀) (Z := bm c₁ ++ M₁) (by simp [SD.ms])
      (flat_bm c₀) D.cov₀ hs (by simpa using h1) (by simpa using h2)
  rcases Nat.lt_or_ge s (c₀.length + M₀.length + c₁.length) with h3 | h3
  · exfalso
    have hget : (D.ms[s]).1 = (c₁[s - (c₀.length + M₀.length)]'(by omega)).1 := by
      simp only [SD.ms]
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp [bm]
    have : (D.ms[s]).1 ∈ c₁.map Prod.fst := by
      rw [hget]; exact List.mem_map_of_mem (List.getElem_mem _)
    exact D.c_not_U (List.mem_append_right _ this) hU
  · exact D.cov_region (A := bm c₀ ++ M₀ ++ bm c₁) (M := M₁) (Z := []) (by simp [SD.ms])
      (by simp only [flat_append, flat_bm])
      D.cov₁ hs (by simp; omega) (by simp; omega)

/-! ### Facts at time `t` -/

variable [Fintype P] [Fintype ι]

lemma run_t (t : ℕ) : I.run (α ++ flat (D.ms.take t)) = some (cfgAt I C D.ms t) := by
  obtain ⟨X, hX⟩ := D.run_ms
  rw [run_append_of_eq I D.run]; exact runFrom_take hX t

lemma mv_sub {t : ℕ} {q : P} (h : q ∈ (D.ms.take t).map Prod.fst) : q ∈ D.ms.map Prod.fst :=
  (List.take_sublist t D.ms).map Prod.fst |>.subset h

lemma unmoved {t : ℕ} {q : P} (hq : q ∉ (D.ms.take t).map Prod.fst) :
    (cfgAt I C D.ms t).loc q = C.loc q ∧ (cfgAt I C D.ms t).pend q = C.pend q := by
  obtain ⟨X, hX⟩ := D.run_ms
  exact cfgAt_other D.owned hX hq

lemma opsOf_unmoved {t : ℕ} {q : P} (hq : q ∉ (D.ms.take t).map Prod.fst) :
    opsOf (flat (D.ms.take t)) q = [] :=
  opsOf_eq_nil_of_proc_ne fun ℓ hℓ he =>
    hq (he ▸ flat_procs_take D.owned t ℓ hℓ)

lemma moved_U {t : ℕ} (ht : t ≤ D.ms.length) {q : P} (hq : q ∈ (D.ms.take t).map Prod.fst)
    (hU : q ∈ U) : ∃ r ∉ (↑R : Set ι), I.Covers (cfgAt I C D.ms t) q r := by
  obtain ⟨X, hX⟩ := D.run_ms
  obtain ⟨s, hst, hs, rfl⟩ := mem_take_map_fst hq
  obtain ⟨r, hr, hcov⟩ := D.Uidx s hs hU
  refine ⟨r, hr, ?_⟩
  rcases Nat.lt_or_ge (s + 1) t with h | h
  · have := cfgAt_frozen D.owned D.nodup_ms hX hs t (by omega) ht
    exact hcov.congr this.1.symm this.2.symm
  · have : t = s + 1 := by omega
    subst this; exact hcov

lemma moved_notU {t : ℕ} {q : P} (hq : q ∈ (D.ms.take t).map Prod.fst) (hU : q ∉ U) :
    q ∈ c₀.map Prod.fst ++ c₁.map Prod.fst := by
  have h := D.mv_sub hq
  rw [D.map_fst] at h
  simp only [List.mem_append] at h ⊢
  rcases h with ((h | h) | h) | h
  · exact Or.inl h
  · exact absurd (D.M_U (by simp [h])) hU
  · exact Or.inr h
  · exact absurd (D.M_U (by simp [h])) hU

lemma idle_iff {t : ℕ} (ht : t ≤ D.ms.length) {q : P} :
    q ∈ idleSet (α ++ flat (D.ms.take t)) ↔ q ∈ idleSet α ∧ q ∉ (D.ms.take t).map Prod.fst := by
  simp only [mem_idleSet, opsOf_append, List.append_eq_nil_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hq => ?_⟩
    by_cases hU : q ∈ U
    · obtain ⟨r, -, hr⟩ := D.moved_U ht hq hU
      exact not_idle_of_pend (D.run_t t) hr.1 (by rw [opsOf_append, h1, h2]; rfl)
    · exact hU ((D.Umem q).2 h1)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, D.opsOf_unmoved h2⟩

lemma adm_t (t : ℕ) : Adm true (α ++ flat (D.ms.take t)) := by
  classical
  refine adm_append_of_count D.adm (fun p => ((M₀ ++ M₁).map Prod.fst).count p)
    (fun p => List.nodup_iff_count_le_one.1 D.Mnd p) (fun p hp => ?_) (fun p => ?_)
  · exact (D.Umem p).1 (D.M_U (List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)))
  · have h1 : getTSCount (flat D.ms) p = getTSCount (flat (D.ms.take t)) p +
        getTSCount (flat (D.ms.drop t)) p := by
      rw [flat_take_drop D.ms t, getTSCount_append]
    have h2 : getTSCount (flat D.ms) p = getTSCount (flat (M₀ ++ M₁)) p := by
      rw [D.flat_ms, flat_append]
      simp only [getTSCount_append, getTSCount_blockWrite]; omega
    have := D.cnt p
    omega

lemma c_cov_le_one (cl : List (P × ι)) (hs : (cl.map Prod.snd).Nodup)
    (hcl : ∀ x ∈ cl, I.Covers C x.1 x.2) (r : ι) [DecidablePred (fun p => p ∈ cl.map Prod.fst ∧ I.Covers C p r)] :
    (Finset.univ.filter (fun p => p ∈ cl.map Prod.fst ∧ I.Covers C p r)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map] at ha hb
  obtain ⟨⟨x, hx, rfl⟩, hxr⟩ := ha
  obtain ⟨⟨y, hy, rfl⟩, hyr⟩ := hb
  have e1 : x.2 = r := Covers.unique (hcl x hx) hxr
  have e2 : y.2 = r := Covers.unique (hcl y hy) hyr
  rw [List.inj_on_of_nodup_map hs hx hy (e1.trans e2.symm)]

lemma mv_early {t : ℕ} (ht : t ≤ c₀.length + M₀.length) {q : P}
    (hq : q ∈ (D.ms.take t).map Prod.fst) : q ∉ c₁.map Prod.fst := by
  have htk : D.ms.take t = (bm c₀ ++ M₀).take t := by
    simp only [SD.ms, List.append_assoc]
    rw [← List.append_assoc, List.take_append_of_le_length (by simp; omega)]
  rw [htk] at hq
  have hq' : q ∈ c₀.map Prod.fst ++ M₀.map Prod.fst := by
    have := ((List.take_sublist t _).map Prod.fst).subset hq
    simpa using this
  intro hc
  have hnd := D.nodup_ms
  rw [D.map_fst] at hnd
  have hnd' : (c₀.map Prod.fst ++ M₀.map Prod.fst ++ (c₁.map Prod.fst ++ M₁.map Prod.fst)).Nodup := by
    simpa only [List.append_assoc] using hnd
  exact (List.nodup_append.1 hnd').2.2 q hq' q (List.mem_append_left _ hc) rfl

/-- Coverage of the objects of `R` decreases by at most one per started block write. -/
lemma R_loss {t : ℕ} (r : ι) :
    sig I C r ≤ sig I (cfgAt I C D.ms t) r + 1 +
      (if t ≤ c₀.length + M₀.length then 0 else 1) := by
  classical
  have hcl : ∀ (cl : List (P × ι)), (∀ x ∈ cl, x ∈ c₀ ++ c₁) → ∀ x ∈ cl, I.Covers C x.1 x.2 :=
    fun cl h x hx => (D.ccov x (h x hx)).1
  set A := Finset.univ.filter (fun p => p ∈ c₀.map Prod.fst ∧ I.Covers C p r)
  set Bt := Finset.univ.filter (fun p => p ∈ c₁.map Prod.fst ∧ I.Covers C p r ∧
    p ∈ (D.ms.take t).map Prod.fst)
  have hA : A.card ≤ 1 := D.c_cov_le_one c₀ D.s₀ (hcl c₀ (fun x hx => by simp [hx])) r
  have hB1 : Bt.card ≤ 1 := by
    have := D.c_cov_le_one c₁ D.s₁ (hcl c₁ (fun x hx => by simp [hx])) r
    refine le_trans (Finset.card_le_card fun p hp => ?_) this
    simp only [Bt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hB0 : t ≤ c₀.length + M₀.length → Bt.card = 0 := by
    intro ht
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    exact D.mv_early ht hp.2.2 hp.1
  have hsub : Finset.univ.filter (fun p => I.Covers C p r) ⊆
      (Finset.univ.filter (fun p => I.Covers (cfgAt I C D.ms t) p r) ∪ A) ∪ Bt := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, Bt]
    by_cases hm : p ∈ (D.ms.take t).map Prod.fst
    · have hU : p ∉ U := fun hU => hp.1 (pend_none_of_opsOf_nil D.run ((D.Umem p).1 hU))
      rcases List.mem_append.1 (D.moved_notU hm hU) with h | h
      · exact Or.inl (Or.inr ⟨h, hp⟩)
      · exact Or.inr ⟨h, hp, hm⟩
    · have := D.unmoved hm
      exact Or.inl (Or.inl (hp.congr this.1.symm this.2.symm))
  rw [sig_eq_card, sig_eq_card]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Finset.univ.filter (fun p => I.Covers (cfgAt I C D.ms t) p r) ∪ A) Bt
  have h3 := Finset.card_union_le (Finset.univ.filter (fun p => I.Covers (cfgAt I C D.ms t) p r)) A
  split_ifs with ht
  · have := hB0 ht; omega
  · omega

lemma M₀_moved {t : ℕ} (ht : c₀.length + M₀.length < t) {q : P} (hq : q ∈ M₀.map Prod.fst) :
    q ∈ (D.ms.take t).map Prod.fst := by
  have hpre : (bm c₀ ++ M₀) <+: D.ms.take t := by
    have : bm c₀ ++ M₀ = D.ms.take (c₀.length + M₀.length) := by
      simp only [SD.ms, List.append_assoc]
      rw [← List.append_assoc, List.take_append_of_le_length (by simp),
        List.take_of_length_le (by simp)]
    rw [this, show c₀.length + M₀.length = min (c₀.length + M₀.length) t by omega,
      ← List.take_take]
    exact List.take_prefix _ _
  exact (hpre.sublist.map Prod.fst).subset (by simp [hq])

/-- At the end of the schedule, the processes covering an object outside `R` include those of
`C` and all the moved processes of `U`. -/
lemma outCov_end :
    (outCov I C R).card + M₀.length + M₁.length ≤
      (outCov I (cfgAt I C D.ms D.ms.length) R).card := by
  classical
  have hsub : outCov I C R ∪ ((M₀ ++ M₁).map Prod.fst).toFinset ⊆
      outCov I (cfgAt I C D.ms D.ms.length) R := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · rw [mem_outCov] at hp ⊢
      obtain ⟨r, hr, hcov⟩ := hp
      have hm : p ∉ (D.ms.take D.ms.length).map Prod.fst := by
        rw [List.take_length]
        intro hm
        rw [D.map_fst] at hm
        have hU : p ∉ U := fun hU => hcov.1 (pend_none_of_opsOf_nil D.run ((D.Umem p).1 hU))
        have hc : p ∈ c₀.map Prod.fst ++ c₁.map Prod.fst := by
          simp only [List.mem_append] at hm ⊢
          rcases hm with ((h | h) | h) | h
          · exact Or.inl h
          · exact absurd (D.M_U (by simp [h])) hU
          · exact Or.inr h
          · exact absurd (D.M_U (by simp [h])) hU
        rw [← List.map_append] at hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
        exact hr (by have := Covers.unique (D.ccov x hx).1 hcov; rw [← this]; exact (D.ccov x hx).2)
      have := D.unmoved hm
      exact ⟨r, hr, hcov.congr this.1.symm this.2.symm⟩
    · rw [List.mem_toFinset] at hp
      have hm : p ∈ (D.ms.take D.ms.length).map Prod.fst := by
        rw [List.take_length, D.map_fst]
        simp only [List.map_append, List.mem_append] at hp ⊢
        tauto
      obtain ⟨r, hr, hcov⟩ := D.moved_U le_rfl hm (D.M_U hp)
      rw [mem_outCov]; exact ⟨r, hr, hcov⟩
  have hdisj : Disjoint (outCov I C R) ((M₀ ++ M₁).map Prod.fst).toFinset := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [mem_outCov] at hp
    obtain ⟨r, -, hcov⟩ := hp
    rw [List.mem_toFinset] at hp'
    exact hcov.1 (pend_none_of_opsOf_nil D.run ((D.Umem p).1 (D.M_U hp')))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup D.Mnd] at h1
  rw [List.length_map, List.length_append] at h1; omega

end SD

end Cslib.SharedMemory.Timestamp
