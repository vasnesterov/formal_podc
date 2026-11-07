import Papers.PODC2010.MultiVersionSTM.Theorem1Lower
import Papers.PODC2010.MultiVersionSTM.SnapshotCompute

/-!
# Theorem 1: no MV-permissive STM is online space optimal

Perelman–Fan–Keidar, PODC 2010, Section 5.1. The competitors are the snapshot STMs of
`Snapshot.lean`:

* at `t₀` (history of Figure 2(a)) the *lazy* snapshot STM keeps only 4 overwritten versions
  (`o₂⁰, o₃⁰, o₄⁰, o₅⁰`): it does not keep `o₃¹`, since `T₃` may still read the latest versions;
* at `t₁` (Figure 2(b)) the *eager* snapshot STM keeps only 6 overwritten versions
  (`o₁⁰, …, o₅⁰` and `o₃¹`), since `T₃` reads its start-time snapshot (Figure 2(c)).

Any valid STM keeps at least 5 overwritten versions at `t₀` if it keeps `o₃¹`, and otherwise at
least 7 at `t₁` (`Theorem1Lower.lean`).
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P] {t : Fin 5 → Tx} {ob : Fin 5 → O}

namespace Setup1

variable (S : Setup1 t ob)
include S

lemma ro_cases {T : Tx} (hb : ∃ k, T = t k) (hro : ro T = true) : T = t 0 ∨ T = t 2 := by
  obtain ⟨k, rfl⟩ := hb
  fin_cases k <;> simp_all [S.r1, S.r3, S.r4]

/-- At `t₀`, the lazy snapshot STM keeps only the initial versions of `o₂, …, o₅` among the
overwritten versions. -/
lemma lazy_kept_σH :
    snapKept true ((snapSTM (P := P) true).hist (σH t ob)) ∩
        {v | Old ((snapSTM (P := P) true).hist (σH t ob)) v} ⊆
      {(ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none)} := by
  have e := S.t_eq; have eo := S.ob_eq
  set X := snapSTM (Tx := Tx) (O := O) (P := P) true
  have hg := S.good_σH X (snapSTM_mvPermissive true)
  set h := X.hist (σH t ob) with hh
  have hmap : h.map Event.inv = σH t ob := X.map_inv_hist _
  rintro ⟨o, v⟩ ⟨hk, hold⟩
  have hne := old_ne_latest hg.1 hold
  -- `o` has a committed writer
  have ho : o = ob 1 ∨ o = ob 2 ∨ o = ob 3 ∨ o = ob 4 := by
    obtain ⟨-, w, -, W', -, hcw, -⟩ := hold
    have := writes_iff_map.1 hcw.2
    rw [hmap] at this
    simp [σH] at this
    rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  rcases hk with hl | ⟨T, hro, hnt, hv⟩
  · exact absurd hl hne
  by_cases hb : Began h T
  swap
  · rw [snap_not_began true hb, List.take_length] at hv; exact absurd hv hne
  have hT : ∃ k, T = t k := by
    rw [began_iff_map, hmap] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp [σH] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  rcases S.ro_cases hT hro with rfl | rfl
  · -- `T₁` froze at the commit of `T₂` (index 5)
    have hf : frz h (t 0) = some 5 := by
      rw [frz_eq_some_iff]
      refine ⟨by simp [hh, σH], ?_, ?_⟩
      · rw [freezes_iff hg.2, hmap]
        exact ⟨_, by simp [σH], ob 1, ⟨t 1, rfl, by simp [σH]⟩, by simp [σH]⟩
      · intro j hj
        rw [freezes_iff hg.2, hmap]
        rintro ⟨i, hi, o', ⟨W, rfl, -⟩, -⟩
        interval_cases j <;> simp [σH] at hi
    have hv' : v = none := by
      change v = latest _ o at hv
      rw [hv, snap, if_pos rfl, hf, Option.getD_some, latest_eq_latestS
        (fun e he => hg.2 e (List.mem_of_mem_take he)), List.map_take, hmap]
      simp [σH, latestS, latestR]
    subst hv'
    rcases ho with rfl | rfl | rfl | rfl <;> simp
  · -- `T₃` never froze: it reads the latest versions
    have hf : frz h (t 2) = none := by
      rw [frz_eq_none_iff]
      intro k _
      rw [freezes_iff hg.2, hmap]
      rintro ⟨i, hi, o', ⟨W, rfl, hw⟩, hr⟩
      have hr' := List.mem_of_mem_take hr
      have hw' := List.mem_of_mem_take hw
      simp [σH, e] at hr'
      subst hr'
      simp [σH, eo] at hw'
    rw [snap, if_pos rfl, hf, Option.getD_none, List.take_length] at hv
    exact absurd hv hne

lemma findIdx_t0 : (σH1 t ob).findIdx (fun i => decide (Inv.tx i = t 0)) = 0 := by
  simp [σH1, σH, List.findIdx_cons]

lemma findIdx_t2 : (σH1 t ob).findIdx (fun i => decide (Inv.tx i = t 2)) = 6 := by
  have e := S.t_eq
  simp [σH1, σH, List.findIdx_cons, e]

lemma latestS_take0 (o : O) : latestS ((σH1 t ob).take 0) o = none := by
  simp [latestS, latestR]

lemma latestS_take6 (o : O) :
    latestS ((σH1 t ob).take 6) o = if o = ob 1 ∨ o = ob 2 then some (t 1) else none := by
  have eo := S.ob_eq
  by_cases h1 : o = ob 1
  · subst h1; simp [σH1, σH, latestS, latestR, eo]
  · by_cases h2 : o = ob 2
    · subst h2; simp [σH1, σH, latestS, latestR, eo]
    · simp [σH1, σH, latestS, latestR, h1, h2, Ne.symm h1, Ne.symm h2]

lemma latestS_ob1 : latestS (σH1 t ob) (ob 1) = some (t 1) := by
  have eo := S.ob_eq; have e := S.t_eq
  simp [σH1, σH, latestS, latestR, eo, e]

/-- At `t₁`, the eager snapshot STM keeps only the initial versions and `o₃¹` among the
overwritten versions (Figure 2(c)). -/
lemma eager_kept_σH1 :
    snapKept false ((snapSTM (P := P) false).hist (σH1 t ob)) ∩
        {v | Old ((snapSTM (P := P) false).hist (σH1 t ob)) v} ⊆
      {(ob 0, none), (ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none), (ob 2, some (t 1))} := by
  set X := snapSTM (Tx := Tx) (O := O) (P := P) false
  have hg := S.good_σH1 X (snapSTM_mvPermissive false)
  set h := X.hist (σH1 t ob) with hh
  have hmap : h.map Event.inv = σH1 t ob := X.map_inv_hist _
  have hs := hg.2
  rintro ⟨o, v⟩ ⟨hk, hold⟩
  have hne := old_ne_latest hg.1 hold
  have hlat : ∀ s o, latest (h.take s) o = latestS ((σH1 t ob).take s) o := fun s o => by
    rw [latest_eq_latestS (fun e he => hs e (List.mem_of_mem_take he)), List.map_take, hmap]
  have ho : o = ob 0 ∨ o = ob 1 ∨ o = ob 2 ∨ o = ob 3 ∨ o = ob 4 := by
    obtain ⟨-, w, -, W', -, hcw, -⟩ := hold
    have := writes_iff_map.1 hcw.2
    rw [hmap] at this
    simp [σH1, σH] at this
    rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
      ⟨-, rfl⟩ <;> simp
  have hini : v = none → (o, v) ∈ ({(ob 0, none), (ob 1, none), (ob 2, none), (ob 3, none),
      (ob 4, none), (ob 2, some (t 1))} : Set (Version Tx O)) := by
    rintro rfl; rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp
  rcases hk with hl | ⟨T, hro, hnt, hv⟩
  · exact absurd hl hne
  change v = latest _ o at hv
  by_cases hb : Began h T
  swap
  · rw [snap_not_began false hb, List.take_length] at hv; exact absurd hv hne
  have hT : ∃ k, T = t k := by
    rw [began_iff_map, hmap] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp [σH1, σH] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> exact ⟨_, rfl⟩
  rcases S.ro_cases hT hro with rfl | rfl
  · rw [snap, if_neg (by simp), firstIdx_eq_map, hmap, S.findIdx_t0, hlat, S.latestS_take0] at hv
    exact hini hv
  · rw [snap, if_neg (by simp), firstIdx_eq_map, hmap, S.findIdx_t2, hlat, S.latestS_take6] at hv
    by_cases h1 : o = ob 1
    · subst h1
      rw [if_pos (Or.inl rfl)] at hv
      subst hv
      refine absurd ?_ hne
      change some (t 1) = latest h (ob 1)
      have hlen : h.length = (σH1 t ob).length := by rw [← hmap, List.length_map]
      rw [← List.take_length (l := h), hlat, hlen, List.take_length, S.latestS_ob1]
    · by_cases h2 : o = ob 2
      · subst h2
        rw [if_pos (Or.inr rfl)] at hv
        rw [hv]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
      · simp only [h1, h2, or_self, if_false] at hv; exact hini hv

lemma encard4 : ({(ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none)} :
    Set (Version Tx O)).encard = 4 := by
  have eo := S.ob_eq
  rw [Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_singleton]
  rfl

lemma encard5 : ({(ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none), (ob 2, some (t 1))} :
    Set (Version Tx O)).encard = 5 := by
  have eo := S.ob_eq
  rw [Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_singleton]
  rfl

lemma encard6 : ({(ob 0, none), (ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none),
    (ob 2, some (t 1))} : Set (Version Tx O)).encard = 6 := by
  have eo := S.ob_eq
  rw [Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_singleton]
  rfl

lemma encard7 : ({(ob 0, none), (ob 1, none), (ob 2, none), (ob 3, none), (ob 4, none),
    (ob 3, some (t 3)), (ob 4, some (t 3))} : Set (Version Tx O)).encard = 7 := by
  have eo := S.ob_eq
  rw [Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_insert_of_notMem (by simp [eo]), Set.encard_insert_of_notMem (by simp [eo]),
    Set.encard_singleton]
  rfl

lemma old_initial (X : STM Tx O P) {σ : List (Inv Tx O)} (hs : AllSucc (X.hist σ)) {o : O} {W : Tx}
    (hc : Inv.commit W ∈ σ) (hw : Inv.write W o ∈ σ) : Old (X.hist σ) (o, none) :=
  ⟨trivial, (o, some W), rfl, W, rfl, (X.cwriter_hist_iff hs).2 ⟨hc, hw⟩, fun _ h => by cases h⟩

/-- Case 1 (`X` keeps `o₃¹` at `t₀`): `X` keeps at least 5 overwritten versions at `t₀`. -/
lemma lower_case1 (X : STM Tx O P) (kept : Config X → Set (Version Tx O)) (hv : X.Valid kept)
    (hk : (ob 2, some (t 1)) ∈ kept (X.conf (σH t ob))) : 5 ≤ X.keptOld kept (σH t ob) := by
  have e := S.t_eq
  have hs := (S.good_σH X hv.mvPermissive).2
  have hk0 := fun k => by simpa using S.t1_keeps_initial X kept hv [] (Or.inl rfl) k
  rw [← S.encard5]
  refine Set.encard_le_encard ?_
  intro v hv'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
  rcases hv' with rfl | rfl | rfl | rfl | rfl
  · exact ⟨hk0 1, S.old_initial X hs (W := t 1) (by simp [σH]) (by simp [σH])⟩
  · exact ⟨hk0 2, S.old_initial X hs (W := t 1) (by simp [σH]) (by simp [σH])⟩
  · exact ⟨hk0 3, S.old_initial X hs (W := t 3) (by simp [σH]) (by simp [σH])⟩
  · exact ⟨hk0 4, S.old_initial X hs (W := t 3) (by simp [σH]) (by simp [σH])⟩
  · refine ⟨hk, (X.cwriter_hist_iff hs).2 (by simp [σH]), (ob 2, some (t 3)), rfl, t 3, rfl,
      (X.cwriter_hist_iff hs).2 (by simp [σH]), fun W hW => ?_⟩
    cases hW
    have := X.commitBefore_hist ((σH t ob).take 6) ((σH t ob).drop 6) (A := t 1) (B := t 3)
      (by simpa using hs) (by simp [σH]) (by simp [σH, e])
    simpa using this

/-- Case 2 (`X` does not keep `o₃¹` at `t₀`): `X` keeps at least 7 overwritten versions at
`t₁`. -/
lemma lower_case2 (X : STM Tx O P) (kept : Config X → Set (Version Tx O)) (hv : X.Valid kept)
    (hk : (ob 2, some (t 1)) ∉ kept (X.conf (σH t ob))) : 7 ≤ X.keptOld kept (σH1 t ob) := by
  have e := S.t_eq
  have hs := (S.good_σH1 X hv.mvPermissive).2
  have hk0 := fun k => S.t1_keeps_initial X kept hv (τ5 t ob) (Or.inr rfl) k
  rw [← S.encard7]
  refine Set.encard_le_encard ?_
  intro v hv'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
  have hold4 : ∀ m : Fin 5, (m = 3 ∨ m = 4) → Old (X.hist (σH1 t ob)) (ob m, some (t 3)) := by
    intro m hm
    refine ⟨(X.cwriter_hist_iff hs).2 (by rcases hm with rfl | rfl <;> simp [σH1, σH]),
      (ob m, some (t 4)), rfl, t 4, rfl,
      (X.cwriter_hist_iff hs).2 (by rcases hm with rfl | rfl <;> simp [σH1, σH]), fun W hW => ?_⟩
    cases hW
    exact X.commitBefore_hist (σ₁ := σH t ob) (σ₂ := τ5 t ob) hs (by simp [σH]) (by simp [σH, e])
  rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hk0 0, S.old_initial X hs (W := t 4) (by simp [σH1]) (by simp [σH1])⟩
  · exact ⟨hk0 1, S.old_initial X hs (W := t 1) (by simp [σH1, σH]) (by simp [σH1, σH])⟩
  · exact ⟨hk0 2, S.old_initial X hs (W := t 1) (by simp [σH1, σH]) (by simp [σH1, σH])⟩
  · exact ⟨hk0 3, S.old_initial X hs (W := t 3) (by simp [σH1, σH]) (by simp [σH1, σH])⟩
  · exact ⟨hk0 4, S.old_initial X hs (W := t 3) (by simp [σH1, σH]) (by simp [σH1, σH])⟩
  · exact ⟨S.t1_keeps_T4 X kept hv hk 3 (Or.inl rfl), hold4 3 (Or.inl rfl)⟩
  · exact ⟨S.t1_keeps_T4 X kept hv hk 4 (Or.inr rfl), hold4 4 (Or.inr rfl)⟩

end Setup1

end Podc.MultiVersionSTM

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type} [TxSys Tx P]

lemma snap_keptOld (lazy : Bool) (σ : List (Inv Tx O)) :
    (snapSTM (P := P) lazy).keptOld (snapKeptC lazy) σ =
      (snapKept lazy ((snapSTM (P := P) lazy).hist σ) ∩
        {v | Old ((snapSTM (P := P) lazy).hist σ) v}).encard := by
  simp only [STM.keptOld, snapKeptC]
  rw [show ((snapSTM (P := P) lazy).conf σ).mem () = (snapSTM (P := P) lazy).hist σ from
    ofStrategy.conf_mem _ σ]

/-- **Theorem 1** of [Perelman–Fan–Keidar, PODC 2010]: no MV-permissive STM is online space
optimal. Here an MV-permissive STM is a strictly serializable, MV-permissive STM whose reads
return written versions, together with its set of kept versions (`STM.Valid`); the universe has
five distinct objects and five distinct transactions on distinct threads, `T₁` and `T₃`
read-only (`Setup1`). If `X` keeps `o₃¹` at time `t₀` of Figure 2(a), the lazy snapshot STM keeps
fewer overwritten versions at `t₀`; otherwise the eager snapshot STM keeps fewer at `t₁` of
Figure 2(b). -/
theorem theorem_1 {t : Fin 5 → Tx} {ob : Fin 5 → O} (S : Setup1 t ob) (X : STM Tx O P)
    (kept : Config X → Set (Version Tx O)) (hv : X.Valid kept) : ¬ X.OnlineSpaceOptimal kept := by
  intro hopt
  by_cases hk : (ob 2, some (t 1)) ∈ kept (X.conf (σH t ob))
  · have h := hopt (snapSTM true) (snapKeptC true) (snapSTM_valid true) (σH t ob)
      (S.good_σH X hv.mvPermissive).1 (S.good_σH _ (snapSTM_mvPermissive true)).1
    have h1 := S.lower_case1 X kept hv hk
    have h2 : (snapSTM (P := P) true).keptOld (snapKeptC true) (σH t ob) ≤ 4 := by
      rw [snap_keptOld, ← S.encard4]; exact Set.encard_le_encard S.lazy_kept_σH
    have := h1.trans (h.trans h2)
    exact absurd this (by decide)
  · have h := hopt (snapSTM false) (snapKeptC false) (snapSTM_valid false) (σH1 t ob)
      (S.good_σH1 X hv.mvPermissive).1 (S.good_σH1 _ (snapSTM_mvPermissive false)).1
    have h1 := S.lower_case2 X kept hv hk
    have h2 : (snapSTM (P := P) false).keptOld (snapKeptC false) (σH1 t ob) ≤ 6 := by
      rw [snap_keptOld, ← S.encard6]; exact Set.encard_le_encard S.eager_kept_σH1
    have := h1.trans (h.trans h2)
    exact absurd this (by decide)

end Podc.MultiVersionSTM
