import Papers.PODC2016.WeakCrashFailures.Fig1Step

/-!
# Fig. 1: the invariant is inductive; agreement and validity (Lemmas 3, 4, Theorem 2)
-/

namespace Podc.WeakCrashFailures.Fig1

open Finset

variable {n : ℕ} {x : Fin n → ℕ}

/-- `omega` after unfolding `setPc` in the memory. -/
local macro "som" : tactic => `(tactic| ((try simp only [setPc_st] at *) <;> omega))

/-! ### Auxiliary facts -/

lemma pc_ne_start_of_st_pos {C : Cfg n} (hI : Inv x C) {k : Fin n} (h : 0 < C.st k) :
    C.pc k ≠ .start := by
  intro hk
  have := hI.li k
  rw [hk] at this
  simp only [LIpc] at this
  omega

lemma inr_of_st_pos {C : Cfg n} (hI : Inv x C) {k : Fin n} (h : 0 < C.st k) :
    C.inr k = x k := hI.inr k (pc_ne_start_of_st_pos hI h)

/-- A process whose state is at most `1` is before round 3. -/
lemma preR3_of_st_le_one {C : Cfg n} (hI : Inv x C) {y : Fin n} (h : C.st y ≤ 1) :
    PreRpc 3 y (C.pc y) := by
  have hli := hI.li y
  generalize C.pc y = c at hli
  cases c with
  | start => trivial
  | scan r j cnt mx => obtain ⟨-, -, -, h4, -⟩ := hli; exact Or.inl (by omega)
  | scanIn r j cnt mx => obtain ⟨-, -, -, h4, -⟩ := hli; exact Or.inl (by omega)
  | wait r j cnt mx => obtain ⟨-, -, -, h4, -⟩ := hli; show r < 3; omega
  | chk j cnt mx => obtain ⟨-, h4, -⟩ := hli; omega
  | chkIn j cnt mx => obtain ⟨h4, -⟩ := hli; omega
  | fin j mx => obtain ⟨-, h4, -⟩ := hli; omega
  | finDec j mx b => obtain ⟨h4, -⟩ := hli; omega
  | finIn j mx => obtain ⟨h4, -⟩ := hli; omega
  | done v => trivial

lemma sup_insert_max (a : Fin n) (S : Finset (Fin n)) :
    (insert a S).sup x = max (S.sup x) (x a) := by
  rw [sup_insert, max_comm]

/-- The local invariant only depends on the memory through monotone facts. -/
lemma LIpc_frame {C C' : Cfg n} {i : Fin n} {c : PC} (hLI : LIpc x C i c)
    (hst : C'.st i = C.st i) (hmono : ∀ k, C.st k ≤ C'.st k) (hle3 : ∀ k, C'.st k ≤ 3)
    (hdec : C.dec.isSome → C'.dec.isSome) (hdoom : ∀ y, DoomedR C 3 y → DoomedR C' 3 y)
    (htag : ∀ t, TagFact C t → TagFact C' t) : LIpc x C' i c := by
  have h3 : ∀ k, C.st k = 3 → C'.st k = 3 := fun k hk => by
    have := hmono k; have := hle3 k; omega
  have hge : ∀ k r, r ≤ C.st k → r ≤ C'.st k := fun k r hk => le_trans hk (hmono k)
  have hcnt : ∀ r, cntGE C r ≤ cntGE C' r := cntGE_mono hmono
  cases c with
  | start => simp only [LIpc] at hLI ⊢; omega
  | scan r j cnt mx =>
    obtain ⟨h1, h2, h3', h4, h5, S, hS, hc, hm⟩ := hLI
    exact ⟨h1, h2, h3', by rw [hst]; exact h4, fun h => le_trans (h5 h) (hcnt 1),
      S, fun k hk => ⟨(hS k hk).1, hge k r (hS k hk).2⟩, hc, hm⟩
  | scanIn r j cnt mx =>
    obtain ⟨h1, h2, hj, h4, h5, h6, S, hS, hc, hm⟩ := hLI
    exact ⟨h1, h2, hj, by rw [hst]; exact h4, fun h => le_trans (h5 h) (hcnt 1), hge _ r h6,
      S, fun k hk => ⟨(hS k hk).1, hge k r (hS k hk).2⟩, hc, hm⟩
  | wait r j cnt mx =>
    obtain ⟨h1, h2, h3', h4, ⟨S, hS, hc⟩, hT⟩ := hLI
    exact ⟨h1, h2, h3', by rw [hst]; exact h4,
      ⟨S, fun k hk => ⟨(hS k hk).1, hge k r (hS k hk).2⟩, hc⟩, hT⟩
  | chk j cnt mx =>
    obtain ⟨hj, h4, ⟨S3, hS3c, hS3⟩, Cn, hCn, hc, hm, hd⟩ := hLI
    exact ⟨hj, by rw [hst]; exact h4, ⟨S3, hS3c, fun k hk => h3 k (hS3 k hk)⟩, Cn,
      fun k hk => ⟨(hCn k hk).1, hge k 2 (hCn k hk).2⟩, hc, hm, fun k hk hk' => hdoom k (hd k hk hk')⟩
  | chkIn j cnt mx =>
    obtain ⟨h4, hj, h2, ⟨S3, hS3c, hS3⟩, Cn, hCn, hc, hm, hd⟩ := hLI
    exact ⟨by rw [hst]; exact h4, hj, hge _ 2 h2, ⟨S3, hS3c, fun k hk => h3 k (hS3 k hk)⟩, Cn,
      fun k hk => ⟨(hCn k hk).1, hge k 2 (hCn k hk).2⟩, hc, hm, fun k hk hk' => hdoom k (hd k hk hk')⟩
  | fin j mx =>
    obtain ⟨hj, h4, h2, hl, hT⟩ := hLI
    exact ⟨hj, by rw [hst]; exact h4, fun k => hge k 2 (h2 k), fun k hk => h3 k (hl k hk), hT⟩
  | finDec j mx b =>
    obtain ⟨h4, h2, hj, hl, hb, hT⟩ := hLI
    exact ⟨by rw [hst]; exact h4, fun k => hge k 2 (h2 k), hj, fun k hk => h3 k (hl k hk),
      fun h => h3 _ (hb h), hT⟩
  | finIn j mx =>
    obtain ⟨h4, h2, hj, hl, hb, hT⟩ := hLI
    exact ⟨by rw [hst]; exact h4, fun k => hge k 2 (h2 k), hj, fun k hk => h3 k (hl k hk),
      h3 _ hb, hT⟩
  | done v =>
    obtain ⟨hd, t, ht, hv⟩ := hLI
    exact ⟨hdec hd, t, htag t ht, hv⟩

/-! ### The stepping process -/

/-- What has to be shown about the stepping process. -/
def SelfOK (x : Fin n → ℕ) (C' : Cfg n) (i : Fin n) : Prop :=
  LIpc x C' i (C'.pc i) ∧ (C'.pc i ≠ .start → C'.inr i = x i) ∧
    (2 ≤ C'.st i → n - 1 ≤ cntGE C' 1) ∧ ∀ v, C'.dec = some v → ∃ t, TagFact C' t ∧ v = val x t

lemma selfOK_setPc {C : Cfg n} (hI : Inv x C) {i : Fin n} {c : PC} (hc : C.pc i ≠ .start)
    (htag : ∀ t, TagFact C t → TagFact (setPc i c C) t) (hli : LIpc x (setPc i c C) i c) :
    SelfOK x (setPc i c C) i := by
  refine ⟨by simpa using hli, fun _ => hI.inr i hc, fun h => hI.g3 i h, fun v hv => ?_⟩
  obtain ⟨t, ht, hvt⟩ := hI.dec v hv
  exact ⟨t, htag t ht, hvt⟩

lemma self_step {C : Cfg n} (hI : Inv x C) (i : Fin n) : SelfOK x (step x i C) i := by
  have htag : ∀ t, TagFact C t → TagFact (step x i C) t := fun t h => tagFact_step hI h i
  have hdoom : ∀ y, DoomedR C 3 y → DoomedR (step x i C) 3 y := fun y h =>
    doomed_step hI (by omega) le_rfl h i
  have hmono := st_step_mono hI i
  have hli := hI.li i
  generalize hC' : step x i C = C' at htag hdoom hmono
  cases hc : C.pc i with
  | start =>
    simp only [step, hc] at hC'
    subst hC'
    simp only [LIpc, hc] at hli
    refine ⟨?_, by simp, by simp [hli], fun v hv => ?_⟩
    · simp only [Function.update_self, LIpc]
      exact ⟨le_rfl, by omega, Nat.zero_le _, by simp [hli], by omega, ∅, by simp, rfl, rfl⟩
    · obtain ⟨t, ht, hvt⟩ := hI.dec v hv
      exact ⟨t, htag t ht, hvt⟩
  | scan r j cnt mx =>
    rw [hc] at hli
    obtain ⟨h1, h3, hjn, hst, h2, S, hS, hcard, hmx⟩ := hli
    simp only [step, hc] at hC'
    split_ifs at hC' with hj hle hcn
    · subst hC'
      refine selfOK_setPc hI (by simp [hc]) htag ⟨h1, h3, hj, hst, h2, ?_, S, hS, by omega, hmx⟩
      rwa [stAt_of_lt hj] at hle
    · subst hC'
      exact selfOK_setPc hI (by simp [hc]) htag ⟨h1, h3, by omega, hst, h2, S,
        fun k hk => ⟨by have := (hS k hk).1; omega, (hS k hk).2⟩, hcard, hmx⟩
    · subst hC'
      have hiS : i ∉ S := fun h => by have := (hS i h).2; omega
      have hSe : S = univ.erase i := eq_erase_of_card hiS (by omega)
      have ht : TagFact { C with dec := some mx, pc := Function.update C.pc i (.done mx) } (.ex i) := by
        refine ⟨fun k hk => ?_, Or.inl ⟨mx, by simp⟩⟩
        have : k ∈ S := by rw [hSe]; simp [hk]
        have := (hS k this).2
        simp only; omega
      refine ⟨by simp only [Function.update_self, LIpc]; exact ⟨by simp, .ex i, ht, by simp [val, hmx, hSe]⟩, fun _ => hI.inr i (by simp [hc]),
        fun h => hI.g3 i h, fun v hv => ⟨.ex i, ht, ?_⟩⟩
      simp only [Option.some.injEq] at hv
      simp [val, ← hv, hmx, hSe]
    · subst hC'
      refine ⟨?_, fun _ => hI.inr i (by simp [hc]), fun h => ?_, fun v hv => ?_⟩
      · simp only [Function.update_self, LIpc]
        exact ⟨h1, h3, Nat.zero_le _, by simp, ⟨∅, by simp, rfl⟩, S, hmx⟩
      · have hm := cntGE_mono hmono 1
        simp only [Function.update_self] at h
        rcases Nat.lt_or_ge r 3 with hr | hr
        · exact le_trans (h2 (by omega)) hm
        · exact le_trans (hI.g3 i (by omega)) hm
      · obtain ⟨t, ht, hvt⟩ := hI.dec v hv
        exact ⟨t, htag t ht, hvt⟩
  | scanIn r j cnt mx =>
    rw [hc] at hli
    obtain ⟨h1, h3, hj, hst, h2, hle, S, hS, hcard, hmx⟩ := hli
    simp only [step, hc] at hC'
    subst hC'
    have hjS : (⟨j, hj⟩ : Fin n) ∉ S := fun h => by have := (hS _ h).1; simp at this
    refine selfOK_setPc hI (by simp [hc]) htag ⟨h1, h3, by omega, hst, h2, insert ⟨j, hj⟩ S,
      fun k hk => ?_, by rw [card_insert_of_notMem hjS]; omega, ?_⟩
    · rcases mem_insert.1 hk with rfl | hk
      · exact ⟨Nat.lt_succ_self j, hle⟩
      · exact ⟨by have := (hS k hk).1; omega, (hS k hk).2⟩
    · rw [sup_insert_max, ← hmx, inAt_of_lt hj, inr_of_st_pos hI (by omega)]
  | wait r j cnt mx =>
    rw [hc] at hli
    obtain ⟨h1, h3, hjn, hst, ⟨S, hS, hcard⟩, T, hT⟩ := hli
    simp only [step, hc] at hC'
    by_cases hj : j < n
    · simp only [hj, ite_true] at hC'
      subst hC'
      refine selfOK_setPc hI (by simp [hc]) htag ⟨h1, h3, by omega, hst, ?_, T, hT⟩
      split_ifs with hle
      · have hjS : (⟨j, hj⟩ : Fin n) ∉ S := fun h => by have := (hS _ h).1; simp at this
        refine ⟨insert ⟨j, hj⟩ S, fun k hk => ?_, by rw [card_insert_of_notMem hjS, hcard]⟩
        rcases mem_insert.1 hk with rfl | hk
        · exact ⟨Nat.lt_succ_self j, by rwa [stAt_of_lt hj] at hle⟩
        · exact ⟨by have := (hS k hk).1; omega, (hS k hk).2⟩
      · exact ⟨S, fun k hk => ⟨by have := (hS k hk).1; omega, (hS k hk).2⟩, hcard⟩
    · simp only [hj, ite_false] at hC'
      cases hd : C.dec with
      | some d =>
        simp only [hd] at hC'
        subst hC'
        obtain ⟨t, ht, hvt⟩ := hI.dec d hd
        exact selfOK_setPc hI (by simp [hc]) htag ⟨by simp [hd], t, htag t ht, hvt⟩
      | none =>
        simp only [hd] at hC'
        have hSn : S.card ≤ n := by simpa using card_le_univ S
        split_ifs at hC' with hge hr3 hcn
        · subst hC'
          refine selfOK_setPc hI (by simp [hc]) htag
            ⟨by omega, by omega, Nat.zero_le _, by som, fun hr => ?_, ∅, by simp, rfl, rfl⟩
          refine le_trans (by omega) (card_le_card (s := S) fun k hk => ?_)
          exact mem_filter.2 ⟨mem_univ _, by have := (hS k hk).2; show 1 ≤ C.st k; omega⟩
        · subst hC'
          refine selfOK_setPc hI (by simp [hc]) htag
            ⟨Nat.zero_le _, by som, ⟨S, by omega, fun k hk => ?_⟩, ∅, by simp, rfl, rfl,
              fun k hk => by simp at hk⟩
          have := (hS k hk).2; have := hI.le3 k; som
        · subst hC'
          have hSu : S = univ := eq_univ_of_card (by omega)
          refine selfOK_setPc hI (by simp [hc]) htag
            ⟨Nat.zero_le _, by som, fun k => ?_, fun k hk => by simp at hk, T, ?_⟩
          · have := (hS k (by rw [hSu]; exact mem_univ k)).2; som
          · simp [ltSet, hT]
        · subst hC'
          exact selfOK_setPc hI (by simp [hc]) htag
            ⟨h1, h3, Nat.zero_le _, hst, ⟨∅, by simp, rfl⟩, T, hT⟩
  | chk j cnt mx =>
    rw [hc] at hli
    obtain ⟨hjn, hst, ⟨S3, hS3c, hS3⟩, Cn, hCn, hcard, hmx, hdm⟩ := hli
    simp only [step, hc] at hC'
    split_ifs at hC' with hj hle hcn
    · subst hC'
      refine selfOK_setPc hI (by simp [hc]) htag ⟨hst, hj, ?_, ⟨S3, hS3c, hS3⟩, Cn, hCn,
        by omega, hmx, fun k hk hk' => hdoom k (hdm k hk hk')⟩
      rwa [stAt_of_lt hj] at hle
    · subst hC'
      refine selfOK_setPc hI (by simp [hc]) htag ⟨by omega, hst, ⟨S3, hS3c, hS3⟩, Cn,
        fun k hk => ⟨by have := (hCn k hk).1; omega, (hCn k hk).2⟩, hcard, hmx,
        fun k hk hk' => hdoom k ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact hdm k hk hk'
      · have hkj : k = ⟨j, hj⟩ := Fin.ext hk
        rw [stAt_of_lt hj, ← hkj] at hle
        have hkS : k ∉ S3 := fun h => by have := hS3 k h; omega
        have hSe := eq_erase_of_card hkS (by omega)
        refine ⟨fun k' hk' => ?_, by omega, preR3_of_st_le_one hI (by omega)⟩
        have : k' ∈ S3 := by rw [hSe]; simp [hk']
        rw [hS3 k' this]
    · subst hC'
      have hCnu : Cn.card < (univ : Finset (Fin n)).card := by
        rw [card_univ, Fintype.card_fin]; have := i.isLt; omega
      obtain ⟨k0, -, hk0⟩ := exists_mem_notMem_of_card_lt_card hCnu
      have hCe := eq_erase_of_card hk0 (by omega)
      have hd0 := hdoom k0 (hdm k0 (by have := k0.isLt; omega) hk0)
      have ht : TagFact { C with dec := some mx, pc := Function.update C.pc i (.done mx) }
          (.ex k0) := by
        refine ⟨fun k hk => ?_, Or.inr hd0⟩
        have := hd0.1 k hk; have := hd0.2.1; omega
      refine ⟨by simp only [Function.update_self, LIpc]; exact ⟨by simp, .ex k0, ht, by simp [val, hmx, hCe]⟩, fun _ => hI.inr i (by simp [hc]),
        fun h => hI.g3 i h, fun v hv => ⟨.ex k0, ht, ?_⟩⟩
      simp only [Option.some.injEq] at hv
      simp [val, ← hv, hmx, hCe]
    · subst hC'
      have hsub : S3 ⊆ Cn := by
        intro k hk
        by_contra hk'
        have := (hdm k (by have := k.isLt; omega) hk').2.1
        have := hS3 k hk
        omega
      have hCnn : Cn.card ≤ n := by simpa using card_le_univ Cn
      have := card_le_card hsub
      have hCu : Cn = univ := eq_univ_of_card (by omega)
      refine selfOK_setPc hI (by simp [hc]) htag
        ⟨Nat.zero_le _, hst, fun k => ?_, fun k hk => by simp at hk, Cn, by simp [ltSet, hmx]⟩
      exact (hCn k (by rw [hCu]; exact mem_univ k)).2
  | chkIn j cnt mx =>
    rw [hc] at hli
    obtain ⟨hst, hj, hle, ⟨S3, hS3c, hS3⟩, Cn, hCn, hcard, hmx, hdm⟩ := hli
    simp only [step, hc] at hC'
    subst hC'
    have hjS : (⟨j, hj⟩ : Fin n) ∉ Cn := fun h => by have := (hCn _ h).1; simp at this
    refine selfOK_setPc hI (by simp [hc]) htag ⟨by omega, hst, ⟨S3, hS3c, hS3⟩, insert ⟨j, hj⟩ Cn,
      fun k hk => ?_, by rw [card_insert_of_notMem hjS]; omega, ?_, fun k hk hk' => hdoom k ?_⟩
    · rcases mem_insert.1 hk with rfl | hk
      · exact ⟨Nat.lt_succ_self j, hle⟩
      · exact ⟨by have := (hCn k hk).1; omega, (hCn k hk).2⟩
    · rw [sup_insert_max, ← hmx, inAt_of_lt hj, inr_of_st_pos hI (by omega)]
    · have hkj : k ≠ ⟨j, hj⟩ := fun h => hk' (by rw [h]; exact mem_insert_self _ _)
      have hk2 : k.val < j := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · exact hk
        · exact absurd (Fin.ext hk) hkj
      exact hdm k hk2 (fun h => hk' (mem_insert_of_mem h))
  | fin j mx =>
    rw [hc] at hli
    obtain ⟨hjn, hst, h2, hl, T, hT⟩ := hli
    simp only [step, hc] at hC'
    split_ifs at hC' with hj
    · subst hC'
      refine selfOK_setPc hI (by simp [hc]) htag ⟨hst, h2, hj, hl, fun hb => ?_, T, hT⟩
      simpa [stAt_of_lt hj] using hb
    · subst hC'
      have ht : TagFact { C with dec := some mx, pc := Function.update C.pc i (.done mx) } .all :=
        fun k => hl k (by have := k.isLt; omega)
      have hmx' : mx = val x .all := by
        rw [hT, ltSet_of_le (by omega), union_eq_right.2 (subset_univ T)]; rfl
      refine ⟨by simp only [Function.update_self, LIpc]; exact ⟨by simp, .all, ht, hmx'⟩, fun _ => hI.inr i (by simp [hc]),
        fun h => hI.g3 i h, fun v hv => ⟨.all, ht, ?_⟩⟩
      simp only [Option.some.injEq] at hv
      rw [← hv, hmx']
  | finDec j mx b =>
    rw [hc] at hli
    obtain ⟨hst, h2, hj, hl, hb, T, hT⟩ := hli
    simp only [step, hc] at hC'
    cases hd : C.dec with
    | some d =>
      simp only [hd] at hC'
      subst hC'
      obtain ⟨t, ht, hvt⟩ := hI.dec d hd
      exact selfOK_setPc hI (by simp [hc]) htag ⟨by simp [hd], t, htag t ht, hvt⟩
    | none =>
      simp only [hd] at hC'
      split_ifs at hC' with hbt
      · subst hC'
        exact selfOK_setPc hI (by simp [hc]) htag ⟨hst, h2, hj, hl, hb hbt, T, hT⟩
      · subst hC'
        exact selfOK_setPc hI (by simp [hc]) htag ⟨by omega, hst, h2, hl, T, hT⟩
  | finIn j mx =>
    rw [hc] at hli
    obtain ⟨hst, h2, hj, hl, hj3, T, hT⟩ := hli
    simp only [step, hc] at hC'
    subst hC'
    refine selfOK_setPc hI (by simp [hc]) htag ⟨by omega, hst, h2, fun k hk => ?_, T, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact hl k hk
      · rw [show k = ⟨j, hj⟩ from Fin.ext hk]; exact hj3
    · rw [ltSet_succ hj, union_insert, sup_insert_max, ← hT,
        inAt_of_lt hj, inr_of_st_pos hI (by omega)]
  | done v =>
    rw [step_done hc] at hC'
    subst hC'
    exact ⟨by rw [hc]; rw [hc] at hli; exact hli, fun h => hI.inr i h, hI.g3 i, hI.dec⟩

/-! ### The invariant is inductive -/

theorem inv_init (x inr₀ : Fin n → ℕ) : Inv x (init inr₀) where
  li i := by simp [init, LIpc]
  le3 k := by simp [init]
  inr k h := absurd rfl h
  g3 k h := by simp [init] at h
  dec v h := by simp [init] at h

theorem inv_step {C : Cfg n} (hI : Inv x C) (i : Fin n) : Inv x (step x i C) := by
  have hmono := st_step_mono hI i
  have hle3 := st_step_le3 hI i
  have hdoom : ∀ y, DoomedR C 3 y → DoomedR (step x i C) 3 y := fun y h =>
    doomed_step hI (by omega) le_rfl h i
  have htag : ∀ t, TagFact C t → TagFact (step x i C) t := fun t h => tagFact_step hI h i
  obtain ⟨hown, hinr, hg3, hdec⟩ := self_step hI i
  refine ⟨fun k => ?_, hle3, fun k hk => ?_, fun k hk => ?_, hdec⟩
  · by_cases hk : k = i
    · subst hk; exact hown
    · rw [step_pc_ne hk]
      exact LIpc_frame (hI.li k) (step_st_ne hk C) hmono hle3 step_dec_isSome hdoom htag
  · by_cases hki : k = i
    · subst hki; exact hinr hk
    · rw [step_inr_ne hki]; rw [step_pc_ne hki] at hk; exact hI.inr k hk
  · by_cases hki : k = i
    · subst hki; exact hg3 hk
    · rw [step_st_ne hki] at hk
      exact le_trans (hI.g3 k hk) (cntGE_mono hmono 1)

theorem inv_exec (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) (t : ℕ) : Inv x (exec x inr₀ σ t) := by
  induction t with
  | zero => exact inv_init x inr₀
  | succ t ih => rw [exec_succ]; exact inv_step ih _

/-! ### Participation -/

lemma step_pc_self_ne_start (i : Fin n) (C : Cfg n) :
    (step x i C).pc i ≠ .start := by
  unfold step
  split <;> (try split) <;> (try split_ifs) <;> (try split) <;> simp_all [setPc]

/-- A process is still at line 1 iff it has not taken a step. -/
lemma pc_eq_start_iff (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) (t : ℕ) (k : Fin n) :
    (exec x inr₀ σ t).pc k = .start ↔ k ∉ started σ t := by
  induction t with
  | zero => simp [init, started, Cslib.SWMR.pre]
  | succ t ih =>
    rw [exec_succ, started_succ, Finset.mem_insert, not_or]
    by_cases hk : k = σ t
    · subst hk
      simp only [not_true_eq_false, false_and, iff_false]
      exact step_pc_self_ne_start _ _
    · rw [step_pc_ne hk, ih]
      simp [hk]

/-! ### Theorem 2 -/

/-- **Theorem 2 (agreement)** of [Taubenfeld, Fig. 1], for `n ≥ 2`: in every execution (any
schedule, any failures — safety does not depend on the failure model), all processes that have
decided decided the same value. Covers Lemmas 3 and 4 (all pairs of the decision lines 7, 20, 25). -/
theorem theorem2_agreement (hn : 2 ≤ n) (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) (t : ℕ)
    {i j : Fin n} {v w : ℕ} (hi : (exec x inr₀ σ t).pc i = .done v)
    (hj : (exec x inr₀ σ t).pc j = .done w) : v = w := by
  have hI := inv_exec x inr₀ σ t
  have h1 := hI.li i; rw [hi] at h1
  have h2 := hI.li j; rw [hj] at h2
  obtain ⟨-, t1, ht1, rfl⟩ := h1
  obtain ⟨-, t2, ht2, rfl⟩ := h2
  rw [TagFact.unique hn ht1 ht2]

/-- **Theorem 2 (validity)** of [Taubenfeld, Fig. 1], for `n ≥ 2`: every decided value is the
input of a participating process. -/
theorem theorem2_validity (hn : 2 ≤ n) (x inr₀ : Fin n → ℕ) (σ : ℕ → Fin n) (t : ℕ)
    {i : Fin n} {v : ℕ} (hi : (exec x inr₀ σ t).pc i = .done v) :
    ∃ k ∈ started σ t, x k = v := by
  have hI := inv_exec x inr₀ σ t
  have h1 := hI.li i; rw [hi] at h1
  obtain ⟨-, tg, htg, rfl⟩ := h1
  have hpart : ∀ k, 0 < (exec x inr₀ σ t).st k → k ∈ started σ t := fun k hk => by
    by_contra h
    exact pc_ne_start_of_st_pos hI hk ((pc_eq_start_iff x inr₀ σ t k).2 h)
  cases tg with
  | ex y =>
    have hne : (univ.erase y).Nonempty := by
      rw [← card_pos, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
    obtain ⟨k, hk, hkv⟩ := exists_mem_eq_sup _ hne x
    have hky : k ≠ y := ne_of_mem_erase hk
    exact ⟨k, hpart k (lt_of_le_of_lt (Nat.zero_le _) (htg.1 k hky)), hkv.symm⟩
  | all =>
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    obtain ⟨k, -, hkv⟩ := exists_mem_eq_sup _ hne x
    exact ⟨k, hpart k (by rw [htg k]; omega), hkv.symm⟩

/-- Theorem 1 claims "for every `n ≥ 1`", but the algorithm of Fig. 1 violates validity for
`n = 1`: the single process passes the test `counter = n − 1 = 0` of line 7 at once and decides
the initial value `0` of `max`, whatever its input. -/
theorem fig1_invalid_n1 :
    (exec (n := 1) (fun _ => 5) (fun _ => 0) (fun _ => 0) 3).pc 0 = .done 0 ∧
      ∀ k : Fin 1, (fun _ => 5 : Fin 1 → ℕ) k ≠ 0 := by
  exact ⟨by decide, fun _ => by simp⟩

end Podc.WeakCrashFailures.Fig1
