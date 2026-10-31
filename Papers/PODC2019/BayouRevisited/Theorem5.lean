import Papers.PODC2019.BayouRevisited.Claim2

/-!
# Theorem 5: no ACT implementation of `F_seq` avoids temporary operation reordering

The run `H` of the proof: the partition phase; `p` catches up on `RB` messages (exactly as in
`H'`) and performs `m + 1` weak reads, the last one returning `x y` (Claim 1); `q` delivers only
its own messages and performs the rounds of `H''` (exactly as in `H''`, so one of its strong reads
returns `y`, Claim 2); finally the partition heals (everyone catches up on all `RB` messages and
all `TOB` messages, in a common total order) and all replicas read forever. This is a fair
stable run; `BEC(weak) ∧ SinOrd(strong) ∧ BEC(strong)` would force a cycle in `ar`.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {α : Type} {J : Impl n (SeqOp α) (SeqVal α)}

/-- `p`'s catch-up after the partition phase (as in `H'`). -/
noncomputable def P1 (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) : List J.Act :=
  J.PA p q x y ++ J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y))

/-- ... followed by `m + 1` weak reads of `p`. -/
noncomputable def PH0 (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) (m : ℕ) :
    List J.Act :=
  J.P1 p q x y ++ J.atR p (List.replicate (m + 1) (.inv .read .weak))

/-- `K` rounds of `q` after its own catch-up. -/
noncomputable def PH (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) (m K : ℕ) :
    List J.Act :=
  J.rounds q (Os q) .read (J.qblk q (J.PH0 p q x y m)) K

/-- The final total order of `TOB` messages: all of `q`'s, then all of `p`'s. -/
def Gf (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (P : List J.Act) : List (Fin n × ℕ) :=
  J.Gq q (J.loc q P) ++ J.Gq p (J.loc p P)

/-- The chain defining `H` (healing after `K1` rounds, then reads forever). -/
noncomputable def CH (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) (m K1 K : ℕ) :
    List J.Act :=
  J.blkFold (List.finRange n) (List.finRange n) (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)
    ++ (List.replicate K (J.readsOf (List.finRange n))).flatten

section H

variable (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α) (m : ℕ)
include hI hpq

lemma P1_spec : J.Valid (seqSpec α) (J.P1 p q x y) ∧ ∀ i', J.tobSeq i' (J.P1 p q x y) = [] := by
  have hc : ∀ pr ∈ ([] : List (Fin n × ℕ)),
      pr.2 < (J.tobCasts pr.1 (J.loc pr.1 (J.PA p q x y))).length := by simp
  refine ⟨(valid_blk hI (valid_PA hI p q x y).1 p (List.nodup_finRange n) List.nodup_nil
    (fun i' => by rw [tobSeq_PA]) hc).1, fun i' => ?_⟩
  by_cases h : i' = p
  · subst h; exact tobSeq_blk i' _ (by rw [tobSeq_PA]) hc
  · rw [P1, tobSeq_append, J.loc_atR_ne (Ne.symm h), tobSeq_PA]; rfl

lemma PH0_spec : J.Valid (seqSpec α) (J.PH0 p q x y m) ∧
    ∀ i', J.tobSeq i' (J.PH0 p q x y m) = [] := by
  obtain ⟨h1, h2⟩ := P1_spec hI hpq x y
  refine ⟨valid_append_invs h1 fun a ha => ?_, fun i' => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    rw [List.eq_of_mem_replicate hz]; exact ⟨p, _, _, rfl, Set.mem_univ _⟩
  · rw [PH0, tobSeq_append, h2, loc_atR]
    split_ifs <;> simp [List.filterMap_replicate, LIn.tobId]

lemma loc_PH0_q : J.loc q (J.PH0 p q x y m) = J.Ablk q y := by
  rw [PH0, P1, loc_append, loc_append, J.loc_atR_ne hpq, J.loc_atR_ne hpq, loc_PA_q hpq]; simp

lemma loc_qblk_PH0 : J.loc q (J.qblk q (J.PH0 p q x y m)) = J.loc q (J.Q0 q y) := by
  have h1 : J.loc q (J.PH0 p q x y m) = J.loc q (J.invBlk q (.append [y]) .weak []) := by
    rw [loc_PH0_q hI hpq, loc_invBlk_self]; simp [Ablk]
  rw [Q0, loc_qblk_self, loc_qblk_self, blk_qblk_congr h1, h1]

lemma PH_spec (K : ℕ) :
    J.Valid (seqSpec α) (J.PH p q x y m K) ∧
    (∀ i', J.tobSeq i' (J.PH p q x y m K) <+: J.Gq q (J.loc q (J.PH p q x y m K))) ∧
    J.loc q (J.PH p q x y m K) =
      J.qRoundsL q .read (J.loc q (J.qblk q (J.PH0 p q x y m))) K ∧
    (∃ R, J.PH p q x y m K = J.qblk q (J.PH0 p q x y m) ++ R ∧ OpsIn (· = SeqOp.read) R) ∧
    (∀ i, i ≠ q → ∃ δ, J.loc i (J.PH p q x y m K) = J.loc i (J.qblk q (J.PH0 p q x y m)) ++ δ ∧
      ∀ z ∈ δ, ¬ Licensing (seqSpec α) z) := by
  obtain ⟨h1, h2⟩ := PH0_spec hI hpq x y m
  obtain ⟨h3, h4⟩ := qblk_spec hI (q := q) h1 h2
  exact rounds_spec hI (Os_nodup q) (q_not_mem_Os q) (rd := SeqOp.read) (Set.mem_univ _)
    (Set.mem_univ _) Fseq_read_readOnly h3 h4 K

lemma loc_PH_q (K : ℕ) : J.loc q (J.PH p q x y m K) = J.loc q (J.C2 q y K) := by
  rw [(PH_spec hI hpq x y m K).2.2.1, (C2_spec hI q y K).2.2.1, loc_qblk_PH0 hI hpq]

lemma PH_mono {K K' : ℕ} (h : K ≤ K') : J.PH p q x y m K <+: J.PH p q x y m K' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    obtain ⟨R, hR⟩ := round_eq_cons q (Os q) .read (J.PH p q x y m _)
    simp only [PH, rounds] at hR ⊢
    rw [hR, List.append_assoc]; exact List.prefix_append _ _

end H

lemma CH_succ (p q : Fin n) (x y : α) (m K1 K : ℕ) :
    J.CH p q x y m K1 (K + 1) = J.CH p q x y m K1 K ++ J.readsOf (List.finRange n) := by
  simp [CH, List.replicate_succ', List.flatten_append]

lemma CH_chain (p q : Fin n) (x y : α) (m K1 : ℕ) : IsChain (J.CH p q x y m K1) where
  mono K := by rw [CH_succ]; exact List.prefix_append _ _
  grow K := by
    induction K with
    | zero => simp
    | succ K ih =>
      have := p.pos
      rw [CH_succ, List.length_append]; simp [readsOf]; omega

section CH

variable (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α) (m K1 : ℕ)
include hI hpq

lemma Gf_nodup (P : List J.Act) : (J.Gf p q P).Nodup := by
  rw [Gf, List.nodup_append]
  refine ⟨Gq_nodup _ _, Gq_nodup _ _, ?_⟩
  intro a ha b hb hab
  subst hab
  exact hpq ((mem_Gq hb).1.symm.trans (mem_Gq ha).1)

lemma FH_spec :
    J.Valid (seqSpec α) (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) ∧
    (∀ r ∉ List.finRange n, J.loc r (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) = J.loc r (J.PH p q x y m K1)) ∧
    (∀ r ∈ List.finRange n, J.Passive r (J.lstate r (J.loc r (J.blkFold (List.finRange n)
      (List.finRange n) (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1))))) ∧
    (∀ r ∈ List.finRange n, J.tobSeq r (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) = J.Gf p q (J.PH p q x y m K1)) ∧
    (∀ r', J.tobSeq r' (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) <+: J.Gf p q (J.PH p q x y m K1)) ∧
    (∀ r ∈ List.finRange n, ∀ j ∈ List.finRange n,
      ∀ k < (J.rbCasts j (J.loc j (J.PH p q x y m K1))).length,
      ∃ m', LIn.rb j k m' ∈ J.loc r (J.blkFold (List.finRange n) (List.finRange n)
        (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1))) ∧
    (∀ r, ∃ δ, J.loc r (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) = J.loc r (J.PH p q x y m K1) ++ δ ∧
      ∀ z ∈ δ, ¬ Licensing (seqSpec α) z) ∧
    J.PH p q x y m K1 <+: J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1) := by
  obtain ⟨hV, hpre, -⟩ := PH_spec hI hpq x y m K1
  refine blkFold_spec hI (List.nodup_finRange n) (Gf_nodup hI hpq _) _ _ (List.nodup_finRange n)
    hV (fun i' => (hpre i').trans (List.prefix_append _ _)) ?_
  intro pr hpr
  rcases List.mem_append.1 hpr with h | h
  · obtain ⟨h1, h2⟩ := mem_Gq h; rw [h1]; exact h2
  · obtain ⟨h1, h2⟩ := mem_Gq h; rw [h1]; exact h2

lemma CH_valid (K : ℕ) : J.Valid (seqSpec α) (J.CH p q x y m K1 K) := by
  induction K with
  | zero => simpa [CH] using (FH_spec hI hpq x y m K1).1
  | succ K ih =>
    rw [CH_succ]
    exact valid_append_invs ih fun a ha => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; exact ⟨r, _, _, rfl, Set.mem_univ _⟩

lemma CH_loc (K : ℕ) (i : Fin n) :
    J.loc i (J.CH p q x y m K1 K) = J.loc i (J.blkFold (List.finRange n) (List.finRange n)
      (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)) ++
      List.replicate K (.inv .read .weak) := by
  induction K with
  | zero => simp [CH]
  | succ K ih =>
    rw [CH_succ, loc_append, ih, readsOf, loc_reads (List.nodup_finRange n),
      if_pos (List.mem_finRange i), List.replicate_succ', List.append_assoc]

lemma PA_prefix_PH (K : ℕ) : J.PA p q x y <+: J.PH p q x y m K := by
  obtain ⟨R, hR, -⟩ := (PH_spec hI hpq x y m K).2.2.2.1
  rw [hR, qblk, PH0, P1]; simp only [List.append_assoc]; exact List.prefix_append _ _

lemma CH_casts (hK1 : 0 < K1) (K : ℕ) (j : Fin n) :
    (J.rbCasts j (J.loc j (J.CH p q x y m K1 K))).length ≤
      (J.rbCasts j (J.loc j (J.PH p q x y m K1))).length ∧
    (J.tobCasts j (J.loc j (J.CH p q x y m K1 K))).length ≤
      (J.tobCasts j (J.loc j (J.PH p q x y m K1))).length ∧
    (j ≠ p → j ≠ q → J.tobCasts j (J.loc j (J.CH p q x y m K1 K)) = []) := by
  obtain ⟨δf, hδf, hδfl⟩ := (FH_spec hI hpq x y m K1).2.2.2.2.2.2.1 j
  have hrd : ∀ z ∈ List.replicate K (LIn.inv SeqOp.read Level.weak : J.Input),
      ¬ Licensing (seqSpec α) z := fun z hz => by
    rw [List.eq_of_mem_replicate hz]; exact not_licensing_read
  -- a quiet prefix `ℓ0` of the local inputs of `j` and its non-licensing rest
  obtain ⟨ℓ0, δ, hloc, hq0, hδ, hpre0, hother⟩ : ∃ ℓ0 δ,
      J.loc j (J.CH p q x y m K1 K) = ℓ0 ++ δ ∧ Quiet (seqSpec α) j ℓ0 ∧
      (∀ z ∈ δ, ¬ Licensing (seqSpec α) z) ∧ ℓ0 <+: J.loc j (J.PH p q x y m K1) ∧
      (j ≠ p → j ≠ q → ℓ0 = []) := by
    by_cases hjq : j = q
    · subst j
      refine ⟨J.loc q (J.PH p q x y m K1), δf ++ List.replicate K (.inv .read .weak), ?_, ?_,
        ?_, List.prefix_refl _, fun _ h => absurd rfl h⟩
      · rw [CH_loc hI hpq, hδf, List.append_assoc]
      · left
        obtain ⟨K', rfl⟩ : ∃ K', K1 = K' + 1 := ⟨K1 - 1, by omega⟩
        obtain ⟨hV', hpr', -⟩ := PH_spec hI hpq x y m K'
        have hRS := round_spec hI (Os_nodup q) (q_not_mem_Os q) (rd := SeqOp.read)
          (Set.mem_univ _) (Set.mem_univ _) Fseq_read_readOnly hV' hpr'
        obtain ⟨R, hR⟩ := round_eq_cons q (Os q) .read (J.PH p q x y m K')
        refine ⟨?_, hRS.2.2.2.2.1⟩
        apply List.ne_nil_of_mem (a := LIn.inv SeqOp.read Level.strong)
        simp only [PH, rounds] at hR ⊢
        rw [hR, loc_append, loc_append, loc_singleton, if_pos rfl]; simp
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hδfl z hz
        · exact hrd z hz
    · obtain ⟨δr, hδr, hδrl⟩ := (PH_spec hI hpq x y m K1).2.2.2.2 j hjq
      refine ⟨J.loc j (J.PA p q x y), J.loc j (J.atR p (J.blk p (List.finRange n) []
        (J.PA p q x y))) ++ J.loc j (J.atR p (List.replicate (m + 1) (.inv .read .weak))) ++
        δr ++ δf ++ List.replicate K (.inv .read .weak), ?_, quiet_PA hI hpq x y j, ?_,
        loc_prefix (PA_prefix_PH hI hpq x y m K1) j, fun h1 h2 => loc_PA_other h1 h2 x y⟩
      · rw [CH_loc hI hpq, hδf, hδr, loc_qblk_ne hjq, PH0, P1]
        simp only [loc_append, List.append_assoc]
      · intro z hz
        simp only [List.mem_append] at hz
        rcases hz with (((hz | hz) | hz) | hz) | hz
        · rw [loc_atR] at hz; split_ifs at hz
          · exact not_licensing_blk _ _ _ _ z hz
          · simp at hz
        · rw [loc_atR] at hz; split_ifs at hz
          · rw [List.eq_of_mem_replicate hz]; exact not_licensing_read
          · simp at hz
        · exact hδrl z hz
        · exact hδfl z hz
        · exact hrd z hz
  have hc := no_casts_of_quiet hI (CH_valid hI hpq x y m K1 K) hloc hq0 hδ
  rw [← hloc] at hc
  refine ⟨?_, ?_, fun h1 h2 => ?_⟩
  · rw [hc.1]; exact rbCasts_length_mono hpre0 j
  · rw [hc.2]; exact tobCasts_length_mono hpre0 j
  · rw [hc.2, hother h1 h2]; rfl

lemma CH_stable (hK1 : 0 < K1) (a₀ : J.Act) :
    J.IsStableRun (seqSpec α) (limRun (J.CH p q x y m K1) a₀) := by
  have hF := FH_spec hI hpq x y m K1
  have hFC : ∀ K, J.blkFold (List.finRange n) (List.finRange n) (J.Gf p q (J.PH p q x y m K1))
      (J.PH p q x y m K1) <+: J.CH p q x y m K1 K := fun K => List.prefix_append _ _
  apply isStableRun_lim (CH_chain p q x y m K1) a₀ (CH_valid hI hpq x y m K1)
  · intro K i
    refine ⟨.inv .read .weak, ?_, trivial⟩
    rw [CH_succ, List.drop_left]
    exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  · intro K i
    have := lstate_reads hI Fseq_read_readOnly (Set.mem_univ _)
      (List.replicate (K + 1) (J.readsOf (List.finRange n))).flatten
      (CH_valid hI hpq x y m K1 (K + 1)) (fun a ha => by
        simp only [List.mem_flatten, List.mem_replicate] at ha
        obtain ⟨L, ⟨-, rfl⟩, ha⟩ := ha
        obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; rfl) i
    simp only [CH] at this ⊢
    rw [this]; exact hF.2.2.1 i (List.mem_finRange i)
  · intro K i j k hk
    have h1 := (CH_casts hI hpq x y m K1 hK1 K j).1
    obtain ⟨m', hm'⟩ := hF.2.2.2.2.2.1 i (List.mem_finRange i) j (List.mem_finRange j) k
      (lt_of_lt_of_le hk h1)
    exact ⟨m', (hFC (K + 1)).subset (mem_of_mem_loc hm')⟩
  · intro K i j k hk
    obtain ⟨h1, -, h3⟩ := CH_casts hI hpq x y m K1 hK1 K j
    have hk' := lt_of_lt_of_le hk (CH_casts hI hpq x y m K1 hK1 K j).2.1
    have hmem : (j, k) ∈ J.Gf p q (J.PH p q x y m K1) := by
      by_cases hjq : j = q
      · subst j; exact List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩)
      by_cases hjp : j = p
      · subst j; exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩)
      · rw [h3 hjp hjq] at hk; simp at hk
    rw [← hF.2.2.2.1 i (List.mem_finRange i)] at hmem
    obtain ⟨z, hz, hze⟩ := List.mem_filterMap.1 hmem
    cases z <;> simp [LIn.tobId] at hze
    obtain ⟨rfl, rfl⟩ := hze
    exact ⟨_, (hFC (K + 1)).subset (mem_of_mem_loc hz)⟩

end CH

/-- The contradiction: if a late weak read of `p` in `H'` returns `x y`, then `H` (a fair stable
run) has no abstract execution satisfying `BEC(weak) ∧ SinOrd(strong) ∧ BEC(strong)`. -/
theorem main_contra (hI : J.IsACT (seqSpec α)) (hyp : J.T5Hyp) {p q : Fin n} (hpq : p ≠ q)
    {x y : α} (hxy : x ≠ y) (m : ℕ)
    (hv : J.immVal p (J.Lp p q x y ++ List.replicate m (.inv .read .weak)) .read =
      some (.word [x, y])) : False := by
  classical
  obtain ⟨K, K1, hKK1, hresp⟩ := claim2 hI hyp q y
  rw [← loc_PH_q hI hpq x y m, ← loc_PH_q hI hpq x y m] at hresp
  set C := J.CH p q x y m K1 with hCdef
  have hC : IsChain C := CH_chain p q x y m K1
  set a₀ : J.Act := (q, .inv .read .weak)
  set r := limRun C a₀ with hr
  have hrun := CH_stable hI hpq x y m K1 (by omega) a₀
  obtain ⟨A, hAH, hWF, ⟨-, -, hRVw⟩, hSin, ⟨-, -, hRVs⟩⟩ := hyp.1 r hrun
  have hrv : ∀ e, A.rval e = J.rvalOf r e := fun e => congrArg (fun H => H.rval e) hAH
  have hop : ∀ e, A.op e = (J.history r).op e := fun e => congrArg (fun H => H.op e) hAH
  have hlv : ∀ e, A.lvl e = (J.history r).lvl e := fun e => congrArg (fun H => H.lvl e) hAH
  have hrC : ∀ K' t (ht : t < (C K').length), r t = (C K')[t] := fun K' t ht => hC.limRun_eq a₀ ht
  -- prefixes
  obtain ⟨hF1, -, -, -, -, -, -, hPHF⟩ := FH_spec hI hpq x y m K1
  have hPHC : J.PH p q x y m K1 <+: C 0 := by simpa [hCdef, CH] using hPHF
  have hpref : ∀ L, L <+: J.PH p q x y m K1 → ∀ t (ht : t < L.length), r t = L[t] := by
    intro L hL t ht
    have h := hL.trans hPHC
    rw [hrC 0 t (lt_of_lt_of_le ht h.length_le)]; exact (h.getElem ht).symm
  obtain ⟨Rr, hRr, hRro⟩ := (PH_spec hI hpq x y m K1).2.2.2.1
  have hPA : J.PA p q x y <+: J.PH p q x y m K1 := PA_prefix_PH hI hpq x y m K1
  have hPH0 : J.PH0 p q x y m <+: J.PH p q x y m K1 := by
    rw [hRr, qblk, List.append_assoc]; exact List.prefix_append _ _
  have htake : ∀ (L : List J.Act), L <+: C 0 → ∀ t ≤ L.length, J.pre r t = L.take t := by
    intro L hL t ht
    rw [pre, hC.pre_eq a₀ (K := 0) (ht.trans hL.length_le)]
    obtain ⟨R, hR⟩ := hL; rw [← hR, List.take_append_of_le_length ht]
  -- the two appends
  have r0 : r 0 = (p, J.appIn x) := by
    rw [hpref _ hPA 0 (by rw [PA_eq]; simp), PA_getElem_zero]
  have rtb : r (J.tb p x) = (q, J.appIn y) := by
    rw [hpref _ hPA _ (tb_lt p q x y), PA_getElem_tb]
  let ea : J.Ev r := ⟨0, by rw [r0]; trivial⟩
  let eb : J.Ev r := ⟨J.tb p x, by rw [rtb]; trivial⟩
  have hne : ea ≠ eb := by
    intro h; have := congrArg Subtype.val h; simp [ea, eb, tb_eq] at this; omega
  have hopa : A.op ea = .append [x] := by rw [hop]; exact history_op ea r0
  have hopb : A.op eb = .append [y] := by rw [hop]; exact history_op eb rtb
  have hlva : A.lvl ea = .weak := by rw [hlv]; exact history_lvl ea r0
  -- the only appends
  have honly : ∀ e : J.Ev r, ∀ s, A.op e = .append s → e = ea ∨ e = eb := by
    intro e s hs
    obtain ⟨op, l, hx⟩ := LIn.exists_of_isInv e.2
    have he : r e.1 = ((r e.1).1, .inv op l) := by rw [← hx]
    rw [hop, history_op e he] at hs
    subst hs
    have ht : e.1 < (C (e.1 + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self _) (hC.grow _)
    have hre := hrC _ _ ht
    obtain ⟨Rf, hRf, hRfo⟩ := blkFold_opsIn (I := J) (· = SeqOp.read) (List.finRange n)
      (List.finRange n) (J.Gf p q (J.PH p q x y m K1)) (J.PH p q x y m K1)
    have hCe : C (e.1 + 1) = J.PA p q x y ++
        (J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y)) ++
          J.atR p (List.replicate (m + 1) (.inv .read .weak)) ++
          J.atR q (J.blk q [q] (J.Gq q (J.loc q (J.PH0 p q x y m))) (J.PH0 p q x y m)) ++
          Rr ++ Rf ++ (List.replicate (e.1 + 1) (J.readsOf (List.finRange n))).flatten) := by
      have h1 : C (e.1 + 1) = J.PH p q x y m K1 ++
          (Rf ++ (List.replicate (e.1 + 1) (J.readsOf (List.finRange n))).flatten) := by
        simp only [hCdef, CH, hRf, List.append_assoc]
      have hPH0eq : J.PH0 p q x y m = J.PA p q x y ++
          (J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y)) ++
            J.atR p (List.replicate (m + 1) (.inv .read .weak))) := by
        simp only [PH0, P1, List.append_assoc]
      rw [h1, hRr, qblk]
      nth_rewrite 1 [hPH0eq]
      simp only [List.append_assoc]
    have hops : OpsIn (I := J) (· = SeqOp.read)
        (J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y)) ++
          J.atR p (List.replicate (m + 1) (.inv .read .weak)) ++
          J.atR q (J.blk q [q] (J.Gq q (J.loc q (J.PH0 p q x y m))) (J.PH0 p q x y m)) ++
          Rr ++ Rf ++ (List.replicate (e.1 + 1) (J.readsOf (List.finRange n))).flatten) := by
      refine OpsIn.append (OpsIn.append (OpsIn.append (OpsIn.append (OpsIn.append ?_ ?_) ?_)
        hRro) hRfo) ?_
      · intro a ha op' l' h'
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
        exact absurd h' (not_inv_blk _ _ _ _ z hz op' l')
      · intro a ha op' l' h'
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
        rw [List.eq_of_mem_replicate hz] at h'; cases h'; rfl
      · intro a ha op' l' h'
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
        exact absurd h' (not_inv_blk _ _ _ _ z hz op' l')
      · intro a ha op' l' h'
        simp only [List.mem_flatten, List.mem_replicate] at ha
        obtain ⟨L, ⟨-, rfl⟩, ha⟩ := ha
        obtain ⟨r', -, rfl⟩ := List.mem_map.1 ha
        cases h'; rfl
    have h1 : (C (e.1 + 1))[e.1] = ((r e.1).1, .inv (.append s) l) := by rw [← hre, he]
    simp only [hCe] at h1 ht
    obtain ⟨hlt, hPAe⟩ := getElem_of_opsIn hops ht h1 (by simp)
    rcases PA_app hlt hPAe with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0
  -- the weak read `er` of `p` returns `x y`
  have hP1len : (J.P1 p q x y).length + m < (J.PH0 p q x y m).length := by
    simp [PH0]
  have rr : r ((J.P1 p q x y).length + m) = (p, .inv .read .weak) := by
    rw [hpref _ hPH0 _ hP1len]
    simp only [PH0]
    rw [List.getElem_append_right (by omega)]; simp [atR]
  let er : J.Ev r := ⟨(J.P1 p q x y).length + m, by rw [rr]; trivial⟩
  have hlvr : A.lvl er = .weak := by rw [hlv]; exact history_lvl er rr
  have hvalr : A.rval er = some (.word [x, y]) := by
    obtain ⟨v, hv1, hv2⟩ := rvalOf_weak hI hrun.1.1 er rr Fseq_read_readOnly (Set.mem_univ _)
    rw [hrv, hv2, ← hv1]
    have hpre_r : J.pre r er.1 = J.P1 p q x y ++ J.atR p (List.replicate m (.inv .read .weak)) := by
      rw [htake _ (hPH0.trans hPHC) _ hP1len.le, PH0, List.take_append,
        List.take_of_length_le (by omega), show (J.P1 p q x y).length + m -
          (J.P1 p q x y).length = m by omega, atR_take, List.take_replicate,
        min_eq_left (by omega)]
    simp only [er] at hpre_r ⊢
    rw [hpre_r, loc_append, loc_atR_self]
    exact hv
  -- the strong read `ex` of `q` returns `y`
  have hKle : J.PH p q x y m (K + 1) <+: J.PH p q x y m K1 := PH_mono hI hpq x y m hKK1
  obtain ⟨Rx, hRx⟩ := round_eq_cons q (Os q) .read (J.PH p q x y m K)
  have hxlt : (J.PH p q x y m K).length < (J.PH p q x y m (K + 1)).length := by
    simp only [PH, rounds] at hRx ⊢; rw [hRx]; simp
  have rx : r (J.PH p q x y m K).length = (q, .inv .read .strong) := by
    rw [hpref _ hKle _ hxlt]
    simp only [PH, rounds] at hRx ⊢
    simp only [hRx]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (le_refl _)]; simp
  let ex : J.Ev r := ⟨(J.PH p q x y m K).length, by rw [rx]; trivial⟩
  have hlvx : A.lvl ex = .strong := by rw [hlv]; exact history_lvl ex rx
  have hvalx : A.rval ex = some (.word [y]) := by
    rw [hrv]
    apply rvalOf_eq_of_lresp ex (T := (C 0).length)
    have hq : (r ex.1).1 = q := by simp only [ex]; rw [rx]
    rw [hq, lidx_eq rx, pre_limRun hC]
    rw [htake _ ((PH_mono hI hpq x y m hKK1.le).trans hPHC) _ le_rfl, List.take_length]
    exact lresp_mono (loc_prefix hPHC q) hresp
  -- the contradiction
  have hopr : A.op er = .read := by rw [hop]; exact history_op er rr
  have hopx : A.op ex = .read := by rw [hop]; exact history_op ex rx
  have hsub : ∀ e, appends (A.context e) ⊆ {ea, eb} := by
    rintro e z ⟨-, s, hs⟩
    rcases honly z s hs with rfl | rfl <;> simp
  have h1 : Fseq SeqOp.read (A.context er) = .word [x, y] := by
    have := hRVw er hlvr
    rw [hvalr, hopr] at this
    exact (Option.some.inj this).symm
  obtain ⟨-, -, hab⟩ :=
    (Fseq_read_two (A.context er) hne (hsub er) hopa hopb hxy hWF.ar_total).1 h1
  have h2 : Fseq SeqOp.read (A.context ex) = .word [y] := by
    have := hRVs ex hlvx
    rw [hvalx, hopx] at this
    exact (Option.some.inj this).symm
  obtain ⟨hbx, hax⟩ :=
    (Fseq_read_two (A.context ex) hne (hsub ex) hopa hopb hxy hWF.ar_total).2.1 h2
  have hvbx : A.vis eb ex := hbx.1
  have hvax : ¬ A.vis ea ex := fun h => hax ⟨h, _, hopa⟩
  obtain ⟨E', hE', hiff⟩ := hSin
  have harb : A.ar eb ex := ((hiff eb ex hlvx).1 hvbx).1
  have hea : ea ∉ E' := by
    intro h
    have := hE' ea h
    rw [hRVw ea hlva] at this
    cases this
  exact hvax ((hiff ea ex hlvx).2 ⟨hWF.ar_total.trans _ _ _ hab harb, hea⟩)

end Podc.BayouRevisited.Impl
