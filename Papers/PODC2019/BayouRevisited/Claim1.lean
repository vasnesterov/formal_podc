import Papers.PODC2019.BayouRevisited.Theorem5Setup

/-!
# Claim 1 of the proof of Theorem 5 (the asynchronous run `H'`)

After the partition phase, the partition heals for `RB` only: every replica catches up on all
`RB` messages and runs until passive (`p` first, then `q`, then the others); then all replicas
invoke weak reads forever. No message is ever `TOB`-delivered: this is a fair asynchronous run.
If the implementation satisfies `BEC(weak, F_seq)` in it, then (according to the arbitration
order of the two appends) a late read of `p` returns `x y`, or a late read of `q` returns `y x`.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {α : Type} {J : Impl n (SeqOp α) (SeqVal α)}

/-- The hypothesis of Theorem 5 on an implementation. -/
def T5Hyp (J : Impl n (SeqOp α) (SeqVal α)) : Prop :=
  (∀ r, J.IsStableRun (seqSpec α) r → (J.history r).Satisfies
      fun A => A.BEC .weak Fseq ∧ A.SinOrd .strong ∧ A.BEC .strong Fseq) ∧
  (∀ r, J.IsAsyncRun (seqSpec α) r ∨ J.IsStableRun (seqSpec α) r →
      (J.history r).Satisfies fun A => A.BEC .weak Fseq)

/-- The order of catch-up in `H'`: `p`, `q`, then the others. -/
def RsH (p q : Fin n) : List (Fin n) :=
  p :: q :: (List.finRange n).filter fun r => r ≠ p ∧ r ≠ q

lemma RsH_nodup {p q : Fin n} (hpq : p ≠ q) : (RsH p q).Nodup := by
  simp only [RsH, List.nodup_cons, List.mem_cons, List.mem_filter, not_or]
  refine ⟨⟨hpq, by simp⟩, by simp, (List.nodup_finRange n).filter _⟩

lemma mem_RsH (p q r : Fin n) : r ∈ RsH p q := by
  simp only [RsH, List.mem_cons, List.mem_filter, List.mem_finRange, true_and]
  by_cases h1 : r = p
  · exact Or.inl h1
  by_cases h2 : r = q
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr (by simp [h1, h2]))

/-- One weak read by every replica of `Rs`. -/
def readsOf (J : Impl n (SeqOp α) (SeqVal α)) (Rs : List (Fin n)) : List J.Act :=
  Rs.map fun r => (r, .inv .read .weak)

/-- The finite part of `H'`. -/
noncomputable def Fp (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) : List J.Act :=
  J.blkFold (RsH p q) (List.finRange n) [] (J.PA p q x y)

/-- The chain defining `H'`. -/
noncomputable def Cp (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) (K : ℕ) :
    List J.Act :=
  J.Fp p q x y ++ (List.replicate K (J.readsOf (RsH p q))).flatten

/-- The local inputs of `p` after its catch-up (the same in `H'` and `H`). -/
noncomputable def Lp (J : Impl n (SeqOp α) (SeqVal α)) (p q : Fin n) (x y : α) : List J.Input :=
  J.loc p (J.PA p q x y ++ J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y)))

lemma not_licensing_read : ¬ Licensing (seqSpec α) (LIn.inv (SeqOp.read) .weak : J.Input) := by
  rintro ⟨op, l, h, hl⟩; cases h; exact hl ⟨rfl, Fseq_read_readOnly⟩

lemma quiet_PA (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α) (j : Fin n) :
    Quiet (seqSpec α) j (J.loc j (J.PA p q x y)) := by
  by_cases hp : j = p
  · subst hp; left; rw [loc_PA_p hpq]; exact ⟨by simp [Ablk], passive_Ablk_p hI hpq x y⟩
  by_cases hq : j = q
  · subst hq; left; rw [loc_PA_q hpq]; exact ⟨by simp [Ablk], passive_Ablk_q hI hpq x y⟩
  right; rw [loc_PA_other hp hq]; simp

lemma Cp_succ (p q : Fin n) (x y : α) (K : ℕ) :
    J.Cp p q x y (K + 1) = J.Cp p q x y K ++ J.readsOf (RsH p q) := by
  simp [Cp, List.replicate_succ', List.flatten_append]

section H'

variable (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α)
include hI hpq

lemma Fp_spec' :
    J.Valid (seqSpec α) (J.Fp p q x y) ∧
    (∀ r ∉ RsH p q, J.loc r (J.Fp p q x y) = J.loc r (J.PA p q x y)) ∧
    (∀ r ∈ RsH p q, J.Passive r (J.lstate r (J.loc r (J.Fp p q x y)))) ∧
    (∀ r ∈ RsH p q, J.tobSeq r (J.Fp p q x y) = []) ∧
    (∀ r', J.tobSeq r' (J.Fp p q x y) <+: []) ∧
    (∀ r ∈ RsH p q, ∀ j ∈ List.finRange n, ∀ k < (J.rbCasts j (J.loc j (J.PA p q x y))).length,
      ∃ m, LIn.rb j k m ∈ J.loc r (J.Fp p q x y)) ∧
    (∀ r, ∃ δ, J.loc r (J.Fp p q x y) = J.loc r (J.PA p q x y) ++ δ ∧
      ∀ z ∈ δ, ¬ Licensing (seqSpec α) z) ∧
    J.PA p q x y <+: J.Fp p q x y :=
  blkFold_spec hI (List.nodup_finRange n) List.nodup_nil (RsH p q) (J.PA p q x y)
    (RsH_nodup hpq) (valid_PA hI p q x y).1 (fun i' => by rw [tobSeq_PA]) (by simp)

lemma Cp_valid (K : ℕ) : J.Valid (seqSpec α) (J.Cp p q x y K) := by
  induction K with
  | zero => simpa [Cp] using (Fp_spec' hI hpq x y).1
  | succ K ih =>
    rw [Cp_succ]
    exact valid_append_invs ih fun a ha => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; exact ⟨r, _, _, rfl, Set.mem_univ _⟩

lemma Cp_loc (K : ℕ) (i : Fin n) :
    J.loc i (J.Cp p q x y K) = J.loc i (J.Fp p q x y) ++ List.replicate K (.inv .read .weak) := by
  induction K with
  | zero => simp [Cp]
  | succ K ih =>
    rw [Cp_succ, loc_append, ih, readsOf, loc_reads (RsH_nodup hpq), if_pos (mem_RsH p q i),
      List.replicate_succ', List.append_assoc]

lemma Cp_chain : IsChain (J.Cp p q x y) where
  mono K := by rw [Cp_succ]; exact List.prefix_append _ _
  grow K := by
    induction K with
    | zero => simp
    | succ K ih => rw [Cp_succ, List.length_append]; simp [readsOf, RsH]; omega

lemma Cp_lstate (K : ℕ) (i : Fin n) :
    J.lstate i (J.loc i (J.Cp p q x y K)) = J.lstate i (J.loc i (J.Fp p q x y)) := by
  have := lstate_reads hI Fseq_read_readOnly (Set.mem_univ _) (P := J.Fp p q x y)
    (List.replicate K (J.readsOf (RsH p q))).flatten (Cp_valid hI hpq x y K)
    (fun a ha => by
      simp only [List.mem_flatten, List.mem_replicate] at ha
      obtain ⟨L, ⟨-, rfl⟩, ha⟩ := ha
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; rfl) i
  exact this

lemma Cp_casts (K : ℕ) (j : Fin n) :
    J.rbCasts j (J.loc j (J.Cp p q x y K)) = J.rbCasts j (J.loc j (J.PA p q x y)) ∧
      J.tobCasts j (J.loc j (J.Cp p q x y K)) = J.tobCasts j (J.loc j (J.PA p q x y)) := by
  obtain ⟨δ, hδ, hδl⟩ := (Fp_spec' hI hpq x y).2.2.2.2.2.2.1 j
  have hloc : J.loc j (J.Cp p q x y K) = J.loc j (J.PA p q x y) ++
      (δ ++ List.replicate K (.inv .read .weak)) := by
    rw [Cp_loc hI hpq, hδ, List.append_assoc]
  have := no_casts_of_quiet hI (Cp_valid hI hpq x y K) hloc (quiet_PA hI hpq x y j)
    (fun z hz => by
      rcases List.mem_append.1 hz with hz | hz
      · exact hδl z hz
      · rw [List.eq_of_mem_replicate hz]; exact not_licensing_read)
  rwa [← hloc] at this

lemma Cp_tobSeq (K : ℕ) (i : Fin n) : J.tobSeq i (J.Cp p q x y K) = [] := by
  have h := (Fp_spec' hI hpq x y).2.2.2.2.1 i
  have h2 : J.tobSeq i (J.Fp p q x y) = [] := List.eq_nil_of_prefix_nil h
  simp only [tobSeq] at h2 ⊢
  rw [Cp_loc hI hpq, List.filterMap_append, h2]
  simp [List.filterMap_replicate, LIn.tobId]

lemma Cp_async (a₀ : J.Act) : J.IsAsyncRun (seqSpec α) (limRun (J.Cp p q x y) a₀) := by
  apply isAsyncRun_lim_noTob (Cp_chain hI hpq x y) a₀ (Cp_valid hI hpq x y)
  · intro K i
    refine ⟨.inv .read .weak, ?_, trivial⟩
    rw [Cp_succ, List.drop_left]
    exact List.mem_map.2 ⟨i, mem_RsH p q i, rfl⟩
  · intro K i
    rw [Cp_lstate hI hpq]
    exact (Fp_spec' hI hpq x y).2.2.1 i (mem_RsH p q i)
  · intro K i j k hk
    rw [(Cp_casts hI hpq x y K j).1] at hk
    obtain ⟨m, hm⟩ := (Fp_spec' hI hpq x y).2.2.2.2.2.1 i (mem_RsH p q i) j
      (List.mem_finRange j) k hk
    refine ⟨m, ?_⟩
    rw [Cp_succ, Cp]
    apply List.mem_append_left; apply List.mem_append_left
    exact mem_of_mem_loc hm
  · intro K i j k m hm
    have h1 : LIn.tob j k m ∈ J.loc i (J.Cp p q x y K) := by
      simp only [loc, List.mem_filterMap]
      exact ⟨(i, .tob j k m), hm, by simp⟩
    have h2 : (j, k) ∈ J.tobSeq i (J.Cp p q x y K) := List.mem_filterMap.2 ⟨_, h1, rfl⟩
    rw [Cp_tobSeq hI hpq] at h2; simp at h2

end H'

section H'

variable (hI : J.IsACT (seqSpec α)) {p q : Fin n} (hpq : p ≠ q) (x y : α)
include hI hpq

lemma Fp_loc_p : J.loc p (J.Fp p q x y) = J.Lp p q x y := by
  rw [Fp, RsH, blkFold, blkFold_loc_not_mem]
  · rfl
  · simp only [List.mem_cons, List.mem_filter, not_or]
    exact ⟨hpq, by simp⟩

lemma Fp_loc_q : J.loc q (J.Fp p q x y) = J.Lp q p y x := by
  set P1 := J.PA p q x y ++ J.atR p (J.blk p (List.finRange n) [] (J.PA p q x y))
  have hV1 : J.Valid (seqSpec α) P1 :=
    (valid_blk hI (valid_PA hI p q x y).1 p (List.nodup_finRange n) List.nodup_nil
      (fun i' => by rw [tobSeq_PA]) (by simp)).1
  rw [Fp, RsH, blkFold, blkFold, blkFold_loc_not_mem]
  · rw [Lp, loc_append, loc_append, loc_append, loc_atR_self, J.loc_atR_ne hpq, loc_atR_self,
      List.append_nil, loc_PA_q hpq, loc_PA_p (Ne.symm hpq)]
    congr 1
    apply blk_congr
    · rw [loc_append, J.loc_atR_ne hpq, List.append_nil, loc_PA_q hpq, loc_PA_p (Ne.symm hpq)]
    · intro j
      by_cases hjp : j = p
      · subst hjp
        rw [loc_PA_q (Ne.symm hpq)]
        have hl : J.loc j P1 = J.Ablk j x ++ J.blk j (List.finRange n) [] (J.PA j q x y) := by
          rw [loc_append, loc_atR_self, loc_PA_p hpq]
        have := no_casts_of_quiet hI hV1 hl (Or.inl ⟨by simp [Ablk], passive_Ablk_p hI hpq x y⟩)
          (not_licensing_blk _ _ _ _)
        rw [hl, this.1]
      by_cases hjq : j = q
      · subst hjq
        rw [loc_append, J.loc_atR_ne hpq, List.append_nil, loc_PA_q hpq, loc_PA_p (Ne.symm hpq)]
      · rw [loc_append, J.loc_atR_ne (Ne.symm hjp), List.append_nil, loc_PA_other hjp hjq,
          loc_PA_other hjq hjp]
    · intro j
      by_cases hjp : j = p
      · subst hjp
        rw [loc_PA_q (Ne.symm hpq)]
        have hl : J.loc j P1 = J.Ablk j x ++ J.blk j (List.finRange n) [] (J.PA j q x y) := by
          rw [loc_append, loc_atR_self, loc_PA_p hpq]
        have := no_casts_of_quiet hI hV1 hl (Or.inl ⟨by simp [Ablk], passive_Ablk_p hI hpq x y⟩)
          (not_licensing_blk _ _ _ _)
        rw [hl, this.2]
      by_cases hjq : j = q
      · subst hjq
        rw [loc_append, J.loc_atR_ne hpq, List.append_nil, loc_PA_q hpq, loc_PA_p (Ne.symm hpq)]
      · rw [loc_append, J.loc_atR_ne (Ne.symm hjp), List.append_nil, loc_PA_other hjp hjq,
          loc_PA_other hjq hjp]
  · simp
end H'


lemma Cp_length_succ (p q : Fin n) (x y : α) (K : ℕ) :
    (J.Cp p q x y (K + 1)).length = (J.Cp p q x y K).length + (RsH p q).length := by
  rw [Cp_succ, List.length_append]; simp [readsOf]

/-- **Claim 1** of the proof of Theorem 5. -/
theorem claim1 (hI : J.IsACT (seqSpec α)) (hyp : J.T5Hyp) {p q : Fin n} (hpq : p ≠ q)
    {x y : α} (hxy : x ≠ y) :
    (∃ m, J.immVal p (J.Lp p q x y ++ List.replicate m (.inv .read .weak)) .read =
        some (.word [x, y])) ∨
    (∃ m, J.immVal q (J.Lp q p y x ++ List.replicate m (.inv .read .weak)) .read =
        some (.word [y, x])) := by
  classical
  set C := J.Cp p q x y with hCdef
  have hC : IsChain C := Cp_chain hI hpq x y
  set a₀ : J.Act := (p, .inv .read .weak)
  set r := limRun C a₀ with hr
  have hrun := Cp_async hI hpq x y a₀
  obtain ⟨A, hAH, hWF, hEV, -, hRV⟩ := hyp.2 r (Or.inl hrun)
  have hrv : ∀ e, A.rval e = J.rvalOf r e := fun e => congrArg (fun H => H.rval e) hAH
  have hop : ∀ e, A.op e = (J.history r).op e := fun e => congrArg (fun H => H.op e) hAH
  have hlv : ∀ e, A.lvl e = (J.history r).lvl e := fun e => congrArg (fun H => H.lvl e) hAH
  have hrb : ∀ e e', A.rb e e' = (J.history r).rb e e' := fun e e' =>
    congrArg (fun H => H.rb e e') hAH
  have hrC : ∀ K t (ht : t < (C K).length), r t = (C K)[t] := fun K t ht => hC.limRun_eq a₀ ht
  -- the prefix `PA`
  obtain ⟨hFV, -, -, -, -, -, -, hPAF⟩ := Fp_spec' hI hpq x y
  have hPAC : J.PA p q x y <+: C 0 := by simpa [hCdef, Cp] using hPAF
  have rPA : ∀ t (ht : t < (J.PA p q x y).length), r t = (J.PA p q x y)[t] := fun t ht => by
    rw [hrC 0 t (lt_of_lt_of_le ht hPAC.length_le)]; exact (hPAC.getElem ht).symm
  have r0 : r 0 = (p, J.appIn x) := by
    rw [rPA 0 (by rw [PA_eq]; simp), PA_getElem_zero]
  have rtb : r (J.tb p x) = (q, J.appIn y) := by
    rw [rPA _ (tb_lt p q x y), PA_getElem_tb]
  let ea : J.Ev r := ⟨0, by rw [r0]; trivial⟩
  let eb : J.Ev r := ⟨J.tb p x, by rw [rtb]; trivial⟩
  have hne : ea ≠ eb := by
    intro h; have := congrArg Subtype.val h; simp [ea, eb, tb_eq] at this; omega
  have hopa : A.op ea = .append [x] := by rw [hop]; exact history_op ea r0
  have hopb : A.op eb = .append [y] := by rw [hop]; exact history_op eb rtb
  -- the only appends
  have honly : ∀ e : J.Ev r, ∀ s, A.op e = .append s → e = ea ∨ e = eb := by
    intro e s hs
    obtain ⟨op, l, hx⟩ := LIn.exists_of_isInv e.2
    have he : r e.1 = ((r e.1).1, .inv op l) := by rw [← hx]
    rw [hop, history_op e he] at hs
    subst hs
    have ht : e.1 < (C (e.1 + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self _) (hC.grow _)
    have hre := hrC _ _ ht
    obtain ⟨R1, hR1, hR1o⟩ := blkFold_opsIn (I := J) (· = SeqOp.read) (RsH p q)
      (List.finRange n) [] (J.PA p q x y)
    have hCe : C (e.1 + 1) = J.PA p q x y ++ (R1 ++
        (List.replicate (e.1 + 1) (J.readsOf (RsH p q))).flatten) := by
      simp only [hCdef, Cp, Fp, hR1, List.append_assoc]
    have hops : OpsIn (I := J) (· = SeqOp.read)
        (R1 ++ (List.replicate (e.1 + 1) (J.readsOf (RsH p q))).flatten) := by
      refine hR1o.append ?_
      intro a ha op' l' h'
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
  -- the appends return
  have hlva : A.lvl ea = .weak := by rw [hlv]; exact history_lvl ea r0
  have hlvb : A.lvl eb = .weak := by rw [hlv]; exact history_lvl eb rtb
  obtain ⟨Ta, hTa⟩ := exists_lresp_of_rvalOf ea (by rw [← hrv]; exact hRV ea hlva)
  obtain ⟨Tb, hTb⟩ := exists_lresp_of_rvalOf eb (by rw [← hrv]; exact hRV eb hlvb)
  -- the reads of the tail
  have hlenC : ∀ K, (C (K + 1)).length = (C K).length + (RsH p q).length :=
    Cp_length_succ p q x y
  have hRs2 : 2 ≤ (RsH p q).length := by simp [RsH]
  have rp : ∀ K, r (C K).length = (p, .inv .read .weak) := fun K => by
    rw [hrC (K + 1) _ (by rw [hlenC]; omega)]
    simp only [hCdef, Cp_succ]
    rw [List.getElem_append_right (le_refl _)]; simp [readsOf, RsH]
  have rq : ∀ K, r ((C K).length + 1) = (q, .inv .read .weak) := fun K => by
    rw [hrC (K + 1) _ (by rw [hlenC]; omega)]
    simp only [hCdef, Cp_succ]
    rw [List.getElem_append_right (by omega)]; simp [readsOf, RsH]
  let fp : ℕ → J.Ev r := fun K => ⟨(C K).length, by rw [rp]; trivial⟩
  let fq : ℕ → J.Ev r := fun K => ⟨(C K).length + 1, by rw [rq]; trivial⟩
  have hmono : StrictMono fun K => (C K).length :=
    strictMono_nat_of_lt_succ fun K => by rw [hlenC]; omega
  have hfp : Function.Injective fp := fun K K' h => hmono.injective (congrArg Subtype.val h)
  have hfq : Function.Injective fq := fun K K' h => by
    have := congrArg Subtype.val h; simp only [fq] at this; exact hmono.injective (by omega)
  have hfin := (hEV ea).union (hEV eb)
  -- a late read sees both appends
  have hsees : ∀ (f : ℕ → J.Ev r), Function.Injective f → (∀ K, (C K).length ≤ (f K).1) →
      (∀ K, A.lvl (f K) = .weak) → ∃ K, A.vis ea (f K) ∧ A.vis eb (f K) := by
    intro f hf hfle hfl
    obtain ⟨K, hK, hKn⟩ := exists_ge_not_mem hf hfin (max Ta Tb)
    refine ⟨K, ?_, ?_⟩
    · by_contra hv
      apply hKn; left
      refine ⟨hfl K, ?_, hv⟩
      rw [hrb]
      exact rb_of_rvalOf (v := _) (by rw [← hrv]; exact hRV ea hlva) hTa
        (le_trans (le_trans (le_max_left _ _) hK) (le_trans (hC.grow K) (hfle K)))
    · by_contra hv
      apply hKn; right
      refine ⟨hfl K, ?_, hv⟩
      rw [hrb]
      exact rb_of_rvalOf (v := _) (by rw [← hrv]; exact hRV eb hlvb) hTb
        (le_trans (le_trans (le_max_right _ _) hK) (le_trans (hC.grow K) (hfle K)))
  -- the value of a read that sees both appends
  have hval : ∀ e : J.Ev r, A.op e = .read → A.lvl e = .weak → A.vis ea e → A.vis eb e →
      A.rval e = some (if A.ar ea eb then .word [x, y] else .word [y, x]) := by
    intro e he hle hva hvb
    rw [hRV e hle, he]
    have hA : appends (A.context e) ⊆ {ea, eb} := by
      rintro z ⟨-, s, hs⟩
      rcases honly z s hs with rfl | rfl <;> simp
    have := (Fseq_read_two (A.context e) hne hA hopa hopb hxy hWF.ar_total).2.2
      ⟨hva, _, hopa⟩ ⟨hvb, _, hopb⟩
    exact congrArg some this
  have hlocC : ∀ K i, J.loc i (C K) = J.loc i (J.Fp p q x y) ++
      List.replicate K (.inv .read .weak) := fun K i => Cp_loc hI hpq x y K i
  rcases hWF.ar_total.total ea eb hne with hab | hba
  · -- `p` reads `x y`
    left
    obtain ⟨K, hva, hvb⟩ := hsees fp hfp (fun K => le_rfl)
      (fun K => by rw [hlv]; exact history_lvl _ (rp K))
    have h1 := hval (fp K) (by rw [hop]; exact history_op _ (rp K))
      (by rw [hlv]; exact history_lvl _ (rp K)) hva hvb
    rw [if_pos hab] at h1
    obtain ⟨v, hv, hv'⟩ := rvalOf_weak hI hrun.1 (fp K) (rp K) Fseq_read_readOnly (Set.mem_univ _)
    rw [← hrv, h1] at hv'
    refine ⟨K, ?_⟩
    have : J.loc p (J.pre r (fp K).1) = J.Lp p q x y ++ List.replicate K (.inv .read .weak) := by
      simp only [fp]; rw [pre_limRun hC, hlocC, Fp_loc_p hI hpq]
    rw [← this, hv, ← hv']
  · -- `q` reads `y x`
    right
    obtain ⟨K, hva, hvb⟩ := hsees fq hfq (fun K => Nat.le_succ _)
      (fun K => by rw [hlv]; exact history_lvl _ (rq K))
    have h1 := hval (fq K) (by rw [hop]; exact history_op _ (rq K))
      (by rw [hlv]; exact history_lvl _ (rq K)) hva hvb
    have hnab : ¬ A.ar ea eb := fun h => hWF.ar_total.irrefl _ (hWF.ar_total.trans _ _ _ h hba)
    rw [if_neg hnab] at h1
    obtain ⟨v, hv, hv'⟩ := rvalOf_weak hI hrun.1 (fq K) (rq K) Fseq_read_readOnly (Set.mem_univ _)
    rw [← hrv, h1] at hv'
    refine ⟨K, ?_⟩
    have : J.loc q (J.pre r (fq K).1) = J.Lp q p y x ++ List.replicate K (.inv .read .weak) := by
      simp only [fq]
      rw [pre_succ, pre_limRun hC, rp, loc_append, loc_singleton, if_neg hpq, List.append_nil,
        hlocC, Fp_loc_q hI hpq]
    rw [← this, hv, ← hv']

end Podc.BayouRevisited.Impl
