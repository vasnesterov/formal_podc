import Papers.PODC2019.BayouRevisited.Claim1

/-!
# Claim 2 of the proof of Theorem 5 (the stable run `H''`)

Only `q` appends (`y`), runs until passive, delivers its own `RB` and `TOB` messages and runs until
passive. Then rounds are repeated forever: `q` invokes a strong read (and runs, delivers its own
new messages, runs until passive); every other replica delivers all messages, runs until passive
and invokes a weak read. This is a fair stable run. If the implementation satisfies
`BEC(weak, F_seq) ∧ BEC(strong, F_seq)` in it, some strong read of `q` returns `y`; its response
is determined by the local inputs of `q` alone.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {α : Type} {J : Impl n (SeqOp α) (SeqVal α)}

/-- The replicas other than `q`. -/
def Os (q : Fin n) : List (Fin n) := (List.finRange n).filter (· ≠ q)

lemma Os_nodup (q : Fin n) : (Os q).Nodup := (List.nodup_finRange n).filter _

lemma q_not_mem_Os (q : Fin n) : q ∉ Os q := by simp [Os]

lemma mem_Os {q i : Fin n} (h : i ≠ q) : i ∈ Os q := by simp [Os, h]

/-- `q`'s own catch-up block after the execution `P`. -/
noncomputable def qblk (J : Impl n (SeqOp α) (SeqVal α)) (q : Fin n) (P : List J.Act) :
    List J.Act :=
  P ++ J.atR q (J.blk q [q] (J.Gq q (J.loc q P)) P)

/-- The start of `H''`: `q` appends `y`, runs until passive, catches up on its own messages. -/
noncomputable def Q0 (J : Impl n (SeqOp α) (SeqVal α)) (q : Fin n) (y : α) : List J.Act :=
  J.qblk q (J.invBlk q (.append [y]) .weak [])

/-- The chain defining `H''`. -/
noncomputable def C2 (J : Impl n (SeqOp α) (SeqVal α)) (q : Fin n) (y : α) (K : ℕ) :
    List J.Act :=
  J.rounds q (Os q) .read (J.Q0 q y) K

lemma blk_qblk_congr {q : Fin n} {P P' : List J.Act} (h : J.loc q P = J.loc q P') :
    J.blk q [q] (J.Gq q (J.loc q P)) P = J.blk q [q] (J.Gq q (J.loc q P')) P' := by
  have hcu : J.cu q [q] (J.Gq q (J.loc q P)) P = J.cu q [q] (J.Gq q (J.loc q P')) P' := by
    simp only [cu, h]
    apply cuL_congr
    · intro j hj; rw [List.mem_singleton.1 hj, h]
    · intro p hp; rw [(mem_Gq hp).1, h]
  rw [blk, blk, hcu, h]

lemma loc_qblk_self (q : Fin n) (P : List J.Act) :
    J.loc q (J.qblk q P) = J.loc q P ++ J.blk q [q] (J.Gq q (J.loc q P)) P := by
  simp [qblk]

lemma loc_qblk_ne {q i : Fin n} (h : i ≠ q) (P : List J.Act) :
    J.loc i (J.qblk q P) = J.loc i P := by
  simp [qblk, J.loc_atR_ne (Ne.symm h)]

/-- Validity of `qblk` and the `TOB` invariant of rounds after it. -/
lemma qblk_spec (hI : J.IsACT (seqSpec α)) {q : Fin n} {P : List J.Act}
    (hP : J.Valid (seqSpec α) P) (hseq : ∀ i', J.tobSeq i' P = []) :
    J.Valid (seqSpec α) (J.qblk q P) ∧
      ∀ i', J.tobSeq i' (J.qblk q P) <+: J.Gq q (J.loc q (J.qblk q P)) := by
  have hcast : ∀ p ∈ J.Gq q (J.loc q P), p.2 < (J.tobCasts p.1 (J.loc p.1 P)).length :=
    fun p hp => by obtain ⟨h1, h2⟩ := mem_Gq hp; rw [h1]; exact h2
  have hpre : ∀ i', J.tobSeq i' P <+: J.Gq q (J.loc q P) := fun i' => by
    rw [hseq]; exact List.nil_prefix
  refine ⟨(valid_blk hI hP q (List.nodup_singleton q) (Gq_nodup q _) hpre hcast).1, ?_⟩
  intro i'
  have hG : J.Gq q (J.loc q P) <+: J.Gq q (J.loc q (J.qblk q P)) :=
    Gq_prefix q (loc_prefix (List.prefix_append _ _) q)
  by_cases h : i' = q
  · subst h; rw [qblk, tobSeq_blk i' [i'] (hpre i') hcast]; exact hG
  · rw [qblk, tobSeq_append, J.loc_atR_ne (Ne.symm h), hseq]; simp

lemma Q0_spec (hI : J.IsACT (seqSpec α)) (q : Fin n) (y : α) :
    J.Valid (seqSpec α) (J.Q0 q y) ∧
      ∀ i', J.tobSeq i' (J.Q0 q y) <+: J.Gq q (J.loc q (J.Q0 q y)) :=
  qblk_spec hI (valid_invBlk hI valid_nil q (op := .append [y]) (l := .weak) (Set.mem_univ _)).1
    (fun i' => by rw [tobSeq_invBlk]; rfl)

lemma round_eq_cons (q : Fin n) (Os : List (Fin n)) (rd : SeqOp α) (P : List J.Act) :
    ∃ R, J.round q Os rd P = P ++ [(q, .inv rd .strong)] ++ R := by
  simp only [round]
  obtain ⟨R, hR, -⟩ := blkFold_noInv (I := J) (List.finRange n)
    (J.Gq q (J.loc q (J.invBlk q rd .strong P ++
      J.atR q (J.blk q [q] (J.Gq q (J.loc q (J.invBlk q rd .strong P))) (J.invBlk q rd .strong P)))))
    Os (J.invBlk q rd .strong P ++
      J.atR q (J.blk q [q] (J.Gq q (J.loc q (J.invBlk q rd .strong P))) (J.invBlk q rd .strong P)))
  rw [hR]
  simp only [invBlk, List.append_assoc]
  exact ⟨_, rfl⟩

lemma Q0_eq (q : Fin n) (y : α) : ∃ M, J.Q0 q y = [(q, J.appIn y)] ++ M ∧
    ∀ a ∈ M, ∀ op l, a.2 ≠ .inv op l := by
  refine ⟨J.atR q (J.intBlk q ([] ++ [J.appIn y])) ++ J.atR q (J.blk q [q]
    (J.Gq q (J.loc q (J.invBlk q (.append [y]) .weak []))) (J.invBlk q (.append [y]) .weak [])),
    by simp [Q0, qblk, invBlk], ?_⟩
  intro a ha op l h
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    simp [intBlk] at hz; obtain ⟨ι, -, rfl⟩ := hz; cases h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
    exact not_inv_blk q [q] _ _ z hz op l h

lemma C2_succ (q : Fin n) (y : α) (K : ℕ) :
    J.C2 q y (K + 1) = J.round q (Os q) .read (J.C2 q y K) := rfl

lemma C2_chain (q : Fin n) (y : α) : IsChain (J.C2 q y) where
  mono K := by
    obtain ⟨R, hR⟩ := round_eq_cons q (Os q) .read (J.C2 q y K)
    rw [C2_succ, hR, List.append_assoc]; exact List.prefix_append _ _
  grow K := by
    induction K with
    | zero => simp
    | succ K ih =>
      obtain ⟨R, hR⟩ := round_eq_cons q (Os q) .read (J.C2 q y K)
      rw [C2_succ, hR]; simp; omega

section H''

variable (hI : J.IsACT (seqSpec α)) (q : Fin n) (y : α)
include hI

lemma C2_spec (K : ℕ) :
    J.Valid (seqSpec α) (J.C2 q y K) ∧
    (∀ i', J.tobSeq i' (J.C2 q y K) <+: J.Gq q (J.loc q (J.C2 q y K))) ∧
    J.loc q (J.C2 q y K) = J.qRoundsL q .read (J.loc q (J.Q0 q y)) K ∧
    (∃ R, J.C2 q y K = J.Q0 q y ++ R ∧ OpsIn (· = SeqOp.read) R) ∧
    (∀ i, i ≠ q → ∃ δ, J.loc i (J.C2 q y K) = J.loc i (J.Q0 q y) ++ δ ∧
      ∀ x ∈ δ, ¬ Licensing (seqSpec α) x) :=
  rounds_spec hI (Os_nodup q) (q_not_mem_Os q) (rd := SeqOp.read) (Set.mem_univ _)
    (Set.mem_univ _) Fseq_read_readOnly (Q0_spec hI q y).1 (Q0_spec hI q y).2 K

lemma C2_casts_other (K : ℕ) {j : Fin n} (hj : j ≠ q) :
    J.rbCasts j (J.loc j (J.C2 q y K)) = [] ∧ J.tobCasts j (J.loc j (J.C2 q y K)) = [] := by
  obtain ⟨δ, hδ, hδl⟩ := (C2_spec hI q y K).2.2.2.2 j hj
  have h0 : J.loc j (J.Q0 q y) = [] := by
    rw [Q0, loc_qblk_ne hj, loc_invBlk_ne (Ne.symm hj)]; rfl
  rw [h0, List.nil_append] at hδ
  have := no_casts_of_quiet hI (C2_spec hI q y K).1 (ℓ := []) (by rw [hδ, List.nil_append])
    (Or.inr (by simp)) hδl
  rw [hδ]; simpa [rbCasts, tobCasts] using this

lemma C2_stable (a₀ : J.Act) : J.IsStableRun (seqSpec α) (limRun (J.C2 q y) a₀) := by
  have hRS := fun K => round_spec hI (Os_nodup q) (q_not_mem_Os q) (rd := SeqOp.read)
    (Set.mem_univ _) (Set.mem_univ _) Fseq_read_readOnly (C2_spec hI q y K).1
    (C2_spec hI q y K).2.1
  have hall : ∀ i, i = q ∨ i ∈ Os q := fun i => by
    by_cases h : i = q
    · exact Or.inl h
    · exact Or.inr (mem_Os h)
  apply isStableRun_lim (C2_chain q y) a₀ (fun K => (C2_spec hI q y K).1)
  · intro K i; exact (hRS K).2.2.2.2.2.2.2.2.1 i (hall i)
  · intro K i
    rcases hall i with rfl | hi
    · exact (hRS K).2.2.2.2.1
    · exact (hRS K).2.2.2.2.2.1 i hi
  · intro K i j k hk
    by_cases hj : j = q
    · subst hj
      obtain ⟨m, hm⟩ := (hRS K).2.2.2.2.2.2.1 i (hall i) k hk
      exact ⟨m, mem_of_mem_loc hm⟩
    · rw [(C2_casts_other hI q y K hj).1] at hk; simp at hk
  · intro K i j k hk
    by_cases hj : j = q
    · subst hj
      obtain ⟨m, hm⟩ := (hRS K).2.2.2.2.2.2.2.1 i (hall i) k hk
      exact ⟨m, mem_of_mem_loc hm⟩
    · rw [(C2_casts_other hI q y K hj).2] at hk; simp at hk

end H''

/-- **Claim 2** of the proof of Theorem 5: some strong read of `q` in `H''` returns `y`;
its response lies within the local inputs of `q` after finitely many rounds. -/
theorem claim2 (hI : J.IsACT (seqSpec α)) (hyp : J.T5Hyp) (q : Fin n) (y : α) :
    ∃ K K1, K < K1 ∧
      J.lresp q (J.loc q (J.C2 q y K1)) (J.loc q (J.C2 q y K)).length = some (.word [y]) := by
  classical
  set C := J.C2 q y with hCdef
  have hC : IsChain C := C2_chain q y
  set a₀ : J.Act := (q, .inv .read .weak)
  set r := limRun C a₀ with hr
  have hrun := C2_stable hI q y a₀
  obtain ⟨A, hAH, hWF, ⟨-, -, hRVw⟩, -, ⟨hEVs, -, hRVs⟩⟩ := hyp.1 r hrun
  have hrv : ∀ e, A.rval e = J.rvalOf r e := fun e => congrArg (fun H => H.rval e) hAH
  have hop : ∀ e, A.op e = (J.history r).op e := fun e => congrArg (fun H => H.op e) hAH
  have hlv : ∀ e, A.lvl e = (J.history r).lvl e := fun e => congrArg (fun H => H.lvl e) hAH
  have hrb : ∀ e e', A.rb e e' = (J.history r).rb e e' := fun e e' =>
    congrArg (fun H => H.rb e e') hAH
  have hrC : ∀ K t (ht : t < (C K).length), r t = (C K)[t] := fun K t ht => hC.limRun_eq a₀ ht
  obtain ⟨M, hM, hMi⟩ := Q0_eq (J := J) q y
  have hC0 : C 0 = [(q, J.appIn y)] ++ M := hM
  have r0 : r 0 = (q, J.appIn y) := by rw [hrC 0 0 (by rw [hC0]; simp)]; simp [hC0]
  let eb : J.Ev r := ⟨0, by rw [r0]; trivial⟩
  have hopb : A.op eb = .append [y] := by rw [hop]; exact history_op eb r0
  have hlvb : A.lvl eb = .weak := by rw [hlv]; exact history_lvl eb r0
  have honly : ∀ e : J.Ev r, ∀ s, A.op e = .append s → e = eb := by
    intro e s hs
    obtain ⟨op, l, hx⟩ := LIn.exists_of_isInv e.2
    have he : r e.1 = ((r e.1).1, .inv op l) := by rw [← hx]
    rw [hop, history_op e he] at hs
    subst hs
    have ht : e.1 < (C (e.1 + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self _) (hC.grow _)
    have hre := hrC _ _ ht
    obtain ⟨R, hR, hRo⟩ := (C2_spec hI q y (e.1 + 1)).2.2.2.1
    have h1 : (C (e.1 + 1))[e.1] = ((r e.1).1, .inv (.append s) l) := by rw [← hre, he]
    simp only [hCdef, hR] at h1 ht
    obtain ⟨hlt, hQe⟩ := getElem_of_opsIn hRo ht h1 (by simp)
    apply Subtype.ext
    by_contra h0
    have h0' : e.1 ≠ 0 := h0
    have hQe' : (J.Q0 q y)[e.1] = ([(q, J.appIn y)] ++ M)[e.1]'(by rw [← hM]; exact hlt) := by
      simp only [hM]
    rw [hQe', List.getElem_append_right (by simp; omega)] at hQe
    exact hMi _ (List.getElem_mem _) _ _ (by rw [hQe])
  obtain ⟨Tb, hTb⟩ := exists_lresp_of_rvalOf eb (by rw [← hrv]; exact hRVw eb hlvb)
  -- the strong reads
  have hCs : ∀ K, ∃ R, C (K + 1) = C K ++ [(q, .inv .read .strong)] ++ R := fun K =>
    round_eq_cons q (Os q) .read (C K)
  have rs : ∀ K, r (C K).length = (q, .inv .read .strong) := fun K => by
    obtain ⟨R, hR⟩ := hCs K
    have hlt : (C K).length < (C (K + 1)).length := by rw [hR]; simp
    rw [hrC (K + 1) _ hlt]
    simp only [hR]
    rw [List.getElem_append_left (by simp), List.getElem_append_right (le_refl _)]; simp
  let f : ℕ → J.Ev r := fun K => ⟨(C K).length, by rw [rs]; trivial⟩
  have hmono : StrictMono fun K => (C K).length :=
    strictMono_nat_of_lt_succ fun K => by obtain ⟨R, hR⟩ := hCs K; rw [hR]; simp
  have hf : Function.Injective f := fun K K' h => hmono.injective (congrArg Subtype.val h)
  obtain ⟨K, hK, hKn⟩ := exists_ge_not_mem hf (hEVs eb) Tb
  have hlvf : A.lvl (f K) = .strong := by rw [hlv]; exact history_lvl _ (rs K)
  have hvis : A.vis eb (f K) := by
    by_contra hv
    apply hKn
    refine ⟨hlvf, ?_, hv⟩
    rw [hrb]
    exact rb_of_rvalOf (v := _) (by rw [← hrv]; exact hRVw eb hlvb) hTb
      (le_trans hK (hC.grow K))
  -- the value of the strong read `f K`
  have hval : A.rval (f K) = some (.word [y]) := by
    rw [hRVs (f K) hlvf, hop, history_op _ (rs K)]
    have hA : appends (A.context (f K)) = {eb} := by
      ext z; constructor
      · rintro ⟨-, s, hs⟩; exact honly z s hs
      · rintro rfl; exact ⟨hvis, _, hopb⟩
    have := Fseq_read_single (A.context (f K)) hA (hWF.ar_total.irrefl _)
    refine congrArg some (this.trans ?_)
    simp only [AbsExec.context]; rw [hopb]; rfl
  rw [hrv] at hval
  obtain ⟨T, hT⟩ := exists_lresp_of_rvalOf (f K) hval
  have hq : (r (f K).1).1 = q := by simp only [f]; rw [rs]
  rw [hq, lidx_eq (rs K)] at hT
  refine ⟨K, max T (K + 1), lt_of_lt_of_le (Nat.lt_succ_self K) (le_max_right _ _), ?_⟩
  have h1 : J.pre r T <+: C (max T (K + 1)) :=
    (pre_limRun_prefix hC a₀ (hC.grow T)).trans (hC.prefix_of_le (le_max_left _ _))
  have := lresp_mono (loc_prefix h1 q) hT
  rwa [pre_limRun hC] at this

end Podc.BayouRevisited.Impl
