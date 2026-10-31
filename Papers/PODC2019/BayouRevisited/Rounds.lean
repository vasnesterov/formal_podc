import Papers.PODC2019.BayouRevisited.Runs

/-!
# Composite blocks: catch-up of several replicas, invocation blocks, and strong-read rounds

The *round* is the repeated procedure of the proof of Theorem 5 (construction of `H''`): replica
`q` invokes a strong read and runs until passive, delivers its own new messages (`RB` and `TOB`)
and runs until passive; then every other replica delivers all messages, runs until passive and
invokes a weak read.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} (I : Impl n Op Val)

/-- Catch-up blocks of the replicas `Rs`, one after the other. -/
noncomputable def blkFold : List (Fin n) → List (Fin n) → List (Fin n × ℕ) → List I.Act →
    List I.Act
  | [], _, _, P => P
  | r :: Rs, Ss, G, P => blkFold Rs Ss G (P ++ I.atR r (I.blk r Ss G P))

/-- Invoke `op` with level `l` at `i`, then run `i` until passive. -/
noncomputable def invBlk (i : Fin n) (op : Op) (l : Level) (P : List I.Act) : List I.Act :=
  P ++ [(i, .inv op l)] ++ I.atR i (I.intBlk i (I.loc i P ++ [.inv op l]))

/-- The `TOB` order consisting of all messages `TOB-cast` by `q` (in `ℓ`). -/
def Gq (q : Fin n) (ℓ : List I.Input) : List (Fin n × ℕ) :=
  (List.range (I.tobCasts q ℓ).length).map fun k => (q, k)

/-- One round of the construction of `H''` (see the module docstring). `Os` are the other
replicas. -/
noncomputable def round (q : Fin n) (Os : List (Fin n)) (rd : Op) (P : List I.Act) :
    List I.Act :=
  let P2 := I.invBlk q rd .strong P
  let P3 := P2 ++ I.atR q (I.blk q [q] (I.Gq q (I.loc q P2)) P2)
  I.blkFold Os (List.finRange n) (I.Gq q (I.loc q P3)) P3 ++ Os.map fun r => (r, .inv rd .weak)

/-- `K` rounds. -/
noncomputable def rounds (q : Fin n) (Os : List (Fin n)) (rd : Op) (P : List I.Act) :
    ℕ → List I.Act
  | 0 => P
  | K + 1 => I.round q Os rd (rounds q Os rd P K)

/-- The local inputs of `q` in one round, as a function of its local inputs before. -/
noncomputable def qRoundL (q : Fin n) (rd : Op) (ℓ : List I.Input) : List I.Input :=
  let ℓ1 := ℓ ++ [.inv rd .strong]
  let ℓ2 := ℓ1 ++ I.intBlk q ℓ1
  let δ := I.cuL ℓ2 [q] (I.Gq q ℓ2) (fun _ => I.rbCasts q ℓ2) (fun _ => I.tobCasts q ℓ2)
  [.inv rd .strong] ++ I.intBlk q ℓ1 ++ δ ++ I.intBlk q (ℓ2 ++ δ)

/-- Local inputs of `q` after `K` rounds. -/
noncomputable def qRoundsL (q : Fin n) (rd : Op) (ℓ : List I.Input) : ℕ → List I.Input
  | 0 => ℓ
  | K + 1 => qRoundsL q rd ℓ K ++ I.qRoundL q rd (qRoundsL q rd ℓ K)

variable {I} {S : ACTSpec Op Val}

/-! ### Congruence -/

lemma cuL_congr (ℓ : List I.Input) (Ss : List (Fin n)) (G : List (Fin n × ℕ))
    {rc rc' tc tc' : Fin n → List I.Msg} (hrc : ∀ j ∈ Ss, rc j = rc' j)
    (htc : ∀ p ∈ G, tc p.1 = tc' p.1) : I.cuL ℓ Ss G rc tc = I.cuL ℓ Ss G rc' tc' := by
  simp only [cuL, catchRBs, catchTOB]
  congr 1
  · exact List.flatMap_congr fun j hj => by rw [hrc j hj]
  · apply List.filterMap_congr
    intro p hp; rw [htc p (List.mem_of_mem_drop hp)]

lemma blk_congr {P P' : List I.Act} (i : Fin n) (Ss : List (Fin n)) (G : List (Fin n × ℕ))
    (hl : I.loc i P = I.loc i P')
    (hrc : ∀ j, I.rbCasts j (I.loc j P) = I.rbCasts j (I.loc j P'))
    (htc : ∀ j, I.tobCasts j (I.loc j P) = I.tobCasts j (I.loc j P')) :
    I.blk i Ss G P = I.blk i Ss G P' := by
  have hcu : I.cu i Ss G P = I.cu i Ss G P' := by
    simp only [cu, hl]; exact cuL_congr _ _ _ (fun j _ => hrc j) (fun p _ => htc p.1)
  simp only [blk, hcu, hl]

/-! ### Invocation blocks -/

lemma valid_invBlk (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n) {op : Op}
    {l : Level} (hl : l ∈ S.lvlmap op) :
    I.Valid S (I.invBlk i op l P) ∧ I.Passive i (I.lstate i (I.loc i (I.invBlk i op l P))) := by
  have h1 : I.Valid S (P ++ [(i, .inv op l)]) := valid_concat hP hl
  have h2 := valid_intBlk hI h1 i
  have h3 := passive_intBlk hI h1 i
  have hloc : I.loc i (P ++ [(i, LIn.inv op l)]) = I.loc i P ++ [.inv op l] := by
    simp [loc_singleton]
  rw [hloc] at h2 h3
  exact ⟨h2, h3⟩

lemma loc_invBlk_self (i : Fin n) (op : Op) (l : Level) (P : List I.Act) :
    I.loc i (I.invBlk i op l P) =
      I.loc i P ++ ([.inv op l] ++ I.intBlk i (I.loc i P ++ [.inv op l])) := by
  simp only [invBlk, loc_append, loc_singleton, loc_atR_self, List.append_assoc, if_true]

lemma loc_invBlk_ne {i j : Fin n} (h : i ≠ j) (op : Op) (l : Level) (P : List I.Act) :
    I.loc j (I.invBlk i op l P) = I.loc j P := by
  simp only [invBlk, loc_append, loc_singleton, if_neg h, I.loc_atR_ne h, List.append_nil]

lemma tobSeq_invBlk (i j : Fin n) (op : Op) (l : Level) (P : List I.Act) :
    I.tobSeq j (I.invBlk i op l P) = I.tobSeq j P := by
  by_cases h : i = j
  · subst h
    simp only [tobSeq, loc_invBlk_self, List.filterMap_append]
    simp [intBlk, LIn.tobId, List.filterMap_map, Function.comp_def]
  · simp only [tobSeq, loc_invBlk_ne h]

/-! ### Catch-up of several replicas -/

lemma blkFold_spec (hI : I.IsACT S) {Ss : List (Fin n)} (hSs : Ss.Nodup)
    {G : List (Fin n × ℕ)} (hG : G.Nodup) :
    ∀ (Rs : List (Fin n)) (P : List I.Act), Rs.Nodup → I.Valid S P →
      (∀ i', I.tobSeq i' P <+: G) →
      (∀ p ∈ G, p.2 < (I.tobCasts p.1 (I.loc p.1 P)).length) →
      I.Valid S (I.blkFold Rs Ss G P) ∧
      (∀ r ∉ Rs, I.loc r (I.blkFold Rs Ss G P) = I.loc r P) ∧
      (∀ r ∈ Rs, I.Passive r (I.lstate r (I.loc r (I.blkFold Rs Ss G P)))) ∧
      (∀ r ∈ Rs, I.tobSeq r (I.blkFold Rs Ss G P) = G) ∧
      (∀ r', I.tobSeq r' (I.blkFold Rs Ss G P) <+: G) ∧
      (∀ r ∈ Rs, ∀ j ∈ Ss, ∀ k < (I.rbCasts j (I.loc j P)).length,
        ∃ m, LIn.rb j k m ∈ I.loc r (I.blkFold Rs Ss G P)) ∧
      (∀ r, ∃ δ, I.loc r (I.blkFold Rs Ss G P) = I.loc r P ++ δ ∧ ∀ x ∈ δ, ¬ Licensing S x) ∧
      P <+: I.blkFold Rs Ss G P
  | [], P, _, hP, hpre, _ => by
    simp only [blkFold]
    refine ⟨hP, fun _ _ => trivial, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp),
      hpre, fun _ h => absurd h (by simp), fun r => ⟨[], by simp, by simp⟩, ?_⟩
    exact List.prefix_refl _
  | r :: Rs, P, hnd, hP, hpre, hcast => by
    rw [List.nodup_cons] at hnd
    set P' := P ++ I.atR r (I.blk r Ss G P)
    obtain ⟨hV', hpas'⟩ := valid_blk hI hP r hSs hG hpre hcast
    have hseq' : ∀ i', i' ≠ r → I.tobSeq i' P' = I.tobSeq i' P := by
      intro i' h; rw [tobSeq_append, I.loc_atR_ne (Ne.symm h)]; simp
    have hseqr : I.tobSeq r P' = G := tobSeq_blk r Ss (hpre r) hcast
    have hpre' : ∀ i', I.tobSeq i' P' <+: G := by
      intro i'; by_cases h : i' = r
      · subst h; rw [hseqr]
      · rw [hseq' i' h]; exact hpre i'
    have hcast' : ∀ p ∈ G, p.2 < (I.tobCasts p.1 (I.loc p.1 P')).length := by
      intro p hp
      have := tobCasts_length_mono
        (loc_prefix (List.prefix_append P (I.atR r (I.blk r Ss G P))) p.1) p.1
      exact lt_of_lt_of_le (hcast p hp) this
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := blkFold_spec hI hSs hG Rs P' hnd.2 hV' hpre' hcast'
    simp only [blkFold]
    refine ⟨h1, ?_, ?_, ?_, h5, ?_, ?_, (List.prefix_append P _).trans h8⟩
    · intro r' hr'
      simp only [List.mem_cons, not_or] at hr'
      rw [h2 r' hr'.2, loc_append, I.loc_atR_ne (Ne.symm hr'.1), List.append_nil]
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · rw [h2 _ hnd.1]; exact hpas'
      · exact h3 r' hr'
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · rw [tobSeq, h2 _ hnd.1]; exact hseqr
      · exact h4 r' hr'
    · intro r' hr' j hj k hk
      rcases List.mem_cons.1 hr' with rfl | hr'
      · rw [h2 _ hnd.1]; exact rb_delivered_blk r' G hj hk
      · apply h6 r' hr' j hj k
        exact lt_of_lt_of_le hk (rbCasts_length_mono
          (loc_prefix (List.prefix_append P (I.atR r (I.blk r Ss G P))) j) j)
    · intro r'
      obtain ⟨δ, hδ, hδl⟩ := h7 r'
      by_cases h : r' = r
      · subst h
        refine ⟨I.blk r' Ss G P ++ δ, ?_, ?_⟩
        · rw [hδ, loc_append, loc_atR_self, List.append_assoc]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact not_licensing_blk r' Ss G P x hx
          · exact hδl x hx
      · refine ⟨δ, ?_, hδl⟩
        rw [hδ, loc_append, I.loc_atR_ne (Ne.symm h), List.append_nil]

/-! ### Rounds -/

lemma Gq_prefix (q : Fin n) {ℓ ℓ' : List I.Input} (h : ℓ <+: ℓ') : I.Gq q ℓ <+: I.Gq q ℓ' := by
  have hle := tobCasts_length_mono h q
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  simp only [Gq, hd, List.range_add, List.map_append]
  exact List.prefix_append _ _

lemma Gq_nodup (q : Fin n) (ℓ : List I.Input) : (I.Gq q ℓ).Nodup :=
  List.nodup_range.map fun a b h => (Prod.mk.inj h).2

lemma mem_Gq {q : Fin n} {ℓ : List I.Input} {p : Fin n × ℕ} (h : p ∈ I.Gq q ℓ) :
    p.1 = q ∧ p.2 < (I.tobCasts q ℓ).length := by
  simp only [Gq, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h; exact ⟨rfl, hk⟩

lemma valid_append_invs {P L : List I.Act} (hP : I.Valid S P)
    (hL : ∀ a ∈ L, ∃ i op l, a = (i, LIn.inv op l) ∧ l ∈ S.lvlmap op) :
    I.Valid S (P ++ L) := by
  induction L using List.reverseRecOn with
  | nil => simpa using hP
  | append_singleton L a ih =>
    rw [← List.append_assoc]
    refine valid_concat (ih fun b hb => hL b (by simp [hb])) ?_
    obtain ⟨i, op, l, rfl, hl⟩ := hL a (by simp)
    exact hl

lemma loc_reads {Os : List (Fin n)} (hOs : Os.Nodup) (rd : Op) (i : Fin n) :
    I.loc i (Os.map fun r => (r, LIn.inv rd .weak)) =
      if i ∈ Os then [LIn.inv rd .weak] else [] := by
  induction Os with
  | nil => simp
  | cons o Os ih =>
    rw [List.nodup_cons] at hOs
    rw [List.map_cons, show (o, LIn.inv rd Level.weak) :: Os.map (fun r => (r, LIn.inv rd .weak))
      = [(o, LIn.inv rd Level.weak)] ++ Os.map (fun r => (r, LIn.inv rd .weak)) from rfl,
      loc_append, loc_singleton, ih hOs.2]
    by_cases h1 : o = i
    · subst h1; simp [hOs.1]
    · simp [h1, Ne.symm h1]

/-- Specification of one round. -/
lemma round_spec (hI : I.IsACT S) {q : Fin n} {Os : List (Fin n)} (hOs : Os.Nodup)
    (hq : q ∉ Os) {rd : Op} (hw : Level.weak ∈ S.lvlmap rd) (hs : Level.strong ∈ S.lvlmap rd)
    (hro : RDT.IsReadOnly S.F rd) {P : List I.Act} (hP : I.Valid S P)
    (hpre : ∀ i', I.tobSeq i' P <+: I.Gq q (I.loc q P)) :
    I.Valid S (I.round q Os rd P) ∧
    P <+: I.round q Os rd P ∧
    (∀ i', I.tobSeq i' (I.round q Os rd P) <+: I.Gq q (I.loc q (I.round q Os rd P))) ∧
    I.loc q (I.round q Os rd P) = I.loc q P ++ I.qRoundL q rd (I.loc q P) ∧
    I.Passive q (I.lstate q (I.loc q (I.round q Os rd P))) ∧
    (∀ r ∈ Os, I.Passive r (I.lstate r (I.loc r (I.round q Os rd P)))) ∧
    (∀ i, i = q ∨ i ∈ Os → ∀ k < (I.rbCasts q (I.loc q P)).length,
      ∃ m, LIn.rb q k m ∈ I.loc i (I.round q Os rd P)) ∧
    (∀ i, i = q ∨ i ∈ Os → ∀ k < (I.tobCasts q (I.loc q P)).length,
      ∃ m, LIn.tob q k m ∈ I.loc i (I.round q Os rd P)) ∧
    (∀ i, i = q ∨ i ∈ Os → ∃ x, (i, x) ∈ (I.round q Os rd P).drop P.length ∧ x.IsInv) ∧
    (∀ i, i ≠ q → ∃ δ, I.loc i (I.round q Os rd P) = I.loc i P ++ δ ∧
      ∀ x ∈ δ, ¬ Licensing S x) := by
  -- the stages
  set P2 := I.invBlk q rd .strong P with hP2
  set G2 := I.Gq q (I.loc q P2)
  set P3 := P2 ++ I.atR q (I.blk q [q] G2 P2) with hP3
  set G3 := I.Gq q (I.loc q P3)
  set P4 := I.blkFold Os (List.finRange n) G3 P3 with hP4
  set reads : List I.Act := Os.map fun r => (r, LIn.inv rd .weak)
  have hround : I.round q Os rd P = P4 ++ reads := rfl
  obtain ⟨hV2, hpas2⟩ := valid_invBlk hI hP q hs
  have hpre2 : ∀ i', I.tobSeq i' P2 <+: G2 := fun i' => by
    rw [tobSeq_invBlk]
    exact (hpre i').trans (Gq_prefix q (loc_prefix (List.prefix_append_of_prefix
      (List.prefix_append _ _)) q))
  have hcast2 : ∀ p ∈ G2, p.2 < (I.tobCasts p.1 (I.loc p.1 P2)).length := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_Gq hp; rw [h1]; exact h2
  obtain ⟨hV3, hpas3⟩ := valid_blk hI hV2 q (List.nodup_singleton q) (Gq_nodup q _) hpre2 hcast2
  have hP23 : P2 <+: P3 := List.prefix_append _ _
  have hseq3q : I.tobSeq q P3 = G2 := tobSeq_blk q [q] (hpre2 q) hcast2
  have hpre3 : ∀ i', I.tobSeq i' P3 <+: G3 := fun i' => by
    have hG23 : G2 <+: G3 := Gq_prefix q (loc_prefix hP23 q)
    by_cases h : i' = q
    · subst h; rw [hseq3q]; exact hG23
    · rw [hP3, tobSeq_append, I.loc_atR_ne (Ne.symm h)]; simpa using (hpre2 i').trans hG23
  have hcast3 : ∀ p ∈ G3, p.2 < (I.tobCasts p.1 (I.loc p.1 P3)).length := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_Gq hp; rw [h1]; exact h2
  obtain ⟨hV4, hloc4, hpas4, hseq4, hpre4, hdel4, hδ4, hP34⟩ :=
    blkFold_spec hI (List.nodup_finRange n) (Gq_nodup q _) Os P3 hOs hV3 hpre3 hcast3
  have hV5 : I.Valid S (P4 ++ reads) := valid_append_invs hV4 (fun a ha => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; exact ⟨r, rd, _, rfl, hw⟩)
  have hlocq : I.loc q (P4 ++ reads) = I.loc q P3 := by
    rw [loc_append, loc_reads hOs, if_neg hq, List.append_nil, hloc4 q hq]
  have hlocr : ∀ r ∈ Os, I.loc r (P4 ++ reads) = I.loc r P4 ++ [LIn.inv rd .weak] := by
    intro r hr; rw [loc_append, loc_reads hOs, if_pos hr]
  have hPP2 : P <+: P2 := by
    rw [hP2, invBlk, List.append_assoc]; exact List.prefix_append _ _
  have hPP4 : P <+: P4 := hPP2.trans (hP23.trans hP34)
  rw [hround]
  refine ⟨hV5, hPP4.trans (List.prefix_append _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- TOB invariant
    intro i'
    rw [hlocq, tobSeq_append, loc_reads hOs]
    have h0 : (if i' ∈ Os then [(LIn.inv rd .weak : I.Input)] else []).filterMap LIn.tobId
        = [] := by
      split_ifs <;> rfl
    rw [h0, List.append_nil]; exact hpre4 i'
  · -- local view of `q`
    rw [hlocq, hP3, loc_append, loc_atR_self, hP2, loc_invBlk_self]
    simp only [qRoundL, blk, List.append_assoc]
    have hl2 : I.loc q (I.invBlk q rd .strong P) =
        I.loc q P ++ [LIn.inv rd .strong] ++ I.intBlk q (I.loc q P ++ [LIn.inv rd .strong]) := by
      rw [loc_invBlk_self, List.append_assoc]
    have hcu : I.cu q [q] (I.Gq q (I.loc q (I.invBlk q rd .strong P))) (I.invBlk q rd .strong P)
        = I.cuL (I.loc q P ++ [LIn.inv rd .strong] ++
            I.intBlk q (I.loc q P ++ [LIn.inv rd .strong])) [q]
          (I.Gq q (I.loc q P ++ [LIn.inv rd .strong] ++
            I.intBlk q (I.loc q P ++ [LIn.inv rd .strong])))
          (fun _ => I.rbCasts q (I.loc q P ++ [LIn.inv rd .strong] ++
            I.intBlk q (I.loc q P ++ [LIn.inv rd .strong])))
          (fun _ => I.tobCasts q (I.loc q P ++ [LIn.inv rd .strong] ++
            I.intBlk q (I.loc q P ++ [LIn.inv rd .strong]))) := by
      rw [cu, hl2]
      apply cuL_congr
      · intro j hj; rw [List.mem_singleton.1 hj, hl2]
      · intro p hp; rw [(mem_Gq hp).1, hl2]
    rw [hcu, hl2]
    simp only [List.append_assoc]
  · -- `q` passive
    rw [hlocq]; exact hpas3
  · -- others passive
    intro r hr
    rw [hlocr r hr, lstate_concat]
    have := (hI.invisible_reads P4 hV4 r rd hro hw).1
    rw [this]; exact hpas4 r hr
  · -- RB deliveries
    rintro i (rfl | hi) k hk
    · have hk2 : k < (I.rbCasts i (I.loc i P2)).length :=
        lt_of_lt_of_le hk (rbCasts_length_mono (loc_prefix hPP2 i) i)
      obtain ⟨m, hm⟩ := rb_delivered_blk (P := P2) i G2 (List.mem_singleton_self i) hk2
      exact ⟨m, by rw [hlocq]; exact hm⟩
    · have hk3 : k < (I.rbCasts q (I.loc q P3)).length :=
        lt_of_lt_of_le hk (rbCasts_length_mono (loc_prefix (hPP2.trans hP23) q) q)
      obtain ⟨m, hm⟩ := hdel4 i hi q (List.mem_finRange q) k hk3
      exact ⟨m, by rw [hlocr i hi]; exact List.mem_append_left _ hm⟩
  · -- TOB deliveries
    have hmemG : ∀ (L : List I.Input) (G : List (Fin n × ℕ)), L.filterMap LIn.tobId = G →
        ∀ k, (q, k) ∈ G → ∃ m, LIn.tob q k m ∈ L := by
      intro L G hG k hk
      rw [← hG] at hk
      obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.1 hk
      cases x <;> simp [LIn.tobId] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      exact ⟨_, hx⟩
    rintro i (rfl | hi) k hk
    · have hk2 : (i, k) ∈ G2 := by
        simp only [G2, Gq, List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨k, lt_of_lt_of_le hk (tobCasts_length_mono (loc_prefix hPP2 i) i), trivial, rfl⟩
      obtain ⟨m, hm⟩ := hmemG _ _ hseq3q k hk2
      exact ⟨m, by rw [hlocq]; exact hm⟩
    · have hk3 : (q, k) ∈ G3 := by
        simp only [G3, Gq, List.mem_map, List.mem_range, Prod.mk.injEq]
        exact ⟨k, lt_of_lt_of_le hk (tobCasts_length_mono (loc_prefix (hPP2.trans hP23) q) q),
          trivial, rfl⟩
      obtain ⟨m, hm⟩ := hmemG _ _ (hseq4 i hi) k hk3
      exact ⟨m, by rw [hlocr i hi]; exact List.mem_append_left _ hm⟩
  · -- invocations
    rintro i (rfl | hi)
    · refine ⟨LIn.inv rd .strong, ?_, trivial⟩
      obtain ⟨R, hR⟩ := hP34
      have hR' : P3 ++ R = P4 := hR
      rw [List.drop_append_of_le_length hPP4.length_le]
      apply List.mem_append_left
      rw [← hR', hP3, hP2, invBlk]
      simp only [List.append_assoc]
      rw [List.drop_append_of_le_length le_rfl, List.drop_length]
      simp
    · refine ⟨LIn.inv rd .weak, ?_, trivial⟩
      rw [List.drop_append_of_le_length hPP4.length_le]
      exact List.mem_append_right _ (List.mem_map.2 ⟨i, hi, rfl⟩)
  · -- local views of other replicas
    intro i hi
    obtain ⟨δ, hδ, hδl⟩ := hδ4 i
    have h3 : I.loc i P3 = I.loc i P := by
      rw [hP3, loc_append, I.loc_atR_ne (Ne.symm hi), List.append_nil, hP2,
        loc_invBlk_ne (Ne.symm hi)]
    refine ⟨δ ++ (if i ∈ Os then [LIn.inv rd .weak] else []), ?_, ?_⟩
    · rw [loc_append, loc_reads hOs, hδ, h3, List.append_assoc]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hδl x hx
      · split_ifs at hx
        · rw [List.mem_singleton.1 hx]
          rintro ⟨op, l, he, hl⟩
          cases he; exact hl ⟨rfl, hro⟩
        · simp at hx

end Podc.BayouRevisited.Impl
