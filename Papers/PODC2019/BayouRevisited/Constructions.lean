import Papers.PODC2019.BayouRevisited.Rounds

/-!
# Further lemmas for the constructions of Theorem 5

* weak reads of a read-only operation do not change states;
* catch-up blocks contain no invocations;
* iterated rounds.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} {I : Impl n Op Val} {S : ACTSpec Op Val}

/-- All invocations in `R` are of operations satisfying `ops`. -/
def OpsIn (ops : Op → Prop) (R : List I.Act) : Prop :=
  ∀ a ∈ R, ∀ op l, a.2 = .inv op l → ops op

lemma OpsIn.append {ops : Op → Prop} {R R' : List I.Act} (h : OpsIn ops R)
    (h' : OpsIn ops R') : OpsIn ops (R ++ R') := by
  intro a ha op l hal
  rcases List.mem_append.1 ha with ha | ha
  · exact h a ha op l hal
  · exact h' a ha op l hal

lemma mem_of_mem_loc {i : Fin n} {x : I.Input} {P : List I.Act} (h : x ∈ I.loc i P) :
    (i, x) ∈ P := by
  obtain ⟨a, ha, hax⟩ := List.mem_filterMap.1 h
  split_ifs at hax with hai
  cases hax; rw [← hai]; exact ha

lemma lstate_reads (hI : I.IsACT S) {rd : Op} (hro : RDT.IsReadOnly S.F rd)
    (hw : Level.weak ∈ S.lvlmap rd) {P : List I.Act} (L : List I.Act)
    (hV : I.Valid S (P ++ L)) (hL : ∀ a ∈ L, a.2 = .inv rd .weak) (i : Fin n) :
    I.lstate i (I.loc i (P ++ L)) = I.lstate i (I.loc i P) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L a ih =>
    rw [← List.append_assoc] at hV ⊢
    have hV' := hV.of_append
    rw [loc_append (P := P ++ L), loc_singleton]
    obtain ⟨j, xa⟩ := a
    have hxa : xa = .inv rd .weak := hL (j, xa) (by simp)
    subst hxa
    split_ifs with hj
    · subst hj
      rw [lstate_concat, (hI.invisible_reads _ hV' j rd hro hw).1]
      exact ih hV' (fun b hb => hL b (by simp [hb]))
    · simp only [List.append_nil]; exact ih hV' (fun b hb => hL b (by simp [hb]))

lemma not_inv_blk (i : Fin n) (Ss : List (Fin n)) (G : List (Fin n × ℕ)) (P : List I.Act) :
    ∀ x ∈ I.blk i Ss G P, ∀ op l, x ≠ .inv op l := by
  intro x hx op l hxe
  subst hxe
  simp only [blk, cu, cuL, List.mem_append] at hx
  rcases hx with (h | h) | h
  · obtain ⟨_, -, _, _, h, -⟩ := mem_catchRBs.1 h; cases h
  · obtain ⟨_, _, _, h, -⟩ := mem_catchTOB h; cases h
  · simp [intBlk] at h

lemma blkFold_noInv (Ss : List (Fin n)) (G : List (Fin n × ℕ)) :
    ∀ (Rs : List (Fin n)) (P : List I.Act), ∃ R, I.blkFold Rs Ss G P = P ++ R ∧
      ∀ a ∈ R, ∀ op l, a.2 ≠ .inv op l
  | [], P => ⟨[], by simp [blkFold], by simp⟩
  | r :: Rs, P => by
    obtain ⟨R, hR, hRi⟩ := blkFold_noInv Ss G Rs (P ++ I.atR r (I.blk r Ss G P))
    refine ⟨I.atR r (I.blk r Ss G P) ++ R, by rw [blkFold, hR, List.append_assoc], ?_⟩
    intro a ha op l
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact not_inv_blk r Ss G P x hx op l
    · exact hRi a ha op l

lemma blkFold_opsIn (ops : Op → Prop) (Rs Ss : List (Fin n)) (G : List (Fin n × ℕ))
    (P : List I.Act) : ∃ R, I.blkFold Rs Ss G P = P ++ R ∧ OpsIn ops R := by
  obtain ⟨R, hR, hRi⟩ := blkFold_noInv Ss G Rs P
  exact ⟨R, hR, fun a ha op l h => absurd h (hRi a ha op l)⟩

lemma round_opsIn (q : Fin n) (Os : List (Fin n)) (rd : Op) (P : List I.Act) :
    ∃ R, I.round q Os rd P = P ++ R ∧ OpsIn (· = rd) R := by
  simp only [round]
  set P2 := I.invBlk q rd .strong P
  set P3 := P2 ++ I.atR q (I.blk q [q] (I.Gq q (I.loc q P2)) P2)
  obtain ⟨R, hR, hRo⟩ := blkFold_opsIn (· = rd) Os (List.finRange n) (I.Gq q (I.loc q P3)) P3
  refine ⟨[(q, .inv rd .strong)] ++ I.atR q (I.intBlk q (I.loc q P ++ [.inv rd .strong])) ++
    I.atR q (I.blk q [q] (I.Gq q (I.loc q P2)) P2) ++ R ++
    Os.map (fun r => (r, LIn.inv rd .weak)), ?_, ?_⟩
  · rw [hR]; simp only [P3, P2, invBlk, List.append_assoc]
  · refine OpsIn.append (OpsIn.append (OpsIn.append (OpsIn.append ?_ ?_) ?_) hRo) ?_
    · intro a ha op l h; simp at ha; subst ha; cases h; rfl
    · intro a ha op l h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      simp [intBlk] at hx; obtain ⟨ι, -, rfl⟩ := hx; cases h
    · intro a ha op l h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact absurd h (not_inv_blk q [q] _ P2 x hx op l)
    · intro a ha op l h
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; cases h; rfl

/-- Specification of iterated rounds. -/
lemma rounds_spec (hI : I.IsACT S) {q : Fin n} {Os : List (Fin n)} (hOs : Os.Nodup)
    (hq : q ∉ Os) {rd : Op} (hw : Level.weak ∈ S.lvlmap rd) (hs : Level.strong ∈ S.lvlmap rd)
    (hro : RDT.IsReadOnly S.F rd) {P : List I.Act} (hP : I.Valid S P)
    (hpre : ∀ i', I.tobSeq i' P <+: I.Gq q (I.loc q P)) (K : ℕ) :
    I.Valid S (I.rounds q Os rd P K) ∧
    (∀ i', I.tobSeq i' (I.rounds q Os rd P K) <+: I.Gq q (I.loc q (I.rounds q Os rd P K))) ∧
    I.loc q (I.rounds q Os rd P K) = I.qRoundsL q rd (I.loc q P) K ∧
    (∃ R, I.rounds q Os rd P K = P ++ R ∧ OpsIn (· = rd) R) ∧
    (∀ i, i ≠ q → ∃ δ, I.loc i (I.rounds q Os rd P K) = I.loc i P ++ δ ∧
      ∀ x ∈ δ, ¬ Licensing S x) := by
  induction K with
  | zero => exact ⟨hP, hpre, rfl, ⟨[], by simp [rounds], fun _ h => by simp at h⟩,
      fun i _ => ⟨[], by simp [rounds], by simp⟩⟩
  | succ K ih =>
    obtain ⟨hV, hpr, hloc, ⟨R, hR, hRo⟩, hδ⟩ := ih
    obtain ⟨h1, -, h3, h4, -, -, -, -, -, h10⟩ := round_spec hI hOs hq hw hs hro hV hpr
    refine ⟨h1, h3, ?_, ?_, ?_⟩
    · simp only [rounds]; rw [h4, hloc]; rfl
    · obtain ⟨R', hR', hR'o⟩ := round_opsIn q Os rd (I.rounds q Os rd P K)
      refine ⟨R ++ R', ?_, hRo.append hR'o⟩
      simp only [rounds]; rw [hR', hR, List.append_assoc]
    · intro i hi
      obtain ⟨δ, hδe, hδl⟩ := hδ i hi
      obtain ⟨δ', hδ'e, hδ'l⟩ := h10 i hi
      refine ⟨δ ++ δ', ?_, fun x hx => ?_⟩
      · simp only [rounds]; rw [hδ'e, hδe, List.append_assoc]
      · rcases List.mem_append.1 hx with hx | hx
        · exact hδl x hx
        · exact hδ'l x hx

lemma blkFold_loc_not_mem (Ss : List (Fin n)) (G : List (Fin n × ℕ)) {r : Fin n} :
    ∀ (Rs : List (Fin n)) (P : List I.Act), r ∉ Rs →
      I.loc r (I.blkFold Rs Ss G P) = I.loc r P
  | [], _, _ => rfl
  | r' :: Rs, P, h => by
    simp only [List.mem_cons, not_or] at h
    rw [blkFold, blkFold_loc_not_mem Ss G Rs _ h.2, loc_append, I.loc_atR_ne (Ne.symm h.1),
      List.append_nil]

lemma LIn.exists_of_isInv {x : I.Input} (h : x.IsInv) : ∃ op l, x = .inv op l := by
  cases x <;> simp [LIn.IsInv] at h; exact ⟨_, _, rfl⟩

end Podc.BayouRevisited.Impl
