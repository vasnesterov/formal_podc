import Papers.PODC2010.EventualLinearizability.Defs

/-!
# Weak consistency and `t`-linearizability are nonblocking (Lemmas 3 and 4)

* `weaklyConsistent_nonblocking` (**Lemma 3**): if `H` is weakly consistent and `inv p x o` is a
  pending invocation of a total operation, then some response can be appended so that the
  result is weakly consistent. As in the paper, the response is the one `o` gets when it is
  executed after `τ(i, o')`, where `o'` is the last completed operation of `p` (the paper writes
  `p_j` for `p_i` in its proof).
* `tLinearizable_nonblocking` (**Lemma 4**): the same for `t`-linearizability, with the same set
  of late operations. Since a `t`-permutation contains every invoked operation (P1), the
  pending operation already has a result in the `t`-linearization; totality is not needed.

Theorem 1 combines the two lemmas; that combination fails, see `Theorem1.lean`.
-/

namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- Facts about appending the response to the pending invocation `a = ⟨p, x, cnt N p x⟩`. -/
structure PendingExt (H : History P X Op Res) (p : P) (x : X) (o : Op) (r : Res)
    (a : OpId P X) : Prop where
  inv : Invoked H a
  notCompleted : ¬ Completed H a
  op : opOf H a = some o
  wf : WellFormed (H ++ [.res p x r])
  opOf_eq : ∀ b, opOf (H ++ [.res p x r]) b = opOf H b
  invoked_iff : ∀ b, Invoked (H ++ [.res p x r]) b ↔ Invoked H b
  completed_iff : ∀ b, Completed (H ++ [.res p x r]) b ↔ Completed H b ∨ b = a
  resOf_eq : ∀ b, Completed H b → resOf (H ++ [.res p x r]) b = resOf H b
  resOf_a : resOf (H ++ [.res p x r]) a = some r
  precedes_iff : ∀ c b, Invoked H b → (Precedes (H ++ [.res p x r]) c b ↔ Precedes H c b)
  a_eq : a.p = p ∧ a.x = x

lemma pendingExt {H : History P X Op Res} (hH : WellFormed H) {p : P} {x : X} {o : Op}
    {N : List (OpRec P X Op Res)} (hN : restrictP H p = seqHist N ++ [.inv p x o]) (r : Res) :
    PendingExt H p x o r ⟨p, x, cnt N p x⟩ := by
  set a : OpId P X := ⟨p, x, cnt N p x⟩ with ha_def
  obtain ⟨hai, hac, hao⟩ := PendingInv.spec hH hN
  have hres_len : (ressOf H p x).length = cnt N p x := by
    rw [ressOf_eq_restrictP, hN, ressOf_append, List.length_append,
      length_ressOf_seqHist]; simp
  refine ⟨hai, hac, hao, wellFormed_concat_res.2 ⟨hH, N, o, hN⟩, fun b => by simp [opOf],
    fun b => by simp [Invoked], ?_, fun b hb => resOf_append_of_completed hb, ?_,
    fun c b hb => ⟨fun h => h.of_append_of_invoked hb, fun h => h.mono⟩, rfl, rfl⟩
  · intro b
    rcases b with ⟨q, y, k⟩
    simp only [Completed, ressOf_append, ressOf_cons, Event.resOf_res, ressOf_nil,
      List.append_nil, List.length_append, ha_def, OpId.mk.injEq]
    by_cases hq : p = q ∧ x = y
    · obtain ⟨rfl, rfl⟩ := hq; simp only [and_self, ↓reduceIte, Option.toList_some,
        List.length_singleton, true_and, hres_len]; omega
    · have : ¬ (q = p ∧ y = x) := fun h => hq ⟨h.1.symm, h.2.symm⟩
      simp only [hq, ↓reduceIte, Option.toList_none, List.length_nil, add_zero]
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl, rfl, -⟩)
        · exact h
        · exact absurd ⟨rfl, rfl⟩ this
  · simp only [resOf, ressOf_append, ha_def, ressOf_cons, Event.resOf_res, and_self,
      ↓reduceIte, Option.toList_some, ressOf_nil, List.append_nil]
    rw [List.getElem?_append_right (by omega)]; simp [hres_len]

/-- Nothing is preceded by the operation whose response is the last event. -/
lemma not_precedes_last {H : History P X Op Res} {p : P} {x : X} {o : Op} {r : Res}
    {a : OpId P X} (hE : PendingExt H p x o r a) {b : OpId P X} (hb : Invoked H b) :
    ¬ Precedes (H ++ [.res p x r]) a b := fun h =>
  hE.notCompleted ((hE.precedes_iff a b hb).1 h).completed

omit [DecidableEq P] in
/-- Legality of a sequential history extended by one record of object `x`, given that the
extension is legal for `x`. -/
lemma legal_append_single {spec : SeqSpec P X Op Res} {M : List (OpRec P X Op Res)}
    (hM : Legal spec (seqHist M)) {e : OpRec P X Op Res}
    (he : seqHist ((M.filter (·.x = e.x)) ++ [e]) ∈ spec e.x) :
    Legal spec (seqHist (M ++ [e])) := by
  rw [legal_seqHist_iff] at hM ⊢
  intro y
  by_cases hy : e.x = y
  · subst hy; simpa [List.filter_append] using he
  · simpa [List.filter_append, hy] using hM y

/-- **Lemma 3** (weak consistency is nonblocking). If `inv` is a pending invocation of a total
operation `o` of process `p` on object `x` in a weakly consistent history `H`, then there is a
response such that `H · resp` is weakly consistent. (We assume, as every sequential
specification does, that the empty history is legal: it is used when `p` has no completed
operation, where the paper takes `τ(i, o) = inv · resp`.) -/
theorem weaklyConsistent_nonblocking {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (hH : WellFormed H) (hempty : ∀ y, ([] : History P X Op Res) ∈ spec y)
    (hWC : WeaklyConsistent spec H) {p : P} {x : X} {o : Op}
    (hpend : PendingInv H p x o) (htot : Total spec p x o) :
    ∃ r, WeaklyConsistent spec (H ++ [.res p x r]) := by
  classical
  obtain ⟨τ, hτ⟩ := hWC
  obtain ⟨N, hN⟩ := hpend
  obtain ⟨hai, hanc, -⟩ := PendingInv.spec hH hN
  obtain ⟨a, ha⟩ : ∃ a, a = (⟨p, x, cnt N p x⟩ : OpId P X) := ⟨_, rfl⟩
  rw [← ha] at hai hanc
  -- the base sequence: `τ` of the last completed operation of `p`, if any
  let S : Set (OpId P X) := {b | b.p = p ∧ Completed H b}
  have hex : ∃ B : IdSeq P X Op Res, IsSeqOf spec H B ∧ a ∉ B.ids ∧
      ∀ b, b.p = p → Precedes H b a → ∀ c ∈ (τ b).ids, c ∈ B.ids := by
    by_cases hS : ∃ b, b ∈ S
    · -- the last completed operation `pv` of `p`
      let m := Nat.findGreatest (fun m => ∃ b ∈ S, tRes H b = m) H.length
      obtain ⟨b₀, hb₀⟩ := hS
      have hm : ∃ b ∈ S, tRes H b = m :=
        Nat.findGreatest_spec (P := fun m => ∃ b ∈ S, tRes H b = m) (m := tRes H b₀)
          (tRes_le_length hb₀.2) ⟨b₀, hb₀, rfl⟩
      obtain ⟨pv, hpv, hpvm⟩ := hm
      have hmax : ∀ b ∈ S, tRes H b ≤ tRes H pv := fun b hb => by
        rw [hpvm]; exact Nat.le_findGreatest (tRes_le_length hb.2) ⟨b, hb, rfl⟩
      obtain ⟨hseq, -, hii, -⟩ := hτ pv hpv.2
      have hpva : Precedes H pv a := by
        rcases precedes_or_precedes hH (hpv.1.trans (by rw [ha])) (hH.invoked_of_completed hpv.2) hai
          (fun h => hanc (h ▸ hpv.2)) with h | h
        · exact h
        · exact absurd h.completed hanc
      refine ⟨τ pv, hseq, fun h => hii a h hpva, ?_⟩
      intro b hbp hba c hc
      by_cases hbe : b = pv
      · subst hbe; exact hc
      · have hbS : b ∈ S := ⟨hbp, hba.completed⟩
        have hbpv : Precedes H b pv := by
          rcases precedes_or_precedes hH (hbp.trans hpv.1.symm)
            (hH.invoked_of_completed hbS.2) (hH.invoked_of_completed hpv.2) hbe with h | h
          · exact h
          · exfalso
            have h1 := (precedes_iff.1 h).2
            have h2 := tInv_lt_tRes hH hbS.2
            have h3 := hmax b hbS
            omega
        exact (hτ pv hpv.2).2.2.2 b (hbp.trans hpv.1.symm) hbpv c hc
    · refine ⟨[], ⟨by simp, by simp, ?_⟩, by simp, ?_⟩
      · rw [legal_seqHist_iff]; intro y; simpa using hempty y
      · intro b hbp hba
        exact absurd ⟨hbp, hba.completed⟩ (fun h => hS ⟨b, h⟩)
  obtain ⟨B, hB, haB, hBsup⟩ := hex
  -- the response, by totality
  have hlegx := (legal_seqHist_iff spec B.recs).1 hB.legal x
  obtain ⟨r, hr⟩ := htot (B.recs.filter (·.x = x)) (by simp) hlegx
  set e : OpRec P X Op Res := ⟨p, x, o, r⟩ with he_def
  have E := pendingExt hH hN r
  rw [← ha] at E
  refine ⟨r, fun b => if b = a then B ++ [(a, e)] else τ b, ?_⟩
  intro b hb
  rcases (E.completed_iff b).1 hb with hb | hb'
  · have hba : b ≠ a := by rintro rfl; exact hanc hb
    simp only [hba, ↓reduceIte]
    obtain ⟨hseq, ⟨e', hl, hr'⟩, hii, hiii⟩ := hτ b hb
    refine ⟨⟨fun ae hae => ?_, hseq.nodup, hseq.legal⟩, ⟨e', hl, ?_⟩, ?_, ?_⟩
    · rw [E.opOf_eq]; exact hseq.ofHist ae hae
    · rw [E.resOf_eq b hb]; exact hr'
    · intro c hc h
      obtain ⟨ae, hae, rfl⟩ := List.mem_map.1 hc
      have hci : Invoked H ae.1 := Invoked.of_opOf (hseq.ofHist ae hae).2.2
      exact hii _ hc ((E.precedes_iff b _ hci).1 h)
    · intro c hcp hcb
      have hcb' := (E.precedes_iff c b (hH.invoked_of_completed hb)).1 hcb
      have hca : c ≠ a := by rintro rfl; exact hanc hcb'.completed
      simp only [hca, ↓reduceIte]
      exact hiii c hcp hcb'
  · subst b
    simp only [↓reduceIte]
    have hrecs : (B ++ [(a, e)]).recs = B.recs ++ [e] := by simp
    refine ⟨⟨fun ae hae => ?_, ?_, ?_⟩, ⟨e, by simp, E.resOf_a⟩, ?_, ?_⟩
    · rcases List.mem_append.1 hae with hae | hae
      · rw [E.opOf_eq]; exact hB.ofHist ae hae
      · rw [List.mem_singleton] at hae; subst hae
        exact ⟨by simp [he_def, ha], by simp [he_def, ha], by rw [E.opOf_eq]; exact E.op⟩
    · simp only [IdSeq.ids, List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.2 ⟨hB.nodup, List.nodup_singleton _,
        fun c hc d hd => by
          rw [List.mem_singleton] at hd; subst hd; rintro rfl; exact haB hc⟩
    · rw [hrecs]; exact legal_append_single hB.legal hr
    · intro c hc
      have hci : Invoked H c := by
        simp only [IdSeq.ids, List.map_append, List.mem_append, List.mem_map,
          List.map_cons, List.map_nil, List.mem_singleton] at hc
        rcases hc with ⟨ae, hae, rfl⟩ | rfl
        · exact Invoked.of_opOf (hB.ofHist ae hae).2.2
        · exact hai
      exact not_precedes_last E hci
    · intro c hcp hca
      have hca' := (E.precedes_iff c a hai).1 hca
      have hne : c ≠ a := by rintro rfl; exact hanc hca'.completed
      simp only [hne, ↓reduceIte]
      intro d hd
      simp only [IdSeq.ids, List.map_append, List.mem_append]
      exact Or.inl (hBsup c (hcp.trans (by rw [ha])) hca' d hd)

/-- **Lemma 4** (`t`-linearizability is nonblocking). If `inv` is a pending invocation of
process `p` on object `x` in a `t`-linearizable history `H`, then there is a response such that
`H · resp` is `t`-linearizable, for the same `t` (the same set `A` of late operations). The
response is the result the pending operation has in the `t`-linearization; totality of the
operation is not needed. -/
theorem tLinearizable_nonblocking {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (hH : WellFormed H) {A : Set (OpId P X)} (hL : TLinearizable spec H A) {p : P} {x : X}
    {o : Op} (hpend : PendingInv H p x o) :
    ∃ r, TLinearizable spec (H ++ [.res p x r]) A := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨N, hN⟩ := hpend
  set a : OpId P X := ⟨p, x, cnt N p x⟩ with ha_def
  obtain ⟨hai, hanc, -⟩ := PendingInv.spec hH hN
  obtain ⟨ae, hae, hae1⟩ := List.mem_map.1 (hL.all a hai)
  have E := pendingExt hH hN ae.2.r
  refine ⟨ae.2.r, L, ⟨⟨⟨fun be hbe => ?_, hL.nodup, hL.legal⟩, fun b hb => ?_, ?_⟩, ?_⟩⟩
  · rw [E.opOf_eq]; exact hL.ofHist be hbe
  · exact hL.all b ((E.invoked_iff b).1 hb)
  · rintro c b ⟨hbA, hbi, hcb⟩
    have hbi' := (E.invoked_iff b).1 hbi
    exact hL.order c b ⟨hbA, hbi', (E.precedes_iff c b hbi').1 hcb⟩
  · intro b f hbf hbA hbc
    rcases (E.completed_iff b).1 hbc with hb | rfl
    · rw [E.resOf_eq b hb]; exact hL.results b f hbf hbA hb
    · rw [E.resOf_a]
      have : ae = (a, f) := by
        have hnd := hL.nodup
        rcases ae with ⟨a', f'⟩
        simp only at hae1; subst hae1
        have := List.inj_on_of_nodup_map hnd hae hbf rfl
        exact this
      rw [this]

end Podc.EventualLinearizability
