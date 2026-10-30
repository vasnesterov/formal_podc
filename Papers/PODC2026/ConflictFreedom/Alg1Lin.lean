import Papers.PODC2026.ConflictFreedom.Alg1Inv3
import Podc.Foundations.Data.Mazurkiewicz.Equiv

/-!
# Theorem 4.3: Algorithm 1 is linearizable

The linearization of an execution is (the operations of the commands of) a representative `L` of
the trace committed at the largest round `R` in which something was committed, built
incrementally: whenever a larger round commits a trace `t`, `L` is extended by a schedule `z`
with `[L · z] = t` (Lemma A.1 makes `[L] ≤ t`). The commands of `z` belong to operations that have
not completed yet, which gives the real-time order (this replaces the paper's block-by-block
construction of the representative `t̂`). Responses are correct by Lemmas 4.1–4.2.
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ} [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

section Derived

variable {α : List (Label (Fin n) A)} {C : Cfg A n}

/-- Commands of committed traces belong to invoked operations. -/
lemma validCmd_of_isCom (hI : Inv1 C) (hK : Inv3 α C) {r : ℕ} {t : Tr A n} (ht : IsCom C r t)
    {c : Cmd A n} (hc : c ∈ t.supp) : ValidCmd α c := by
  obtain ⟨q, gq, hq, hpc, hout, -⟩ := ht
  obtain ⟨j, g, hg, hcg⟩ := mem_input_of_mem_output hI hq hpc (by rw [hout]; exact hc)
  exact (hK.known r j g hg c hcg).1

/-- A completed operation committed a trace containing its command. -/
lemma isCom_of_completed (hI : Inv1 C) (hK : Inv3 α C) {a : OpId (Fin n)} (ha : Completed α a) :
    ∃ t o, IsCom C (crOf C a) t ∧ opOf α a = some o ∧ (o, a.1, a.2 + 1) ∈ t.supp ∧
      respOf α a = some (retT t (o, a.1, a.2 + 1)) := by
  obtain ⟨g, o, h1, h2, -, h4, h5, h6⟩ := (hK.at_ a.1).compl a.2 ha
  have hpc := (hI.loc a.1).hist_pc _ _ h1
  exact ⟨g.output.1, o, ⟨a.1, g, hI.locAt_of_hist h1, hpc, rfl, h2⟩, h4, h5, h6⟩

lemma opId_mk (o : A.Op) (a : OpId (Fin n)) : opId ((o, a.1, a.2 + 1) : Cmd A n) = a := by
  simp [opId]

end Derived

/-- The ghost linearization: `L` represents the trace committed at the largest committed round
`R`, and its order respects real time. -/
structure LinInv (α : List (Label (Fin n) A)) (C : Cfg A n) (R : ℕ) (L : List (Cmd A n)) :
    Prop where
  nodup : L.Nodup
  top : (R = 0 ∧ L = []) ∨ (1 ≤ R ∧ IsCom C R (NTrace.mk L nodup))
  max : ∀ r t, IsCom C r t → r ≤ R
  rt : ∀ a b, Precedes α a b → b ∈ L.map opId → [a, b].Sublist (L.map opId)

section LinInv

variable {α : List (Label (Fin n) A)} {C : Cfg A n} {R : ℕ} {L : List (Cmd A n)}

lemma LinInv.le_top (hL : LinInv α C R L) (hI : Inv1 C) (hJ : Inv2 C) {r : ℕ} {t : Tr A n}
    (ht : IsCom C r t) : t ≤ NTrace.mk L hL.nodup := by
  rcases hL.top with ⟨hR, -⟩ | ⟨-, htop⟩
  · have hmax := hL.max r t ht
    obtain ⟨q, gq, hq, -⟩ := ht
    have := hI.one_le_of_locAt hq; omega
  · exact lemma_A1' hI hJ ht (hL.max r t ht) htop.isOut

lemma LinInv.valid (hL : LinInv α C R L) (hI : Inv1 C) (hK : Inv3 α C) {c : Cmd A n}
    (hc : c ∈ L) : ValidCmd α c := by
  rcases hL.top with ⟨-, rfl⟩ | ⟨-, htop⟩
  · simp at hc
  · exact validCmd_of_isCom hI hK htop (by simpa using hc)

lemma LinInv.mem_of_completed (hL : LinInv α C R L) (hI : Inv1 C) (hJ : Inv2 C) (hK : Inv3 α C)
    {a : OpId (Fin n)} (ha : Completed α a) :
    ∃ o, opOf α a = some o ∧ (o, a.1, a.2 + 1) ∈ L ∧
      respOf α a = some (retT (NTrace.mk L hL.nodup) (o, a.1, a.2 + 1)) := by
  obtain ⟨t, o, ht, hop, hmem, hresp⟩ := isCom_of_completed hI hK ha
  have hle := hL.le_top hI hJ ht
  refine ⟨o, hop, ?_, ?_⟩
  · have := NTrace.supp_mono hle hmem; simpa using this
  · rw [hresp]
    congr 1
    -- `ret*` of the command is the same in `t` and in its extension `[L]`
    unfold retT
    have hrep : NTrace.mk (D := CmdConflict A n) t.rep t.rep_nodup ≤ NTrace.mk L hL.nodup := by
      simpa using hle
    obtain ⟨z, hz⟩ := NTrace.mk_le_mk_iff.1 hrep
    have hnd : (t.rep ++ z).Nodup := (hz.1.nodup_iff).1 hL.nodup
    have hcm : (o, a.1, a.2 + 1) ∈ t.rep := NTrace.mem_supp.1 hmem
    have hD : ∀ x y : Cmd A n, ¬ CmdConflict A n x y → ∀ q, Commute (cmdδ A n) x y q :=
      fun x y hxy q => commute_of_not_conflict hxy q
    rw [respFirst_eq_of_nequiv hD (NTrace.rep_nodup _) hL.nodup (NTrace.rep_mk_nequiv L hL.nodup),
      respFirst_eq_of_nequiv hD hL.nodup hnd hz, respFirst_append_of_mem _ hcm]

end LinInv

/-- Legality: if every completed instance of a command of `L` returned the response of the
command in `L`, the sequential history of `L` is legal. -/
lemma seqOK_of_respFirst {α : List (Label (Fin n) A)} :
    ∀ (L : List (Cmd A n)) (q : A.State), L.Nodup →
      (∀ c ∈ L, ∀ r, respOf α (opId c) = some r → respFirst (cmdδ A n) q L c = some r) →
      SeqOK α q (L.map fun c => (opId c, c.1))
  | [], _, _, _ => trivial
  | c :: L, q, hnd, h => by
    refine ⟨fun r hr => ?_, ?_⟩
    · have := h c (by simp) r hr
      simp only [respFirst_cons, if_true, Option.some.injEq] at this
      exact this
    · refine seqOK_of_respFirst L _ (List.nodup_cons.1 hnd).2 fun c' hc' r hr => ?_
      have hne : c ≠ c' := fun he => (List.nodup_cons.1 hnd).1 (he ▸ hc')
      have := h c' (by simp [hc']) r hr
      simpa [respFirst_cons, hne, cmdδ] using this

lemma Inv1.le_r_of_locAt {C : Cfg A n} (hI : Inv1 C) {i : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (h : locAt (C.loc i) r = some g) : r ≤ (C.loc i).r := by
  unfold locAt at h
  split at h
  · split_ifs at h with hr
    · exact hr.le
    · exact ((hI.loc i).hist_le r (by rw [h]; simp)).2
  · exact ((hI.loc i).hist_le r (by rw [h]; simp)).2

/-- Commit rounds are bounded. -/
lemma Inv1.isCom_le {C : Cfg A n} (hI : Inv1 C) {r : ℕ} {t : Tr A n} (h : IsCom C r t) :
    r ≤ Finset.univ.sup fun i => (C.loc i).r := by
  obtain ⟨i, g, hg, -⟩ := h
  exact (hI.le_r_of_locAt hg).trans (Finset.le_sup (f := fun i => (C.loc i).r) (Finset.mem_univ i))

lemma rt_of_concat {α : List (Label (Fin n) A)} {ℓ : Label (Fin n) A} {M : List (OpId (Fin n))}
    (hM : ∀ b ∈ M, Invoked (α ++ [ℓ]) b) {a b : OpId (Fin n)} (h : Precedes (α ++ [ℓ]) a b)
    (hb : b ∈ M) : Precedes α a b := by
  rcases precedes_concat h with h | ⟨-, h2⟩
  · exact h
  · exact absurd (hM b hb) h2

theorem LinInv.step {α : List (Label (Fin n) A)} {ℓ : Label (Fin n) A} {C C' : Cfg A n}
    {R : ℕ} {L : List (Cmd A n)} (hrun : (impl (A := A) (n := n)).run α = some C)
    (hrun' : (impl (A := A) (n := n)).run (α ++ [ℓ]) = some C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') (hL : LinInv α C R L) :
    ∃ R' L', LinInv (α ++ [ℓ]) C' R' L' := by
  obtain ⟨hI, hJ, hK⟩ := inv_of_run hrun
  obtain ⟨hI', hJ', hK'⟩ := inv_of_run hrun'
  have hvalid' : ∀ R' L' (hnd : L'.Nodup), (R' = 0 ∧ L' = []) ∨ (1 ≤ R' ∧ IsCom C' R' (NTrace.mk L' hnd)) →
      ∀ b ∈ L'.map opId, Invoked (α ++ [ℓ]) b := by
    intro R' L' hnd htop b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    rcases htop with ⟨-, rfl⟩ | ⟨-, htop⟩
    · simp at hc
    · exact (validCmd_of_isCom hI' hK' htop (by simpa using hc)).invoked
  by_cases hnew : ∃ r t, IsCom C' r t ∧ R < r
  · obtain ⟨r0, t0, ht0, hr0⟩ := hnew
    set B := Finset.univ.sup fun i => (C'.loc i).r with hB
    let Pc : ℕ → Prop := fun r => ∃ t, IsCom C' r t
    set R' := Nat.findGreatest Pc B with hR'
    have hr0B : r0 ≤ B := hI'.isCom_le ht0
    have hr0R' : r0 ≤ R' := Nat.le_findGreatest hr0B ⟨t0, ht0⟩
    have hPR' : Pc R' := Nat.findGreatest_spec hr0B ⟨t0, ht0⟩
    obtain ⟨t', ht'⟩ := hPR'
    have hmaxR' : ∀ r t, IsCom C' r t → r ≤ R' := fun r t ht =>
      Nat.le_findGreatest (hI'.isCom_le ht) ⟨t, ht⟩
    have hle : NTrace.mk L hL.nodup ≤ t' := by
      rcases hL.top with ⟨-, hLnil⟩ | ⟨-, htop⟩
      · subst hLnil
        have : NTrace.mk (D := CmdConflict A n) [] hL.nodup = ⊥ := (NTrace.bot_eq).symm
        rw [this]; exact bot_le
      · exact lemma_A1' hI' hJ' (htop.step hI hI' h) (by omega) ht'.isOut
    obtain ⟨z, hz, hzt⟩ := NTrace.exists_append_of_le hle
    have hR1 : 1 ≤ R' := by obtain ⟨q, gq, hq, -⟩ := ht'; exact hI'.one_le_of_locAt hq
    have htop' : (R' = 0 ∧ L ++ z = []) ∨ (1 ≤ R' ∧ IsCom C' R' (NTrace.mk (L ++ z) hz)) :=
      Or.inr ⟨hR1, by rw [hzt]; exact ht'⟩
    refine ⟨R', L ++ z, hz, htop', hmaxR', fun a b hab hb => ?_⟩
    have hab' := rt_of_concat (hvalid' R' (L ++ z) hz htop') hab hb
    obtain ⟨o, -, hamem, -⟩ := hL.mem_of_completed hI hJ hK hab'.completed
    have ha : a ∈ L.map opId := List.mem_map.2 ⟨_, hamem, opId_mk o a⟩
    rw [List.map_append] at hb ⊢
    by_cases hbL : b ∈ L.map opId
    · exact (hL.rt a b hab' hbL).trans (List.sublist_append_left _ _)
    · have hbz : b ∈ z.map opId := by
        rcases List.mem_append.1 hb with h1 | h1
        · exact absurd h1 hbL
        · exact h1
      exact (List.singleton_sublist.2 ha).append (List.singleton_sublist.2 hbz)
  · push Not at hnew
    have htop : (R = 0 ∧ L = []) ∨ (1 ≤ R ∧ IsCom C' R (NTrace.mk L hL.nodup)) := by
      rcases hL.top with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2.step hI hI' h⟩
    refine ⟨R, L, hL.nodup, htop, fun r t ht => ?_, fun a b hab hb => ?_⟩
    · by_contra hlt; exact absurd (hnew r t ht) (by omega)
    · exact hL.rt a b (rt_of_concat (hvalid' R L hL.nodup htop) hab hb) hb

/-- The ghost linearization exists along every execution. -/
theorem exists_linInv {α : List (Label (Fin n) A)} {C : Cfg A n}
    (h : (impl (A := A) (n := n)).run α = some C) : ∃ R L, LinInv α C R L := by
  refine Impl.run_induction (Q := fun α C => ∃ R L, LinInv α C R L) ?_ ?_ h
  · refine ⟨0, [], List.nodup_nil, Or.inl ⟨rfl, rfl⟩, fun r t ht => ?_, fun a b _ hb => by simp at hb⟩
    obtain ⟨i, g, hg, -⟩ := ht
    simp [Impl.initCfg, impl, locAt] at hg
  · rintro α C ℓ C' hrun ⟨R, L, hL⟩ hs
    exact hL.step hrun (by rw [Impl.run_concat, hrun]; exact hs) hs

/-- Theorem 4.3 of [KST26]: Algorithm 1 (with Algorithm 2 implementing every `GCA_r`) is a
linearizable implementation of the sequential object `A`. -/
theorem linearizable : (impl (A := A) (n := n)).Linearizable := by
  refine Impl.linearizable_of_run fun α C hrun => ?_
  obtain ⟨hI, hJ, hK⟩ := inv_of_run hrun
  obtain ⟨R, L, hL⟩ := exists_linInv hrun
  have hmapfst : (L.map fun c => (opId c, c.1)).map Prod.fst = L.map opId := by
    simp [Function.comp_def]
  refine ⟨L.map fun c => (opId c, c.1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmapfst]
    refine List.Nodup.map_on (fun c hc c' hc' he => ?_) hL.nodup
    have h1 := hL.valid hI hK hc
    have h2 := hL.valid hI hK hc'
    have hop : c.1 = c'.1 := by
      have := h1.2; rw [he, h2.2] at this; exact (Option.some.inj this).symm
    obtain ⟨o, i, k⟩ := c
    obtain ⟨o', i', k'⟩ := c'
    simp only [opId, Prod.mk.injEq] at he hop h1 h2
    obtain ⟨rfl, hk⟩ := he
    have hk1 : 1 ≤ k := h1.1
    have hk2 : 1 ≤ k' := h2.1
    simp only [Prod.mk.injEq]
    exact ⟨hop, trivial, by omega⟩
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact (hL.valid hI hK hc).2
  · intro a ha
    rw [hmapfst]
    obtain ⟨o, -, hamem, -⟩ := hL.mem_of_completed hI hJ hK ha
    exact List.mem_map.2 ⟨_, hamem, opId_mk o a⟩
  · intro a b hab hb
    rw [hmapfst] at hb ⊢
    exact hL.rt a b hab hb
  · refine seqOK_of_respFirst L A.init hL.nodup fun c hc r hr => ?_
    have hv := hL.valid hI hK hc
    have hcomp : Completed α (opId c) := completed_iff_respOf.2 (by rw [hr]; rfl)
    obtain ⟨o, hop, hmem, hresp⟩ := hL.mem_of_completed hI hJ hK hcomp
    have hc' : ((o, (opId c).1, (opId c).2 + 1) : Cmd A n) = c := by
      have : o = c.1 := by rw [hv.2] at hop; exact (Option.some.inj hop).symm
      obtain ⟨o', i, k⟩ := c
      have hk1 : 1 ≤ k := hv.1
      simp only [opId]
      rw [this, Nat.sub_add_cancel hk1]
    rw [hc', hr] at hresp
    simp only [Option.some.injEq] at hresp
    rw [hresp]
    unfold retT
    have hD : ∀ x y : Cmd A n, ¬ CmdConflict A n x y → ∀ q, Commute (cmdδ A n) x y q :=
      fun x y hxy q => commute_of_not_conflict hxy q
    rw [respFirst_eq_of_nequiv hD (NTrace.rep_nodup _) hL.nodup (NTrace.rep_mk_nequiv L hL.nodup)]
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 ((respFirst_isSome_iff (cmdδ A n) A.init L c).2 hc)
    rw [hv']; rfl

end Alg1

end Podc.ConflictFreedom
