import Papers.PODC2016.RWLockRMRTradeoff.Awareness

/-!
# Lemma 2: one step of every poised process at most triples the awareness sets

Given a fragment `C ↪ E` and a set `T` of processes, each poised to access a register, the steps of
`T` can be ordered (each process exactly once) so that `max_p |AW(p)|` grows at most by a factor 3.

We schedule greedily: as long as some remaining step is not a value-changing CAS (w.r.t. the
*current* value of its register), take it; otherwise take any remaining step. This keeps every
familiarity set of size `≤ M`, or of size `≤ 2M` with all remaining CAS steps on that register
bound to fail; so a reading step adds at most `2M` processes to an awareness set of size `≤ M`.

The paper's proof (reads and trivial steps, then writes, then CAS) claims in its case 1 that after
the writes "the value differs from the expected parameter of all CAS steps", which is false (a
write may restore the expected value); the bound still holds because at most one of the CAS steps
on a register succeeds. See `differencies.md`.

`round_expanding`: if all steps of `T` are reading steps (read or CAS), any order preserves
expanding-ness: each process of `T` that is poised on an expanding step takes an expanding step.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable {I : Impl A (Regs ι V v₀) P L} {cm : CacheModel P ι}

/-- A step that is scheduled from configuration `Z`: the effect on the stepping process's
awareness set and on the familiarity set and value of the accessed variable. -/
lemma tau_effect {Z Z' : Ext I cm} {q : P} {j : ι} {o : (Regs ι V v₀ j).Op} {k}
    (hact : I.act q (Z.cfg.loc q) = .access j o k) (hs : xstep Z (.tau q) = some Z') :
    (∀ j', j' ≠ j → Z'.kn.fam j' = Z.kn.fam j' ∧ Z'.cfg.mem j' = Z.cfg.mem j') ∧
    match (o : CASOp V) with
    | .read => Z'.kn.aw q = Z.kn.aw q ∪ Z.kn.fam j ∧ Z'.kn.fam j = Z.kn.fam j ∧
        Z'.cfg.mem j = Z.cfg.mem j
    | .write v => Z'.kn.aw q = Z.kn.aw q ∧
        (Z'.kn.fam j = Z.kn.fam j ∨ Z'.kn.fam j = Z.kn.aw q) ∧ Z'.cfg.mem j = v
    | .cas a b => Z'.kn.aw q = Z.kn.aw q ∪ Z.kn.fam j ∧
        (if Z.cfg.mem j = a ∧ b ≠ a then
          Z'.kn.fam j = Z.kn.aw q ∪ Z.kn.fam j ∧ Z'.cfg.mem j = b
        else Z'.kn.fam j = Z.kn.fam j ∧ Z'.cfg.mem j = Z.cfg.mem j) := by
  obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
  obtain ⟨-, -, i', o', k', hact', hm, -⟩ := Impl.step_tau h1
  rw [hact] at hact'; cases hact'
  refine ⟨fun j' hj' => ⟨?_, ?_⟩, ?_⟩
  · rw [h2]; exact kstep_fam_of_ne I _ _ _ j' (by
      rintro q' i' o' k' hq' hact'
      cases hq'; rw [hact] at hact'; cases hact'; exact Ne.symm hj')
  · rw [hm, Function.update_of_ne hj']
  · rw [h2, hm]
    cases o with
    | read => rw [kstep_read I hact]; simp
    | write v =>
      rw [kstep_write I hact]
      split_ifs with hv
      · simp
      · simp
    | cas a b =>
      rw [kstep_cas I hact]
      simp only [Function.update_self]
      by_cases hc : Z.cfg.mem j = a ∧ b ≠ a
      · simp [hc]
      · simp only [hc, if_false, and_true]
        refine ⟨by simp, ?_⟩
        by_cases ha : Z.cfg.mem j = a
        · have : b = a := by tauto
          simp [ha, this]
        · simp [ha]

section Round

variable (X : Ext I cm) (T : Finset P) (B : ℕ)

/-- `q` is poised (at `X`) on a CAS on `j` that would change the value of `j` at `Z`. -/
def BadAt (Z : Ext I cm) (q : P) : Prop :=
  ∃ j a b k, I.act q (X.cfg.loc q) = .access j (CASOp.cas a b : CASOp V) k ∧
    Z.cfg.mem j = a ∧ b ≠ a

/-- The invariant of the greedy schedule (remaining processes `R`). -/
structure RInv (Z : Ext I cm) (R : Finset P) : Prop where
  fresh : ∀ q ∈ R, Z.cfg.loc q = X.cfg.loc q ∧ Z.cfg.pend q = X.cfg.pend q ∧
    Z.kn.aw q = X.kn.aw q
  aw : ∀ q, (Z.kn.aw q).card ≤ 3 * B
  fam : ∀ j, (Z.kn.fam j).card ≤ B ∨ ((Z.kn.fam j).card ≤ 2 * B ∧
    ∀ q ∈ R, ∀ a b k, I.act q (X.cfg.loc q) = .access j (CASOp.cas a b : CASOp V) k →
      Z.cfg.mem j ≠ a)

variable {X T B}

lemma card_union_le_of {s t : Finset P} {a b : ℕ} (hs : s.card ≤ a) (ht : t.card ≤ b) :
    (s ∪ t).card ≤ a + b := (Finset.card_union_le s t).trans (Nat.add_le_add hs ht)

lemma rinv_step {Z Z' : Ext I cm} {R : Finset P} {q : P} (hRT : R ⊆ T)
    (hX : ∀ q, (X.kn.aw q).card ≤ B) (hI : RInv X B Z R) (hq : q ∈ R)
    (hchoice : BadAt X Z q → ∀ q' ∈ R, BadAt X Z q')
    {j : ι} {o : (Regs ι V v₀ j).Op} {k} (hact : I.act q (X.cfg.loc q) = .access j o k)
    (hs : xstep Z (.tau q) = some Z') : RInv X B Z' (R.erase q) := by
  obtain ⟨hl, hp, ha⟩ := hI.fresh q hq
  have hact' : I.act q (Z.cfg.loc q) = .access j o k := by rw [hl]; exact hact
  obtain ⟨hoth, heff⟩ := tau_effect hact' hs
  obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
  have hawo : ∀ r, r ≠ q → Z'.kn.aw r = Z.kn.aw r := fun r hr =>
    by rw [h2]; exact (kstep_aw I Z.cfg Z.kn (.tau q) r).2 (by simpa [Label.proc] using Ne.symm hr)
  have hqB : (Z.kn.aw q).card ≤ B := ha ▸ hX q
  refine ⟨fun r hr => ?_, fun r => ?_, fun j' => ?_⟩
  · have hrq : r ≠ q := Finset.ne_of_mem_erase hr
    have := Impl.step_other h1 (q := r) (by simpa [Label.proc] using Ne.symm hrq)
    rw [this.1, this.2, hawo r hrq]
    exact hI.fresh r (Finset.mem_of_mem_erase hr)
  · by_cases hrq : r = q
    · subst hrq
      -- the stepping process learns at most one familiarity set of size `≤ 2B`
      have hfj : (Z.kn.fam j).card ≤ 2 * B := by rcases hI.fam j with h | h <;> omega
      cases o with
      | read => rw [heff.1]; have := card_union_le_of hqB hfj; omega
      | write v => rw [heff.1]; omega
      | cas a b => rw [heff.1]; have := card_union_le_of hqB hfj; omega
    · rw [hawo r hrq]; exact hI.aw r
  · by_cases hj : j' = j
    · subst hj
      cases o with
      | read =>
        rw [heff.2.1, heff.2.2]
        exact (hI.fam j').imp_right fun ⟨h1, h2⟩ =>
          ⟨h1, fun r hr => h2 r (Finset.mem_of_mem_erase hr)⟩
      | write v =>
        rcases heff.2.1 with hf | hf
        · rw [hf]
          rcases hI.fam j' with h | ⟨h, -⟩
          · exact Or.inl h
          · -- unchanged familiarity set but changed value: only possible for a trivial write
            obtain ⟨-, -, hm⟩ := heff
            by_cases hv : Z.cfg.mem j' = v
            · refine (hI.fam j').imp_right fun ⟨h1, h2⟩ =>
                ⟨h1, fun r hr a b k h => ?_⟩
              rw [hm, ← hv]; exact h2 r (Finset.mem_of_mem_erase hr) a b k h
            · -- a non-trivial write sets `F(v) := AW(q)`
              have : Z'.kn.fam j' = Z.kn.aw q := by
                rw [h2, kstep_write I hact']; simp [hv]
              left; rw [← hf, this]; exact hqB
        · left; rw [hf]; exact hqB
      | cas a b =>
        obtain ⟨-, heff⟩ := heff
        split_ifs at heff with hc
        · -- a value-changing CAS: by the greedy choice, all remaining steps are such CAS
          have hbad : BadAt X Z q := ⟨j', a, b, k, hact, hc⟩
          have hall := hchoice hbad
          have hfB : (Z.kn.fam j').card ≤ B := by
            rcases hI.fam j' with h | ⟨-, h⟩
            · exact h
            · exact absurd hc.1 (h q hq a b k hact)
          right
          refine ⟨by rw [heff.1]; have := card_union_le_of hqB hfB; omega, ?_⟩
          intro r hr a' b' k' hr'
          obtain ⟨j'', a'', b'', k'', hr'', hm'', hb''⟩ := hall r (Finset.mem_of_mem_erase hr)
          rw [hr'] at hr''
          cases hr''
          intro h
          exact hc.2 ((heff.2.symm.trans h).trans (hm''.symm.trans hc.1))
        · rw [heff.1, heff.2]
          exact (hI.fam j').imp_right fun ⟨h1, h2⟩ =>
            ⟨h1, fun r hr => h2 r (Finset.mem_of_mem_erase hr)⟩
    · obtain ⟨hf, hm⟩ := hoth j' hj
      rw [hf, hm]
      exact (hI.fam j').imp_right fun ⟨h1, h2⟩ =>
        ⟨h1, fun r hr => h2 r (Finset.mem_of_mem_erase hr)⟩

end Round

/-- **Lemma 2.** If every process of `T` is poised to access a register, there is an ordering `l`
of `T` (each process once) such that after `l` every awareness set has at most
`3 · max_p |AW(p)|` elements. -/
theorem lemma2 {X : Ext I cm} (hK : KInv X.kn) (T : Finset P)
    (hT : ∀ p ∈ T, X.cfg.pend p ≠ none ∧ ∃ i o k, I.act p (X.cfg.loc p) = .access i o k)
    {B : ℕ} (hB : ∀ q, (X.kn.aw q).card ≤ B) :
    ∃ l : List P, l.Nodup ∧ l.toFinset = T ∧ ∃ Y, xrun X (l.map .tau) = some Y ∧
      ∀ q, (Y.kn.aw q).card ≤ 3 * B := by
  classical
  -- strong induction on the remaining set
  suffices H : ∀ N, ∀ (Z : Ext I cm) (R : Finset P), R.card = N → R ⊆ T → RInv X B Z R →
      ∃ l : List P, l.Nodup ∧ l.toFinset = R ∧ ∃ Y, xrun Z (l.map .tau) = some Y ∧
        ∀ q, (Y.kn.aw q).card ≤ 3 * B by
    exact H T.card X T rfl subset_rfl
      ⟨fun q _ => ⟨rfl, rfl, rfl⟩, fun q => (hB q).trans (by omega),
        fun j => Or.inl (hK.card_fam_le j hB)⟩
  intro N
  induction N with
  | zero =>
    intro Z R hR _ hI
    rw [Finset.card_eq_zero] at hR; subst hR
    exact ⟨[], List.nodup_nil, rfl, Z, rfl, hI.aw⟩
  | succ N ih =>
    intro Z R hR hRT hI
    -- the greedy choice
    have hne : R.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨q, hq, hchoice⟩ : ∃ q ∈ R, BadAt X Z q → ∀ q' ∈ R, BadAt X Z q' := by
      by_cases h : ∃ q ∈ R, ¬ BadAt X Z q
      · obtain ⟨q, hq, hnb⟩ := h; exact ⟨q, hq, fun hb => absurd hb hnb⟩
      · push Not at h
        obtain ⟨q, hq⟩ := hne
        exact ⟨q, hq, fun _ => h⟩
    obtain ⟨hpend, j, o, k, hact⟩ := hT q (hRT hq)
    obtain ⟨hl, hp, -⟩ := hI.fresh q hq
    have hs := Impl.step_tau_eq_some (I := I) (C := Z.cfg) (by rw [hp]; exact hpend)
      (by rw [hl]; exact hact)
    set Z' : Ext I cm := ⟨_, kstep I Z.cfg Z.kn (.tau q), cacheStep I cm Z.cfg Z.cache (.tau q)⟩
    have hxs : xstep Z (.tau q) = some Z' := xstep_eq_some.2 ⟨hs, rfl, rfl⟩
    have hI' := rinv_step (T := T) hRT hB hI hq hchoice hact hxs
    obtain ⟨l, hnd, hl', Y, hY, hYB⟩ := ih Z' (R.erase q)
      (by rw [Finset.card_erase_of_mem hq]; omega) ((Finset.erase_subset _ _).trans hRT) hI'
    refine ⟨q :: l, ?_, ?_, Y, ?_, hYB⟩
    · refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
      have : q ∈ l.toFinset := List.mem_toFinset.2 h
      rw [hl'] at this; simp at this
    · rw [List.toFinset_cons, hl', Finset.insert_erase hq]
    · rw [List.map_cons, xrun_cons, hxs]; exact hY

/-- In a round in which every process of `T` takes one *reading* step (read or CAS), familiarity
sets only grow and awareness sets of processes that have not stepped yet do not change; hence every
process poised on an expanding step takes an expanding step, whatever the order. -/
theorem round_expanding {X : Ext I cm} (l : List P) (hnd : l.Nodup)
    (hT : ∀ p ∈ l, ∃ i o k, I.act p (X.cfg.loc p) = .access i o k ∧
      (o = (CASOp.read : CASOp V) ∨ ∃ a b, o = (CASOp.cas a b : CASOp V)))
    {Y : Ext I cm} (hY : xrun X (l.map .tau) = some Y) :
    ∀ p ∈ l, Expanding X (.tau p) → 1 ≤ xcount (ExpBy p) X (l.map .tau) := by
  classical
  -- invariant: unstepped processes are fresh, familiarity sets have grown
  suffices H : ∀ (l' : List P) (Z : Ext I cm), l'.Nodup → (∀ p ∈ l', p ∈ l) →
      (∀ p ∈ l', Z.cfg.loc p = X.cfg.loc p ∧ Z.kn.aw p = X.kn.aw p) →
      (∀ j, X.kn.fam j ⊆ Z.kn.fam j) → ∀ Y, xrun Z (l'.map .tau) = some Y →
      ∀ p ∈ l', Expanding X (.tau p) → 1 ≤ xcount (ExpBy p) Z (l'.map .tau) by
    exact H l X hnd (fun _ h => h) (fun _ _ => ⟨rfl, rfl⟩) (fun _ => subset_rfl) Y hY
  intro l'
  induction l' with
  | nil => intro Z _ _ _ _ Y _ p hp; simp at hp
  | cons q l' ih =>
    intro Z hnd hsub hfr hfam Y hY p hp hexp
    simp only [List.map_cons, xrun_cons] at hY
    cases hs : xstep Z (.tau q) with
    | none => simp [hs] at hY
    | some Z' =>
      simp only [hs, Option.bind_some] at hY
      obtain ⟨i, o, k, hact, ho⟩ := hT q (hsub q List.mem_cons_self)
      obtain ⟨hlq, haq⟩ := hfr q List.mem_cons_self
      have hact' : I.act q (Z.cfg.loc q) = .access i o k := by rw [hlq]; exact hact
      obtain ⟨hoth, heff⟩ := tau_effect hact' hs
      have hnd' := List.nodup_cons.1 hnd
      obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
      have hfam' : ∀ j, X.kn.fam j ⊆ Z'.kn.fam j := by
        intro j
        by_cases hj : j = i
        · subst hj
          rcases ho with rfl | ⟨a, b, rfl⟩
          · rw [heff.2.1]; exact hfam j
          · dsimp only at heff
            split_ifs at heff with hc
            · rw [heff.2.1]; exact (hfam j).trans Finset.subset_union_right
            · rw [heff.2.1]; exact hfam j
        · rw [(hoth j hj).1]; exact hfam j
      simp only [List.map_cons, xcount, hs]
      rcases List.mem_cons.1 hp with rfl | hp'
      · -- `p` steps now: its step is expanding
        have : ExpBy p Z (.tau p) := by
          refine ⟨rfl, expanding_iff.2 ⟨p, i, o, k, rfl, hact', ho, fun hs' => ?_⟩⟩
          obtain ⟨p', i', o', k', hp', hact'', -, hn⟩ := expanding_iff.1 hexp
          cases hp'; rw [hact] at hact''; cases hact''
          exact hn ((hfam i).trans (haq ▸ hs'))
        simp [this]
      · have := ih Z' hnd'.2 (fun p h => hsub p (List.mem_cons_of_mem _ h))
          (fun r hr => by
            have hrq : q ≠ r := fun h => hnd'.1 (h ▸ hr)
            have := Impl.step_other h1 (q := r) (by simpa [Label.proc] using hrq)
            refine ⟨this.1.trans (hfr r (List.mem_cons_of_mem _ hr)).1, ?_⟩
            rw [h2, (kstep_aw I Z.cfg Z.kn (.tau q) r).2 (by simpa [Label.proc] using hrq)]
            exact (hfr r (List.mem_cons_of_mem _ hr)).2)
          hfam' Y hY p hp' hexp
        omega

end Podc.RWLockRMRTradeoff
