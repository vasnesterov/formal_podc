import Papers.PODC2016.RWLockRMRTradeoff.Awareness

/-!
# Lemma 1 (expanding steps and RMRs), repaired

The paper's Lemma 1 claims that *every* expanding step incurs an RMR. This is false for the
paper's own definitions in the write-back CC model (`Counterexample.lean`): after a *trivial* write
(which does not change the familiarity set, Definition 1) the writer holds an exclusive copy and its
next read of the variable can be expanding without an RMR.

What the lower bound needs, and what we prove here (`lemma1_count`), is the counting version: in
every execution fragment `C ↪ E` (knowledge measured from `C`, arbitrary cache state at `C`) and for
every process `p`, the number of expanding steps of `p` is at most the number of RMRs of `p`.
The proof charges each expanding step without RMR to the earlier RMR that created `p`'s valid
cached copy (potential: the number of variables of which `p` holds a valid copy but whose
familiarity set it does not know).
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {A : ObjSpec} {ι V P L : Type} [DecidableEq ι] [DecidableEq V] [DecidableEq P] {v₀ : V}
variable {I : Impl A (Regs ι V v₀) P L} {cm : CacheModel P ι}

/-- An access that does not change the value does not change the familiarity set. -/
lemma kstep_fam_of_not_changes {C : Config A (Regs ι V v₀) P L} {K : Know P ι} {q : P} {i : ι}
    {o : (Regs ι V v₀ i).Op} {k} (hact : I.act q (C.loc q) = .access i o k)
    (hc : (accessOf (C.mem i) (o : CASOp V)).changes = false) :
    (kstep I C K (.tau q)).fam = K.fam := by
  cases o with
  | read => rw [kstep_read I hact]
  | write v =>
    rw [kstep_write I hact]
    simp only [accessOf, Access.changes, decide_eq_false_iff_not, not_not] at hc
    simp [hc]
  | cas a b =>
    rw [kstep_cas I hact]
    simp only [accessOf, Access.changes, decide_eq_false_iff_not] at hc
    simp [hc]

variable (p : P)

/-- `p` holds a valid copy of `v` but does not know `F(v)`: a "token" that a later expanding step
of `p` on `v` may consume without an RMR. -/
def Tok (X : Ext I cm) (i : ι) : Prop := cm.valid X.cache p i ∧ ¬ X.kn.fam i ⊆ X.kn.aw p

open Classical in
/-- The potential: number of tokens among the variables `S`. -/
noncomputable def Φ (X : Ext I cm) (S : Finset ι) : ℕ := (S.filter (Tok p X)).card

variable (I) in
/-- The variables accessed by a label. -/
def accSet (C : Config A (Regs ι V v₀) P L) (ℓ : Label P A) : Finset ι :=
  match accessAt I C ℓ with
  | some (i, _) => {i}
  | none => ∅

variable {p}

open Classical in
/-- One step of the potential argument. -/
lemma tok_step {X Y : Ext I cm} {ℓ : Label P A} (hs : xstep X ℓ = some Y) (S : Finset ι)
    (hS : ∀ j ∉ S, X.kn.fam j = ∅) :
    (∀ j ∉ S ∪ accSet I X.cfg ℓ, Y.kn.fam j = ∅) ∧
    (if ExpBy p X ℓ then 1 else 0) + Φ p Y (S ∪ accSet I X.cfg ℓ) ≤
      (if RMRBy p X ℓ then 1 else 0) + Φ p X S := by
  obtain ⟨h1, h2, h3⟩ := xstep_eq_some.1 hs
  have hawp := kstep_aw I X.cfg X.kn ℓ
  rw [← h2] at hawp
  -- tokens at the start live in `S`
  have htokS : ∀ j, Tok p X j → j ∈ S := fun j hj => by
    by_contra hjS; apply hj.2; rw [hS j hjS]; exact Finset.empty_subset _
  cases ℓ with
  | inv q o =>
    have hK : Y.kn = X.kn := by rw [h2]; rfl
    have hc : Y.cache = X.cache := by rw [h3]; rfl
    have hacc : accSet I X.cfg (.inv q o) = ∅ := rfl
    have hE : ¬ ExpBy p X (.inv q o) := fun ⟨_, h⟩ => by
      obtain ⟨_, _, _, _, h, _⟩ := expanding_iff.1 h; cases h
    rw [hacc, Finset.union_empty]
    refine ⟨fun j hj => by rw [hK]; exact hS j (by simpa using hj), ?_⟩
    have hT : Tok p Y = Tok p X := by funext j; simp [Tok, hK, hc]
    simp only [hE, ite_false, Φ]
    rw [show (Finset.filter (Tok p Y) S) = Finset.filter (Tok p X) S from by simp only [hT]]; omega
  | ret q r =>
    have hK : Y.kn = X.kn := by rw [h2]; rfl
    have hc : Y.cache = X.cache := by rw [h3]; rfl
    have hacc : accSet I X.cfg (.ret q r) = ∅ := rfl
    have hE : ¬ ExpBy p X (.ret q r) := fun ⟨_, h⟩ => by
      obtain ⟨_, _, _, _, h, _⟩ := expanding_iff.1 h; cases h
    rw [hacc, Finset.union_empty]
    refine ⟨fun j hj => by rw [hK]; exact hS j (by simpa using hj), ?_⟩
    have hT : Tok p Y = Tok p X := by funext j; simp [Tok, hK, hc]
    simp only [hE, ite_false, Φ]
    rw [show (Finset.filter (Tok p Y) S) = Finset.filter (Tok p X) S from by simp only [hT]]; omega
  | tau q =>
    obtain ⟨-, -, i, o, k, hact, -, -⟩ := Impl.step_tau h1
    have hacc : accessAt I X.cfg (.tau q) = some (i, accessOf (X.cfg.mem i) (o : CASOp V)) := by
      simp [accessAt, hact]
    have hset : accSet I X.cfg (.tau q) = {i} := by simp [accSet, hacc]
    have hcache : Y.cache = cm.step X.cache q i (accessOf (X.cfg.mem i) (o : CASOp V)) := by
      rw [h3]; simp [cacheStep, hacc, Label.proc]
    have hrmr : RMRBy p X (.tau q) ↔ q = p ∧ cm.rmr X.cache q i (accessOf (X.cfg.mem i) o) := by
      simp [RMRBy, IsRMR, hacc, Label.proc]
    have hfj : ∀ j, j ≠ i → Y.kn.fam j = X.kn.fam j := fun j hj => by
      rw [h2]; exact kstep_fam_of_ne I _ _ _ j (by
        rintro q' i' o' k' hq' hact'
        cases hq'; rw [hact] at hact'; cases hact'; exact Ne.symm hj)
    -- validity at other variables can only be lost
    have hvj : ∀ j, j ≠ i → cm.valid Y.cache p j → cm.valid X.cache p j := fun j hj hv => by
      rw [hcache] at hv; exact cm.valid_of_step _ _ _ _ _ _ hv (Or.inr (Ne.symm hj))
    have htokj : ∀ j, j ≠ i → Tok p Y j → Tok p X j := fun j hj ⟨hv, hn⟩ =>
      ⟨hvj j hj hv, fun hsub => hn (by rw [hfj j hj]; exact hsub.trans (hawp p).1)⟩
    rw [hset]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hji : j ≠ i := fun h => hj (by simp [h])
      rw [hfj j hji]; exact hS j (fun h => hj (Finset.mem_union_left _ h))
    -- the key case analysis at variable `i`
    by_cases hqp : q = p
    · subst hqp
      by_cases hE : ExpBy q X (.tau q)
      · obtain ⟨q', i', o', k', hq', hact', ho', hn⟩ := expanding_iff.1 hE.2
        cases hq'; rw [hact] at hact'; cases hact'
        -- after a reading step `F(v) ⊆ AW(q)`
        have hnoY : ¬ Tok q Y i := by
          rintro ⟨-, hn'⟩; apply hn'
          rw [h2]
          rcases ho' with rfl | ⟨a, b, rfl⟩
          · rw [kstep_read I hact]; simp
          · rw [kstep_cas I hact]; simp only [Function.update_self]
            split_ifs <;> simp
        have hsub : (({i} ∪ S) ∪ S).filter (Tok q Y) ⊆ (S.filter (Tok q X)).erase i := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton] at hj
          obtain ⟨-, hj⟩ := hj
          have hji : j ≠ i := by rintro rfl; exact hnoY hj
          have := htokj j hji hj
          simp [hji, htokS j this, this]
        have hsub' : (S ∪ {i}).filter (Tok q Y) ⊆ (S.filter (Tok q X)).erase i := by
          intro j hj; apply hsub; simp only [Finset.mem_filter, Finset.mem_union] at hj ⊢
          tauto
        by_cases hR : RMRBy q X (.tau q)
        · simp only [hE, hR, ite_true, Φ]
          have := Finset.card_le_card hsub'
          have := Finset.card_erase_le (s := S.filter (Tok q X)) (a := i)
          omega
        · -- no RMR: the copy was valid, so `p` held a token at `i`
          have hv : cm.valid X.cache q i := by
            by_contra hv; exact hR (hrmr.2 ⟨rfl, cm.rmr_of_not_valid _ _ _ _ hv⟩)
          have hti : i ∈ S.filter (Tok q X) := by
            have ht : Tok q X i := ⟨hv, hn⟩
            simp [htokS i ht, ht]
          simp only [hE, hR, ite_true, ite_false, Φ]
          have := Finset.card_le_card hsub'
          have := Finset.card_erase_of_mem hti
          have := Finset.card_pos.2 ⟨i, hti⟩
          omega
      · -- not expanding
        by_cases hR : RMRBy q X (.tau q)
        · have hsub : (S ∪ {i}).filter (Tok q Y) ⊆ insert i (S.filter (Tok q X)) := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton] at hj
            by_cases hji : j = i
            · simp [hji]
            · have := htokj j hji hj.2
              simp [hji, htokS j this, this]
          simp only [hE, hR, ite_true, ite_false, Φ]
          have := Finset.card_le_card hsub
          have := Finset.card_insert_le i (S.filter (Tok q X))
          omega
        · have hv : cm.valid X.cache q i := by
            by_contra hv; exact hR (hrmr.2 ⟨rfl, cm.rmr_of_not_valid _ _ _ _ hv⟩)
          -- a token at `i` after the step was already there
          have hti : Tok q Y i → Tok q X i := by
            rintro ⟨-, hn'⟩
            refine ⟨hv, fun hsub => hn' ?_⟩
            have hne : ¬ Expanding X (.tau q) := fun h => hE ⟨rfl, h⟩
            rw [expanding_iff] at hne
            rw [h2]
            cases o with
            | read => rw [kstep_read I hact]; simp
            | write v =>
              rw [kstep_write I hact]
              split_ifs
              · exact hsub
              · simp
            | cas a b =>
              rw [kstep_cas I hact]; simp only [Function.update_self]
              split_ifs <;> simp
          have hsub : (S ∪ {i}).filter (Tok q Y) ⊆ S.filter (Tok q X) := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton] at hj
            by_cases hji : j = i
            · subst hji; have := hti hj.2; simp [htokS j this, this]
            · have := htokj j hji hj.2
              simp [htokS j this, this]
          simp only [hE, hR, ite_false, Φ]
          have := Finset.card_le_card hsub
          omega
    · -- another process accesses `i`
      have hE : ¬ ExpBy p X (.tau q) := fun h => hqp h.1
      have hR : ¬ RMRBy p X (.tau q) := fun h => hqp h.1
      have hawq : Y.kn.aw p = X.kn.aw p := (hawp p).2 (by simpa [Label.proc] using hqp)
      have hti : Tok p Y i → Tok p X i := by
        rintro ⟨hv, hn⟩
        by_cases hc : (accessOf (X.cfg.mem i) (o : CASOp V)).changes = true
        · exact absurd (hcache ▸ hv) (cm.not_valid_step _ _ _ _ _ hc hqp)
        · have hf : Y.kn.fam = X.kn.fam := by
            rw [h2]; exact kstep_fam_of_not_changes hact (by simpa using hc)
          refine ⟨?_, by rwa [hf, hawq] at hn⟩
          rw [hcache] at hv; exact cm.valid_of_step _ _ _ _ _ _ hv (Or.inl hqp)
      have hsub : (S ∪ {i}).filter (Tok p Y) ⊆ S.filter (Tok p X) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton] at hj
        by_cases hji : j = i
        · subst hji; have := hti hj.2; simp [htokS j this, this]
        · have := htokj j hji hj.2
          simp [htokS j this, this]
      simp only [hE, hR, ite_false, Φ]
      have := Finset.card_le_card hsub
      omega

/-- Counting along a run. -/
lemma exp_le_rmr_add {X Y : Ext I cm} {β : List (Label P A)} (h : xrun X β = some Y)
    (S : Finset ι) (hS : ∀ j ∉ S, X.kn.fam j = ∅) :
    xcount (ExpBy p) X β ≤ xcount (RMRBy p) X β + Φ p X S := by
  induction β generalizing X S with
  | nil => simp [xcount]
  | cons ℓ β ih =>
    simp only [xrun_cons] at h
    cases hs : xstep X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨hS', hstep⟩ := tok_step (p := p) hs S hS
      have := ih h _ hS'
      simp only [xcount, hs]
      omega

/-- **Lemma 1 (counting form).** In every execution fragment `C ↪ E` (knowledge measured from `C`,
arbitrary cache state at `C`), every process performs at least as many RMRs as expanding steps. -/
theorem lemma1_count {X Y : Ext I cm} {β : List (Label P A)} (hX : X.kn = Know.init)
    (h : xrun X β = some Y) : xcount (ExpBy p) X β ≤ xcount (RMRBy p) X β := by
  have := exp_le_rmr_add (p := p) h ∅ (fun j _ => by rw [hX]; rfl)
  simpa [Φ] using this

end Podc.RWLockRMRTradeoff
