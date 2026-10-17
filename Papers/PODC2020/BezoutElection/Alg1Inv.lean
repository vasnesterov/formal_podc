import Papers.PODC2020.BezoutElection.Alg1Step

/-!
# Algorithm 1: the safety invariant

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Theorem 2 (safety part).

Values of the register `REG` and of pending writes are called the *values* of a configuration
(`InVals`). The invariant `Inv` is the conjunction of

* `Basic`: identifiers in `discarded` sets are identifiers of losers; a pending write of an
  identifier is `⟨id_p, discarded_p, phase_p⟩` of its non-loser writer `p`; there is always a
  non-loser, and the identifier in `REG` (if any) is the one of a non-loser; bookkeeping of the
  program counters;
* either `NoLead` (no value `⟨id, D, ·⟩` with `|D| = n - 1` has ever been written: everything is
  electing and nobody returns), or `Lead L` for the *leader* `L`: all other processes are losers
  forever, every identifier in a value is `id_L`, every returned value is computed from `id_L`,
  plus the phase-specific facts `ElPart` (while `L` is electing) and `CoPart` (once `L` is
  committing) needed for termination.

When the first value `⟨id_L, D, electing⟩` with `|D| = n - 1` is decided, `D` consists of
identifiers of losers (`Basic`), so all processes but `L` are losers, and `Lead L` starts.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R] {P : Type} [DecidableEq P]

/-! ### Values of a configuration -/

/-- `v` is the content of `REG` or the value of a pending write. -/
def InVals (C : Cfg Id R P) (v : Reg Id) : Prop := reg C = v ∨ ∃ q, (C.loc q).pc = .write v

lemma InVals.reg_self (C : Cfg Id R P) : InVals C (reg C) := Or.inl rfl

lemma InVals.of_write {C : Cfg Id R P} {q : P} {v : Reg Id} (h : (C.loc q).pc = .write v) :
    InVals C v := Or.inr ⟨q, h⟩

lemma invals_of_update {C C' : Cfg Id R P} {p : P} {s' : St Id}
    (hloc : C'.loc = Function.update C.loc p s') {v : Reg Id} (hv : InVals C' v) :
    reg C' = v ∨ (∃ q, q ≠ p ∧ (C.loc q).pc = .write v) ∨ s'.pc = .write v := by
  rcases hv with h | ⟨q, hq⟩
  · exact Or.inl h
  · rw [hloc] at hq
    by_cases hqp : q = p
    · subst hqp; simp only [Function.update_self] at hq; exact Or.inr (Or.inr hq)
    · rw [Function.update_of_ne hqp] at hq; exact Or.inr (Or.inl ⟨q, hqp, hq⟩)

/-! ### Outputs -/

lemma outputs_append_single (α : List (Label P (elecObj R))) (ℓ : Label P (elecObj R)) (q : P) :
    outputs (α ++ [ℓ]) q = (outputs α q).or (ℓ.retOf q) := by
  simp only [outputs, respsOf_append]
  rw [List.head?_append]
  congr 1
  cases h : ℓ.retOf q <;> simp [respsOf, h]

lemma outputs_append_ne_none {α : List (Label P (elecObj R))} (ℓ : Label P (elecObj R)) {q : P}
    (h : outputs α q ≠ none) : outputs (α ++ [ℓ]) q ≠ none := by
  rw [outputs_append_single]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  simp [hr]

lemma outputs_append_tau (α : List (Label P (elecObj R))) (p q : P) :
    outputs (α ++ [.tau p]) q = outputs α q := by
  simp [outputs_append_single]

lemma outputs_append_inv (α : List (Label P (elecObj R))) (p q : P) (o : Unit) :
    outputs (α ++ [.inv p o]) q = outputs α q := by
  simp [outputs_append_single]

/-! ### Counting identifiers -/

section Count

variable [Fintype P] {ids : P → Id}

/-- A set of identifiers of processes other than `L` has at most `n - 1` elements. -/
lemma card_le_of_ids_ne {n : ℕ} (hn : Fintype.card P = n) (D : Finset Id) (L : P)
    (hD : ∀ x ∈ D, ∃ j, ids j = x ∧ j ≠ L) : D.card ≤ n - 1 := by
  have hsub : D ⊆ (Finset.univ.erase L).image ids := by
    intro x hx
    obtain ⟨j, rfl, hj⟩ := hD x hx
    exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩
  calc D.card ≤ ((Finset.univ.erase L).image ids).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.erase L).card := Finset.card_image_le
    _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hn]

/-- A set of `n - 1` identifiers of processes other than `L` contains all of them. -/
lemma mem_of_card_eq {n : ℕ} (hid : Function.Injective ids) (hn : Fintype.card P = n)
    (D : Finset Id) (L : P) (hD : ∀ x ∈ D, ∃ j, ids j = x ∧ j ≠ L) (hc : D.card = n - 1)
    (j : P) (hj : j ≠ L) : ids j ∈ D := by
  have hsub : D ⊆ (Finset.univ.erase L).image ids := by
    intro x hx
    obtain ⟨j, rfl, hj⟩ := hD x hx
    exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩
  have hcard : ((Finset.univ.erase L).image ids).card ≤ D.card := by
    rw [Finset.card_image_of_injective _ hid, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, hn, hc]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [heq]
  exact Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩

/-- If a set of `n - 1` identifiers consists of identifiers of losers and `L` is not a loser,
all processes but `L` are losers. -/
lemma losers_of_card {n : ℕ} (hid : Function.Injective ids) (hn : Fintype.card P = n)
    (D : Finset Id) (lo : P → Bool) (L : P)
    (hD : ∀ x ∈ D, ∃ j, ids j = x ∧ lo j = true) (hL : lo L = false) (hc : D.card = n - 1)
    (j : P) (hj : j ≠ L) : lo j = true := by
  have hD' : ∀ x ∈ D, ∃ j, ids j = x ∧ j ≠ L := by
    intro x hx
    obtain ⟨i, rfl, hi⟩ := hD x hx
    exact ⟨i, rfl, by rintro rfl; simp [hL] at hi⟩
  obtain ⟨j', hj', hl⟩ := hD _ (mem_of_card_eq hid hn D L hD' hc j hj)
  rw [← hid hj']; exact hl

end Count

/-! ### Basic invariant -/

variable (ids : P → Id)

/-- Basic facts about all reachable configurations. -/
structure Basic (α : List (Label P (elecObj R))) (C : Cfg Id R P) : Prop where
  me : ∀ p, (C.loc p).me = ids p
  disc_val : ∀ v, InVals C v → ∀ x ∈ v.disc, ∃ j, ids j = x ∧ (C.loc j).loser = true
  disc_loc : ∀ p, ∀ x ∈ (C.loc p).disc, ∃ j, ids j = x ∧ (C.loc j).loser = true
  wsome : ∀ p w, (C.loc p).pc = .write w → w.id ≠ none →
    w = ⟨some (ids p), (C.loc p).disc, (C.loc p).phase⟩ ∧ (C.loc p).loser = false
  nl : Nonempty P → ∃ c, (C.loc c).loser = false
  regsome : ∀ a, (reg C).id = some a → ∃ c, ids c = a ∧ (C.loc c).loser = false
  idle : ∀ p, (C.loc p).pc = .idle → C.pend p = none
  busy : ∀ p, (C.loc p).pc ≠ .idle → (C.loc p).pc ≠ .fin → C.pend p ≠ none
  fin : ∀ p, (C.loc p).pc = .fin → outputs α p ≠ none

variable {ids} {n : ℕ} {out : Id → Id → R} {π : P → Equiv.Perm (Fin 1)}

lemma basic_init : Basic ids [] ((alg1 Id n out).impl ids π).initCfg := by
  refine ⟨fun p => rfl, ?_, fun p x hx => by simp [Impl.initCfg, SymAlg.impl, alg1] at hx,
    fun p w hw => by simp [Impl.initCfg, SymAlg.impl, alg1] at hw, ?_, ?_, fun p _ => rfl,
    fun p h1 _ => by simp [Impl.initCfg, SymAlg.impl, alg1] at h1,
    fun p h => by simp [Impl.initCfg, SymAlg.impl, alg1] at h⟩
  · intro v hv x hx
    rcases hv with h | ⟨q, hq⟩
    · subst h; simp [reg, Impl.initCfg, SymAlg.impl, alg1, Reg.init] at hx
    · simp [Impl.initCfg, SymAlg.impl, alg1] at hq
  · rintro ⟨c⟩; exact ⟨c, rfl⟩
  · intro a h; simp [reg, Impl.initCfg, SymAlg.impl, alg1, Reg.init] at h


lemma invals_congr {C C' : Cfg Id R P} (hloc : C'.loc = C.loc) (hreg : reg C' = reg C)
    {v : Reg Id} : InVals C' v ↔ InVals C v := by
  simp only [InVals, hloc, hreg]

section StepFacts

variable {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)}

/-- Identifiers never change, losers stay losers and committing processes stay committing. -/
lemma step_loc_mono (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') (j : P) :
    (C'.loc j).me = (C.loc j).me ∧ ((C.loc j).loser = true → (C'.loc j).loser = true) ∧
    ((C.loc j).phase = .committing → (C'.loc j).phase = .committing) := by
  rcases step_cases h with ⟨p, o, rfl, hp, hloc, hpend, hreg⟩ |
    ⟨p, rfl, hp, hpc, hloc, hpend, hreg⟩ | ⟨p, w, rfl, hp, hpc, hloc, hpend, hreg⟩ |
    ⟨p, r, rfl, hp, hpend, hreg, ⟨a, hpc, hr, hloc⟩ | ⟨-, hloc⟩⟩ <;> rw [hloc] <;>
    by_cases hj : j = p
  · subst hj; simp only [Function.update_self]; split_ifs <;> simp
  · simp [Function.update_of_ne hj]
  · subst hj; simp only [Function.update_self]
    exact ⟨afterRead_me _ _ _, afterRead_loser_of _ _ _, afterRead_phase_of _ _ _⟩
  · simp [Function.update_of_ne hj]
  · subst hj; simp
  · simp [Function.update_of_ne hj]
  · subst hj; simp
  · simp [Function.update_of_ne hj]
  · simp
  · simp

end StepFacts

theorem basic_step {α : List (Label P (elecObj R))} {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)}
    (hB : Basic ids α C) (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') :
    Basic ids (α ++ [ℓ]) C' := by
  have hm := step_loc_mono h
  have hlo : ∀ x, (∃ j, ids j = x ∧ (C.loc j).loser = true) →
      ∃ j, ids j = x ∧ (C'.loc j).loser = true :=
    fun x ⟨j, hj, hl⟩ => ⟨j, hj, (hm j).2.1 hl⟩
  have hme : ∀ p, (C'.loc p).me = ids p := fun p => (hm p).1.trans (hB.me p)
  rcases step_cases h with ⟨p, o, rfl, hp, hloc, hpend, hreg⟩ |
    ⟨p, rfl, hp, hpc, hloc, hpend, hreg⟩ | ⟨p, w, rfl, hp, hpc, hloc, hpend, hreg⟩ |
    ⟨p, r, rfl, hp, hpend, hreg, hcase⟩
  · -- invocation
    have hpc0 : (C.loc p).pc = .idle ∨ (C.loc p).pc = .fin := by
      by_contra hc; push Not at hc; exact hB.busy p hc.1 hc.2 hp
    rcases hpc0 with h0 | h0
    · rw [ite_eq_left h0] at hloc
      have hl : ∀ q, C'.loc q = if q = p then { C.loc p with pc := .read } else C.loc q := by
        intro q; rw [hloc, Function.update_apply]
      have hv : ∀ v, InVals C' v → InVals C v := by
        intro v hv
        rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
        · exact Or.inl (hreg ▸ h1)
        · exact InVals.of_write hq
        · simp at h1
      refine ⟨hme, fun v hv' x hx => hlo x (hB.disc_val v (hv v hv') x hx), ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · intro q x hx; rw [hl] at hx; split_ifs at hx
        · subst q; exact hlo x (hB.disc_loc p x hx)
        · exact hlo x (hB.disc_loc q x hx)
      · intro q w hw hwid; by_cases hqp : q = p
        · subst hqp; rw [hl, ite_eq_left rfl] at hw; simp at hw
        · rw [hl, ite_eq_right hqp] at hw ⊢; exact hB.wsome q w hw hwid
      · intro hP; obtain ⟨c, hc⟩ := hB.nl hP; refine ⟨c, ?_⟩; rw [hl]; split_ifs <;> simp_all
      · intro a ha; rw [hreg] at ha; obtain ⟨c, hc1, hc2⟩ := hB.regsome a ha
        refine ⟨c, hc1, ?_⟩; rw [hl]; split_ifs <;> simp_all
      · intro q hq; by_cases hqp : q = p
        · subst hqp; rw [hl, ite_eq_left rfl] at hq; simp at hq
        · rw [hl, ite_eq_right hqp] at hq
          rw [hpend, Function.update_of_ne hqp]; exact hB.idle q hq
      · intro q h1 h2; rw [hpend]; by_cases hqp : q = p
        · subst hqp; simp
        · rw [Function.update_of_ne hqp]; rw [hl, ite_eq_right hqp] at h1 h2; exact hB.busy q h1 h2
      · intro q hq; rw [outputs_append_inv]; by_cases hqp : q = p
        · subst hqp; rw [hl, ite_eq_left rfl] at hq; simp at hq
        · rw [hl, ite_eq_right hqp] at hq; exact hB.fin q hq
    · rw [ite_eq_right (by rw [h0]; simp), Function.update_eq_self] at hloc
      have hv : ∀ v, InVals C' v ↔ InVals C v := fun v => invals_congr hloc hreg
      refine ⟨hme, fun v hv' x hx => hlo x (hB.disc_val v ((hv v).1 hv') x hx), ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro q x hx; rw [hloc] at hx ⊢; exact hB.disc_loc q x hx
      · intro q w hw; rw [hloc] at hw ⊢; exact hB.wsome q w hw
      · rw [hloc]; exact hB.nl
      · rw [hloc, hreg]; exact hB.regsome
      · intro q hq; rw [hloc] at hq; rw [hpend]; by_cases hqp : q = p
        · subst hqp; simp [h0] at hq
        · rw [Function.update_of_ne hqp]; exact hB.idle q hq
      · intro q h1 h2; rw [hpend]; by_cases hqp : q = p
        · subst hqp; simp
        · rw [Function.update_of_ne hqp]; rw [hloc] at h1 h2; exact hB.busy q h1 h2
      · intro q hq; rw [outputs_append_inv]; rw [hloc] at hq; exact hB.fin q hq
  · -- read
    set s := C.loc p with hs
    set r := reg C with hr
    have hv : ∀ v, InVals C' v → InVals C v ∨ (afterRead n s r).pc = .write v := by
      intro v hv
      rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
      · exact Or.inl (Or.inl (hreg.symm.trans h1))
      · exact Or.inl (InVals.of_write hq)
      · exact Or.inr h1
    have hp' : C'.loc p = afterRead n s r := by rw [hloc]; simp
    have hq' : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hdl : ∀ q, ∀ x ∈ (C'.loc q).disc, ∃ j, ids j = x ∧ (C'.loc j).loser = true := by
      intro q x hx
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hx
        rcases afterRead_disc n s r x hx with h1 | h1 | ⟨h1, h2⟩
        · exact hlo x (hB.disc_loc q x h1)
        · exact hlo x (hB.disc_val r (InVals.reg_self C) x h1)
        · exact ⟨q, by rw [h1, hs, hB.me], by rw [hp']; exact h2⟩
      · rw [hq' q hqp] at hx; exact hlo x (hB.disc_loc q x hx)
    have hlp : ∀ c, (C.loc c).loser = false → (C'.loc c).loser = true →
        c = p ∧ ∃ a, r.id = some a ∧ a ≠ ids p := by
      intro c h1 h2
      by_cases hcp : c = p
      · subst hcp; rw [hp'] at h2
        rcases afterRead_loser_new n s r h2 with h3 | ⟨a, ha, hne⟩
        · rw [← hs] at h1; simp [h1] at h3
        · exact ⟨rfl, a, ha, by rw [← hB.me c]; exact hne⟩
      · rw [hq' c hcp] at h2; simp [h1] at h2
    refine ⟨hme, ?_, hdl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv' x hx
      rcases hv v hv' with h1 | h1
      · exact hlo x (hB.disc_val v h1 x hx)
      · rcases afterRead_write n s r h1 with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · simp at hx
        · exact hdl p x (by rw [hp']; exact hx)
        · exact hdl p x (by rw [hp']; exact hx)
    · intro q w hw hwid
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hw ⊢
        rcases afterRead_write n s r hw with rfl | ⟨rfl, h2⟩ | ⟨rfl, -⟩
        · simp at hwid
        · exact ⟨by rw [hs, hB.me], h2⟩
        · simp at hwid
      · rw [hq' q hqp] at hw ⊢; exact hB.wsome q w hw hwid
    · intro hP
      obtain ⟨c, hc⟩ := hB.nl hP
      cases hc' : (C'.loc c).loser
      · exact ⟨c, hc'⟩
      · obtain ⟨rfl, a, ha, hne⟩ := hlp c hc hc'
        obtain ⟨c', rfl, hc'2⟩ := hB.regsome a ha
        have hcc : c' ≠ c := fun h => hne (by rw [h])
        exact ⟨c', by rw [hq' c' hcc]; exact hc'2⟩
    · intro a ha
      rw [hreg] at ha
      obtain ⟨c, rfl, hc⟩ := hB.regsome a ha
      refine ⟨c, rfl, ?_⟩
      cases hc' : (C'.loc c).loser
      · rfl
      · obtain ⟨rfl, a', ha', hne⟩ := hlp c hc hc'
        rw [ha] at ha'; simp at ha'; exact absurd ha'.symm hne
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hq
        rcases afterRead_pc n s r with h1 | ⟨w, h1⟩ | ⟨a, h1⟩ <;> rw [h1] at hq <;> cases hq
      · rw [hq' q hqp] at hq; rw [hpend]; exact hB.idle q hq
    · intro q h1 h2; rw [hpend]
      by_cases hqp : q = p
      · subst hqp; exact hp
      · rw [hq' q hqp] at h1 h2; exact hB.busy q h1 h2
    · intro q hq
      rw [outputs_append_tau]
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hq
        rcases afterRead_pc n s r with h1 | ⟨w, h1⟩ | ⟨a, h1⟩ <;> rw [h1] at hq <;> cases hq
      · rw [hq' q hqp] at hq; exact hB.fin q hq
  · -- write
    have hp' : C'.loc p = { C.loc p with pc := .read } := by rw [hloc]; simp
    have hq' : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hlos : ∀ q, (C'.loc q).loser = (C.loc q).loser := by
      intro q; by_cases hqp : q = p
      · subst hqp; rw [hp']
      · rw [hq' q hqp]
    have hdisc : ∀ q, (C'.loc q).disc = (C.loc q).disc := by
      intro q; by_cases hqp : q = p
      · subst hqp; rw [hp']
      · rw [hq' q hqp]
    have hv : ∀ v, InVals C' v → InVals C v := by
      intro v hv
      rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
      · rw [hreg] at h1; subst h1; exact InVals.of_write hpc
      · exact InVals.of_write hq
      · simp at h1
    refine ⟨hme, fun v hv' x hx => hlo x (hB.disc_val v (hv v hv') x hx), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · intro q x hx; rw [hdisc] at hx; exact hlo x (hB.disc_loc q x hx)
    · intro q w' hw hwid
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hw; simp at hw
      · rw [hq' q hqp] at hw ⊢; exact hB.wsome q w' hw hwid
    · intro hP; obtain ⟨c, hc⟩ := hB.nl hP; exact ⟨c, by rw [hlos]; exact hc⟩
    · intro a ha
      rw [hreg] at ha
      obtain ⟨h1, h2⟩ := hB.wsome p w hpc (by rw [ha]; simp)
      rw [h1] at ha; simp at ha; subst ha
      exact ⟨p, rfl, by rw [hlos]; exact h2⟩
    · intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hq; simp at hq
      · rw [hq' q hqp] at hq; rw [hpend]; exact hB.idle q hq
    · intro q h1 h2; rw [hpend]
      by_cases hqp : q = p
      · subst hqp; exact hp
      · rw [hq' q hqp] at h1 h2; exact hB.busy q h1 h2
    · intro q hq
      rw [outputs_append_tau]
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hq; simp at hq
      · rw [hq' q hqp] at hq; exact hB.fin q hq
  · -- response
    have hret : ∀ q, q ≠ p → outputs (α ++ [.ret p r]) q = outputs α q := by
      intro q hq; rw [outputs_append_single]; simp [Ne.symm hq]
    rcases hcase with ⟨a, hpc, -, hloc⟩ | ⟨hpc, hloc⟩
    · have hp' : C'.loc p = { C.loc p with pc := .fin } := by rw [hloc]; simp
      have hq' : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
        rw [hloc, Function.update_of_ne hq]
      have hlos : ∀ q, (C'.loc q).loser = (C.loc q).loser := by
        intro q; by_cases hqp : q = p
        · subst hqp; rw [hp']
        · rw [hq' q hqp]
      have hdisc : ∀ q, (C'.loc q).disc = (C.loc q).disc := by
        intro q; by_cases hqp : q = p
        · subst hqp; rw [hp']
        · rw [hq' q hqp]
      have hv : ∀ v, InVals C' v → InVals C v := by
        intro v hv
        rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
        · rw [hreg] at h1; exact Or.inl h1
        · exact InVals.of_write hq
        · simp at h1
      refine ⟨hme, fun v hv' x hx => hlo x (hB.disc_val v (hv v hv') x hx), ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · intro q x hx; rw [hdisc] at hx; exact hlo x (hB.disc_loc q x hx)
      · intro q w' hw hwid
        by_cases hqp : q = p
        · subst hqp; rw [hp'] at hw; simp at hw
        · rw [hq' q hqp] at hw ⊢; exact hB.wsome q w' hw hwid
      · intro hP; obtain ⟨c, hc⟩ := hB.nl hP; exact ⟨c, by rw [hlos]; exact hc⟩
      · intro a' ha; rw [hreg] at ha
        obtain ⟨c, h1, h2⟩ := hB.regsome a' ha
        exact ⟨c, h1, by rw [hlos]; exact h2⟩
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [hp'] at hq; simp at hq
        · rw [hq' q hqp] at hq; rw [hpend, Function.update_of_ne hqp]; exact hB.idle q hq
      · intro q h1 h2; rw [hpend]
        by_cases hqp : q = p
        · subst hqp; rw [hp'] at h2; simp at h2
        · rw [Function.update_of_ne hqp]; rw [hq' q hqp] at h1 h2; exact hB.busy q h1 h2
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; rw [outputs_append_single]; simp
        · rw [hret q hqp]; rw [hq' q hqp] at hq; exact hB.fin q hq
    · have hfin : (C.loc p).pc = .fin := by
        rcases hpc with h1 | h1
        · exact absurd (hB.idle p h1) hp
        · exact h1
      have hv : ∀ v, InVals C' v ↔ InVals C v := fun v => invals_congr hloc hreg
      refine ⟨hme, fun v hv' x hx => hlo x (hB.disc_val v ((hv v).1 hv') x hx), ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro q x hx; rw [hloc] at hx ⊢; exact hB.disc_loc q x hx
      · intro q w hw; rw [hloc] at hw ⊢; exact hB.wsome q w hw
      · rw [hloc]; exact hB.nl
      · rw [hloc, hreg]; exact hB.regsome
      · intro q hq; rw [hloc] at hq; rw [hpend]; by_cases hqp : q = p
        · subst hqp; simp
        · rw [Function.update_of_ne hqp]; exact hB.idle q hq
      · intro q h1 h2; rw [hloc] at h1 h2; rw [hpend]; by_cases hqp : q = p
        · subst hqp; exact absurd hfin h2
        · rw [Function.update_of_ne hqp]; exact hB.busy q h1 h2
      · intro q hq; rw [hloc] at hq; exact outputs_append_ne_none _ (hB.fin q hq)


/-! ### Before the leader is determined -/

variable (n out ids)

/-- No value `⟨id, D, ·⟩` with `|D| = n - 1` has been decided yet: everything is electing and
nobody has returned. -/
structure NoLead (α : List (Label P (elecObj R))) (C : Cfg Id R P) : Prop where
  vals : ∀ v, InVals C v → v.phase = .electing ∧ (v.id ≠ none → v.disc.card ≠ n - 1)
  phase : ∀ p, (C.loc p).phase = .electing
  noret : ∀ p a, (C.loc p).pc ≠ .ret a
  nofin : ∀ p, (C.loc p).pc ≠ .fin
  noout : ∀ p, outputs α p = none

/-- While the leader `L` is electing. -/
structure ElPart (C : Cfg Id R P) (L : P) : Prop where
  disc : (C.loc L).disc.card = n - 1
  some_val : ∀ v, InVals C v → v.id ≠ none → v.phase = .electing ∧ v.disc.card = n - 1
  co_val : ∀ v, InVals C v → v.phase = .committing → v.id = none ∧ v.disc = ∅
  noret : ∀ p a, (C.loc p).pc ≠ .ret a
  nofin : ∀ p, (C.loc p).pc ≠ .fin

/-- Once the leader `L` is committing: its `discarded` set `D` only grows; the values with an
identifier are committing with a `discarded` set included in `D`; the processes of `D` are
*quiet* (committing, no pending write, contained in all values with an identifier); a committing
`⊥`-value only contains identifiers of `D` and of its quiet writer; once somebody returns, `REG`
holds an identifier and `|D| = n - 1`. -/
structure CoPart (C : Cfg Id R P) (L : P) : Prop where
  some_val : ∀ v, InVals C v → v.id ≠ none →
    v.phase = .committing ∧ v.disc ⊆ (C.loc L).disc
  reg_bot : (reg C).id = none → (reg C).phase = .committing → ∀ j, ids j ∈ (reg C).disc →
    ids j ∈ (C.loc L).disc ∨ ((∀ w, (C.loc j).pc ≠ .write w) ∧ (C.loc j).phase = .committing)
  pend_bot : ∀ k Y, (C.loc k).pc = .write ⟨none, Y, .committing⟩ → ∀ j, ids j ∈ Y →
    ids j ∈ (C.loc L).disc ∨ (j = k ∧ (C.loc k).phase = .committing)
  quiet : ∀ j, ids j ∈ (C.loc L).disc → (C.loc j).phase = .committing ∧
    (∀ w, (C.loc j).pc ≠ .write w) ∧ ∀ v, InVals C v → v.id ≠ none → ids j ∈ v.disc
  done : (∃ q, (∃ a, (C.loc q).pc = .ret a) ∨ (C.loc q).pc = .fin) →
    (reg C).id ≠ none ∧ (C.loc L).disc.card = n - 1
  lw : ∀ w, (C.loc L).pc = .write w → w.id ≠ none

/-- `L` is the leader: all other processes are losers, all identifiers in values are `id_L`,
and all responses are computed from `id_L`. -/
structure Lead (α : List (Label P (elecObj R))) (C : Cfg Id R P) (L : P) : Prop where
  loser : ∀ j, (C.loc j).loser = true ↔ j ≠ L
  ids_val : ∀ v a, InVals C v → v.id = some a → a = ids L
  ret : ∀ p a, (C.loc p).pc = .ret a → a = ids L
  out : ∀ p r, outputs α p = some r → r = out (ids p) (ids L)
  el : (C.loc L).phase = .electing → ElPart n C L
  co : (C.loc L).phase = .committing → CoPart ids n C L

variable {n out ids}

/-- Frame lemma: steps that only change program counters from `idle` to `read` or from `ret a` to
`fin` preserve `Lead`. -/
lemma lead_of_pc_change {α α' : List (Label P (elecObj R))} {C C' : Cfg Id R P} {L : P}
    (hL : Lead ids n out α C L) (hreg : reg C' = reg C)
    (hdisc : ∀ q, (C'.loc q).disc = (C.loc q).disc)
    (hphase : ∀ q, (C'.loc q).phase = (C.loc q).phase)
    (hlos : ∀ q, (C'.loc q).loser = (C.loc q).loser)
    (hw : ∀ q w, (C'.loc q).pc = .write w → (C.loc q).pc = .write w)
    (hr : ∀ q a, (C'.loc q).pc = .ret a → (C.loc q).pc = .ret a)
    (hf : ∀ q, (C'.loc q).pc = .fin → (C.loc q).pc = .fin ∨ ∃ a, (C.loc q).pc = .ret a)
    (hout : ∀ p r, outputs α' p = some r → r = out (ids p) (ids L)) :
    Lead ids n out α' C' L := by
  have hv : ∀ v, InVals C' v → InVals C v := by
    rintro v (h | ⟨q, hq⟩)
    · exact Or.inl (hreg ▸ h)
    · exact InVals.of_write (hw q v hq)
  have hdone : (∃ q, (∃ a, (C'.loc q).pc = .ret a) ∨ (C'.loc q).pc = .fin) →
      ∃ q, (∃ a, (C.loc q).pc = .ret a) ∨ (C.loc q).pc = .fin := by
    rintro ⟨q, ⟨a, ha⟩ | hq⟩
    · exact ⟨q, Or.inl ⟨a, hr q a ha⟩⟩
    · rcases hf q hq with h1 | h1
      · exact ⟨q, Or.inr h1⟩
      · exact ⟨q, Or.inl h1⟩
  refine ⟨fun j => by rw [hlos]; exact hL.loser j, fun v a h1 h2 => hL.ids_val v a (hv v h1) h2,
    fun p a h => hL.ret p a (hr p a h), hout, ?_, ?_⟩
  · intro hph
    rw [hphase] at hph
    have E := hL.el hph
    refine ⟨by rw [hdisc]; exact E.disc, fun v h1 h2 => E.some_val v (hv v h1) h2,
      fun v h1 h2 => E.co_val v (hv v h1) h2, fun p a h => E.noret p a (hr p a h), ?_⟩
    intro p h
    rcases hf p h with h1 | ⟨a, h1⟩
    · exact E.nofin p h1
    · exact E.noret p a h1
  · intro hph
    rw [hphase] at hph
    have E := hL.co hph
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v h1 h2; rw [hdisc]; exact E.some_val v (hv v h1) h2
    · intro h1 h2 j hj; rw [hreg] at h1 h2 hj; rw [hdisc, hphase]
      rcases E.reg_bot h1 h2 j hj with h3 | ⟨h3, h4⟩
      · exact Or.inl h3
      · exact Or.inr ⟨fun w h => h3 w (hw j w h), h4⟩
    · intro k Y hk j hj; rw [hdisc, hphase]; exact E.pend_bot k Y (hw k _ hk) j hj
    · intro j hj; rw [hdisc] at hj
      obtain ⟨h1, h2, h3⟩ := E.quiet j hj
      exact ⟨by rw [hphase]; exact h1, fun w h => h2 w (hw j w h),
        fun v hv' hv'' => h3 v (hv v hv') hv''⟩
    · intro h; rw [hreg, hdisc]; exact E.done (hdone h)
    · intro w h; exact E.lw w (hw L w h)


/-- Frame lemma for `CoPart`. -/
lemma coPart_frame {C C' : Cfg Id R P} {L : P} (E : CoPart ids n C L) (hreg : reg C' = reg C)
    (hdiscL : (C'.loc L).disc = (C.loc L).disc)
    (hphase : ∀ q, (C.loc q).phase = .committing → (C'.loc q).phase = .committing)
    (hw : ∀ q w, (C'.loc q).pc = .write w → (C.loc q).pc = .write w)
    (hdone : (∃ q, (∃ a, (C'.loc q).pc = .ret a) ∨ (C'.loc q).pc = .fin) →
      (reg C').id ≠ none ∧ (C'.loc L).disc.card = n - 1) : CoPart ids n C' L := by
  have hv : ∀ v, InVals C' v → InVals C v := by
    rintro v (h | ⟨q, hq⟩)
    · exact Or.inl (hreg ▸ h)
    · exact InVals.of_write (hw q v hq)
  refine ⟨?_, ?_, ?_, ?_, hdone, fun w h => E.lw w (hw L w h)⟩
  · intro v h1 h2; rw [hdiscL]; exact E.some_val v (hv v h1) h2
  · intro h1 h2 j hj; rw [hreg] at h1 h2 hj; rw [hdiscL]
    rcases E.reg_bot h1 h2 j hj with h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨fun w h => h3 w (hw j w h), hphase j h4⟩
  · intro k Y hk j hj; rw [hdiscL]
    rcases E.pend_bot k Y (hw k _ hk) j hj with h3 | ⟨h3, h4⟩
    · exact Or.inl h3
    · exact Or.inr ⟨h3, hphase k h4⟩
  · intro j hj; rw [hdiscL] at hj
    obtain ⟨h1, h2, h3⟩ := E.quiet j hj
    exact ⟨hphase j h1, fun w h => h2 w (hw j w h), fun v hv' hv'' => h3 v (hv v hv') hv''⟩

/-- In `Lead L`, the leader's `discarded` set has at most `n - 1` elements. -/
lemma Lead.card_le [Fintype P] (hn : Fintype.card P = n) {α : List (Label P (elecObj R))}
    {C : Cfg Id R P} {L : P} (hL : Lead ids n out α C L) (D : Finset Id)
    (hD : ∀ x ∈ D, ∃ j, ids j = x ∧ (C.loc j).loser = true) : D.card ≤ n - 1 :=
  card_le_of_ids_ne hn D L (fun x hx => by
    obtain ⟨j, h1, h2⟩ := hD x hx; exact ⟨j, h1, (hL.loser j).1 h2⟩)

/-- In `Lead L`, a set of `n - 1` identifiers of losers contains all processes but `L`. -/
lemma Lead.mem_of_card [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C : Cfg Id R P} {L : P} (hL : Lead ids n out α C L)
    (D : Finset Id) (hD : ∀ x ∈ D, ∃ j, ids j = x ∧ (C.loc j).loser = true)
    (hc : D.card = n - 1) (j : P) (hj : j ≠ L) : ids j ∈ D :=
  mem_of_card_eq hid hn D L (fun x hx => by
    obtain ⟨i, h1, h2⟩ := hD x hx; exact ⟨i, h1, (hL.loser i).1 h2⟩) hc j hj

lemma Lead.not_mem_disc {α : List (Label P (elecObj R))} {C : Cfg Id R P} {L : P}
    (hB : Basic ids α C) (hL : Lead ids n out α C L) (hid : Function.Injective ids) (q : P) :
    ids L ∉ (C.loc q).disc := by
  intro h
  obtain ⟨j, hj, hl⟩ := hB.disc_loc q _ h
  rw [hid hj] at hl
  exact (hL.loser L).1 hl rfl

theorem lead_step_read [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C C' : Cfg Id R P} {p L : P}
    (hB : Basic ids α C) (hB' : Basic ids (α ++ [.tau p]) C') (hL : Lead ids n out α C L)
    (hloc : C'.loc = Function.update C.loc p (afterRead n (C.loc p) (reg C)))
    (hreg : reg C' = reg C) (hpc : (C.loc p).pc = .read) :
    Lead ids n out (α ++ [.tau p]) C' L := by
  have hp' : C'.loc p = afterRead n (C.loc p) (reg C) := by rw [hloc]; simp
  have hq' : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
    rw [hloc, Function.update_of_ne hq]
  have hv : ∀ v, InVals C' v → InVals C v ∨ (afterRead n (C.loc p) (reg C)).pc = .write v := by
    intro v hv
    rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
    · exact Or.inl (Or.inl (hreg ▸ h1))
    · exact Or.inl (InVals.of_write hq)
    · exact Or.inr h1
  have hsme : (C.loc p).me = ids p := hB.me p
  have hrv : InVals C (reg C) := InVals.reg_self C
  have hout : ∀ q r, outputs (α ++ [.tau p]) q = some r → r = out (ids q) (ids L) := by
    intro q r h; rw [outputs_append_tau] at h; exact hL.out q r h
  -- losers
  have hlos : ∀ j, (C'.loc j).loser = true ↔ j ≠ L := by
    intro j
    by_cases hjp : j = p
    · rw [hjp, hp']
      by_cases hpL : p = L
      · subst hpL
        have h0 : (C.loc p).loser = false := by
          have := hL.loser p; cases h : (C.loc p).loser <;> simp_all
        simp only [ne_eq, not_true_eq_false, iff_false, Bool.not_eq_true]
        cases h1 : (afterRead n (C.loc p) (reg C)).loser
        · rfl
        · rcases afterRead_loser_new n (C.loc p) (reg C) h1 with h2 | ⟨a, ha, hne⟩
          · simp [h0] at h2
          · exact absurd (by rw [hsme]; exact hL.ids_val _ a hrv ha) hne
      · have h0 : (C.loc p).loser = true := (hL.loser p).2 hpL
        simp [afterRead_loser_of n (C.loc p) (reg C) h0, hpL]
    · rw [hq' j hjp]; exact hL.loser j
  have hpL_of : (afterRead n (C.loc p) (reg C)).loser = false → p = L := by
    intro h; by_contra hne; have := (hlos p).2 hne; rw [hp', h] at this; simp at this
  have hids : ∀ v a, InVals C' v → v.id = some a → a = ids L := by
    intro v a hv' ha
    rcases hv v hv' with h1 | h1
    · exact hL.ids_val v a h1 ha
    · rcases afterRead_write n (C.loc p) (reg C) h1 with rfl | ⟨rfl, h2⟩ | ⟨rfl, -⟩
      · simp at ha
      · simp only [Option.some.injEq] at ha; rw [← ha, hsme, hpL_of h2]
      · simp at ha
  have hret : ∀ q a, (C'.loc q).pc = .ret a → a = ids L := by
    intro q a h
    by_cases hqp : q = p
    · rw [hqp, hp'] at h
      exact hL.ids_val _ a hrv (afterRead_ret n _ _ h).1
    · rw [hq' q hqp] at h; exact hL.ret q a h
  have hphL : (C.loc L).phase = .committing → (C'.loc L).phase = .committing := by
    intro h
    by_cases hLp : L = p
    · rw [hLp] at h ⊢; rw [hp']; exact afterRead_phase_of n _ _ h
    · rw [hq' L hLp]; exact h
  have hdiscB : ∀ D : Finset Id, (∀ x ∈ D, ∃ j, ids j = x ∧ (C'.loc j).loser = true) →
      D.card ≤ n - 1 := fun D hD => card_le_of_ids_ne hn D L (fun x hx => by
        obtain ⟨j, h1, h2⟩ := hD x hx; exact ⟨j, h1, (hlos j).1 h2⟩)
  -- generic parts of `ElPart`
  have hel : (C'.loc L).phase = .electing → (C.loc L).phase = .electing ∧
      (C'.loc L).disc.card = n - 1 ∧
      (∀ v, InVals C' v → v.id ≠ none → v.phase = .electing ∧ v.disc.card = n - 1) ∧
      (∀ q a, (C'.loc q).pc ≠ .ret a) ∧ (∀ q, (C'.loc q).pc ≠ .fin) := by
    intro hE'
    have hE : (C.loc L).phase = .electing := by
      cases h : (C.loc L).phase
      · rfl
      · have := hphL h; rw [hE'] at this; cases this
    have E := hL.el hE
    have hdL : (C'.loc L).disc.card = n - 1 := by
      by_cases hLp : L = p
      · subst hLp
        have hlL' : (afterRead n (C.loc L) (reg C)).loser = false := by
          have := hlos L; rw [hp'] at this; simpa using this
        have hph : (afterRead n (C.loc L) (reg C)).phase = (C.loc L).phase := by
          rw [← hp', hE', hE]
        have hsub := afterRead_disc_mono n (C.loc L) (reg C) hlL' hph
        have h1 := E.disc
        have h2 := hdiscB _ (hB'.disc_loc L)
        rw [hp'] at h2 ⊢
        have := Finset.card_le_card hsub
        omega
      · rw [hq' L hLp]; exact E.disc
    refine ⟨hE, hdL, ?_, ?_, ?_⟩
    · intro v hv' hid'
      rcases hv v hv' with h1 | h1
      · exact E.some_val v h1 hid'
      · rcases afterRead_write n (C.loc p) (reg C) h1 with rfl | ⟨rfl, h2⟩ | ⟨rfl, -⟩
        · simp at hid'
        · have := hpL_of h2; subst this
          rw [← hp']; exact ⟨hE', hdL⟩
        · simp at hid'
    · intro q a h
      by_cases hqp : q = p
      · rw [hqp, hp'] at h
        have := afterRead_ret n _ _ h
        have h2 := (E.some_val _ hrv (by rw [this.1]; simp)).1
        rw [this.2.2] at h2; cases h2
      · rw [hq' q hqp] at h; exact E.noret q a h
    · intro q h
      by_cases hqp : q = p
      · rw [hqp, hp'] at h
        rcases afterRead_pc n (C.loc p) (reg C) with h1 | ⟨w, h1⟩ | ⟨a, h1⟩ <;> rw [h1] at h <;>
          cases h
      · rw [hq' q hqp] at h; exact E.nofin q h
  refine ⟨hlos, hids, hret, hout, ?_, ?_⟩
  · -- `ElPart`
    intro hE'
    obtain ⟨hE, h1, h2, h3, h4⟩ := hel hE'
    have E := hL.el hE
    refine ⟨h1, h2, ?_, h3, h4⟩
    intro v hv' hph
    rcases hv v hv' with h5 | h5
    · exact E.co_val v h5 hph
    rcases afterRead_cases n (C.loc p) (reg C) with ⟨hA1, hA2, hs'⟩ |
      ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, hid0, hlo0, hs'⟩ |
      ⟨hnA, a, ha, hc, hne, hni, hs'⟩ | ⟨hs', hnA, hE1, hE2⟩ <;> rw [hs'] at h5 <;>
      simp only [PC.write.injEq, reduceCtorEq] at h5
    · subst h5; simp
    · subst h5
      have hpL := hpL_of (by rw [hs']; exact hlo0)
      subst hpL
      simp only at hph; rw [hph] at hE; cases hE
    · exfalso
      have haL := hL.ids_val _ a hrv ha
      have hpL : p ≠ L := by rintro rfl; exact hne (by rw [haL, hsme])
      have hcard := (E.some_val _ hrv (by rw [ha]; simp)).2
      exact hc hcard
  · -- `CoPart`
    intro hC'
    rcases afterRead_cases n (C.loc p) (reg C) with ⟨hA1, hA2, hs'⟩ |
      ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, hid0, hlo0, hs'⟩ |
      ⟨hnA, a, ha, hc, hne, hni, hs'⟩ | ⟨hs', hnA, hE1, hE2⟩
    · -- line 4
      by_cases hpL : p = L
      · -- the leader enters the committing phase
        subst hpL
        have E := hL.el hA2
        obtain ⟨hr0, hr1⟩ := E.co_val _ hrv hA1
        have hp'' : C'.loc p = { C.loc p with pc := .read, phase := .committing, disc := ∅ } := by
          rw [hp', hs']
        have hv2 : ∀ v, InVals C' v → InVals C v := by
          intro v hv'
          rcases hv v hv' with h1 | h1
          · exact h1
          · rw [hs'] at h1; cases h1
        have hnov : ∀ v, InVals C v → v.id ≠ none → False := by
          rintro v (h1 | ⟨q, hq⟩) h2
          · rw [← h1, hr0] at h2; exact h2 rfl
          · have h6 := (hB.wsome q v hq h2).2
            have hq2 : q = p := by
              by_contra hne; have h7 := (hL.loser q).2 hne; rw [h6] at h7; cases h7
            subst hq2; rw [hpc] at hq; cases hq
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro v hv' hid'; exact (hnov v (hv2 v hv') hid').elim
        · intro _ _ j hj; rw [hreg, hr1] at hj; simp at hj
        · intro k Y hk j hj
          have hkp : k ≠ p := by rintro rfl; rw [hp''] at hk; cases hk
          rw [hq' k hkp] at hk
          have h6 := (E.co_val _ (InVals.of_write hk) rfl).2
          simp only at h6; rw [h6] at hj; simp at hj
        · intro j hj; rw [hp''] at hj; simp at hj
        · rintro ⟨q, ⟨a, ha⟩ | hq⟩
          · by_cases hqp : q = p
            · rw [hqp, hp''] at ha; cases ha
            · rw [hq' q hqp] at ha; exact (E.noret q a ha).elim
          · by_cases hqp : q = p
            · rw [hqp, hp''] at hq; cases hq
            · rw [hq' q hqp] at hq; exact (E.nofin q hq).elim
        · intro w hw; rw [hp''] at hw; cases hw
      · have hC : (C.loc L).phase = .committing := by rw [← hq' L (Ne.symm hpL)]; exact hC'
        have E := hL.co hC
        refine coPart_frame E hreg (by rw [hq' L (Ne.symm hpL)]) ?_ ?_ ?_
        · intro q hq; by_cases hqp : q = p
          · rw [hqp, hp', hs']
          · rw [hq' q hqp]; exact hq
        · intro q w hw; by_cases hqp : q = p
          · rw [hqp, hp', hs'] at hw; cases hw
          · rw [hq' q hqp] at hw; exact hw
        · rintro ⟨q, hq⟩
          rw [hreg, hq' L (Ne.symm hpL)]
          apply E.done
          refine ⟨q, ?_⟩
          by_cases hqp : q = p
          · rw [hqp, hp', hs'] at hq; simp at hq
          · rw [hq' q hqp] at hq; exact hq
    · -- line 7: decide to return
      have hC : (C.loc L).phase = .committing := by
        by_cases hLp : L = p
        · rw [hLp, hp', hs'] at hC'; rw [hLp]; exact hC'
        · rw [← hq' L hLp]; exact hC'
      have E := hL.co hC
      have hdL : (C'.loc L).disc = (C.loc L).disc := by
        by_cases hLp : L = p
        · rw [hLp, hp', hs']
        · rw [hq' L hLp]
      refine coPart_frame E hreg hdL ?_ ?_ ?_
      · intro q hq; by_cases hqp : q = p
        · rw [hqp, hp', hs']; rw [hqp] at hq; exact hq
        · rw [hq' q hqp]; exact hq
      · intro q w hw; by_cases hqp : q = p
        · rw [hqp, hp', hs'] at hw; cases hw
        · rw [hq' q hqp] at hw; exact hw
      · intro _
        refine ⟨by rw [hreg, ha]; simp, ?_⟩
        have hsub := (E.some_val _ hrv (by rw [ha]; simp)).2
        have h1 := Finset.card_le_card hsub
        have h2 := hdiscB _ (hB'.disc_loc L)
        rw [hdL] at h2 ⊢
        omega
    · -- line 8
      exfalso
      have hC : (C.loc L).phase = .committing := by
        by_cases hLp : L = p
        · rw [hLp, hp', hs'] at hC'; rw [hLp]; exact hC'
        · rw [← hq' L hLp]; exact hC'
      have := (( hL.co hC).some_val _ hrv (by rw [ha]; simp)).1
      rw [hph'] at this; cases this
    · -- line 14 (the leader writes its value)
      have hpL := hpL_of (by rw [hs']; exact hlo0)
      subst L
      have hC : (C.loc p).phase = .committing := by rw [hp', hs'] at hC'; exact hC'
      have E := hL.co hC
      set d := if (reg C).phase = (C.loc p).phase then (C.loc p).disc ∪ (reg C).disc
        else (C.loc p).disc with hd
      have hp'' : C'.loc p =
          { C.loc p with pc := .write ⟨some (C.loc p).me, d, (C.loc p).phase⟩, disc := d } := by
        rw [hp', hs']
      have hDd : (C.loc p).disc ⊆ d := by
        rw [hd]; split_ifs
        · exact Finset.subset_union_left
        · exact Finset.Subset.refl _
      have hv2 : ∀ v, InVals C' v → InVals C v ∨
          v = ⟨some (C.loc p).me, d, (C.loc p).phase⟩ := by
        intro v hv'
        rcases hv v hv' with h1 | h1
        · exact Or.inl h1
        · rw [hs'] at h1; simp only [PC.write.injEq] at h1; exact Or.inr h1.symm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv' hid'
        rcases hv2 v hv' with h1 | rfl
        · obtain ⟨h2, h3⟩ := E.some_val v h1 hid'
          exact ⟨h2, by rw [hp'']; exact h3.trans hDd⟩
        · rw [hp'']; exact ⟨hC, Finset.Subset.refl _⟩
      · intro _ h2 j hj
        rw [hreg] at h2 hj
        left; rw [hp'']; dsimp only
        rw [hd, ite_eq_left (by rw [h2, hC])]
        exact Finset.mem_union_right _ hj
      · intro k Y hk j hj
        have hkp : k ≠ p := by rintro rfl; rw [hp''] at hk; cases hk
        rw [hq' k hkp] at hk ⊢
        rcases E.pend_bot k Y hk j hj with h1 | h1
        · left; rw [hp'']; exact hDd h1
        · exact Or.inr h1
      · intro j hj
        rw [hp''] at hj
        have hjp : j ≠ p := by
          intro h; rw [h] at hj
          obtain ⟨i, hi, hl⟩ := hB'.disc_loc p _ (by rw [hp'']; exact hj)
          rw [hid hi] at hl; exact (hlos p).1 hl rfl
        rw [hq' j hjp]
        have hvals : ∀ v, InVals C' v → v.id ≠ none → v.disc ⊆ d →
            (∀ v, InVals C v → v.id ≠ none → ids j ∈ v.disc) → ids j ∈ v.disc := by
          intro v hv' hid' _ hall
          rcases hv2 v hv' with h1 | rfl
          · exact hall v h1 hid'
          · exact hj
        by_cases hjD : ids j ∈ (C.loc p).disc
        · obtain ⟨h1, h2, h3⟩ := E.quiet j hjD
          exact ⟨h1, h2, fun v hv' hid' => hvals v hv' hid' (by
            rcases hv2 v hv' with h4 | rfl
            · exact ((E.some_val v h4 hid').2).trans hDd
            · exact Finset.Subset.refl _) h3⟩
        · have hrd : (reg C).phase = (C.loc p).phase ∧ ids j ∈ (reg C).disc := by
            rw [hd] at hj; split_ifs at hj with h1
            · rcases Finset.mem_union.1 hj with h2 | h2
              · exact absurd h2 hjD
              · exact ⟨h1, h2⟩
            · exact absurd hj hjD
          rcases E.reg_bot hid0 (by rw [hrd.1, hC]) j hrd.2 with h1 | ⟨h1, h2⟩
          · exact absurd h1 hjD
          · refine ⟨h2, h1, fun v hv' hid' => ?_⟩
            rcases hv2 v hv' with h4 | rfl
            · exfalso
              rcases h4 with h5 | ⟨q, hq⟩
              · rw [← h5, hid0] at hid'; exact hid' rfl
              · have h6 := (hB.wsome q v hq hid').2
                have hq2 : q = p := by
                  by_contra hne; have h7 := (hL.loser q).2 hne; rw [h6] at h7; cases h7
                subst hq2; rw [hpc] at hq; cases hq
            · exact hj
      · rintro ⟨q, hq⟩
        exfalso
        have := (E.done ⟨q, by
          by_cases hqp : q = p
          · rw [hqp, hp''] at hq; simp at hq
          · rw [hq' q hqp] at hq; exact hq⟩).1
        exact this hid0
      · intro w hw; rw [hp''] at hw; simp only [PC.write.injEq] at hw; subst hw; simp
    · -- line 17: a loser writes `⊥`
      have haL := hL.ids_val _ a hrv ha
      have hpL : p ≠ L := by rintro rfl; exact hne (by rw [haL, hsme])
      have hC : (C.loc L).phase = .committing := by rw [← hq' L (Ne.symm hpL)]; exact hC'
      have E := hL.co hC
      obtain ⟨hrph, hrsub⟩ := E.some_val _ hrv (by rw [ha]; simp)
      have hsph : (C.loc p).phase = .committing := by
        cases h : (C.loc p).phase
        · exact absurd ⟨hrph, h⟩ hnA
        · rfl
      have hp'' : C'.loc p =
          { C.loc p with pc := .write ⟨none, insert (C.loc p).me (reg C).disc, (C.loc p).phase⟩,
                         loser := true, disc := insert (C.loc p).me (reg C).disc } := by
        rw [hp', hs']
      have hdL : (C'.loc L).disc = (C.loc L).disc := by rw [hq' L (Ne.symm hpL)]
      have hv2 : ∀ v, InVals C' v → v.id ≠ none → InVals C v := by
        intro v hv' hid'
        rcases hv v hv' with h1 | h1
        · exact h1
        · rw [hs'] at h1; simp only [PC.write.injEq] at h1; subst h1; simp at hid'
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v hv' hid'; rw [hdL]; exact E.some_val v (hv2 v hv' hid') hid'
      · intro h1; rw [hreg, ha] at h1; simp at h1
      · intro k Y hk j hj
        rw [hdL]
        by_cases hkp : k = p
        · rw [hkp, hp''] at hk ⊢
          simp only [PC.write.injEq, Reg.mk.injEq] at hk
          obtain ⟨-, rfl, -⟩ := hk
          rcases Finset.mem_insert.1 hj with h1 | h1
          · right; rw [hsme] at h1; exact ⟨hid h1, hsph⟩
          · left; exact hrsub h1
        · rw [hq' k hkp] at hk ⊢; exact E.pend_bot k Y hk j hj
      · intro j hj
        rw [hdL] at hj
        obtain ⟨h1, h2, h3⟩ := E.quiet j hj
        have hjp : j ≠ p := by
          rintro rfl
          exact hni (by rw [hsme]; exact h3 _ hrv (by rw [ha]; simp))
        rw [hq' j hjp]
        exact ⟨h1, h2, fun v hv' hid' => h3 v (hv2 v hv' hid') hid'⟩
      · rintro ⟨q, hq⟩
        rw [hreg, hdL]
        apply E.done
        refine ⟨q, ?_⟩
        by_cases hqp : q = p
        · rw [hqp, hp''] at hq; simp at hq
        · rw [hq' q hqp] at hq; exact hq
      · intro w hw; rw [hq' L (Ne.symm hpL)] at hw; exact E.lw w hw
    · -- nothing happens
      have hC : (C.loc L).phase = .committing := by
        by_cases hLp : L = p
        · rw [hLp, hp', hs'] at hC'; rw [hLp]; exact hC'
        · rw [← hq' L hLp]; exact hC'
      have hloc' : C'.loc = C.loc := by
        rw [hloc, hs']
        have : ({ C.loc p with pc := .read } : St Id) = C.loc p := by
          cases h : C.loc p; simp only [h] at hpc; simp [hpc]
        rw [this, Function.update_eq_self]
      refine coPart_frame (hL.co hC) hreg (by rw [hloc']) (fun q h => by rw [hloc']; exact h)
        (fun q w h => by rwa [hloc'] at h) ?_
      intro h; rw [hloc', hreg]; apply (hL.co hC).done; simpa [hloc'] using h


/-- Steps that only change the program counter of `p` to `x`. -/
lemma pc_only {C C' : Cfg Id R P} {p : P} {x : PC Id}
    (hloc : C'.loc = Function.update C.loc p { C.loc p with pc := x }) (q : P) :
    (C'.loc q).disc = (C.loc q).disc ∧ (C'.loc q).phase = (C.loc q).phase ∧
    (C'.loc q).loser = (C.loc q).loser ∧ (C'.loc q).me = (C.loc q).me ∧
    (C'.loc q).pc = if q = p then x else (C.loc q).pc := by
  rw [hloc]
  by_cases hqp : q = p
  · subst hqp; simp
  · simp [hqp]

theorem lead_step [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)} {L : P}
    (hB : Basic ids α C) (hB' : Basic ids (α ++ [ℓ]) C') (hL : Lead ids n out α C L)
    (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') : Lead ids n out (α ++ [ℓ]) C' L := by
  rcases step_cases h with ⟨p, o, rfl, hp, hloc, hpend, hreg⟩ |
    ⟨p, rfl, hp, hpc, hloc, hpend, hreg⟩ | ⟨p, w, rfl, hp, hpc, hloc, hpend, hreg⟩ |
    ⟨p, r, rfl, hp, hpend, hreg, hcase⟩
  · -- invocation
    have hout : ∀ q r, outputs (α ++ [.inv p o]) q = some r → r = out (ids q) (ids L) := by
      intro q r h; rw [outputs_append_inv] at h; exact hL.out q r h
    by_cases h0 : (C.loc p).pc = .idle
    · rw [ite_eq_left h0] at hloc
      have hf := pc_only hloc
      refine lead_of_pc_change hL hreg (fun q => (hf q).1) (fun q => (hf q).2.1)
        (fun q => (hf q).2.2.1) ?_ ?_ ?_ hout
      · intro q w hw; rw [(hf q).2.2.2.2] at hw; split_ifs at hw; exact hw
      · intro q a hw; rw [(hf q).2.2.2.2] at hw; split_ifs at hw; exact hw
      · intro q hw; rw [(hf q).2.2.2.2] at hw; split_ifs at hw; exact Or.inl hw
    · rw [ite_eq_right h0, Function.update_eq_self] at hloc
      exact lead_of_pc_change hL hreg (fun q => by rw [hloc]) (fun q => by rw [hloc])
        (fun q => by rw [hloc]) (fun q w h => by rwa [hloc] at h) (fun q a h => by rwa [hloc] at h)
        (fun q h => Or.inl (by rwa [hloc] at h)) hout
  · exact lead_step_read hid hn hB hB' hL hloc hreg hpc
  · -- write
    have hf := pc_only hloc
    have hpcq : ∀ q, (C'.loc q).pc = if q = p then .read else (C.loc q).pc := fun q => (hf q).2.2.2.2
    have hw' : ∀ q w', (C'.loc q).pc = .write w' → (C.loc q).pc = .write w' := by
      intro q w' h; rw [hpcq] at h; split_ifs at h; exact h
    have hv : ∀ v, InVals C' v → InVals C v := by
      rintro v (h1 | ⟨q, hq⟩)
      · rw [hreg] at h1; subst h1; exact InVals.of_write hpc
      · exact InVals.of_write (hw' q v hq)
    have hr' : ∀ q a, (C'.loc q).pc = .ret a → (C.loc q).pc = .ret a := by
      intro q a h; rw [hpcq] at h; split_ifs at h; exact h
    have hfin : ∀ q, (C'.loc q).pc = .fin → (C.loc q).pc = .fin := by
      intro q h; rw [hpcq] at h; split_ifs at h; exact h
    have hdone : (∃ q, (∃ a, (C'.loc q).pc = .ret a) ∨ (C'.loc q).pc = .fin) →
        ∃ q, (∃ a, (C.loc q).pc = .ret a) ∨ (C.loc q).pc = .fin := by
      rintro ⟨q, ⟨a, ha⟩ | hq⟩
      · exact ⟨q, Or.inl ⟨a, hr' q a ha⟩⟩
      · exact ⟨q, Or.inr (hfin q hq)⟩
    refine ⟨fun j => by rw [(hf j).2.2.1]; exact hL.loser j,
      fun v a h1 h2 => hL.ids_val v a (hv v h1) h2, fun q a h => hL.ret q a (hr' q a h),
      fun q r h => hL.out q r (by rwa [outputs_append_tau] at h), ?_, ?_⟩
    · intro hph
      rw [(hf L).2.1] at hph
      have E := hL.el hph
      exact ⟨by rw [(hf L).1]; exact E.disc, fun v h1 h2 => E.some_val v (hv v h1) h2,
        fun v h1 h2 => E.co_val v (hv v h1) h2, fun q a h => E.noret q a (hr' q a h),
        fun q h => E.nofin q (hfin q h)⟩
    · intro hph
      rw [(hf L).2.1] at hph
      have E := hL.co hph
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v h1 h2; rw [(hf L).1]; exact E.some_val v (hv v h1) h2
      · intro h1 h2 j hj
        rw [hreg] at h1 h2 hj
        rw [(hf L).1, (hf j).2.1]
        have hw2 : (C.loc p).pc = .write ⟨none, w.disc, .committing⟩ := by
          rw [hpc]; cases w; simp only at h1 h2; rw [h1, h2]
        rcases E.pend_bot p w.disc hw2 j hj with h3 | ⟨rfl, h4⟩
        · exact Or.inl h3
        · refine Or.inr ⟨fun w' h5 => ?_, h4⟩
          rw [hpcq, ite_eq_left rfl] at h5; cases h5
      · intro k Y hk j hj
        rw [(hf L).1, (hf k).2.1]
        exact E.pend_bot k Y (hw' k _ hk) j hj
      · intro j hj
        rw [(hf L).1] at hj
        obtain ⟨h1, h2, h3⟩ := E.quiet j hj
        exact ⟨by rw [(hf j).2.1]; exact h1, fun w' h => h2 w' (hw' j w' h),
          fun v h4 h5 => h3 v (hv v h4) h5⟩
      · intro hq
        obtain ⟨h1, h2⟩ := E.done (hdone hq)
        refine ⟨?_, by rw [(hf L).1]; exact h2⟩
        rw [hreg]
        by_cases hpL : p = L
        · subst hpL; exact E.lw w hpc
        · exfalso
          have hmem := Lead.mem_of_card hid hn hL _ (hB.disc_loc L) h2 p hpL
          exact (E.quiet p hmem).2.1 w hpc
      · intro w' h; exact E.lw w' (hw' L w' h)
  · -- response
    rcases hcase with ⟨a, hpc, hr, hloc⟩ | ⟨hpc, hloc⟩
    · have hf := pc_only hloc
      have hpcq : ∀ q, (C'.loc q).pc = if q = p then .fin else (C.loc q).pc :=
        fun q => (hf q).2.2.2.2
      refine lead_of_pc_change hL hreg (fun q => (hf q).1) (fun q => (hf q).2.1)
        (fun q => (hf q).2.2.1) ?_ ?_ ?_ ?_
      · intro q w hw; rw [hpcq] at hw; split_ifs at hw; exact hw
      · intro q a hw; rw [hpcq] at hw; split_ifs at hw; exact hw
      · intro q hw; rw [hpcq] at hw; split_ifs at hw with hqp
        · subst hqp; exact Or.inr ⟨a, hpc⟩
        · exact Or.inl hw
      · intro q r' h'
        rw [outputs_append_single] at h'
        by_cases hqp : q = p
        · subst hqp
          cases ho : outputs α q with
          | some r0 => rw [ho] at h'; simp at h'; subst h'; exact hL.out q _ ho
          | none =>
            rw [ho] at h'; simp at h'
            rw [← h', hr, hB.me, hL.ret q a hpc]
        · simp [Ne.symm hqp] at h'; exact hL.out q r' h'
    · have hfin : (C.loc p).pc = .fin := by
        rcases hpc with h1 | h1
        · exact absurd (hB.idle p h1) hp
        · exact h1
      refine lead_of_pc_change hL hreg (fun q => by rw [hloc]) (fun q => by rw [hloc])
        (fun q => by rw [hloc]) (fun q w h => by rwa [hloc] at h) (fun q a h => by rwa [hloc] at h)
        (fun q h => Or.inl (by rwa [hloc] at h)) ?_
      intro q r' h'
      rw [outputs_append_single] at h'
      by_cases hqp : q = p
      · subst hqp
        obtain ⟨r0, hr0⟩ := Option.ne_none_iff_exists'.1 (hB.fin q hfin)
        rw [hr0] at h'; simp at h'; subst h'; exact hL.out q _ hr0
      · simp [Ne.symm hqp] at h'; exact hL.out q r' h'


theorem noLead_step [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)}
    (hB : Basic ids α C) (hB' : Basic ids (α ++ [ℓ]) C') (hN : NoLead n α C)
    (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') :
    NoLead n (α ++ [ℓ]) C' ∨ ∃ L, Lead ids n out (α ++ [ℓ]) C' L := by
  rcases step_cases h with ⟨p, o, rfl, hp, hloc, hpend, hreg⟩ |
    ⟨p, rfl, hp, hpc, hloc, hpend, hreg⟩ | ⟨p, w, rfl, hp, hpc, hloc, hpend, hreg⟩ |
    ⟨p, r, rfl, hp, hpend, hreg, hcase⟩
  · -- invocation
    left
    have h0 : (C.loc p).pc = .idle := by
      by_contra hc; exact hB.busy p hc (hN.nofin p) hp
    rw [ite_eq_left h0] at hloc
    have hf := pc_only hloc
    refine ⟨?_, fun q => by rw [(hf q).2.1]; exact hN.phase q, ?_, ?_,
      fun q => by rw [outputs_append_inv]; exact hN.noout q⟩
    · rintro v (h1 | ⟨q, hq⟩)
      · rw [hreg] at h1; exact hN.vals v (Or.inl h1)
      · rw [(hf q).2.2.2.2] at hq; split_ifs at hq; exact hN.vals v (InVals.of_write hq)
    · intro q a hq; rw [(hf q).2.2.2.2] at hq; split_ifs at hq; exact hN.noret q a hq
    · intro q hq; rw [(hf q).2.2.2.2] at hq; split_ifs at hq; exact hN.nofin q hq
  · -- read
    have hp' : C'.loc p = afterRead n (C.loc p) (reg C) := by rw [hloc]; simp
    have hq' : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq => by
      rw [hloc, Function.update_of_ne hq]
    have hv : ∀ v, InVals C' v → InVals C v ∨ (afterRead n (C.loc p) (reg C)).pc = .write v := by
      intro v hv
      rcases invals_of_update hloc hv with h1 | ⟨q, -, hq⟩ | h1
      · exact Or.inl (Or.inl (hreg ▸ h1))
      · exact Or.inl (InVals.of_write hq)
      · exact Or.inr h1
    have hrv : InVals C (reg C) := InVals.reg_self C
    have hrE := (hN.vals _ hrv).1
    have hsE := hN.phase p
    have hout : ∀ q, outputs (α ++ [.tau p]) q = none := fun q => by
      rw [outputs_append_tau]; exact hN.noout q
    -- a frame for `NoLead`
    have frame : (∀ v, (afterRead n (C.loc p) (reg C)).pc = .write v →
          v.phase = .electing ∧ (v.id ≠ none → v.disc.card ≠ n - 1)) →
        (afterRead n (C.loc p) (reg C)).phase = .electing →
        (∀ a, (afterRead n (C.loc p) (reg C)).pc ≠ .ret a) →
        NoLead n (α ++ [.tau p]) C' := by
      intro h1 h2 h3
      refine ⟨?_, ?_, ?_, ?_, hout⟩
      · intro v hv'
        rcases hv v hv' with h4 | h4
        · exact hN.vals v h4
        · exact h1 v h4
      · intro q; by_cases hqp : q = p
        · rw [hqp, hp']; exact h2
        · rw [hq' q hqp]; exact hN.phase q
      · intro q a; by_cases hqp : q = p
        · rw [hqp, hp']; exact h3 a
        · rw [hq' q hqp]; exact hN.noret q a
      · intro q; by_cases hqp : q = p
        · rw [hqp, hp']
          rcases afterRead_pc n (C.loc p) (reg C) with h4 | ⟨w, h4⟩ | ⟨a, h4⟩ <;> rw [h4] <;>
            simp
        · rw [hq' q hqp]; exact hN.nofin q
    rcases afterRead_cases n (C.loc p) (reg C) with ⟨hA1, hA2, hs'⟩ |
      ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, a, ha, hc, hph', hs'⟩ | ⟨hnA, hid0, hlo0, hs'⟩ |
      ⟨hnA, a, ha, hc, hne, hni, hs'⟩ | ⟨hs', hnA, hE1, hE2⟩
    · rw [hrE] at hA1; cases hA1
    · rw [hrE] at hph'; cases hph'
    · exact absurd hc ((hN.vals _ hrv).2 (by rw [ha]; simp))
    · -- line 14
      set d := if (reg C).phase = (C.loc p).phase then (C.loc p).disc ∪ (reg C).disc
        else (C.loc p).disc with hd
      have hp'' : C'.loc p =
          { C.loc p with pc := .write ⟨some (C.loc p).me, d, (C.loc p).phase⟩, disc := d } := by
        rw [hp', hs']
      by_cases hcard : d.card = n - 1
      · -- `p` becomes the leader
        right
        refine ⟨p, ?_⟩
        have hlp : (C'.loc p).loser = false := by rw [hp'']; exact hlo0
        have hlos : ∀ j, (C'.loc j).loser = true ↔ j ≠ p := by
          intro j
          constructor
          · intro h1 h2; rw [h2, hlp] at h1; cases h1
          · intro hj
            exact losers_of_card hid hn d (fun j => (C'.loc j).loser) p
              (fun x hx => hB'.disc_loc p x (by rw [hp'']; exact hx)) hlp hcard j hj
        have hsome : ∀ v, InVals C' v → v.id ≠ none →
            v = ⟨some (ids p), d, (C.loc p).phase⟩ := by
          rintro v (h1 | ⟨q, hq⟩) h2
          · rw [hreg] at h1; rw [← h1, hid0] at h2; exact absurd rfl h2
          · obtain ⟨h3, h4⟩ := hB'.wsome q v hq h2
            have hqp : q = p := by
              by_contra hne; have := (hlos q).2 hne; rw [h4] at this; cases this
            subst hqp; rw [h3, hp'']
        have hvE : ∀ v, InVals C' v → v.phase = .electing := by
          intro v hv'
          rcases hv v hv' with h1 | h1
          · exact (hN.vals v h1).1
          · rw [hs'] at h1; simp only [PC.write.injEq] at h1; rw [← h1]; exact hsE
        refine ⟨hlos, ?_, ?_, (fun q r h => by rw [hout q] at h; cases h), ?_, ?_⟩
        · intro v a' h1 h2
          rw [hsome v h1 (by rw [h2]; simp)] at h2; simp at h2; exact h2.symm
        · intro q a' h1
          by_cases hqp : q = p
          · rw [hqp, hp''] at h1; cases h1
          · rw [hq' q hqp] at h1; exact absurd h1 (hN.noret q a')
        · intro _
          refine ⟨by rw [hp'']; exact hcard, ?_, ?_, ?_, ?_⟩
          · intro v h1 h2; rw [hsome v h1 h2]; exact ⟨hsE, hcard⟩
          · intro v h1 h2; rw [hvE v h1] at h2; cases h2
          · intro q a' h1
            by_cases hqp : q = p
            · rw [hqp, hp''] at h1; cases h1
            · rw [hq' q hqp] at h1; exact hN.noret q a' h1
          · intro q h1
            by_cases hqp : q = p
            · rw [hqp, hp''] at h1; cases h1
            · rw [hq' q hqp] at h1; exact hN.nofin q h1
        · intro h1; rw [hp''] at h1; simp only at h1; rw [hsE] at h1; cases h1
      · left
        refine frame ?_ (by rw [hs']; exact hsE) (by rw [hs']; simp)
        intro v h1; rw [hs'] at h1; simp only [PC.write.injEq] at h1; subst h1
        exact ⟨hsE, fun _ => hcard⟩
    · -- line 17
      left
      refine frame ?_ (by rw [hs']; exact hsE) (by rw [hs']; simp)
      intro v h1; rw [hs'] at h1; simp only [PC.write.injEq] at h1; subst h1
      exact ⟨hsE, fun h => absurd rfl h⟩
    · left
      refine frame ?_ (by rw [hs']; exact hsE) (by rw [hs']; simp)
      intro v h1; rw [hs'] at h1; cases h1
  · -- write
    left
    have hf := pc_only hloc
    have hpcq : ∀ q, (C'.loc q).pc = if q = p then .read else (C.loc q).pc :=
      fun q => (hf q).2.2.2.2
    refine ⟨?_, fun q => by rw [(hf q).2.1]; exact hN.phase q, ?_, ?_,
      fun q => by rw [outputs_append_tau]; exact hN.noout q⟩
    · rintro v (h1 | ⟨q, hq⟩)
      · rw [hreg] at h1; subst h1; exact hN.vals _ (InVals.of_write hpc)
      · rw [hpcq] at hq; split_ifs at hq; exact hN.vals v (InVals.of_write hq)
    · intro q a hq; rw [hpcq] at hq; split_ifs at hq; exact hN.noret q a hq
    · intro q hq; rw [hpcq] at hq; split_ifs at hq; exact hN.nofin q hq
  · -- response: impossible
    exfalso
    rcases hcase with ⟨a, hpc, -, -⟩ | ⟨hpc | hpc, -⟩
    · exact hN.noret p a hpc
    · exact hp (hB.idle p hpc)
    · exact hN.nofin p hpc

/-! ### The invariant -/

variable (n out ids)

/-- The safety invariant of Algorithm 1. -/
def Inv (α : List (Label P (elecObj R))) (C : Cfg Id R P) : Prop :=
  Basic ids α C ∧ (NoLead n α C ∨ ∃ L, Lead ids n out α C L)

variable {n out ids}

theorem inv_init : Inv ids n out [] ((alg1 Id n out).impl ids π).initCfg := by
  refine ⟨basic_init, Or.inl ⟨?_, fun p => rfl, fun p a h => by
    simp [Impl.initCfg, SymAlg.impl, alg1] at h, fun p h => by
    simp [Impl.initCfg, SymAlg.impl, alg1] at h, fun p => rfl⟩⟩
  rintro v (h | ⟨q, hq⟩)
  · subst h; simp [reg, Impl.initCfg, SymAlg.impl, alg1, Reg.init]
  · simp [Impl.initCfg, SymAlg.impl, alg1] at hq

theorem inv_step [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)}
    (hI : Inv ids n out α C) (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') :
    Inv ids n out (α ++ [ℓ]) C' := by
  have hB' := basic_step hI.1 h
  refine ⟨hB', ?_⟩
  rcases hI.2 with hN | ⟨L, hL⟩
  · exact noLead_step hid hn hI.1 hB' hN h
  · exact Or.inr ⟨L, lead_step hid hn hI.1 hB' hL h⟩

/-- **The invariant holds in every reachable configuration.** -/
theorem inv_run [Fintype P] (hid : Function.Injective ids) (hn : Fintype.card P = n)
    {α : List (Label P (elecObj R))} {C : Cfg Id R P}
    (h : ((alg1 Id n out).impl ids π).run α = some C) : Inv ids n out α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil] at h
    rw [← Option.some.inj h]; exact inv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : ((alg1 Id n out).impl ids π).runFrom ((alg1 Id n out).impl ids π).initCfg α with
    | none => simp [hα] at h
    | some C₁ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      exact inv_step hid hn (ih hα) h

end BezoutElection.Alg1
