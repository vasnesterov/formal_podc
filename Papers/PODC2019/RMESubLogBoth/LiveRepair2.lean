import Papers.PODC2019.RMESubLogBoth.LiveRepair

/-!
# Liveness, part 2 (continued): a rank for the repairer

The rank `μc` of a configuration measures the remaining work of the holder of `RLock`: the
repair distance `rd` of its program counter (line 24 → 30 → 31 → scan → lines 39–49 → exit),
refined at line 35 by the progress of the process whose node the repairer waits for.
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-! ### Counting maximal paths -/

/-- The maximal paths of `(V, E)` not yet visited at line 42. -/
def mpSet (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (dn : List (List ℕ)) : Set (List ℕ) :=
  {σ | IsMaxPath V E σ ∧ σ ∉ dn}

/-- The number of maximal paths of `(V, E)` not yet visited at line 42. -/
noncomputable def nmp (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (dn : List (List ℕ)) : ℕ :=
  (mpSet V E dn).ncard

section
variable {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {dn : List (List ℕ)}

lemma mpSet_injOn (hout : OutDeg1 E) : Set.InjOn pstart (mpSet V E dn) := by
  intro _ hσ _ hτ hs
  exact path_eq_of_start hout hσ.1.1.1 hσ.1.1.2.2 hσ.1.2.2 hτ.1.1.1 hτ.1.1.2.2 hτ.1.2.2 hs

lemma mpSet_mapsTo : ∀ σ ∈ mpSet V E dn, pstart σ ∈ (V : Set ℕ) :=
  fun _ hσ => hσ.1.1.2.1 _ (pstart_mem hσ.1.1.1)

lemma mpSet_finite (hout : OutDeg1 E) : (mpSet V E dn).Finite :=
  Set.Finite.of_finite_image (V.finite_toSet.subset (by
    rintro _ ⟨σ, hσ, rfl⟩; exact mpSet_mapsTo σ hσ)) (mpSet_injOn hout)

lemma nmp_le (hout : OutDeg1 E) : nmp V E dn ≤ V.card := by
  rw [← Set.ncard_coe_finset V]
  exact Set.ncard_le_ncard_of_injOn pstart mpSet_mapsTo (mpSet_injOn hout) V.finite_toSet

lemma nmp_cons (hout : OutDeg1 E) {σ : List ℕ} (hσ : IsMaxPath V E σ) (hσd : σ ∉ dn) :
    nmp V E (σ :: dn) + 1 = nmp V E dn := by
  have : mpSet V E (σ :: dn) = mpSet V E dn \ {σ} := by
    ext τ; simp only [mpSet, Set.mem_ofPred_eq, List.mem_cons, Set.mem_sdiff,
      Set.mem_singleton_iff]; tauto
  rw [nmp, nmp, this]
  exact Set.ncard_sdiff_singleton_add_one ⟨hσ, hσd⟩ (mpSet_finite hout)

end

lemma card_addV_le (V : Finset ℕ) (a : ℕ) (v : PV) : (addV V a v).card ≤ V.card + 2 := by
  unfold addV
  split
  · exact (Finset.card_insert_le _ _).trans (by simpa using Finset.card_insert_le _ _)
  · exact (Finset.card_insert_le _ _).trans (by omega)

/-! ### The repair distance -/

/-- Repair distance of the holder of `RLock`. -/
noncomputable def rd : PC k → ℕ
  | .l24 _ _ => 10 * k + 14
  | .l30 _ _ => 10 * k + 13
  | .l31 _ => 10 * k + 12
  | .l33 _ _ V _ i => 11 + 3 * V.card + 10 * (k - i)
  | .l35 _ _ V _ i _ => 10 + 3 * V.card + 10 * (k - i)
  | .l36 _ _ V _ i _ => 9 + 3 * V.card + 10 * (k - i)
  | .l39 _ _ V E => 8 + 3 * nmp V E []
  | .l42 _ _ V E _ _ _ dn => 5 + 3 * nmp V E dn
  | .l43 _ _ V E _ _ _ dn _ => 7 + 3 * nmp V E dn
  | .l44 _ _ V E _ _ _ dn _ => 6 + 3 * nmp V E dn
  | .l46 _ _ _ _ _ _ _ => 4
  | .l47 _ _ => 3
  | .l49 _ _ => 2
  | .rx _ _ => 1
  | _ => 0

/-- Every step of the holder in the CS of `RLock` (except its exit, and except a busy-wait at
line 35) decreases the repair distance. -/
lemma rd_step {c c' : Cfg k} {own : ℕ → ℕ} {h : Fin k} (hL : LI c own h) (hs : Step c h c')
    (hR : (c.pc h).InR) (hrx : ∀ x v, c.pc h ≠ .rx x v)
    (hnb : ∀ x tl V E i a, c.pc h = .l35 x tl V E i a → c.nn a = true) :
    rd (c'.pc h) < rd (c.pc h) := by
  unfold LI at hL
  cases hpc : c.pc h with
  | l30 x v => rcases step_l30 hs hpc with h' | h' <;> simp [h', rd]
  | l31 x => simp [step_l31 hs hpc, rd]; omega
  | l33 x tl V E i =>
    rw [hpc] at hL
    obtain ⟨-, -, -, hik, EA, hS⟩ := hL
    rcases step_l33 hs hpc with ⟨hi, h'⟩ | ⟨hi, a, h'⟩ | ⟨hi, h'⟩
    · simp [h', rd]; omega
    · simp [h', rd]
    · have := nmp_le (dn := []) (V := V) hS.Eout
      simp [h', rd]; omega
  | l35 x tl V E i a =>
    rcases step_l35 hs hpc with ⟨-, h'⟩ | ⟨hn, -⟩
    · simp [h', rd]
    · have := hnb _ _ _ _ _ _ hpc; rw [this] at hn; cases hn
  | l36 x tl V E i a =>
    rw [hpc] at hL
    obtain ⟨-, -, -, hik, -⟩ := hL
    have := card_addV_le V a (c.pred a)
    simp [step_l36 hs hpc, rd]; omega
  | l39 x tl V E => obtain ⟨_, _, h'⟩ := step_l39 hs hpc; simp [h', rd]
  | l42 x tl V E mp tp hp' dn =>
    rw [hpc] at hL
    obtain ⟨-, -, -, EA, hS, -⟩ := hL
    rcases step_l42 hs hpc with ⟨σ, hσ, hσd, h'⟩ | h'
    · have := nmp_cons hS.Eout hσ hσd
      simp [h', rd]; omega
    · simp [h', rd]; omega
  | l43 x tl V E mp tp hp' dn σ => rcases step_l43 hs hpc with h' | h' <;> simp [h', rd]
  | l44 x tl V E mp tp hp' dn σ => obtain ⟨_, h'⟩ := step_l44 hs hpc; simp [h', rd]
  | l46 x tl V E mp tp hp' =>
    rcases step_l46 hs hpc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> simp [h', rd]
  | l47 x s => simp [step_l47 hs hpc, rd]
  | l49 x m => simp [step_l49 hs hpc, rd]
  | rx x v => exact absurd hpc (hrx x v)
  | _ => simp [hpc, PC.InR] at hR

/-! ### Waiting at line 35 -/

/-- Remaining steps of a process before it sets the `NonNil_Signal` of its node (line 15). -/
def f13 : PC k → ℕ
  | .l13 _ => 3
  | .l14 _ _ => 2
  | .l15 _ _ => 1
  | _ => 0

lemma f13_le (q : PC k) : f13 q ≤ 3 := by cases q <;> simp [f13]

open Classical in
/-- Remaining steps of the owner of node `a` before it sets `a.NonNil_Signal`. -/
noncomputable def ownW (c : Cfg k) (a : ℕ) : ℕ :=
  if h : ∃ o, c.node o = some a then f13 (c.pc h.choose) else 0

lemma ownW_eq {c : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) {o : Fin k} {a : ℕ}
    (hn : c.node o = some a) : ownW c a = f13 (c.pc o) := by
  have hex : ∃ o, c.node o = some a := ⟨o, hn⟩
  rw [ownW, dite_eq_left hex, hG.node_inj hex.choose_spec hn]

lemma ownW_le (c : Cfg k) (a : ℕ) : ownW c a ≤ 3 := by
  unfold ownW; split
  · exact f13_le _
  · omega

/-- Extra rank of the holder `h` waiting at line 35 for a node whose signal is not set. -/
noncomputable def blk (c : Cfg k) (h : Fin k) : ℕ :=
  match c.pc h with
  | .l35 _ _ _ _ _ a => if c.nn a then 0 else ownW c a
  | _ => 0

lemma blk_le (c : Cfg k) (h : Fin k) : blk c h ≤ 3 := by
  unfold blk; split
  · split
    · omega
    · exact ownW_le _ _
  · omega

lemma blk_of_l35 {c : Cfg k} {h : Fin k} {x tl : ℕ} {V : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {i a : ℕ} (hpc : c.pc h = .l35 x tl V E i a) :
    blk c h = if c.nn a then 0 else ownW c a := by
  simp [blk, hpc]

lemma blk_eq_zero {c : Cfg k} {h : Fin k}
    (hnb : ∀ x tl V E i a, c.pc h = .l35 x tl V E i a → c.nn a = true) : blk c h = 0 := by
  unfold blk; split
  · next a _ hpc => simp [hnb _ _ _ _ _ _ hpc]
  · rfl

/-- The rank of a configuration. -/
noncomputable def μc (c : Cfg k) : ℕ :=
  match c.holder with
  | none => 4 * (10 * k + 15)
  | some h => 4 * rd (c.pc h) + blk c h

lemma μc_none {c : Cfg k} (hh : c.holder = none) : μc c = 4 * (10 * k + 15) := by
  simp [μc, hh]

lemma μc_some {c : Cfg k} {h : Fin k} (hh : c.holder = some h) :
    μc c = 4 * rd (c.pc h) + blk c h := by
  simp [μc, hh]

/-- The driver: a process whose next step decreases the rank. -/
def Drv (c : Cfg k) (p : Fin k) : Prop :=
  match c.holder with
  | none => ∃ y v, c.pc p = .l24 y v
  | some h => (∃ x tl V E i a, c.pc h = .l35 x tl V E i a ∧ c.nn a = false ∧
      c.node p = some a) ∨ (p = h ∧ ∀ x tl V E i a, c.pc h = .l35 x tl V E i a → c.nn a = true)

/-! ### Frame lemmas for signals -/

lemma step_nn_mono {c c' : Cfg k} {p : Fin k} (hs : Step c p c') {a : ℕ} (ha : c.nn a = true) :
    c'.nn a = true := by
  cases hs <;> simp_all [Cfg.setPc, Function.update_apply]

lemma step_nn_change {c c' : Cfg k} {p : Fin k} (hs : Step c p c') {a : ℕ}
    (hne : c'.nn a ≠ c.nn a) : (∃ m, c.pc p = .l15 a m) ∨ ∃ v, c.pc p = .l23 a v := by
  cases hs <;> simp_all [Cfg.setPc, Function.update_apply]

lemma step_l24_acq {c c' : Cfg k} {p : Fin k} (hs : Step c p c') {x : ℕ} {v : PV}
    (hpc : c.pc p = .l24 x v) (hl : c.holder = none ∨ c.holder = some p) :
    c'.pc p = .l30 x v ∧ c'.holder = some p := by
  cases hs <;> simp_all

/-- A node whose `NonNil_Signal` is not set belongs to a process at lines 13–15 (when nobody runs
the recovery code before `RLock`). -/
lemma owner_of_nn {c : Cfg k} {own : ℕ → ℕ} (hG : Glob c own) (hL : ∀ q, LI c own q)
    (h0 : ∀ q, preW c q = 0) {a : ℕ} (ha : a < c.nxt) (hna : c.nn a = false) :
    ∃ o, c.node o = some a ∧ 0 < f13 (c.pc o) := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · have := hG.special.2.2; simp_all
  rcases hG.table a hpos ha with ⟨o, ho⟩ | hrel
  · refine ⟨o, ho, ?_⟩
    have hLo := hL o
    have h0o := h0 o
    unfold LI at hLo
    have hio := hG.ioNN a
    cases hpc : c.pc o <;> simp only [hpc] at hLo <;> simp only [f13] <;> try omega
    all_goals first
      | (simp [preW, hpc] at h0o; done)
      | (simp [preW, hpc] at h0o; split_ifs at h0o)
      | simp_all [Cfg.Rel]
  · have := hG.ioNN a (.inr hrel.1); simp_all

end Podc.RMESubLogBoth
