import Papers.PODC2011.SimultaneousAllCaseOptimal.ThreeProcesses

/-!
# A protocol with the ConCon properties for `n = 3`, `t = 2`

To show that `theorem6_fails` is not vacuous, we exhibit, for `n = 3` and `t = 2`, a
continuous-consensus protocol `loneCC` with every property the paper attributes to ConCon in §2.3
and uses (accuracy, consistency, (i) and (ii); `IsConCon`): flood the known pairs; a process that
received nothing in round 1 (it is alone, and `W = 1`) puts its own pair in the core at time `2`;
otherwise the core is the set of known pairs from time `3` on (`W = 0`).

With `C = loneCC`, `Opt(floodSet 2, 2)` is therefore a concrete instance of the paper's construction
which is not all-case optimal (`theorem6_counterexample`).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I : Type} [Fintype P] [DecidableEq P] [DecidableEq I] [LinearOrder I]

open Classical in
/-- The CC protocol for `n = 3`, `t = 2`. -/
noncomputable def loneCC : CCProtocol P I (FloodMsg P I) where
  send p x h _ := some (known p x h)
  core p x h q :=
    if 2 ≤ h.length ∧ ∀ s, rcv h 0 s = none then (if q = p then some x else none)
    else if hh : 3 ≤ h.length ∧ ∃ v, (q, v) ∈ known p x h then some (Classical.choose hh.2)
    else none

lemma hist_loneCC (r : Run P I) (m : ℕ) (p : P) :
    hist (loneCC (P := P) (I := I)).toProtocol r m p = hist (floodSet 0) r m p :=
  hist_eq_of_send (A := loneCC.toProtocol) (B := floodSet 0) rfl r m p

open Classical in
lemma coreAt_loneCC {r : Run P I} {p : P} {m : ℕ} :
    (loneCC (P := P) (I := I)).coreAt r p m = fun q =>
      if 2 ≤ m ∧ SilentInbox r p then (if q = p then some (r.input p) else none)
      else if hh : 3 ≤ m ∧ ∃ v, (q, v) ∈ knownAt r m p then some (Classical.choose hh.2)
      else none := by
  classical
  funext q
  have e : ∀ s, 1 ≤ m → rcv (hist (floodSet (P := P) (I := I) 0) r m p) 0 s =
      msg (floodSet 0) r s p 0 := fun s hm => rcv_hist r p s (by omega)
  have hc : ∀ x h, (loneCC (P := P) (I := I)).core p x h q =
      if 2 ≤ h.length ∧ ∀ s, rcv h 0 s = none then (if q = p then some x else none)
      else if hh : 3 ≤ h.length ∧ ∃ v, (q, v) ∈ known p x h then some (Classical.choose hh.2)
      else none := fun _ _ => rfl
  rw [CCProtocol.coreAt, hc, hist_loneCC, Cslib.SyncCrash.length_hist]
  by_cases hm : 2 ≤ m
  · have : (∀ s, rcv (hist (floodSet (P := P) (I := I) 0) r m p) 0 s = none) ↔
        SilentInbox r p := by
      simp only [SilentInbox, e _ (by omega)]
    by_cases hs : SilentInbox r p
    · simp only [hm, true_and, this, hs, ↓reduceIte]
    · simp only [hm, true_and, this, hs, ↓reduceIte]; rfl
  · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]; rfl

/-- Two distinct processes and two processes different from both: the latter are equal
(`n = 3`). -/
lemma eq_of_card_three (hn : Fintype.card P = 3) {a b x y : P} (hab : a ≠ b) (hxa : x ≠ a)
    (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) : x = y := by
  by_contra hxy
  have : ({a, b, x, y} : Finset P).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hxy]
    · simp [hxa.symm, hxb.symm, hya.symm, hyb.symm, hxy]
    · simp [hab, hxa.symm, hya.symm]
  have := Finset.card_le_univ ({a, b, x, y} : Finset P)
  omega

/-- For `n = 3`, `t = 2`: the waste is `1` iff some process survives round 1 with an empty
round-1 inbox. -/
lemma waste_eq_one_iff (hn : Fintype.card P = 3) {r : Run P I}
    (hr : (consensus P I).IsRun 2 r) :
    r.waste = 1 ↔ ∃ p, r.Alive p 1 ∧ SilentInbox r p := by
  classical
  have hlt := waste_lt hr.1 (by norm_num)
  constructor
  · intro hw
    have hpos : 0 < r.waste := by omega
    unfold Run.waste at hpos
    obtain ⟨k, hk, hk'⟩ := (Finset.lt_sup_iff (f := fun k => r.exposed k - k)).1 hpos
    have hle := (exposed_le_faulty r k).trans hr.1.1
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · rcases Nat.eq_zero_or_pos k with rfl | h0
        · have := exposed_zero r; omega
        · omega
      · omega
    subst hk1
    obtain ⟨a, b, hab, ha, hb⟩ := exists_pair_of_two_le_exposed (r := r) (k := 1) (by omega)
    -- an exposure in round 1 means a crash in round 1, with a missing edge to a survivor
    have expo : ∀ x, (∃ j ≤ 1, r.ExposedIn x j) → ¬ r.Alive x 1 ∧
        ∃ w, r.Alive w 1 ∧ ¬ r.Deliv x w 0 := by
      rintro x ⟨j, hj, hj1, w, hw, hd⟩
      have : j = 1 := by omega
      subst this
      refine ⟨fun hx => hd ⟨hr.1.alive_zero x, fun hc => ?_⟩, w, hw, hd⟩
      have := hx 1 hc.1; omega
    obtain ⟨hadead, wa, hwa, hda⟩ := expo a ha
    obtain ⟨hbdead, wb, hwb, hdb⟩ := expo b hb
    have hwab : wa = wb := eq_of_card_three hn hab
      (fun h => hadead (h ▸ hwa)) (fun h => hbdead (h ▸ hwa))
      (fun h => hadead (h ▸ hwb)) (fun h => hbdead (h ▸ hwb))
    subst hwab
    refine ⟨wa, hwa, fun s => ?_⟩
    rw [msg_eq_deliv]
    split_ifs with hs
    · exfalso
      obtain ⟨hsw, hd⟩ := hs
      have hsa : s ≠ a := fun h => hda (h ▸ hd)
      have hsb : s ≠ b := fun h => hdb (h ▸ hd)
      exact hsw (eq_of_card_three hn hab hsa hsb (fun h => hadead (h ▸ hwa))
        (fun h => hbdead (h ▸ hwa)))
    · rfl
  · rintro ⟨p, hp, hs⟩
    have hexp : 2 ≤ r.exposed 1 := by
      refine le_trans ?_ (card_le_exposed (Finset.univ.erase p) fun q hq => ?_)
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hn]
      · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
        refine ⟨1, le_rfl, le_rfl, p, hp, fun hd => ?_⟩
        have := hs q
        rw [msg_eq_deliv, if_pos ⟨hq, hd⟩] at this
        simp [floodSet] at this
    have := le_waste r (k := 1) (by omega)
    omega

/-- **Non-vacuity**: for `n = 3`, `t = 2`, `loneCC` has the ConCon properties of §2.3. -/
theorem loneCC_isConCon (hn : Fintype.card P = 3) :
    IsConCon (loneCC (P := P) (I := I)) (consensus P I) 2 := by
  classical
  have hW : ∀ r, (consensus P I).IsRun 2 r → r.waste = 0 ∨ r.waste = 1 := fun r hr => by
    have := waste_lt hr.1 (by norm_num); omega
  -- the known branch of the core
  have known_core : ∀ (r : Run P I) (m : ℕ) (p q : P) (v : I),
      (if hh : 3 ≤ m ∧ ∃ v, (q, v) ∈ knownAt r m p then some (Classical.choose hh.2) else none) =
        some v → r.input q = v := by
    intro r m p q v h
    split_ifs at h with hh
    cases h
    exact mem_knownAt (Classical.choose_spec hh.2)
  refine { accurate := ?_, consistent := ?_, empty := ?_, full := ?_ }
  · intro r hr p m q v hp h
    rw [coreAt_loneCC] at h
    simp only at h
    split_ifs at h with h1 h2
    · subst h2; cases h; rfl
    · exact known_core r m p q v (by rw [dif_pos ‹_›]; exact h)
  · intro r hr p q m hp hq
    by_cases hpq : p = q
    · rw [hpq]
    have hns : ∀ x, r.Alive x m → 1 ≤ m → ¬ SilentInbox r x := by
      intro x hx hm hs
      have hy : ∃ y, y ≠ x ∧ r.Alive y m := by
        by_cases hxp : x = p
        · exact ⟨q, fun h => hpq (hxp.symm.trans h.symm), hq⟩
        · exact ⟨p, hxp ∘ Eq.symm, hp⟩
      obtain ⟨y, hyx, hy⟩ := hy
      exact hs.not_alive hr.1 hyx (hy.mono hm)
    rw [coreAt_loneCC, coreAt_loneCC]
    funext s
    by_cases hm : 1 ≤ m
    · simp only [hns p hp hm, hns q hq hm, and_false, if_false]
      by_cases h3 : 3 ≤ m
      · rw [known_hist_agree hr.1 (t := 2) (R := m) (Or.inl (by omega)) hp hq]
      · simp [h3]
    · simp [show ¬ 2 ≤ m by omega, show ¬ 3 ≤ m by omega]
  · intro r hr p m hp hm q
    rw [coreAt_loneCC]
    simp only
    rcases hW r hr with hw | hw
    · rw [hw] at hm
      have : ¬ (2 ≤ m ∧ SilentInbox r p) := fun h =>
        absurd ((waste_eq_one_iff hn hr).2 ⟨p, hp.mono (by omega), h.2⟩) (by omega)
      rw [if_neg this, dif_neg (by omega)]
    · rw [hw] at hm
      rw [if_neg (by omega), dif_neg (by omega)]
  · intro r hr p q hp hq
    rw [coreAt_loneCC]
    simp only
    rcases hW r hr with hw | hw
    · rw [hw] at hp hq ⊢
      have hns : ¬ SilentInbox r p := fun h =>
        absurd ((waste_eq_one_iff hn hr).2 ⟨p, hp.mono (by omega), h⟩) (by omega)
      have hmem : (q, r.input q) ∈ knownAt r 3 p := by
        by_cases hqp : q = p
        · rw [hqp]; exact self_mem_knownAt r 3 p
        · exact mem_knownAt_of_deliv (by omega)
            ⟨hr.1.alive_zero q, fun hc => by have := hq 1 hc.1; omega⟩
      have hex : 3 ≤ 2 + 1 - 0 ∧ ∃ v, (q, v) ∈ knownAt r (2 + 1 - 0) p := ⟨le_rfl, _, hmem⟩
      rw [if_neg (fun h => hns h.2), dif_pos hex]
      exact congrArg some (mem_knownAt (Classical.choose_spec hex.2)).symm
    · rw [hw] at hp hq ⊢
      obtain ⟨s, hs1, hss⟩ := (waste_eq_one_iff hn hr).1 hw
      have hps : p = s := by
        by_contra hne; exact hss.not_alive hr.1 hne (hp.mono (by omega))
      have hqs : q = s := by
        by_contra hne; exact hss.not_alive hr.1 hne (hq.mono (by omega))
      subst hps; subst hqs
      rw [if_pos ⟨by omega, hss⟩, if_pos rfl]

/-- **Theorem 6 fails for a concrete protocol with the ConCon properties**: for `n = 3`, `t = 2`,
consensus on a set with two distinct values, `k̂ = 2`, `A = floodSet 2` and `C = loneCC`, all
hypotheses of Theorem 6 except Lemma 5 hold (`theorem6_hypotheses`, `loneCC_isConCon`), but
`Opt(A, k̂)` is not all-case optimal. -/
theorem theorem6_counterexample (hn : Fintype.card P = 3) [Nonempty I] :
    IsConCon (loneCC (P := P) (I := I)) (consensus P I) 2 ∧
      ¬ AllCaseOptimal (Opt loneCC (floodSet 2) (consensus P I) 2) (consensus P I) 2 :=
  ⟨loneCC_isConCon hn, theorem6_fails hn (loneCC_isConCon hn)⟩

end Podc.SimultaneousAllCaseOptimal
