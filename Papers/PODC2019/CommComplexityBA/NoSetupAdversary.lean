import Papers.PODC2019.CommComplexityBA.NoSetupTwoCopy

/-!
# The adversaries of the proof of Theorem 13

The adversary's randomness `ρ : P → T` is a set of fresh tapes. Reading the real messages of the
special node `S` from the transcript, it simulates in its head an execution of all nodes other than
`S` with inputs `x2` and tapes `ρ` (`simRun`), and *injects* the messages that simulated nodes send
to `S`, as long as at most `C` simulated nodes have spoken so far.

* `advH` (world `W_{h,b}`): corrupts the simulated speakers (at most `C`); `S` stays honest.
* `advC` (world `W_{c,b}`): corrupts only `S` (it injects to `S`, i.e. `S` behaves as if it had
  received the simulated messages).

Both inject the same messages, so the two worlds have *the same execution*; only the set of
corrupted nodes differs. `run_eq_tc`: this execution is the two-copy system with copy 2 truncated.
-/

set_option linter.unusedSectionVars false

open MeasureTheory

namespace CommComplexityBA.NoSetup

variable {P I M T : Type*} [DecidableEq P] [Fintype P]

namespace Protocol

variable (π : Protocol P I M T) (S : P) (C : ℕ) (x2 : P → I)

/-- Simulated traffic in round `r` given the simulated histories `h`; `S`'s messages are read from
the transcript `l`. -/
def simTraffic (ρ : P → T) (l : List (Traffic P M)) (r : ℕ) (h : P → MHistory P M) :
    Traffic P M :=
  fun j q => if j = S then (l.getD r fun _ _ => 0) S q else π.sent x2 ρ h j q

/-- The adversary's simulation: histories and speakers (other than `S`) after `r` rounds. -/
noncomputable def simRun (ρ : P → T) (l : List (Traffic P M)) : ℕ → (P → MHistory P M) × Finset P
  | 0 => (fun _ => [], ∅)
  | r + 1 =>
    ((fun q => (simRun ρ l r).1 q ++ [fun j => π.simTraffic S x2 ρ l r (simRun ρ l r).1 j q]),
      (simRun ρ l r).2 ∪ speakersOf S (π.simTraffic S x2 ρ l r (simRun ρ l r).1))

/-- Simulated speakers in rounds `0..r`. -/
noncomputable def simSp (ρ : P → T) (l : List (Traffic P M)) (r : ℕ) : Finset P :=
  (π.simRun S x2 ρ l (r + 1)).2

/-- Injected messages: simulated messages to `S` while at most `C` simulated nodes have spoken. -/
noncomputable def wInject (ρ : P → T) (l : List (Traffic P M)) (j q : P) : Multiset M := by
  classical exact
    if q = S ∧ j ≠ S ∧ (π.simSp S x2 ρ l l.length).card ≤ C then
      π.simTraffic S x2 ρ l l.length (π.simRun S x2 ρ l l.length).1 j S
    else 0

/-- Corrupted nodes of `W_h`: the simulated speakers up to the last round with at most `C` of
them. -/
noncomputable def wCorrupt (ρ : P → T) (l : List (Traffic P M)) : Finset P := by
  classical exact
    if (π.simSp S x2 ρ l (Nat.findGreatest (fun r => (π.simSp S x2 ρ l r).card ≤ C) l.length)).card
        ≤ C
    then π.simSp S x2 ρ l (Nat.findGreatest (fun r => (π.simSp S x2 ρ l r).card ≤ C) l.length)
    else ∅

lemma speakersOf_simTraffic (ρ : P → T) (l l' : List (Traffic P M)) (r r' : ℕ)
    (h : P → MHistory P M) :
    speakersOf S (π.simTraffic S x2 ρ l r h) = speakersOf S (π.simTraffic S x2 ρ l' r' h) :=
  speakersOf_congr fun j hj => by funext q; simp [simTraffic, hj]

lemma simRun_append (ρ : P → T) (l m : List (Traffic P M)) :
    ∀ r ≤ l.length, π.simRun S x2 ρ (l ++ m) r = π.simRun S x2 ρ l r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    have ih := ih (by omega)
    have hg : (l ++ m).getD r (fun _ _ => 0) = l.getD r (fun _ _ => 0) :=
      List.getD_append _ _ _ _ (by omega)
    simp only [simRun, ih]
    rw [π.speakersOf_simTraffic S x2 ρ (l ++ m) l r r]
    simp only [simTraffic, hg]

lemma simSp_eq (ρ : P → T) (l : List (Traffic P M)) (r : ℕ) :
    π.simSp S x2 ρ l r = (π.simRun S x2 ρ l r).2 ∪
      speakersOf S (π.simTraffic S x2 ρ l r (π.simRun S x2 ρ l r).1) := rfl

lemma simSp_append (ρ : P → T) (l m : List (Traffic P M)) (r : ℕ) (hr : r ≤ l.length) :
    π.simSp S x2 ρ (l ++ m) r = π.simSp S x2 ρ l r := by
  rw [simSp_eq, simSp_eq, π.simRun_append S x2 ρ l m r hr]
  congr 1
  exact π.speakersOf_simTraffic S x2 ρ _ _ _ _ _

lemma simSp_mono (ρ : P → T) (l : List (Traffic P M)) {r r' : ℕ} (h : r ≤ r') :
    π.simSp S x2 ρ l r ⊆ π.simSp S x2 ρ l r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    rw [simSp_eq _ _ _ _ _ (_ + 1)]
    exact Finset.subset_union_left

lemma not_mem_simRun (ρ : P → T) (l : List (Traffic P M)) (r : ℕ) :
    S ∉ (π.simRun S x2 ρ l r).2 := by
  induction r with
  | zero => simp [simRun]
  | succ r ih =>
    simp only [simRun, Finset.mem_union, ih, false_or, mem_speakersOf]
    simp

lemma not_mem_simSp (ρ : P → T) (l : List (Traffic P M)) (r : ℕ) : S ∉ π.simSp S x2 ρ l r :=
  π.not_mem_simRun S x2 ρ l (r + 1)

lemma card_wCorrupt (ρ : P → T) (l : List (Traffic P M)) : (π.wCorrupt S C x2 ρ l).card ≤ C := by
  unfold wCorrupt; split_ifs with h
  · exact h
  · simp

lemma not_mem_wCorrupt (ρ : P → T) (l : List (Traffic P M)) : S ∉ π.wCorrupt S C x2 ρ l := by
  unfold wCorrupt; split_ifs
  · exact π.not_mem_simSp S x2 ρ l _
  · simp

lemma wCorrupt_mono (ρ : P → T) (l : List (Traffic P M)) (x : Traffic P M) :
    π.wCorrupt S C x2 ρ l ⊆ π.wCorrupt S C x2 ρ (l ++ [x]) := by
  classical
  set g := Nat.findGreatest (fun r => (π.simSp S x2 ρ l r).card ≤ C) l.length with hg
  set g' := Nat.findGreatest (fun r => (π.simSp S x2 ρ (l ++ [x]) r).card ≤ C)
    (l ++ [x]).length with hg'
  have hgl : g ≤ l.length := Nat.findGreatest_le _
  have heq : π.simSp S x2 ρ (l ++ [x]) g = π.simSp S x2 ρ l g := π.simSp_append S x2 ρ l [x] g hgl
  unfold wCorrupt
  rw [← hg, ← hg']
  split_ifs with h1 h2 h2
  · have hle : g ≤ g' := Nat.le_findGreatest (by simp; omega) (by rw [heq]; exact h1)
    rw [← heq]; exact π.simSp_mono S x2 ρ _ hle
  · exact absurd (Nat.findGreatest_spec (P := fun r => (π.simSp S x2 ρ (l ++ [x]) r).card ≤ C)
      (m := g) (by simp; omega) (by rw [heq]; exact h1)) h2
  · simp
  · simp

lemma wInject_spec (ρ : P → T) (l : List (Traffic P M)) (j q : P)
    (h : π.wInject S C x2 ρ l j q ≠ 0) : j ∈ π.wCorrupt S C x2 ρ l ∧ q = S := by
  classical
  unfold wInject at h
  split_ifs at h with hc
  · obtain ⟨hq, hj, hcard⟩ := hc
    refine ⟨?_, hq⟩
    have hfg : Nat.findGreatest (fun r => (π.simSp S x2 ρ l r).card ≤ C) l.length = l.length :=
      Nat.findGreatest_eq hcard
    unfold wCorrupt
    rw [hfg, if_pos hcard, simSp_eq]
    exact Finset.mem_union_right _ (mem_speakersOf.mpr ⟨hj, S, h⟩)
  · exact absurd rfl h

/-- The adversary of world `W_{h,b}`. -/
noncomputable def advH : Adversary P M (P → T) C where
  corrupt := π.wCorrupt S C x2
  inject := π.wInject S C x2
  corrupt_mono := π.wCorrupt_mono S C x2
  card_corrupt := π.card_wCorrupt S C x2
  inject_spec ρ l p q h := Or.inl (π.wInject_spec S C x2 ρ l p q h).1

/-- The adversary of world `W_{c,b}`. -/
noncomputable def advC (hC : 1 ≤ C) : Adversary P M (P → T) C where
  corrupt _ _ := {S}
  inject := π.wInject S C x2
  corrupt_mono _ _ _ := le_rfl
  card_corrupt _ _ := by simpa using hC
  inject_spec ρ l p q h := Or.inr (by simp [(π.wInject_spec S C x2 ρ l p q h).2])

/-! ### The execution of `W` is the two-copy system with copy 2 truncated -/

/-- Parameters of the two-copy system realised by `W` (real inputs `x1`, tapes `ω`, `ρ`). -/
def wParams (x1 : P → I) (ω ρ : P → T) (t1 t2 : Bool) : TCParams P I T :=
  ⟨ω S, x1 S, ω, ρ, x1, x2, t1, t2⟩

variable (x1 : P → I) (ω ρ : P → T)

/-- Copy-1 traffic list of the first `r` rounds. -/
noncomputable def trList (c : TCParams P I T) (r : ℕ) : List (Traffic P M) :=
  (List.range r).map fun i =>
    π.copyTraffic S c.τS c.xS c.τ1 c.x1 (π.tcRun S C c i).hS (π.tcRun S C c i).h1

lemma copyTraffic_S (τS : T) (xS : I) (τ τ' : P → T) (x x' : P → I) (hS : MHistory P M)
    (h h' : P → MHistory P M) :
    π.copyTraffic S τS xS τ x hS h S = π.copyTraffic S τS xS τ' x' hS h' S := by
  funext q; simp [copyTraffic, Protocol.sent]

/-- The simulation inside the adversary reproduces copy 2 of the two-copy system. -/
lemma simRun_eq_tc (c : TCParams P I T) (hc : c.τ2 = ρ ∧ c.x2 = x2) (l : List (Traffic P M))
    (r : ℕ) (hl : ∀ i < r, (l.getD i fun _ _ => 0) S =
      π.copyTraffic S c.τS c.xS c.τ1 c.x1 (π.tcRun S C c i).hS (π.tcRun S C c i).h1 S) :
    (∀ j, j ≠ S → (π.simRun S x2 ρ l r).1 j = (π.tcRun S C c r).h2 j) ∧
      (π.simRun S x2 ρ l r).2 = (π.tcRun S C c r).sp2 := by
  obtain ⟨rfl, rfl⟩ := hc
  induction r with
  | zero => exact ⟨fun _ _ => rfl, rfl⟩
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => hl i (by omega)
    have htr : ∀ j, j ≠ S → π.simTraffic S c.x2 c.τ2 l r (π.simRun S c.x2 c.τ2 l r).1 j =
        π.copyTraffic S c.τS c.xS c.τ2 c.x2 (π.tcRun S C c r).hS (π.tcRun S C c r).h2 j := by
      intro j hj; funext q
      simp [simTraffic, copyTraffic, Protocol.sent, hj, ih1 j hj]
    have htrS : π.simTraffic S c.x2 c.τ2 l r (π.simRun S c.x2 c.τ2 l r).1 S =
        π.copyTraffic S c.τS c.xS c.τ2 c.x2 (π.tcRun S C c r).hS (π.tcRun S C c r).h2 S := by
      funext q
      simp only [simTraffic, ite_true]
      rw [hl r (by omega)]
      exact congrFun (π.copyTraffic_S S _ _ _ _ _ _ _ _ _) q
    have htr' : π.simTraffic S c.x2 c.τ2 l r (π.simRun S c.x2 c.τ2 l r).1 =
        π.copyTraffic S c.τS c.xS c.τ2 c.x2 (π.tcRun S C c r).hS (π.tcRun S C c r).h2 := by
      funext j
      by_cases hj : j = S
      · subst hj; exact htrS
      · exact htr j hj
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [simRun, tcRun_succ, tcStep, htr', ih1 j hj]
    · simp only [simRun, tcRun_succ, tcStep, htr', ih2]

/-- **The execution of `W`** (either adversary) is the two-copy system with copy 2 truncated. -/
lemma run_eq_tc (r : ℕ) :
    π.runI x1 ω (π.wInject S C x2 ρ) r =
      (Function.update (π.tcRun S C (wParams S x2 x1 ω ρ false true) r).h1 S
        (π.tcRun S C (wParams S x2 x1 ω ρ false true) r).hS,
       π.trList S C (wParams S x2 x1 ω ρ false true) r) := by
  set c := wParams S x2 x1 ω ρ false true with hc
  have hτ2 : c.τ2 = ρ := rfl
  have hx2 : c.x2 = x2 := rfl
  have hct : ∀ i, π.copyTraffic S c.τS c.xS c.τ1 c.x1 (π.tcRun S C c i).hS (π.tcRun S C c i).h1 =
      π.sent x1 ω (Function.update (π.tcRun S C c i).h1 S (π.tcRun S C c i).hS) := by
    intro i
    simp [copyTraffic, hc, wParams]
  have hlen : ∀ i, (π.trList S C c i).length = i := fun i => by simp [trList]
  have hget : ∀ i r', i < r' → (π.trList S C c r').getD i (fun _ _ => 0) =
      π.copyTraffic S c.τS c.xS c.τ1 c.x1 (π.tcRun S C c i).hS (π.tcRun S C c i).h1 := by
    intro i r' hi
    simp [trList, List.getD_eq_getElem?_getD, hi]
  induction r with
  | zero =>
    simp only [Protocol.runI, Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    funext q; by_cases hq : q = S <;> simp [hq, tcRun]
  | succ r ih =>
    simp only [Protocol.runI, ih, Prod.mk.injEq]
    obtain ⟨hs1, hs2⟩ := π.simRun_eq_tc S C x2 ρ c ⟨rfl, rfl⟩ (π.trList S C c r) r
      (fun i hi => by rw [hget i r hi])
    refine ⟨?_, ?_⟩
    · funext q
      rw [← hct r]
      by_cases hq : q = S
      · subst hq
        simp only [Function.update_self, tcRun_succ, tcStep]
        congr 2
        funext j
        have hw : π.wInject q C x2 ρ (π.trList q C c r) j q =
            if ((π.tcRun q C c r).sp2 ∪ speakersOf q (π.copyTraffic q c.τS c.xS c.τ2 c.x2
              (π.tcRun q C c r).hS (π.tcRun q C c r).h2)).card ≤ C then
            π.copyTraffic q c.τS c.xS c.τ2 c.x2 (π.tcRun q C c r).hS (π.tcRun q C c r).h2 j q
            else 0 := by
          unfold wInject
          rw [hlen r]
          by_cases hj : j = q
          · subst hj
            simp [copyTraffic, Protocol.sent]
          · have hsp : π.simSp q x2 ρ (π.trList q C c r) r = (π.tcRun q C c r).sp2 ∪
                speakersOf q (π.copyTraffic q c.τS c.xS c.τ2 c.x2 (π.tcRun q C c r).hS
                  (π.tcRun q C c r).h2) := by
              rw [simSp_eq, hs2]
              congr 1
              apply speakersOf_congr
              intro j' hj'
              funext q'
              simp [simTraffic, copyTraffic, Protocol.sent, hj', hs1 j' hj', hτ2, hx2]
            have hval : π.simTraffic q x2 ρ (π.trList q C c r) r
                (π.simRun q x2 ρ (π.trList q C c r) r).1 j q =
                π.copyTraffic q c.τS c.xS c.τ2 c.x2 (π.tcRun q C c r).hS (π.tcRun q C c r).h2 j q := by
              simp [simTraffic, copyTraffic, Protocol.sent, hj, hs1 j hj, hτ2, hx2]
            simp only [hsp, hval, true_and, ne_eq, hj, not_false_eq_true]
        rw [hw]
        simp [hc, wParams]
      · have hinj : π.wInject S C x2 ρ (π.trList S C c r) = fun j q' =>
            if q' = S ∧ j ≠ S ∧ (π.simSp S x2 ρ (π.trList S C c r) (π.trList S C c r).length).card
              ≤ C then
              π.simTraffic S x2 ρ (π.trList S C c r) (π.trList S C c r).length
                (π.simRun S x2 ρ (π.trList S C c r) (π.trList S C c r).length).1 j S else 0 := by
          funext j q'; unfold wInject; congr
        simp only [Function.update_of_ne hq, tcRun_succ, tcStep, hinj, hq, false_and, ite_false,
          add_zero]
    · simp only [trList, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [hct r]

end Protocol

end CommComplexityBA.NoSetup
