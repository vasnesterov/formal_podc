import Papers.PODC2011.KSetAgreement.Theorem2

/-!
# The trivial algorithm and the degenerate case `f = n`

`own` decides its own input in its first step and never sends anything. It solves `k`-set
agreement for every `k ≥ n` under any failure assumption in which every process is faulty or
correct. This shows that the impossibility statements need `f < n` (which the paper assumes
implicitly — its sets `D_i` of size `n - f` must be nonempty):

* Theorem 8 claims that with up to `f` initially dead processes `k`-set agreement is solvable only
  if `k * n > (k + 1) * f`; for `f = n` and `k ≥ n` this fails (`theorem8_false_of_f_eq_n`).
* Theorem 2 / Corollary 5 for `f = n` would claim impossibility of `n`-set agreement
  (`k * (n - f) = 0 ≤ n - 1`), but `own` solves it (`theorem2_false_of_f_eq_n`).
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P V : Type*} [DecidableEq P]

/-- Decide your own input in your first step; never send anything. -/
def own : KAlgorithm P Unit V V where
  init _ v := v
  step _ _ st := st.1
  send _ _ _ := 0
  out _ e st := if e.isNone then some st.1 else none

omit [DecidableEq P] in
theorem own_run_some (p : P) (es : List (Option Unit)) (v : V) :
    (own.run p es (v, some v)) = ((v, some v), 0) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [KAlgorithm.run]
    have : own.apply p e (v, some v) = (v, some v) := by
      simp [KAlgorithm.apply, own]
    rw [this, ih]
    simp [own]

omit [DecidableEq P] in
theorem own_run_wake (p : P) (es : List (Option Unit)) (v : V) :
    (own.run p (none :: es) (v, none)) = ((v, some v), 0) := by
  simp only [KAlgorithm.run]
  have : own.apply p none (v, none) = (v, some v) := by
    simp [KAlgorithm.apply, own]
  rw [this, own_run_some]
  simp [own]

/-- Invariant of `own`: a woken process has decided its own input. -/
def OwnInv (x : P → V) (s : State P Unit (Loc Unit V V)) : Prop :=
  ∀ p, (∃ l, (s.proc p).state = Sum.inl l) ∨ (s.proc p).state = Sum.inr (x p, some (x p))

theorem ownInv_tr (x : P → V) {s s' : State P Unit (Loc Unit V V)} {a : Action P Unit}
    (h : OwnInv x s) (htr : (own.algX x).lts.Tr s a s') : OwnInv x s' := by
  cases a with
  | none =>
    have : s' = s := htr
    subst this; exact h
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    intro p
    simp only [Algorithm.recvMsg]
    by_cases hp : p = m.dest
    · subst hp
      simp only [↓reduceIte]
      show (∃ l, own.nextLoc (fun p _ => x p) m.dest m.msg (s.proc m.dest).state = Sum.inl l) ∨
        own.nextLoc (fun p _ => x p) m.dest m.msg (s.proc m.dest).state =
          Sum.inr (x m.dest, some (x m.dest))
      rcases hmsg : m.msg with b | u
      · rcases (h m.dest) with ⟨l, hl⟩ | hl
        · right
          simp only [KAlgorithm.nextLoc, hl]
          rw [show own.init m.dest (x m.dest) = x m.dest from rfl, own_run_wake]
        · right; simp [KAlgorithm.nextLoc, hl]
      · rcases (h m.dest) with ⟨l, hl⟩ | hl
        · left; simp [KAlgorithm.nextLoc, hl]
        · right; simp [KAlgorithm.nextLoc, hl, KAlgorithm.apply, own]
    · simp only [hp, ↓reduceIte]
      exact h p

theorem ownInv_reachable [Fintype P] (x : P → V) (inp : P → Bool)
    {s : State P Unit (Loc Unit V V)} (h : (own.algX x).Reachable inp s) : OwnInv x s := by
  obtain ⟨xl, hxl⟩ := h
  have h0 : OwnInv x ((own.algX x).start inp) := fun p => Or.inl ⟨[], rfl⟩
  generalize (own.algX x).start inp = s₀ at h0 hxl
  induction hxl with
  | refl => exact h0
  | stepL htr _ ih => exact ih (ownInv_tr x h0 htr)

/-- `own` is safe for `k ≥ |P|`. -/
theorem own_safe [Fintype P] {k : ℕ} (hk : Fintype.card P ≤ k) : KSafe (own : KAlgorithm P Unit V V) k := by
  intro x inp s hs
  have hinv := ownInv_reachable x inp hs
  have hval : ∀ p v, dec s p = some v → x p = v := by
    intro p v hv
    rcases hinv p with ⟨l, hl⟩ | hl
    · simp [dec, hl, KAlgorithm.decOf] at hv
    · simpa [dec, hl, KAlgorithm.decOf] using hv
  refine ⟨?_, fun p v hv => ⟨p, hval p v hv⟩⟩
  have hsub : decVals s ⊆ Set.range x := by
    rintro v ⟨p, hp⟩; exact ⟨p, hval p v hp⟩
  calc (decVals s).ncard ≤ (Set.range x).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set P).ncard := by
        rw [← Set.image_univ]; exact Set.ncard_image_le (Set.toFinite _)
    _ = Fintype.card P := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    _ ≤ k := hk

/-- `own` terminates in every run in which every process is faulty or correct. -/
theorem own_terminates [Fintype P] (R : RunPred P Unit (Loc Unit V V))
    (hR : ∀ a inp ss xs, R a inp ss xs →
      IsRun a inp ss xs ∧ ∀ p, ProcFaulty p ss xs ∨ ProcFair p ss xs) :
    Terminates (own : KAlgorithm P Unit V V) R := by
  intro x inp ss xs h p
  obtain ⟨⟨h0, hex⟩, hfr⟩ := hR _ _ _ _ h
  rcases hfr p with hf | hf
  · exact Or.inl hf
  · right
    have hw : (⟨p, Sum.inl (inp p)⟩ : Message P Unit) ∈ (ss 0).msgs := by
      rw [h0]; simp [Algorithm.start]
    obtain ⟨j, -, hj⟩ := hf _ rfl 0 hw
    refine ⟨j + 1, x p, ?_⟩
    have htr := hex j
    rw [hj] at htr
    obtain ⟨_, hss⟩ := htr
    have hinv := ownInv_reachable x inp (s := ss (j + 1))
      ⟨_, by rw [← h0]; exact LTS.OmegaExecution.extract_mTr hex (Nat.zero_le _)⟩
    rcases hinv p with ⟨l, hl⟩ | hl
    · exfalso
      rw [hss] at hl
      simp only [Algorithm.recvMsg, ↓reduceIte] at hl
      change own.nextLoc (fun p _ => x p) p (Sum.inl (inp p)) ((ss j).proc p).state =
        Sum.inl l at hl
      rcases hst : ((ss j).proc p).state with buf | st <;>
        simp [KAlgorithm.nextLoc, hst] at hl
    · simp [dec, hl, KAlgorithm.decOf]

theorem initDead_faulty_or_fair [Fintype P] {M L : Type*} [DecidableEq M] {f : ℕ}
    {a : Algorithm P M L} {inp : P → Bool} {ss : ωSequence (State P M L)}
    {xs : ωSequence (Action P M)} (h : InitDead f a inp ss xs) :
    IsRun a inp ss xs ∧ ∀ p, ProcFaulty p ss xs ∨ ProcFair p ss xs := by
  obtain ⟨hrun, dead, -, hdead, hfair⟩ := h
  refine ⟨hrun, fun p => ?_⟩
  by_cases hp : p ∈ dead
  · exact Or.inl (neverSteps_procFaulty hrun (hdead p hp))
  · exact Or.inr (hfair p hp)

/-- **Theorem 8 is false for `f = n`**: with all `n` processes possibly initially dead and
`k ≥ n`, the condition `k * n > (k + 1) * f` fails, but `own` solves `k`-set agreement. -/
theorem theorem8_false_of_f_eq_n [Fintype P] {k : ℕ} (hk : Fintype.card P ≤ k) :
    ¬ ((k + 1) * Fintype.card P < k * Fintype.card P) ∧
      SolvesKSA (own : KAlgorithm P Unit V V) k (InitDead (Fintype.card P)) := by
  refine ⟨by nlinarith, own_safe hk, own_terminates _ fun _ _ _ _ h => initDead_faulty_or_fair h⟩

/-- **Theorem 2 / Corollary 5 need `f < n`**: for `f = n = k` the bound `k * (n - f) ≤ n - 1`
holds, but `own` solves `n`-set agreement with up to `n` crashes (so in particular with Theorem 2's
failure pattern). -/
theorem theorem2_false_of_f_eq_n [Fintype P] :
    Fintype.card P * (Fintype.card P - Fintype.card P) ≤ Fintype.card P - 1 ∧
      SolvesKSA (own : KAlgorithm P Unit V V) (Fintype.card P) (Crash (Fintype.card P)) ∧
      SolvesKSA (own : KAlgorithm P Unit V V) (Fintype.card P) (OneCrash (Fintype.card P)) := by
  refine ⟨by simp, ⟨own_safe le_rfl, own_terminates _ fun _ _ _ _ h => ⟨⟨h.1, h.2.1⟩, h.2.2.1⟩⟩,
    own_safe le_rfl, own_terminates _ fun _ _ _ _ h => ?_⟩
  have h' := oneCrash_crash h
  exact ⟨⟨h'.1, h'.2.1⟩, h'.2.2.1⟩

end KSetAgreement
