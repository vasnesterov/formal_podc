import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# Consensus over a lossy link with a finite horizon (Lemma 17)

Two distinct processes `a, b` are connected by a *lossy link*: in every round `t < L` at least one
of the messages `b → a`, `a → b` is delivered (the letter `w t : Lk` says which ones), there are no
other edges into `a` or `b`, and from round `L` on both are deaf (`lossyPat a b w L`; all other
processes are deaf as well, which is irrelevant for `a` and `b`).

* `lossy_decC_const`: if for every word `w` the processes `a` and `b` decide the same value, then
  this value does not depend on `w` (induction on the horizon `L`, the classical argument of
  Santoro–Widmayer / [52, Lemma 3]: the words `hearA·hearB^L` and `both·hearB^L` are
  indistinguishable for `a`, and `both·hearA^L`, `hearB·hearA^L` for `b`).
* `exists_lossy_disagree`: hence, if `a` deaf for the whole run decides `va` and `b` deaf for the
  whole run decides `vb ≠ va`, some word makes `a` and `b` decide differently.
* `lemma17_fixed`, `lemma17`: Lemma 17 of the paper for the two-process system `Fin 2`, in the
  fixed-horizon form (the switch round `r'` is fixed in advance) and in the paper's literal form
  (some `r'` exists, chosen by the adversary).

The general form (`exists_lossy_disagree` inside an arbitrary process set) is what the proof of
Theorem 9 needs: there the horizon `L` is determined by earlier phases and the bad word must be of
length exactly `L`.

We also prove the time-varying locality lemma `conf_eq_of_family` used throughout.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

section Locality

variable {P σ : Type}

/-- **Time-varying locality.** If the processes of `S (t + 1)` have the same in-neighbours in the
round-`t` graphs of `ρ` and `ρ'` and only hear processes of `S t`, and the initial configurations
agree on `S 0`, then the configurations at time `t` agree on `S t`. -/
theorem conf_eq_of_family (step : StepFn P σ) {C C' : P → σ} {ρ ρ' : ℕ → Graph P}
    (S : ℕ → Set P) (h0 : ∀ i ∈ S 0, C i = C' i)
    (hsame : ∀ t, ∀ i ∈ S (t + 1), SameIn (ρ t) (ρ' t) i)
    (hcl : ∀ t, ∀ i ∈ S (t + 1), ∀ j, Hears (ρ t) i j → j ∈ S t) :
    ∀ t, ∀ i ∈ S t, conf step C ρ t i = conf step C' ρ' t i := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro i hi
    exact next_eq_of_agree (hsame t i hi) (fun j hj => ih j (hcl t i hi j hj))

end Locality

namespace Alg

variable {P V σ : Type} (A : Alg P V σ)

/-- `i` eventually decides `v` when the run starts in configuration `C` and follows `ρ`. -/
def DecC (C : P → σ) (ρ : ℕ → Graph P) (i : P) (v : V) : Prop :=
  ∃ t, A.dec (conf A.step C ρ t i) = some v

variable {A}

theorem decides_iff_decC {x : P → V} {ρ : ℕ → Graph P} {i : P} {v : V} :
    A.Decides x ρ i v ↔ A.DecC (A.initC x) ρ i v := Iff.rfl

theorem DecC.unique {C : P → σ} {ρ : ℕ → Graph P} {i : P} {v w : V}
    (hv : A.DecC C ρ i v) (hw : A.DecC C ρ i w) : v = w := by
  obtain ⟨t, ht⟩ := hv
  obtain ⟨t', ht'⟩ := hw
  have h1 := A.dec_conf_mono ht (le_max_left t t')
  have h2 := A.dec_conf_mono ht' (le_max_right t t')
  exact Option.some_injective _ (h1.symm.trans h2)

/-- Decisions only depend on the trajectory of the process. -/
theorem decC_congr {C C' : P → σ} {ρ ρ' : ℕ → Graph P} {i i' : P} {v : V}
    (h : ∀ t, conf A.step C ρ t i = conf A.step C' ρ' t i') :
    A.DecC C ρ i v ↔ A.DecC C' ρ' i' v := by
  unfold DecC
  simp only [h]

/-- Decisions after a first round `G`. -/
theorem decC_pcons {C : P → σ} {G : Graph P} {ρ : ℕ → Graph P} {i : P} {v : V} :
    A.DecC C (pcons G ρ) i v ↔ A.DecC (next A.step G C) ρ i v := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← conf_pcons_succ]
    exact A.dec_conf_mono ht (Nat.le_succ t)
  · rintro ⟨t, ht⟩
    exact ⟨t + 1, by rw [conf_pcons_succ]; exact ht⟩

end Alg

/-! ### Lossy links -/

/-- A round of a lossy link between `a` and `b`: only `a` hears (`hearA`), only `b` hears
(`hearB`), or both hear each other (`both`). -/
inductive Lk
  | hearA
  | hearB
  | both
  deriving DecidableEq

/-- `a` receives the message of `b` in a round with letter `ℓ`. -/
def Lk.aH : Lk → Prop
  | .hearB => False
  | _ => True

/-- `b` receives the message of `a` in a round with letter `ℓ`. -/
def Lk.bH : Lk → Prop
  | .hearA => False
  | _ => True

variable {P : Type}

/-- The edges of a lossy-link round between `a` and `b` (no other edges). -/
def linkG (a b : P) (ℓ : Lk) : Graph P :=
  fun u v => (v = a ∧ u = b ∧ ℓ.aH) ∨ (v = b ∧ u = a ∧ ℓ.bH)

/-- The lossy-link pattern: rounds `t < L` follow the word `w`, afterwards nobody hears anybody. -/
def lossyPat (a b : P) (w : ℕ → Lk) (L : ℕ) : ℕ → Graph P :=
  fun t u v => t < L ∧ linkG a b (w t) u v

/-- Prepend a letter to a word. -/
def Lk.cons (ℓ : Lk) (w : ℕ → Lk) : ℕ → Lk
  | 0 => ℓ
  | t + 1 => w t

theorem lossyPat_zero (a b : P) (w w' : ℕ → Lk) : lossyPat a b w 0 = lossyPat a b w' 0 := by
  funext t u v; simp [lossyPat]

theorem lossyPat_succ (a b : P) (w : ℕ → Lk) (L : ℕ) :
    lossyPat a b w (L + 1) = pcons (linkG a b (w 0)) (lossyPat a b (fun t => w (t + 1)) L) := by
  funext t u v
  cases t with
  | zero => simp [lossyPat, pcons]
  | succ t => simp [lossyPat, pcons]

/-- In the lossy link, a process hears only the other end. -/
theorem linkG_mem {a b u v : P} {ℓ : Lk} (h : linkG a b ℓ u v) : (u = a ∨ u = b) ∧ (v = a ∨ v = b) := by
  rcases h with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> simp

theorem deaf_lossyPat_hearB {a b : P} (hab : a ≠ b) (L t : ℕ) :
    Deaf (lossyPat a b (fun _ => .hearB) L t) a := by
  rintro u ⟨-, ⟨-, -, h⟩ | ⟨h, -, -⟩⟩
  · exact h.elim
  · exact absurd h hab

theorem deaf_lossyPat_hearA {a b : P} (hab : a ≠ b) (L t : ℕ) :
    Deaf (lossyPat a b (fun _ => .hearA) L t) b := by
  rintro u ⟨-, ⟨h, -, -⟩ | ⟨-, -, h⟩⟩
  · exact absurd h.symm hab
  · exact h.elim

section Core

variable {V σ : Type} (A : Alg P V σ) {a b : P}

/-- **Core of Lemma 17.** If, for every word, `a` and `b` decide a common value, then this value
does not depend on the word. -/
theorem lossy_decC_const (hab : a ≠ b) : ∀ (L : ℕ) (C : P → σ),
    (∀ w, ∃ v, A.DecC C (lossyPat a b w L) a v ∧ A.DecC C (lossyPat a b w L) b v) →
    ∀ w w' v, A.DecC C (lossyPat a b w L) a v → A.DecC C (lossyPat a b w' L) a v := by
  intro L
  induction L with
  | zero =>
    intro C _ w w' v h
    rwa [lossyPat_zero a b w' w]
  | succ L ih =>
    intro C hagree
    -- the configuration after the first round with letter `ℓ`
    set N : Lk → P → σ := fun ℓ => next A.step (linkG a b ℓ) C with hN
    have hag : ∀ ℓ u, ∃ v, A.DecC (N ℓ) (lossyPat a b u L) a v ∧
        A.DecC (N ℓ) (lossyPat a b u L) b v := by
      intro ℓ u
      obtain ⟨v, h1, h2⟩ := hagree (Lk.cons ℓ u)
      rw [lossyPat_succ, Alg.decC_pcons] at h1 h2
      exact ⟨v, h1, h2⟩
    have IH : ∀ ℓ u u' v, A.DecC (N ℓ) (lossyPat a b u L) a v →
        A.DecC (N ℓ) (lossyPat a b u' L) a v := fun ℓ => ih (N ℓ) (hag ℓ)
    -- `a` and `b` decide the same values
    have hab' : ∀ ℓ u v, A.DecC (N ℓ) (lossyPat a b u L) a v ↔
        A.DecC (N ℓ) (lossyPat a b u L) b v := by
      intro ℓ u v
      obtain ⟨v', h1, h2⟩ := hag ℓ u
      constructor
      · intro h; exact (h.unique h1) ▸ h2
      · intro h; exact (h.unique h2) ▸ h1
    -- `E ℓ ℓ'`: the value after first letter `ℓ` is the value after first letter `ℓ'`
    let E : Lk → Lk → Prop := fun ℓ ℓ' => ∀ u u' v,
      A.DecC (N ℓ) (lossyPat a b u L) a v → A.DecC (N ℓ') (lossyPat a b u' L) a v
    have Etrans : ∀ {ℓ₁ ℓ₂ ℓ₃}, E ℓ₁ ℓ₂ → E ℓ₂ ℓ₃ → E ℓ₁ ℓ₃ :=
      fun h₁ h₂ u u' v h => h₂ u' u' v (h₁ u u' v h)
    -- `a` cannot distinguish `hearA` from `both` in the first round
    have hNa : N .hearA a = N .both a := by
      refine next_eq_of_agree (fun j => ?_) (fun _ _ => rfl)
      simp only [Hears, linkG, Lk.aH, Lk.bH]
      tauto
    have hNb : N .both b = N .hearB b := by
      refine next_eq_of_agree (fun j => ?_) (fun _ _ => rfl)
      simp only [Hears, linkG, Lk.aH, Lk.bH]
      tauto
    have tA : ∀ v, A.DecC (N .hearA) (lossyPat a b (fun _ => .hearB) L) a v ↔
        A.DecC (N .both) (lossyPat a b (fun _ => .hearB) L) a v := fun v =>
      Alg.decC_congr (conf_agree_deaf (deaf_lossyPat_hearB hab L) (deaf_lossyPat_hearB hab L) hNa)
    have tB : ∀ v, A.DecC (N .both) (lossyPat a b (fun _ => .hearA) L) b v ↔
        A.DecC (N .hearB) (lossyPat a b (fun _ => .hearA) L) b v := fun v =>
      Alg.decC_congr (conf_agree_deaf (deaf_lossyPat_hearA hab L) (deaf_lossyPat_hearA hab L) hNb)
    have E1 : E .hearA .both := fun u u' v h =>
      IH _ _ u' v ((tA v).1 (IH _ u _ v h))
    have E2 : E .both .hearA := fun u u' v h =>
      IH _ _ u' v ((tA v).2 (IH _ u _ v h))
    have E3 : E .both .hearB := fun u u' v h =>
      IH _ _ u' v ((hab' _ _ v).2 ((tB v).1 ((hab' _ _ v).1 (IH _ u _ v h))))
    have E4 : E .hearB .both := fun u u' v h =>
      IH _ _ u' v ((hab' _ _ v).2 ((tB v).2 ((hab' _ _ v).1 (IH _ u _ v h))))
    have Eall : ∀ ℓ ℓ', E ℓ ℓ' := by
      intro ℓ ℓ'
      cases ℓ <;> cases ℓ'
      all_goals first
        | exact IH _
        | exact E1 | exact E2 | exact E3 | exact E4
        | exact Etrans E1 E3 | exact Etrans E4 E2
    intro w w' v h
    rw [lossyPat_succ, Alg.decC_pcons] at h ⊢
    exact Eall _ _ _ _ v h

/-- **Lemma 17, finite-horizon form, inside an arbitrary system.** If `a`, deaf during the whole
run, decides `va`, and `b`, deaf during the whole run, decides `vb ≠ va`, and `a` and `b` decide in
all runs, then for some word of length `L` the processes `a` and `b` decide different values. -/
theorem exists_lossy_disagree (hab : a ≠ b) (L : ℕ) (C : P → σ) {va vb : V} (hne : va ≠ vb)
    (ha : A.DecC C (lossyPat a b (fun _ => .hearB) L) a va)
    (hb : A.DecC C (lossyPat a b (fun _ => .hearA) L) b vb)
    (hterm : ∀ w, (∃ v, A.DecC C (lossyPat a b w L) a v) ∧ ∃ v, A.DecC C (lossyPat a b w L) b v) :
    ∃ w v v', v ≠ v' ∧ A.DecC C (lossyPat a b w L) a v ∧ A.DecC C (lossyPat a b w L) b v' := by
  by_contra hcon
  push Not at hcon
  have hagree : ∀ w, ∃ v, A.DecC C (lossyPat a b w L) a v ∧ A.DecC C (lossyPat a b w L) b v := by
    intro w
    obtain ⟨⟨v, hv⟩, ⟨v', hv'⟩⟩ := hterm w
    by_cases hvv : v = v'
    · exact ⟨v, hv, hvv ▸ hv'⟩
    · exact absurd hv' (hcon w v v' hvv hv)
  have ha' := lossy_decC_const A hab L C hagree _ (fun _ => .hearA) va ha
  exact hcon _ va vb hne ha' hb

end Core

/-! ### Lemma 17 for the two-process system -/

section Lemma17

variable {V σ : Type}

/-- The message adversary of Lemma 17 on the two processes `0, 1` with a **fixed** switch round:
in every round `t < L` at least one of the messages `0 → 1`, `1 → 0` is delivered, in every round
`t ≥ L` none. (Self-loops are irrelevant: every process always hears itself.) -/
def lossyAdv (L : ℕ) : Set (ℕ → Graph (Fin 2)) :=
  {ρ | (∀ t < L, ρ t 0 1 ∨ ρ t 1 0) ∧ ∀ t, L ≤ t → ¬ ρ t 0 1 ∧ ¬ ρ t 1 0}

/-- The message adversary of Lemma 17 as literally stated: *some* round `r' > 0` (paper rounds are
`1`-indexed; our round index `t` is the paper's round `t + 1`) such that rounds `r < r'` are
lossy-link rounds and rounds `r ≥ r'` have no edges. -/
def lemma17Adv : Set (ℕ → Graph (Fin 2)) :=
  {ρ | ∃ r', 0 < r' ∧ (∀ t, t + 1 < r' → ρ t 0 1 ∨ ρ t 1 0) ∧
    ∀ t, r' ≤ t + 1 → ¬ ρ t 0 1 ∧ ¬ ρ t 1 0}

theorem lossyPat_mem_lossyAdv (w : ℕ → Lk) (L : ℕ) : lossyPat (0 : Fin 2) 1 w L ∈ lossyAdv L := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [lossyPat, linkG, ht, true_and]
    cases w t <;> simp [Lk.aH, Lk.bH]
  · simp [lossyPat, show ¬ t < L by omega]

theorem lossyAdv_subset (L : ℕ) : lossyAdv L ⊆ lemma17Adv :=
  fun _ ⟨h1, h2⟩ => ⟨L + 1, by omega, fun t ht => h1 t (by omega),
    fun t ht => h2 t (by omega)⟩

/-- **Lemma 17 (fixed-horizon form).** For every fixed switch round `L`, no algorithm solves
consensus between two processes connected by a lossy link up to round `L` and disconnected
afterwards (provided there are two different input values). -/
theorem lemma17_fixed (A : Alg (Fin 2) V σ) {v₀ v₁ : V} (hv : v₀ ≠ v₁) (L : ℕ) :
    ¬ A.SolvesConsensus (lossyAdv L) := by
  classical
  intro hA
  let x : Fin 2 → V := ![v₀, v₁]
  have hmem := fun w => lossyPat_mem_lossyAdv w L
  obtain ⟨w, v, v', hvv, h0, h1⟩ := exists_lossy_disagree A (a := (0 : Fin 2)) (b := 1)
    (by decide) L (A.initC x) hv
    (A.decides_own_of_deaf hA x (hmem _) (deaf_lossyPat_hearB (by decide) L))
    (A.decides_own_of_deaf hA x (hmem _) (deaf_lossyPat_hearA (by decide) L))
    (fun w => ⟨(hA x _ (hmem w)).2.2 0, (hA x _ (hmem w)).2.2 1⟩)
  have := (hA x _ (hmem w)).1 {v, v'} (by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩)
  rw [Finset.card_pair hvv] at this
  omega

/-- **Lemma 17** of the paper, as literally stated: consensus is impossible in the two-process
system whose communication graphs are lossy-link rounds up to some round `r'` and empty from
`r'` on. (Literally, this already follows from the runs with `r' = 1`, where both processes are
deaf forever; the substantial statement is `lemma17_fixed`, for every fixed `r'`.) -/
theorem lemma17 (A : Alg (Fin 2) V σ) {v₀ v₁ : V} (hv : v₀ ≠ v₁) :
    ¬ A.SolvesConsensus lemma17Adv :=
  fun hA => lemma17_fixed A hv 0 (hA.mono (lossyAdv_subset 0))

end Lemma17

end Podc.GracefulKSetAgreement
