import Papers.PODC2011.CCvsDSMSeparation.RollForward
import Podc.Foundations.Combinatorics.OutDegreeIndep

/-!
# One round of the construction (proof of Lemma 6.10)

`Inv i τ B` is the invariant `S(i)` of Definition 6.9 (with our constants): `τ` is a regular
history with active set `B`, at most `i` finished processes, and every active process is stable or
has performed at least `i` RMRs. `round` constructs `S(i+1)` from `S(i)` for `i < c`, losing
only `|B| ↦ keep c |B| = ⌊√(|B|/3)⌋/5 − (c² + 3)` active processes.
-/

namespace Podc.CCvsDSMSeparation

open Cslib (exists_indep_of_outdeg fiber_or_image)

variable {N : ℕ} {V Val S : Type*}

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- **Definition 6.9** (the statement `S(i)`), relative to the active set `B`. -/
structure Inv (i : ℕ) (τ : List (Ev N V Val)) (B : Finset (Fin N)) : Prop where
  valid : A.Valid τ
  nosig : signals τ = 0
  reg : A.Regular B τ
  settled : A.Settled B τ
  fin : (par τ \ B).card ≤ i
  prog : ∀ p ∈ B, A.Stable τ p ∨ i ≤ A.rmrOf τ p

lemma advance_append (α : Fin N → List (Ev N V Val)) (e : Fin N → Ev N V Val)
    (ρ : List (Ev N V Val)) (L₁ L₂ : List (Fin N)) :
    A.advance α e ρ (L₁ ++ L₂) = A.advance α e (A.advance α e ρ L₁) L₂ := by
  induction L₁ generalizing ρ with
  | nil => rfl
  | cons p L₁ ih => simp only [List.cons_append, advance_cons, ih]

lemma NextData.mono {τ : List (Ev N V Val)} {T T' : Finset (Fin N)}
    {α : Fin N → List (Ev N V Val)} {e : Fin N → Ev N V Val} (h : A.NextData τ T α e)
    (hT : T' ⊆ T) : A.NextData τ T' α e :=
  ⟨fun p hp => h.solo p (hT hp), fun p hp => h.valid p (hT hp), fun p hp => h.loc p (hT hp),
    fun p hp => h.remote p (hT hp)⟩

/-- Keep only the processes `T ⊆ B` and let them perform their next RMRs (in the order `L`). -/
lemma select_base {i : ℕ} {τ : List (Ev N V Val)} {B T : Finset (Fin N)}
    {α : Fin N → List (Ev N V Val)} {e : Fin N → Ev N V Val}
    (hI : A.Inv i τ B) (hTB : T ⊆ B) (hd : A.NextData τ T α e)
    (hprogT : ∀ p ∈ T, i ≤ A.rmrOf τ p)
    (hind : ∀ p ∈ T, ∀ v, (e p).op.var = some v → A.home v ∉ T)
    (hwr : ∀ p ∈ T, ∀ v q, (e p).op.var = some v → writer v τ = some q → q ∈ T → q = p)
    (hRW : ∀ p ∈ T, ∀ q ∈ T, ∀ v x, (e p).op = .read v x → ¬ (e q).Writes v)
    (L : List (Fin N)) (hL : L.Nodup) (hLT : ∀ p, p ∈ L ↔ p ∈ T) :
    A.Valid (A.advance α e (erase (B \ T) τ) L) ∧
    signals (A.advance α e (erase (B \ T) τ) L) = 0 ∧
    NoSee T (A.advance α e (erase (B \ T) τ) L) ∧
    A.NoTouch T (A.advance α e (erase (B \ T) τ) L) ∧
    A.Settled T (A.advance α e (erase (B \ T) τ) L) ∧
    par (A.advance α e (erase (B \ T) τ) L) \ T ⊆ par τ \ B ∧
    (∀ p ∈ T, i + 1 ≤ A.rmrOf (A.advance α e (erase (B \ T) τ) L) p) ∧
    (∀ v, (∀ p ∈ T, ¬ (e p).Writes v) → SoleW T (A.advance α e (erase (B \ T) τ) L) v) ∧
    (∀ v p, p ∈ T → (e p).Writes v → (∀ q ∈ T, q ≠ p → ¬ (e q).Writes v) →
      SoleW T (A.advance α e (erase (B \ T) τ) L) v) := by
  classical
  set τ₁ := erase (B \ T) τ with hτ₁
  have hBT : B \ (B \ T) = T := Finset.sdiff_sdiff_eq_self hTB
  have hsub : B \ T ⊆ B := Finset.sdiff_subset
  have hv₁ : A.Valid τ₁ := hI.reg.valid_erase A hI.valid hsub
  have hreg₁ : A.Regular T τ₁ := by have := hI.reg.erase A hsub; rwa [hBT] at this
  have hset₁ : A.Settled T τ₁ := by have := Settled.erase A hI.settled (E := B \ T); rwa [hBT] at this
  have hnotin : ∀ q ∈ T, q ∉ B \ T := fun q hq h' => (Finset.mem_sdiff.1 h').2 hq
  have hpj : ∀ q ∈ T, proj τ₁ q = proj τ q := fun q hq => proj_erase_of_not_mem τ (hnotin q hq)
  have hmem : ∀ q ∈ T, ∀ v, A.home v = q → A.memVal τ₁ v = A.memVal τ v := by
    intro q hq v hv
    refine A.memVal_erase fun w hw hwBT => ?_
    have := A.okW_writer_of_home hI.reg.noTouch (hTB hq) hv w hw (hsub hwBT)
    subst this; exact hnotin w hq hwBT
  have hok : ∀ p ∈ T, ∀ v, (e p).op.var = some v → OkW T p (writer v τ₁) := by
    intro p hp v hv w hw hwT
    have := (hI.reg.sole v).okW_erase hsub w hw
    exact hwr p hp v w hv (this.2 (hTB hwT)) hwT
  obtain ⟨s1, ⟨σ, hσ, hshape⟩, s3⟩ := A.advance_spec hd hind L τ₁ hL (fun p hp => (hLT p).1 hp)
    hv₁ (fun q hq => hpj q ((hLT q).1 hq)) (fun q hq => hmem q ((hLT q).1 hq))
  obtain ⟨r1, r2, r3, r4⟩ := A.advance_regular hd hind L τ₁ hL (fun p hp => (hLT p).1 hp)
    hreg₁.noSee hreg₁.noTouch
    (fun p hp v x hx => hok p ((hLT p).1 hp) v (by simp [hx, Op.var]))
    (fun p hp q hq => hRW p ((hLT p).1 hp) q ((hLT q).1 hq))
  have hσT : ∀ e' ∈ σ, e'.p ∈ T := fun e' he' => (hLT _).1 (hshape e' he').1
  refine ⟨s1, ?_, r1, r2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ, signals_append, signals_eq_zero (fun e' he' => (hshape e' he').2.1)]
    exact Nat.le_zero.1 ((signals_erase_le _ τ).trans (by rw [hI.nosig]))
  · rw [hσ]; exact Settled.append_active A hset₁ hσT
  · intro q hq
    rw [Finset.mem_sdiff, hσ, par_append, Finset.mem_union, par_erase] at hq
    rcases hq.1 with h1 | h1
    · rw [Finset.mem_sdiff] at h1
      exact Finset.mem_sdiff.2 ⟨h1.1, fun hqB => h1.2 (Finset.mem_sdiff.2 ⟨hqB, hq.2⟩)⟩
    · exact absurd (par_subset_of_forall hσT h1) hq.2
  · intro p hp
    rw [s3 p ((hLT p).2 hp), A.rmrOf_eq_of_proj (hpj p hp)]
    exact Nat.add_le_add_right (hprogT p hp) 1
  · intro v hno
    exact r3 v (fun p hp => hno p ((hLT p).1 hp)) (hreg₁.sole v)
  · intro v p hp hw huniq
    exact r4 v p ((hLT p).2 hp) hw (fun q hq hqp => huniq q ((hLT q).1 hq) hqp)
      (hok p hp v hw.var) (hreg₁.sole v)

/-- The processes another process conflicts with in its next RMR: the owner of the accessed
variable and its last writer. -/
noncomputable def conflicts (τ : List (Ev N V Val)) (e : Fin N → Ev N V Val) (p : Fin N) :
    Finset (Fin N) :=
  ((e p).op.var.map A.home).toFinset ∪ (((e p).op.var).bind fun v => writer v τ).toFinset

lemma card_conflicts_le (τ : List (Ev N V Val)) (e : Fin N → Ev N V Val) (p : Fin N) :
    (A.conflicts τ e p).card ≤ 2 := by
  unfold conflicts
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ∀ o : Option (Fin N), o.toFinset.card ≤ 1 := by
    intro o; cases o <;> simp
  have := h1 ((e p).op.var.map A.home); have := h1 (((e p).op.var).bind fun v => writer v τ)
  omega

/-- A round in which the processes `X` (pairwise non-conflicting after the independent-set
selection) perform their next RMRs: reads, or writes to distinct variables. -/
lemma round_indep {i : ℕ} {τ : List (Ev N V Val)} {B X : Finset (Fin N)}
    {α : Fin N → List (Ev N V Val)} {e : Fin N → Ev N V Val}
    (hI : A.Inv i τ B) (hXB : X ⊆ B) (hd : A.NextData τ X α e)
    (hprog : ∀ p ∈ X, i ≤ A.rmrOf τ p)
    (hX : ∀ p ∈ X, ∀ q ∈ X, ∀ v, (e p).Writes v → (e q).op.var = some v → q = p) :
    ∃ τ' T, A.Inv (i + 1) τ' T ∧ X.card ≤ 5 * T.card := by
  classical
  obtain ⟨T, hTX, hcard, hindep⟩ := exists_indep_of_outdeg (A.conflicts τ e) 2 X
    (fun x _ => A.card_conflicts_le τ e x)
  have hdT := NextData.mono A hd hTX
  have hind : ∀ p ∈ T, ∀ v, (e p).op.var = some v → A.home v ∉ T := by
    intro p hp v hv hvT
    obtain ⟨u, hu, hne⟩ := hd.var_e (hTX hp)
    rw [hv] at hu; cases hu
    exact hne (hindep p hp _ hvT (by simp [conflicts, hv]))
  have hwr : ∀ p ∈ T, ∀ v q, (e p).op.var = some v → writer v τ = some q → q ∈ T → q = p := by
    intro p hp v q hv hw hq
    exact hindep p hp q hq (by simp [conflicts, hv, hw])
  have hRW : ∀ p ∈ T, ∀ q ∈ T, ∀ v x, (e p).op = .read v x → ¬ (e q).Writes v := by
    intro p hp q hq v x hx hw
    have := hX q (hTX hq) p (hTX hp) v hw (by simp [hx, Op.var])
    subst this
    obtain ⟨y, hy⟩ := hw; rw [hx] at hy; cases hy
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := A.select_base hI (hTX.trans hXB) hdT
    (fun p hp => hprog p (hTX hp)) hind hwr hRW T.toList (Finset.nodup_toList T)
    (fun p => Finset.mem_toList)
  refine ⟨_, T, ⟨s1, s2, ⟨s3, s4, fun v => ?_⟩, s5, ?_, fun p hp => Or.inr (s7 p hp)⟩, by omega⟩
  · by_cases hw : ∃ p ∈ T, (e p).Writes v
    · obtain ⟨p, hp, hpw⟩ := hw
      refine s9 v p hp hpw fun q hq hqp hqw => hqp ?_
      exact hX p (hTX hp) q (hTX hq) v hpw hqw.var
    · push Not at hw; exact s8 v hw
  · exact (Finset.card_le_card s6).trans (hI.fin.trans (Nat.le_succ _))

/-- The roll-forward round: the processes `X` all write the same variable `v₀` in their next
RMRs. -/
lemma round_rollforward {c K i : ℕ} (hT : A.SoloTerminating) (hb : A.AmortBound c K)
    (hcK : c ≤ K) (hic : i < c) {τ : List (Ev N V Val)} {B X : Finset (Fin N)}
    {α : Fin N → List (Ev N V Val)} {e : Fin N → Ev N V Val}
    (hI : A.Inv i τ B) (hXB : X ⊆ B) (hd : A.NextData τ X α e)
    (hprog : ∀ p ∈ X, i ≤ A.rmrOf τ p) {v₀ : V}
    (hX : ∀ p ∈ X, (e p).Writes v₀) (hXc : c * c + 3 < X.card) :
    ∃ τ' B', A.Inv (i + 1) τ' B' ∧ X.card ≤ B'.card + (c * c + 3) := by
  classical
  -- drop the owner of `v₀` and the last writer of `v₀`
  set W := (X.erase (A.home v₀)).filter fun q => writer v₀ τ ≠ some q with hW
  have hWX : W ⊆ X := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hWcard : X.card ≤ W.card + 2 := by
    have h1 : X.card ≤ (X.erase (A.home v₀)).card + 1 := by
      have := Finset.pred_card_le_card_erase (s := X) (a := A.home v₀); omega
    have h2 : (X.erase (A.home v₀)).card ≤ W.card + 1 := by
      have := Finset.card_filter_add_card_filter_not (s := X.erase (A.home v₀))
        (p := fun q => writer v₀ τ ≠ some q)
      have h3 : ((X.erase (A.home v₀)).filter fun q => ¬ writer v₀ τ ≠ some q).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        simp only [Finset.mem_filter, not_not] at ha hb
        rw [ha.2] at hb; exact Option.some.inj hb.2
      rw [← hW] at this; omega
    omega
  obtain ⟨r, hrW⟩ : W.Nonempty := Finset.card_pos.1 (by omega)
  have hdW := NextData.mono A hd hWX
  have hvar : ∀ p ∈ X, (e p).op.var = some v₀ := fun p hp => (hX p hp).var
  have hind : ∀ p ∈ W, ∀ v, (e p).op.var = some v → A.home v ∉ W := by
    intro p hp v hv hvW
    rw [hvar p (hWX hp)] at hv; cases hv
    simp [hW] at hvW
  have hwr : ∀ p ∈ W, ∀ v q, (e p).op.var = some v → writer v τ = some q → q ∈ W → q = p := by
    intro p hp v q hv hw hq
    rw [hvar p (hWX hp)] at hv; cases hv
    simp [hW, hw] at hq
  have hRW : ∀ p ∈ W, ∀ q ∈ W, ∀ v x, (e p).op = .read v x → ¬ (e q).Writes v := by
    intro p hp q hq v x hx _
    obtain ⟨y, hy⟩ := hX p (hWX hp); rw [hx] at hy; cases hy
  set L₀ := (W.erase r).toList with hL₀
  have hL : (L₀ ++ [r]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, List.nodup_singleton r, ?_⟩
    intro a ha b hb hab; simp at hb; subst hb; subst hab; simp [hL₀] at ha
  have hLW : ∀ p, p ∈ L₀ ++ [r] ↔ p ∈ W := by
    intro p; simp only [List.mem_append, hL₀, Finset.mem_toList, Finset.mem_erase,
      List.mem_singleton]
    constructor
    · rintro (⟨-, h⟩ | rfl) <;> assumption
    · intro h; by_cases hpr : p = r
      · exact Or.inr hpr
      · exact Or.inl ⟨hpr, h⟩
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, -⟩ := A.select_base hI (hWX.trans hXB) hdW
    (fun p hp => hprog p (hWX hp)) hind hwr hRW (L₀ ++ [r]) hL hLW
  set τ₁ := erase (B \ W) τ
  set ρ := A.advance α e τ₁ (L₀ ++ [r]) with hρ
  have hρ' : ρ = A.advance α e τ₁ L₀ ++ α r ++
      [A.stepAt e (A.advance α e τ₁ L₀ ++ α r) r] := by
    rw [hρ, advance_append, advance_cons]; rfl
  have hwrite_r : (A.stepAt e (A.advance α e τ₁ L₀ ++ α r) r).Writes v₀ := by
    rw [stepAt_writes_iff]; exact hX r (hWX hrW)
  have hwρ : writer v₀ ρ = some r := by
    rw [hρ', writer_snoc]; simp only [hwrite_r, ↓reduceIte]; rfl
  have hbusy : ∃ o, A.Busy ρ r o := by
    have := A.busy_snoc_access (ρ := A.advance α e τ₁ L₀ ++ α r) (by rw [← hρ']; exact s1)
      (by obtain ⟨x, hx⟩ := hwrite_r; rw [hx]; rfl)
    rw [← hρ'] at this; exact this
  obtain ⟨o, hbusy⟩ := hbusy
  set B' := W.erase r with hB'
  have hrB' : r ∉ B' := by simp [hB']
  have hins : insert r B' = W := Finset.insert_erase hrW
  have hreg' : A.Regular B' ρ := by
    refine ⟨s3.mono (Finset.erase_subset _ _), NoTouch.mono A s4 (Finset.erase_subset _ _),
      fun v => ?_⟩
    by_cases hv : v = v₀
    · subst hv
      exact SoleW.of_writer_not_mem fun q hq hqB' => by
        rw [hwρ] at hq; cases hq; exact hrB' hqB'
    · refine (s8 v fun p hp hw => hv ?_).mono (Finset.erase_subset _ _)
      have := hw.var; rw [hvar p (hWX hp)] at this; cases this; rfl
  have hpar : (par ρ \ B') ∪ {r} ⊆ (par τ \ B) ∪ {r} := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, hB',
      Finset.mem_erase] at hq ⊢
    rcases hq with ⟨h1, h2⟩ | h
    · by_cases hqr : q = r
      · exact Or.inr hqr
      · left
        have : q ∉ W := fun h' => h2 ⟨hqr, h'⟩
        exact Finset.mem_sdiff.1 (s6 (Finset.mem_sdiff.2 ⟨h1, this⟩))
    · exact Or.inr h
  have hparcard : ((par ρ \ B') ∪ {r}).card ≤ i + 1 :=
    (Finset.card_le_card hpar).trans ((Finset.card_union_le _ _).trans (by
      simp only [Finset.card_singleton]; exact Nat.add_le_add_right hI.fin 1))
  obtain ⟨E, hEB, hEcard, σ, hσr, t1, t2, t3, t4, t5⟩ := A.roll_forward hT hb s1 s2 hreg'
    (by rw [hins]; exact s4) (by rw [hins]; exact s5) hrB' hbusy (hparcard.trans (by omega))
  refine ⟨erase E ρ ++ σ, B' \ E, ⟨t1, t2, t3, t4, ?_, ?_⟩, ?_⟩
  · exact (Finset.card_le_card (t5.trans hpar)).trans
      ((Finset.card_union_le _ _).trans (by
        simp only [Finset.card_singleton]; have := hI.fin; omega))
  · intro p hp
    right
    have hpE : p ∉ E := (Finset.mem_sdiff.1 hp).2
    have hpB' := (Finset.mem_sdiff.1 hp).1
    have hpW : p ∈ W := Finset.mem_of_mem_erase hpB'
    have hpr : p ≠ r := Finset.ne_of_mem_erase hpB'
    rw [A.rmrOf_append, A.rmrOf_eq_zero_of_forall (p := p) (fun e' he' heq =>
      hpr (heq.symm.trans (hσr e' he'))), Nat.add_zero,
      A.rmrOf_eq_of_proj (proj_erase_of_not_mem ρ hpE)]
    exact s7 p hpW
  · have h1 : (B' \ E).card + E.card ≥ B'.card := by
      have := Finset.card_sdiff_add_card_inter B' E
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := B') (s₂ := E)); omega
    have h2 : B'.card + 1 = W.card := Finset.card_erase_add_one hrW
    have h3 : E.card ≤ c * c :=
      hEcard.trans (Nat.mul_le_mul_left _ (hparcard.trans (by omega)))
    omega

/-- The number of active processes guaranteed to survive a round that starts with `n`. -/
def keep (c n : ℕ) : ℕ := Nat.sqrt (n / 3) / 5 - (c * c + 3)

lemma keep_mono (c : ℕ) {m n : ℕ} (h : m ≤ n) : keep c m ≤ keep c n := by
  unfold keep
  have := Nat.sqrt_le_sqrt (Nat.div_le_div_right (c := 3) h)
  have := Nat.div_le_div_right (c := 5) this
  omega

/-- **One round of the proof of Lemma 6.10**: `S(i)` implies `S(i+1)` (for `i < c`). -/
lemma round {c K i : ℕ} (hT : A.SoloTerminating) (hb : A.AmortBound c K) (hcK : c ≤ K)
    (hic : i < c) {τ : List (Ev N V Val)} {B : Finset (Fin N)} (hI : A.Inv i τ B) :
    ∃ τ' B', A.Inv (i + 1) τ' B' ∧ keep c B.card ≤ B'.card := by
  classical
  set n := B.card with hn
  have hfin := hI.fin
  -- degenerate case: erase everybody
  by_cases hg : keep c n = 0
  · refine ⟨erase B τ, ∅, ⟨hI.reg.valid_erase A hI.valid subset_rfl, ?_, ?_, ?_, ?_, by simp⟩,
      by simp [hg]⟩
    · exact Nat.le_zero.1 ((signals_erase_le B τ).trans (by rw [hI.nosig]))
    · have := hI.reg.erase A (subset_rfl : B ⊆ B); rwa [Finset.sdiff_self] at this
    · have := Settled.erase A hI.settled (E := B); rwa [Finset.sdiff_self] at this
    · rw [Finset.sdiff_empty, par_erase]; omega
  set s := Nat.sqrt (n / 3) with hs
  have hs3 : s ≤ n / 3 := Nat.sqrt_le_self _
  have hkeep : keep c n = s / 5 - (c * c + 3) := rfl
  set Sb := B.filter (A.Stable τ) with hSb
  set U := B.filter (fun p => ¬ A.Stable τ p) with hU
  have hSU : Sb.card + U.card = n := Finset.card_filter_add_card_filter_not _
  have hUB : U ⊆ B := Finset.filter_subset _ _
  by_cases h1 : n ≤ 3 * Sb.card
  · -- many stable processes: erase the unstable ones
    have hBU : B \ U = Sb := by
      ext p; simp only [hSb, hU, Finset.mem_sdiff, Finset.mem_filter]; tauto
    refine ⟨erase U τ, Sb, ⟨hI.reg.valid_erase A hI.valid hUB, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact Nat.le_zero.1 ((signals_erase_le U τ).trans (by rw [hI.nosig]))
    · have := hI.reg.erase A hUB; rwa [hBU] at this
    · have := Settled.erase A hI.settled (E := U); rwa [hBU] at this
    · rw [← hBU, par_erase]
      refine (Finset.card_le_card ?_).trans (hfin.trans (Nat.le_succ _))
      intro q hq
      simp only [Finset.mem_sdiff] at hq ⊢
      exact ⟨hq.1.1, fun hqB => hq.2 ⟨hqB, hq.1.2⟩⟩
    · intro p hp
      left
      have hpB : p ∈ B := (Finset.mem_filter.1 hp).1
      have hpU : p ∉ U := fun h' => (Finset.mem_filter.1 h').2 (Finset.mem_filter.1 hp).2
      refine A.stable_congr hI.valid (proj_erase_of_not_mem τ hpU) (fun v hv => ?_)
        (Finset.mem_filter.1 hp).2
      refine A.memVal_erase fun w hw hwU => ?_
      have := A.okW_writer_of_home hI.reg.noTouch hpB hv w hw (hUB hwU)
      subst this; exact hpU hwU
    · omega
  -- many unstable processes
  obtain ⟨p0, hp0⟩ : U.Nonempty := Finset.card_pos.1 (by omega)
  have : Nonempty (Ev N V Val) := ⟨⟨p0, .inv .poll⟩⟩
  have hex : ∀ p ∈ U, ∃ (α : List (Ev N V Val)) (e : Ev N V Val), SoloPoll p (α ++ [e]) ∧
      A.Valid (τ ++ α ++ [e]) ∧ A.rmr α = 0 ∧ e.remote A.home = true :=
    fun p hp => A.exists_next_rmr (Finset.mem_filter.1 hp).2
  choose! α e hαe using hex
  have hd : A.NextData τ U α e := ⟨fun p hp => (hαe p hp).1, fun p hp => (hαe p hp).2.1,
    fun p hp => (hαe p hp).2.2.1, fun p hp => (hαe p hp).2.2.2⟩
  have hprog : ∀ p ∈ U, i ≤ A.rmrOf τ p := fun p hp =>
    (hI.prog p (Finset.mem_filter.1 hp).1).resolve_left (Finset.mem_filter.1 hp).2
  set Ur := U.filter (fun p => ∃ v x, (e p).op = .read v x) with hUr
  set Uw := U.filter (fun p => ¬ ∃ v x, (e p).op = .read v x) with hUw
  have hRWc : Ur.card + Uw.card = U.card := Finset.card_filter_add_card_filter_not _
  have hUrU : Ur ⊆ U := Finset.filter_subset _ _
  have hUwU : Uw ⊆ U := Finset.filter_subset _ _
  have hwrite : ∀ p ∈ Uw, ∃ v x, (e p).op = .write v x := by
    intro p hp
    obtain ⟨v, hv, -⟩ := hd.var_e (hUwU hp)
    have hnr := (Finset.mem_filter.1 hp).2
    rcases hop : (e p).op with o | ⟨u, x⟩ | ⟨u, x⟩ | b <;> rw [hop] at hv <;>
      simp [Op.var] at hv
    · exact absurd ⟨u, x, hop⟩ hnr
    · exact ⟨u, x, rfl⟩
  by_cases h2 : Uw.card ≤ Ur.card
  · -- readers
    obtain ⟨τ', T, hI', hT'⟩ := A.round_indep hI (hUrU.trans hUB) (NextData.mono A hd hUrU)
      (fun p hp => hprog p (hUrU hp)) (by
        intro p hp q _ v hw _
        obtain ⟨v', x, hx⟩ := (Finset.mem_filter.1 hp).2
        obtain ⟨y, hy⟩ := hw; rw [hx] at hy; cases hy)
    refine ⟨τ', T, hI', ?_⟩
    omega
  · -- writers
    have h3 : n ≤ 3 * Uw.card := by omega
    set t := Nat.sqrt Uw.card with ht
    have htt : t * t ≤ Uw.card := Nat.sqrt_le _
    have hst : s ≤ t := Nat.sqrt_le_sqrt (by omega)
    rcases fiber_or_image Uw (fun p => (e p).op.var) t htt with ⟨b, hb'⟩ | himg
    · -- roll-forward case
      set F := Uw.filter fun p => (e p).op.var = b with hF
      have hFUw : F ⊆ Uw := Finset.filter_subset _ _
      obtain ⟨p1, hp1⟩ : F.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v₀, x₀, hx₀⟩ := hwrite p1 (hFUw hp1)
      have hb0 : b = some v₀ := by
        rw [← (Finset.mem_filter.1 hp1).2, hx₀]; rfl
      have hXw : ∀ p ∈ F, (e p).Writes v₀ := by
        intro p hp
        obtain ⟨v, x, hx⟩ := hwrite p (hFUw hp)
        have := (Finset.mem_filter.1 hp).2
        rw [hx, hb0] at this; simp [Op.var] at this; subst this
        exact ⟨x, hx⟩
      obtain ⟨τ', B', hI', hB'⟩ := A.round_rollforward hT hb hcK hic hI
        ((hFUw.trans hUwU).trans hUB) (NextData.mono A hd (hFUw.trans hUwU))
        (fun p hp => hprog p (hUwU (hFUw hp))) hXw (by omega)
      exact ⟨τ', B', hI', by omega⟩
    · -- erasing case: one writer per variable
      have hpick : ∀ b ∈ Uw.image (fun p => (e p).op.var), ∃ p ∈ Uw, (e p).op.var = b :=
        fun b hb => Finset.mem_image.1 hb
      have : Nonempty (Fin N) := ⟨p0⟩
      choose! pick hpickUw hpickv using hpick
      set W' := (Uw.image fun p => (e p).op.var).image pick with hW'
      have hW'Uw : W' ⊆ Uw := by
        intro p hp; obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp; exact hpickUw b hb
      have hW'card : W'.card = (Uw.image fun p => (e p).op.var).card := by
        refine Finset.card_image_of_injOn fun b₁ hb₁ b₂ hb₂ h => ?_
        rw [← hpickv b₁ hb₁, ← hpickv b₂ hb₂, h]
      obtain ⟨τ', T, hI', hT'⟩ := A.round_indep hI ((hW'Uw.trans hUwU).trans hUB)
        (NextData.mono A hd (hW'Uw.trans hUwU)) (fun p hp => hprog p (hUwU (hW'Uw hp))) (by
          intro p hp q hq v hw hqv
          obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_image.1 hp
          obtain ⟨b₂, hb₂, rfl⟩ := Finset.mem_image.1 hq
          have e1 := hpickv b₁ hb₁; have e2 := hpickv b₂ hb₂
          rw [hw.var] at e1; rw [hqv] at e2
          rw [← e1, ← e2])
      exact ⟨τ', T, hI', by omega⟩

end Algorithm

end Podc.CCvsDSMSeparation
