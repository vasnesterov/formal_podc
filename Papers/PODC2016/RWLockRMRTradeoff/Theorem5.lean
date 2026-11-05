import Papers.PODC2016.RWLockRMRTradeoff.E2
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Lemma 4, Theorem 5 and Corollary 6

* `lemma4`: if a writer is in the CS at the end of an execution `C₁ ↪ E` that starts with reader
  `R` in the CS, then the writer is `C₁ ↪ E`-aware of `R`.
* `theorem5`: for every reader-writer lock for `n` readers and one writer from read/write/CAS
  registers in the CC model (write-back, write-through, or any `CacheModel`): if the writer's entry
  section incurs at most `Wb` RMRs and the readers' exit section at most `Rb` RMRs, then
  `n ≤ Wb · 3^Rb`; i.e. `Rb ≥ log₃ (n / Wb)`.
* `theorem5_asymptotic`: the paper's form `Wb(n) = O(f(n)) ⇒ Rb(n) = Ω(log (n / f(n)))`, stated
  with explicit constants.
* `corollary6`: `log₃ n ≤ Wb + Rb`, hence `max(Wb, Rb) = Ω(log n)`.
-/

namespace Podc.RWLockRMRTradeoff

open Cslib.SharedMemory

variable {n m : ℕ} {ι V L : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : RWAlg n m ι V v₀ L} {cm : CacheModel (Proc n m) ι}

/-- **Lemma 4.** Let `C₁` (reached by `α₁`) be a configuration in which reader `i` is in the CS,
and let `C₁ ↪ E` be a fragment after which writer `w` is in the CS. Then `w` is `C₁ ↪ E`-aware of
reader `i`. -/
theorem lemma4 (hME : RWMutualExclusion I) {α₁ : List (Label (Proc n m) mutexObj)}
    {X₁ Y : Ext I cm} {E : List (Label (Proc n m) mutexObj)}
    (hX₁ : xrun (Ext.init I cm) α₁ = some X₁) (hE : xrun X₁.fresh E = some Y)
    (hwf : ClientWF (α₁ ++ E)) (i : Fin n) (hcs : regionOf α₁ (.inl i) = some .cs) (w : Fin m)
    (hw : InCS (α₁ ++ E) (.inr w)) : (Sum.inl i : Proc n m) ∈ Y.kn.aw (.inr w) := by
  classical
  by_contra hnot
  obtain ⟨Y', hY', -⟩ := lemma3 (p := .inl i) (X := X₁.fresh) rfl hE
  set E' := eraseFrom (.inl i) X₁.fresh E
  have hrun : I.run (α₁ ++ E') = some Y'.cfg := by
    rw [Impl.run_append_of_eq I (run_of_xrun hX₁)]
    have := xrun_cfg hY'; exact this
  have hreg : ∀ q, regionOf (α₁ ++ E') q =
      regFold (regionOf α₁ q) (E'.filter fun ℓ => decide (ℓ.proc = q)) q := fun q => by
    rw [regionOf_append, regFold_filter]
  have hwf' : ClientWF (α₁ ++ E') := by
    intro q
    rw [hreg q]
    apply regFold_ne_none_of_prefix (eraseFrom_filter_prefix hE q)
    rw [regFold_filter, ← regionOf_append]; exact hwf q
  have hcsw : InCS (α₁ ++ E') (.inr w) := by
    unfold InCS at hw ⊢
    rw [hreg, eraseFrom_filter_of_not_mem hE _ hnot, regFold_filter, ← regionOf_append]
    exact hw
  have hcsi : InCS (α₁ ++ E') (.inl i) := by
    unfold InCS
    rw [regionOf_append, regFold_of_forall_ne _ _ _ (eraseFrom_proc_ne KInv.init hE), hcs]
  have := hME _ ⟨_, hrun⟩ hwf' w _ hcsw hcsi
  cases this

/-- While only `p` takes steps, each expanding step of `p` adds at most `K` processes to its
awareness set, where `K` bounds the familiarity sets at the start. -/
theorem aw_solo_bound {X Y : Ext I cm} {β : List (Label (Proc n m) mutexObj)} (p : Proc n m)
    (hβ : ∀ ℓ ∈ β, ℓ.proc = p) {K : ℕ} (hK : ∀ i, (X.kn.fam i).card ≤ K)
    (h : xrun X β = some Y) :
    (Y.kn.aw p).card ≤ (X.kn.aw p).card + K * xcount (ExpBy p) X β := by
  classical
  -- invariant: familiarity sets stay below the initial ones plus `AW(p)`
  suffices H : ∀ (Z : Ext I cm), (∀ i, Z.kn.fam i ⊆ X.kn.fam i ∪ Z.kn.aw p) →
      ∀ β' Y', (∀ ℓ ∈ β', ℓ.proc = p) → xrun Z β' = some Y' →
      (Y'.kn.aw p).card ≤ (Z.kn.aw p).card + K * xcount (ExpBy p) Z β' by
    exact H X (fun i => Finset.subset_union_left) β Y hβ h
  intro Z hZ β'
  induction β' generalizing Z with
  | nil => intro Y' _ h; simp only [xrun_nil, Option.some.injEq] at h; subst h; simp [xcount]
  | cons ℓ β' ih =>
    intro Y' hβ' h
    simp only [xrun_cons] at h
    cases hs : xstep Z ℓ with
    | none => simp [hs] at h
    | some Z' =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2, -⟩ := xstep_eq_some.1 hs
      have hp : ℓ.proc = p := hβ' ℓ List.mem_cons_self
      -- effect of the step
      have hZ' : (∀ i, Z'.kn.fam i ⊆ X.kn.fam i ∪ Z'.kn.aw p) ∧
          (Z'.kn.aw p).card ≤ (Z.kn.aw p).card + K * (if ExpBy p Z ℓ then 1 else 0) := by
        have haw := (kstep_aw I Z.cfg Z.kn ℓ p).1
        rw [← h2] at haw
        cases ℓ with
        | inv q o =>
          have hk : Z'.kn = Z.kn := by rw [h2]; rfl
          rw [hk]; exact ⟨hZ, by omega⟩
        | ret q r =>
          have hk : Z'.kn = Z.kn := by rw [h2]; rfl
          rw [hk]; exact ⟨hZ, by omega⟩
        | tau q =>
          simp only [Label.proc] at hp; subst hp
          obtain ⟨-, -, i₀, o, k, hact, -, -⟩ := Impl.step_tau h1
          have hfam_old : ∀ j, Z.kn.fam j ⊆ X.kn.fam j ∪ Z'.kn.aw q := fun j =>
            (hZ j).trans (Finset.union_subset_union subset_rfl haw)
          -- a reading step adds `F(v) ⊆ F₀(v) ∪ AW(q)`
          have hread : ∀ (hr : (kstep I Z.cfg Z.kn (.tau q)).aw q = Z.kn.aw q ∪ Z.kn.fam i₀),
              ((kstep I Z.cfg Z.kn (.tau q)).aw q).card ≤
                (Z.kn.aw q).card + K * (if ExpBy q Z (.tau q) then 1 else 0) := by
            intro hr
            rw [hr]
            split_ifs with hE
            · have : Z.kn.aw q ∪ Z.kn.fam i₀ ⊆ Z.kn.aw q ∪ X.kn.fam i₀ := by
                intro x hx
                rcases Finset.mem_union.1 hx with hx | hx
                · exact Finset.mem_union_left _ hx
                · rcases Finset.mem_union.1 (hZ i₀ hx) with h' | h'
                  · exact Finset.mem_union_right _ h'
                  · exact Finset.mem_union_left _ h'
              have := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
              have := hK i₀; omega
            · have hsub : Z.kn.fam i₀ ⊆ Z.kn.aw q := by
                by_contra hn
                apply hE
                refine ⟨rfl, ⟨q, ?_⟩⟩
                rw [hr]
                apply Finset.card_lt_card
                refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h => hn ?_⟩
                rw [h]; exact Finset.subset_union_right
              simp [Finset.union_eq_left.2 hsub]
          cases o with
          | read =>
            have e : Z'.kn = { Z.kn with aw := Function.update Z.kn.aw q (Z.kn.aw q ∪ Z.kn.fam i₀) } := by
              rw [h2, kstep_read I hact]
            refine ⟨fun j => by rw [show Z'.kn.fam j = Z.kn.fam j by rw [e]]; exact hfam_old j, ?_⟩
            rw [h2]
            exact hread (by rw [kstep_read I hact]; simp)
          | write v =>
            have hcard : Z'.kn.aw q = Z.kn.aw q := by
              rw [h2, kstep_write I hact]; split_ifs <;> rfl
            refine ⟨fun j => ?_, by rw [hcard]; omega⟩
            rw [hcard, h2, kstep_write I hact]
            by_cases hv : Z.cfg.mem i₀ = v
            · rw [if_pos hv]; exact hZ j
            · rw [if_neg hv]
              by_cases hj : j = i₀
              · subst hj; simp
              · simp only [Function.update_of_ne hj]; exact hZ j
          | cas a b =>
            have hfam' : ∀ j, (kstep I Z.cfg Z.kn (.tau q)).fam j ⊆
                X.kn.fam j ∪ (kstep I Z.cfg Z.kn (.tau q)).aw q := by
              intro j
              rw [kstep_cas I hact]
              simp only [Function.update_self]
              split_ifs with hc
              · by_cases hj : j = i₀
                · subst hj; simp
                · simp only [Function.update_of_ne hj]
                  exact (hZ j).trans (Finset.union_subset_union subset_rfl
                    Finset.subset_union_left)
              · exact (hZ j).trans (Finset.union_subset_union subset_rfl
                  Finset.subset_union_left)
            rw [h2]
            exact ⟨hfam', hread (by rw [kstep_cas I hact]; simp)⟩
      have := ih Z' hZ'.1 Y' (fun ℓ' h' => hβ' ℓ' (List.mem_cons_of_mem _ h')) h
      simp only [xcount, hs]
      have := hZ'.2
      split_ifs at this ⊢ <;> simp only [Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.zero_add] at * <;> omega

/-- **Theorem 5** (general form: any number `m ≥ 1` of writers, one of which, `w`, is used).
For a reader-writer lock from read/write/CAS registers satisfying Mutual Exclusion, Bounded Exit,
Deadlock Freedom and Concurrent Entering, in any cache-coherent model: if the writers' entry
section incurs at most `Wb` RMRs and the readers' exit section at most `Rb` RMRs, then
`n ≤ Wb · 3^Rb`. -/
theorem theorem5_general (hall : ∀ p o, I.allowed p o) (hME : RWMutualExclusion I)
    (hBE : BoundedExit I) (hDF : I.DeadlockFree) (hCE : ConcurrentEntering I) (w : Fin m)
    {Wb Rb : ℕ} (hW : WriterEntryRMR I cm Wb) (hR : ReaderExitRMR I cm Rb) :
    n ≤ Wb * 3 ^ Rb := by
  classical
  /- `E₁`: all readers enter the CS -/
  obtain ⟨α₁, X₁, hX₁, hwf₁, hr₁, hw₁, hp₁, -⟩ :=
    exists_E1 (cm := cm) hall hCE (List.finRange n) (List.nodup_finRange n)
  have hr₁' : ∀ i, regionOf α₁ (.inl i) = some .cs := fun i => by rw [hr₁]; simp
  /- the readers invoke `unlock` -/
  set β₀ : List (Label (Proc n m) mutexObj) :=
    (List.finRange n).map fun i => .inv (.inl i) .unlock with hβ₀
  obtain ⟨X₀, hX₀, hk₀, hp₀, hq₀⟩ := xrun_invs (List.finRange n) (List.nodup_finRange n)
    X₁.fresh hall (fun i _ => hp₁ _)
  have hX₀kn : X₀.kn = Know.init := hk₀
  have hβ₀lbl : ∀ ℓ ∈ β₀, ℓ.proc.isLeft ∧ ∀ q, ℓ ≠ .inv q .lock := by
    intro ℓ h; obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact ⟨rfl, fun q h => by cases h⟩
  have hreg01 : ∀ q, regionOf (α₁ ++ β₀) q =
      some (if q.isLeft then .exiting else .rem) := by
    intro q
    rw [regionOf_append, hβ₀, regFold_invs _ (List.nodup_finRange n)]
    cases q with
    | inl i => simp [hr₁' i, Region.next]
    | inr j => simp [hw₁ j]
  have hrun₀ : ∀ γ (Z : Ext I cm), xrun X₀ γ = some Z → I.run (α₁ ++ β₀ ++ γ) = some Z.cfg := by
    intro γ Z h
    have h1 : I.run (α₁ ++ β₀) = some X₀.cfg := by
      rw [Impl.run_append_of_eq I (run_of_xrun hX₁)]; have := xrun_cfg hX₀; exact this
    rw [Impl.run_append_of_eq I h1]; exact xrun_cfg h
  /- Bounded Exit gives a bound on the exit steps -/
  have hBi : ∀ i : Fin n, ∃ B, ∀ β, I.Valid (α₁ ++ β₀ ++ β) → ¬ Returns (.inl i) β →
      tauCount (.inl i) β ≤ B := fun i =>
    hBE (α₁ ++ β₀) (.inl i) ⟨X₀.cfg, by simpa using hrun₀ [] X₀ rfl⟩
      (fun q => by rw [hreg01 q]; simp) (by rw [hreg01]; rfl)
  choose B hB using hBi
  set Bm := ∑ i, B i
  have hBm : ∀ γ (Z : Ext I cm), xrun X₀ γ = some Z → (∀ ℓ ∈ γ, ∀ q o, ℓ ≠ .inv q o) →
      ∀ i, ¬ Returns (.inl i) γ → tauCount (.inl i) γ ≤ Bm := fun γ Z h _ i hi =>
    (hB i γ ⟨_, hrun₀ γ Z h⟩ hi).trans
      (Finset.single_le_sum (f := B) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  /- `E₂` -/
  have hInv0 : E2Inv X₀ [] X₀ 0 := by
    refine ⟨rfl, by simp, fun i => ?_, fun j => ?_, fun q => ?_, fun _ _ => Nat.zero_le _,
      Or.inl rfl⟩
    · simp [hp₀ i (List.mem_finRange i)]
    · rw [hq₀ _ (fun i _ h => by cases h)]; exact hp₁ _
    · rw [hX₀kn]; simp [Know.init]
  obtain ⟨γ, Z₂, r, hI, hidle⟩ := e2_construct X₀ hX₀kn Bm hBm _ [] X₀ 0 hInv0 le_rfl
  simp only [List.nil_append] at hI
  have hZ₂ : xrun X₁.fresh (β₀ ++ γ) = some Z₂ := by rw [xrun_append_of_eq hX₀]; exact hI.run
  have hγlbl : ∀ ℓ ∈ β₀ ++ γ, ℓ.proc.isLeft ∧ ∀ q, ℓ ≠ .inv q .lock := by
    intro ℓ h
    rcases List.mem_append.1 h with h | h
    · exact hβ₀lbl ℓ h
    · exact ⟨(hI.lbl ℓ h).1, fun q => (hI.lbl ℓ h).2 q _⟩
  have hreg02 : ∀ q, regionOf (α₁ ++ β₀ ++ γ) q = some .rem := by
    intro q
    rw [regionOf_append, hreg01]
    cases q with
    | inl i => simpa [hidle i] using hI.reg i
    | inr j =>
      rw [regFold_of_forall_ne]
      · rfl
      · intro ℓ h he; have := (hI.lbl ℓ h).1; rw [he] at this; cases this
  have hidle₂ : ∀ q, Z₂.cfg.pend q = none := by
    intro q; cases q with
    | inl i => exact hidle i
    | inr j => exact hI.wr j
  have hrun₂ : I.run (α₁ ++ β₀ ++ γ) = some Z₂.cfg := hrun₀ γ Z₂ hI.run
  /- `E₃`: writer `w` enters the CS -/
  have hs₃ := Impl.step_inv_eq_some (I := I) (o := MutexOp.lock) (hidle₂ (.inr w)) (hall _ _)
  set C₃ := { Z₂.cfg with pend := Function.update Z₂.cfg.pend (.inr w) (some .lock),
                          loc := Function.update Z₂.cfg.loc (.inr w)
                            (I.invoke (.inr w) (Z₂.cfg.loc (.inr w)) .lock) } with hC₃
  have hrun₃ : I.run (α₁ ++ β₀ ++ γ ++ [.inv (.inr w) .lock]) = some C₃ := by
    rw [Impl.run_append_of_eq I hrun₂, Impl.runFrom_singleton, hs₃]
  have hreg03 : ∀ q, regionOf (α₁ ++ β₀ ++ γ ++ [.inv (.inr w) .lock]) q =
      some (if q = .inr w then .trying else .rem) := by
    intro q
    rw [regionOf_append, hreg02]
    by_cases hq : q = .inr w
    · subst hq; simp [regFold_cons, Label.proc, Region.next]
    · simp [regFold_cons, Label.proc, Ne.symm hq, hq]
  obtain ⟨k, hk⟩ := solo_returns_of_deadlockFree I hDF hrun₃
    (fun q => by rw [hreg03]; simp)
    (fun q hq => by unfold InCS at hq; rw [hreg03] at hq; split_ifs at hq <;> cases hq)
    (p := .inr w) (by simp [hC₃])
    (fun q hq => by simp [hC₃, Function.update_of_ne hq, hidle₂ q])
  set E₃ : List (Label (Proc n m) mutexObj) :=
    [.inv (.inr w) .lock] ++ I.soloLabels (.inr w) C₃ k with hE₃
  have hE₃proc : ∀ ℓ ∈ E₃, ℓ.proc = .inr w := by
    intro ℓ h
    rcases List.mem_append.1 h with h | h
    · simp only [List.mem_singleton] at h; subst h; rfl
    · exact I.soloLabels_proc _ _ _ ℓ h
  have hrunE₃ : I.runFrom Z₂.cfg E₃ = some ((I.soloStep (.inr w))^[k] C₃) := by
    rw [hE₃, Impl.runFrom_append, Impl.runFrom_singleton, hs₃, Option.bind_some,
      Impl.runFrom_soloLabels]
  obtain ⟨Y₃, hY₃, -⟩ := exists_xrun (X := Z₂) hrunE₃
  have hreg04 : ∀ q, regionOf (α₁ ++ β₀ ++ γ ++ E₃) q =
      some (if q = .inr w then .cs else .rem) := by
    intro q
    rw [hE₃, ← List.append_assoc, regionOf_append, hreg03]
    by_cases hq : q = .inr w
    · subst hq
      rw [if_pos rfl, regFold_soloLabels I _ .trying .cs (fun _ => rfl) rfl k C₃ (by simp [hC₃]),
        if_pos hk, if_pos rfl]
    · rw [if_neg hq, if_neg hq, regFold_of_forall_ne]
      intro ℓ hℓ; rw [I.soloLabels_proc _ _ _ ℓ hℓ]; exact Ne.symm hq
  have hassoc : α₁ ++ (β₀ ++ γ ++ E₃) = α₁ ++ β₀ ++ γ ++ E₃ := by
    simp only [List.append_assoc]
  have hwf₄ : ClientWF (α₁ ++ (β₀ ++ γ ++ E₃)) := fun q => by
    rw [hassoc, hreg04]; simp
  have hδ : xrun X₁.fresh (β₀ ++ γ ++ E₃) = some Y₃ := by
    rw [xrun_append_of_eq hZ₂]; exact hY₃
  /- Lemma 4: the writer is aware of every reader -/
  have hL4 : ∀ i, (Sum.inl i : Proc n m) ∈ Y₃.kn.aw (.inr w) := fun i =>
    lemma4 hME hX₁ hδ hwf₄ i (hr₁' i) w (by
      unfold InCS; rw [hassoc, hreg04]; simp)
  /- counting -/
  have hKZ₂ : KInv Z₂.kn := xrun_kinv hZ₂ KInv.init
  have hawZ₂ : Z₂.kn.aw (.inr w) = {.inr w} := by
    rw [xrun_aw_of_not_mem hZ₂ _ (fun ℓ h he => by
      have := (hγlbl ℓ h).1; rw [he] at this; cases this)]
    rfl
  have hsolo := aw_solo_bound (.inr w) hE₃proc
    (fun i => hKZ₂.card_fam_le i (fun q => hI.aw q)) hY₃
  rw [hawZ₂, Finset.card_singleton] at hsolo
  have hcardY : n + 1 ≤ (Y₃.kn.aw (.inr w)).card := by
    have hsub : insert (Sum.inr w) (Finset.univ.image (Sum.inl : Fin n → Proc n m)) ⊆
        Y₃.kn.aw (.inr w) := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact (xrun_kinv hδ KInv.init).self_mem _
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact hL4 i
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_univ, Fintype.card_fin] at this
    exact this
  -- the writer's expanding steps are RMRs (Lemma 1)
  have hexpW : xcount (ExpBy (.inr w)) Z₂ E₃ ≤ xcount (RMRBy (.inr w)) Z₂ E₃ := by
    have h1 := lemma1_count (p := .inr w) (X := X₁.fresh) rfl hδ
    rw [xcount_append _ hZ₂, xcount_append _ hZ₂] at h1
    rw [xcount_eq_zero _ _ (β₀ ++ γ) (fun ℓ h Y he => by
        have := (hγlbl ℓ h).1; rw [he.1] at this; cases this),
      xcount_eq_zero _ _ (β₀ ++ γ) (fun ℓ h Y he => by
        have := (hγlbl ℓ h).1; rw [he.1] at this; cases this)] at h1
    omega
  -- RMRs of the writer's entry section
  obtain ⟨X₂, hX₂, hX₂c, hX₂ca⟩ := xrun_congr (X := X₁.fresh) (X' := X₁) rfl rfl hZ₂
  obtain ⟨Y₃', hY₃', -⟩ := xrun_congr (X := Z₂) (X' := X₂) hX₂c hX₂ca hY₃
  have hWb : xcount (RMRBy (.inr w)) Z₂ E₃ ≤ Wb := by
    rw [← xcount_rmr_congr (X' := X₂) _ _ hX₂c hX₂ca]
    apply hW (α₁ ++ β₀ ++ γ) E₃ X₂ Y₃' w
      (by rw [List.append_assoc, xrun_append_of_eq hX₁]; exact hX₂) hY₃'
      (fun q => by rw [hreg04]; simp) (by rw [hreg02])
    intro ℓ h he
    rcases List.mem_append.1 h with h | h
    · simp only [List.mem_singleton] at h; rw [h] at he; cases he
    · exact soloLabels_not_inv I _ k C₃ ℓ h _ _ he
  have hn : n ≤ 3 ^ r * Wb := by
    have := Nat.mul_le_mul_left (3 ^ r) (hexpW.trans hWb)
    omega
  /- the reader that took part in all rounds performs at least `r` RMRs in its exit section -/
  rcases hI.some with hr0 | ⟨i, hi⟩
  · subst hr0
    calc n ≤ 3 ^ 0 * Wb := hn
      _ = Wb * 1 := by simp
      _ ≤ Wb * 3 ^ Rb := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by decide))
  · have hβ₀exp : xcount (ExpBy (.inl i)) X₁.fresh β₀ = 0 :=
      xcount_eq_zero _ _ _ (fun ℓ h Y => by
        obtain ⟨i', -, rfl⟩ := List.mem_map.1 h
        exact not_expBy_of_not_tau (fun q h => by cases h) _ Y)
    have hexpR : r ≤ xcount (ExpBy (.inl i)) X₁.fresh (β₀ ++ γ) := by
      rw [xcount_append _ hX₀, hβ₀exp]; omega
    have h1 := lemma1_count (p := .inl i) (X := X₁.fresh) rfl hZ₂
    rw [xcount_rmr_congr (X := X₁) (X' := X₁.fresh) _ _ rfl rfl] at h1
    have hRb : xcount (RMRBy (.inl i)) X₁ (β₀ ++ γ) ≤ Rb :=
      hR α₁ (β₀ ++ γ) X₁ X₂ i hX₁ hX₂ (fun q => by
        rw [← List.append_assoc, hreg02]; simp) (hr₁' i)
        (fun ℓ h => (hγlbl ℓ h).2 _)
    have hrR : r ≤ Rb := by omega
    calc n ≤ 3 ^ r * Wb := hn
      _ ≤ 3 ^ Rb * Wb := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hrR)
      _ = Wb * 3 ^ Rb := Nat.mul_comm _ _

/-- **Theorem 5** (`n` readers, a single writer). For a reader-writer lock from read/write/CAS
registers satisfying Mutual Exclusion, Bounded Exit, Deadlock Freedom and Concurrent Entering, in
any cache-coherent model (e.g. `writeBack`, `writeThrough`): if the writer's entry section incurs at
most `Wb` RMRs and the reader's exit section at most `Rb` RMRs, then `n ≤ Wb · 3^Rb`. -/
theorem theorem5 {I : RWAlg n 1 ι V v₀ L} {cm : CacheModel (Proc n 1) ι}
    (hall : ∀ p o, I.allowed p o) (hME : RWMutualExclusion I) (hBE : BoundedExit I)
    (hDF : I.DeadlockFree) (hCE : ConcurrentEntering I) {Wb Rb : ℕ}
    (hW : WriterEntryRMR I cm Wb) (hR : ReaderExitRMR I cm Rb) : n ≤ Wb * 3 ^ Rb :=
  theorem5_general hall hME hBE hDF hCE 0 hW hR

/-- **Theorem 5**, logarithmic form: if the writer's entry section incurs at most `C` RMRs (e.g.
`C = c · f(n)`), then the reader's exit section incurs at least `log₃ (n / C)` RMRs; i.e.
`O(f(n))` writer entry forces `Ω(log (n / f(n)))` reader exit. -/
theorem theorem5_logb {I : RWAlg n 1 ι V v₀ L} {cm : CacheModel (Proc n 1) ι}
    (hall : ∀ p o, I.allowed p o) (hME : RWMutualExclusion I) (hBE : BoundedExit I)
    (hDF : I.DeadlockFree) (hCE : ConcurrentEntering I) {Wb Rb C : ℕ} (hC : Wb ≤ C)
    (hn : 0 < n) (hW : WriterEntryRMR I cm Wb) (hR : ReaderExitRMR I cm Rb) :
    Real.logb 3 ((n : ℝ) / C) ≤ Rb := by
  have h := theorem5 hall hME hBE hDF hCE hW hR
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos Wb with h0 | h0
    · subst h0; simp at h; omega
    · omega
  have hle : (n : ℝ) ≤ C * 3 ^ Rb := by
    have : n ≤ C * 3 ^ Rb := h.trans (Nat.mul_le_mul_right _ hC)
    exact_mod_cast this
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), div_le_iff₀ (by positivity),
    Real.rpow_natCast]
  linarith

/-- **Corollary 6.** Either the writer's entry section or the reader's exit section incurs
`Ω(log n)` RMRs: `⌊log₃ n⌋ ≤ Wb + Rb`, hence `⌊log₃ n⌋ ≤ 2 · max Wb Rb`. -/
theorem corollary6 {I : RWAlg n 1 ι V v₀ L} {cm : CacheModel (Proc n 1) ι}
    (hall : ∀ p o, I.allowed p o) (hME : RWMutualExclusion I) (hBE : BoundedExit I)
    (hDF : I.DeadlockFree) (hCE : ConcurrentEntering I) {Wb Rb : ℕ}
    (hW : WriterEntryRMR I cm Wb) (hR : ReaderExitRMR I cm Rb) :
    Nat.log 3 n ≤ Wb + Rb ∧ Nat.log 3 n ≤ 2 * max Wb Rb := by
  have h := theorem5 hall hME hBE hDF hCE hW hR
  have h1 : n ≤ 3 ^ (Wb + Rb) := by
    rw [pow_add]
    exact h.trans (Nat.mul_le_mul_right _ (Nat.lt_pow_self (by norm_num)).le)
  have h2 : Nat.log 3 n ≤ Wb + Rb :=
    (Nat.log_mono_right h1).trans (by rw [Nat.log_pow (by norm_num)])
  exact ⟨h2, by omega⟩

end Podc.RWLockRMRTradeoff
