import Papers.PODC2011.RulesOfThumb.Concat

/-!
# Theorem 4.1: multiple stable states imply non-convergence

The valency argument of Appendix F, assembled:

* `not_convergent_of_absorbing`: for self-independent `k`-recall reaction functions (not
  necessarily stationary), two distinct stable states rule out convergence, **provided** the limit
  of every fair dynamics is eventually *absorbing* (from some time on, a node that sees its `k`
  most recent profiles all equal to the limit reproduces its action). This proviso is what makes
  a forever-bivalent fair run non-convergent; the paper does not address it (see `README.md`).
* `theorem_4_1`: Theorem 4.1 for stationary bounded-recall reaction functions (the version
  restated and proved in Appendix F.6/F.8), where the proviso is automatic.
-/

namespace Podc.RulesOfThumb

open Filter

universe u v

variable {ι : Type u} {A : ι → Type v} [DecidableEq ι]

namespace System

variable (F : System A)

/-- From time `T` on, the profile `c` is absorbing for the `k`-recall dynamics: a node that is
activated when its `k` most recent profiles are all `c` chooses its action in `c`. -/
def AbsorbingAfter (k : ℕ) (c : Profile A) (T : ℕ) : Prop :=
  ∀ i (h : Hist A), T ≤ h.time → k ≤ h.time → h.toList.take k = List.replicate k c →
    F.f i (h.time + 1) h = c i

variable {F}

lemma take_pred_of_take_eq_replicate {α : Type*} {l : List α} {k : ℕ} {c : α}
    (h : l.take (k + 1) = List.replicate (k + 1) c) : l.take k = List.replicate k c := by
  have : l.take k = (l.take (k + 1)).take k := by
    rw [List.take_take, min_eq_left (Nat.le_succ k)]
  rw [this, h, List.take_replicate, min_eq_left (Nat.le_succ k)]

lemma AbsorbingAfter.run {k : ℕ} (hk : 1 ≤ k) {c : Profile A} {T : ℕ}
    (habs : F.AbsorbingAfter k c T) {h : Hist A} (hT : T ≤ h.time) (hkt : k ≤ h.time)
    (htake : h.toList.take k = List.replicate k c) (σ : ℕ → Finset ι) (m : ℕ) :
    (F.run h σ m).toList.take k = List.replicate k c := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction m with
  | zero => exact htake
  | succ m ih =>
    have hcur : (F.run h σ m).cur = c := by
      have := ih; simp only [Hist.toList, take_cons_succ, List.replicate_succ,
        List.cons.injEq] at this
      exact this.1
    rw [run_succ, step_toList, take_cons_succ, List.replicate_succ,
      take_pred_of_take_eq_replicate ih]
    congr 1
    funext i
    by_cases hi : i ∈ σ ((F.run h σ m).time + 1)
    · rw [step_cur_of_mem _ hi]
      exact habs i _ (by simp; omega) (by simp; omega) ih
    · rw [step_cur_of_not_mem _ hi, hcur]

lemma subsingleton_lims_of_absorbing {k : ℕ} (hk : 1 ≤ k) {c : Profile A} {T : ℕ}
    (habs : F.AbsorbingAfter k c T) {h : Hist A} (hT : T ≤ h.time) (hkt : k ≤ h.time)
    (htake : h.toList.take k = List.replicate k c) (P : Finset ι) :
    (F.lims h P).Subsingleton := by
  have hmem : ∀ a ∈ F.lims h P, a = c := by
    rintro a ⟨σ, -, -, -, hconv⟩
    obtain ⟨m, hm⟩ := hconv.exists
    have := habs.run hk hT hkt htake σ m
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Hist.toList, take_cons_succ, List.replicate_succ, List.cons.injEq] at this
    rw [← hm, this.1]
  intro a ha b hb
  rw [hmem a ha, hmem b hb]

/-- Once the dynamics has stayed at `a` for `n` steps, the `n` most recent profiles are `a`. -/
lemma take_run_eq_replicate {h : Hist A} {σ : ℕ → Finset ι} {a : Profile A} {N : ℕ}
    (hN : ∀ j, N ≤ j → (F.run h σ j).cur = a) (n : ℕ) :
    (F.run h σ (N + n)).toList.take n = List.replicate n a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, run_succ, step_toList, take_cons_succ, ih, List.replicate_succ,
      ← run_succ, hN _ (by omega)]

/-- **The valency argument (Appendix F).** Self-independent `k`-recall reaction functions (not
necessarily stationary) and two distinct stable states rule out convergence, provided that in a
convergent system the limit of every fair dynamics is eventually absorbing. -/
theorem not_convergent_of_absorbing [Fintype ι] {k : ℕ} (hk : 1 ≤ k)
    (hrec : ∀ i, F.HasRecall i k) (hsi : F.SelfIndependent)
    (habs : F.Convergent → ∀ (h : Hist A) (σ : ℕ → Finset ι) (c : Profile A), IsSchedule σ →
      Fair σ → F.ConvergesTo h σ c → ∃ T, F.AbsorbingAfter k c T)
    {c d : Profile A} (hcd : c ≠ d) (hc : F.IsStableState c) (hd : F.IsStableState d) :
    ¬ F.Convergent := by
  intro hconv
  have : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact hcd (funext fun i => isEmptyElim i)
  obtain ⟨h₀, hb⟩ := exists_biv_hist hk hrec hsi hconv hcd hc hd
  obtain ⟨σ, hσ, hf, hinf⟩ := exists_fair_of_segments (F := F) (fun h => F.Biv (h, ∅))
    (fun _ _ _ => True) hb (fun h hh i => by
      obtain ⟨τ, m, h1, h2, h3⟩ := exists_segment hk hrec hsi hconv hh i
      exact ⟨τ, m, h1, h2, h3, trivial⟩)
  obtain ⟨a, ha⟩ := hconv h₀ σ hσ hf
  obtain ⟨T, hT⟩ := habs hconv h₀ σ a hσ hf ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha
  obtain ⟨n, hn, -, -, hbiv, -⟩ := hinf (N + k + T)
  apply hbiv
  refine subsingleton_lims_of_absorbing hk hT (by simp; omega) (by simp; omega) ?_ ∅
  have := take_run_eq_replicate (N := n - k) (fun j hj => hN j (by omega)) k
  rwa [show n - k + k = n by omega] at this

/-- In a stationary `k`-recall system the limit of a fair dynamics is absorbing. -/
lemma absorbingAfter_of_stationary {k : ℕ} (hst : ∀ i, F.Stationary i k) {h : Hist A}
    {σ : ℕ → Finset ι} {c : Profile A} (hf : Fair σ) (hc : F.ConvergesTo h σ c) :
    F.AbsorbingAfter k c 0 := by
  intro i g _ hkg htake
  obtain ⟨gi, hgi⟩ := hst i
  rw [hgi g hkg, htake]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  obtain ⟨t, hit, ht⟩ := ((hf i).and_eventually (eventually_gt_atTop (h.time + N + k))).exists
  set m := t - h.time - 1
  have hmt : (F.run h σ m).time + 1 = t := by simp [m]; omega
  have h1 : (F.run h σ (m + 1)).cur i = c i := by rw [hN _ (by omega)]
  rw [run_succ, hmt, step_cur_of_mem _ hit] at h1
  rw [hgi _ (by simp; omega)] at h1
  have := take_run_eq_replicate (N := m - k) (fun j hj => hN j (by omega)) k
  rw [show m - k + k = m by omega] at this
  rwa [this] at h1

/-- **Theorem 4.1** of [Jaggard–Schapira–Wright], in the form restated and proved in Appendix F
(F.6, F.8): if every reaction function is deterministic, self-independent and stationary with
bounded recall, then the existence of two distinct stable states implies that the system is not
convergent. -/
theorem theorem_4_1 [Fintype ι] (hst : ∀ i, ∃ k, F.Stationary i k) (hsi : F.SelfIndependent)
    (h2 : ∃ a b, a ≠ b ∧ F.IsStableState a ∧ F.IsStableState b) : ¬ F.Convergent := by
  obtain ⟨a, b, hab, ha, hb⟩ := h2
  choose k hk using hst
  set K := Finset.univ.sup k + 1
  have hstK : ∀ i, F.Stationary i K := fun i =>
    (hk i).mono ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
  exact not_convergent_of_absorbing (k := K) (Nat.le_add_left 1 _) (fun i => (hstK i).hasRecall)
    hsi (fun _ _ _ _ _ hf hc => ⟨0, absorbingAfter_of_stationary hstK hf hc⟩) hab ha hb

end System

end Podc.RulesOfThumb
