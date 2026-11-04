import Podc.Computability.Distributed.MessagePassing.Timed.Lin
import Papers.PODC2011.SharedObjectTimeBounds.Spec

/-!
# Common machinery for the lower bounds of Chapter IV

* `rhoCalls p₀ g ρ`: process `p₀` invokes the operations of `ρ` one after the other, at times
  `0, g, 2g, …` (with `g` larger than the bound `B_op` on operation times, every operation has
  responded before the next is invoked; this is the run of `R_ρ` of §IV.B.2, with a fixed gap
  instead of "immediately after the response").
* `Scenario.trunc`, `wf_of_trunc`, `wf_of_spaced`: well-formedness of a scenario, proved by
  induction on the invocations (each operation must respond before the next invocation of its
  process, which is checked in the run truncated before that invocation).
* `contLin`: in a correct algorithm, a run consisting of the `ρ`-phase followed by later
  operations `cont` yields a legal sequence `ρ ∘ L` where `L` is a permutation of `cont`
  respecting the real-time order (the `ρ`-operations return exactly as in `ρ`).
-/

namespace Podc.SharedObjectTimeBounds

open Cslib.TimedMP

variable {P I R M : Type*}

/-- `p₀` invokes the operations of `ρ` (ids from `j`) at times `j g, (j+1) g, …`. -/
def rhoCallsFrom (p₀ : P) (g : ℝ) : ℕ → List (I × R) → List (Call P I)
  | _, [] => []
  | j, o :: ρ => ⟨p₀, j, j * g, o.1⟩ :: rhoCallsFrom p₀ g (j + 1) ρ

/-- The `ρ`-phase: `p₀` invokes the operations of `ρ` at times `0, g, 2g, …`. -/
def rhoCalls (p₀ : P) (g : ℝ) (ρ : List (I × R)) : List (Call P I) := rhoCallsFrom p₀ g 0 ρ

theorem mem_rhoCallsFrom {p₀ : P} {g : ℝ} :
    ∀ {j : ℕ} {ρ : List (I × R)} {c : Call P I}, c ∈ rhoCallsFrom p₀ g j ρ →
      c.p = p₀ ∧ j ≤ c.k ∧ c.k < j + ρ.length ∧ c.t = c.k * g
  | _, [], _, h => by simp [rhoCallsFrom] at h
  | j, o :: ρ, c, h => by
    simp only [rhoCallsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2, h3, h4⟩ := mem_rhoCallsFrom h
      refine ⟨h1, by omega, by simp; omega, h4⟩

theorem pairwise_rhoCallsFrom {p₀ : P} {g : ℝ} :
    ∀ (j : ℕ) (ρ : List (I × R)), (rhoCallsFrom p₀ g j ρ).Pairwise (fun c c' => c.k < c'.k)
  | _, [] => by simp [rhoCallsFrom]
  | j, o :: ρ => by
    simp only [rhoCallsFrom, List.pairwise_cons]
    exact ⟨fun c hc => by have := (mem_rhoCallsFrom hc).2.1; simp; omega,
      pairwise_rhoCallsFrom (j + 1) ρ⟩

theorem map_a_rhoCallsFrom {p₀ : P} {g : ℝ} :
    ∀ (j : ℕ) (ρ : List (I × R)), (rhoCallsFrom p₀ g j ρ).map Call.a = ρ.map Prod.fst
  | _, [] => rfl
  | j, o :: ρ => by simp [rhoCallsFrom, map_a_rhoCallsFrom (j + 1) ρ]

theorem length_rhoCallsFrom {p₀ : P} {g : ℝ} :
    ∀ (j : ℕ) (ρ : List (I × R)), (rhoCallsFrom p₀ g j ρ).length = ρ.length
  | _, [] => rfl
  | j, o :: ρ => by simp [rhoCallsFrom, length_rhoCallsFrom (j + 1) ρ]

theorem nodup_rhoCalls (p₀ : P) (g : ℝ) (ρ : List (I × R)) : (rhoCalls p₀ g ρ).Nodup :=
  (pairwise_rhoCallsFrom 0 ρ).imp fun h e => by subst e; exact lt_irrefl _ h

theorem mem_rhoCalls {p₀ : P} {g : ℝ} {ρ : List (I × R)} {c : Call P I}
    (h : c ∈ rhoCalls p₀ g ρ) : c.p = p₀ ∧ c.k < ρ.length ∧ c.t = c.k * g := by
  obtain ⟨h1, -, h3, h4⟩ := mem_rhoCallsFrom h
  exact ⟨h1, by simpa using h3, h4⟩


theorem trunc_trunc (s : Scenario P I) {a b : ℝ} (hab : b ≤ a) :
    (s.trunc a).trunc b = s.trunc b := by
  simp only [Scenario.trunc, List.filter_filter]
  congr 2
  funext c
  by_cases h : c.t < b
  · simp [h, lt_of_lt_of_le h hab]
  · simp [h]

section WF

variable [Finite P] (A : Algorithm P I R M)

theorem trunc_minDelay {s : Scenario P I} {γ : ℝ} (h : s.MinDelay γ) (τ : ℝ) :
    (s.trunc τ).MinDelay γ := h

theorem trunc_admissible {s : Scenario P I} {d u ε : ℝ} (h : s.Admissible d u ε) (τ : ℝ) :
    (s.trunc τ).Admissible d u ε := h

/-- Well-formedness by induction on invocations: it suffices that each operation responds before
the next invocation of its process in the run truncated before that invocation. -/
theorem wf_of_trunc {γ : ℝ} :
    ∀ (N : ℕ) (s : Scenario P I), s.calls.length ≤ N → s.MinDelay γ → s.calls.Nodup →
      (∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.k = c'.k → c = c') →
      (∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t = c'.t → c = c') →
      (∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t < c'.t →
        ∀ H₀, IsRun A (s.trunc c'.t) H₀ → WF A (s.trunc c'.t) H₀ →
          ∃ σ r, RespAt A (s.trunc c'.t) H₀ c σ r ∧ c.t ≤ σ ∧ σ < c'.t) →
      ∀ H, IsRun A s H → WF A s H := by
  intro N
  induction N with
  | zero =>
    intro s hN _ hnd hid htm _ H _
    have : s.calls = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨hnd, hid, htm, fun c hc => by simp [this] at hc⟩
  | succ N ih =>
    intro s hN hγ hnd hid htm hresp H hH
    refine ⟨hnd, hid, htm, fun c hc c' hc' hp ht => ?_⟩
    -- the truncation before `c'.t`
    set s₀ := s.trunc c'.t
    have hlen : s₀.calls.length ≤ N := by
      have : s₀.calls.length < s.calls.length := by
        simp only [s₀, Scenario.trunc]
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨c', hc', by simp⟩
      omega
    obtain ⟨H₀, hH₀⟩ := exists_run A s₀ hγ
    have hsub : ∀ x ∈ s₀.calls, x ∈ s.calls := fun x hx => List.mem_of_mem_filter hx
    have hwf₀ : WF A s₀ H₀ := by
      refine ih s₀ hlen hγ (hnd.filter _) (fun x hx y hy => hid x (hsub x hx) y (hsub y hy))
        (fun x hx y hy => htm x (hsub x hx) y (hsub y hy)) ?_ H₀ hH₀
      intro x hx y hy hpxy hxy H₁ hH₁ hwf₁
      have hyt : y.t < c'.t := by simpa [s₀, Scenario.trunc] using (List.mem_filter.mp hy).2
      rw [trunc_trunc s (le_of_lt hyt)] at hH₁ hwf₁ ⊢
      exact hresp x (hsub x hx) y (hsub y hy) hpxy hxy H₁ hH₁ hwf₁
    obtain ⟨σ, r, hr, h1, h2⟩ := hresp c hc c' hc' hp ht H₀ hH₀ hwf₀
    refine ⟨σ, r, ?_, h1, h2⟩
    have hag := agree_of_calls_ge (A := A) (s := s₀) (s' := s) rfl rfl hH₀ hH hγ c'.t
      (fun x hx hn => absurd (hsub x hx) hn)
      (fun x hx hn => by
        by_contra hlt; push_neg at hlt
        exact hn (List.mem_filter.mpr ⟨hx, by simpa using hlt⟩))
    exact (respAt_congr rfl (fun e he => hag c.p e he) h2).mp hr

/-- Well-formedness of scenarios in which invocations of a process are more than `B_op` apart. -/
theorem wf_of_spaced {legal : List (I × R) → Prop} {d u ε Bop γ : ℝ}
    (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop)
    (s : Scenario P I) (hadm : s.Admissible d u ε) (hγ : s.MinDelay γ) (hnd : s.calls.Nodup)
    (hid : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.k = c'.k → c = c')
    (hsp : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c ≠ c' → c.t < c'.t → c.t + Bop < c'.t)
    (htm : ∀ c ∈ s.calls, ∀ c' ∈ s.calls, c.p = c'.p → c.t = c'.t → c = c') :
    ∀ H, IsRun A s H → WF A s H := by
  refine wf_of_trunc A _ s le_rfl hγ hnd hid htm ?_
  intro c hc c' hc' hp ht H₀ hH₀ hwf₀
  have hc₀ : c ∈ (s.trunc c'.t).calls := List.mem_filter.mpr ⟨hc, by simpa using ht⟩
  obtain ⟨rt, ret, hr, -⟩ := hcor _ H₀ (trunc_admissible hadm _) hH₀ hwf₀
  obtain ⟨h1, h2, -⟩ := hr c hc₀
  have hne : c ≠ c' := by rintro rfl; exact lt_irrefl _ ht
  refine ⟨rt c, ret c, h2, h1, ?_⟩
  have := hB _ H₀ (trunc_admissible hadm _) hH₀ hwf₀ c hc₀ trivial _ _ h2
  have := hsp c hc c' hc' hp hne ht
  linarith

end WF

section ContLin

variable [Finite P] (A : Algorithm P I R M)

/-- **Linearization after the `ρ`-phase.** In a correct algorithm with operation times at most
`Bop < g`, a well-formed admissible run of `ρ`-phase followed by operations `cont` invoked at
times `≥ |ρ| g` linearizes as `ρ ∘ L` with `L` a permutation of `cont` respecting the real-time
order of `cont`. -/
theorem contLin {legal : List (I × R) → Prop} {d u ε Bop g : ℝ}
    (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g)
    (hg0 : 0 < g) {p₀ : P} {ρ : List (I × R)} (hρ : legal ρ) {cont : List (Call P I)}
    (hcont : ∀ c ∈ cont, ρ.length * g ≤ c.t)
    (s : Scenario P I) (hs : s.calls = rhoCalls p₀ g ρ ++ cont) (hadm : s.Admissible d u ε)
    {H : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H) (hwf : WF A s H) :
    ∃ rt : Call P I → ℝ, ∃ ret : Call P I → R,
      (∀ c ∈ s.calls, c.t ≤ rt c ∧ RespAt A s H c (rt c) (ret c) ∧
        ∀ σ r, RespAt A s H c σ r → σ = rt c ∧ r = ret c) ∧
      (rhoCalls p₀ g ρ).map (fun c => (c.a, ret c)) = ρ ∧
      ∃ L : List (Call P I), L.Perm cont ∧ L.Nodup ∧ legal (ρ ++ L.map fun c => (c.a, ret c)) ∧
        ∀ c ∈ cont, ∀ c' ∈ cont, rt c < c'.t → [c, c'].Sublist L := by
  obtain ⟨rt, ret, hr, L, hLp, hLl, hLrt⟩ := hcor s H hadm hH hwf
  have hmem : ∀ c ∈ cont, c ∈ s.calls := fun c hc => by rw [hs]; exact List.mem_append_right _ hc
  have hmemρ : ∀ c ∈ rhoCalls p₀ g ρ, c ∈ s.calls := fun c hc => by
    rw [hs]; exact List.mem_append_left _ hc
  refine ⟨rt, ret, hr, ?_⟩
  have hnd : L.Nodup := hLp.nodup_iff.mpr (hs ▸ hwf.1)
  -- response times of the `ρ`-operations
  have hrtρ : ∀ c ∈ rhoCalls p₀ g ρ, rt c < (c.k + 1 : ℕ) * g := by
    intro c hc
    have := hB s H hadm hH hwf c (hmemρ c hc) trivial _ _ (hr c (hmemρ c hc)).2.1
    rw [(mem_rhoCalls hc).2.2] at this
    push_cast; nlinarith
  have hrel : ∀ c ∈ rhoCalls p₀ g ρ, ∀ c' ∈ s.calls, (c.k + 1 : ℕ) * g ≤ c'.t →
      [c, c'].Sublist L := fun c hc c' hc' hle =>
    hLrt c (hmemρ c hc) c' hc' (lt_of_lt_of_le (hrtρ c hc) hle)
  -- the `ρ`-operations come first, in order
  have hpw : (rhoCalls p₀ g ρ).Pairwise (fun a b => [a, b].Sublist L) :=
    (pairwise_rhoCallsFrom 0 ρ).imp_of_mem fun {a b} ha hb hab => by
      refine hrel a ha b (hmemρ b hb) ?_
      rw [(mem_rhoCalls hb).2.2]
      have : ((a.k + 1 : ℕ) : ℝ) ≤ b.k := by exact_mod_cast hab
      nlinarith
  have hxy : ∀ x ∈ rhoCalls p₀ g ρ, ∀ y ∈ cont, [x, y].Sublist L := fun x hx y hy => by
    refine hrel x hx y (hmem y hy) (le_trans ?_ (hcont y hy))
    have : ((x.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast (mem_rhoCalls hx).2.1
    nlinarith
  obtain ⟨L', rfl, hL'⟩ := peel _ cont L (hs ▸ hLp) hnd hpw hxy
  have hρeq : (rhoCalls p₀ g ρ).map (fun c => (c.a, ret c)) = ρ := by
    refine det_seq hpc hdet _ _ [] ?_ (by simpa using hρ) ?_
    · simp only [List.nil_append]
      exact hpc _ _ (by simpa using hLl)
    · simp only [List.map_map]
      rw [show (Prod.fst ∘ fun c : Call P I => (c.a, ret c)) = Call.a from rfl]
      exact map_a_rhoCallsFrom 0 ρ
  have hdisj : ∀ c ∈ cont, c ∉ rhoCalls p₀ g ρ := fun c hc hcρ => by
    have := (hs ▸ hwf.1 : (rhoCalls p₀ g ρ ++ cont).Nodup)
    exact (List.nodup_append.mp this).2.2 c hcρ c hc rfl
  refine ⟨hρeq, L', hL', (List.nodup_append.mp hnd).2.1, ?_, ?_⟩
  · rw [List.map_append, hρeq] at hLl; exact hLl
  · intro c hc c' hc' hlt
    have h := hLrt c (hmem c hc) c' (hmem c' hc') hlt
    exact sublist_pair_append h (hdisj c hc)

/-- A `ρ`-only run: `p₀` alone executes exactly `ρ`. -/
theorem soloOps_rho {legal : List (I × R) → Prop} {d u ε Bop g : ℝ}
    (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g)
    (hg0 : 0 < g) {p₀ : P} {ρ : List (I × R)} (hρ : legal ρ)
    (s : Scenario P I) (hs : s.calls = rhoCalls p₀ g ρ) (hadm : s.Admissible d u ε)
    {H : P → Set (ℝ × InEv P I M)} (hH : IsRun A s H) (hwf : WF A s H) :
    SoloOps A s H p₀ ρ := by
  obtain ⟨rt, ret, hr, hρeq, -⟩ := contLin A hpc hdet hcor hB hg hg0 hρ (cont := [])
    (by simp) s (by simpa using hs) hadm hH hwf
  refine ⟨fun c hc => (mem_rhoCalls (hs ▸ hc)).1, rhoCalls p₀ g ρ, hs ▸ List.Perm.refl _, ?_, ?_⟩
  · refine (pairwise_rhoCallsFrom 0 ρ).imp_of_mem fun {a b} ha hb hab => ?_
    rw [(mem_rhoCalls ha).2.2, (mem_rhoCalls hb).2.2]
    have : (a.k : ℝ) < b.k := by exact_mod_cast hab
    nlinarith
  · have : List.Forall₂ (fun c o => c.a = o.1 ∧ ∃ σ, RespAt A s H c σ o.2) (rhoCalls p₀ g ρ)
        ((rhoCalls p₀ g ρ).map fun c => (c.a, ret c)) := by
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      intro c hc
      exact ⟨rfl, rt c, (hr c (hs ▸ hc)).2.1⟩
    rwa [hρeq] at this

/-- **Restart after the `ρ`-phase** (Claims B.3, B.4 and Corollary B.4 of the thesis). Two runs
with the same offsets whose parts before the clock times `κ` are (possibly different) admissible
runs in which `p₀` alone executes `ρ` agree in the windows `[κ, C)` under the window conditions of
`agree_window`; this uses history-obliviousness. -/
theorem restart {d u ε : ℝ} (hHO : HistoryOblivious A d u ε)
    (s s' : Scenario P I) (hoff : s.off = s'.off) {H H' : P → Set (ℝ × InEv P I M)}
    (hH : IsRun A s H) (hH' : IsRun A s' H') {γ : ℝ} (hγ : s.MinDelay γ)
    (r r' : Scenario P I) {Hr Hr' : P → Set (ℝ × InEv P I M)}
    (hra : r.Admissible d u ε) (hra' : r'.Admissible d u ε)
    (hHr : IsRun A r Hr) (hHr' : IsRun A r' Hr') (hwr : WF A r Hr) (hwr' : WF A r' Hr')
    {p₀ : P} {ρ : List (I × R)} (hso : SoloOps A r Hr p₀ ρ) (hso' : SoloOps A r' Hr' p₀ ρ)
    (κ : P → ℝ)
    (hagr : ∀ p (e : ℝ × InEv P I M), e.1 < κ p → (e ∈ H p ↔ e ∈ Hr p))
    (hagr' : ∀ p (e : ℝ × InEv P I M), e.1 < κ p → (e ∈ H' p ↔ e ∈ Hr' p))
    (hfin : ∀ p, (∀ e ∈ Hr p, e.1 < κ p) ∧ ∀ o ∈ A.beh p (Hr p), o.1 < κ p)
    (hfin' : ∀ p, (∀ e ∈ Hr' p, e.1 < κ p) ∧ ∀ o ∈ A.beh p (Hr' p), o.1 < κ p)
    (hmsg : ∀ q r₀ σ (m : M), (σ, OutEv.send r₀ m) ∈ A.beh q (Hr q) →
      σ - s.off q + s.delay q r₀ (σ - s.off q) < κ r₀ - s.off r₀)
    (hmsg' : ∀ q r₀ σ (m : M), (σ, OutEv.send r₀ m) ∈ A.beh q (Hr' q) →
      σ - s.off q + s'.delay q r₀ (σ - s.off q) < κ r₀ - s.off r₀)
    (C : P → ℝ)
    (hcalls : ∀ p (e : ℝ × InEv P I M), κ p ≤ e.1 → e.1 - s.off p < C p →
      (e ∈ s.callEv p ↔ e ∈ s'.callEv p))
    (hdel : ∀ q r₀ σ, κ q - s.off q ≤ σ → σ < C q → s.delay q r₀ σ = s'.delay q r₀ σ ∨
      (C r₀ ≤ σ + s.delay q r₀ σ ∧ C r₀ ≤ σ + s'.delay q r₀ σ))
    (hcut : ∀ q r₀ σ, C q ≤ σ → C r₀ ≤ σ + s.delay q r₀ σ ∧ C r₀ ≤ σ + s'.delay q r₀ σ) :
    (∀ p (e : ℝ × InEv P I M), κ p ≤ e.1 → e.1 - s.off p < C p → (e ∈ H p ↔ e ∈ H' p)) ∧
    ∀ p (o : ℝ × OutEv P R M), κ p ≤ o.1 → o.1 - s.off p < C p →
      (o ∈ A.beh p (H p) ↔ o ∈ A.beh p (H' p)) := by
  have pre1 : ∀ p, H p ∩ {e | e.1 < κ p - s.off p + s.off p} = Hr p := by
    intro p; ext e
    simp only [sub_add_cancel, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => (hagr p e h2).mp h1,
      fun h => ⟨(hagr p e ((hfin p).1 e h)).mpr h, (hfin p).1 e h⟩⟩
  have pre2 : ∀ p, H' p ∩ {e | e.1 < κ p - s.off p + s.off p} = Hr' p := by
    intro p; ext e
    simp only [sub_add_cancel, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => (hagr' p e h2).mp h1,
      fun h => ⟨(hagr' p e ((hfin' p).1 e h)).mpr h, (hfin' p).1 e h⟩⟩
  have hres : ∀ p, SameResidual (A.beh p) (Hr p) (Hr' p) (κ p) := fun p =>
    hHO r r' Hr Hr' p₀ ρ hra hra' hHr hHr' hwr hwr' hso hso' p (κ p) (hfin p).1
        (hfin' p).1 (hfin p).2 (hfin' p).2
  have key := agree_window A s s' hoff hH hH' hγ (fun p => κ p - s.off p) C
    (fun p => by rw [pre1, pre2, sub_add_cancel]; exact hres p)
    (fun q r₀ σ m hσ => by
      simp only [sub_add_cancel] at hσ
      refine ⟨fun ho => hmsg q r₀ σ m ?_, fun ho => hmsg' q r₀ σ m ?_⟩
      · exact (beh_agree A q (fun e he => hagr q e he) _ hσ).mp ho
      · exact (beh_agree A q (fun e he => hagr' q e he) _ hσ).mp ho)
    (fun p e hQ hC => hcalls p e (by linarith) hC) hdel hcut
  have hin : ∀ p (e : ℝ × InEv P I M), κ p ≤ e.1 → e.1 - s.off p < C p → (e ∈ H p ↔ e ∈ H' p) :=
    fun p e hκ hC => key p e (by linarith) hC
  refine ⟨hin, fun p o hκ hC => ?_⟩
  have split : ∀ (G : Set (ℝ × InEv P I M)) (G₀ : Set (ℝ × InEv P I M)),
      (∀ e, e.1 < κ p → (e ∈ G ↔ e ∈ G₀)) → (∀ e ∈ G₀, e.1 < κ p) →
      G = G₀ ∪ (G ∩ {e | κ p ≤ e.1}) := by
    intro G G₀ h1 h2; ext e
    by_cases he : e.1 < κ p
    · simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, not_le.mpr he, and_false,
        or_false]
      exact h1 e he
    · push_neg at he
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, he, and_true]
      exact ⟨Or.inr, fun h => h.elim (fun h' => absurd (h2 e h') (not_lt.mpr he)) id⟩
  rw [split (H p) (Hr p) (hagr p) (hfin p).1, split (H' p) (Hr' p) (hagr' p) (hfin' p).1]
  rw [hres p _ (fun e he => he.2) o hκ]
  refine A.causal p _ _ o.1 (fun e he => ?_) o le_rfl
  by_cases hk : e.1 < κ p
  · simp [hk, not_le.mpr hk]
  · push_neg at hk
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, hk, and_true]
    have := hin p e hk (by linarith)
    constructor
    · rintro (h | h)
      · exact absurd ((hfin' p).1 e h) (not_lt.mpr hk)
      · exact Or.inr (this.mp h)
    · rintro (h | h)
      · exact absurd ((hfin' p).1 e h) (not_lt.mpr hk)
      · exact Or.inr (this.mpr h)

/-- Well-formedness of a `ρ`-phase followed by operations of pairwise distinct processes. -/
theorem wf_rho_cont {legal : List (I × R) → Prop} {d u ε Bop g γ : ℝ}
    (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop) (hg : Bop < g)
    (hg0 : 0 < g) {p₀ : P} {ρ : List (I × R)} {cont : List (Call P I)}
    (hcp : cont.Pairwise (fun c c' => c.p ≠ c'.p)) (hck : ∀ c ∈ cont, ρ.length ≤ c.k)
    (hct : ∀ c ∈ cont, ρ.length * g ≤ c.t)
    (s : Scenario P I) (hs : s.calls = rhoCalls p₀ g ρ ++ cont) (hadm : s.Admissible d u ε)
    (hγ : s.MinDelay γ) : ∀ H, IsRun A s H → WF A s H := by
  have hρk : ∀ c ∈ rhoCalls p₀ g ρ, c.k < ρ.length := fun c hc => (mem_rhoCalls hc).2.1
  have hρt : ∀ c ∈ rhoCalls p₀ g ρ, c.t + Bop < ρ.length * g := fun c hc => by
    rw [(mem_rhoCalls hc).2.2]
    have : ((c.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hρk c hc
    push_cast at this; nlinarith
  have hρρ : ∀ c ∈ rhoCalls p₀ g ρ, ∀ c' ∈ rhoCalls p₀ g ρ, c.k = c'.k → c = c' := by
    intro c hc c' hc' hk
    by_contra hne
    have hpw : (rhoCalls p₀ g ρ).Pairwise (fun a b => a.k ≠ b.k) :=
      (pairwise_rhoCallsFrom 0 ρ).imp fun h => Nat.ne_of_lt h
    haveI : Std.Symm (fun a b : Call P I => a.k ≠ b.k) := ⟨fun a b h => Ne.symm h⟩
    exact hpw.forall hc hc' hne hk
  have hcc : ∀ c ∈ cont, ∀ c' ∈ cont, c.p = c'.p → c = c' := by
    intro c hc c' hc' hp
    by_contra hne
    haveI : Std.Symm (fun a b : Call P I => a.p ≠ b.p) := ⟨fun a b h => Ne.symm h⟩
    exact hcp.forall hc hc' hne hp
  refine wf_of_spaced A hcor hB s hadm hγ ?_ ?_ ?_ ?_
  · rw [hs]
    refine List.nodup_append.mpr ⟨nodup_rhoCalls p₀ g ρ, ?_, ?_⟩
    · refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab hab' => hab (hab' ▸ rfl)) hcp
    · intro a ha b hb hab; subst hab; have := hρk a ha; have := hck a hb; omega
  · intro c hc c' hc' hp hk
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · exact hρρ c hc c' hc' hk
    · have := hρk c hc; have := hck c' hc'; omega
    · have := hρk c' hc'; have := hck c hc; omega
    · exact hcc c hc c' hc' hp
  · intro c hc c' hc' hp hne ht
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · rw [(mem_rhoCalls hc).2.2, (mem_rhoCalls hc').2.2] at ht ⊢
      have hk : c.k ≠ c'.k := fun h => hne (hρρ c hc c' hc' h)
      have hk' : c.k < c'.k := by
        rcases Nat.lt_or_gt_of_ne hk with h | h
        · exact h
        · exfalso
          have : (c'.k : ℝ) < c.k := by exact_mod_cast h
          nlinarith
      have : ((c.k + 1 : ℕ) : ℝ) ≤ c'.k := by exact_mod_cast hk'
      push_cast at this; nlinarith
    · have := hρt c hc; have := hct c' hc'; linarith
    · have := hρt c' hc'; have := hct c hc; linarith
    · exact absurd (hcc c hc c' hc' hp) hne
  · intro c hc c' hc' hp ht
    rw [hs, List.mem_append] at hc hc'
    rcases hc with hc | hc <;> rcases hc' with hc' | hc'
    · rw [(mem_rhoCalls hc).2.2, (mem_rhoCalls hc').2.2] at ht
      have : (c.k : ℝ) = c'.k := by
        rcases mul_eq_mul_right_iff.mp ht with h | h
        · exact h
        · linarith
      exact hρρ c hc c' hc' (by exact_mod_cast this)
    · have := hρt c hc; have := hct c' hc'
      have : Bop < 0 ∨ 0 ≤ Bop := lt_or_ge Bop 0
      exfalso
      have h0 : 0 ≤ c.t := by rw [(mem_rhoCalls hc).2.2]; positivity
      have h1 : c.t < ρ.length * g := by
        rw [(mem_rhoCalls hc).2.2]
        have : ((c.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hρk c hc
        push_cast at this; nlinarith
      linarith
    · exfalso
      have h1 : c'.t < ρ.length * g := by
        rw [(mem_rhoCalls hc').2.2]
        have : ((c'.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hρk c' hc'
        push_cast at this; nlinarith
      have := hct c hc; linarith
    · exact hcc c hc c' hc' hp

end ContLin

end Podc.SharedObjectTimeBounds
