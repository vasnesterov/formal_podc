import Papers.PODC2020.AsyncApproxBCDirected.Operational.RefineComp

/-!
# Every fair run of the operational algorithm yields round executions

* `mkRound` — round `r < N` of a fair run with `|B| ≤ f`, once all correct nodes start it, is a
  `RoundExec` (all communication-layer hypotheses are proved, none assumed).
* `verify_iff` — the abstract `Verify` is the operational one.
* `started_succ` — by Theorem 9, every correct node starts round `r + 1`; its value is an
  abstract output of round `r` (`output_next`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

namespace BWOp

variable {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (f N : ℕ)
  (B : Finset V) (inp : V → ℝ) (ev : ℕ → Event V (BMsg V))

/-- All correct nodes eventually start round `r`. -/
def Started (r : ℕ) : Prop :=
  ∀ s ∉ B, ∃ t, (xv G f N s (inp s) r (hst G f N B inp ev t s)).isSome

variable {G f N B inp ev} in
/-- Round `r` of a fair run, as a `RoundExec`. -/
noncomputable def mkRound (r : ℕ) (hr : r < N) (hB : B.card ≤ f)
    (hfair : Fair (alg G f N) G B inp ev) (hst : Started G f N B inp ev r) : RoundExec G f where
  F := B
  card_F := hB
  x := Xr G f N B inp ev r
  M := Mr G f N B inp ev r
  acc := accR G f N B inp ev r
  CR := CRr G f N B inp ev r
  idx := idxR G f N B inp ev r
  M_mono v := Mr_mono G f N B inp ev r v
  M_last _ _ t m hm := M_last' G f N B inp ev r t m hm
  M_first _ hv t y p hm := M_first' G f N B inp ev r hv t y p hm
  M_honest _ hv t y p hm hp := M_honest' G f N B inp ev r hv t y p hm hp
  acc_self s _ := accR_single G f N B inp ev r s
  acc_snoc p q w hq hqB := acc_snoc' G f N B inp ev r p q w hq hqB
  M_src _ hv t y p q hm hq hqB := M_src' G f N B inp ev r hv t y p q hm hq hqB
  M_live_self s hs := M_live_self' G f N B inp ev r (hst s hs)
  M_live _ hv p q hq hqB hadj hqv hred hacc := M_live' r hr hfair hv p q hq hqB hadj hqv hred hacc
  CR_mono v _ _ h := CRop_mono G f N v (inp v) r (hst_prefix G f N B inp ev h v)
  CR_honest _ hv t c p Mc F' hm hp := CR_honest' G f N B inp ev r hv t c p Mc F' hm hp
  CR_fifo _ hv t c p Mc F' F'' hm hp hs h := CR_fifo' G f N B inp ev r hv t c p Mc F' F'' hm hp hs h
  CR_live _ hv c p F' hs hp hpB := CR_live' r hr hfair hv c p F' hs hp hpB
  idx_inj c _ F₁ F₂ h₁ h₂ h := idx_inj' G f N B inp ev r c F₁ F₂ h₁ h₂ h

section Corr

variable {G f N B inp ev} {r : ℕ} {hr : r < N} {hB : B.card ≤ f}
  {hfair : Fair (alg G f N) G B inp ev} {hs : Started G f N B inp ev r}

theorem fifoRecAll_iff {v : V} {Fv : Finset V} {t : ℕ} :
    (mkRound r hr hB hfair hs).FIFORecAll v Fv t ↔
      FIFORecAllOp G f v r (ownF G f N inp v r) (hst G f N B inp ev t v) Fv := Iff.rfl

/-- The abstract `Verify` is the operational one. -/
theorem verify_iff {v : V} {Fv : Finset V} {t : ℕ} :
    (mkRound r hr hB hfair hs).Verify v Fv t ↔
      VerifyOp G f v r (ownF G f N inp v r) (hst G f N B inp ev t v) Fv := by
  unfold RoundExec.Verify VerifyOp
  apply and_congr _ Iff.rfl
  constructor
  · rintro ⟨t', ht', hf⟩
    refine ⟨(hst G f N B inp ev t' v).length, (hst_prefix G f N B inp ev ht' v).length_le, ?_⟩
    rw [← List.prefix_iff_eq_take.mp (hst_prefix G f N B inp ev ht' v)]
    exact hf
  · rintro ⟨k, -, hf⟩
    obtain ⟨t', ht', heq⟩ := take_hst_exists G f N B inp ev (c := v) (t := t) (k := k)
    exact ⟨t', ht', by rw [fifoRecAll_iff, heq]; exact hf⟩

end Corr

/-- Under 3-reach, in a fair run, every correct node that started round `r < N` eventually starts
round `r + 1`, with a value that is a possible output of the abstract round `r`. -/
theorem output_next (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {r : ℕ} (hr : r < N)
    (hB : B.card ≤ f) (hfair : Fair (alg G f N) G B inp ev) (hs : Started G f N B inp ev r)
    {v : V} (hv : v ∉ B) :
    ∃ t y, xv G f N v (inp v) (r + 1) (hst G f N B inp ev t v) = some y ∧
      (mkRound r hr hB hfair hs).Output v y := by
  classical
  set E := mkRound r hr hB hfair hs
  obtain ⟨Fv, t, ev'⟩ := E.exists_executes hG hn (v := v) hv
  have hver : VerifyOp G f v r (ownF G f N inp v r) (hst G f N B inp ev t v) Fv :=
    verify_iff.mp ev'.2.2.1
  -- the operational first verified prefix
  set h := hst G f N B inp ev t v
  have hexk : ∃ k, k ≤ h.length ∧ ∃ F' : Finset V, v ∉ F' ∧ F'.card ≤ f ∧
      VerifyOp G f v r (ownF G f N inp v r) (h.take k) F' :=
    ⟨h.length, le_rfl, Fv, ev'.1, ev'.2.1, by rw [List.take_length]; exact hver⟩
  rcases hfa : faK G f v r (ownF G f N inp v r) h with _ | k
  · exfalso
    obtain ⟨k, hk, hP⟩ := hexk
    exact (firstIdx_eq_none.mp hfa) k hk hP
  obtain ⟨hkl, ⟨F₀, hF₀, hF₀c, hP₀⟩, hmin⟩ := firstIdx_eq_some.mp hfa
  -- the first time the history is `h.take k`
  have hext : ∃ s, hst G f N B inp ev s v = h.take k := by
    obtain ⟨s, -, hs'⟩ := take_hst_exists G f N B inp ev (c := v) (t := t) (k := k)
    exact ⟨s, hs'⟩
  set s₀ := Nat.find hext
  have hs₀ : hst G f N B inp ev s₀ v = h.take k := Nat.find_spec hext
  have hs₀t : s₀ ≤ t := by
    obtain ⟨s, hst', hs'⟩ := take_hst_exists G f N B inp ev (c := v) (t := t) (k := k)
    exact (Nat.find_min' hext hs').trans hst'
  have hexec : E.Executes v F₀ s₀ := by
    refine ⟨hF₀, hF₀c, verify_iff.mpr (by rw [hs₀]; exact hP₀), fun s' hs' F' h1 h2 h3 => ?_⟩
    have hpre : hst G f N B inp ev s' v <+: h.take k := by
      rw [← hs₀]; exact hst_prefix G f N B inp ev hs'.le v
    have hne : hst G f N B inp ev s' v ≠ h.take k := fun he => Nat.find_min hext hs' he
    have hlt : (hst G f N B inp ev s' v).length < k := by
      have := hpre.length_le
      rcases this.lt_or_eq with h' | h'
      · simpa [hkl] using h'
      · exact absurd (hpre.eq_of_length (by simpa using h')) hne
    apply hmin _ hlt ⟨F', h1, h2, ?_⟩
    rw [verify_iff] at h3
    have : h.take (hst G f N B inp ev s' v).length = hst G f N B inp ev s' v := by
      rw [← List.prefix_iff_eq_take.mp (hpre.trans (List.take_prefix _ _))]
    rwa [this]
  -- the value computed by Filter-and-Average
  have hown : ∃ m ∈ E.M v s₀, m.2 = [v] := by
    obtain ⟨hsent, htm⟩ := E.executes_sent hv hexec
    obtain ⟨y, hy⟩ := (hsent.full G f) [v] isSimplePath_singleton.isRedundant
      (by simpa [Avoids] using hsent.1) (by simp)
    exact ⟨(y, [v]), E.mcMsg_subset htm hy, rfl⟩
  obtain ⟨y₀, hy₀⟩ := IsFA.exists (f := f) hown
  have hfaOut : IsFA f v (E.M v s₀) (faOut f v (E.M v s₀)) := by
    have hex : ∃ y, IsFA f v (E.M v s₀) y := ⟨y₀, hy₀⟩
    simp only [faOut, hex, dite_true]
    exact Classical.choose_spec hex
  have hMs₀ : E.M v s₀ = recvM v r (xv G f N v (inp v) r (h.take k)) (h.take k) := by
    show Mr G f N B inp ev r v s₀ = _
    simp only [Mr]; rw [hs₀]
  refine ⟨t, faOut f v (E.M v s₀), ?_, F₀, s₀, hexec, hfaOut⟩
  simp only [xv, hr, ite_true]
  show (match faK G f v r (ownF G f N inp v r) h with
    | some k => some (faOut f v (recvM v r (xv G f N v (inp v) r (h.take k)) (h.take k)))
    | none => none) = _
  rw [hfa, hMs₀]

theorem started_zero : Started G f N B inp ev 0 := fun s _ => ⟨0, by simp [xv]⟩

theorem started_succ (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) {r : ℕ} (hr : r < N)
    (hB : B.card ≤ f) (hfair : Fair (alg G f N) G B inp ev) (hs : Started G f N B inp ev r) :
    Started G f N B inp ev (r + 1) := fun v hv => by
  obtain ⟨t, y, hy, -⟩ := output_next G f N B inp ev hG hn hr hB hfair hs hv
  exact ⟨t, by simp [hy]⟩

theorem started_all (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (hB : B.card ≤ f)
    (hfair : Fair (alg G f N) G B inp ev) : ∀ r ≤ N, Started G f N B inp ev r := by
  intro r
  induction r with
  | zero => intro _; exact started_zero G f N B inp ev
  | succ r ih => intro hr; exact started_succ G f N B inp ev hG hn (by omega) hB hfair (ih (by omega))

end BWOp

end AsyncApproxBCDirected
