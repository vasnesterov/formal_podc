import Papers.PODC2025.LanguageDecidability.CounterDefs

/-!
# Counterexamples around Example 3, Figure 5 and Lemmas 5.2, 5.3

All counterexamples are for `n = 2` processes (`p₀, p₁`; the paper's `p₁, p₂`). They use the
family `fam b v0 c` of round-robin words: in round `j` (positions `4j … 4j+3`) process `p₀`
does `inc` if `b j` and otherwise a `read` returning `v0 j`, then `p₁` does a `read` returning
`c`. The generic facts (well-formedness, typedness, properties (1)–(3)) are proved once for the
family.

1. **Figure 5 is wrong** (`fig5_not_weaklyDecides`, `fig5_not_weakAllDecides`): the second
   clause of Line 06 (`curr_read < snap[i] ∨ curr_read < prev_read`) is also evaluated in
   iterations whose operation is an `inc`, where `curr_read` is stale (initially `0`). In
   `x5 = <₀⁺ >₀ <₁ >₁¹ (<₀ >₀¹ <₁ >₁¹)^ω ∈ WEC_COUNT` (even `∈ SEC_COUNT`, `x5_mem_SEC`), process
   `p₀` sets its flag in its first iteration and reports `NO` forever (`fig5_noSet_infinite`).
2. **Lemma 5.3 fails for the literal reading of property (3)** (`not_WD_WEClit`): read literally,
   property (3) is vacuous when there are infinitely many `inc`s. A diagonal argument (as for
   `ω`-regular non-`Π₂` sets): starting from words "finite prefix with `≥ 1` increments of `p₀`,
   then `p₀` reads its own count and `p₁` reads `0` forever" (not in `WEClit`, so `p₀` reports
   `NO` infinitely often), we insert a new increment of `p₀` after each forced `NO`. The limit
   word has infinitely many increments and satisfies (1), (2), so it is in `WEClit`, yet `p₀`
   reports `NO` infinitely often in its canonical execution (causality of `canon`).
3. **The word in the proof of Lemma 5.2 is unsuitable** (`xPaper_cut_not_mem`): the paper's
   `x = <₁⁺ >₁ <₂ >₂⁰ <₁ >₁⁰ …` violates property (1) at position 5 (`p₁` reads `0` after its
   own `inc`), so for every prefix `x(F)` containing that symbol, every continuation (in
   particular the paper's `x'`) is outside `WEC_COUNT`, and no contradiction is reached.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability

/-! ### A family of two-process counter words -/

/-- `oi b j`: the number of rounds `j' < j` with `b j' = true`. -/
def oi (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => oi b j + if b j then 1 else 0

/-- Round `j` (positions `4j … 4j+3`): `p₀` does `inc` if `b j`, otherwise a `read` returning
`v0 j`; then `p₁` does a `read` returning `c`. -/
def fam (b : ℕ → Bool) (v0 : ℕ → ℕ) (c : ℕ) : CWord 2 := fun m =>
  if m % 4 = 0 then ⟨0, .inl (if b (m / 4) then .inc else .read)⟩
  else if m % 4 = 1 then ⟨0, .inr (if b (m / 4) then .ack else .val (v0 (m / 4)))⟩
  else if m % 4 = 2 then ⟨1, .inl .read⟩
  else ⟨1, .inr (.val c)⟩

section fam

variable (b : ℕ → Bool) (v0 : ℕ → ℕ) (c : ℕ)

/-! #### The four symbols of a round -/

lemma fam0 (j : ℕ) : fam b v0 c (4 * j) = ⟨0, .inl (if b j then .inc else .read)⟩ := by
  simp only [fam, show 4 * j % 4 = 0 by omega, show 4 * j / 4 = j by omega, ↓reduceIte]

lemma fam1 (j : ℕ) :
    fam b v0 c (4 * j + 1) = ⟨0, .inr (if b j then .ack else .val (v0 j))⟩ := by
  simp only [fam, show (4 * j + 1) % 4 = 1 by omega, show (4 * j + 1) / 4 = j by omega]
  rfl

lemma fam2 (j : ℕ) : fam b v0 c (4 * j + 2) = ⟨1, .inl .read⟩ := by
  simp only [fam, show (4 * j + 2) % 4 = 2 by omega]
  rfl

lemma fam3 (j : ℕ) : fam b v0 c (4 * j + 3) = ⟨1, .inr (.val c)⟩ := by
  simp only [fam, show (4 * j + 3) % 4 = 3 by omega]
  rfl

/-- The process of the symbol at position `m`. -/
lemma fam_proc (m : ℕ) : (fam b v0 c m).1 = if m % 4 < 2 then 0 else 1 := by
  unfold fam; split_ifs <;> first | rfl | omega

lemma cnt_fam0 (m : ℕ) : cnt (fam b v0 c) 0 m = 2 * (m / 4) + min (m % 4) 2 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cnt_succ, ih, fam_proc]
    by_cases h : m % 4 < 2
    · simp only [h, ite_true]; omega
    · simp only [h, ite_false]; simp; omega

lemma cnt_fam1 (m : ℕ) : cnt (fam b v0 c) 1 m = 2 * (m / 4) + (m % 4 - 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [cnt_succ, ih, fam_proc]
    by_cases h : m % 4 < 2
    · simp only [h, ite_true]; simp; omega
    · simp only [h, ite_false]; simp; omega

lemma fam_decomp (m : ℕ) : ∃ j r, r < 4 ∧ m = 4 * j + r := ⟨m / 4, m % 4, by omega, by omega⟩

/-- Every word of the family is well formed (Definition 2.1). -/
lemma wf_fam : WF (fam b v0 c) where
  reliable p N := by
    fin_cases p
    · exact ⟨4 * N, by omega, by rw [fam0]; rfl⟩
    · exact ⟨4 * N + 2, by omega, by rw [fam2]; rfl⟩
  seq m := by
    obtain ⟨j, r, hr, rfl⟩ := fam_decomp m
    interval_cases r
    · rw [add_zero, fam0, cnt_fam0]; simp
    · rw [fam1, cnt_fam0]; simp
    · rw [fam2, cnt_fam1]; simp
    · rw [fam3, cnt_fam1]; simp

/-- Inversion: the responses of the family. -/
lemma fam_inr {r : ℕ} {p : Fin 2} {w : CRes} (h : fam b v0 c r = ⟨p, .inr w⟩) :
    (r % 4 = 1 ∧ p = 0 ∧ w = if b (r / 4) then .ack else .val (v0 (r / 4))) ∨
      (r % 4 = 3 ∧ p = 1 ∧ w = .val c) := by
  obtain ⟨j, k, hk, rfl⟩ := fam_decomp r
  interval_cases k
  · rw [add_zero, fam0] at h; simp at h
  · rw [fam1] at h; simp at h
    left; refine ⟨by omega, h.1.symm, ?_⟩
    rw [show (4 * j + 1) / 4 = j by omega]; exact h.2.symm
  · rw [fam2] at h; simp at h
  · rw [fam3] at h; simp at h
    right; exact ⟨by omega, h.1.symm, h.2.symm⟩

lemma fam_val {r : ℕ} {p : Fin 2} {v : ℕ} (h : fam b v0 c r = ⟨p, .inr (.val v)⟩) :
    (r % 4 = 1 ∧ p = 0 ∧ b (r / 4) = false ∧ v = v0 (r / 4)) ∨ (r % 4 = 3 ∧ p = 1 ∧ v = c) := by
  rcases fam_inr b v0 c h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left; refine ⟨h1, h2, ?_⟩
    cases hb : b (r / 4) <;> simp [hb] at h3; exact ⟨rfl, h3⟩
  · right; exact ⟨h1, h2, by simpa using h3⟩

lemma isInc_fam (m : ℕ) : IsInc (fam b v0 c m) ↔ m % 4 = 0 ∧ b (m / 4) = true := by
  obtain ⟨j, k, hk, rfl⟩ := fam_decomp m
  interval_cases k
  · rw [add_zero, fam0]; cases hb : b j <;> simp [IsInc, hb]
  · rw [fam1]; simp [IsInc]
  · rw [fam2]; simp [IsInc]
  · rw [fam3]; simp [IsInc]

/-- Every operation of the family is `inc : ack` or `read : val v`. -/
lemma typed_fam : Typed (fam b v0 c) := by
  intro r i p w hr ⟨hir, hpi, hbet⟩
  obtain ⟨j, k, hk, rfl⟩ := fam_decomp r
  interval_cases k
  · rw [add_zero, fam0] at hr; simp at hr
  · have hi : i = 4 * j := by
      by_contra hne
      exact hbet (4 * j) (by omega) (by omega) (by rw [fam0, fam1])
    subst hi; rw [fam1] at hr; rw [fam0]
    cases hb : b j <;> simp [hb] at hr ⊢ <;> obtain ⟨rfl, rfl⟩ := hr <;> simp
  · rw [fam2] at hr; simp at hr
  · have hi : i = 4 * j + 2 := by
      by_contra hne
      exact hbet (4 * j + 2) (by omega) (by omega) (by rw [fam2, fam3])
    subst hi; rw [fam3] at hr; rw [fam2]
    simp at hr; obtain ⟨rfl, rfl⟩ := hr; simp

lemma ownIncs_succ (x : CWord 2) (p : Fin 2) (k : ℕ) :
    ownIncs x p (k + 1) = ownIncs x p k + if IsInc (x k) ∧ (x k).1 = p then 1 else 0 := rfl

lemma incs_succ (x : CWord 2) (k : ℕ) :
    incs x (k + 1) = incs x k + if IsInc (x k) then 1 else 0 := rfl

lemma ownIncs_fam0 (j : ℕ) : ownIncs (fam b v0 c) 0 (4 * j) = oi b j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, ownIncs_succ, ownIncs_succ, ownIncs_succ,
      ownIncs_succ, fam3, fam2, fam1, fam0, ih, oi]
    cases b j <;> simp [IsInc]

lemma ownIncs_fam0' (j : ℕ) (hb : b j = false) : ownIncs (fam b v0 c) 0 (4 * j + 1) = oi b j := by
  rw [ownIncs_succ, ownIncs_fam0, fam0]; simp [hb, IsInc]

lemma ownIncs_fam1 (m : ℕ) : ownIncs (fam b v0 c) 1 m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have : ¬ (IsInc (fam b v0 c m) ∧ (fam b v0 c m).1 = 1) := by
      rintro ⟨hi, hp⟩
      rw [isInc_fam] at hi
      rw [fam_proc] at hp
      simp [show m % 4 < 2 by omega] at hp
    rw [ownIncs_succ, ih]; simp only [this, ite_false]

lemma incs_fam (j : ℕ) : incs (fam b v0 c) (4 * j) = oi b j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 4 * (j + 1) = 4 * j + 3 + 1 by ring, incs_succ, incs_succ, incs_succ,
      incs_succ, fam3, fam2, fam1, fam0, ih, oi]
    cases b j <;> simp [IsInc]

/-- Property (1) for the family: `p₀`'s reads return at least its own number of increments. -/
lemma wec1_fam (hv : ∀ j, b j = false → oi b j ≤ v0 j) : WEC1 (fam b v0 c) := by
  intro r p v hr
  rcases fam_val b v0 c hr with ⟨h1, rfl, h3, rfl⟩ | ⟨h1, rfl, rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, r = 4 * j + 1 := ⟨r / 4, by omega⟩
    rw [show (4 * j + 1) / 4 = j by omega] at h3 ⊢
    rw [ownIncs_fam0' b v0 c _ h3]
    exact hv _ h3
  · rw [ownIncs_fam1]; exact Nat.zero_le _

/-- Property (2) for the family: `p₀`'s read values are monotone. -/
lemma wec2_fam (hv : ∀ j j', j' < j → b j' = false → b j = false → v0 j' ≤ v0 j) :
    WEC2 (fam b v0 c) := by
  intro r r' p v v' hlt hr' hr
  rcases fam_val b v0 c hr with ⟨h1, hp, h3, hv1⟩ | ⟨h1, hp, hv1⟩ <;>
    rcases fam_val b v0 c hr' with ⟨h1', hp', h3', hv1'⟩ | ⟨h1', hp', hv1'⟩
  · subst hv1 hv1'; exact hv _ _ (by omega) h3' h3
  · rw [hp] at hp'; simp at hp'
  · rw [hp] at hp'; simp at hp'
  · rw [hv1, hv1']

/-- No increments from round `J` on: there are `oi b J` increments in total. -/
lemma finIncs_fam {J : ℕ} (hJ : ∀ j, J ≤ j → b j = false) : FinIncs (fam b v0 c) (oi b J) :=
  ⟨4 * J, incs_fam b v0 c J, fun m hm h => by
    rw [isInc_fam] at h; rw [hJ (m / 4) (by omega)] at h; simp at h⟩

/-- Infinitely many increments. -/
lemma not_finIncs_fam (hb : ∀ J, ∃ j, J ≤ j ∧ b j = true) (S : ℕ) :
    ¬ FinIncs (fam b v0 c) S := by
  rintro ⟨N, -, hN⟩
  obtain ⟨j, hj, hbj⟩ := hb N
  exact hN (4 * j) (by omega) ((isInc_fam b v0 c _).2 ⟨by omega, by simpa using hbj⟩)

/-- `p₁` reads `c` forever, so reads do not eventually return `S ≠ c`. -/
lemma not_evReads_fam {S : ℕ} (hS : c ≠ S) : ¬ EvReads (fam b v0 c) S := by
  rintro ⟨N, hN⟩
  exact hS (hN (4 * N + 3) 1 c (by omega) (fam3 b v0 c N))

end fam

lemma oi_mono (b : ℕ → Bool) {j j' : ℕ} (h : j ≤ j') : oi b j ≤ oi b j' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [oi]; omega

lemma oi_congr {b b' : ℕ → Bool} {J : ℕ} (h : ∀ j < J, b j = b' j) : oi b J = oi b' J := by
  induction J with
  | zero => rfl
  | succ J ih => rw [oi, oi, ih (fun j hj => h j (by omega)), h J (by omega)]

/-! ### Figure 5 as written: the flag is monotone -/

section fig5

variable {n : ℕ}

/-- The flag of Figure 5 is never reset (any schedule). -/
lemma flag_step (s : ℕ → Ev (n := n) (fun _ => CInv) (fun _ => CRes)) (t : ℕ) (p : Fin n)
    (h : Loc.flag (((fig5Alg (n := n)).run s t).loc p) = true) :
    Loc.flag (((fig5Alg (n := n)).run s (t + 1)).loc p) = true := by
  simp only [Alg.run]
  cases hs : s t with
  | pre q v =>
    simp only [Alg.next]
    by_cases hq : p = q
    · subst hq; rw [Function.update_self]
      cases v <;> simpa [fig5Alg, pre5] using h
    · rw [Function.update_of_ne hq]; exact h
  | send q v => exact h
  | recv q w => exact h
  | post q w =>
    simp only [Alg.next]
    by_cases hq : p = q
    · subst hq; rw [Function.update_self]
      simp only [fig5Alg, post5] at h ⊢
      simp [h]
    · rw [Function.update_of_ne hq]; exact h

lemma flag_mono (s : ℕ → Ev (n := n) (fun _ => CInv) (fun _ => CRes)) {t : ℕ} (p : Fin n)
    (h : Loc.flag (((fig5Alg (n := n)).run s t).loc p) = true) :
    ∀ t', t ≤ t' → Loc.flag (((fig5Alg (n := n)).run s t').loc p) = true := by
  intro t' ht'
  induction ht' with
  | refl => exact h
  | step _ ih => exact flag_step s _ p ih

/-- Once the flag is set, every Line 06 of the process reports `NO`. -/
lemma outs_of_flag (s : ℕ → Ev (n := n) (fun _ => CInv) (fun _ => CRes)) {t : ℕ} {p : Fin n}
    {w : CRes} (h : Loc.flag (((fig5Alg (n := n)).run s t).loc p) = true) (hs : s t = .post p w) :
    (fig5Alg (n := n)).outs s t = some (p, .no) := by
  simp only [Alg.outs, hs, Alg.next]
  simp only [fig5Alg, post5] at h ⊢
  simp [h]

end fig5

/-- The counterexample word for Figure 5: `p₀` increments once and then reads `1` forever,
`p₁` reads `1` forever. -/
def x5 : CWord 2 := fam (fun j => decide (j = 0)) (fun _ => 1) 1

lemma oi_x5 (j : ℕ) : oi (fun j => decide (j = 0)) j = min j 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [oi, ih]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; rfl
    · simp [show j ≠ 0 by omega]; omega

lemma incs_mono (x : CWord n) {k m : ℕ} (h : k ≤ m) : incs x k ≤ incs x m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [incs]; omega

/-- The word `x5` is a weakly-eventual (even strongly-eventual) consistent counter history:
`p₀`'s increment precedes all `read`s and every `read` returns `1`. -/
lemma x5_mem_SEC : x5 ∈ (SEC : Set (CWord 2)) := by
  have hv : ∀ r p v, x5 r = ⟨p, .inr (.val v)⟩ → v = 1 ∧ 1 ≤ r := by
    intro r p v h
    rcases fam_val _ _ _ h with ⟨h1, -, -, rfl⟩ | ⟨h1, -, rfl⟩
    · exact ⟨rfl, by omega⟩
    · exact ⟨rfl, by omega⟩
  refine ⟨⟨wf_fam _ _ _, typed_fam _ _ _, wec1_fam _ _ _ ?_, wec2_fam _ _ _ ?_, ?_⟩, ?_⟩
  · intro j _; rw [oi_x5]; omega
  · intro _ _ _ _ _; exact le_rfl
  · refine ⟨1, ?_, 0, fun r p v _ h => (hv r p v h).1⟩
    have := finIncs_fam (fun j => decide (j = 0)) (fun _ => 1) 1 (J := 1)
      (fun j hj => by simp; omega)
    exact this
  · intro r p v h
    obtain ⟨rfl, hr⟩ := hv r p v h
    exact le_trans (by rfl) (incs_mono x5 hr)

lemma x5_mem_WEC : x5 ∈ (WEC : Set (CWord 2)) := x5_mem_SEC.1

/-- After its first iteration (an `inc`), process `p₀` has set its flag. -/
lemma flag_x5 : Loc.flag (((fig5Alg (n := 2)).run (canon x5) 4).loc 0) = true := by
  rfl

/-- **Figure 5 is wrong**: in the canonical execution of `x5 ∈ WEC_COUNT`, process `p₀`
reports `NO` infinitely often under the algorithm of Figure 5 (literally). In the `inc`
iteration, Line 06 compares the stale `curr_read = 0` with `snap[0] = 1` and sets the flag. -/
theorem fig5_noSet_infinite : (NoSet ((fig5Alg (n := 2)).outs (canon x5)) 0).Infinite := by
  rw [infinite_iff_frequently]
  intro N
  refine ⟨8 * (N + 1) + 3, by omega, ?_⟩
  have hflag := flag_mono _ 0 flag_x5 (8 * (N + 1) + 3) (by omega)
  refine outs_of_flag _ hflag (w := .val 1) ?_
  rw [show 8 * (N + 1) + 3 = 2 * (4 * (N + 1) + 1) + 1 by ring, canon_odd, x5, fam1]
  simp [ev1]

/-- **Figure 5 does not weakly-all decide `WEC_COUNT`** (contrary to the proof of Lemma 5.3). -/
theorem fig5_not_weakAllDecides : ¬ WeakAllDecides (fig5Alg (n := 2)) WEC := fun h =>
  fig5_noSet_infinite ((h (canon x5) x5 (isExec_canon (wf_fam _ _ _)) (hasInput_canon x5)).1
    x5_mem_WEC 0)

/-- **Figure 5 does not weakly decide `WEC_COUNT`** (contrary to the proof of Lemma 5.3). -/
theorem fig5_not_weaklyDecides : ¬ WeaklyDecides (fig5Alg (n := 2)) WEC := fun h =>
  fig5_noSet_infinite ((h (canon x5) x5 (isExec_canon (wf_fam _ _ _)) (hasInput_canon x5)).1
    x5_mem_WEC 0)

/-- Figure 5 does not weakly decide the literal reading `WEClit` either. -/
theorem fig5_not_weaklyDecides_lit : ¬ WeaklyDecides (fig5Alg (n := 2)) WEClit := fun h =>
  fig5_noSet_infinite ((h (canon x5) x5 (isExec_canon (wf_fam _ _ _)) (hasInput_canon x5)).1
    (WEC_subset_WEClit x5_mem_WEC) 0)

/-- Figure 5 does not weakly-all decide the literal reading `WEClit` either. -/
theorem fig5_not_weakAllDecides_lit : ¬ WeakAllDecides (fig5Alg (n := 2)) WEClit := fun h =>
  fig5_noSet_infinite ((h (canon x5) x5 (isExec_canon (wf_fam _ _ _)) (hasInput_canon x5)).1
    (WEC_subset_WEClit x5_mem_WEC) 0)

/-! ### The literal reading of property (3) makes Lemma 5.3 false -/

/-- Words of the diagonal argument: in round `j`, `p₀` increments if `b j`, otherwise it reads
its own number of increments so far; `p₁` always reads `0`. -/
def wd (b : ℕ → Bool) : CWord 2 := fam b (oi b) 0

lemma wd_props (b : ℕ → Bool) : WF (wd b) ∧ Typed (wd b) ∧ WEC1 (wd b) ∧ WEC2 (wd b) :=
  ⟨wf_fam _ _ _, typed_fam _ _ _, wec1_fam _ _ _ (fun _ _ => le_rfl),
    wec2_fam _ _ _ (fun _ _ h _ _ => oi_mono b h.le)⟩

/-- With finitely many, but at least one, increments, `wd b ∉ WEClit`: property (3) fails since
`p₁` reads `0` forever. -/
lemma wd_not_mem {b : ℕ → Bool} {j₀ J : ℕ} (h₀ : b j₀ = true) (hJ : ∀ j, J ≤ j → b j = false) :
    wd b ∉ (WEClit : Set (CWord 2)) := by
  intro h
  have hj₀ : j₀ < J := by
    by_contra hc; rw [hJ j₀ (by omega)] at h₀; exact Bool.false_ne_true h₀
  have hS : 1 ≤ oi b J := le_trans (by simp [oi, h₀]) (oi_mono b (Nat.succ_le_of_lt hj₀))
  exact not_evReads_fam b (oi b) 0 (S := oi b J) (by omega) (h.2.2.2.2 _ (finIncs_fam b _ _ hJ))

/-- With infinitely many increments, `wd b ∈ WEClit`: property (3), read literally, is vacuous. -/
lemma wd_mem {b : ℕ → Bool} (hb : ∀ J, ∃ j, J ≤ j ∧ b j = true) :
    wd b ∈ (WEClit : Set (CWord 2)) := by
  obtain ⟨h1, h2, h3, h4⟩ := wd_props b
  exact ⟨h1, h2, h3, h4, fun S hS => absurd hS (not_finIncs_fam b _ _ hb S)⟩

/-- `wd b` up to round `J` only depends on `b` up to round `J`. -/
lemma wd_congr {b b' : ℕ → Bool} {J : ℕ} (h : ∀ j < J, b j = b' j) :
    ∀ m < 4 * J, wd b m = wd b' m := by
  intro m hm
  simp only [wd, fam]
  rw [h (m / 4) (by omega), oi_congr (fun j hj => h j (by omega))]

section diag

variable (V : Alg 2 (fun _ => CInv) (fun _ => CRes) Verdict)

/-- `p₀` reports `NO` at step `t` of the canonical execution of `wd b`. -/
def NoAt (b : ℕ → Bool) (t : ℕ) : Prop := V.outs (canon (wd b)) t = some (0, .no)

open Classical in
/-- Some step `≥ T` at which `p₀` reports `NO` in the canonical execution of `wd b` (if any). -/
noncomputable def tNext (b : ℕ → Bool) (T : ℕ) : ℕ :=
  if h : ∃ t, T ≤ t ∧ NoAt V b t then h.choose else T

lemma le_tNext (b : ℕ → Bool) (T : ℕ) : T ≤ tNext V b T := by
  unfold tNext; split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

lemma noAt_tNext {b : ℕ → Bool} {T : ℕ} (h : ∃ t, T ≤ t ∧ NoAt V b t) :
    NoAt V b (tNext V b T) := by
  unfold tNext; split_ifs
  exact h.choose_spec.2

/-- Stages of the diagonal construction: `(b, R)`, `b` has its last increment round at `R`. -/
noncomputable def stage : ℕ → (ℕ → Bool) × ℕ
  | 0 => (fun j => decide (j = 0), 0)
  | k + 1 =>
    let R' := tNext V (stage k).1 (8 * ((stage k).2 + 1)) / 8 + 1
    (fun j => (stage k).1 j || decide (j = R'), R')

/-- The `NO` step found at stage `k`. -/
noncomputable def tStage (k : ℕ) : ℕ := tNext V (stage V k).1 (8 * ((stage V k).2 + 1))

lemma stage_R_succ (k : ℕ) : (stage V (k + 1)).2 = tStage V k / 8 + 1 := rfl

lemma stage_b_succ (k : ℕ) (j : ℕ) :
    (stage V (k + 1)).1 j = ((stage V k).1 j || decide (j = (stage V (k + 1)).2)) := rfl

lemma tStage_ge (k : ℕ) : 8 * ((stage V k).2 + 1) ≤ tStage V k := le_tNext _ _ _

lemma tStage_lt (k : ℕ) : tStage V k < 8 * (stage V (k + 1)).2 := by
  rw [stage_R_succ]; omega

lemma stage_R_lt (k : ℕ) : (stage V k).2 < (stage V (k + 1)).2 := by
  have := tStage_ge V k; rw [stage_R_succ]; omega

lemma stage_R_mono {k k' : ℕ} (h : k ≤ k') : (stage V k).2 ≤ (stage V k').2 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (stage_R_lt V _).le

lemma le_stage_R (k : ℕ) : k ≤ (stage V k).2 := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => have := stage_R_lt V k; omega

lemma stage_b_zero (k : ℕ) : (stage V k).1 0 = true := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stage_b_succ, ih]; rfl

lemma stage_b_le (k : ℕ) : ∀ j, (stage V k).1 j = true → j ≤ (stage V k).2 := by
  induction k with
  | zero => intro j h; simpa [stage] using h
  | succ k ih =>
    intro j h
    rw [stage_b_succ] at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact (ih j h).trans (stage_R_lt V k).le
    · simp at h; omega

lemma stage_b_agree {k k' : ℕ} (h : k ≤ k') :
    ∀ j ≤ (stage V k).2, (stage V k').1 j = (stage V k).1 j := by
  induction h with
  | refl => intro j _; rfl
  | @step m hle ih =>
    intro j hj
    rw [stage_b_succ, ih j hj]
    have h1 := stage_R_mono V hle; have h2 := stage_R_lt V m
    simp; omega

/-- The limit of the stages. -/
noncomputable def bLim (j : ℕ) : Bool := (stage V j).1 j

lemma bLim_agree (k : ℕ) : ∀ j ≤ (stage V k).2, bLim V j = (stage V k).1 j := by
  intro j hj
  unfold bLim
  rcases le_total j k with h | h
  · exact (stage_b_agree V h j (le_stage_R V j)).symm
  · exact stage_b_agree V h j hj

lemma bLim_agree' (k : ℕ) : ∀ j < (stage V (k + 1)).2, bLim V j = (stage V k).1 j := by
  intro j hj
  rw [bLim_agree V (k + 1) j hj.le, stage_b_succ]
  simp; omega

lemma bLim_inf : ∀ J, ∃ j, J ≤ j ∧ bLim V j = true := by
  intro J
  refine ⟨(stage V (J + 1)).2, by have := le_stage_R V (J + 1); omega, ?_⟩
  rw [bLim_agree V (J + 1) _ le_rfl, stage_b_succ]; simp

end diag

/-- **Lemma 5.3 is false for the literal reading of Definition 2.7**: `WEC_COUNT`, with
property (3) read literally (vacuous when there are infinitely many increments), is not weakly
decidable (for `n = 2`). -/
theorem not_WD_WEClit : ¬ WD (WEClit : Set (CWord 2)) := by
  rintro ⟨V, hV⟩
  -- every stage word is rejected: `p₀` reports `NO` infinitely often
  have hstage : ∀ k, NoAt V (stage V k).1 (tStage V k) := by
    intro k
    apply noAt_tNext
    have hnot : wd (stage V k).1 ∉ (WEClit : Set (CWord 2)) :=
      wd_not_mem (J := (stage V k).2 + 1) (stage_b_zero V k) (fun j hj => by
        by_contra hc
        have := stage_b_le V k j (by simpa using hc); omega)
    have hinf := (hV _ _ (isExec_canon (wd_props _).1) (hasInput_canon _)).2 hnot 0
    exact (infinite_iff_frequently.1 hinf) _
  -- the limit word agrees with the stage words long enough
  have hlim : ∀ k, NoAt V (bLim V) (tStage V k) := by
    intro k
    have hw := wd_congr (b := bLim V) (b' := (stage V k).1) (bLim_agree' V k)
    have hc := canon_congr hw
    have ho := outs_congr V hc (tStage V k) (by have := tStage_lt V k; omega)
    unfold NoAt; rw [ho]; exact hstage k
  have hfin := (hV _ _ (isExec_canon (wd_props _).1) (hasInput_canon _)).1
    (wd_mem (bLim_inf V)) 0
  obtain ⟨N, hN⟩ := finite_iff_eventually.1 hfin
  exact hN (tStage V N) (by have := tStage_ge V N; have := le_stage_R V N; omega) (hlim N)

/-- Consequently, `WEC_COUNT` (literal reading) is in none of `WAD = WOD = WD` (Theorem 4.1). -/
theorem not_WAD_WEClit : ¬ WAD (WEClit : Set (CWord 2)) := fun h =>
  not_WD_WEClit ((thm_4_1 _).2.2.1 h)

/-! ### The word used in the paper's proof of Lemma 5.2 -/

/-- The word of the proof of Lemma 5.2 (`n = 2`; the paper's `p₁, p₂` are `0, 1`):
`<₁⁺ >₁ <₂ >₂⁰ <₁ >₁⁰ <₂ >₂⁰ <₁ >₁⁰ …`. -/
def xPaper : CWord 2 := fam (fun j => decide (j = 0)) (fun _ => 0) 0

lemma ownIncs_congr {x y : CWord n} {p : Fin n} {k : ℕ} (h : ∀ m < k, x m = y m) :
    ownIncs x p k = ownIncs y p k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [ownIncs]; rw [ih (fun m hm => h m (by omega)), h k (by omega)]

/-- **The word of the proof of Lemma 5.2 is unsuitable**: its symbol at position 5 is `>₁⁰`, a
`read` of `p₁` returning `0` after `p₁`'s own `inc`, violating property (1). Hence for every
prefix `x(F)` containing this symbol (length `≥ 6`), *every* continuation — in particular the
paper's `x(F) <₁ >₁¹ <₂ >₂¹ …` — is not in `WEC_COUNT` (either reading), so the claimed
contradiction is not obtained. -/
theorem xPaper_cut_not_mem (F : ℕ) (hF : 6 ≤ F) (y : CWord 2) :
    app (pfx xPaper F) y ∉ (WEClit : Set (CWord 2)) := by
  intro h
  have h5 : app (pfx xPaper F) y 5 = ⟨0, .inr (.val 0)⟩ := by
    rw [app_lt (by simp; omega)]
    simp only [pfx, List.getElem_map, List.getElem_range]
    exact fam1 _ _ _ 1
  have h1 := h.2.2.1 5 0 0 h5
  rw [ownIncs_congr (y := xPaper) (fun m hm => by
    rw [app_lt (by simp; omega)]; simp [pfx])] at h1
  rw [show 5 = 4 * 1 + 1 from rfl, xPaper, ownIncs_fam0' _ _ _ 1 rfl] at h1
  exact absurd h1 (by decide)

lemma xPaper_cut_not_mem_WEC (F : ℕ) (hF : 6 ≤ F) (y : CWord 2) :
    app (pfx xPaper F) y ∉ (WEC : Set (CWord 2)) := fun h =>
  xPaper_cut_not_mem F hF y (WEC_subset_WEClit h)

/-- In particular `xPaper` itself is not in `WEC_COUNT`. -/
lemma xPaper_not_mem : xPaper ∉ (WEClit : Set (CWord 2)) := by
  have := xPaper_cut_not_mem 6 le_rfl (shift xPaper 6)
  rwa [app_pfx_shift] at this

/-! ### Figure 5 fails independently of the initial value of `curr_read` -/

/-- `p₀` reads `0`, increments, then reads `1` forever; `p₁` reads `1` forever. The first
operation of `p₀` is a `read`, so `curr_read` is overwritten before the `inc` iteration and the
failure does not depend on the (unspecified) initial value of `curr_read`. -/
def x5' : CWord 2 := fam (fun j => decide (j = 1)) (fun j => if j = 0 then 0 else 1) 1

lemma oi_x5' : ∀ j, oi (fun j => decide (j = 1)) j = if 1 < j then 1 else 0
  | 0 => rfl
  | j + 1 => by
    rw [oi, oi_x5' j]
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rfl
    · rcases h.eq_or_lt with h | h
      · subst h; rfl
      · simp [show j ≠ 1 by omega, show 1 < j by omega, show 1 < j + 1 by omega]

lemma x5'_mem_WEC : x5' ∈ (WEC : Set (CWord 2)) := by
  refine ⟨wf_fam _ _ _, typed_fam _ _ _, wec1_fam _ _ _ ?_, wec2_fam _ _ _ ?_, ?_⟩
  · intro j hj
    rw [oi_x5']
    simp at hj
    split_ifs <;> omega
  · intro j j' _ _ _
    split_ifs <;> omega
  · refine ⟨oi (fun j => decide (j = 1)) 2, finIncs_fam _ _ _ fun j hj => by simp; omega,
      8, fun r p v hr h => ?_⟩
    rw [oi_x5']
    rcases fam_val _ _ _ h with ⟨h1, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · simp [show r / 4 ≠ 0 by omega]
    · simp

/-- In `x5'`, `p₀` sets its flag in its `inc` iteration (its second iteration). -/
lemma flag_x5' : Loc.flag (((fig5Alg (n := 2)).run (canon x5') 12).loc 0) = true := by
  rfl

theorem fig5_noSet_infinite' : (NoSet ((fig5Alg (n := 2)).outs (canon x5')) 0).Infinite := by
  rw [infinite_iff_frequently]
  intro N
  refine ⟨8 * (N + 2) + 3, by omega, ?_⟩
  have hflag := flag_mono _ 0 flag_x5' (8 * (N + 2) + 3) (by omega)
  refine outs_of_flag _ hflag (w := .val 1) ?_
  rw [show 8 * (N + 2) + 3 = 2 * (4 * (N + 2) + 1) + 1 by ring, canon_odd, x5', fam1]
  simp [ev1]

/-- **Figure 5 does not weakly-all decide `WEC_COUNT`**, independently of the initial value of
`curr_read`. -/
theorem fig5_not_weakAllDecides' : ¬ WeakAllDecides (fig5Alg (n := 2)) WEC := fun h =>
  fig5_noSet_infinite' ((h (canon x5') x5' (isExec_canon (wf_fam _ _ _)) (hasInput_canon x5')).1
    x5'_mem_WEC 0)

end Podc2025.LanguageDecidability.Counter
