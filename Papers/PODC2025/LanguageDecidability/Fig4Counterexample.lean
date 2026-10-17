import Papers.PODC2025.LanguageDecidability.Classes

/-!
# The construction of Figure 4 (proof of Lemma 4.3) is wrong

Figure 4 transforms an algorithm `V` that weakly-one decides `L` into `W`: in Line 06, process
`pᵢ` increments `C[i]` if `V` reports `NO`, takes a snapshot of `C`, reports `YES` iff *some*
entry is unchanged since its *previous* snapshot, and stores the snapshot. The paper claims that
`W` weakly-one decides `L` and that every process reports `NO` infinitely often if `x(E) ∉ L`
("no entry of `C` ever stabilizes, hence all processes report NO infinitely often"). This is
false: an entry can change infinitely often without changing between two consecutive snapshots
of a given process.

Counterexample (`fig4_fails`): `n = 2`, `L = ∅`, `V = altAlg` (every process alternately reports
`YES` and `NO`). `V` weakly-one (and weakly-all) decides `∅`. In the execution where `p₀` runs
two iterations, then `p₁` runs two iterations, and so on, the algorithm `W` of Figure 4 always
reports `YES` at both processes, so `W` neither weakly-one nor weakly-all decides `∅`.

Lemma 4.3 itself is true; `Classes.lemma_4_3` proves it with a corrected construction.
-/

namespace Podc2025.LanguageDecidability.Fig4

open Podc2025.LanguageDecidability

/-- Line 06 of Figure 4: `C[i].write(prev[i] + 1)` if `V` reports `NO`; `snap ← Snapshot(C)`;
report `YES` iff `∃ j, snap[j] = prev[j]`; `prev ← snap`. -/
noncomputable def fFig4 {n : ℕ} (p : Fin n) (prev C : Fin n → ℕ) (d : Verdict) :
    (Fin n → ℕ) × (Fin n → ℕ) × Verdict :=
  haveI := Classical.dec
  let C' := if d = .no then Function.update C p (prev p + 1) else C
  (C', C', if ∃ j, C' j = prev j then .yes else .no)

/-- The algorithm `W` of Figure 4. -/
noncomputable def fig4Alg {n : ℕ} {I O : Fin n → Type} (V : Alg n I O Verdict) :
    Alg n I O Verdict :=
  V.extend (fun _ _ => 0) (fun _ => 0) fFig4

/-- Trivial alphabets. -/
abbrev U2 : Fin 2 → Type := fun _ => Unit

/-- Every process alternately reports `YES` and `NO`. -/
abbrev altAlg : Alg 2 U2 U2 Verdict where
  L := Bool
  M := Unit
  m0 := ()
  l0 := fun _ => false
  pre := fun _ _ l _ m => (l, m)
  post := fun _ _ b _ m => (!b, m, if b then .no else .yes)

/-! ### `altAlg` weakly decides `∅` -/

/-- `e` is a `post` event of `p`. -/
def isPost (p : Fin 2) : Ev U2 U2 → Bool
  | .post q _ => decide (q = p)
  | _ => false

lemma altAlg_loc (s : ℕ → Ev U2 U2) (t : ℕ) (p : Fin 2) :
    (altAlg.run s (t + 1)).loc p =
      if isPost p (s t) then !(altAlg.run s t).loc p else (altAlg.run s t).loc p := by
  rcases h : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩
  · simp only [Alg.run, h, Alg.next, isPost]
    by_cases hq : p = q
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  · simp [Alg.run, h, Alg.next, isPost]
  · simp [Alg.run, h, Alg.next, isPost]
  · simp only [Alg.run, h, Alg.next, isPost]
    by_cases hq : p = q
    · subst hq; simp
    · simp [Function.update_of_ne hq, Ne.symm hq]

lemma altAlg_noSet_infinite {s : ℕ → Ev U2 U2} (hs : IsExec s) (p : Fin 2) :
    (NoSet (altAlg.outs s) p).Infinite := by
  rw [infinite_iff_frequently]
  intro N
  obtain ⟨t₁, ht₁, w₁, hw₁⟩ := hs.fair p N
  have hout : ∀ t w, s t = .post p w →
      altAlg.outs s t = some (p, if (altAlg.run s t).loc p then .no else .yes) := by
    intro t w hw
    rw [outs_post altAlg s hw]
  by_cases hb : (altAlg.run s t₁).loc p = true
  · exact ⟨t₁, ht₁, by simp [NoSet, hout t₁ w₁ hw₁, hb]⟩
  · have hex : ∃ t, t₁ + 1 ≤ t ∧ ∃ w, s t = .post p w := hs.fair p (t₁ + 1)
    classical
    let t₂ := Nat.find hex
    have ht₂ : t₁ + 1 ≤ t₂ ∧ ∃ w, s t₂ = .post p w := Nat.find_spec hex
    have hmin : ∀ t, t₁ + 1 ≤ t → t < t₂ → ¬ ∃ w, s t = .post p w :=
      fun t h1 h2 h3 => Nat.find_min hex h2 ⟨h1, h3⟩
    have htrue : ∀ t, t₁ + 1 ≤ t → t ≤ t₂ → (altAlg.run s t).loc p = true := by
      intro t h1 h2
      induction t, h1 using Nat.le_induction with
      | base => rw [altAlg_loc, hw₁]; simpa [isPost] using hb
      | succ t ht ih =>
        have : isPost p (s t) = false := by
          rcases h : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> simp [isPost]
          rintro rfl; exact hmin t ht (by omega) ⟨w, h⟩
        rw [altAlg_loc, this, ih (by omega)]; rfl
    obtain ⟨w₂, hw₂⟩ := ht₂.2
    exact ⟨t₂, by omega, by simp [NoSet, hout t₂ w₂ hw₂, htrue t₂ ht₂.1 le_rfl]⟩

/-- `altAlg` weakly-one decides `∅`. -/
theorem altAlg_weakOne : WeakOneDecides altAlg (∅ : Set (Word U2 U2)) := by
  intro s x hs _
  simp only [Set.mem_empty_iff_false, false_iff, PWOD, not_exists]
  exact fun p => altAlg_noSet_infinite hs p

/-- `altAlg` weakly-all decides `∅`. -/
theorem altAlg_weakAll : WeakAllDecides altAlg (∅ : Set (Word U2 U2)) := by
  intro s x hs _
  simp only [Set.mem_empty_iff_false, false_iff, PWAD, not_forall]
  exact ⟨0, altAlg_noSet_infinite hs 0⟩

/-! ### The bad execution -/

/-- The process running iteration `i`: `p₀, p₀, p₁, p₁, p₀, p₀, …`. -/
def P (i : ℕ) : Fin 2 := if i % 4 < 2 then 0 else 1

/-- Iteration `i` occupies slots `4i … 4i+3`. -/
def sched (t : ℕ) : Ev U2 U2 :=
  if t % 4 = 0 then .pre (P (t / 4)) ()
  else if t % 4 = 1 then .send (P (t / 4)) ()
  else if t % 4 = 2 then .recv (P (t / 4)) ()
  else .post (P (t / 4)) ()

lemma sched_0 (i : ℕ) : sched (4 * i) = .pre (P i) () := by simp [sched]
lemma sched_1 (i : ℕ) : sched (4 * i + 1) = .send (P i) () := by
  simp [sched, Nat.add_mod]; congr; omega
lemma sched_2 (i : ℕ) : sched (4 * i + 2) = .recv (P i) () := by
  simp [sched, Nat.add_mod]; congr; omega
lemma sched_3 (i : ℕ) : sched (4 * i + 3) = .post (P i) () := by
  simp [sched, Nat.add_mod]; congr; omega

lemma phs_sched (i : ℕ) : phs sched (4 * i) = fun _ => .idle := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have : phs sched (4 * (i + 1)) = phStep (phStep (phStep (phStep (phs sched (4 * i))
        (sched (4 * i))) (sched (4 * i + 1))) (sched (4 * i + 2))) (sched (4 * i + 3)) := by
      rw [show 4 * (i + 1) = 4 * i + 3 + 1 by ring]; rfl
    rw [this, ih, sched_0, sched_1, sched_2, sched_3]
    funext q
    by_cases hq : q = P i
    · subst hq; simp
    · simp [hq]

theorem isExec_sched : IsExec sched where
  valid t := by
    obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 4 ∧ t = 4 * i + j := ⟨t / 4, t % 4, by omega, by omega⟩
    have h1 : phs sched (4 * i + 1) = phStep (phs sched (4 * i)) (sched (4 * i)) := rfl
    have h2 : phs sched (4 * i + 2) = phStep (phs sched (4 * i + 1)) (sched (4 * i + 1)) := rfl
    have h3 : phs sched (4 * i + 3) = phStep (phs sched (4 * i + 2)) (sched (4 * i + 2)) := rfl
    interval_cases j
    · simp [phs_sched, sched_0]
    · rw [h1, phs_sched, sched_0, sched_1]; simp
    · rw [h2, h1, phs_sched, sched_0, sched_1, sched_2]; simp
    · rw [h3, h2, h1, phs_sched, sched_0, sched_1, sched_2, sched_3]; simp
  fair p N := by
    refine ⟨4 * (4 * N + if p = 0 then 0 else 2) + 3, by split_ifs <;> omega, (), ?_⟩
    rw [sched_3]
    congr 1
    fin_cases p <;> simp [P, Nat.add_mod]

/-- The input of the bad execution. -/
def xin (k : ℕ) : Sym U2 U2 := ⟨P (k / 2), if k % 2 = 0 then .inl () else .inr ()⟩

theorem hasInput_sched : HasInput sched xin := by
  refine ⟨fun k => 4 * (k / 2) + 1 + k % 2, strictMono_nat_of_lt_succ fun k => by omega,
    fun t ht => ?_, fun k => ?_⟩ <;> dsimp only
  · obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 4 ∧ t = 4 * i + j := ⟨t / 4, t % 4, by omega, by omega⟩
    interval_cases j
    · simp [sched_0, Ev.sym] at ht
    · exact ⟨2 * i, by omega⟩
    · exact ⟨2 * i + 1, by omega⟩
    · simp [sched_3, Ev.sym] at ht
  · obtain ⟨i, rfl | rfl⟩ : ∃ i, k = 2 * i ∨ k = 2 * i + 1 := ⟨k / 2, by omega⟩
    · rw [show 4 * (2 * i / 2) + 1 + 2 * i % 2 = 4 * i + 1 by omega, sched_1]
      simp [Ev.sym, xin]
    · rw [show 4 * ((2 * i + 1) / 2) + 1 + (2 * i + 1) % 2 = 4 * i + 2 by omega, sched_2]
      simp [Ev.sym, xin, show (2 * i + 1) / 2 = i by omega, Nat.add_mod]

/-! ### Reports of `altAlg` and of `W` along the bad execution -/

lemma altAlg_run_sched (i : ℕ) :
    (altAlg.run sched (4 * i)).loc = fun p => decide (i % 2 = 1 ∧ p = P i) := by
  induction i with
  | zero => funext p; simp [Alg.run, altAlg]
  | succ i ih =>
    have e : ∀ q, (altAlg.run sched (4 * (i + 1))).loc q =
        if q = P i then !(altAlg.run sched (4 * i)).loc q
        else (altAlg.run sched (4 * i)).loc q := by
      intro q
      rw [show 4 * (i + 1) = 4 * i + 3 + 1 by ring, altAlg_loc, altAlg_loc, altAlg_loc, altAlg_loc]
      simp only [sched_0, sched_1, sched_2, sched_3, isPost]
      by_cases hq : P i = q
      · simp [hq]
      · simp [hq, Ne.symm hq]
    funext q
    rw [e, ih]
    have hP : ∀ j, P j = if j % 4 < 2 then 0 else 1 := fun _ => rfl
    have h4 : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h2 : i % 2 = i % 4 % 2 := (Nat.mod_mod_of_dvd i (by norm_num)).symm
    have h2' : (i + 1) % 2 = (i % 4 + 1) % 2 := by omega
    have h4' : (i + 1) % 4 = (i % 4 + 1) % 4 := by omega
    rw [hP, hP (i + 1), h2, h2', h4']
    fin_cases q <;> interval_cases i % 4 <;> simp

lemma altAlg_outs_sched (i : ℕ) :
    altAlg.outs sched (4 * i + 3) = some (P i, if i % 2 = 1 then .no else .yes) := by
  rw [outs_post altAlg sched (sched_3 i)]
  have h : (altAlg.run sched (4 * i + 3)).loc = (altAlg.run sched (4 * i)).loc := by
    funext q
    rw [altAlg_loc, altAlg_loc, altAlg_loc]
    simp [sched_0, sched_1, sched_2, isPost]
  simp only [altAlg]
  rw [h, altAlg_run_sched]
  by_cases hi : i % 2 = 1 <;> simp [hi]

lemma altAlg_outs_none {t : ℕ} (ht : t % 4 ≠ 3) : altAlg.outs sched t = none := by
  obtain ⟨i, j, hj, rfl⟩ : ∃ i j, j < 4 ∧ t = 4 * i + j := ⟨t / 4, t % 4, by omega, by omega⟩
  interval_cases j
  · exact outs_pre altAlg sched (sched_0 i)
  · exact outs_of_sym altAlg sched (by simp [sched_1, Ev.sym])
  · exact outs_of_sym altAlg sched (by simp [sched_2, Ev.sym])
  · omega

local notation "o₀" => altAlg.outs sched
local notation "TR" => tRun fFig4 (fun _ _ => 0) (fun _ => 0) o₀

lemma TR_iter (i : ℕ) : TR (4 * i + 4) = tStep fFig4 (TR (4 * i)) (o₀ (4 * i + 3)) := by
  have h0 := altAlg_outs_none (t := 4 * i) (by omega)
  have h1 := altAlg_outs_none (t := 4 * i + 1) (by omega)
  have h2 := altAlg_outs_none (t := 4 * i + 2) (by omega)
  show tStep fFig4 (tStep fFig4 (tStep fFig4 (tStep fFig4 (TR (4 * i)) (o₀ (4 * i)))
    (o₀ (4 * i + 1))) (o₀ (4 * i + 2))) (o₀ (4 * i + 3)) = _
  rw [h0, h1, h2]; rfl

lemma TR_mid (i : ℕ) : TR (4 * i + 3) = TR (4 * i) := by
  have h0 := altAlg_outs_none (t := 4 * i) (by omega)
  have h1 := altAlg_outs_none (t := 4 * i + 1) (by omega)
  have h2 := altAlg_outs_none (t := 4 * i + 2) (by omega)
  show tStep fFig4 (tStep fFig4 (tStep fFig4 (TR (4 * i)) (o₀ (4 * i)))
    (o₀ (4 * i + 1))) (o₀ (4 * i + 2)) = _
  rw [h0, h1, h2]; rfl

/-- The invariant at the start of iteration `i = 4r + j`: `prev₀`, `prev₁` (local states) and
`C` (shared counters). -/
def Inv (i : ℕ) (st : (Fin 2 → Fin 2 → ℕ) × (Fin 2 → ℕ)) : Prop :=
  let r := i / 4
  match i % 4 with
  | 0 => st.2 0 = r ∧ st.2 1 = r ∧ st.1 0 0 = r ∧ st.1 1 0 = r ∧ st.1 1 1 = r
  | 1 => st.2 0 = r ∧ st.2 1 = r ∧ st.1 0 0 = r ∧ st.1 0 1 = r ∧ st.1 1 0 = r ∧ st.1 1 1 = r
  | 2 => st.2 0 = r + 1 ∧ st.2 1 = r ∧ st.1 0 0 = r + 1 ∧ st.1 0 1 = r ∧ st.1 1 0 = r ∧
      st.1 1 1 = r
  | _ => st.2 0 = r + 1 ∧ st.2 1 = r ∧ st.1 0 0 = r + 1 ∧ st.1 0 1 = r ∧ st.1 1 0 = r + 1 ∧
      st.1 1 1 = r

/-- Each iteration preserves the invariant and `W` reports `YES`. -/
lemma Inv_step (i : ℕ) (h : Inv i (TR (4 * i))) :
    Inv (i + 1) (TR (4 * (i + 1))) ∧
      (fFig4 (P i) ((TR (4 * i)).1 (P i)) (TR (4 * i)).2
        (if i % 2 = 1 then .no else .yes)).2.2 = .yes := by
  rw [show 4 * (i + 1) = 4 * i + 4 by ring, TR_iter, altAlg_outs_sched]
  generalize TR (4 * i) = st at h ⊢
  obtain ⟨r, j, hj, rfl⟩ : ∃ r j, j < 4 ∧ i = 4 * r + j := ⟨i / 4, i % 4, by omega, by omega⟩
  have hd : (4 * r + j) / 4 = r := by omega
  have hm : (4 * r + j) % 4 = j := by omega
  have hd' : (4 * r + j + 1) / 4 = if j = 3 then r + 1 else r := by split_ifs <;> omega
  have hm' : (4 * r + j + 1) % 4 = if j = 3 then 0 else j + 1 := by split_ifs <;> omega
  have hP : P (4 * r + j) = if j < 2 then 0 else 1 := by simp [P, hm]
  have h2 : (4 * r + j) % 2 = j % 2 := by omega
  simp only [Inv, hd, hm, hd', hm'] at h ⊢
  rw [hP, h2]
  obtain ⟨st1, st2⟩ := st
  interval_cases j <;> obtain ⟨h1, h2, h3, h4, h5⟩ := h <;>
    simp_all [tStep, fFig4, Function.update_apply, Fin.exists_fin_two]

lemma Inv_all : ∀ i, Inv i (TR (4 * i))
  | 0 => by simp [Inv, tRun]
  | i + 1 => (Inv_step i (Inv_all i)).1

/-- `W` (Figure 4 applied to `altAlg`) never reports `NO` in the bad execution. -/
theorem fig4_never_no (t : ℕ) (p : Fin 2) : (fig4Alg altAlg).outs sched t ≠ some (p, .no) := by
  unfold fig4Alg
  rw [outs_extend]
  by_cases ht : t % 4 = 3
  · obtain ⟨i, rfl⟩ : ∃ i, t = 4 * i + 3 := ⟨t / 4, by omega⟩
    simp only [tOut, altAlg_outs_sched, Option.map_some, TR_mid, ne_eq, Option.some.injEq,
      Prod.mk.injEq, not_and]
    intro _
    rw [(Inv_step i (Inv_all i)).2]
    exact fun h => by cases h
  · simp [tOut, altAlg_outs_none ht]

/-- **The construction of Figure 4 fails**: `∅` is weakly-one (and weakly-all) decided by
`altAlg`, but the algorithm `W` that Figure 4 builds from `altAlg` neither weakly-one decides nor
weakly-all decides `∅`. -/
theorem fig4_fails :
    WeakOneDecides altAlg (∅ : Set (Word U2 U2)) ∧ WeakAllDecides altAlg (∅ : Set (Word U2 U2)) ∧
      ¬ WeakOneDecides (fig4Alg altAlg) (∅ : Set (Word U2 U2)) ∧
      ¬ WeakAllDecides (fig4Alg altAlg) (∅ : Set (Word U2 U2)) := by
  have hempty : ∀ p, NoSet ((fig4Alg altAlg).outs sched) p = ∅ := fun p =>
    Set.eq_empty_iff_forall_notMem.2 fun t ht => fig4_never_no t p ht
  refine ⟨altAlg_weakOne, altAlg_weakAll, fun h => ?_, fun h => ?_⟩
  · have := (h sched xin isExec_sched hasInput_sched).2 ⟨0, by rw [hempty]; exact Set.finite_empty⟩
    exact this
  · have := (h sched xin isExec_sched hasInput_sched).2 fun p => by
      rw [hempty]; exact Set.finite_empty
    exact this

end Podc2025.LanguageDecidability.Fig4
