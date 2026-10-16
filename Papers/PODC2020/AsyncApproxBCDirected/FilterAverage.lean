import Mathlib

/-!
# Algorithm 3 (Filter-and-Average)

A node `v` holds a finite set `Mv` of messages `(value, propagation path)`. It sorts them by value
(ties in any order), removes the longest prefix `O^lo` and the longest suffix `O^hi` that admit an
`f`-cover (a set of at most `f` nodes meeting every path), and outputs the midpoint of the minimum
and the maximum of the remaining values.

Corrections w.r.t. the paper:
* line 5 of Algorithm 3 reads `(max − min)/2`; it must be `(max + min)/2` (`IsFA`);
* covers never contain the node `v` itself (`CoverFor`): every path of a message received by `v`
  ends at `v`, so the cover `{v}` would trim everything when `f ≥ 1`.

`IsFA.props` extracts the four facts used by the correctness proof (Lemma 15, Theorem 16): the
minimum `a` of the trimmed vector is at most the value of every message avoiding the cover of
`O^lo`; the maximum `b` is at least the value of every message avoiding the cover of `O^hi`; and
`a, b` lie between any bounds that hold for all messages avoiding some `f`-set not containing `v`.
`IsFA.exists`: the output is well defined as soon as `v` holds its own message (path `[v]`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

variable {V : Type*} [DecidableEq V]

/-- Messages: a value together with its propagation path (list of nodes, ending at the
receiver). -/
abbrev Msg (V : Type*) := ℝ × List V

/-- The path `p` avoids the set `A`. -/
def Avoids (p : List V) (A : Finset V) : Prop := ∀ y ∈ p, y ∉ A

/-- `H` is an `f`-cover (Definition 4) of the paths of the messages in `L`, for the receiver `v`
(the receiver itself is never suspected). -/
def CoverFor (f : ℕ) (v : V) (H : Finset V) (L : List (Msg V)) : Prop :=
  H.card ≤ f ∧ v ∉ H ∧ ∀ m ∈ L, ¬ Avoids m.2 H

/-- Some `f`-cover exists. -/
def Coverable (f : ℕ) (v : V) (L : List (Msg V)) : Prop := ∃ H, CoverFor f v H L

/-- The values of the trimmed vector `O'` = positions `[i, j)` of `O`. -/
def windowVals (O : List (Msg V)) (i j : ℕ) : Set ℝ := {z | ∃ m ∈ (O.take j).drop i, m.1 = z}

/-- **Algorithm 3** (Filter-and-Average): `y` is a possible output of node `v` holding `Mv`. -/
def IsFA (f : ℕ) (v : V) (Mv : Finset (Msg V)) (y : ℝ) : Prop :=
  ∃ (O : List (Msg V)) (i j : ℕ) (a b : ℝ),
    O.Perm Mv.toList ∧ O.Pairwise (fun m m' => m.1 ≤ m'.1) ∧
    IsGreatest {k | k ≤ O.length ∧ Coverable f v (O.take k)} i ∧
    IsLeast {k | k ≤ O.length ∧ Coverable f v (O.drop k)} j ∧
    IsLeast (windowVals O i j) a ∧ IsGreatest (windowVals O i j) b ∧
    y = (a + b) / 2

theorem mem_window {O : List (Msg V)} {i j : ℕ} {m : Msg V} :
    m ∈ (O.take j).drop i ↔ ∃ (k : ℕ) (hk : k < O.length), i ≤ k ∧ k < j ∧ O[k] = m := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [List.length_take] at hk
    refine ⟨i + k, by omega, by omega, by omega, ?_⟩
    simp [List.getElem_take]
  · rintro ⟨k, hk, hik, hkj, rfl⟩
    refine ⟨k - i, by simp; omega, ?_⟩
    simp only [List.getElem_take]
    congr 1; omega

theorem mem_take_iff {O : List (Msg V)} {i : ℕ} {m : Msg V} :
    m ∈ O.take i ↔ ∃ (k : ℕ) (hk : k < O.length), k < i ∧ O[k] = m := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, by omega, rfl⟩
  · rintro ⟨k, hk, hki, rfl⟩; exact ⟨k, by omega, rfl⟩

theorem mem_drop_iff {O : List (Msg V)} {j : ℕ} {m : Msg V} :
    m ∈ O.drop j ↔ ∃ (k : ℕ) (hk : k < O.length), j ≤ k ∧ O[k] = m := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨j + k, by omega, by omega, rfl⟩
  · rintro ⟨k, hk, hjk, rfl⟩; exact ⟨k - j, by omega, by congr 1; omega⟩

section Props

variable {f : ℕ} {v : V}

/-- The facts about Filter-and-Average used in the correctness proof. -/
theorem IsFA.props {Mv : Finset (Msg V)} {y : ℝ} (h : IsFA f v Mv y) :
    ∃ a b : ℝ, y = (a + b) / 2 ∧ a ≤ b ∧
      (∃ H : Finset V, H.card ≤ f ∧ v ∉ H ∧ ∀ m ∈ Mv, Avoids m.2 H → a ≤ m.1) ∧
      (∃ H : Finset V, H.card ≤ f ∧ v ∉ H ∧ ∀ m ∈ Mv, Avoids m.2 H → m.1 ≤ b) ∧
      (∀ (F : Finset V) (lo : ℝ), F.card ≤ f → v ∉ F →
        (∀ m ∈ Mv, Avoids m.2 F → lo ≤ m.1) → lo ≤ a) ∧
      (∀ (F : Finset V) (hi : ℝ), F.card ≤ f → v ∉ F →
        (∀ m ∈ Mv, Avoids m.2 F → m.1 ≤ hi) → b ≤ hi) := by
  obtain ⟨O, i, j, a, b, hperm, hsort, hi, hj, ha, hb, rfl⟩ := h
  have hmemO : ∀ m, m ∈ Mv ↔ m ∈ O := fun m => by rw [hperm.mem_iff, Finset.mem_toList]
  have hmono : ∀ (k k' : ℕ) (hk : k < O.length) (hk' : k' < O.length), k ≤ k' →
      O[k].1 ≤ O[k'].1 := by
    intro k k' hk hk' hkk'
    rcases hkk'.lt_or_eq with h | h
    · exact List.pairwise_iff_getElem.mp hsort k k' hk hk' h
    · subst h; exact le_rfl
  obtain ⟨-, Hlo, hHlo⟩ := hi.1
  obtain ⟨-, Hhi, hHhi⟩ := hj.1
  obtain ⟨ma, hma, rfl⟩ := ha.1
  obtain ⟨ka, hka, hika, hkaj, rfl⟩ := mem_window.mp hma
  refine ⟨O[ka].1, b, rfl, hb.2 ⟨O[ka], hma, rfl⟩, ⟨Hlo, hHlo.1, hHlo.2.1, ?_⟩,
    ⟨Hhi, hHhi.1, hHhi.2.1, ?_⟩, ?_, ?_⟩
  · intro m hm hav
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ((hmemO m).mp hm)
    have hik : i ≤ k := by
      by_contra hlt
      exact hHlo.2.2 O[k] (mem_take_iff.mpr ⟨k, hk, by omega, rfl⟩) hav
    by_cases hkj : k < j
    · exact ha.2 ⟨O[k], mem_window.mpr ⟨k, hk, hik, hkj, rfl⟩, rfl⟩
    · exact hmono ka k hka hk (by omega)
  · intro m hm hav
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ((hmemO m).mp hm)
    have hkj : k < j := by
      by_contra hle
      exact hHhi.2.2 O[k] (mem_drop_iff.mpr ⟨k, hk, by omega, rfl⟩) hav
    by_cases hik : i ≤ k
    · exact hb.2 ⟨O[k], mem_window.mpr ⟨k, hk, hik, hkj, rfl⟩, rfl⟩
    · obtain ⟨mb, hmb, rfl⟩ := hb.1
      obtain ⟨kb, hkb, hikb, -, rfl⟩ := mem_window.mp hmb
      exact hmono k kb hk hkb (by omega)
  · intro F lo hF hvF hlo
    by_contra hlt
    push Not at hlt
    have : ka + 1 ∈ {k | k ≤ O.length ∧ Coverable f v (O.take k)} := by
      refine ⟨by omega, F, hF, hvF, fun m hm hav => ?_⟩
      obtain ⟨k, hk, hkk, rfl⟩ := mem_take_iff.mp hm
      have := hlo O[k] ((hmemO _).mpr (List.getElem_mem hk)) hav
      have := hmono k ka hk hka (by omega)
      linarith
    have := hi.2 this
    omega
  · intro F hi' hF hvF hhi
    obtain ⟨mb, hmb, rfl⟩ := hb.1
    obtain ⟨kb, hkb, hikb, hkbj, rfl⟩ := mem_window.mp hmb
    by_contra hlt
    push Not at hlt
    have : kb ∈ {k | k ≤ O.length ∧ Coverable f v (O.drop k)} := by
      refine ⟨by omega, F, hF, hvF, fun m hm hav => ?_⟩
      obtain ⟨k, hk, hkk, rfl⟩ := mem_drop_iff.mp hm
      have := hhi O[k] ((hmemO _).mpr (List.getElem_mem hk)) hav
      have := hmono kb k hkb hk hkk
      linarith
    have := hj.2 this
    omega

/-- Filter-and-Average is well defined (`O'` is non-empty) as soon as `v` holds a message with
path `[v]` (its own value): no cover avoiding `v` can meet that path. -/
theorem IsFA.exists {Mv : Finset (Msg V)} (hown : ∃ m ∈ Mv, m.2 = [v]) :
    ∃ y, IsFA f v Mv y := by
  classical
  set O := Mv.toList.insertionSort (fun m m' : Msg V => m.1 ≤ m'.1)
  have hperm : O.Perm Mv.toList := List.perm_insertionSort _ _
  have hsort : O.Pairwise (fun m m' : Msg V => m.1 ≤ m'.1) := List.pairwise_insertionSort _ _
  set P := fun k => Coverable f v (O.take k)
  set i := Nat.findGreatest P O.length
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp⟩
  have hi : IsGreatest {k | k ≤ O.length ∧ Coverable f v (O.take k)} i :=
    ⟨⟨Nat.findGreatest_le _, Nat.findGreatest_spec (Nat.zero_le _) hP0⟩,
      fun k hk => Nat.le_findGreatest hk.1 hk.2⟩
  have hex : ∃ k, k ≤ O.length ∧ Coverable f v (O.drop k) :=
    ⟨O.length, le_rfl, ∅, by simp, by simp, by simp⟩
  set j := Nat.find hex
  have hj : IsLeast {k | k ≤ O.length ∧ Coverable f v (O.drop k)} j :=
    ⟨Nat.find_spec hex, fun k hk => Nat.find_min' hex hk⟩
  -- the own message lies in the window
  obtain ⟨m₀, hm₀, hm₀p⟩ := hown
  have hm₀O : m₀ ∈ O := hperm.mem_iff.mpr (Finset.mem_toList.mpr hm₀)
  obtain ⟨k₀, hk₀, rfl⟩ := List.mem_iff_getElem.mp hm₀O
  have hnot : ∀ H : Finset V, v ∉ H → Avoids O[k₀].2 H := fun H hv y hy => by
    rw [hm₀p, List.mem_singleton] at hy; subst hy; exact hv
  have hik : i ≤ k₀ := by
    by_contra hlt
    obtain ⟨H, -, hvH, hH⟩ := hi.1.2
    exact hH O[k₀] (mem_take_iff.mpr ⟨k₀, hk₀, by omega, rfl⟩) (hnot H hvH)
  have hkj : k₀ < j := by
    by_contra hle
    obtain ⟨H, -, hvH, hH⟩ := hj.1.2
    exact hH O[k₀] (mem_drop_iff.mpr ⟨k₀, hk₀, by omega, rfl⟩) (hnot H hvH)
  -- the window is a non-empty finite set of values
  set W := ((O.take j).drop i).map Prod.fst
  have hW : (W.toFinset).Nonempty :=
    ⟨O[k₀].1, by simp only [W, List.mem_toFinset, List.mem_map]
                 exact ⟨O[k₀], mem_window.mpr ⟨k₀, hk₀, hik, hkj, rfl⟩, rfl⟩⟩
  have hWset : windowVals O i j = (W.toFinset : Set ℝ) := by
    ext z
    simp only [windowVals, W, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
  refine ⟨_, O, i, j, W.toFinset.min' hW, W.toFinset.max' hW, hperm, hsort, hi, hj, ?_, ?_, rfl⟩
  · rw [hWset]; exact ⟨Finset.min'_mem _ _, fun z hz => Finset.min'_le _ _ hz⟩
  · rw [hWset]; exact ⟨Finset.max'_mem _ _, fun z hz => Finset.le_max' _ _ hz⟩

end Props

end AsyncApproxBCDirected
