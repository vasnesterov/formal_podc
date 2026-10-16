import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Rounds

/-!
# Class `C₂`, sufficiency: correctness of the decision procedure (Lemma 4)

The decision procedure `decideC2` of process `pᵢ` returns the index of the process whose first
operation on `O` is applied first, given the facts about the history of `O` established by the
invariant of Algorithm 3 (`decide0_ok`, `decide1_ok`). The proof enumerates the possible
interleavings of the operations on `O` and uses the properties of class `C₂` (Corollary 1).
-/

namespace TwoShotCons

open Cslib.SharedMemory

section Shuffle

variable {α : Type}

lemma length_filter_fin2 (h : List (Fin 2 × α)) :
    h.length = (h.filter (·.1 = 0)).length + (h.filter (·.1 = 1)).length := by
  induction h with
  | nil => simp
  | cons e h ih =>
    obtain ⟨p, x⟩ := e
    fin_cases p <;> simp [ih] <;> omega

lemma shuf_2_0 {h : List (Fin 2 × α)} {x0 y0 : α}
    (h0 : h.filter (·.1 = 0) = [(0, x0), (0, y0)]) (h1 : h.filter (·.1 = 1) = []) :
    h = [(0, x0), (0, y0)] := by
  have hl := length_filter_fin2 h
  rw [h0, h1] at hl
  rcases h with _ | ⟨⟨p1, a1⟩, _ | ⟨⟨p2, a2⟩, _ | _⟩⟩ <;> simp at hl
  fin_cases p1 <;> fin_cases p2 <;> simp_all

lemma shuf_0_2 {h : List (Fin 2 × α)} {x1 y1 : α}
    (h0 : h.filter (·.1 = 0) = []) (h1 : h.filter (·.1 = 1) = [(1, x1), (1, y1)]) :
    h = [(1, x1), (1, y1)] := by
  have hl := length_filter_fin2 h
  rw [h0, h1] at hl
  rcases h with _ | ⟨⟨p1, a1⟩, _ | ⟨⟨p2, a2⟩, _ | _⟩⟩ <;> simp at hl
  fin_cases p1 <;> fin_cases p2 <;> simp_all

lemma shuf_2_1 {h : List (Fin 2 × α)} {x0 y0 x1 : α}
    (h0 : h.filter (·.1 = 0) = [(0, x0), (0, y0)]) (h1 : h.filter (·.1 = 1) = [(1, x1)]) :
    h = [(0, x0), (0, y0), (1, x1)] ∨ h = [(0, x0), (1, x1), (0, y0)] ∨
      h = [(1, x1), (0, x0), (0, y0)] := by
  have hl := length_filter_fin2 h
  rw [h0, h1] at hl
  rcases h with _ | ⟨⟨p1, a1⟩, _ | ⟨⟨p2, a2⟩, _ | ⟨⟨p3, a3⟩, _ | _⟩⟩⟩ <;> simp at hl
  fin_cases p1 <;> fin_cases p2 <;> fin_cases p3 <;> simp_all

lemma shuf_1_2 {h : List (Fin 2 × α)} {x0 x1 y1 : α}
    (h0 : h.filter (·.1 = 0) = [(0, x0)]) (h1 : h.filter (·.1 = 1) = [(1, x1), (1, y1)]) :
    h = [(1, x1), (1, y1), (0, x0)] ∨ h = [(1, x1), (0, x0), (1, y1)] ∨
      h = [(0, x0), (1, x1), (1, y1)] := by
  have hl := length_filter_fin2 h
  rw [h0, h1] at hl
  rcases h with _ | ⟨⟨p1, a1⟩, _ | ⟨⟨p2, a2⟩, _ | ⟨⟨p3, a3⟩, _ | _⟩⟩⟩ <;> simp at hl
  fin_cases p1 <;> fin_cases p2 <;> fin_cases p3 <;> simp_all

lemma shuf_2_2 {h : List (Fin 2 × α)} {x0 y0 x1 y1 : α}
    (h0 : h.filter (·.1 = 0) = [(0, x0), (0, y0)])
    (h1 : h.filter (·.1 = 1) = [(1, x1), (1, y1)]) :
    h = [(0, x0), (0, y0), (1, x1), (1, y1)] ∨ h = [(0, x0), (1, x1), (0, y0), (1, y1)] ∨
      h = [(0, x0), (1, x1), (1, y1), (0, y0)] ∨ h = [(1, x1), (0, x0), (0, y0), (1, y1)] ∨
      h = [(1, x1), (0, x0), (1, y1), (0, y0)] ∨ h = [(1, x1), (1, y1), (0, x0), (0, y0)] := by
  have hl := length_filter_fin2 h
  rw [h0, h1] at hl
  rcases h with _ | ⟨⟨p1, a1⟩, _ | ⟨⟨p2, a2⟩, _ | ⟨⟨p3, a3⟩, _ | ⟨⟨p4, a4⟩, _ | _⟩⟩⟩⟩ <;>
    simp at hl
  fin_cases p1 <;> fin_cases p2 <;> fin_cases p3 <;> fin_cases p4 <;>
    simp_all

end Shuffle

section Decide

variable {O : ObjSpec} {m : Fin 2 → Set O.Op} {s : O.State} {f g : O.Op} {N : ℕ}
  {c : ℕ → O.Op}

open Classical in
lemma decideC2_zero {a : ℕ} {r0 r1 w : Option O.Resp} {nx : Option ℕ}
    (hN : N % 2 = 1) (ha : a % 2 = 0) :
    decideC2 s f g N c 0 a r0 r1 w nx =
      if a = 0 ∧ r0 = tv s [] f ∧ r1 = tv s [f] (c 0) ∧ (w = none ∨ w = tv s [f, c 0] g) then 0
      else if a = N - 1 ∧ r0 = tv s [g, c N] f ∧ r1 = tv s [g, c N, f] (c (N - 1)) ∧
        nx = some N then 1
      else match nx with
        | none => if r1 = tv s [f, g] (c a) then 0 else 1
        | some j => if r1 = tv s [f, g, c j] (c a) ∨ r1 = tv s [f, g] (c a) then 0 else 1 := by
  have h1 : a ≠ 1 := by omega
  have h2 : a ≠ N := by omega
  simp [decideC2, h1, h2]; congr

open Classical in
lemma decideC2_one {b : ℕ} {r0 r1 w : Option O.Resp} {nx : Option ℕ}
    (hN : N % 2 = 1) (hb : b % 2 = 1) :
    decideC2 s f g N c 1 b r0 r1 w nx =
      if b = 1 ∧ r0 = tv s [f, c 0] g ∧ r1 = tv s [f, c 0, g] (c 1) ∧ nx = some 0 then 0
      else if b = N ∧ r0 = tv s [] g ∧ r1 = tv s [g] (c N) ∧
        (w = none ∨ w = tv s [g, c N] f) then 1
      else match nx with
        | none => if r1 = tv s [f, g] (c b) then 0 else 1
        | some j => if r1 = tv s [f, g, c j] (c b) ∨ r1 = tv s [f, g] (c b) then 0 else 1 := by
  have h1 : b ≠ 0 := by omega
  have h2 : b ≠ N - 1 := by omega
  simp [decideC2, h1, h2]; congr

set_option hygiene false in
/-- Closing tactic for the case analysis of the decision procedure. -/
macro "dec_close" : tactic => `(tactic| first
  | rfl
  | (simp only [tv, List.foldl_cons, List.foldl_nil, h1a, h1b, Option.some.injEq] at *
     exfalso
     casesm* _ ∧ _
     subst_vars
     first
     | (simp_all; done)
     | (simp_all; omega)))

set_option maxHeartbeats 1000000 in
/-- **Lemma 4 for `p₀`**: the decision procedure of `p₀` returns the index of the process whose
first operation on `O` comes first in the history `h` of `O`. -/
theorem decide0_ok (hC : C2At O m s f g N c) (h : List (Fin 2 × O.Op)) (a b : ℕ)
    (r0 r1 w : Option O.Resp) (nx : Option ℕ)
    (hf0 : h.filter (·.1 = 0) = [(0, f), (0, c a)])
    (hf1 : h.filter (·.1 = 1) = [] ∨ h.filter (·.1 = 1) = [(1, g)] ∨
      h.filter (·.1 = 1) = [(1, g), (1, c b)])
    (hv : (view O s h 0).map some = [r0, r1])
    (ha : a ≤ N) (ha2 : a % 2 = 0)
    (hnx : nx = none ∨ (nx = some b ∧ (a + 1 = b ∨ b + 1 = a) ∧ b ≤ N ∧ b % 2 = 1))
    (hnx2 : h.filter (·.1 = 1) = [(1, g), (1, c b)] → nx = some b)
    (hT0 : (h.take 2).map Prod.fst = [0, 0] → a = 0)
    (hT1 : (h.take 2).map Prod.fst = [1, 1] → b = N)
    (hw : w = none ∨ w = (view O s h 1).head?)
    (hw2 : (h.getLast?).map Prod.fst = some 0 → (h.filter (·.1 = 1)).length = 2 → w ≠ none)
    (hN3 : 3 ≤ N) :
    some (decideC2 s f g N c 0 a r0 r1 w nx) = h.head?.map Prod.fst := by
  have h1a := hC.h1a
  have h1b := hC.h1b
  obtain ⟨-, -, -, -, -, -, -, h3, h4, h5, h6⟩ := id hC
  simp only [DistBoth, TwoShotCons.Dist, view, resps, List.filterMap_cons, List.filterMap_nil]
    at h3 h4 h5 h6
  simp at h3 h4 h5 h6
  simp only [h1a, h1b, true_implies] at h3 h4 h5 h6
  have hNodd : N % 2 = 1 := by
    obtain ⟨t, ht⟩ := hC.1; omega
  have key : h = [(0, f), (0, c a)] ∨
      h = [(0, f), (0, c a), (1, g)] ∨ h = [(0, f), (1, g), (0, c a)] ∨
      h = [(1, g), (0, f), (0, c a)] ∨
      h = [(0, f), (0, c a), (1, g), (1, c b)] ∨ h = [(0, f), (1, g), (0, c a), (1, c b)] ∨
      h = [(0, f), (1, g), (1, c b), (0, c a)] ∨ h = [(1, g), (0, f), (0, c a), (1, c b)] ∨
      h = [(1, g), (0, f), (1, c b), (0, c a)] ∨ h = [(1, g), (1, c b), (0, f), (0, c a)] := by
    rcases hf1 with hf1 | hf1 | hf1
    · exact Or.inl (shuf_2_0 hf0 hf1)
    · rcases shuf_2_1 hf0 hf1 with h' | h' | h' <;> simp [h']
    · rcases shuf_2_2 hf0 hf1 with h' | h' | h' | h' | h' | h' <;> simp [h']
  clear hf0 hf1
  have hfg := hC.fg_gf ha
  have hfg' := hfg.symm
  rw [decideC2_zero hNodd ha2]
  rcases key with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [view, resps] at hv hT0 hT1 hw hw2 hnx2
    obtain ⟨rfl, rfl⟩ := hv
    try simp only [h1b] at hw
    simp only [List.head?_cons, Option.map_some]
    rcases hnx with rfl | ⟨rfl, hadj, hb, hb2⟩
    all_goals dsimp only
  · -- shape 1, nx none
    split_ifs <;> dec_close
  · -- shape 1, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 2, nx none
    split_ifs <;> dec_close
  · -- shape 2, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 3, nx none
    split_ifs <;> dec_close
  · -- shape 3, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 4, nx none
    split_ifs <;> dec_close
  · -- shape 4, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 5, nx none
    split_ifs <;> dec_close
  · -- shape 5, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 6, nx none
    split_ifs <;> dec_close
  · -- shape 6, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 7, nx none
    split_ifs <;> dec_close
  · -- shape 7, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 8, nx none
    split_ifs <;> dec_close
  · -- shape 8, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 9, nx none
    split_ifs <;> dec_close
  · -- shape 9, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 10, nx none
    split_ifs <;> dec_close
  · -- shape 10, nx some
    have hadj2 := hC.adj ha hb hadj
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close

set_option maxHeartbeats 1000000 in
/-- **Lemma 4 for `p₁`**: the decision procedure of `p₁` returns the index of the process whose
first operation on `O` comes first in the history `h` of `O`. -/
theorem decide1_ok (hC : C2At O m s f g N c) (h : List (Fin 2 × O.Op)) (a b : ℕ)
    (r0 r1 w : Option O.Resp) (nx : Option ℕ)
    (hf1 : h.filter (·.1 = 1) = [(1, g), (1, c b)])
    (hf0 : h.filter (·.1 = 0) = [] ∨ h.filter (·.1 = 0) = [(0, f)] ∨
      h.filter (·.1 = 0) = [(0, f), (0, c a)])
    (hv : (view O s h 1).map some = [r0, r1])
    (hb : b ≤ N) (hb2 : b % 2 = 1)
    (hnx : nx = none ∨ (nx = some a ∧ (a + 1 = b ∨ b + 1 = a) ∧ a ≤ N ∧ a % 2 = 0))
    (hnx2 : h.filter (·.1 = 0) = [(0, f), (0, c a)] → nx = some a)
    (hT0 : (h.take 2).map Prod.fst = [0, 0] → a = 0)
    (hT1 : (h.take 2).map Prod.fst = [1, 1] → b = N)
    (hw : w = none ∨ w = (view O s h 0).head?)
    (hw2 : (h.getLast?).map Prod.fst = some 1 → (h.filter (·.1 = 0)).length = 2 → w ≠ none)
    (hN3 : 3 ≤ N) :
    some (decideC2 s f g N c 1 b r0 r1 w nx) = h.head?.map Prod.fst := by
  have h1a := hC.h1a
  have h1b := hC.h1b
  obtain ⟨-, -, -, -, -, -, -, h3, h4, h5, h6⟩ := id hC
  simp only [DistBoth, TwoShotCons.Dist, view, resps, List.filterMap_cons, List.filterMap_nil]
    at h3 h4 h5 h6
  simp at h3 h4 h5 h6
  simp only [h1a, h1b, true_implies] at h3 h4 h5 h6
  have hNodd : N % 2 = 1 := by
    obtain ⟨t, ht⟩ := hC.1; omega
  have key : h = [(1, g), (1, c b)] ∨
      h = [(1, g), (1, c b), (0, f)] ∨ h = [(1, g), (0, f), (1, c b)] ∨
      h = [(0, f), (1, g), (1, c b)] ∨
      h = [(0, f), (0, c a), (1, g), (1, c b)] ∨ h = [(0, f), (1, g), (0, c a), (1, c b)] ∨
      h = [(0, f), (1, g), (1, c b), (0, c a)] ∨ h = [(1, g), (0, f), (0, c a), (1, c b)] ∨
      h = [(1, g), (0, f), (1, c b), (0, c a)] ∨ h = [(1, g), (1, c b), (0, f), (0, c a)] := by
    rcases hf0 with hf0 | hf0 | hf0
    · exact Or.inl (shuf_0_2 hf0 hf1)
    · rcases shuf_1_2 hf0 hf1 with h' | h' | h' <;> simp [h']
    · rcases shuf_2_2 hf0 hf1 with h' | h' | h' | h' | h' | h' <;> simp [h']
  clear hf0 hf1
  have hfg := hC.fg_gf hb
  have hfg' := hfg.symm
  rw [decideC2_one hNodd hb2]
  rcases key with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [view, resps] at hv hT0 hT1 hw hw2 hnx2
    obtain ⟨rfl, rfl⟩ := hv
    try simp only [h1b] at hw
    simp only [List.head?_cons, Option.map_some]
    rcases hnx with rfl | ⟨rfl, hadj, ha, ha2⟩
    all_goals dsimp only
  · -- shape 1, nx none
    split_ifs <;> dec_close
  · -- shape 1, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 2, nx none
    split_ifs <;> dec_close
  · -- shape 2, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 3, nx none
    split_ifs <;> dec_close
  · -- shape 3, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 4, nx none
    split_ifs <;> dec_close
  · -- shape 4, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 5, nx none
    split_ifs <;> dec_close
  · -- shape 5, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 6, nx none
    split_ifs <;> dec_close
  · -- shape 6, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    rcases h6 with h6 | ⟨h6a, h6b⟩
    · have h6' := Ne.symm h6
      split_ifs <;> dec_close
    · have h6' := Ne.symm h6b
      by_cases hbN : b = N
      · obtain rfl : a = N - 1 := by omega
        subst hbN
        split_ifs <;> dec_close
      · split_ifs <;> dec_close
  · -- shape 7, nx none
    split_ifs <;> dec_close
  · -- shape 7, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 8, nx none
    split_ifs <;> dec_close
  · -- shape 8, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 9, nx none
    split_ifs <;> dec_close
  · -- shape 9, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close
  · -- shape 10, nx none
    split_ifs <;> dec_close
  · -- shape 10, nx some
    have hadj2 := hC.adj hb ha hadj.symm
    have hadj3 := And.intro hadj2.1.symm (And.intro hadj2.2.1.symm (And.intro hadj2.2.2.1.symm hadj2.2.2.2.symm))
    split_ifs <;> dec_close

end Decide

end TwoShotCons
