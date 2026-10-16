import Papers.PODC2019.FloodingTermination.Model

/-!
# The paper's own proof of Theorem 2.2

`Termination.lean` derives Theorem 2.2 from the parity-distance characterization
(`mem_roundSet_iff`). Here we check the paper's original argument, which uses only the local rules
of amnesiac flooding: a node `g` cannot lie in two round-sets `R_a`, `R_{a+d}` with `d > 0` even.
The paper takes such a pair with minimal duration `d` and, among those, minimal start `a`, picks the
node `g'` that sends to `g` in round `a + d`, and distinguishes
(i) `g'` sent to `g` in round `a` — then `g' ∈ R_{a-1} ∩ R_{a+d-1}`, an earlier start; and
(ii) `g` sent to `g'` in round `a + 1` — then `d ≠ 2` and `g' ∈ R_{a+1} ∩ R_{a+d-1}`, a shorter
duration. We replace the double minimality by a nested strong induction.
-/

namespace FloodingTermination.PaperProof

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s : V}

/-- A node receiving in round `t ≥ 1` received from someone. -/
lemma exists_sender {g : V} {t : ℕ} (ht : 1 ≤ t) (h : g ∈ roundSet G s t) :
    ∃ g', sends G s t g' g := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact h

/-- A sender in round `t + 1` is in `R_t`. -/
lemma mem_roundSet_of_sends {u v : V} {t : ℕ} (h : sends G s (t + 1) u v) : u ∈ roundSet G s t := by
  cases t with
  | zero => exact (sends_one.1 h).1
  | succ t => exact (sends_add_two.1 h).2.1

/-- A receiver in round `t` is in `R_t`. -/
lemma mem_roundSet_of_sends' {u v : V} {t : ℕ} (h : sends G s t u v) : v ∈ roundSet G s t := by
  cases t with
  | zero => exact absurd h (sends_zero u v)
  | succ t => exact ⟨u, h⟩

/-- If `g ∈ R_t` and `g'` is a neighbour, then either `g'` sent to `g` in round `t` or `g` sends to
`g'` in round `t + 1`. -/
lemma sends_or_sends {g g' : V} {t : ℕ} (h : g ∈ roundSet G s t) (hadj : G.Adj g g') :
    sends G s t g' g ∨ sends G s (t + 1) g g' := by
  cases t with
  | zero =>
    rw [roundSet_zero, Set.mem_singleton_iff] at h
    exact Or.inr ⟨h, hadj⟩
  | succ t =>
    by_cases hs : sends G s (t + 1) g' g
    · exact Or.inl hs
    · exact Or.inr (sends_add_two.2 ⟨hadj, h, hs⟩)

/-- No back-and-forth in consecutive rounds. -/
lemma not_sends_back {g g' : V} {t : ℕ} (h : sends G s t g g') : ¬ sends G s (t + 1) g' g := by
  cases t with
  | zero => exact absurd h (sends_zero g g')
  | succ t => exact fun h' => (sends_add_two.1 h').2.2 h

lemma sends_adj {u v : V} {t : ℕ} (h : sends G s t u v) : G.Adj u v := by
  match t, h with
  | 0, h => exact absurd h (sends_zero u v)
  | 1, h => exact (sends_one.1 h).2
  | t + 2, h => exact (sends_add_two.1 h).1

/-- The paper's proof of Theorem 2.2: no node lies in two round-sets an even positive number of
rounds apart. -/
theorem no_even_repeat (md : ℕ) :
    ∀ ms (g : V), 0 < md → Even md → g ∈ roundSet G s ms → g ∉ roundSet G s (ms + md) := by
  induction md using Nat.strong_induction_on with
  | _ md ihd =>
    intro ms
    induction ms using Nat.strong_induction_on with
    | _ ms ihs =>
      intro g hpos heven hg hg'
      -- `g'` sends to `g` in round `ms + md`
      obtain ⟨g', hsend⟩ := exists_sender (by omega) hg'
      have hadj : G.Adj g g' := (sends_adj hsend).symm
      have hprev : g' ∈ roundSet G s (ms + md - 1) := by
        have : ms + md = (ms + md - 1) + 1 := by omega
        rw [this] at hsend
        exact mem_roundSet_of_sends hsend
      rcases sends_or_sends hg hadj with hi | hii
      · -- Case (i): `g'` sends to `g` in round `ms`: earlier start, same duration
        have hms : 1 ≤ ms := by
          rcases ms with _ | ms
          · exact absurd hi (sends_zero g' g)
          · omega
        have hg'0 : g' ∈ roundSet G s (ms - 1) := by
          have : ms = (ms - 1) + 1 := by omega
          rw [this] at hi
          exact mem_roundSet_of_sends hi
        exact ihs (ms - 1) (by omega) g' hpos heven hg'0 (by
          rw [show ms - 1 + md = ms + md - 1 by omega]; exact hprev)
      · -- Case (ii): `g` sends to `g'` in round `ms + 1`
        have hmd : md ≠ 2 := by
          rintro rfl
          exact not_sends_back hii hsend
        have hmd4 : 4 ≤ md := by
          rcases heven with ⟨k, hk⟩; omega
        have hg'1 : g' ∈ roundSet G s (ms + 1) := mem_roundSet_of_sends' hii
        exact ihd (md - 2) (by omega) (ms + 1) g' (by omega)
          (by rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩) hg'1 (by
            rw [show ms + 1 + (md - 2) = ms + md - 1 by omega]; exact hprev)

/-- **Theorem 2.2** via the paper's proof: any node is contained in at most two round-sets. -/
theorem theorem_2_2 (v : V) {a b c : ℕ} (ha : v ∈ roundSet G s a) (hb : v ∈ roundSet G s b)
    (hc : v ∈ roundSet G s c) : a = b ∨ a = c ∨ b = c := by
  have key : ∀ x y, x < y → (y - x) % 2 = 0 → v ∈ roundSet G s x → v ∉ roundSet G s y :=
    fun x y hxy hpar hx hy => no_even_repeat (y - x) x v (by omega)
      (Nat.even_iff.2 hpar) hx (by rw [show x + (y - x) = y by omega]; exact hy)
  by_contra hne
  push Not at hne
  obtain ⟨hab, hac, hbc⟩ := hne
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3 <;>
    rcases Nat.mod_two_eq_zero_or_one a with p1 | p1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with p2 | p2 <;>
    rcases Nat.mod_two_eq_zero_or_one c with p3 | p3 <;>
    first
    | exact key a b h1 (by omega) ha hb
    | exact key b a h1 (by omega) hb ha
    | exact key a c h2 (by omega) ha hc
    | exact key c a h2 (by omega) hc ha
    | exact key b c h3 (by omega) hb hc
    | exact key c b h3 (by omega) hc hb

end FloodingTermination.PaperProof
