import Papers.PODC2022.RecoverableHarder.Recording

/-!
# The type `T_n` of Proposition 19

`T_n` has values `(winner, row, col)` with `winner ∈ {A, B}`, `0 ≤ row < ⌈n/2⌉`,
`0 ≤ col < ⌊n/2⌋`, and `(⊥, 0, 0)`; operations `op_A`, `op_B` (Figure 5) and `Read`.

We define the family `TT a b` (`col < a + 1`, `row < b + 1`; winner `false` = A, `true` = B)
and `Tn n := TT (n / 2 - 1) ((n + 1) / 2 - 1)`.

* `TT.isDiscerning`: `TT a b` is `(a + b + 2)`-discerning (Proposition 19, first part);
* `TT.not_isRecording`: `TT a b` (`a, b ≥ 1`) is not `k`-recording for `k ≥ a + b + 1`
  (Proposition 19, second part, for all `k ≥ n − 1`);
* `TT.not_isDiscerning`: `TT a b` is not `k`-discerning for `k ≥ a + b + 3`, i.e. `T_n` is not
  `(n+1)`-discerning — **needed for `cons(T_n) = n` in Corollary 20 but not proved in the paper**.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-! ## General counting -/

lemma countP_le_card_of_nodup {N : ℕ} (P : Fin N → Bool) {l : List (Fin N)} (hl : l.Nodup) :
    l.countP P ≤ (Finset.univ.filter fun p => P p = true).card := by
  classical
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hl.filter _)]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_filter] at hx
  simpa using hx.2

/-! ## The type -/

/-- Values of `T`: `(⊥, 0, 0)` or `(winner, row, col)`. -/
inductive TSt (a b : ℕ) where
  | bot
  | st (w : Bool) (r : Fin (b + 1)) (c : Fin (a + 1))
  deriving DecidableEq

/-- Operations: `op_A`, `op_B`, `Read`. -/
inductive TOp where
  | opA
  | opB
  | read
  deriving DecidableEq

/-- Responses: a winner (`false` = A, `true` = B), or a value (of `Read`). -/
inductive TRes (a b : ℕ) where
  | win (w : Bool)
  | val (s : TSt a b)
  deriving DecidableEq

/-- Figure 5. -/
def tδ (a b : ℕ) : TSt a b → TOp → TSt a b × TRes a b
  | s, .read => (s, .val s)
  | .bot, .opA => (.st false 0 0, .win false)
  | .bot, .opB => (.st true 0 0, .win true)
  | .st w r c, .opA => if c + 1 = 0 then (.bot, .win w) else (.st w r (c + 1), .win w)
  | .st w r c, .opB => if r + 1 = 0 then (.bot, .win w) else (.st w (r + 1) c, .win w)

/-- The type `TT a b` (`⌊n/2⌋ = a + 1`, `⌈n/2⌉ = b + 1`). -/
abbrev TT (a b : ℕ) : ObjSpec where
  State := TSt a b
  Op := TOp
  Resp := TRes a b
  init := .bot
  δ := tδ a b

/-- The type `T_n` of Proposition 19. -/
abbrev Tn (n : ℕ) : ObjSpec := TT (n / 2 - 1) ((n + 1) / 2 - 1)

theorem TT.readable (a b : ℕ) : (TT a b).Readable :=
  ⟨.read, fun _ => rfl, fun s t h => by simpa [tδ] using h⟩

lemma fin_add_one_eq_zero {k : ℕ} (c : Fin (k + 1)) : c + 1 = 0 ↔ c.val = k := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [Fin.val_add_one] at this
    split_ifs at this with h'
    · simp [h']
    · simp at this
  · intro h
    have : c = Fin.last k := Fin.ext (by simp [h])
    simp [this]

lemma fin_val_add_one_of_lt {k : ℕ} (c : Fin (k + 1)) (h : c.val < k) :
    (c + 1).val = c.val + 1 := by
  rw [Fin.val_add_one]
  split_ifs with h'
  · subst h'; simp at h
  · rfl

/-! ## Proposition 19, first part: `TT a b` is `(a + b + 2)`-discerning -/

section Disc

variable {a b : ℕ}

/-- Teams: processes `0, …, a` are on team `A` (`false`), the others on team `B`. -/
def tTeam (a b : ℕ) (p : Fin (a + b + 2)) : Bool := decide (a + 1 ≤ p.val)

/-- Operations: `op_A` for team `A`, `op_B` for team `B`. -/
def tOp (a b : ℕ) (p : Fin (a + b + 2)) : TOp := if tTeam a b p then .opB else .opA

lemma card_tTeam_false : (Finset.univ.filter fun p : Fin (a + b + 2) =>
    (!tTeam a b p) = true).card = a + 1 := by
  have : (Finset.univ.filter fun p : Fin (a + b + 2) => (!tTeam a b p) = true) =
      Finset.univ.filter fun p : Fin (a + b + 2) => p.val < a + 1 := by
    ext p; simp [tTeam]
  rw [this, Fin.card_filter_val_lt]; omega

lemma card_tTeam_true : (Finset.univ.filter fun p : Fin (a + b + 2) =>
    tTeam a b p = true).card = b + 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (a + b + 2))))
    (fun p => tTeam a b p = true)
  have h2 : (Finset.univ.filter fun p : Fin (a + b + 2) => ¬ tTeam a b p = true) =
      Finset.univ.filter fun p : Fin (a + b + 2) => (!tTeam a b p) = true := by
    ext p; simp
  rw [h2, card_tTeam_false] at h
  simp at h; omega

/-- Invariant when team `A` went first: `x` operations `op_A` and `y` operations `op_B` were
applied. -/
def InvA (a b : ℕ) (s : TSt a b) (x y : ℕ) : Prop :=
  (∃ r c, s = .st false r c ∧ c.val + 1 ≤ x ∧ ((r.val = y ∧ y < b + 1) ∨ (r.val = 0 ∧ y = b + 1)))
    ∨ (s = .bot ∧ y = b + 1)

/-- Invariant when team `B` went first. -/
def InvB (a b : ℕ) (s : TSt a b) (x y : ℕ) : Prop :=
  (∃ r c, s = .st true r c ∧ r.val + 1 ≤ y ∧ ((c.val = x ∧ x < a + 1) ∨ (c.val = 0 ∧ x = a + 1)))
    ∨ (s = .bot ∧ x = a + 1)

lemma invA_opA {s : TSt a b} {x y : ℕ} (h : InvA a b s x y) (hx : x ≤ a) :
    InvA a b (tδ a b s .opA).1 (x + 1) y ∧ (tδ a b s .opA).2 = .win false := by
  rcases h with ⟨r, c, rfl, hc, hr⟩ | ⟨rfl, hy⟩
  · have hc' : ¬ c + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
    simp only [tδ, hc', ite_false]
    refine ⟨Or.inl ⟨r, c + 1, rfl, ?_, hr⟩, by trivial⟩
    rw [fin_val_add_one_of_lt c (by omega)]; omega
  · simp only [tδ]
    exact ⟨Or.inl ⟨0, 0, rfl, by simp, Or.inr ⟨rfl, hy⟩⟩, by trivial⟩

lemma invA_opB {s : TSt a b} {x y : ℕ} (h : InvA a b s x y) (hy : y ≤ b) :
    InvA a b (tδ a b s .opB).1 x (y + 1) ∧ (tδ a b s .opB).2 = .win false := by
  rcases h with ⟨r, c, rfl, hc, ⟨hr, -⟩ | ⟨-, hr⟩⟩ | ⟨rfl, hy'⟩
  · by_cases hyb : y = b
    · have : r + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
      simp only [tδ, this, ite_true]
      exact ⟨Or.inr ⟨rfl, by omega⟩, by trivial⟩
    · have hr' : ¬ r + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
      simp only [tδ, hr', ite_false]
      refine ⟨Or.inl ⟨r + 1, c, rfl, hc, Or.inl ⟨?_, by omega⟩⟩, by trivial⟩
      rw [fin_val_add_one_of_lt r (by omega)]; omega
  · omega
  · omega

lemma invB_opB {s : TSt a b} {x y : ℕ} (h : InvB a b s x y) (hy : y ≤ b) :
    InvB a b (tδ a b s .opB).1 x (y + 1) ∧ (tδ a b s .opB).2 = .win true := by
  rcases h with ⟨r, c, rfl, hr, hc⟩ | ⟨rfl, hx⟩
  · have hr' : ¬ r + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
    simp only [tδ, hr', ite_false]
    refine ⟨Or.inl ⟨r + 1, c, rfl, ?_, hc⟩, by trivial⟩
    rw [fin_val_add_one_of_lt r (by omega)]; omega
  · simp only [tδ]
    exact ⟨Or.inl ⟨0, 0, rfl, by simp, Or.inr ⟨rfl, hx⟩⟩, by trivial⟩

lemma invB_opA {s : TSt a b} {x y : ℕ} (h : InvB a b s x y) (hx : x ≤ a) :
    InvB a b (tδ a b s .opA).1 (x + 1) y ∧ (tδ a b s .opA).2 = .win true := by
  rcases h with ⟨r, c, rfl, hr, ⟨hc, -⟩ | ⟨-, hc⟩⟩ | ⟨rfl, hx'⟩
  · by_cases hxa : x = a
    · have : c + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
      simp only [tδ, this, ite_true]
      exact ⟨Or.inr ⟨rfl, by omega⟩, by trivial⟩
    · have hc' : ¬ c + 1 = 0 := by rw [fin_add_one_eq_zero]; omega
      simp only [tδ, hc', ite_false]
      refine ⟨Or.inl ⟨r, c + 1, rfl, hr, Or.inl ⟨?_, by omega⟩⟩, by trivial⟩
      rw [fin_val_add_one_of_lt c (by omega)]; omega
  · omega
  · omega

/-- Along a schedule, the invariant of the first team is kept and every operation returns the
first team. -/
lemma resp_of_inv (w : Bool) (Inv : TSt a b → ℕ → ℕ → Prop)
    (hA : ∀ s x y, Inv s x y → x ≤ a → Inv (tδ a b s .opA).1 (x + 1) y ∧
      (tδ a b s .opA).2 = .win w)
    (hB : ∀ s x y, Inv s x y → y ≤ b → Inv (tδ a b s .opB).1 x (y + 1) ∧
      (tδ a b s .opB).2 = .win w) :
    ∀ (l : List (Fin (a + b + 2))) (s : TSt a b) (x y : ℕ), Inv s x y →
      x + l.countP (fun p => !tTeam a b p) ≤ a + 1 → y + l.countP (tTeam a b) ≤ b + 1 →
      ∀ m (hm : m < l.length),
        (tδ a b (apply (TT a b) s (tOp a b) (l.take m)) (tOp a b l[m])).2 = .win w := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _ m hm; simp at hm
  | cons p l ih =>
    intro s x y hs hx hy m hm
    by_cases hp : tTeam a b p
    · have hy' : y ≤ b := by simp [hp] at hy; omega
      obtain ⟨hs', hr⟩ := hB s x y hs hy'
      cases m with
      | zero => simpa [tOp, hp] using hr
      | succ m =>
        simp only [List.take_succ_cons, apply_cons, List.getElem_cons_succ]
        exact ih _ x (y + 1) (by simpa [tOp, hp] using hs')
          (by simp [hp] at hx; omega)
          (by simp [hp] at hy; omega) m (by simpa using hm)
    · have hx' : x ≤ a := by simp [hp] at hx; omega
      obtain ⟨hs', hr⟩ := hA s x y hs hx'
      cases m with
      | zero => simpa [tOp, hp] using hr
      | succ m =>
        simp only [List.take_succ_cons, apply_cons, List.getElem_cons_succ]
        exact ih _ (x + 1) y (by simpa [tOp, hp] using hs')
          (by simp [hp] at hx; omega)
          (by simp [hp] at hy; omega) m (by simpa using hm)

/-- **Proposition 19 (first part).** `TT a b` is `(a + b + 2)`-discerning: from `(⊥, 0, 0)`, with
`op_A` for the `a + 1` processes of team `A` and `op_B` for the `b + 1` processes of team `B`,
every operation returns the team of the first operation. -/
theorem TT.isDiscerning (a b : ℕ) : IsDiscerning (a + b + 2) (TT a b) := by
  refine ⟨.bot, tTeam a b, tOp a b, ⟨⟨0, by omega⟩, by simp [tTeam]⟩,
    ⟨⟨a + 1, by omega⟩, by simp [tTeam]⟩, ?_⟩
  intro σ τ j m m' hm hm' hσ hτ hσne hτne tσ tτ hσj hτj heq
  have key : ∀ (l : List (Fin (a + b + 2))) (hl : l.Nodup) (hne : l ≠ []) (w : Bool),
      tTeam a b (l.head hne) = w → ∀ k (hk : k < l.length),
      (tδ a b (apply (TT a b) .bot (tOp a b) (l.take k)) (tOp a b l[k])).2 = .win w := by
    intro l hl hne w hw k hk
    obtain ⟨p, l', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head_cons] at hw
    have cA := countP_le_card_of_nodup (fun p => !tTeam a b p) hl
    have cB := countP_le_card_of_nodup (tTeam a b) hl
    rw [card_tTeam_false] at cA
    rw [card_tTeam_true] at cB
    subst hw
    cases k with
    | zero =>
      by_cases hp : tTeam a b p <;> simp [tOp, hp, tδ]
    | succ k =>
      simp only [List.take_succ_cons, apply_cons, List.getElem_cons_succ]
      by_cases hp : tTeam a b p
      · rw [hp]
        exact resp_of_inv true (InvB a b) (fun s x y h hx => invB_opA h hx)
          (fun s x y h hy => invB_opB h hy) l' _ 0 1
          (by simp only [tOp, hp, ite_true, tδ]; exact Or.inl ⟨0, 0, rfl, by simp, Or.inl
            ⟨rfl, by omega⟩⟩)
          (by simp [hp] at cA; omega)
          (by simp [hp] at cB; omega) k (by simpa using hk)
      · simp only [Bool.not_eq_true] at hp
        rw [hp]
        exact resp_of_inv false (InvA a b) (fun s x y h hx => invA_opA h hx)
          (fun s x y h hy => invA_opB h hy) l' _ 1 0
          (by simp only [tOp, hp, tδ]; exact Or.inl ⟨0, 0, rfl, by simp, Or.inl
            ⟨rfl, by omega⟩⟩)
          (by simp [hp] at cA; omega)
          (by simp [hp] at cB; omega) k (by simpa using hk)
  have h1 := key σ hσ hσne false tσ m hm
  have h2 := key τ hτ hτne true tτ m' hm'
  rw [hσj] at h1
  rw [hτj] at h2
  have := congrArg Prod.fst heq
  simp only at this
  rw [h1, h2] at this
  simp at this

end Disc

/-! ## Proposition 19, second part: `TT a b` is not `k`-recording for `k ≥ a + b + 1` -/

section NotRec

variable {a b : ℕ}

/-- From a value other than `(⊥, 0, 0)`, any two operations of `TT a b` lead to the same value,
overwrite one another or commute. -/
lemma TT.pair_of_ne_bot {u : TSt a b} (hu : u ≠ .bot) (x y : TOp) :
    (tδ a b u x).1 = (tδ a b u y).1 ∨ (tδ a b (tδ a b u y).1 x).1 = (tδ a b u x).1 ∨
      (tδ a b (tδ a b u x).1 y).1 = (tδ a b u y).1 ∨
      (tδ a b (tδ a b u x).1 y).1 = (tδ a b (tδ a b u y).1 x).1 := by
  obtain ⟨w, r, c, rfl⟩ : ∃ w r c, u = .st w r c := by
    cases u with
    | bot => exact absurd rfl hu
    | st w r c => exact ⟨w, r, c, rfl⟩
  cases x <;> cases y <;> simp only [tδ] <;> (try split_ifs) <;> simp_all

/-- The same, for discerning: one of the four discerning obstructions holds. -/
lemma TT.pair_disc_of_ne_bot {u : TSt a b} (hu : u ≠ .bot) (x y : TOp) :
    (tδ a b u x).1 = (tδ a b u y).1 ∨ tδ a b (tδ a b u y).1 x = tδ a b u x ∨
      tδ a b (tδ a b u x).1 y = tδ a b u y ∨
      ((tδ a b (tδ a b u x).1 y).1 = (tδ a b (tδ a b u y).1 x).1 ∧
        (tδ a b u x).2 = (tδ a b (tδ a b u y).1 x).2) := by
  obtain ⟨w, r, c, rfl⟩ : ∃ w r c, u = .st w r c := by
    cases u with
    | bot => exact absurd rfl hu
    | st w r c => exact ⟨w, r, c, rfl⟩
  cases x <;> cases y <;> simp only [tδ] <;> (try split_ifs) <;> simp_all

lemma TT.iterA {k : ℕ} (o : Fin k → TOp) :
    ∀ (l : List (Fin k)), (∀ p ∈ l, o p = .opA) → ∀ (w : Bool) (r : Fin (b + 1)) (c : Fin (a + 1)),
      c.val + l.length = a + 1 → apply (TT a b) (.st w r c) o l = .bot := by
  intro l
  induction l with
  | nil => intro _ w r c h; have := c.isLt; simp at h; omega
  | cons p l ih =>
    intro hl w r c hc
    rw [apply_cons, hl p (by simp)]
    by_cases hca : c.val = a
    · have : c + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hca
      simp only [TT, tδ, this, ite_true]
      have : l = [] := by simp at hc; exact List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    · have hc' : ¬ c + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hca
      simp only [TT, tδ, hc', ite_false]
      exact ih (fun q hq => hl q (by simp [hq])) w r (c + 1)
        (by rw [fin_val_add_one_of_lt c (by omega)]; simp at hc; omega)

lemma TT.iterB {k : ℕ} (o : Fin k → TOp) :
    ∀ (l : List (Fin k)), (∀ p ∈ l, o p = .opB) → ∀ (w : Bool) (r : Fin (b + 1)) (c : Fin (a + 1)),
      r.val + l.length = b + 1 → apply (TT a b) (.st w r c) o l = .bot := by
  intro l
  induction l with
  | nil => intro _ w r c h; have := r.isLt; simp at h; omega
  | cons p l ih =>
    intro hl w r c hc
    rw [apply_cons, hl p (by simp)]
    by_cases hrb : r.val = b
    · have : r + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hrb
      simp only [TT, tδ, this, ite_true]
      have : l = [] := by simp at hc; exact List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    · have hr' : ¬ r + 1 = 0 := by rw [fin_add_one_eq_zero]; exact hrb
      simp only [TT, tδ, hr', ite_false]
      exact ih (fun q hq => hl q (by simp [hq])) w (r + 1) c
        (by rw [fin_val_add_one_of_lt r (by omega)]; simp at hc; omega)

/-- In data for a type `TT a b` (with recording or discerning conditions) where all pairs of
processes on different teams have distinct update operations, each team uses one operation. -/
lemma TT.ops_of_pairs {k : ℕ} (team : Fin k → Bool) (o : Fin k → TOp) (i j : Fin k)
    (hi : team i = false) (hj : team j = true)
    (hp : ∀ p q, team p ≠ team q → o p ≠ o q ∧ o p ≠ .read ∧ o q ≠ .read) :
    (o i = .opA ∧ o j = .opB ∨ o i = .opB ∧ o j = .opA) ∧
      (∀ p, team p = false → o p = o i) ∧ (∀ p, team p = true → o p = o j) := by
  have hij := hp i j (by simp [hi, hj])
  refine ⟨?_, fun p tp => ?_, fun p tp => ?_⟩
  · rcases hoi : o i <;> rcases hoj : o j <;> simp_all
  · have h1 := hp p j (by simp [tp, hj])
    rcases hoi : o i <;> rcases hoj : o j <;> rcases hop : o p <;> simp_all
  · have h1 := hp i p (by simp [tp, hi])
    rcases hoi : o i <;> rcases hoj : o j <;> rcases hop : o p <;> simp_all

/-- **Proposition 19 (second part), generalized.** For `a, b ≥ 1`, `TT a b` is not `k`-recording
for any `k ≥ a + b + 1`; in particular `T_n` (`n ≥ 4`) is not `(n-1)`-recording. -/
theorem TT.not_isRecording (ha : 1 ≤ a) (hb : 1 ≤ b) {k : ℕ} (hk : a + b + 1 ≤ k) :
    ¬ IsRecording k (TT a b) := by
  classical
  intro h
  obtain ⟨u, team, o, hrec⟩ := isRecording_iff.1 h
  obtain ⟨⟨i, -, hi⟩, ⟨j, -, hj⟩, -, hcyc⟩ := id hrec
  have hpair := fun p q (hpq : team p ≠ team q) =>
    recOn_pair hrec (Finset.mem_univ p) (Finset.mem_univ q) hpq
  -- the initial value is `(⊥, 0, 0)`
  have hu : u = .bot := by
    by_contra hu
    have := hpair i j (by simp [hi, hj])
    rcases TT.pair_of_ne_bot hu (o i) (o j) with e | e | e | e
    · exact this.1 e
    · exact this.2.1 e
    · exact this.2.2.1 e
    · exact this.2.2.2 e
  subst hu
  have hops := TT.ops_of_pairs team o i j hi hj (fun p q hpq => by
    have := hpair p q hpq
    refine ⟨fun e => this.1 (by rw [e]), fun e => this.2.2.1 ?_, fun e => this.2.1 ?_⟩
    · rw [e]; rfl
    · rw [e]; rfl)
  -- a schedule returning to `(⊥, 0, 0)` that starts with `s` and continues with at least two
  -- processes of the other team contradicts condition 2/3
  have key : ∀ (X : Bool) (s : Fin k), team s = !X → ∀ (l : List (Fin k)), l.Nodup →
      (∀ p ∈ l, team p = X) → 2 ≤ l.length → apply (TT a b) .bot o (s :: l) ≠ .bot := by
    intro X s hs l hl hlX hlen heq
    have hnd : (s :: l).Nodup := by
      refine List.nodup_cons.2 ⟨fun hm => ?_, hl⟩
      have := hlX s hm; rw [hs] at this; cases X <;> simp at this
    obtain ⟨q, ⟨-, hq⟩, huniq⟩ := hcyc s l (by simp) hnd heq
    obtain ⟨p₁, p₂, l', rfl⟩ : ∃ p₁ p₂ l', l = p₁ :: p₂ :: l' := by
      match l, hlen with
      | p₁ :: p₂ :: l', _ => exact ⟨p₁, p₂, l', rfl⟩
    have h12 : p₁ ≠ p₂ := by intro e; subst e; simp at hl
    have e1 := huniq p₁ ⟨by simp, by rw [hs, hlX p₁ (by simp)]; simp⟩
    have e2 := huniq p₂ ⟨by simp, by rw [hs, hlX p₂ (by simp)]; simp⟩
    exact h12 (e1.trans e2.symm)
  set SA := Finset.univ.filter fun p : Fin k => team p = false
  set SB := Finset.univ.filter fun p : Fin k => team p = true
  have hcard : SA.card + SB.card = k := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (fun p => team p = false)
    simpa [SA, SB] using this
  -- bounding a team using the operation of the other team
  have bound : ∀ (X : Bool) (s : Fin k) (m : ℕ), team s = !X → 2 ≤ m →
      (∀ l : List (Fin k), l.length = m → (∀ p ∈ l, team p = X) →
        apply (TT a b) .bot o (s :: l) = .bot) →
      (Finset.univ.filter fun p : Fin k => team p = X).card < m := by
    intro X s m hs hm hcy
    by_contra hlt
    obtain ⟨l, hl, hlen, hlX⟩ := Finset.exists_nodup_list (not_lt.1 hlt)
    exact key X s hs l hl (fun p hp => by simpa using hlX p hp) (by omega)
      (hcy l hlen (fun p hp => by simpa using hlX p hp))
  rcases hops with ⟨⟨hoi, hoj⟩ | ⟨hoi, hoj⟩, hA, hB⟩
  · have b1 : SA.card < a + 1 := bound false j (a + 1) (by simp [hj]) (by omega) (fun l hlen hl => by
      rw [apply_cons, hoj]
      exact TT.iterA o l (fun p hp => by rw [hA p (hl p hp), hoi]) true 0 0 (by simp [hlen]))
    have b2 : SB.card < b + 1 := bound true i (b + 1) (by simp [hi]) (by omega) (fun l hlen hl => by
      rw [apply_cons, hoi]
      exact TT.iterB o l (fun p hp => by rw [hB p (hl p hp), hoj]) false 0 0 (by simp [hlen]))
    omega
  · have b1 : SA.card < b + 1 := bound false j (b + 1) (by simp [hj]) (by omega) (fun l hlen hl => by
      rw [apply_cons, hoj]
      exact TT.iterB o l (fun p hp => by rw [hA p (hl p hp), hoi]) false 0 0 (by simp [hlen]))
    have b2 : SB.card < a + 1 := bound true i (a + 1) (by simp [hi]) (by omega) (fun l hlen hl => by
      rw [apply_cons, hoi]
      exact TT.iterA o l (fun p hp => by rw [hB p (hl p hp), hoj]) true 0 0 (by simp [hlen]))
    omega

/-- **`T_n` is not `(n+1)`-discerning** (generalized: `TT a b` is not `k`-discerning for
`k ≥ a + b + 3`). This is needed for `cons(T_n) = n` in Corollary 20 (with Ruppert's
characterization), but is not proved in the paper. -/
theorem TT.not_isDiscerning {k : ℕ} (hk : a + b + 3 ≤ k) : ¬ IsDiscerning k (TT a b) := by
  classical
  intro h
  obtain ⟨u, team, o, ⟨i, hi⟩, ⟨j, hj⟩, hd⟩ := isDiscerning_iff.1 h
  have third : ∀ p q : Fin k, ∃ r, r ≠ p ∧ r ≠ q := by
    intro p q
    by_contra hno
    push Not at hno
    have : (Finset.univ : Finset (Fin k)) ⊆ {p, q} := fun r _ => by
      by_cases h : r = p
      · simp [h]
      · simp [hno r h]
    have h1 := Finset.card_le_card this
    have h2 := Finset.card_insert_le p {q}
    simp at h1 h2; omega
  have hpair := fun p q (hpq : team p ≠ team q) => DiscCond.pair hd (i := p) (j := q) hpq
  have hij : team i ≠ team j := by simp [hi, hj]
  have hu : u = .bot := by
    by_contra hu
    obtain ⟨r, hri, hrj⟩ := third i j
    rcases TT.pair_disc_of_ne_bot hu (o i) (o j) with e | e | e | e
    · exact (hpair i j hij).2.2 r hri hrj e
    · exact (hpair j i (Ne.symm hij)).1 e
    · exact (hpair i j hij).1 e
    · exact (hpair i j hij).2.1 e
  subst hu
  have hops := TT.ops_of_pairs team o i j hi hj (fun p q hpq => by
    obtain ⟨r, hrp, hrq⟩ := third p q
    refine ⟨fun e => (hpair p q hpq).2.2 r hrp hrq (by rw [e]), fun e => (hpair p q hpq).1 ?_,
      fun e => (hpair q p (Ne.symm hpq)).1 ?_⟩
    · rw [e]; rfl
    · rw [e]; rfl)
  have cyc : ∀ (X : Bool) (s : Fin k), team s = !X → ∀ l : List (Fin k), l.Nodup →
      (hne : l ≠ []) → (∀ p ∈ l, team p = X) → apply (TT a b) .bot o l = .bot → False := by
    intro X s hs l hl hne hlX heq
    have hsl : s ∉ l := fun hm => by have := hlX s hm; rw [hs] at this; cases X <;> simp at this
    obtain ⟨p, l', rfl⟩ := List.exists_cons_of_ne_nil hne
    refine DiscCond.false_of_last_ne hd (p :: l') [] s ?_ (by simp) ?_ (by simpa using heq)
    · rw [List.nodup_append]
      exact ⟨hl, by simp, fun x hx y hy => by simp at hy; subst hy; rintro rfl; exact hsl hx⟩
    · simp [hlX p (by simp), hs]
  set SA := Finset.univ.filter fun p : Fin k => team p = false
  set SB := Finset.univ.filter fun p : Fin k => team p = true
  have hcard : SA.card + SB.card = k := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
      (fun p => team p = false)
    simpa [SA, SB] using this
  -- a team with too many members, all using `x`, returns to `(⊥, 0, 0)`
  have big : ∀ (X : Bool) (s : Fin k) (m : ℕ), team s = !X →
      m ≤ (Finset.univ.filter fun p : Fin k => team p = X).card →
      (∀ p l, l.length + 1 = m → (∀ q ∈ p :: l, team q = X) →
        apply (TT a b) .bot o (p :: l) = .bot) → 1 ≤ m → False := by
    intro X s m hs hm hcy hm1
    obtain ⟨l, hl, hlen, hlX⟩ := Finset.exists_nodup_list hm
    obtain ⟨p, l', rfl⟩ := List.exists_cons_of_ne_nil (l := l) (by rintro rfl; simp at hlen; omega)
    exact cyc X s hs _ hl (by simp) (fun q hq => by simpa using hlX q hq)
      (hcy p l' (by simpa using hlen) (fun q hq => by simpa using hlX q hq))
  rcases hops with ⟨⟨hoi, hoj⟩ | ⟨hoi, hoj⟩, hA, hB⟩
  · by_cases hSA : a + 2 ≤ SA.card
    · refine big false j (a + 2) (by simp [hj]) hSA (fun p l hlen hl => ?_) (by omega)
      rw [apply_cons, hA p (hl p (by simp)), hoi]
      exact TT.iterA o l (fun q hq => by rw [hA q (hl q (by simp [hq])), hoi]) false 0 0
        (by simp; omega)
    · refine big true i (b + 2) (by simp [hi]) (show b + 2 ≤ SB.card by omega)
        (fun p l hlen hl => ?_) (by omega)
      rw [apply_cons, hB p (hl p (by simp)), hoj]
      exact TT.iterB o l (fun q hq => by rw [hB q (hl q (by simp [hq])), hoj]) true 0 0
        (by simp; omega)
  · by_cases hSA : b + 2 ≤ SA.card
    · refine big false j (b + 2) (by simp [hj]) hSA (fun p l hlen hl => ?_) (by omega)
      rw [apply_cons, hA p (hl p (by simp)), hoi]
      exact TT.iterB o l (fun q hq => by rw [hA q (hl q (by simp [hq])), hoi]) true 0 0
        (by simp; omega)
    · refine big true i (a + 2) (by simp [hi]) (show a + 2 ≤ SB.card by omega)
        (fun p l hlen hl => ?_) (by omega)
      rw [apply_cons, hB p (hl p (by simp)), hoj]
      exact TT.iterA o l (fun q hq => by rw [hB q (hl q (by simp [hq])), hoj]) false 0 0
        (by simp; omega)

end NotRec

end Podc.RecoverableHarder
