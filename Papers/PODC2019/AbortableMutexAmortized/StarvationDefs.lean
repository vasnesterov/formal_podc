import Papers.PODC2019.AbortableMutexAmortized.Invariant

/-!
# Starvation freedom: the distance function `δ` and the promoters set `Ψ` (Section 4.1)

The paper (Section 4.1) measures how far a process `p` in the Try section is from the CS by a
decimal number `δ(p)` whose digits are read off the queue prefix `q₁ … q_i = p`:
`d_j = 3` for `j < m`, `d_m = f(q_m)`, `d_j = 0` for `j > m`, where `q_m` is the first process of
the prefix that is not at line 1, and `f` is the digit function of equation (1).

We define:
* `fDigit s r` — the function `f` of equation (1). The paper leaves `f` unspecified at line 11
  (it only remarks that a queue member is never at lines 2, 8), but a queue member *can* be at
  line 11 (an aborted process that has marked its node and is about to wake its successor), and
  `q_m` may be such a process. We set `f = 4` at line 11: the transitions `10 → 11 → 1` must make
  the digit decrease (`5 > f(11) > 3`), so `4` is the only possible choice.
* `decVal ds` — the value of the big-endian decimal digit list `ds`.
* `qPrefix Q p` — the prefix `q₁ … q_i` of `Q` ending at `p = q_i`.
* `deltaDigits s P` — the digit list of Definition 4.1 for the prefix `P`, and
  `delta s p = decVal (deltaDigits s (qPrefix (Qof s) p))`.
* `leaderQm s P` — the process `q_m`, and `promoters s p` — the set `Ψ(p)`.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-! ## Decimal numbers given by digit lists -/

/-- The value of a big-endian list of decimal digits: `decVal [d₁, …, d_k] = d₁ d₂ … d_k`. -/
def decVal : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + decVal ds

@[simp] theorem decVal_nil : decVal [] = 0 := rfl

@[simp] theorem decVal_cons (d : ℕ) (ds : List ℕ) :
    decVal (d :: ds) = d * 10 ^ ds.length + decVal ds := rfl

/-- A list of `k` decimal digits denotes a number `< 10 ^ k`. -/
theorem decVal_lt {ds : List ℕ} (h : ∀ d ∈ ds, d ≤ 9) : decVal ds < 10 ^ ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd : d ≤ 9 := h d (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [decVal_cons, List.length_cons, pow_succ]
    nlinarith

/-- A number with `k + 1` digits and nonzero leading digit is `≥ 10 ^ k`. -/
theorem le_decVal {d : ℕ} {ds : List ℕ} (h : 1 ≤ d) : 10 ^ ds.length ≤ decVal (d :: ds) := by
  simp only [decVal_cons]
  have := Nat.mul_le_mul_right (10 ^ ds.length) h
  omega

/-- Lexicographic comparison: a smaller leading digit gives a smaller number (equal lengths). -/
theorem decVal_lt_of_head {a b : ℕ} {ys zs : List ℕ} (hl : ys.length = zs.length)
    (h9 : ∀ d ∈ ys, d ≤ 9) (hab : a < b) : decVal (a :: ys) < decVal (b :: zs) := by
  have := decVal_lt h9
  simp only [decVal_cons, hl] at this ⊢
  have h2 : (a + 1) * 10 ^ zs.length ≤ b * 10 ^ zs.length := Nat.mul_le_mul_right _ hab
  nlinarith

/-- Lexicographic comparison: equal leading digits, compare the rest (equal lengths). -/
theorem decVal_lt_of_tail {a : ℕ} {ys zs : List ℕ} (hl : ys.length = zs.length)
    (h : decVal ys < decVal zs) : decVal (a :: ys) < decVal (a :: zs) := by
  simp only [decVal_cons, hl]; omega

/-! ## The digit function `f` (equation (1)) -/

/-- The digit function `f` of equation (1):
`f(r) = 3, 2, 8, 9, 7, 2, 1, 6, 5` for `PC_r = 1, 3, 4 ∧ go_r, 4 ∧ ¬go_r, 5, 6, 7, 9, 10`.
**Deviation:** the paper does not define `f` at line 11, although a queue member (and `q_m`) can be
at line 11; we set `f(r) = 4` there (the only value with `f(10) > f(11) > f(1)`). Lines 2 and 8
(never occupied by queue members) get the dummy value `0`. -/
def fDigit (s : State n) (r : Fin n) : ℕ :=
  match s.pc r with
  | .l1 => 3
  | .l2 => 0
  | .l3 => 2
  | .l4 => if s.go r then 8 else 9
  | .l5 => 7
  | .l6 => 2
  | .l7 => 1
  | .l8 => 0
  | .l9 => 6
  | .l10 => 5
  | .l11 => 4

theorem fDigit_le (s : State n) (r : Fin n) : fDigit s r ≤ 9 := by
  unfold fDigit; split <;> (try split) <;> omega

theorem fDigit_of_l1 {s : State n} {r : Fin n} (h : s.pc r = .l1) : fDigit s r = 3 := by
  simp [fDigit, h]

/-- `f` is a nonzero digit for queue members (they are never at lines 2, 8). -/
theorem one_le_fDigit {s : State n} {r : Fin n} (h : InQ s r) : 1 ≤ fDigit s r := by
  unfold fDigit
  rcases h with h | ⟨h, -⟩ <;> split <;> (try split) <;> simp_all [PC.act, PC.ab]

theorem fDigit_eq_one {s : State n} {r : Fin n} : fDigit s r = 1 ↔ s.pc r = .l7 := by
  unfold fDigit; split <;> (try split) <;> simp_all

/-! ## Definition 4.1 -/

/-- The digits `d₁ … d_i` of `δ` for the queue prefix `P = q₁ … q_i` (Definition 4.1):
`d_j = f(q_j) = 3` while `q_j` is at line 1 (`j < m`), `d_m = f(q_m)` for the first `q_m` not at
line 1, and `d_j = 0` for `j > m`. -/
def deltaDigits (s : State n) : List (Fin n) → List ℕ
  | [] => []
  | q :: qs => fDigit s q :: if s.pc q = .l1 then deltaDigits s qs else List.replicate qs.length 0

/-- `q_m`: the first process of the list that is not at line 1 (Definition 4.1). -/
def leaderQm (s : State n) : List (Fin n) → Option (Fin n)
  | [] => none
  | q :: qs => if s.pc q = .l1 then leaderQm s qs else some q

/-- The prefix `q₁ … q_i` of the queue `Q` that ends at `p = q_i`. -/
def qPrefix (Q : List (Fin n)) (p : Fin n) : List (Fin n) := Q.take (Q.idxOf p + 1)

/-- Definition 4.1: the distance `δ(p)` of a process `p` in the Try section or CS from the CS:
the `i`-digit decimal number `d₁ … d_i` (`p = q_i`). -/
noncomputable def delta (s : State n) (p : Fin n) : ℕ :=
  decVal (deltaDigits s (qPrefix (Qof s) p))

/-- The promoters of `p` when its queue leader is `q = q_m`: the processes about to wake `q`
(lines 8, 11 with `v_r = &go_q`) if `q` is waiting at line 4 with `go_q = false`, else `{q}`. -/
def psiOf (s : State n) (q : Fin n) : Set (Fin n) :=
  if s.pc q = .l4 ∧ s.go q = false then {r | (s.pc r = .l8 ∨ s.pc r = .l11) ∧ s.v r = .go q}
  else {q}

/-- Definition 4.1: the promoters set `Ψ(p)`. -/
noncomputable def promoters (s : State n) (p : Fin n) : Set (Fin n) :=
  match leaderQm s (qPrefix (Qof s) p) with
  | none => ∅
  | some q => psiOf s q

/-- The Try section (lines 3–6). -/
def InTry (c : PC) : Prop := c = .l3 ∨ c = .l4 ∨ c = .l5 ∨ c = .l6

/-! ## Basic lemmas -/

theorem deltaDigits_length (s : State n) (P : List (Fin n)) :
    (deltaDigits s P).length = P.length := by
  induction P with
  | nil => rfl
  | cons q qs ih => simp only [deltaDigits]; split <;> simp [ih]

theorem deltaDigits_le (s : State n) (P : List (Fin n)) : ∀ d ∈ deltaDigits s P, d ≤ 9 := by
  induction P with
  | nil => simp [deltaDigits]
  | cons q qs ih =>
    simp only [deltaDigits]
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact fDigit_le s q
    · split at hd
      · exact ih d hd
      · simp [List.mem_replicate] at hd; omega

theorem decVal_deltaDigits_lt (s : State n) (P : List (Fin n)) :
    decVal (deltaDigits s P) < 10 ^ P.length := by
  rw [← deltaDigits_length s P]; exact decVal_lt (deltaDigits_le s P)

theorem le_decVal_deltaDigits {s : State n} {q : Fin n} {P : List (Fin n)} (h : 1 ≤ fDigit s q) :
    10 ^ P.length ≤ decVal (deltaDigits s (q :: P)) := by
  have := le_decVal (ds := if s.pc q = .l1 then deltaDigits s P else List.replicate P.length 0) h
  simp only [deltaDigits]
  convert this using 2
  split <;> simp [deltaDigits_length]

theorem deltaDigits_append_of_l1 {s : State n} {C : List (Fin n)} (hC : ∀ c ∈ C, s.pc c = .l1)
    (L : List (Fin n)) :
    deltaDigits s (C ++ L) = List.replicate C.length 3 ++ deltaDigits s L := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    have hc := hC c (by simp)
    simp [deltaDigits, hc, fDigit_of_l1 hc, ih (fun x hx => hC x (by simp [hx])),
      List.replicate_succ]

/-- The shape of `δ`'s digits: `3 … 3 f(q_m) 0 … 0`. -/
theorem deltaDigits_split {s : State n} {C D : List (Fin n)} {q : Fin n}
    (hC : ∀ c ∈ C, s.pc c = .l1) (hq : s.pc q ≠ .l1) :
    deltaDigits s (C ++ q :: D) =
      List.replicate C.length 3 ++ fDigit s q :: List.replicate D.length 0 := by
  rw [deltaDigits_append_of_l1 hC]; simp [deltaDigits, hq]

theorem leaderQm_split {s : State n} {C D : List (Fin n)} {q : Fin n}
    (hC : ∀ c ∈ C, s.pc c = .l1) (hq : s.pc q ≠ .l1) : leaderQm s (C ++ q :: D) = some q := by
  induction C with
  | nil => simp [leaderQm, hq]
  | cons c C ih => simp [leaderQm, hC c (by simp), ih (fun x hx => hC x (by simp [hx]))]

theorem sf_exists_split {s : State n} {P : List (Fin n)} (h : ∃ q ∈ P, s.pc q ≠ .l1) :
    ∃ C q D, P = C ++ q :: D ∧ (∀ c ∈ C, s.pc c = .l1) ∧ s.pc q ≠ .l1 := by
  induction P with
  | nil => simp at h
  | cons x P ih =>
    by_cases hx : s.pc x = .l1
    · obtain ⟨C, q, D, rfl, hC, hq⟩ := ih (by
        obtain ⟨q, hq, hq'⟩ := h
        rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd hx hq'
        · exact ⟨q, hq, hq'⟩)
      exact ⟨x :: C, q, D, rfl, by simpa [hx] using hC, hq⟩
    · exact ⟨[], x, P, rfl, by simp, hx⟩

/-- Lexicographic decrease of `δ`'s digits: if the processes before `q` stay at line 1 and the
digit `f(q)` decreases, the number decreases. -/
theorem decVal_lt_of_split {s s' : State n} {C D : List (Fin n)} {q : Fin n}
    (hC : ∀ c ∈ C, s.pc c = .l1) (hC' : ∀ c ∈ C, s'.pc c = .l1)
    (hlt : fDigit s' q < fDigit s q) :
    decVal (deltaDigits s' (C ++ q :: D)) < decVal (deltaDigits s (C ++ q :: D)) := by
  induction C with
  | nil =>
    simp only [List.nil_append, deltaDigits]
    apply decVal_lt_of_head _ _ hlt
    · split <;> split <;> simp [deltaDigits_length]
    · intro d hd; split at hd
      · exact deltaDigits_le s' D d hd
      · simp [List.mem_replicate] at hd; omega
  | cons c C ih =>
    have hc := hC c (by simp)
    have hc' := hC' c (by simp)
    simp only [List.cons_append, deltaDigits, hc, hc', ite_true, fDigit_of_l1 hc,
      fDigit_of_l1 hc']
    exact decVal_lt_of_tail (by simp [deltaDigits_length])
      (ih (fun x hx => hC x (by simp [hx])) (fun x hx => hC' x (by simp [hx])))

/-! ## Queue prefixes -/

theorem qPrefix_eq {A B : List (Fin n)} {p : Fin n} (h : p ∉ A) :
    qPrefix (A ++ p :: B) p = A ++ [p] := by
  simp [qPrefix, List.idxOf_append_of_notMem h, List.take_append]

theorem sf_exists_split_mem {Q : List (Fin n)} (hnd : Q.Nodup) {p : Fin n} (hp : p ∈ Q) :
    ∃ A B, Q = A ++ p :: B ∧ p ∉ A := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hp
  refine ⟨A, B, rfl, fun h => ?_⟩
  have := (List.nodup_append.1 hnd).2.2 p h p (by simp)
  exact this rfl

end Podc.AbortableMutexAmortized
