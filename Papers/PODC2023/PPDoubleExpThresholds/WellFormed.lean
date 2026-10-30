import Papers.PODC2023.PPDoubleExpThresholds.Totals

/-!
# Well-formedness and size of the program of Section 6
-/

namespace Podc.PPDoubleExpThresholds

open Program Finset

variable {n : ℕ}

/-- The register swapped with `x` (`x̄` for `x ∈ Qᵢ`, and `R` itself). -/
def partner : Reg n → Reg n
  | .r i k => .r i (bar k)
  | .R => .R

theorem partner_reg (i : ℕ) (k : Fin 4) : partner (reg n i k) = reg n i (bar k) := by
  unfold reg; split <;> rfl

theorem partner_partner (x : Reg n) : partner (partner x) = x := by
  cases x <;> simp [partner, bar_bar]

/-- Membership in the procedure set. -/
def InProcs (n : ℕ) : Proc → Prop
  | .assertEmpty i => i ≤ n + 1
  | .assertProper i => i ≤ n
  | .zero i _ => 1 ≤ i ∧ i ≤ n
  | .incrPair i _ _ => 1 ≤ i ∧ i ≤ n
  | .large i _ => 1 ≤ i ∧ i ≤ n
  | .main => True

theorem mem_procs (p : Proc) : p ∈ procs n ↔ InProcs n p := by
  cases p <;> simp [procs, InProcs] <;> omega

/-- The rank witnessing acyclicity of calls. -/
def rank (n : ℕ) : Proc → ℕ
  | .assertEmpty i => n + 2 - i
  | .assertProper i => 4 * i + 3
  | .zero i _ => 4 * i + 1
  | .incrPair i _ _ => 4 * i + 2
  | .large i _ => 4 * i
  | .main => 5 * n + 10

/-- The properties of the instructions of the program checked for well-formedness and size. -/
def Ok (n : ℕ) (p : Proc) (ins : Instr (Reg n) Proc) : Prop :=
  (∀ x y, ins = .swap x y → y = partner x) ∧
  (InProcs n p → ∀ x y, ins = .move x y → x ≠ y) ∧
  (InProcs n p → ∀ q tT tF, ins = .call q tT tF → InProcs n q ∧ rank n q < rank n p)

theorem mem_itsCode {m a : ℕ} {ins : Instr (Reg n) Proc} (h : ins ∈ itsCode n m a) :
    ∃ j b, 1 ≤ j ∧ j ≤ m ∧ ins ∈ itCode n j b := by
  induction m generalizing a with
  | zero => simp [itsCode] at h
  | succ m ih =>
    simp only [itsCode, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨j, b, h1, h2, h3⟩ := ih h; exact ⟨j, b, h1, by omega, h3⟩
    · exact ⟨m + 1, _, by omega, le_rfl, h⟩

theorem ok_main {ins : Instr (Reg n) Proc} (h : ins ∈ (prog n).code .main) : Ok n .main ins := by
  rw [code_main] at h
  simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (rfl | h) | rfl | rfl | rfl | rfl | rfl
  · simp [Ok]
  · obtain ⟨j, b, hj, hjn, h⟩ := mem_itsCode h
    simp only [itCode, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      simp [Ok, InProcs, rank] <;> omega
  all_goals simp [Ok, InProcs, rank] <;> omega

theorem ok_code (p : Proc) {ins : Instr (Reg n) Proc} (h : ins ∈ (prog n).code p) : Ok n p ins := by
  cases p with
  | main => exact ok_main h
  | assertEmpty i =>
    by_cases hi : i ≤ n
    · rw [code_assertEmpty n hi] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> simp [Ok, InProcs, rank] <;> omega
    by_cases hi' : i = n + 1
    · subst hi'; rw [code_assertEmpty_last n] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [Ok]
    · have : (prog n).code (.assertEmpty i) = [.ret false] := by
        simp [prog, body, hi, hi', Stmt.body, Stmt.compile]
      rw [this] at h; simp at h; subst h; simp [Ok]
  | assertProper i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [code_assertProper_zero n] at h; simp at h; subst h; simp [Ok]
    · rw [code_assertProper n hi] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [Ok, InProcs, rank] <;> omega
  | zero i k =>
    rw [code_zero n] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ok, InProcs, rank] <;> omega
  | incrPair i bx by' =>
    rw [code_incrPair n] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Ok, InProcs, rank, partner_reg] <;>
      first
      | omega
      | (intro h1 h2; exact fun h => reg_ne_bar (n := n) h1 h2 _ h.symm)
  | large i k =>
    by_cases hi : i ≤ 1
    · rw [code_large_one n hi] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Ok, InProcs, rank, partner_reg] <;>
        first
        | omega
        | (intro h1 h2; exact reg_ne_bar (n := n) h1 h2 _)
    · rw [code_large n (by omega)] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Ok, InProcs, rank, partner_reg] <;>
        first
        | omega
        | (intro h1 h2; exact reg_ne_bar (n := n) h1 h2 _)
        | (intro h1 h2; have := reg_ne_bar (n := n) h1 h2 k; exact fun h => this h.symm)

/-- The program is well formed: `Main` is a procedure, calls stay inside the procedure set and are
acyclic, moves are between distinct registers. -/
theorem wellFormed (n : ℕ) : (prog n).WellFormed where
  main_mem := (mem_procs _).2 trivial
  call_mem p hp q tT tF h :=
    (mem_procs q).2 ((ok_code p h).2.2 ((mem_procs p).1 hp) q tT tF rfl).1
  acyclic := ⟨rank n, fun p hp q tT tF h => ((ok_code p h).2.2 ((mem_procs p).1 hp) q tT tF rfl).2⟩
  move_ne p hp x y h := (ok_code p h).2.1 ((mem_procs p).1 hp) x y rfl

/-! ### Size -/

theorem swapEdge_partner {x y : Reg n} (h : (prog n).SwapEdge x y) : y = partner x := by
  obtain ⟨p, -, h | h⟩ := h
  · exact (ok_code p h).1 x y rfl
  · rw [(ok_code p h).1 y x rfl, partner_partner]

theorem transGen_partner {x y : Reg n} (h : Relation.TransGen (prog n).SwapEdge x y) :
    y = x ∨ y = partner x := by
  induction h with
  | single h => exact .inr (swapEdge_partner h)
  | tail _ h ih =>
    rw [swapEdge_partner h]
    rcases ih with rfl | rfl
    · exact .inr rfl
    · exact .inl (partner_partner _)

/-- The swap-size is at most the number of registers (only `x` and `x̄` are swapped). -/
theorem swapSize_le : (prog n).swapSize ≤ 4 * n + 1 := by
  classical
  rw [← card_reg n, Program.swapSize]
  refine Fintype.card_le_of_injective (fun xy => xy.1.1) fun a b hab => ?_
  obtain ⟨⟨x, y⟩, hne, hy⟩ := a
  obtain ⟨⟨x', y'⟩, hne', hy'⟩ := b
  simp only at hab hne hne' hy hy'
  subst hab
  have h1 := (transGen_partner hy).resolve_left (Ne.symm hne)
  have h2 := (transGen_partner hy').resolve_left (Ne.symm hne')
  simp [h1, h2]

theorem length_code (p : Proc) :
    ((prog n).code p).length ≤ 25 + if p = .main then 5 * n + 6 else 0 := by
  cases p with
  | main => rw [code_main]; simp [len_itsCode]
  | assertEmpty i =>
    by_cases hi : i ≤ n
    · rw [code_assertEmpty n hi]; simp
    by_cases hi' : i = n + 1
    · subst hi'; rw [code_assertEmpty_last n]; simp
    · have : (prog n).code (.assertEmpty i) = [.ret false] := by
        simp [prog, body, hi, hi', Stmt.body, Stmt.compile]
      rw [this]; simp
  | assertProper i =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [code_assertProper_zero n]; simp
    · rw [code_assertProper n hi]; simp
  | zero i k => rw [code_zero n]; simp
  | incrPair i bx by' => rw [code_incrPair n]; simp
  | large i k =>
    by_cases hi : i ≤ 1
    · rw [code_large_one n hi]; simp
    · rw [code_large n (by omega)]; simp

theorem card_procs : (procs n).card ≤ 14 * n + 4 := by
  unfold procs
  refine ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add
    ((card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add
    ((card_union_le _ _).trans (add_le_add le_rfl card_image_le)) card_image_le))
    card_image_le)) card_image_le)) card_image_le)).trans ?_
  simp; omega

/-- **Size bound of Theorem 3**: the program has size `O(n)`. -/
theorem size_le : (prog n).size ≤ 363 * n + 108 := by
  have h1 : ∑ p ∈ procs n, ((prog n).code p).length ≤ 25 * (14 * n + 4) + (5 * n + 6) := by
    calc ∑ p ∈ procs n, ((prog n).code p).length
        ≤ ∑ p ∈ procs n, (25 + if p = .main then 5 * n + 6 else 0) := sum_le_sum fun p _ => length_code p
      _ = 25 * (procs n).card + (5 * n + 6) := by
        rw [sum_add_distrib, sum_ite_eq' (procs n) Proc.main, if_pos ((mem_procs (n := n) Proc.main).2 trivial)]
        simp [mul_comm]
      _ ≤ _ := by have := card_procs (n := n); omega
  have h2 := swapSize_le (n := n)
  unfold Program.size
  rw [card_reg]
  change 4 * n + 1 + ∑ p ∈ procs n, ((prog n).code p).length + (prog n).swapSize ≤ _
  omega

end Podc.PPDoubleExpThresholds
