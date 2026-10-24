import Papers.PODC2019.StrongLinSnapshots.SnapSim
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Algorithm 3: lock-freedom (Theorem 32, with atomic `S` and `R`)

Section 4.4 of the paper argues lock-freedom through an amortized step bound. We give a direct
proof by a natural-number potential that strictly decreases at every step that is not a
response (`Impl.lockFree_of_potential`). Write `X` for the contents of `S` and `r` for the
vector in `R`. The potential is the lexicographic combination (encoded in mixed radix) of

1. `U`: remaining steps of updates — `4` for every idle process (it may invoke an update),
   `3, 2, 1` before lines 43, 44, 45. Every invocation and every update step decreases `U`;
   scanner steps do not change it. Only update steps change `X`.
2. `Stale`: the number of scanners about to execute line 49 or 51 with a view `ℓ ≠ X`;
   each such scanner may write the stale `ℓ` to `R` once. A scanner reading `S` on line 48
   gets `ℓ = X`, so scanner steps never increase `Stale`.
3. `Bad = [r ≠ X]`: with `X` fixed and no stale writes, `R` can only be written with `X`.
4. `W`: the number of scanners whose current iteration will execute `DWrite` on line 51
   if `X` and `r` do not change (e.g. a scanner before line 47 iff `r ≠ X`). A `DWrite(X)`
   when `r = X` decreases `W` and changes neither `Stale` nor `Bad`.
5. `T`: steps until the current scan iteration ends, given the scanner's ABA flag
   (`3` before line 47; `2` or `5` before line 48, `1` or `4` before line 49, depending on
   the flag). Scanner steps that change neither `X`, `r` nor the flags of others decrease `T`;
   a failed iteration (flag set) restarts at `3 < 4`.

`DWrite`s set all flags, increasing `T`, but each `DWrite` decreases `Stale`, `Bad` or `W`.
The model has atomic base objects (see `README.md`), so this is lock-freedom of Algorithm 3
with `S` and `R` atomic, i.e. Theorem 32 in the case where `S` and `R` are atomic.
-/

namespace Podc.StrongLinSnapshots.Snap

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ## The components of the potential -/

/-- Remaining update work of process `q` (`4` if idle). -/
def uw (C : Cfg n) (q : Fin n) : ℕ :=
  if C.pend q = none then 4 else
    match C.loc q with
    | .u43 _ => 3
    | .u44 _ => 2
    | .u45 _ _ => 1
    | _ => 0

/-- `1` iff the scanner may still write a stale view `ℓ ≠ X` in its current iteration. -/
def stl (X : Vec n) : PC n → ℕ
  | .s49 _ l => if l = X then 0 else 1
  | .s51 l => if l = X then 0 else 1
  | _ => 0

/-- `1` iff the scanner's current iteration writes `R` (line 51), if `X` and `r` stay put. -/
def ww (X r : Vec n) : PC n → ℕ
  | .s47 => if r = X then 0 else 1
  | .s48 s1 => if s1 = X ∧ r = X then 0 else 1
  | .s49 s1 l => if s1 = l ∧ l = r then 0 else 1
  | .s51 _ => 1
  | _ => 0

/-- Remaining steps of the current scan iteration, given the ABA flag `f`. -/
def tt (f : Bool) : PC n → ℕ
  | .s47 => 3
  | .s48 _ => if f then 5 else 2
  | .s49 _ _ => if f then 4 else 1
  | _ => 0

/-- Level 1: update work. -/
def potU (C : Cfg n) : ℕ := ∑ q, uw C q
/-- Level 2: pending stale writes. -/
def potS (C : Cfg n) : ℕ := ∑ q, stl (Sv C) (C.loc q)
/-- Level 3: `R` differs from `S`. -/
def potB (C : Cfg n) : ℕ := if (Rv C).1 = Sv C then 0 else 1
/-- Level 4: iterations that will write `R`. -/
def potW (C : Cfg n) : ℕ := ∑ q, ww (Sv C) (Rv C).1 (C.loc q)
/-- Level 5: remaining iteration steps. -/
def potT (C : Cfg n) : ℕ := ∑ q, tt ((Rv C).2 q) (C.loc q)

/-- The potential: `(U, Stale, Bad, W, T)` in mixed radix. -/
def pot (C : Cfg n) : ℕ :=
  (((potU C * (n + 1) + potS C) * 2 + potB C) * (n + 1) + potW C) * (5 * n + 1) + potT C

/-! ## Arithmetic -/

lemma enc_lt {a a' b b' c : ℕ} (hb : b' < c) (h : a' < a ∨ (a' = a ∧ b' < b)) :
    a' * c + b' < a * c + b := by
  rcases h with h | ⟨rfl, h⟩
  · have : (a' + 1) * c ≤ a * c := Nat.mul_le_mul_right c h
    rw [Nat.add_mul, one_mul] at this
    omega
  · omega

lemma lex5_lt {u u' s s' b b' w w' t t' N M : ℕ} (hs : s' < N) (hb : b' < 2) (hw : w' < N)
    (ht : t' < M)
    (h : u' < u ∨ u' = u ∧ (s' < s ∨ s' = s ∧ (b' < b ∨ b' = b ∧ (w' < w ∨ w' = w ∧ t' < t)))) :
    (((u' * N + s') * 2 + b') * N + w') * M + t' < (((u * N + s) * 2 + b) * N + w) * M + t := by
  have k1 : u' * N + s' < u * N + s ∨
      (u' * N + s' = u * N + s ∧ (b' < b ∨ b' = b ∧ (w' < w ∨ w' = w ∧ t' < t))) := by
    rcases h with h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩
    · exact Or.inl (enc_lt hs (Or.inl h1))
    · exact Or.inl (enc_lt hs (Or.inr ⟨rfl, h2⟩))
    · exact Or.inr ⟨rfl, h3⟩
  have k2 : (u' * N + s') * 2 + b' < (u * N + s) * 2 + b ∨
      ((u' * N + s') * 2 + b' = (u * N + s) * 2 + b ∧ (w' < w ∨ w' = w ∧ t' < t)) := by
    rcases k1 with h0 | ⟨h1, h2 | ⟨rfl, h3⟩⟩
    · exact Or.inl (enc_lt hb (Or.inl h0))
    · exact Or.inl (enc_lt hb (Or.inr ⟨h1, h2⟩))
    · exact Or.inr ⟨by rw [h1], h3⟩
  have k3 : ((u' * N + s') * 2 + b') * N + w' < ((u * N + s) * 2 + b) * N + w ∨
      (((u' * N + s') * 2 + b') * N + w' = ((u * N + s) * 2 + b) * N + w ∧ t' < t) := by
    rcases k2 with h0 | ⟨h1, h2 | ⟨rfl, h3⟩⟩
    · exact Or.inl (enc_lt hw (Or.inl h0))
    · exact Or.inl (enc_lt hw (Or.inr ⟨h1, h2⟩))
    · exact Or.inr ⟨by rw [h1], h3⟩
  exact enc_lt ht k3

lemma sum_le_mul {f : Fin n → ℕ} {c : ℕ} (h : ∀ q, f q ≤ c) : ∑ q, f q ≤ c * n := by
  have := Finset.sum_le_card_nsmul Finset.univ f c (fun q _ => h q)
  simpa [mul_comm] using this

lemma sum_swap {f g : Fin n → ℕ} (p : Fin n) (h : ∀ q, q ≠ p → f q = g q) :
    (∑ q, f q) + g p = (∑ q, g q) + f p := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    Finset.sum_congr rfl (fun q hq => h q (Finset.ne_of_mem_erase hq))]
  ring

lemma stl_le (X : Vec n) (pc : PC n) : stl X pc ≤ 1 := by
  cases pc <;> simp only [stl] <;> (try split_ifs) <;> omega

lemma ww_le (X r : Vec n) (pc : PC n) : ww X r pc ≤ 1 := by
  cases pc <;> simp only [ww] <;> (try split_ifs) <;> omega

lemma tt_le (f : Bool) (pc : PC n) : tt f pc ≤ 5 := by
  cases pc <;> simp only [tt] <;> (try split_ifs) <;> omega

/-- The potential decreases if `(U, Stale, Bad, W, T)` decreases lexicographically. -/
lemma pot_lt_of {C C' : Cfg n}
    (h : potU C' < potU C ∨ potU C' = potU C ∧ (potS C' < potS C ∨ potS C' = potS C ∧
      (potB C' < potB C ∨ potB C' = potB C ∧ (potW C' < potW C ∨ potW C' = potW C ∧
        potT C' < potT C)))) : pot C' < pot C := by
  unfold pot
  refine lex5_lt ?_ ?_ ?_ ?_ h
  · have := sum_le_mul (n := n) (fun q => stl_le (Sv C') (C'.loc q)); unfold potS; omega
  · unfold potB; split_ifs <;> omega
  · have := sum_le_mul (n := n) (fun q => ww_le (Sv C') (Rv C').1 (C'.loc q)); unfold potW
    omega
  · have := sum_le_mul (n := n) (fun q => tt_le ((Rv C').2 q) (C'.loc q)); unfold potT; omega

/-! ## Frame lemmas: a step of `p` changes only `p`'s summands -/

section Frame

variable {C C' : Cfg n} {p : Fin n} (hloc : ∀ q, q ≠ p → C'.loc q = C.loc q)
include hloc

lemma potU_swap (hpend : ∀ q, q ≠ p → C'.pend q = C.pend q) :
    potU C' + uw C p = potU C + uw C' p :=
  sum_swap p fun q hq => by simp only [uw, hloc q hq, hpend q hq]

lemma potS_swap (hX : Sv C' = Sv C) :
    potS C' + stl (Sv C) (C.loc p) = potS C + stl (Sv C) (C'.loc p) := by
  unfold potS; rw [hX]
  exact sum_swap (f := fun q => stl (Sv C) (C'.loc q)) (g := fun q => stl (Sv C) (C.loc q)) p
    fun q hq => by simp only [hloc q hq]

lemma potW_swap (hX : Sv C' = Sv C) (hr : (Rv C').1 = (Rv C).1) :
    potW C' + ww (Sv C) (Rv C).1 (C.loc p) = potW C + ww (Sv C) (Rv C).1 (C'.loc p) := by
  unfold potW; rw [hX, hr]
  exact sum_swap (f := fun q => ww (Sv C) (Rv C).1 (C'.loc q))
    (g := fun q => ww (Sv C) (Rv C).1 (C.loc q)) p fun q hq => by simp only [hloc q hq]

lemma potT_swap (hf : ∀ q, q ≠ p → (Rv C').2 q = (Rv C).2 q) :
    potT C' + tt ((Rv C).2 p) (C.loc p) = potT C + tt ((Rv C').2 p) (C'.loc p) := by
  unfold potT
  exact sum_swap (f := fun q => tt ((Rv C').2 q) (C'.loc q))
    (g := fun q => tt ((Rv C).2 q) (C.loc q)) p fun q hq => by simp only [hloc q hq, hf q hq]

end Frame

/-! ## Every non-response step decreases the potential -/

/-- Every step that is not a response strictly decreases `pot`. -/
lemma pot_lt {C C' : Cfg n} {ℓ : Label (Fin n) (snapObj n)}
    (h : (impl (n := n)).step C ℓ = some C') (hℓ : ∀ p r, ℓ ≠ .ret p r) : pot C' < pot C := by
  apply pot_lt_of
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, -⟩ := Impl.step_inv h
    left
    have := potU_swap (C := C) (C' := C') (p := p)
      (fun q hq => by rw [hloc, Function.update_of_ne hq])
      (fun q hq => by rw [hpend, Function.update_of_ne hq])
    have h1 : uw C p = 4 := by simp [uw, h0]
    have h2 : uw C' p ≤ 3 := by
      rw [uw, hpend, hloc]; cases o <;> simp [impl]
    omega
  | tau p =>
    obtain ⟨h0, hpend, -⟩ := Impl.step_tau h
    have hloc : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q hq =>
      (Impl.step_other h (q := q) (fun h' => hq h'.symm)).1
    have hU := potU_swap hloc (fun q _ => by rw [hpend])
    cases hpc : C.loc p with
    | idle | uRet | sRet _ =>
      exfalso
      obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
      simp [impl, act, hpc] at hact
    | u43 x =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .S (.update p x) (fun _ => .u44 x) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .u44 x := by rw [hC]; simp
      left
      have h1 : uw C p = 3 := by simp [uw, h0, hpc]
      have h2 : uw C' p = 2 := by simp [uw, hpend, h0, hl]
      omega
    | u44 x =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .S .scan (fun s => .u45 x s) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .u45 x (C.mem .S) := by rw [hC]; simp
      left
      have h1 : uw C p = 2 := by simp [uw, h0, hpc]
      have h2 : uw C' p = 1 := by simp [uw, hpend, h0, hl]
      omega
    | u45 x s =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dwrite s) (fun _ => .uRet) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .uRet := by rw [hC]; simp
      left
      have h1 : uw C p = 1 := by simp [uw, h0, hpc]
      have h2 : uw C' p = 0 := by simp [uw, hpend, h0, hl]
      omega
    | s47 =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dread p) (fun r => .s48 r.1) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .s48 (Rv C).1 := by rw [hC]; simp [Rv]
      have hX : Sv C' = Sv C := by rw [hC]; simp [Sv]
      have hR : Rv C' = ((Rv C).1, Function.update (Rv C).2 p false) := by rw [hC]; simp [Rv]
      have hS := potS_swap hloc hX
      have hW := potW_swap hloc hX (by rw [hR])
      have hT := potT_swap hloc (fun q hq => by rw [hR]; exact Function.update_of_ne hq _ _)
      have hB : potB C' = potB C := by simp [potB, hX, hR]
      right
      have e1 : uw C p = 0 := by simp [uw, h0, hpc]
      have e2 : uw C' p = 0 := by simp [uw, hpend, h0, hl]
      refine ⟨by omega, Or.inr ⟨?_, Or.inr ⟨hB, Or.inr ⟨?_, ?_⟩⟩⟩⟩
      · simp only [hpc, hl, stl] at hS; omega
      · simp only [hpc, hl, ww, and_self] at hW; omega
      · simp only [hpc, hl, hR, tt, Function.update_self] at hT; simp at hT; omega
    | s48 s1 =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .S .scan (fun l => .s49 s1 l) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .s49 s1 (Sv C) := by rw [hC]; simp [Sv]
      have hmem : C'.mem = C.mem := by rw [hC]; simp
      have hX : Sv C' = Sv C := by simp [Sv, hmem]
      have hR : Rv C' = Rv C := by simp [Rv, hmem]
      have hS := potS_swap hloc hX
      have hW := potW_swap hloc hX (by rw [hR])
      have hT := potT_swap hloc (fun q hq => by rw [hR])
      have hB : potB C' = potB C := by simp [potB, hX, hR]
      right
      have e1 : uw C p = 0 := by simp [uw, h0, hpc]
      have e2 : uw C' p = 0 := by simp [uw, hpend, h0, hl]
      refine ⟨by omega, Or.inr ⟨?_, Or.inr ⟨hB, Or.inr ⟨?_, ?_⟩⟩⟩⟩
      · simp only [hpc, hl, stl, ite_true] at hS; omega
      · simp only [hpc, hl, ww] at hW
        by_cases h1 : s1 = Sv C <;> by_cases h2 : (Rv C).1 = Sv C <;>
          simp [h1, h2, eq_comm] at hW <;> omega
      · simp only [hpc, hl, hR, tt] at hT; split_ifs at hT <;> omega
    | s49 s1 l =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dread p) (fun r =>
          if s1 = l ∧ l = r.1 then (if r.2 = false then .sRet r.1 else .s47) else .s51 l) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = if s1 = l ∧ l = (Rv C).1 then
          (if (Rv C).2 p = false then .sRet (Rv C).1 else .s47) else .s51 l := by
        rw [hC]; simp [Rv]
      have hX : Sv C' = Sv C := by rw [hC]; simp [Sv]
      have hR : Rv C' = ((Rv C).1, Function.update (Rv C).2 p false) := by rw [hC]; simp [Rv]
      have hS := potS_swap hloc hX
      have hW := potW_swap hloc hX (by rw [hR])
      have hT := potT_swap hloc (fun q hq => by rw [hR]; exact Function.update_of_ne hq _ _)
      have hB : potB C' = potB C := by simp [potB, hX, hR]
      right
      have e1 : uw C p = 0 := by simp [uw, h0, hpc]
      have e2 : uw C' p = 0 := by rw [uw, hl]; split_ifs <;> simp_all
      refine ⟨by omega, ?_⟩
      by_cases hg : s1 = l ∧ l = (Rv C).1
      · obtain ⟨rfl, hr⟩ := hg
        simp only [and_self, hr, ↓reduceIte] at hl
        by_cases hlX : (Rv C).1 = Sv C
        · -- the iteration ends (return or restart because of the flag)
          refine Or.inr ⟨?_, Or.inr ⟨hB, Or.inr ⟨?_, ?_⟩⟩⟩
          · rw [hpc, hl] at hS; simp only [stl, hr, hlX, ite_true] at hS
            split_ifs at hS <;> simp at hS <;> omega
          · rw [hpc, hl] at hW; simp only [ww, hr, hlX, and_self, ite_true] at hW
            split_ifs at hW <;> simp at hW <;> omega
          · rw [hpc, hl] at hT; simp only [tt] at hT
            cases hf : (Rv C).2 p <;> simp [hf] at hT <;> omega
        · -- a stale view `ℓ ≠ X` is dropped
          left
          rw [hpc, hl] at hS; simp only [stl, hr, hlX, ite_false] at hS
          split_ifs at hS <;> simp at hS <;> omega
      · simp only [hg, ↓reduceIte] at hl
        refine Or.inr ⟨?_, Or.inr ⟨hB, Or.inr ⟨?_, ?_⟩⟩⟩
        · rw [hpc, hl] at hS; simp only [stl] at hS; omega
        · rw [hpc, hl] at hW; simp only [ww, hg, ite_false] at hW; omega
        · rw [hpc, hl] at hT; simp only [tt] at hT; split_ifs at hT <;> omega
    | s51 l =>
      have hact : (impl (n := n)).act p (C.loc p) = .access .R (.dwrite l) (fun _ => .s47) := by
        simp [impl, act, hpc]
      have hC := tau_eq h hact
      have hl : C'.loc p = .s47 := by rw [hC]; simp
      have hX : Sv C' = Sv C := by rw [hC]; simp [Sv]
      have hR : Rv C' = (l, fun _ => true) := by rw [hC]; simp [Rv]
      have hS := potS_swap hloc hX
      right
      have e1 : uw C p = 0 := by simp [uw, h0, hpc]
      have e2 : uw C' p = 0 := by simp [uw, hpend, h0, hl]
      refine ⟨by omega, ?_⟩
      by_cases hlX : l = Sv C
      · subst hlX
        have hS' : potS C' = potS C := by rw [hpc, hl] at hS; simp [stl] at hS; omega
        by_cases hr : (Rv C).1 = Sv C
        · -- `R` already holds `X`: the write decreases `W`
          have hW := potW_swap hloc hX (by rw [hR, hr])
          have hB : potB C' = potB C := by simp [potB, hX, hR, hr]
          refine Or.inr ⟨hS', Or.inr ⟨hB, Or.inl ?_⟩⟩
          rw [hpc, hl] at hW; simp only [ww, hr, ite_true] at hW; omega
        · -- `R` now holds `X`: `Bad` decreases
          refine Or.inr ⟨hS', Or.inl ?_⟩
          simp [potB, hX, hR, hr]
      · -- a stale write
        left
        rw [hpc, hl] at hS; simp only [stl, hlX, ite_false] at hS; omega

/-- **Lock-freedom** of Algorithm 3 with atomic `S` and `R` (Theorem 32, atomic case): in every
infinite execution with infinitely many steps, infinitely many operations return. -/
theorem lockFree : (impl (n := n)).LockFree :=
  (impl (n := n)).lockFree_of_potential pot fun _ _ _ _ _ h hℓ => pot_lt h hℓ

end Podc.StrongLinSnapshots.Snap
