import Papers.PODC2020.RecoverableMutexRMR.Model

/-!
# The invariant of the Chan–Woelfel algorithm (definitions)

`Inv s g` is an inductive invariant of configurations `s` with ghost state `g`. It contains the
paper's Lemma 2.1 (in state form), the potential `Φ = D + |I| − C ≥ 0` of Lemma 2.3, and a
second potential `Ψ ≥ Φ` bounding the number of skipped tickets by twice the number of crashes
(Lemma 2.10 / the claim "the total number of skipped tickets is at most twice the number of
process crashes" of Section 3.1).
-/

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-- `p ∈ I_t` (Section 3.3): `p` holds a ticket that is not skipped and has not incremented `D`
since obtaining it. -/
def inI (s : Cfg P) (g : Ghost P) (p : P) : Prop :=
  g.cur p ≠ 0 ∧ s.A (g.cur p) ≠ .skipped ∧ g.pend p = true

instance (s : Cfg P) (g : Ghost P) : DecidablePred (inI s g) := fun p => by
  unfold inI; infer_instance

/-- `|I_t|`. -/
def Isize (s : Cfg P) (g : Ghost P) : ℕ := (Finset.univ.filter (inI s g)).card

/-- The potential `Φ_t = D_t + |I_t| − C_t` of Lemmas 2.2–2.3. -/
def Phi (s : Cfg P) (g : Ghost P) : ℤ := (s.D : ℤ) + Isize s g - s.C

/-- Processes holding a "crash credit" for a ticket that is not skipped. -/
def crCount (s : Cfg P) (g : Ghost P) : ℕ :=
  (Finset.univ.filter fun p => g.cr p = true ∧ s.A (g.cur p) ≠ .skipped).card

/-- Lost tickets that are still unclaimed and unskipped. -/
def lostCount (s : Cfg P) (g : Ghost P) : ℕ := (g.lost.filter fun x => s.A x = .empty).card

/-- Number of processes about to execute line 15. -/
def nR15 (s : Cfg P) : ℕ := (Finset.univ.filter fun p => s.pc p = .r15).card

/-- Number of skipped tickets (entries `A[x] = −1`). -/
def nSkipped (s : Cfg P) : ℕ := ((Finset.range (s.C + 1)).filter fun x => s.A x = .skipped).card

/-- The second potential `Ψ = Φ + crCount + lostCount`. -/
def Psi (s : Cfg P) (g : Ghost P) : ℤ := Phi s g + crCount s g + lostCount s g

/-- `q` is in its `Exit()` section after line 10, on its way to move `Token` past its own
ticket `T + 1`. -/
def OnTrack (s : Cfg P) (q : P) : Prop :=
  match s.pc q with
  | .x9 | .x10 | .r15 | .r16 | .m34 .ex => True
  | .m35 .ex ℓ | .m36 .ex ℓ _ | .m38 .ex ℓ _ _ | .m42 .ex ℓ => ℓ = s.T
  | .m40 .ex ℓ q' | .m41 .ex ℓ q' => ℓ = s.T ∧ q' = q
  | _ => False

/-- Invariant of the return address of a `Move_Token()` call. -/
def RetInv (s : Cfg P) (p : P) : Ret → Prop
  | .wr w => s.X p = false ∧ (s.W p).1 = w ∧ w ≠ 0 ∧ s.A w = .claimed p
  | .ex => s.X p = true ∧ s.W p = (0, false)

/-- Hypothesis of the potential argument of Lemma 2.3 for a process about to skip `ℓ + 1`. -/
def JHyp (s : Cfg P) (g : Ghost P) (ℓ : ℕ) : Prop :=
  s.A (ℓ + 1) = .empty ∧ ∃ o, inI s g o ∧ g.cur o = ℓ + 1

/-- Local invariant of process `p`, by program counter. -/
def LI (s : Cfg P) (g : Ghost P) (p : P) : Prop :=
  match s.pc p with
  | .rem => s.W p = (0, false) ∧ s.X p = false
  | .l3 => s.X p = false
  | .l4 => s.X p = false ∧ s.W p = (0, false)
  | .l5 c => s.X p = false ∧ s.W p = (0, false) ∧ c = g.cur p ∧ c ≠ 0 ∧
      (s.A c = .empty ∨ s.A c = .skipped) ∧ g.pend p = true
  | .w23 => s.X p = false ∧ (s.W p).1 ≠ 0
  | .w24 w => s.X p = false ∧ (s.W p).1 = w ∧ w ≠ 0
  | .w25 w => s.X p = false ∧ (s.W p).1 = w ∧ w ≠ 0 ∧ s.A w ≠ .empty
  | .w26 => s.X p = false ∧ (s.W p).1 = g.cur p ∧ g.cur p ≠ 0 ∧ s.A (g.cur p) = .skipped
  | .w28 w => RetInv s p (.wr w)
  | .w31 w => RetInv s p (.wr w)
  | .cs => s.X p = false ∧ (s.W p).2 = true
  | .x9 => (s.W p).2 = true ∨ (s.W p = (0, false) ∧ s.X p = true)
  | .x10 => s.X p = true
  | .x12 => s.X p = true ∧ s.W p = (0, false)
  | .r15 => True
  | .r16 => g.cr p = true
  | .r18 => s.X p = false ∧ g.cr p = true
  | .m34 r => RetInv s p r
  | .m35 r ℓ => RetInv s p r ∧ ℓ ≤ s.T
  | .m36 r ℓ d => RetInv s p r ∧ ℓ ≤ s.T ∧ d ≤ s.D
  | .m38 r ℓ c d => RetInv s p r ∧ ℓ ≤ s.T ∧ ℓ < c ∧ c ≤ s.C ∧ d ≤ s.D ∧
      (c ≤ d → JHyp s g ℓ → 1 ≤ Phi s g)
  | .m40 r ℓ q => RetInv s p r ∧ ℓ ≤ s.T ∧ s.A (ℓ + 1) = .claimed q
  | .m41 r ℓ q => RetInv s p r ∧ ℓ ≤ s.T ∧ s.A (ℓ + 1) = .claimed q ∧
      (q = p → s.W p ≠ (ℓ + 1, false))
  | .m42 r ℓ => RetInv s p r ∧ ℓ ≤ s.T ∧ s.A (ℓ + 1) = .claimed p ∧ (s.W p).1 ≠ ℓ + 1
  | .m46 r ℓ => RetInv s p r ∧ ℓ ≤ s.T ∧ ℓ + 1 ≤ s.C ∧ (JHyp s g ℓ → 1 ≤ Phi s g)
  | .m47 r ℓ => RetInv s p r ∧ ℓ ≤ s.T ∧ s.A (ℓ + 1) ≠ .empty
  | .m48 r ℓ => RetInv s p r ∧ ℓ ≤ s.T ∧ s.A (ℓ + 1) = .skipped

/-- Program counters at which `pend p` may hold for a non-skipped ticket (`p ∈ I`). -/
def PendPC (k : PC P) : Prop :=
  match k with
  | .l5 _ | .w23 | .w24 _ | .w25 _ | .w28 _ | .r15 => True
  | _ => False

/-- Program counters before line 28 (after line 3) and in `Recover()` after line 15. -/
def CrPC (k : PC P) : Prop :=
  match k with
  | .w23 | .w24 _ | .w25 _ | .w26 | .w28 _ | .r16 | .r18 => True
  | _ => False

/-- The "future tickets" part of the invariant for process `q`: a claimed ticket beyond `Token`
is `q`'s current ticket, or `q` left the critical section with ticket `T + 1` and is on its way
to move `Token`. -/
def Future (s : Cfg P) (q : P) : Prop :=
  ∀ x, s.A x = .claimed q → s.T < x →
    (s.W q).1 = x ∨ (x = s.T + 1 ∧ s.W q = (0, false) ∧ s.X q = true ∧ OnTrack s q)

/-- The inductive invariant. -/
structure Inv (s : Cfg P) (g : Ghost P) : Prop where
  T_le : s.T ≤ s.C
  A_ne : ∀ x, s.A x ≠ .empty → x ≠ 0 ∧ x ≤ s.C
  A_tok : ∀ x, x ≠ 0 → x ≤ s.T → s.A x ≠ .empty
  /-- Lemma 2.1 (15) in state form: tickets up to `Token` are done. -/
  done : ∀ x q, x ≤ s.T → s.A x = .claimed q → (s.W q).1 ≠ x
  /-- Only the owner of ticket `Token + 1` can be allowed to enter (gives Lemma 2.1 (16)). -/
  grant : ∀ q, (s.W q).2 = true → (s.W q).1 = s.T + 1 ∧ s.A (s.T + 1) = .claimed q
  future : ∀ q, Future s q
  own_claimed : ∀ x q, s.A x = .claimed q → g.own x = some q
  own_le : ∀ x q, g.own x = some q → x ≠ 0 ∧ x ≤ s.C
  own_ex : ∀ x, x ≠ 0 → x ≤ s.C → ∃ q, g.own x = some q
  cur_le : ∀ p, g.cur p ≤ s.C
  own_cur : ∀ p, g.cur p ≠ 0 → g.own (g.cur p) = some p
  W_cur : ∀ p, (s.W p).1 ≠ 0 → (s.W p).1 = g.cur p
  X_W : ∀ p, s.X p = true → (s.W p).2 = true ∨ s.W p = (0, false)
  pend_pc : ∀ p, g.pend p = true → PendPC (s.pc p) ∨ s.A (g.cur p) = .skipped
  cr_pc : ∀ p, CrPC (s.pc p) → g.pend p = true ∨ g.cr p = true
  l3_cr : ∀ p, s.pc p = .l3 → g.pend p = true ∨ g.cr p = true ∨ s.W p = (0, false)
  I_cr : ∀ p, inI s g p → g.cr p = false
  lost_wit : ∀ x, x ≠ 0 → x ≤ s.C → s.A x = .empty →
    x ∈ g.lost ∨ ∃ o, g.own x = some o ∧ g.cur o = x ∧ (g.pend o = true ∨ g.cr o = true)
  /-- Lemma 2.3. -/
  phi_nonneg : 0 ≤ Phi s g
  psi_bound : Psi s g + 2 * (nR15 s : ℤ) + nSkipped s ≤ 2 * (g.ncr : ℤ)
  loc : ∀ p, LI s g p

end Podc.RecoverableMutexRMR
