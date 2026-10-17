import Papers.PODC2019.CryptoConsensusNumber.System

/-!
# Lemma 1: consensus for `k` processes from one `k`-shared asset-transfer object (Figure 2)

Processes `p ∈ {0, …, k-1}` (the paper's `1, …, k`; we write `id(p) = p + 1`). Shared objects:
registers `R[p]` (initially `⊥`) and one asset-transfer object with an account `a = 0` owned by
all `k` processes, initial balance `2k`, and an account `s = 1` (no owners). Code of `p` with
input `v`:

1. `R[p].write(v)`;
2. `AT.transfer(a, s, 2k - id(p))`;
3. `β := AT.read(a)`; decide `R[β - 1].read()` (the paper's `R[AT.read(a)].read()`).

Any two amounts sum to at least `2k + 1 > 2k`, so exactly the first transfer succeeds, leaving
balance `id(w)` for its issuer `w`, who wrote `R[w]` before.
-/

namespace CryptoCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

namespace Lemma1

variable (n : ℕ)

/-- The registers `R[p]`, values `Option Bool` (`⊥ = none`). -/
abbrev Reg : Fin n → ObjSpec := fun _ => register (Option Bool) none

/-- Owner map: account `0` (the paper's `a`) is owned by all processes, account `1` (`s`) by
nobody. -/
def μ₁ : Unit → Fin 2 → Finset (Fin n) := fun _ a => if a = 0 then Finset.univ else ∅

/-- The objects of Figure 2. -/
abbrev Obj : Fin n ⊕ Unit → ObjSpec := atSys (Reg n) (μ₁ n)

/-- Program counter of Figure 2. -/
inductive Stage where
  | write (v : Bool)
  | transfer
  | readBal
  | readReg (β : ℕ)
  | done (v : Bool)

/-- The amount withdrawn by `p`: `2k - id(p)` with `id(p) = p + 1`. -/
def amount (p : Fin n) : ℕ := 2 * n - (p.val + 1)

/-- The register `R[β - 1]` (`p` itself if out of range, which never happens). -/
def regIdx (p : Fin n) (β : ℕ) : Fin n := if h : β - 1 < n then ⟨β - 1, h⟩ else p

/-- A balance response as a number. -/
def toNat : Bool ⊕ ℕ → ℕ := Sum.elim (fun _ => 0) id

/-- The code of Figure 2 (local states carry the process identifier). -/
def act : Fin n × Stage → Act (Obj n) (Fin n × Stage)
  | (p, .write v) => .access (.inl p) (RWOp.write (some v)) (fun _ => (p, .transfer))
  | (p, .transfer) =>
    .access (.inr ()) (ATOp.transfer p 0 1 (amount n p)) (fun _ => (p, .readBal))
  | (p, .readBal) => .access (.inr ()) (ATOp.read 0) (fun r => (p, .readReg (toNat r)))
  | (p, .readReg β) =>
    .access (.inl (regIdx n p β)) RWOp.read (fun r => (p, .done (Option.getD r false)))
  | (_, .done v) => .out v

/-- Initial values: registers `⊥`, balance `2k` on account `a = 0`, `0` on `s = 1`. -/
def mem₀ : (i : Fin n ⊕ Unit) → (Obj n i).State
  | .inl _ => (none : Option Bool)
  | .inr () => (fun a : Fin 2 => if a = 0 then 2 * n else 0)

/-- The algorithm of Figure 2. -/
abbrev alg : Alg n (Obj n) where
  L := Fin n × Stage
  init p v := (p, .write v)
  act := act n
  mem₀ := mem₀ n

variable {n}

/-- Balance of account `a`. -/
def bal (C : Cfg (alg n)) : ℕ := (C.mem (.inr ()) : Fin 2 → ℕ) 0

/-- Register contents. -/
def reg (C : Cfg (alg n)) (i : Fin n) : Option Bool := C.mem (.inl i)

/-- Stages after the transfer. -/
def AfterT : Stage → Prop
  | .readBal => True
  | .readReg _ => True
  | .done _ => True
  | _ => False

/-- The invariant. -/
structure Inv (x : Fin n → Bool) (C : Cfg (alg n)) : Prop where
  id : ∀ p, (C.loc p).1 = p
  wr : ∀ p v, (C.loc p).2 = .write v → v = x p
  rg : ∀ p, (∀ v, (C.loc p).2 ≠ .write v) → reg C p = some (x p)
  bl : bal C = 2 * n ∨ ∃ w : Fin n, bal C = w.val + 1 ∧ AfterT (C.loc w).2
  aft : ∀ p, AfterT (C.loc p).2 → bal C ≠ 2 * n
  rd : ∀ p β, (C.loc p).2 = .readReg β → bal C = β
  dn : ∀ p v, (C.loc p).2 = .done v → ∃ w : Fin n, bal C = w.val + 1 ∧ v = x w

/-! ### One step of each kind -/

section Steps

variable {C : Cfg (alg n)} {p : Fin n}

lemma reg_update_inl (C : Cfg (alg n)) (i : Fin n) (v : Option Bool) (q : Fin n) :
    (Function.update C.mem (.inl i) v : (j : Fin n ⊕ Unit) → (Obj n j).State) (.inl q) =
      if q = i then v else reg C q := by
  by_cases h : q = i
  · subst h; simp only [↓reduceIte]; exact Function.update_self _ _ _
  · simp only [h, ↓reduceIte, reg]; exact Function.update_of_ne (by simpa using h) _ _

lemma step_write {v : Bool} (hl : C.loc p = (p, .write v)) :
    (C.stepP p).loc = Function.update C.loc p (p, .transfer) ∧
    (∀ q, reg (C.stepP p) q = if q = p then some v else reg C q) ∧ bal (C.stepP p) = bal C := by
  have hact : (alg n).act (C.loc p) = .access (.inl p) (RWOp.write (some v)) (fun _ => (p, .transfer)) := by
    rw [hl]; rfl
  rw [stepP_of_access C hact]
  refine ⟨rfl, fun q => ?_, ?_⟩
  · simp only [reg]; exact reg_update_inl C p _ q
  · simp only [bal]; rw [Function.update_of_ne (by simp)]

lemma bal_transfer (m : Fin 2 → ℕ) (p : Fin n) :
    ((atSpec (Fin n) (Fin 2) (μ₁ n ()) (fun _ => 0)).δ m (.transfer p 0 1 (amount n p))).1 0 =
      if amount n p ≤ m 0 then m 0 - amount n p else m 0 := by
  rw [atSpec_transfer]
  by_cases h : amount n p ≤ m 0
  · have hown : p ∈ μ₁ n () 0 := by simp [μ₁]
    simp [hown, h, moveFunds_apply]
  · simp [h]

lemma step_transfer (hl : C.loc p = (p, .transfer)) :
    (C.stepP p).loc = Function.update C.loc p (p, .readBal) ∧
    (∀ q, reg (C.stepP p) q = reg C q) ∧
    bal (C.stepP p) = if amount n p ≤ bal C then bal C - amount n p else bal C := by
  have hact : (alg n).act (C.loc p) = .access (.inr ()) (ATOp.transfer p 0 1 (amount n p))
      (fun _ => (p, .readBal)) := by
    rw [hl]; rfl
  rw [stepP_of_access C hact]
  refine ⟨rfl, fun q => ?_, ?_⟩
  · simp only [reg]; rw [Function.update_of_ne (by simp)]
  · simp only [bal, Function.update_self]
    exact bal_transfer _ p

lemma step_readBal (hl : C.loc p = (p, .readBal)) :
    (C.stepP p).loc = Function.update C.loc p (p, .readReg (bal C)) ∧
    (∀ q, reg (C.stepP p) q = reg C q) ∧ bal (C.stepP p) = bal C := by
  have hact : (alg n).act (C.loc p) = .access (.inr ()) (ATOp.read 0)
      (fun r => (p, .readReg (toNat r))) := by
    rw [hl]; rfl
  rw [stepP_of_access C hact]
  refine ⟨rfl, fun q => ?_, ?_⟩
  · simp only [reg]; rw [Function.update_of_ne (by simp)]
  · simp only [bal, Function.update_self]; rfl

lemma step_readReg {β : ℕ} (hl : C.loc p = (p, .readReg β)) :
    (C.stepP p).loc =
      Function.update C.loc p (p, .done (Option.getD (reg C (regIdx n p β)) false)) ∧
    (∀ q, reg (C.stepP p) q = reg C q) ∧ bal (C.stepP p) = bal C := by
  have hact : (alg n).act (C.loc p) = .access (.inl (regIdx n p β)) RWOp.read
      (fun r => (p, .done (Option.getD r false))) := by
    rw [hl]; rfl
  rw [stepP_of_access C hact]
  refine ⟨rfl, fun q => ?_, ?_⟩
  · exact congrFun (Function.update_eq_self _ C.mem) _
  · simp only [bal]; rw [Function.update_of_ne (by simp)]

lemma step_done {v : Bool} (hl : C.loc p = (p, .done v)) : C.stepP p = C :=
  stepP_of_out C (show (alg n).act (C.loc p) = .out v by rw [hl]; rfl)

end Steps

/-! ### The invariant -/

lemma inv_init (x : Fin n → Bool) : Inv x (initCfg (alg n) x) where
  id p := rfl
  wr p v h := by
    change ((p, Stage.write (x p)) : Fin n × Stage).2 = _ at h
    cases h; rfl
  rg p h := absurd rfl (h (x p))
  bl := Or.inl (by simp [bal, initCfg, alg, mem₀])
  aft p h := by
    change AfterT ((p, Stage.write (x p)) : Fin n × Stage).2 at h
    exact h.elim
  rd p β h := by
    change ((p, Stage.write (x p)) : Fin n × Stage).2 = _ at h
    cases h
  dn p v h := by
    change ((p, Stage.write (x p)) : Fin n × Stage).2 = _ at h
    cases h

lemma loc_update (C : Cfg (alg n)) (p q : Fin n) (l : Fin n × Stage) :
    Function.update C.loc p l q = if q = p then l else C.loc q := by
  by_cases h : q = p
  · subst h; simp only [↓reduceIte]; exact Function.update_self _ _ _
  · simp only [h, ↓reduceIte]; exact Function.update_of_ne h _ _

lemma amount_gt {p w : Fin n} (hpw : p ≠ w) : w.val + 1 < amount n p := by
  have h1 := p.isLt
  have h2 := w.isLt
  have : p.val ≠ w.val := fun h => hpw (Fin.ext h)
  unfold amount
  omega

lemma inv_of_step {x : Fin n → Bool} {C D : Cfg (alg n)} {p : Fin n} (hI : Inv x C) (st : Stage)
    (hloc : D.loc = Function.update C.loc p (p, st))
    (hreg : ∀ q, q ≠ p → reg D q = reg C q)
    (hregp : (∀ v, st ≠ .write v) → reg D p = some (x p))
    (hwr : ∀ v, st = .write v → v = x p)
    (hbl : bal D = 2 * n ∨ ∃ w : Fin n, bal D = w.val + 1 ∧
      ((w = p ∧ AfterT st) ∨ (w ≠ p ∧ AfterT (C.loc w).2)))
    (haftp : AfterT st → bal D ≠ 2 * n)
    (haft : ∀ q, q ≠ p → AfterT (C.loc q).2 → bal D ≠ 2 * n)
    (hrdp : ∀ β, st = .readReg β → bal D = β)
    (hrd : ∀ q, q ≠ p → ∀ β, (C.loc q).2 = .readReg β → bal D = β)
    (hdnp : ∀ v, st = .done v → ∃ w : Fin n, bal D = w.val + 1 ∧ v = x w)
    (hdn : ∀ q, q ≠ p → ∀ v, (C.loc q).2 = .done v → ∃ w : Fin n, bal D = w.val + 1 ∧ v = x w) :
    Inv x D := by
  have hl : ∀ q, D.loc q = if q = p then (p, st) else C.loc q := by
    intro q; rw [hloc, loc_update]
  refine ⟨fun q => ?_, fun q v h => ?_, fun q h => ?_, ?_, fun q h => ?_, fun q β h => ?_,
    fun q v h => ?_⟩
  · rw [hl]; split_ifs with hq
    · exact hq.symm
    · exact hI.id q
  · rw [hl] at h; split_ifs at h with hq
    · subst hq; exact hwr v h
    · exact hI.wr q v h
  · rw [hl] at h; split_ifs at h with hq
    · subst hq; exact hregp h
    · rw [hreg q hq]; exact hI.rg q h
  · rcases hbl with h | ⟨w, hw, h | h⟩
    · exact Or.inl h
    · refine Or.inr ⟨w, hw, ?_⟩
      rw [hl]; simp only [h.1, ↓reduceIte]; exact h.2
    · refine Or.inr ⟨w, hw, ?_⟩
      rw [hl]; simp only [h.1, ↓reduceIte]; exact h.2
  · rw [hl] at h; split_ifs at h with hq
    · exact haftp h
    · exact haft q hq h
  · rw [hl] at h; split_ifs at h with hq
    · exact hrdp β h
    · exact hrd q hq β h
  · rw [hl] at h; split_ifs at h with hq
    · exact hdnp v h
    · exact hdn q hq v h

lemma inv_step (hn : 0 < n) (x : Fin n → Bool) (C : Cfg (alg n)) (p : Fin n) (hI : Inv x C) :
    Inv x (C.stepP p) := by
  have hid := hI.id p
  rcases hl : C.loc p with ⟨p', st⟩
  rw [hl] at hid
  simp only at hid
  subst hid
  cases st with
  | write v =>
    obtain ⟨hloc, hreg, hbal⟩ := step_write hl
    have hv : v = x p' := hI.wr p' v (by rw [hl])
    subst hv
    refine inv_of_step hI .transfer hloc (fun q hq => by rw [hreg]; simp only [hq, ↓reduceIte])
      (fun _ => by rw [hreg]; simp only [↓reduceIte]) (fun _ h => by cases h) ?_ (fun h => h.elim)
      (fun q _ h => by rw [hbal]; exact hI.aft q h) (fun _ h => by cases h)
      (fun q _ β h => by rw [hbal]; exact hI.rd q β h) (fun _ h => by cases h)
      (fun q _ v h => by rw [hbal]; exact hI.dn q v h)
    rw [hbal]
    rcases hI.bl with h | ⟨w, hw, haw⟩
    · exact Or.inl h
    · have hwp : w ≠ p' := by
        rintro rfl; rw [hl] at haw; exact haw
      exact Or.inr ⟨w, hw, Or.inr ⟨hwp, haw⟩⟩
  | transfer =>
    obtain ⟨hloc, hreg, hbal⟩ := step_transfer hl
    have key : bal (C.stepP p') ≠ 2 * n ∧
        (∃ w : Fin n, bal (C.stepP p') = w.val + 1 ∧
          ((w = p' ∧ AfterT .readBal) ∨ (w ≠ p' ∧ AfterT (C.loc w).2))) ∧
        (bal C ≠ 2 * n → bal (C.stepP p') = bal C) := by
      rw [hbal]
      rcases hI.bl with h | ⟨w, hw, haw⟩
      · have : amount n p' ≤ bal C := by unfold amount; omega
        simp only [this, ↓reduceIte]
        have hp := p'.isLt
        exact ⟨by unfold amount; omega, ⟨p', by unfold amount; omega, Or.inl ⟨rfl, trivial⟩⟩,
          fun h' => absurd h h'⟩
      · have hwp : p' ≠ w := by
          rintro rfl; rw [hl] at haw; exact haw
        have := amount_gt hwp
        have hnot : ¬ amount n p' ≤ bal C := by omega
        simp only [hnot, ↓reduceIte]
        have hw' := w.isLt
        exact ⟨by omega, ⟨w, hw, Or.inr ⟨Ne.symm hwp, haw⟩⟩, by intros; first | rfl | trivial⟩
    obtain ⟨hne, hbl, hsame⟩ := key
    refine inv_of_step hI .readBal hloc (fun q _ => hreg q)
      (fun _ => by rw [hreg]; exact hI.rg p' (by rw [hl]; simp)) (fun _ h => by cases h)
      (Or.inr hbl) (fun _ => hne) (fun _ _ _ => hne) (fun _ h => by cases h)
      (fun q _ β h => by rw [hsame (hI.aft q (by rw [h]; trivial))]; exact hI.rd q β h)
      (fun _ h => by cases h)
      (fun q _ v h => by rw [hsame (hI.aft q (by rw [h]; trivial))]; exact hI.dn q v h)
  | readBal =>
    obtain ⟨hloc, hreg, hbal⟩ := step_readBal hl
    have hne : bal C ≠ 2 * n := hI.aft p' (by rw [hl]; trivial)
    refine inv_of_step hI (.readReg (bal C)) hloc (fun q _ => hreg q)
      (fun _ => by rw [hreg]; exact hI.rg p' (by rw [hl]; simp)) (fun _ h => by cases h) ?_
      (fun _ => by rw [hbal]; exact hne) (fun q _ h => by rw [hbal]; exact hI.aft q h)
      (fun β h => by cases h; exact hbal) (fun q _ β h => by rw [hbal]; exact hI.rd q β h)
      (fun _ h => by cases h) (fun q _ v h => by rw [hbal]; exact hI.dn q v h)
    rw [hbal]
    rcases hI.bl with h | ⟨w, hw, haw⟩
    · exact Or.inl h
    · by_cases hwp : w = p'
      · exact Or.inr ⟨w, hw, Or.inl ⟨hwp, trivial⟩⟩
      · exact Or.inr ⟨w, hw, Or.inr ⟨hwp, haw⟩⟩
  | readReg β =>
    obtain ⟨hloc, hreg, hbal⟩ := step_readReg hl
    have hβ : bal C = β := hI.rd p' β (by rw [hl])
    have hne : bal C ≠ 2 * n := hI.aft p' (by rw [hl]; trivial)
    obtain ⟨w, hw, haw⟩ : ∃ w : Fin n, bal C = w.val + 1 ∧ AfterT (C.loc w).2 := by
      rcases hI.bl with h | h
      · exact absurd h hne
      · exact h
    have hidx : regIdx n p' β = w := by
      unfold regIdx
      have := w.isLt
      simp only [show β - 1 < n by omega, ↓reduceDIte]
      ext; simp; omega
    have hrw : reg C w = some (x w) := hI.rg w (fun v h => by rw [h] at haw; exact haw)
    refine inv_of_step hI (.done (Option.getD (reg C (regIdx n p' β)) false)) hloc
      (fun q _ => hreg q)
      (fun _ => by rw [hreg]; exact hI.rg p' (by rw [hl]; simp)) (fun _ h => by cases h) ?_
      (fun _ => by rw [hbal]; exact hne) (fun q _ h => by rw [hbal]; exact hI.aft q h)
      (fun _ h => by cases h) (fun q _ β h => by rw [hbal]; exact hI.rd q β h)
      (fun v h => ?_) (fun q _ v h => by rw [hbal]; exact hI.dn q v h)
    · rw [hbal]
      by_cases hwp : w = p'
      · exact Or.inr ⟨w, hw, Or.inl ⟨hwp, trivial⟩⟩
      · exact Or.inr ⟨w, hw, Or.inr ⟨hwp, haw⟩⟩
    · cases h
      refine ⟨w, by rw [hbal]; exact hw, ?_⟩
      rw [hidx, hrw]; rfl
  | done v =>
    rw [step_done hl]; exact hI

lemma inv_out (hn : 0 < n) (x : Fin n → Bool) (C : Cfg (alg n)) (hI : Inv x C) :
    ∃ q, ∀ p w, C.Out p w → w = x q := by
  rcases hI.bl with h | ⟨w, hw, -⟩
  · refine ⟨⟨0, hn⟩, fun p v hp => ?_⟩
    exfalso
    rcases hl : C.loc p with ⟨p', st⟩
    have hid := hI.id p
    rw [hl] at hid; simp only at hid; subst hid
    cases st with
    | done v' => exact hI.aft p' (by rw [hl]; trivial) h
    | _ =>
      simp only [Cfg.Out, hl] at hp
      cases hp
  · refine ⟨w, fun p v hp => ?_⟩
    rcases hl : C.loc p with ⟨p', st⟩
    have hid := hI.id p
    rw [hl] at hid; simp only at hid; subst hid
    cases st with
    | done v' =>
      have hv : v' = v := by
        simp only [Cfg.Out, hl] at hp
        change Act.out v' = Act.out v at hp
        cases hp; rfl
      subst hv
      obtain ⟨w', hw', hv'⟩ := hI.dn p' v' (by rw [hl])
      have : w' = w := Fin.ext (by omega)
      rw [hv', this]
    | _ =>
      simp only [Cfg.Out, hl] at hp
      cases hp

/-- Rank: remaining steps. -/
def rank : Fin n × Stage → ℕ
  | (_, .write _) => 4
  | (_, .transfer) => 3
  | (_, .readBal) => 2
  | (_, .readReg _) => 1
  | (_, .done _) => 0

lemma rank_lt (l : Fin n × Stage) (i : Fin n ⊕ Unit) (o : (Obj n i).Op)
    (κ : (Obj n i).Resp → Fin n × Stage) (r : (Obj n i).Resp)
    (h : (alg n).act l = .access i o κ) : rank (κ r) < rank l := by
  obtain ⟨p, st⟩ := l
  cases st <;> simp only [alg, act] at h <;> (try cases h) <;> simp [rank]

/-- **Lemma 1 (Figure 2).** For `k ≥ 1` processes, the algorithm of Figure 2 solves wait-free
consensus using registers and one asset-transfer object (with an account owned by all `k`
processes), and processes transfer only under their own identity. -/
theorem lemma_1 (hn : 0 < n) : WFConsensus (alg n) ∧ Honest (Reg n) (μ₁ n) (alg n) := by
  refine ⟨wfConsensus_of_inv Inv inv_init (fun x C p hI => inv_step hn x C p hI)
    (fun x C hI => inv_out hn x C hI) rank rank_lt, ?_⟩
  intro x α hα p j q a b y κ h
  have hI := inv_run_crashFree (Inv x) (fun C p hI => inv_step hn x C p hI) α _ (inv_init x) hα
  have hid := hI.id p
  rcases hl : (run (initCfg (alg n) x) α).loc p with ⟨p', st⟩
  rw [hl] at h hid
  simp only at hid
  subst hid
  cases st <;> simp only [alg, act] at h <;> (try cases h)
  rfl

/-- The asset-transfer object of Figure 2 is `k`-shared: account `a` has exactly `k` owners. -/
lemma μ₁_card : (μ₁ n () 0).card = n ∧ KShared (μ₁ n ()) n := by
  refine ⟨by simp [μ₁], fun a => ?_⟩
  by_cases h : a = 0
  · simp [μ₁, h]
  · simp [μ₁, h]

end Lemma1

end CryptoCons
