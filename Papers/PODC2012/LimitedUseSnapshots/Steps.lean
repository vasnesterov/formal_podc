import Papers.PODC2012.LimitedUseSnapshots.Algorithm
import Cslib.Computability.Distributed.SharedMemory.Potential
import Mathlib.Data.Nat.Log

/-!
# Step complexity of Algorithm 2 (Lemma 3.5 and its erratum)

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity* [AACE15], Lemma 3.5: with balanced trees, `MaxUpdate0` takes `O(log k)` steps,
`MaxUpdate1` takes `O(log h)` steps and `MaxScan` takes `O(log k log h)` steps. The authors'
erratum corrects the step complexity of `MaxUpdate1` to `O(log k log h)`: with the correction
(line 9.5) it performs an embedded `MaxScan`.

In `alg P T fix` the `MaxReg_h` objects `second` are atomic base objects (`Obj.sec a`); an access
to one of them costs `cm` steps (for the balanced max register of Aspnes et al., `cm = ⌈log₂ h⌉`),
an access to a switch (`Obj.sw a`, a 1-bit register) costs `cs` steps (`cs = 1`). We count the
accesses of one operation of a process `p` with these weights (`Obj.cost cs cm`).

## Main results

* `opCost` — the weighted cost of the base-object accesses that `p` performs after invoking `o`
  (at the end of `β`) during the continuation `γ`; `accCost` replays `γ` from a configuration.
  Generic over implementations (CSLib candidates), with `accCost_le_of_potential`: a potential on
  local states that drops by at least `c i` at every access to base object `i` bounds the cost.
* `opCost_le` — per-operation bound in terms of `D = T.depth` (exact for every tree):
  `MaxUpdate0`: `cs·D`; `MaxScan`: `(cs + 3·cm)·D + cm`; `MaxUpdate1`: `cm` (Algorithm 2),
  `cm + (cs + 3·cm)·D + cm` (corrected algorithm).
* Specializations: `switchAccesses_le`, `maxRegAccesses_le` (switch accesses / max-register
  accesses separately: `MaxUpdate0` reads or writes exactly one switch per level and never
  touches a max register; `MaxScan` reads one switch and accesses at most 3 max registers per
  level, plus one at the leaf) and `tauSteps_le` (all accesses, unweighted, as a count of `.tau p`
  labels).
* `Shape.depth_balanced`: the balanced tree with `k` leaves has depth `⌈log₂ k⌉`.
* `lemma_3_5`, `lemma_3_5_erratum`: the paper's conclusions for the balanced tree.
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

/-! ### Weighted cost of the accesses of a process (generic) -/

section Generic

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

-- CSLib candidate
/-- The total weight (`c i` per access to base object `i`) of the base-object accesses of `p`
along the fragment `γ` replayed from the configuration `C` (only the valid prefix of `γ`
counts). -/
noncomputable def accCost (I : Impl A B P L) (c : ι → ℕ) (p : P) :
    Config A B P L → List (Label P A) → ℕ
  | _, [] => 0
  | C, ℓ :: γ =>
    match I.step C ℓ with
    | none => 0
    | some C' =>
      (if ℓ.isTauOf p then
        (match I.act p (C.loc p) with
          | .access i _ _ => c i
          | .ret _ _ => 0)
      else 0) + accCost I c p C' γ

-- CSLib candidate
/-- The weighted cost of the operation `o` invoked by `p` at the end of `β`, during the
continuation `γ` of the execution `β ++ inv p o :: γ` (`0` if `β ++ [inv p o]` is not an
execution). -/
noncomputable def opCost (I : Impl A B P L) (c : ι → ℕ) (p : P) (β : List (Label P A))
    (o : A.Op) (γ : List (Label P A)) : ℕ :=
  match I.run (β ++ [.inv p o]) with
  | some C => accCost I c p C γ
  | none => 0

-- CSLib candidate
/-- **Weighted step complexity from a potential.** If the potential `Φ` of a local state drops
by at least `c i` at every access to base object `i`, then along a fragment in which `p` is
pending and does not return, the weighted cost of `p`'s accesses is at most the potential of its
local state at the start. -/
theorem accCost_le_of_potential (I : Impl A B P L) (c : ι → ℕ) (p : P) (Φ : L → ℕ)
    (hΦ : ∀ l i o k, I.act p l = .access i o k → ∀ x, Φ (k x) + c i ≤ Φ l) :
    ∀ (γ : List (Label P A)) (C : Config A B P L), C.pend p ≠ none → (∀ r, .ret p r ∉ γ) →
      accCost I c p C γ ≤ Φ (C.loc p)
  | [], _, _, _ => Nat.zero_le _
  | ℓ :: γ, C, hp, hr => by
    simp only [accCost]
    cases hs : I.step C ℓ with
    | none => exact Nat.zero_le _
    | some C₁ =>
      simp only
      have hp₁ : C₁.pend p ≠ none := by
        by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 hp
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
          | tau q => rw [(Impl.step_tau hs).2.1]; exact hp
        · rw [(Impl.step_other hs hq).2]; exact hp
      have ih := accCost_le_of_potential I c p Φ hΦ γ C₁ hp₁
        (fun r hr' => hr r (List.mem_cons_of_mem _ hr'))
      rcases I.step_tau_or_other hs hp hp₁ with rfl | ⟨hq, hloc⟩
      · obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
        rw [hloc, Function.update_self] at ih
        have := hΦ _ i o k hact ((B i).δ (C.mem i) o).2
        simp only [Label.isTauOf_tau, decide_true, ↓reduceIte, hact]
        omega
      · have ht : ℓ.isTauOf p = false := by
          cases ℓ <;> simp_all [Label.proc]
        rw [hloc] at ih
        simp only [ht, Bool.false_eq_true, ↓reduceIte, zero_add]
        exact ih

-- CSLib candidate
/-- **Weighted step complexity of an operation.** Under the potential hypothesis, the weighted
cost of an operation `o` of `p` is at most the potential of the local state right after its
invocation, until it returns. -/
theorem opCost_le_of_potential (I : Impl A B P L) (c : ι → ℕ) (p : P) (Φ : L → ℕ)
    (hΦ : ∀ l i o k, I.act p l = .access i o k → ∀ x, Φ (k x) + c i ≤ Φ l)
    (β : List (Label P A)) (o : A.Op) (γ : List (Label P A)) (hr : ∀ r, .ret p r ∉ γ) :
    ∃ l, opCost I c p β o γ ≤ Φ (I.invoke p l o) := by
  unfold opCost
  cases h : I.run (β ++ [.inv p o]) with
  | none => exact ⟨I.locInit p, Nat.zero_le _⟩
  | some C₁ =>
    simp only
    rw [Impl.run_concat] at h
    cases hβ : I.run β with
    | none => simp [hβ] at h
    | some C₀ =>
      simp only [hβ, Option.bind_some] at h
      obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv h
      have := accCost_le_of_potential I c p Φ hΦ γ C₁ (by simp [hpend]) hr
      rw [hloc, Function.update_self] at this
      exact ⟨C₀.loc p, this⟩

end Generic

/-! ### The potential of Algorithm 2 -/

/-- Cost of an access: `cs` for a switch (1-bit register), `cm` for a `MaxReg_h`. -/
def Obj.cost (cs cm : ℕ) : Obj → ℕ
  | .sw _ => cs
  | .sec _ => cm

@[simp] lemma Obj.cost_sw (cs cm : ℕ) (a : List Bool) : (Obj.sw a).cost cs cm = cs := rfl
@[simp] lemma Obj.cost_sec (cs cm : ℕ) (a : List Bool) : (Obj.sec a).cost cs cm = cm := rfl

/-- Remaining cost of a `MaxScan` starting at node `a`: `(cs + 3cm)` per level below `a`, plus
the final `ReadMax` at the leaf. -/
def scanPot (T : Shape) (cs cm : ℕ) (a : List Bool) : ℕ :=
  (cs + 3 * cm) * (T.subD a).depth + cm

/-- Bound on `scanPot` at the children of `a`. -/
def childPot (T : Shape) (cs cm : ℕ) (a : List Bool) : ℕ :=
  (cs + 3 * cm) * ((T.subD a).depth - 1) + cm

/-- The potential (remaining weighted cost) of a local state of Algorithm 2. -/
def pot (T : Shape) (fix : Bool) (cs cm : ℕ) : Loc → ℕ
  | .idle => 0
  | .d0 _ a => cs * ((T.subD a).depth + a.count true)
  | .up _ a => cs * a.count true
  | .w1 _ => cm + if fix then scanPot T cs cm [] else 0
  | .s1 _ a => scanPot T cs cm a
  | .s2 _ a _ => childPot T cs cm a + cs + 2 * cm
  | .s3 _ a _ => childPot T cs cm a + cm
  | .s4 _ a => childPot T cs cm a + 2 * cm
  | .s5 _ a _ => childPot T cs cm a + cm
  | .rt _ => 0

lemma deepRight_none : ∀ a : List Bool, deepRight a = none → a.count true = 0
  | [], _ => rfl
  | b :: c, h => by
    simp only [deepRight] at h
    cases hc : deepRight c with
    | some _ => simp [hc] at h
    | none =>
      simp only [hc] at h
      cases b
      · simp [deepRight_none c hc]
      · simp at h

lemma deepRight_some : ∀ (a a' : List Bool), deepRight a = some a' →
    a'.count true + 1 = a.count true
  | [], _, h => by simp [deepRight] at h
  | b :: c, a', h => by
    simp only [deepRight] at h
    cases hc : deepRight c with
    | some a₀ =>
      simp only [hc, Option.some.injEq] at h; subst h
      have := deepRight_some c a₀ hc
      cases b <;> simp <;> omega
    | none =>
      simp only [hc] at h
      cases b
      · simp at h
      · simp only [↓reduceIte, Option.some.injEq] at h; subst h
        simp [deepRight_none c hc]

lemma upAct_pot {T : Shape} {fix : Bool} {cs cm v : ℕ} {a : List Bool} {i : Obj}
    {o : (baseObj i).Op} {k : (baseObj i).Resp → Loc} (h : upAct v a = .access i o k)
    (x : (baseObj i).Resp) : pot T fix cs cm (k x) + i.cost cs cm ≤ cs * a.count true := by
  unfold upAct at h
  cases hd : deepRight a with
  | none => simp [hd] at h
  | some a' =>
    simp only [hd, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun _ => Loc.up v a' := eq_of_heq hk.symm
    subst hk'
    have := deepRight_some a a' hd
    simp only [pot, Obj.cost_sw]
    rw [← this, Nat.mul_add, Nat.mul_one]

lemma d0Act_pot {T : Shape} {fix : Bool} {cs cm v : ℕ} :
    ∀ (t : Shape) (w : ℕ) (a : List Bool), T.subD a = t →
      ∀ {i : Obj} {o : (baseObj i).Op} {k : (baseObj i).Resp → Loc},
      d0Act v w t a = .access i o k → ∀ x,
      pot T fix cs cm (k x) + i.cost cs cm ≤ cs * (t.depth + a.count true)
  | .leaf, w, a, _, i, o, k, h, x => by
    simp only [d0Act] at h
    have := upAct_pot (T := T) (fix := fix) (cs := cs) (cm := cm) h x
    simpa [Shape.depth] using this
  | .node l r, w, a, ht, i, o, k, h, x => by
    simp only [d0Act] at h
    split_ifs at h with hw
    · simp only [Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      have hk' : k = fun b => if b then Loc.up v a else Loc.d0 v (a ++ [false]) :=
        eq_of_heq hk.symm
      subst hk'
      have hdepth : (Shape.node l r).depth = max l.depth r.depth + 1 := rfl
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte, pot, Shape.subD_append_false ht,
          List.count_append, Obj.cost_sw, hdepth]
        simp only [List.count_singleton, Bool.false_eq_true, beq_iff_eq,
          ↓reduceIte, add_zero]
        have : l.depth + a.count true + 1 ≤ max l.depth r.depth + 1 + a.count true := by omega
        calc cs * (l.depth + a.count true) + cs = cs * (l.depth + a.count true + 1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ this
      · simp only [↓reduceIte, pot, Obj.cost_sw, hdepth]
        calc cs * a.count true + cs = cs * (a.count true + 1) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    · have := d0Act_pot (T := T) (fix := fix) (cs := cs) (cm := cm) r (w - l.size) (a ++ [true]) (Shape.subD_append_true ht) h x
      have hdepth : (Shape.node l r).depth = max l.depth r.depth + 1 := rfl
      simp only [List.count_append, List.count_singleton, beq_self_eq_true, ↓reduceIte] at this
      refine this.trans (Nat.mul_le_mul_left _ ?_)
      rw [hdepth]; omega

/-- The potential drops by at least the cost of the accessed object at every access. -/
lemma pot_access (T : Shape) (fix : Bool) (cs cm : ℕ) (l : Loc) (i : Obj)
    (o : (baseObj i).Op) (k : (baseObj i).Resp → Loc) (h : act T fix l = .access i o k)
    (x : (baseObj i).Resp) : pot T fix cs cm (k x) + i.cost cs cm ≤ pot T fix cs cm l := by
  cases l with
  | idle => simp [act] at h
  | rt r => simp [act] at h
  | d0 v a => exact d0Act_pot _ _ a rfl h x
  | up v a => exact upAct_pot h x
  | w1 v =>
    simp only [act, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun _ => if fix then Loc.s1 true [] else Loc.rt (0, 0) := eq_of_heq hk.symm
    subst hk'
    cases fix <;> simp [pot]; omega
  | s1 e a =>
    simp only [act] at h
    have hsc : scanPot T cs cm a = (cs + 3 * cm) * (T.subD a).depth + cm := rfl
    cases ht : T.subD a with
    | leaf =>
      simp only [ht, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      have hk' : k = fun x => Loc.rt (if e then (0, 0) else (T.lo a, x)) := eq_of_heq hk.symm
      subst hk'
      simp [pot, hsc]
    | node l r =>
      simp only [ht, Action.access.injEq] at h
      obtain ⟨rfl, -, hk⟩ := h
      have hk' : k = fun x => Loc.s2 e a x := eq_of_heq hk.symm
      subst hk'
      simp only [pot, childPot, hsc, ht, Obj.cost_sec]
      have hd : (Shape.node l r).depth = (Shape.node l r).depth - 1 + 1 := by
        simp [Shape.depth]
      rw [hd, Nat.add_sub_cancel]
      ring_nf; omega
  | s2 e a y =>
    simp only [act, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun b => if b then Loc.s4 e a else Loc.s3 e a y := eq_of_heq hk.symm
    subst hk'
    cases x <;> simp [pot] <;> omega
  | s3 e a y =>
    simp only [act, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun _ => Loc.s1 e (a ++ [false]) := eq_of_heq hk.symm
    subst hk'
    simp only [pot, scanPot, childPot, Obj.cost_sec]
    have : (T.subD (a ++ [false])).depth ≤ (T.subD a).depth - 1 := by
      cases ht : T.subD a with
      | leaf => simp [Shape.subD_append, ht, Shape.depth]
      | node l r => rw [Shape.subD_append_false ht]; simp [Shape.depth]
    have := Nat.mul_le_mul_left (cs + 3 * cm) this
    omega
  | s4 e a =>
    simp only [act, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun x => Loc.s5 e a x := eq_of_heq hk.symm
    subst hk'
    simp [pot]; omega
  | s5 e a y =>
    simp only [act, Action.access.injEq] at h
    obtain ⟨rfl, -, hk⟩ := h
    have hk' : k = fun _ => Loc.s1 e (a ++ [true]) := eq_of_heq hk.symm
    subst hk'
    simp only [pot, scanPot, childPot, Obj.cost_sec]
    have : (T.subD (a ++ [true])).depth ≤ (T.subD a).depth - 1 := by
      cases ht : T.subD a with
      | leaf => simp [Shape.subD_append, ht, Shape.depth]
      | node l r => rw [Shape.subD_append_true ht]; simp [Shape.depth]
    have := Nat.mul_le_mul_left (cs + 3 * cm) this
    omega

/-! ### Per-operation bounds -/

/-- The bound of Lemma 3.5 (with the erratum's correction for `fix = true`) on the weighted cost
of one operation, for a tree of depth `D`: `MaxUpdate0` `cs·D`, `MaxScan` `(cs + 3cm)·D + cm`,
`MaxUpdate1` `cm` (Algorithm 2) or `cm + (cs + 3cm)·D + cm` (corrected algorithm). -/
def opBound (D : ℕ) (fix : Bool) (cs cm : ℕ) : MAOp → ℕ
  | .upd0 _ => cs * D
  | .upd1 _ => cm + if fix then (cs + 3 * cm) * D + cm else 0
  | .scan => (cs + 3 * cm) * D + cm

lemma pot_invokeLoc (T : Shape) (fix : Bool) (cs cm : ℕ) (o : MAOp) :
    pot T fix cs cm (invokeLoc o) = opBound T.depth fix cs cm o := by
  cases o <;> simp [invokeLoc, pot, opBound, scanPot]

/-- **Lemma 3.5 of [AACE15], weighted form (with the erratum).** In every execution
`β ++ inv p o :: γ` of Algorithm 2 (`fix = false`) or of its corrected version (`fix = true`) over
a tree `T` of depth `D`, in which the operation `o` of `p` has not returned by the end of `γ`, the
accesses of `p` during `γ` cost (switch access `cs`, max-register access `cm`) at most
`opBound D fix cs cm o`. -/
theorem opCost_le (P : Type) [DecidableEq P] (T : Shape) (fix : Bool) (cs cm : ℕ) (p : P)
    (β γ : List (Label P maxArrObj)) (o : MAOp) (hr : ∀ r, .ret p r ∉ γ) :
    opCost (alg P T fix) (Obj.cost cs cm) p β o γ ≤ opBound T.depth fix cs cm o := by
  obtain ⟨l, h⟩ := opCost_le_of_potential (alg P T fix) (Obj.cost cs cm) p (pot T fix cs cm)
    (fun l i o k h x => pot_access T fix cs cm l i o k h x) β o γ hr
  simpa [alg, pot_invokeLoc] using h

/-- **Lemma 3.5 of [AACE15]: switch accesses.** An operation accesses at most `D = T.depth`
switches: `MaxUpdate0` reads or writes one switch per level of its path (at a left step it reads
the switch, at a right step it writes it on the way back), `MaxScan` reads one switch per level;
`MaxUpdate1` accesses none (Algorithm 2) or those of its embedded `MaxScan` (corrected). -/
theorem switchAccesses_le (P : Type) [DecidableEq P] (T : Shape) (fix : Bool) (p : P)
    (β γ : List (Label P maxArrObj)) (o : MAOp) (hr : ∀ r, .ret p r ∉ γ) :
    opCost (alg P T fix) (Obj.cost 1 0) p β o γ ≤
      match o with
      | .upd0 _ => T.depth
      | .upd1 _ => if fix then T.depth else 0
      | .scan => T.depth := by
  have := opCost_le P T fix 1 0 p β γ o hr
  cases o <;> cases fix <;> simpa [opBound] using this

/-- **Lemma 3.5 of [AACE15]: max-register accesses.** `MaxUpdate0` accesses no `MaxReg_h`,
`MaxScan` at most `3D + 1` (`ReadMax`, `WriteMax` at a left step, `ReadMax`, `ReadMax`, `WriteMax`
at a right step, and one `ReadMax` at the leaf), `MaxUpdate1` one (Algorithm 2) or
`1 + (3D + 1)` (corrected). -/
theorem maxRegAccesses_le (P : Type) [DecidableEq P] (T : Shape) (fix : Bool) (p : P)
    (β γ : List (Label P maxArrObj)) (o : MAOp) (hr : ∀ r, .ret p r ∉ γ) :
    opCost (alg P T fix) (Obj.cost 0 1) p β o γ ≤
      match o with
      | .upd0 _ => 0
      | .upd1 _ => if fix then 1 + (3 * T.depth + 1) else 1
      | .scan => 3 * T.depth + 1 := by
  have := opCost_le P T fix 0 1 p β γ o hr
  cases o <;> cases fix <;> simpa [opBound] using this

/-- **Lemma 3.5 of [AACE15]: number of steps.** In every execution `β ++ inv p o :: γ` in which
`o` has not returned by the end of `γ`, `p` takes at most `D` (`MaxUpdate0`), `4D + 1`
(`MaxScan`), `1` (`MaxUpdate1` of Algorithm 2) or `4D + 2` (`MaxUpdate1` of the corrected
algorithm) steps in `γ`, where `D = T.depth`. -/
theorem tauSteps_le (P : Type) [DecidableEq P] (T : Shape) (fix : Bool) (p : P)
    (β γ : List (Label P maxArrObj)) (o : MAOp) (hv : (alg P T fix).Valid (β ++ .inv p o :: γ))
    (hr : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤
      match o with
      | .upd0 _ => T.depth
      | .upd1 _ => if fix then 4 * T.depth + 2 else 1
      | .scan => 4 * T.depth + 1 := by
  obtain ⟨l, h⟩ := Impl.tauSteps_le_potential_invoke (alg P T fix)
    (fun _ => pot T fix 1 1)
    (fun _ l i o k h x => by
      have := pot_access T fix 1 1 l i o k h x
      cases i <;> simp at this <;> omega) hv hr
  simp only [alg, pot_invokeLoc] at h
  cases o <;> cases fix <;> simp [opBound] at h ⊢ <;> omega

/-! ### The balanced tree -/

/-- The balanced tree with `k ≥ 1` leaves has `k` leaves. -/
lemma Shape.size_balanced : ∀ k : ℕ, (Shape.balanced k).size = max k 1
  | 0 => by simp [Shape.balanced, Shape.size]
  | 1 => by simp [Shape.balanced, Shape.size]
  | k + 2 => by
    rw [Shape.balanced, Shape.size, Shape.size_balanced ((k + 3) / 2),
      Shape.size_balanced ((k + 2) / 2)]
    omega

/-- The balanced tree with `k` leaves has depth `⌈log₂ k⌉`. -/
lemma Shape.depth_balanced : ∀ k : ℕ, (Shape.balanced k).depth = Nat.clog 2 k
  | 0 => by simp [Shape.balanced, Shape.depth]
  | 1 => by simp [Shape.balanced, Shape.depth]
  | k + 2 => by
    have hc : Nat.clog 2 (k + 2) = Nat.clog 2 ((k + 3) / 2) + 1 := by
      rw [Nat.clog_of_two_le (by norm_num) (by omega)]
      congr 3
    rw [Shape.balanced, Shape.depth, Shape.depth_balanced ((k + 3) / 2),
      Shape.depth_balanced ((k + 2) / 2), hc,
      max_eq_left (Nat.clog_mono_right 2 (by omega))]

/-! ### The paper's conclusions -/

/-- **Lemma 3.5 of [AACE15]** (Algorithm 2, balanced tree with `k` leaves, each `MaxReg_h` access
costing `ch` steps, e.g. `ch = ⌈log₂ h⌉` for the balanced max register): the weighted cost of an
operation is at most `⌈log₂ k⌉` for `MaxUpdate0` (`O(log k)`), `ch` for `MaxUpdate1`
(`O(log h)`), and `(1 + 3ch)⌈log₂ k⌉ + ch ≤ 4 (⌈log₂ k⌉ + 1)(ch + 1)` for `MaxScan`
(`O(log k log h)`). Switch accesses cost one step. -/
theorem lemma_3_5 (P : Type) [DecidableEq P] (k ch : ℕ) (p : P)
    (β γ : List (Label P maxArrObj)) (hr : ∀ r, .ret p r ∉ γ) :
    (∀ v, opCost (alg P (.balanced k) false) (Obj.cost 1 ch) p β (.upd0 v) γ ≤ Nat.clog 2 k) ∧
    (∀ v, opCost (alg P (.balanced k) false) (Obj.cost 1 ch) p β (.upd1 v) γ ≤ ch) ∧
    opCost (alg P (.balanced k) false) (Obj.cost 1 ch) p β .scan γ ≤
      (1 + 3 * ch) * Nat.clog 2 k + ch ∧
    (1 + 3 * ch) * Nat.clog 2 k + ch ≤ 4 * (Nat.clog 2 k + 1) * (ch + 1) := by
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · simpa [opBound, Shape.depth_balanced] using opCost_le P (.balanced k) false 1 ch p β γ (.upd0 v) hr
  · simpa [opBound] using opCost_le P (.balanced k) false 1 ch p β γ (.upd1 v) hr
  · simpa [opBound, Shape.depth_balanced] using opCost_le P (.balanced k) false 1 ch p β γ .scan hr
  · nlinarith

/-- **Lemma 3.5 of [AACE15] as corrected by the erratum** (corrected algorithm, balanced tree
with `k` leaves, `MaxReg_h` access cost `ch`): `MaxUpdate0` costs at most `⌈log₂ k⌉`, `MaxScan`
at most `(1 + 3ch)⌈log₂ k⌉ + ch`, and `MaxUpdate1`, which now performs an embedded `MaxScan`,
at most `ch + (1 + 3ch)⌈log₂ k⌉ + ch ≤ 5 (⌈log₂ k⌉ + 1)(ch + 1)` (`O(log k log h)` instead of
`O(log h)`). -/
theorem lemma_3_5_erratum (P : Type) [DecidableEq P] (k ch : ℕ) (p : P)
    (β γ : List (Label P maxArrObj)) (hr : ∀ r, .ret p r ∉ γ) :
    (∀ v, opCost (alg P (.balanced k) true) (Obj.cost 1 ch) p β (.upd0 v) γ ≤ Nat.clog 2 k) ∧
    (∀ v, opCost (alg P (.balanced k) true) (Obj.cost 1 ch) p β (.upd1 v) γ ≤
      ch + ((1 + 3 * ch) * Nat.clog 2 k + ch)) ∧
    opCost (alg P (.balanced k) true) (Obj.cost 1 ch) p β .scan γ ≤
      (1 + 3 * ch) * Nat.clog 2 k + ch ∧
    ch + ((1 + 3 * ch) * Nat.clog 2 k + ch) ≤ 5 * (Nat.clog 2 k + 1) * (ch + 1) := by
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · simpa [opBound, Shape.depth_balanced] using opCost_le P (.balanced k) true 1 ch p β γ (.upd0 v) hr
  · simpa [opBound, Shape.depth_balanced] using opCost_le P (.balanced k) true 1 ch p β γ (.upd1 v) hr
  · simpa [opBound, Shape.depth_balanced] using opCost_le P (.balanced k) true 1 ch p β γ .scan hr
  · nlinarith

end Podc.LimitedUseSnapshots
