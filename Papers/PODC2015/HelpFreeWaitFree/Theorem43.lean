import Papers.PODC2015.HelpFreeWaitFree.Loop
import Papers.PODC2015.HelpFreeWaitFree.Examples

/-!
# Theorem 4.3: exact order types have no wait-free help-free implementation

The base objects are registers supporting `read`, `write` and `cas` (CSLib `casObject`, one per
location `i : ι`, with values in `V i`).

* `claim_4_5_10` — **Claim 4.5.10 / Corollary 4.1**: at the exit of the inner loop, the next steps
  of `p₁` and `p₂` are successful `cas` operations on the same location; after `p₂`'s `cas`,
  `p₁`'s `cas` fails, so `p₂` and `p₃` cannot tell whether `p₁` took it.
* `theorem_4_3` — **Theorem 4.3** (for the weak, owner-only notion of help-freedom, which makes it
  stronger): with at least three processes, no wait-free implementation of an exact order type
  from read/write/cas registers has a weakly help-free linearization function.
* `theorem_4_3_helpFree` — the paper's statement: no wait-free linearizable implementation of an
  exact order type is help-free.
* `queue_not_waitFree_helpFree` — in particular for the FIFO queue.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {P L : Type} [DecidableEq P]

/-- A step following the program that changes the memory is a base-object access that changes
the accessed object. -/
lemma lab_access {B : ι → ObjSpec} {I : Impl A B P L} {C C' : Config A B P L} {p : P} {o : A.Op}
    (hs : I.step C (labOf I C p o) = some C') (hm : C'.mem ≠ C.mem) :
    C.pend p ≠ none ∧ labOf I C p o = .tau p ∧ ∃ i o' k, I.act p (C.loc p) = .access i o' k ∧
      ((B i).δ (C.mem i) o').1 ≠ C.mem i := by
  unfold labOf at hs ⊢
  by_cases hp : C.pend p = none
  · simp only [hp, ↓reduceIte] at hs
    exact absurd (Impl.step_inv hs).2.2.2.2 hm
  · simp only [hp, ↓reduceIte] at hs ⊢
    refine ⟨hp, ?_⟩
    unfold Impl.nextLabel at hs ⊢
    split at hs
    · rename_i i o' k hact
      refine ⟨rfl, i, o', k, hact, fun he => hm ?_⟩
      obtain ⟨-, -, i', o'', k', hact', hmem, -⟩ := Impl.step_tau hs
      rw [hact] at hact'; cases hact'
      rw [hmem, he, Function.update_eq_self]
    · exact absurd (Impl.step_ret hs).2.2.1 hm

/-- A base-object step of a pending process. -/
lemma tau_step {B : ι → ObjSpec} {I : Impl A B P L} {C : Config A B P L} {p : P} {i : ι}
    {o : (B i).Op} {k : (B i).Resp → L} (hp : C.pend p ≠ none)
    (hact : I.act p (C.loc p) = .access i o k) :
    ∃ C', I.step C (.tau p) = some C' ∧
      C'.mem = Function.update C.mem i ((B i).δ (C.mem i) o).1 ∧ C'.pend = C.pend ∧
      ∀ q, q ≠ p → C'.loc q = C.loc q :=
  ⟨_, Impl.step_tau_eq_some hp hact, rfl, rfl, fun _ hq => Function.update_of_ne hq _ _⟩

/-- Taus of `p₁`, `p₂` preserve `Std`. -/
lemma Ctx.Std.append_taus {B : ι → ObjSpec} {I : Impl A B P L} (X : Ctx I) {n : ℕ}
    {h u : List (Label P A)} (hs : X.Std n h) (hv : I.Valid (h ++ u))
    (hu : ∀ γ ∈ u, γ = .tau X.p₁ ∨ γ = .tau X.p₂) : X.Std n (h ++ u) := by
  have hops : ∀ q, opsOf u q = [] := fun q => by
    simp only [opsOf, List.filterMap_eq_nil_iff]
    intro γ hγ; rcases hu γ hγ with rfl | rfl <;> rfl
  refine Ctx.Std.append X hs hv (fun γ hγ => ?_) ?_ ?_
  · rcases hu γ hγ with rfl | rfl
    · left; rfl
    · right; rfl
  · rw [opsOf_append, hops, List.append_nil]; exact hs.ops1
  · rw [opsOf_append, hops, List.append_nil]; exact hs.ops2

section CAS

variable {V : ι → Type} [∀ i, DecidableEq (V i)] {v₀ : ∀ i, V i}
variable {I : Impl A (fun i => casObject (V i) (v₀ i)) P L} (X : Ctx I)

namespace Ctx

/-- **Claim 4.5.10 and Corollary 4.1.** At the exit of the inner loop (`Crit n h`), `p₂`'s next
step is a `cas` deciding `op₂` before `op₁`, and after it `p₁`'s next step (a failed `cas`)
changes neither the memory nor `p₂`, `p₃`.

The paper rules out a non-modifying step of `p₁` or `p₂` using only Claim 4.5.3 (1); this does
not work (a failed `cas` of `p₁` may succeed after `p₂`'s step), and we use Claim 4.5.3 (2) and
(3) instead. -/
theorem claim_4_5_10 {n m : ℕ} {h : List (Label P A)} (hJ : X.J n h) (hcrit : X.Crit n h)
    (hsep : X.Sep n m) :
    ∃ Cx Cy, I.run (h ++ [.tau X.p₂]) = some Cx ∧ I.run (h ++ [.tau X.p₂, .tau X.p₁]) = some Cy ∧
      Impl.AgreeOn {X.p₂, X.p₃} Cx Cy ∧ X.DB (h ++ [.tau X.p₂]) (X.p₂, n) (X.p₁, 0) := by
  obtain ⟨hr1, hr2⟩ := Std.undecided X hJ.std hsep hJ.und12 hJ.und21
  obtain ⟨C, hC⟩ := hJ.std.valid
  obtain ⟨d1, d2⟩ := hcrit C hC
  obtain ⟨C1, hs1⟩ := step_labOf (I := I) C X.p₁ X.op (X.allowed _ _)
  obtain ⟨C2, hs2⟩ := step_labOf (I := I) C X.p₂ (X.W n) (X.allowed _ _)
  have hrun1 : I.run (h ++ [labOf I C X.p₁ X.op]) = some C1 := by rw [I.run_concat, hC]; exact hs1
  have hrun2 : I.run (h ++ [labOf I C X.p₂ (X.W n)]) = some C2 := by rw [I.run_concat, hC]; exact hs2
  -- both steps change the memory (Claim 4.5.3 (2), (3))
  have hm1 : C1.mem ≠ C.mem := by
    intro heq
    have hag : Impl.AgreeOn {X.p₂, X.p₃} C1 C := ⟨heq, fun q hq => ?_, fun q hq => ?_⟩
    · exact X.claim_4_5_3_2 hJ.std (Std.append_lab1 X hJ.std hC hr1 hs1) hC hrun1 hag hsep hr2
        (by rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [labOf_proc]; exact X.h12)];
            simpa using hr2) hJ.und12 d1
    all_goals
      have hq' : X.p₁ ≠ q := by
        rcases hq with rfl | hq
        · exact X.h12
        · rw [Set.mem_singleton_iff.1 hq]; exact X.h13
      have := Impl.step_other hs1 (by rw [labOf_proc]; exact hq')
    · exact this.1
    · exact this.2
  have hm2 : C2.mem ≠ C.mem := by
    intro heq
    have hag : Impl.AgreeOn {X.p₁, X.p₃} C2 C := ⟨heq, fun q hq => ?_, fun q hq => ?_⟩
    · exact X.claim_4_5_3_3 hJ.std (Std.append_lab2 X hJ.std hC hr2 hs2) hC hrun2 hag hsep hr1
        (by rw [respsOf_concat, Label.retOf_eq_none_of_proc_ne (by rw [labOf_proc]; exact X.h12.symm)];
            simpa using hr1) hJ.und21 d2
    all_goals
      have hq' : X.p₂ ≠ q := by
        rcases hq with rfl | hq
        · exact X.h12.symm
        · rw [Set.mem_singleton_iff.1 hq]; exact X.h23
      have := Impl.step_other hs2 (by rw [labOf_proc]; exact hq')
    · exact this.1
    · exact this.2
  obtain ⟨hp1, hl1, i₁, o₁, k₁, hact1, hch1⟩ := lab_access hs1 hm1
  obtain ⟨hp2, hl2, i₂, o₂, k₂, hact2, hch2⟩ := lab_access hs2 hm2
  rw [hl1] at hs1 hrun1 d1
  rw [hl2] at hs2 hrun2 d2
  -- the four configurations
  obtain ⟨C1', hs1', hm1', hpd1, hlc1⟩ := tau_step hp1 hact1
  obtain ⟨C2', hs2', hm2', hpd2, hlc2⟩ := tau_step hp2 hact2
  rw [hs1] at hs1'; cases hs1'
  rw [hs2] at hs2'; cases hs2'
  obtain ⟨C12, s12, hm12, hpd12, hlc12⟩ := tau_step (C := C1) (by rw [hpd1]; exact hp2)
    (by rw [hlc1 _ X.h12.symm]; exact hact2)
  obtain ⟨C21, s21, hm21, hpd21, hlc21⟩ := tau_step (C := C2) (by rw [hpd2]; exact hp1)
    (by rw [hlc2 _ X.h12]; exact hact1)
  have hrun12 : I.run (h ++ [.tau X.p₁, .tau X.p₂]) = some C12 := by
    rw [show h ++ [Label.tau X.p₁, .tau X.p₂] = (h ++ [.tau X.p₁]) ++ [.tau X.p₂] by simp,
      I.run_concat, hrun1]
    exact s12
  have hrun21 : I.run (h ++ [.tau X.p₂, .tau X.p₁]) = some C21 := by
    rw [show h ++ [Label.tau X.p₂, .tau X.p₁] = (h ++ [.tau X.p₂]) ++ [.tau X.p₁] by simp,
      I.run_concat, hrun2]
    exact s21
  have hstd12 := Std.append_taus X hJ.std ⟨_, hrun12⟩ (by simp)
  have hstd21 := Std.append_taus X hJ.std ⟨_, hrun21⟩ (by simp)
  have hstd1 := Std.append_taus X hJ.std ⟨_, hrun1⟩ (by simp)
  have hstd2 := Std.append_taus X hJ.std ⟨_, hrun2⟩ (by simp)
  -- Claim 4.5.3 (1) applied to two histories with the same memory
  have key : ∀ {h₁ h₂ : List (Label P A)} {D₁ D₂ : Config A (fun i => casObject (V i) (v₀ i)) P L},
      X.Std n h₁ → X.Std n h₂ → I.run h₁ = some D₁ → I.run h₂ = some D₂ →
      D₁.mem = D₂.mem → D₁.loc X.p₃ = C.loc X.p₃ → D₂.loc X.p₃ = C.loc X.p₃ →
      D₁.pend = C.pend → D₂.pend = C.pend →
      X.DB h₁ (X.p₁, 0) (X.p₂, n) → X.DB h₂ (X.p₂, n) (X.p₁, 0) → False := by
    intro h₁ h₂ D₁ D₂ hs₁ hs₂ hD₁ hD₂ hmem hl₁ hl₂ hp₁ hp₂ hd₁ hd₂
    refine X.claim_4_5_3_1 hs₁ hs₂ hD₁ hD₂ ⟨hmem, fun q hq => ?_, fun q hq => ?_⟩ hsep hd₁ hd₂
    · rw [Set.mem_singleton_iff.1 hq, hl₁, hl₂]
    · rw [hp₁, hp₂]
  have l12 : C12.loc X.p₃ = C.loc X.p₃ := by rw [hlc12 _ X.h23.symm, hlc1 _ X.h13.symm]
  have l21 : C21.loc X.p₃ = C.loc X.p₃ := by rw [hlc21 _ X.h13.symm, hlc2 _ X.h23.symm]
  have p12 : C12.pend = C.pend := by rw [hpd12, hpd1]
  have p21 : C21.pend = C.pend := by rw [hpd21, hpd2]
  -- same location
  by_cases hi : i₁ = i₂
  swap
  · exfalso
    refine key hstd12 hstd21 hrun12 hrun21 ?_ l12 l21 p12 p21 (by simpa using d1.append [.tau X.p₂]) (by simpa using d2.append [.tau X.p₁])
    rw [hm12, hm21, hm1', hm2', Function.update_of_ne (Ne.symm hi), Function.update_of_ne hi,
      Function.update_comm hi]
  subst hi
  -- `p₁`'s step is not a write
  have hw1 : ∀ w, o₁ ≠ .write w := by
    rintro w rfl
    refine key hstd1 hstd21 hrun1 hrun21 ?_ (hlc1 _ X.h13.symm) l21 hpd1 p21 d1 (by simpa using d2.append [.tau X.p₁])
    rw [hm21, hm1', hm2', Function.update_idem]
  have hw2 : ∀ w, o₂ ≠ .write w := by
    rintro w rfl
    refine key hstd12 hstd2 hrun12 hrun2 ?_ l12 (hlc2 _ X.h23.symm) p12 hpd2 (by simpa using d1.append [.tau X.p₂]) d2
    rw [hm12, hm1', hm2', Function.update_idem]
  -- both are successful `cas` with expected value `C.mem i₁`
  have hcas : ∀ (o : CASOp (V i₁)), ((casObject (V i₁) (v₀ i₁)).δ (C.mem i₁) o).1 ≠ C.mem i₁ →
      (∀ w, o ≠ .write w) → ∃ n', o = .cas (C.mem i₁) n' ∧ n' ≠ C.mem i₁ := by
    intro o hch hw
    cases o with
    | read => exact absurd rfl hch
    | write w => exact absurd rfl (hw w)
    | cas e n' =>
      simp only [casObject] at hch
      split_ifs at hch with he
      · exact ⟨n', by rw [he], hch⟩
      · exact absurd rfl hch
  obtain ⟨n₁, rfl, -⟩ := hcas o₁ hch1 hw1
  obtain ⟨n₂, rfl, hn₂⟩ := hcas o₂ hch2 hw2
  -- after `p₂`'s `cas`, `p₁`'s `cas` fails
  refine ⟨_, _, hrun2, hrun21, ⟨?_, fun q hq => ?_, fun q hq => ?_⟩, d2⟩
  · rw [hm21, hm2']
    simp [casObject, hn₂]
  · have : q ≠ X.p₁ := by
      rcases hq with rfl | hq
      · exact X.h12.symm
      · rw [Set.mem_singleton_iff.1 hq]; exact X.h13.symm
    rw [hlc21 _ this]
  · rw [hpd21]

end Ctx

/-- **Theorem 4.3** (strong form). Let `A` be an exact order type and `I` a wait-free
implementation of `A` from read/write/cas registers, in a system with (at least) three distinct
processes that may invoke any operation. Then no linearization function of `I` is help-free,
even in the weak sense that a step deciding `a` before `b` must be taken by the owner of `a`. -/
theorem theorem_4_3 (I : Impl A (fun i => casObject (V i) (v₀ i)) P L) (hA : ExactOrder A)
    (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) (hwf : I.WaitFree) : ¬ WeaklyHelpFree I := by
  classical
  rintro ⟨f, hlin, hown⟩
  obtain ⟨op, W, R, hEO⟩ := hA
  let X : Ctx I := ⟨f, hlin, hown, hwf, hall, p₁, p₂, p₃, h12, h13, h23, op, W, R⟩
  have hsep : ∀ n, ∃ m, X.Sep n m := fun n => by
    obtain ⟨m, hm, hd⟩ := hEO n
    exact ⟨m, hm, hd⟩
  -- one iteration of the main loop
  have hiter : ∀ (n : ℕ) (h : List (Label P A)), X.Inv n h → ∃ y, X.Inv (n + 1) y ∧ h <+: y ∧
      h.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁) := by
    intro n h hi
    obtain ⟨m, hm⟩ := hsep n
    obtain ⟨m', hm'⟩ := hsep (n + 1)
    obtain ⟨h', hJ', hcrit, hpre⟩ := X.loop_terminates hi.j hm
    obtain ⟨Cx, Cy, hx, hy, hag, hdx⟩ := X.claim_4_5_10 hJ' hcrit hm
    obtain ⟨y, hy', hpre', hcnt⟩ := X.critical_step hJ' hm hm' hx hy hag hdx
    refine ⟨y, hy', hpre.trans hpre', lt_of_le_of_lt ?_ hcnt⟩
    obtain ⟨u, rfl⟩ := hpre
    simp [List.countP_append]
  let G := {g : ℕ × List (Label P A) // X.Inv g.1 g.2}
  have hnext : ∀ g : G, ∃ y, X.Inv (g.1.1 + 1) y ∧ g.1.2 <+: y ∧
      g.1.2.countP (Label.isTauOf X.p₁) < y.countP (Label.isTauOf X.p₁) :=
    fun g => hiter g.1.1 g.1.2 g.2
  choose yf hyf hpref hcntf using hnext
  let nxt : G → G := fun g => ⟨(g.1.1 + 1, yf g), hyf g⟩
  let g₀ : G := ⟨(0, []), X.inv_zero⟩
  let E : ℕ → List (Label P A) := fun k => (nxt^[k] g₀).1.2
  have hE : ∀ k, E (k + 1) = yf (nxt^[k] g₀) := fun k => by
    simp only [E, Function.iterate_succ_apply']; rfl
  have hinv : ∀ k, X.Inv (nxt^[k] g₀).1.1 (E k) := fun k => (nxt^[k] g₀).2
  have hmono : ∀ k, E k <+: E (k + 1) := fun k => by rw [hE]; exact hpref _
  have hcount : ∀ k, k ≤ (E k).countP (Label.isTauOf X.p₁) := by
    intro k; induction k with
    | zero => omega
    | succ k ih =>
      have := hcntf (nxt^[k] g₀)
      have e : E k = (nxt^[k] g₀).1.2 := rfl
      rw [e] at ih; rw [hE]; omega
  exact false_of_starving_chain hwf E hmono
    (fun k => (hcount k).trans List.countP_le_length) (fun k => (hinv k).std.valid) X.p₁
    (fun k => by rw [(hinv k).resp1, (hinv 0).resp1]) (fun N => ⟨N, hcount N⟩)

/-- **Theorem 4.3** of [CPT15]: a wait-free linearizable implementation of an exact order type
(from read, write and cas, with at least three processes) cannot be help-free. -/
theorem theorem_4_3_helpFree (I : Impl A (fun i => casObject (V i) (v₀ i)) P L)
    (hA : ExactOrder A) (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) (hwf : I.WaitFree) : ¬ HelpFree I :=
  fun h => theorem_4_3 I hA p₁ p₂ p₃ h12 h13 h23 hall hwf h.weaklyHelpFree

/-- In particular (Section 4.5), there is no wait-free help-free linearizable FIFO queue from
read/write/cas registers for three or more processes. -/
theorem queue_not_waitFree_helpFree (I : Impl queueSpec (fun i => casObject (V i) (v₀ i)) P L)
    (p₁ p₂ p₃ : P) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hall : ∀ p o, I.allowed p o) : ¬ (I.WaitFree ∧ HelpFree I) :=
  fun ⟨hwf, hhf⟩ => theorem_4_3_helpFree I queue_exactOrder p₁ p₂ p₃ h12 h13 h23 hall hwf hhf

end CAS

end Podc.HelpFreeWaitFree
