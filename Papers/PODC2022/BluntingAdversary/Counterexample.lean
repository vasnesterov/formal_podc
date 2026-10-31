import Papers.PODC2022.BluntingAdversary.Model
import Cslib.Computability.Distributed.SharedMemory.OneAccess

/-!
# Counterexample to Lemmas 4.3 and 4.4 of the paper

Lemma 4.3 claims that for every adversary `𝒜` against `P(O^k)`,
`Prob[(P(O^k) ‖ 𝒜 → B) | X] ≤ Prob[P(O^a) → B]`, and Lemma 4.4 that
`Prob[(P(O^k) ‖ 𝒜 → B) | ¬X] ≤ Prob[P(O) → B]`. Both fail: the adversary can make the event `X`
(every object random step selects a randomization-free preamble iteration) depend on an earlier
program coin, so conditioning on `X` (or on `¬X`) biases that coin.

## The instance

Two processes `p = 0`, `q = 1`, one object `A` combining a register `R` (values `Option Bool`,
initially `none`) and a dummy `S` whose read returns `none`. The implementation `I` performs every
operation with a single atomic access (CSLib's `OneAccess`); it is strongly linearizable, hence
tail strongly linearizable for every preamble mapping. The preamble mapping `Pi` declares the
`S`-read to be inside its preamble until its access (effect free: it is a read).

* `p`: `c₁ := random{0,1}; R.write(c₁); c₂ := random{0,1}`;
* `q`: `S.read; y := R.read`.

`B` = "`q` read `y = some true`". With atomic objects or with `I`, `Prob[P → B] ≤ 1/2`
(`B` forces `c₁ = 1`). In `P(O²)`, the adversary `σ false` flips `c₁` first; if `c₁ = 0` it lets
`q` start its `S`-read and lets `p` flip `c₂` during the first preamble iteration (which is thus not
randomization-free), otherwise it runs `p` to completion first. Then `Pr[B ∧ X] = 1/2` and
`Pr[X] = 3/4`, so `Pr[B | X] = 2/3 > 1/2`. The adversary `σ true` spoils the iteration when
`c₁ = 1`: `Pr[B ∧ ¬X] = Pr[¬X] = 1/4`, so `Pr[B | ¬X] = 1 > 1/2`.
-/

set_option linter.unnecessarySeqFocus false

namespace Podc.BluntingAdversary.Counterexample

/-! ## Values of positional adversaries -/

section PosAdv

open MDP

open scoped Classical

variable {Q S : Type*} (M : MDP Q S)

/-- The probability of the payoff under the positional adversary `σ` (runs that do not terminate
pay `0`). -/
noncomputable def optS (σ : S → Q) (pay : S → ℝ) (s : S) : ℝ := ⨆ n, M.valS σ pay n s

/-- The value of `σ` from `s` is eventually equal to `v`. -/
def EvS (σ : S → Q) (pay : S → ℝ) (s : S) (v : ℝ) : Prop := ∃ N, ∀ n ≥ N, M.valS σ pay n s = v

/-- Eventual value after a move. -/
def MEvS (σ : S → Q) (pay : S → ℝ) : Move S → ℝ → Prop
  | .stop, _ => False
  | .det s', v => EvS M σ pay s' v
  | .rand m g, v => ∃ vs : Fin (m + 1) → ℝ, (∀ i, EvS M σ pay (g i) (vs i)) ∧
      (∑ i, vs i) / (m + 1) = v

variable {M} {σ : S → Q} {pay : S → ℝ}

lemma valS_zero (s : S) : M.valS σ pay 0 s = if M.Terminal s then pay s else 0 := by
  simp [valS]

lemma valS_succ (n : ℕ) (s : S) :
    M.valS σ pay (n + 1) s = if M.Terminal s then pay s else (M.move s (σ s)).ev (M.valS σ pay n) := by
  simp [valS]

lemma valS_of_terminal {s : S} (h : M.Terminal s) (n : ℕ) : M.valS σ pay n s = pay s := by
  cases n <;> simp [valS_zero, valS_succ, h]

lemma EvS_term {s : S} (h : M.Terminal s) : EvS M σ pay s (pay s) :=
  ⟨0, fun n _ => valS_of_terminal h n⟩

lemma EvS_term' {s F : S} (h : M.Terminal s) (he : s = F) : EvS M σ pay s (pay F) :=
  he ▸ EvS_term h

lemma EvS_step {s : S} {v : ℝ} (h : MEvS M σ pay (M.move s (σ s)) v) : EvS M σ pay s v := by
  cases hm : M.move s (σ s) with
  | stop => rw [hm] at h; exact h.elim
  | det s' =>
    rw [hm] at h
    obtain ⟨N, hN⟩ := h
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [valS_succ, hm]; simp only [not_terminal_of_det hm, ↓reduceIte, Move.ev_det]
    exact hN n (by omega)
  | rand m g =>
    rw [hm] at h
    obtain ⟨vs, hvs, rfl⟩ := h
    choose N hN using hvs
    refine ⟨Finset.univ.sup N + 1, fun n hn => ?_⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [valS_succ, hm]; simp only [not_terminal_of_rand hm, ↓reduceIte, Move.ev_rand]
    congr 1
    refine Finset.sum_congr rfl fun i _ => hN i n ?_
    have := Finset.le_sup (f := N) (Finset.mem_univ i)
    omega

@[simp] lemma mevs_det {s' : S} {v : ℝ} : MEvS M σ pay (.det s') v ↔ EvS M σ pay s' v := Iff.rfl

lemma mevs_rand2 {g : Fin 2 → S} {a b : ℝ} (h0 : EvS M σ pay (g 0) a)
    (h1 : EvS M σ pay (g 1) b) : MEvS M σ pay (.rand 1 g) ((a + b) / 2) := by
  refine ⟨![a, b], fun i => ?_, ?_⟩
  · fin_cases i
    · exact h0
    · exact h1
  · simp [Fin.sum_univ_two]; norm_num

lemma mevs_rand_const {m : ℕ} {g : Fin (m + 1) → S} {v : ℝ} (hg : ∀ i, g i = g 0)
    (h : EvS M σ pay (g 0) v) : MEvS M σ pay (.rand m g) v := by
  refine ⟨fun _ => v, fun i => by rw [hg i]; exact h, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

lemma valS_nonneg (hp : ∀ s, 0 ≤ pay s) : ∀ n s, 0 ≤ M.valS σ pay n s
  | 0, s => by rw [valS_zero]; split_ifs <;> simp [hp]
  | n + 1, s => by
    rw [valS_succ]; split_ifs
    · exact hp s
    · exact Move.ev_nonneg (valS_nonneg hp n) _

lemma valS_le_succ (hp : ∀ s, 0 ≤ pay s) : ∀ n s, M.valS σ pay n s ≤ M.valS σ pay (n + 1) s
  | 0, s => by
    by_cases h : M.Terminal s
    · simp [valS_of_terminal h]
    · rw [valS_zero]; simp only [h, ↓reduceIte]; exact valS_nonneg hp 1 s
  | n + 1, s => by
    by_cases h : M.Terminal s
    · simp [valS_of_terminal h]
    · rw [valS_succ, valS_succ (n := n + 1)]; simp only [h, ↓reduceIte]
      exact Move.ev_mono (valS_le_succ hp n) _

/-- An eventual value is the value of the adversary. -/
lemma optS_eq (hp : ∀ s, 0 ≤ pay s) {s : S} {v : ℝ} (h : EvS M σ pay s v) :
    optS M σ pay s = v := by
  obtain ⟨N, hN⟩ := h
  have hmono : Monotone fun n => M.valS σ pay n s :=
    monotone_nat_of_le_succ fun n => valS_le_succ hp n s
  have hle : ∀ n, M.valS σ pay n s ≤ v := fun n =>
    (hmono (le_max_left n N)).trans (hN _ (le_max_right n N)).le
  refine le_antisymm (ciSup_le hle) ?_
  rw [← hN N le_rfl]
  exact le_ciSup ⟨v, by rintro _ ⟨n, rfl⟩; exact hle n⟩ N

end PosAdv


/-! ## The instance -/

open Cslib.SharedMemory
open scoped Classical

/-- Operations of the object: write the register `R`, read `R`, read the dummy `S`. -/
inductive Op where
  | wr (b : Bool)
  | rdR
  | rdS
  deriving DecidableEq

/-- The object `A` (register `R` with values `Option Bool` and a dummy `S`). -/
@[reducible] def A : ObjSpec where
  State := Option Bool
  Op := Op
  Resp := Option Bool
  init := none
  δ q o := match o with
    | .wr b => (some b, none)
    | .rdR => (q, q)
    | .rdS => (q, none)

/-- The single base object (a copy of `A`). -/
abbrev Bs : Unit → ObjSpec := fun _ => A

/-- The single-access scheme: every operation is applied directly to the base object. -/
def scheme : OneAccess A Bs (Fin 2) Unit where
  memInit _ := none
  dInit _ := ()
  obj _ _ _ := ()
  prim _ _ o := o
  upd _ _ _ _ := ()
  out _ _ _ r := r

/-- Local states of the implementation. -/
abbrev OL := OALoc Unit A

/-- The implementation `I` of `A`. -/
def I : Impl A Bs (Fin 2) OL := scheme.impl none

/-- The preamble mapping: an `S`-read is inside its preamble until its (single) access. -/
def Pi (_ : Fin 2) (l : OL) : Prop := l = .pend () Op.rdS

/-- Client states. `p`: `p0` (flip `c₁`), `p1 c₁` (write), `p2 c₁` (flip `c₂`), `p3 c₁` (done);
`q`: `q0` (read `S`), `q1` (read `R`), `q2 y` (done, `y` read from `R`). -/
inductive CS where
  | p0
  | p1 (c : Bool)
  | p2 (c : Bool)
  | p3 (c : Bool)
  | q0
  | q1
  | q2 (y : Option Bool)
  deriving DecidableEq

/-- The program: `p` runs `c₁ := random{0,1}; R.write(c₁); c₂ := random{0,1}`, `q` runs
`S.read; y := R.read`. -/
def Pr : Program (Fin 2) A CS where
  init := ![.p0, .q0]
  next _ c := match c with
    | .p0 => .rnd 1 ![.p1 false, .p1 true]
    | .p1 c => .call (Op.wr c) fun _ => .p2 c
    | .p2 c => .rnd 1 fun _ => .p3 c
    | .p3 _ => .done
    | .q0 => .call Op.rdS fun _ => .q1
    | .q1 => .call Op.rdR fun r => .q2 r
    | .q2 _ => .done

/-- The outcomes: `q` read `some true` from `R`. -/
def B (cl : Fin 2 → CS) : Prop := cl 1 = .q2 (some true)

lemma upd0 {α : Type*} (a b c : α) : Function.update ![a, b] (0 : Fin 2) c = ![c, b] := by
  funext i; fin_cases i <;> rfl

lemma upd1 {α : Type*} (a b c : α) : Function.update ![a, b] (1 : Fin 2) c = ![a, c] := by
  funext i; fin_cases i <;> rfl

lemma updU {α : Type*} (m : Unit → α) (c : α) : Function.update m () c = fun _ => c := by
  funext u; cases u; simp

/-! ### The hypotheses of the paper hold for `I` and `Pi` -/

/-- Strong linearizability implies tail strong linearizability for every preamble mapping. -/
lemma tsl_of_sl {A : ObjSpec} {ι P L : Type} [DecidableEq ι] [DecidableEq P]
    {Bs : ι → ObjSpec} {I : Impl A Bs P L} (h : I.StronglyLinearizable) (Pi : P → L → Prop) :
    TailStronglyLinearizable I Pi := by
  obtain ⟨f, hf, hpre⟩ := h
  exact ⟨⟨f, hf⟩, f, fun α C hC _ => hf α ⟨C, hC⟩,
    fun α β _ C' _ hβ _ _ hp => hpre α β ⟨C', hβ⟩ hp⟩

/-- `I` is strongly linearizable (it is a single-access implementation). -/
lemma I_stronglyLinearizable : I.StronglyLinearizable := by
  refine scheme.stronglyLinearizable (Abs := fun m _ s => m () = s) ⟨rfl, ?_⟩ none
  rintro m ds s p d o - rfl -
  refine ⟨?_, ?_⟩
  · simp only [scheme, Function.update_self]
  · rfl

lemma I_tsl : TailStronglyLinearizable I Pi := tsl_of_sl I_stronglyLinearizable Pi

lemma I_act_pend (p : Fin 2) (o : Op) :
    I.act p (.pend () o) = .access () o (fun r => .done () r) := rfl

lemma I_effectFree : EffectFree I Pi := by
  rintro p l i o k rfl h
  rw [I_act_pend] at h
  simp only [Action.access.injEq] at h
  obtain ⟨-, h2, -⟩ := h
  cases i
  cases h2
  intro q; rfl

lemma I_wf : PreambleWF I Pi where
  stay p l i o k r _ h := by
    cases l with
    | idle d => cases h
    | done d r => cases h
    | pend d o' =>
      cases d
      rw [I_act_pend] at h
      simp only [Action.access.injEq] at h
      obtain ⟨-, -, h3⟩ := h
      cases i
      cases h3
      simp [Pi]
  ret p l r l' h := by
    rintro rfl
    rw [I_act_pend] at h
    cases h

/-! ## `Prob[P(O) → B] ≤ 1/2` and `Prob[P(O^a) → B] ≤ 1/2` -/

/-- The value of `c₁`, once flipped. -/
def c1o : CS → Option Bool
  | .p1 c => some c
  | .p2 c => some c
  | .p3 c => some c
  | _ => none

/-- `p`'s client states. -/
def isP : CS → Bool
  | .p0 => true
  | .p1 _ => true
  | .p2 _ => true
  | .p3 _ => true
  | _ => false

/-- `q`'s client states. -/
def isQ : CS → Bool
  | .q0 => true
  | .q1 => true
  | .q2 _ => true
  | _ => false

/-- A value that may have been read from `R`: `none` or `c₁`. -/
def okv (a : CS) (v : Option Bool) : Prop := v = none ∨ v = c1o a

/-- The potential: the probability of `B` given `p`'s client state. -/
noncomputable def pot : CS → ℝ
  | .p0 => 1 / 2
  | .p1 c => if c then 1 else 0
  | .p2 c => if c then 1 else 0
  | .p3 c => if c then 1 else 0
  | _ => 0

@[simp] lemma c1o_p0 : c1o .p0 = none := rfl
@[simp] lemma c1o_p1 (c : Bool) : c1o (.p1 c) = some c := rfl
@[simp] lemma c1o_p2 (c : Bool) : c1o (.p2 c) = some c := rfl
@[simp] lemma c1o_p3 (c : Bool) : c1o (.p3 c) = some c := rfl
@[simp] lemma c1o_q0 : c1o .q0 = none := rfl
@[simp] lemma c1o_q1 : c1o .q1 = none := rfl
@[simp] lemma c1o_q2 (y : Option Bool) : c1o (.q2 y) = none := rfl

/-- The number of `p`'s remaining coins. -/
def rem : CS → ℕ
  | .p0 => 2
  | .p1 _ => 1
  | .p2 _ => 1
  | _ => 0

lemma pot_nonneg (a : CS) : 0 ≤ pot a := by
  cases a <;> simp only [pot] <;> (try split_ifs) <;> norm_num

/-- Configurations of `P(O)`. -/
abbrev CfgI := Cfg (Fin 2) CS OL (Mem Bs)

/-- The invariant of `P(O)`. -/
def GoodI (s : CfgI) : Prop :=
  isP (s.cl 0) = true ∧ isQ (s.cl 1) = true ∧ okv (s.cl 0) (s.mem ()) ∧
  (∀ p r, s.lo p = .done () r → okv (s.cl 0) r) ∧
  (∀ p c, s.lo p = .pend () (Op.wr c) → c1o (s.cl 0) = some c) ∧
  (∀ y, s.cl 1 = .q2 y → okv (s.cl 0) y) ∧ s.coins + rem (s.cl 0) ≤ 2

lemma cfgI_eq (s : CfgI) : ∃ a b ba bb la lb v n bc, s =
    ⟨![a, b], ![ba, bb], ![la, lb], fun _ => v, n, bc⟩ := by
  refine ⟨s.cl 0, s.cl 1, s.busy 0, s.busy 1, s.lo 0, s.lo 1, s.mem (), s.coins, s.badCoin, ?_⟩
  cases s with
  | mk cl busy lo mem coins bc =>
    simp only [Cfg.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> funext i <;> fin_cases i <;> rfl

/-- Unfold one move of `P(O)`. -/
macro "smv" h:ident : tactic => `(tactic| (simp [sysMove, implSem, I, OneAccess.impl, scheme, Pr,
  upd0, upd1, updU] at $h:ident))

/-- Check the invariant after a move. -/
macro "fing" : tactic => `(tactic| (refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
  simp_all [Fin.forall_fin_two, okv, isP, isQ, OALoc.data, pot, rem]))

lemma impl_det (s s' : CfgI) (q : Fin 2) (hG : GoodI s)
    (h : sysMove Pr (implSem I Pi) s q = .det s') : GoodI s' ∧ pot (s'.cl 0) = pot (s.cl 0) := by
  obtain ⟨a, b, ba, bb, la, lb, v, n, bc, rfl⟩ := cfgI_eq s
  obtain ⟨hA, hB, hm, hd, hw, hy, hc⟩ := hG
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.forall_fin_two]
    at hA hB hm hd hw hy hc
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hw0, hw1⟩ := hw
  fin_cases q
  · cases ba
    · cases a <;> simp [isP] at hA <;> smv h <;> subst h <;> fing
    · cases la with
      | idle d => cases a <;> simp [isP] at hA <;> smv h <;> subst h <;> fing
      | pend d o => cases o <;> smv h <;> subst h <;> fing
      | done d r => cases a <;> simp [isP] at hA <;> smv h <;> subst h <;> fing
  · cases bb
    · cases b <;> simp [isQ] at hB <;> smv h <;> subst h <;> fing
    · cases lb with
      | idle d => cases b <;> simp [isQ] at hB <;> smv h <;> subst h <;> fing
      | pend d o => cases o <;> smv h <;> subst h <;> fing
      | done d r => cases b <;> simp [isQ] at hB <;> smv h <;> subst h <;> fing

lemma impl_rand (s : CfgI) (q : Fin 2) (m : ℕ) (g : Fin (m + 1) → CfgI) (hG : GoodI s)
    (h : sysMove Pr (implSem I Pi) s q = .rand m g) :
    (∀ i, GoodI (g i)) ∧ (∑ i, pot ((g i).cl 0)) / (m + 1) ≤ pot (s.cl 0) := by
  obtain ⟨a, b, ba, bb, la, lb, v, n, bc, rfl⟩ := cfgI_eq s
  obtain ⟨hA, hB, hm, hd, hw, hy, hc⟩ := hG
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.forall_fin_two]
    at hA hB hm hd hw hy hc
  obtain ⟨hd0, hd1⟩ := hd
  obtain ⟨hw0, hw1⟩ := hw
  fin_cases q
  · cases ba
    · cases a <;> simp [isP] at hA <;> smv h <;> obtain ⟨rfl, h⟩ := h <;> cases h <;>
        refine ⟨fun i => ?_, ?_⟩ <;> (try fin_cases i) <;>
        simp_all [GoodI, Fin.forall_fin_two, okv, isP, isQ, pot, rem, Fin.sum_univ_two] <;>
        (try split_ifs) <;> norm_num
    · cases la <;> (try rename_i o; cases o) <;> cases a <;> simp [isP] at hA <;> smv h
  · cases bb
    · cases b <;> simp [isQ] at hB <;> smv h
    · cases lb <;> (try rename_i o; cases o) <;> cases b <;> simp [isQ] at hB <;> smv h

lemma goodI_init : GoodI (initCfg Pr (implSem I Pi)) := by
  simp [GoodI, initCfg, Pr, implSem, I, OneAccess.impl, scheme, okv, isP, isQ, rem]

lemma reach_goodI {s s' : CfgI} (h : (sys Pr (implSem I Pi)).Reach s s') (hG : GoodI s) :
    GoodI s' := by
  induction h with
  | refl => exact hG
  | det q hm _ ih => exact ih (impl_det _ _ q hG hm).1
  | rand q m g i hm _ ih => exact ih ((impl_rand _ q m g hG hm).1 i)

/-- The program has at most two (program) random steps. -/
lemma atMostRandom : AtMostRandom Pr (implSem I Pi) 2 := fun s h => by
  have := (reach_goodI h goodI_init).2.2.2.2.2.2
  omega

lemma payB_le_pot {L M : Type} (s : Cfg (Fin 2) CS L M) (hA : isP (s.cl 0) = true)
    (hy : ∀ y, s.cl 1 = .q2 y → okv (s.cl 0) y) : payB B s ≤ pot (s.cl 0) := by
  unfold payB B
  split_ifs with hb
  · have := hy _ hb
    revert hA this
    cases s.cl 0 <;> simp [okv, isP, pot] <;> rintro rfl <;> simp
  · exact pot_nonneg _

/-- `Prob[P(O) → B] ≤ 1/2`. -/
theorem prob_impl_le : prob Pr (implSem I Pi) B ≤ 1 / 2 := by
  unfold prob
  refine MDP.opt_le_of_super (fun s x => GoodI s ∧ x = pot (s.cl 0)) ?_ ?_ ?_ ?_
    ⟨goodI_init, by simp [initCfg, Pr, pot]⟩
  · rintro s x ⟨-, rfl⟩; exact pot_nonneg _
  · rintro s x ⟨hG, rfl⟩ -; exact payB_le_pot s hG.1 hG.2.2.2.2.2.1
  · rintro s x q s' ⟨hG, rfl⟩ hm
    obtain ⟨h1, h2⟩ := impl_det s s' q hG hm
    exact ⟨_, h2.le, h1, rfl⟩
  · rintro s x q m g ⟨hG, rfl⟩ hm
    obtain ⟨h1, h2⟩ := impl_rand s q m g hG hm
    exact ⟨fun i => pot ((g i).cl 0), h2, fun i => ⟨h1 i, rfl⟩⟩

/-- Configurations of `P(O^a)`. -/
abbrev CfgA := Cfg (Fin 2) CS Unit (Option Bool)

/-- The invariant of `P(O^a)`. -/
def GoodA (s : CfgA) : Prop :=
  isP (s.cl 0) = true ∧ isQ (s.cl 1) = true ∧ okv (s.cl 0) s.mem ∧
  (∀ y, s.cl 1 = .q2 y → okv (s.cl 0) y)

lemma cfgA_eq (s : CfgA) : ∃ a b ba bb v n bc, s =
    ⟨![a, b], ![ba, bb], ![(), ()], v, n, bc⟩ := by
  refine ⟨s.cl 0, s.cl 1, s.busy 0, s.busy 1, s.mem, s.coins, s.badCoin, ?_⟩
  cases s with
  | mk cl busy lo mem coins bc =>
    simp only [Cfg.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> funext i <;> fin_cases i <;> rfl

/-- Unfold one move of `P(O^a)`. -/
macro "smva" h:ident : tactic => `(tactic| (simp [sysMove, atomSem, Pr, upd0, upd1] at $h:ident))

lemma atom_det (s s' : CfgA) (q : Fin 2) (hG : GoodA s)
    (h : sysMove Pr (atomSem A) s q = .det s') : GoodA s' ∧ pot (s'.cl 0) = pot (s.cl 0) := by
  obtain ⟨a, b, ba, bb, v, n, bc, rfl⟩ := cfgA_eq s
  obtain ⟨hA, hB, hm, hy⟩ := hG
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hA hB hm hy
  fin_cases q
  · cases ba <;> cases a <;> simp [isP] at hA <;> smva h <;> subst h <;>
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [okv, isP, isQ, pot]
  · cases bb <;> cases b <;> simp [isQ] at hB <;> smva h <;> subst h <;>
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp_all [okv, isP, isQ, pot]

lemma atom_rand (s : CfgA) (q : Fin 2) (m : ℕ) (g : Fin (m + 1) → CfgA) (hG : GoodA s)
    (h : sysMove Pr (atomSem A) s q = .rand m g) :
    (∀ i, GoodA (g i)) ∧ (∑ i, pot ((g i).cl 0)) / (m + 1) ≤ pot (s.cl 0) := by
  obtain ⟨a, b, ba, bb, v, n, bc, rfl⟩ := cfgA_eq s
  obtain ⟨hA, hB, hm, hy⟩ := hG
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at hA hB hm hy
  fin_cases q
  · cases ba <;> cases a <;> simp [isP] at hA <;> smva h <;> obtain ⟨rfl, h⟩ := h <;> cases h <;>
      refine ⟨fun i => ?_, ?_⟩ <;> (try fin_cases i) <;>
      simp_all [GoodA, okv, isP, isQ, pot, Fin.sum_univ_two] <;> (try split_ifs) <;> norm_num
  · cases bb <;> cases b <;> simp [isQ] at hB <;> smva h

/-- `Prob[P(O^a) → B] ≤ 1/2`. -/
theorem prob_atom_le : prob Pr (atomSem A) B ≤ 1 / 2 := by
  unfold prob
  refine MDP.opt_le_of_super (fun s x => GoodA s ∧ x = pot (s.cl 0)) ?_ ?_ ?_ ?_
    ⟨by simp [GoodA, initCfg, Pr, atomSem, okv, isP, isQ], by simp [initCfg, Pr, pot]⟩
  · rintro s x ⟨-, rfl⟩; exact pot_nonneg _
  · rintro s x ⟨hG, rfl⟩ -; exact payB_le_pot s hG.1 hG.2.2.2
  · rintro s x q s' ⟨hG, rfl⟩ hm
    obtain ⟨h1, h2⟩ := atom_det s s' q hG hm
    exact ⟨_, h2.le, h1, rfl⟩
  · rintro s x q m g ⟨hG, rfl⟩ hm
    obtain ⟨h1, h2⟩ := atom_rand s q m g hG hm
    exact ⟨fun i => pot ((g i).cl 0), h2, fun i => ⟨h1 i, rfl⟩⟩

/-! ## Two adversaries against `P(O²)` -/

/-- Configurations of `P(O²)`. -/
abbrev Cfg2 := Cfg (Fin 2) CS (LK OL) (Mem Bs)

/-- The game `P(O²)`. -/
noncomputable def G2 : MDP (Fin 2) Cfg2 := sys Pr (iterSem I Pi 2)

lemma G2_move (s : Cfg2) (p : Fin 2) : G2.move s p = sysMove Pr (iterSem I Pi 2) s p := rfl

/-- Initial local state of `O²`. -/
def lk0 : LK OL := ⟨.idle (), .idle (), .idle (), .tail, [], 0, false, false⟩

lemma init2 : initCfg Pr (iterSem I Pi 2) =
    (⟨![.p0, .q0], ![false, false], ![lk0, lk0], fun _ => none, 0, false⟩ : Cfg2) := by
  simp only [initCfg, Cfg.mk.injEq]
  refine ⟨rfl, ?_, ?_, rfl, trivial, trivial⟩ <;> funext i <;> fin_cases i <;> rfl

/-- The adversary `σ b`: flip `c₁` first; if `c₁ = b`, let `q` start its `S`-read and run `p`
(write, flip `c₂`) inside `q`'s first preamble iteration; otherwise run `p` to completion
first; then run `q` to completion. -/
def σ (b : Bool) (s : Cfg2) : Fin 2 :=
  if s.cl 0 = .p1 b ∧ s.cl 1 = .q0 ∧ s.busy 1 = false then 1
  else match s.cl 0 with
    | .p3 _ => 1
    | _ => 0

/-- One step of the adversary's run. -/
macro "stp" : tactic => `(tactic| (apply EvS_step; simp [G2_move, σ, sysMove, Pr, iterSem, I,
  OneAccess.impl, scheme, Pi, Cfg.inPreamble, upd0, upd1, updU, lk0, OALoc.data]))

/-- An object random step whose outcomes are all equal. -/
macro "stpc" : tactic => `(tactic| (stp; apply mevs_rand_const (fun i => by fin_cases i <;> rfl)))

/-- The last step of a run. -/
macro "fin" : tactic => `(tactic| (refine EvS_term' (fun q => ?_) rfl; fin_cases q <;>
  simp [G2_move, sysMove, Pr]))

/-- `p`'s final local state. -/
def plk (c : Bool) : LK OL :=
  ⟨.idle (), .idle (), .pend () (Op.wr c), .tail, [(.pend () (Op.wr c), false),
    (.pend () (Op.wr c), false)], 1, false, false⟩

/-- `q`'s final local state (`x`: the `S`-read chose a spoiled iteration). -/
def qlk (x : Bool) : LK OL :=
  ⟨.idle (), .idle (), .pend () Op.rdR, .tail, [(.pend () Op.rdR, false), (.pend () Op.rdR, false)],
    2, false, x⟩

/-- The final configurations: `c₁ = c`, `x` = the `S`-read chose a spoiled iteration. -/
def leaf (c x : Bool) : Cfg2 :=
  ⟨![.p3 c, .q2 (some c)], ![false, false], ![plk c, qlk x], fun _ => some c, 2, false⟩

/-- The run of `σ false`: `c₁ = 0` is spoiled, `c₁ = 1` is clean. -/
lemma run_false (pay : Cfg2 → ℝ) : EvS G2 (σ false) pay (initCfg Pr (iterSem I Pi 2))
    (((pay (leaf false true) + pay (leaf false false)) / 2 + pay (leaf true false)) / 2) := by
  rw [init2]
  stp
  apply mevs_rand2
  · stp; stp; stp; stp
    stpc
    stp; stp
    stpc
    stp; stp; stp; stp
    stp
    apply mevs_rand2
    · stp; stp; stp; stp
      stpc
      stp; stp
      fin
    · stp; stp; stp; stp
      stpc
      stp; stp
      fin
  · stp; stp; stp
    stpc
    stp; stp
    stpc
    stp; stp; stp; stp; stp
    stpc
    stp; stp; stp; stp
    stpc
    stp; stp
    fin

/-- The run of `σ true`: `c₁ = 0` is clean, `c₁ = 1` is spoiled. -/
lemma run_true (pay : Cfg2 → ℝ) : EvS G2 (σ true) pay (initCfg Pr (iterSem I Pi 2))
    ((pay (leaf false false) + (pay (leaf true true) + pay (leaf true false)) / 2) / 2) := by
  rw [init2]
  stp
  apply mevs_rand2
  · stp; stp; stp
    stpc
    stp; stp
    stpc
    stp; stp; stp; stp; stp
    stpc
    stp; stp; stp; stp
    stpc
    stp; stp
    fin
  · stp; stp; stp; stp
    stpc
    stp; stp
    stpc
    stp; stp; stp; stp
    stp
    apply mevs_rand2
    · stp; stp; stp; stp
      stpc
      stp; stp
      fin
    · stp; stp; stp; stp
      stpc
      stp; stp
      fin

/-! ### The conditional probabilities -/

/-- Payoff `X`: every object random step chose a randomization-free preamble iteration. -/
noncomputable def payX (s : Cfg2) : ℝ := if ∀ p, (s.lo p).xbad = false then 1 else 0

/-- Payoff `B ∧ ¬X`. -/
noncomputable def payBNX (B : (Fin 2 → CS) → Prop) (s : Cfg2) : ℝ :=
  if B s.cl ∧ ∃ p, (s.lo p).xbad = true then 1 else 0

/-- The initial configuration of `P(O²)`. -/
noncomputable abbrev init : Cfg2 := initCfg Pr (iterSem I Pi 2)

lemma val_BX :
    optS (sys Pr (iterSem I Pi 2)) (σ false) (payBX B) (initCfg Pr (iterSem I Pi 2)) = 1 / 2 := by
  change optS G2 (σ false) (payBX B) init = 1 / 2
  rw [optS_eq (fun s => by unfold payBX; split_ifs <;> norm_num) (run_false _)]
  simp [payBX, leaf, B, plk, qlk, Fin.forall_fin_two]

lemma val_X :
    optS (sys Pr (iterSem I Pi 2)) (σ false) payX (initCfg Pr (iterSem I Pi 2)) = 3 / 4 := by
  change optS G2 (σ false) payX init = 3 / 4
  rw [optS_eq (fun s => by unfold payX; split_ifs <;> norm_num) (run_false _)]
  simp [payX, leaf, plk, qlk, Fin.forall_fin_two]; norm_num

lemma val_BNX :
    optS (sys Pr (iterSem I Pi 2)) (σ true) (payBNX B) (initCfg Pr (iterSem I Pi 2)) = 1 / 4 := by
  change optS G2 (σ true) (payBNX B) init = 1 / 4
  rw [optS_eq (fun s => by unfold payBNX; split_ifs <;> norm_num) (run_true _)]
  simp [payBNX, leaf, B, plk, qlk, Fin.exists_fin_two]; norm_num

lemma val_NX :
    optS (sys Pr (iterSem I Pi 2)) (σ true) payNX (initCfg Pr (iterSem I Pi 2)) = 1 / 4 := by
  change optS G2 (σ true) payNX init = 1 / 4
  rw [optS_eq (fun s => by unfold payNX; split_ifs <;> norm_num) (run_true _)]
  simp [payNX, leaf, plk, qlk, Fin.exists_fin_two]; norm_num

/-! ## Lemmas 4.3 and 4.4 are false -/

/-- Under `σ false`: `Pr[B ∧ X] = 1/2`, `Pr[X] = 3/4`, hence `Pr[B | X] = 2/3`, while
`Prob[P(O^a) → B] ≤ 1/2`. -/
theorem lemma_4_3_numbers :
    optS (sys Pr (iterSem I Pi 2)) (σ false) (payBX B) (initCfg Pr (iterSem I Pi 2)) = 1 / 2 ∧
    optS (sys Pr (iterSem I Pi 2)) (σ false) payX (initCfg Pr (iterSem I Pi 2)) = 3 / 4 ∧
    prob Pr (atomSem A) B ≤ 1 / 2 :=
  ⟨val_BX, val_X, prob_atom_le⟩

/-- Under `σ true`: `Pr[B ∧ ¬X] = Pr[¬X] = 1/4`, hence `Pr[B | ¬X] = 1`, while
`Prob[P(O) → B] ≤ 1/2`. -/
theorem lemma_4_4_numbers :
    optS (sys Pr (iterSem I Pi 2)) (σ true) (payBNX B) (initCfg Pr (iterSem I Pi 2)) = 1 / 4 ∧
    optS (sys Pr (iterSem I Pi 2)) (σ true) payNX (initCfg Pr (iterSem I Pi 2)) = 1 / 4 ∧
    prob Pr (implSem I Pi) B ≤ 1 / 2 :=
  ⟨val_BNX, val_NX, prob_impl_le⟩

/-- **Lemma 4.3 of the paper is false.** For a program with two processes and at most two
random steps, using one object whose (single-access, hence strongly linearizable) implementation
`I` has effect-free preambles w.r.t. the well-formed preamble mapping `Pi`, there is an adversary
`σ` against `P(O²)` with `Prob[X] > 0` and
`Prob[(P(O²) ‖ σ → B) | X] = 2/3 > 1/2 ≥ Prob[P(O^a) → B]`. -/
theorem lemma_4_3_false :
    TailStronglyLinearizable I Pi ∧ EffectFree I Pi ∧ PreambleWF I Pi ∧
    AtMostRandom Pr (implSem I Pi) 2 ∧
    ∃ σ : Cfg (Fin 2) CS (LK OL) (Mem Bs) → Fin 2,
      0 < optS (sys Pr (iterSem I Pi 2)) σ payX (initCfg Pr (iterSem I Pi 2)) ∧
      optS (sys Pr (iterSem I Pi 2)) σ (payBX B) (initCfg Pr (iterSem I Pi 2)) /
        optS (sys Pr (iterSem I Pi 2)) σ payX (initCfg Pr (iterSem I Pi 2)) >
      prob Pr (atomSem A) B := by
  refine ⟨I_tsl, I_effectFree, I_wf, atMostRandom, σ false, ?_, ?_⟩
  · rw [val_X]; norm_num
  · rw [val_BX, val_X]
    linarith [prob_atom_le]

/-- **Lemma 4.4 of the paper is false.** In the same setting, there is an adversary `σ` against
`P(O²)` with `Prob[¬X] > 0` and `Prob[(P(O²) ‖ σ → B) | ¬X] = 1 > 1/2 ≥ Prob[P(O) → B]`. -/
theorem lemma_4_4_false :
    TailStronglyLinearizable I Pi ∧ EffectFree I Pi ∧ PreambleWF I Pi ∧
    AtMostRandom Pr (implSem I Pi) 2 ∧
    ∃ σ : Cfg (Fin 2) CS (LK OL) (Mem Bs) → Fin 2,
      0 < optS (sys Pr (iterSem I Pi 2)) σ payNX (initCfg Pr (iterSem I Pi 2)) ∧
      optS (sys Pr (iterSem I Pi 2)) σ (payBNX B) (initCfg Pr (iterSem I Pi 2)) /
        optS (sys Pr (iterSem I Pi 2)) σ payNX (initCfg Pr (iterSem I Pi 2)) >
      prob Pr (implSem I Pi) B := by
  refine ⟨I_tsl, I_effectFree, I_wf, atMostRandom, σ true, ?_, ?_⟩
  · rw [val_NX]; norm_num
  · rw [val_BNX, val_NX]
    linarith [prob_impl_le]

end Podc.BluntingAdversary.Counterexample
