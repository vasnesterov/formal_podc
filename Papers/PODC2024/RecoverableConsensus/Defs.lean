import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Recoverable

/-!
# Determining Recoverable Consensus Numbers — definitions

Sean Ovens, *Determining Recoverable Consensus Numbers*, PODC 2024 (arXiv 2405.04775).

Type-level conditions (Section 2 of the paper) and consensus numbers:

* `apply S u o σ` — the value of an object of type `S` with initial value `u` after the processes
  of the schedule `σ` (a list of distinct processes) apply their operations `o p` in order;
* `IsRecording n S` — `S` is `n`-recording (Delporte-Gallet–Fatourou–Fauconnier–Ruppert);
* `IsDiscerning n S` — `S` is `n`-discerning (Ruppert);
* `Readable S`; `IsRW S` (read/write-like objects: every operation is read-only or a blind write;
  registers are `IsRW`, `isRW_register`);
* `WFSolvable S n` / `RecSolvable S n` — wait-free / recoverable wait-free binary consensus for `n`
  processes is solvable using objects of type `S` together with read/write objects;
* `ConsensusNumber S n`, `RecConsensusNumber S n`;
* the type `Tnn n n'` of Section 4.
-/

namespace Cslib.SharedMemory.Recoverable.Ovens

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- Value of an object of type `S` with initial value `u` after the processes of `σ` apply their
operations `o p` in order. -/
def apply (S : ObjSpec) {n : ℕ} (u : S.State) (o : Fin n → S.Op) (σ : List (Fin n)) : S.State :=
  σ.foldl (fun s p => (S.δ s (o p)).1) u

@[simp] lemma apply_nil (S : ObjSpec) {n : ℕ} (u : S.State) (o : Fin n → S.Op) :
    apply S u o [] = u := rfl

@[simp] lemma apply_cons (S : ObjSpec) {n : ℕ} (u : S.State) (o : Fin n → S.Op) (p : Fin n)
    (σ : List (Fin n)) : apply S u o (p :: σ) = apply S (S.δ u (o p)).1 o σ := rfl

/-- A deterministic type `S` is **`n`-recording** (Section 2; Delporte-Gallet, Fatourou,
Fauconnier, Ruppert, PODC'22): there are a value `u`, a partition of the processes `p₀,…,p_{n-1}`
into two nonempty teams (`team p`), and an operation `o p` for each process such that
* `U₀ ∩ U₁ = ∅`, where `U_x` is the set of values reached from `u` by schedules (sequences of
  distinct processes) whose first process is on team `x`, and
* if `u ∈ U_x` then team `x̄` has exactly one member. -/
def IsRecording (n : ℕ) (S : ObjSpec) : Prop :=
  ∃ (u : S.State) (team : Fin n → Bool) (o : Fin n → S.Op),
    (∃ p, team p = false) ∧ (∃ p, team p = true) ∧
    (∀ p σ q τ, (p :: σ).Nodup → (q :: τ).Nodup → team p = false → team q = true →
      apply S u o (p :: σ) ≠ apply S u o (q :: τ)) ∧
    (∀ p σ, (p :: σ).Nodup → apply S u o (p :: σ) = u → ∃! q, team q = !team p)

/-- A deterministic type `S` is **`n`-discerning** (Section 2; Ruppert, SICOMP 2000): there are a
value `u`, a partition into two nonempty teams and operations `o p` such that for every `j`,
`R_{0,j} ∩ R_{1,j} = ∅`, where `R_{x,j}` is the set of pairs (response of `p_j`, final value) over
schedules containing `p_j` whose first process is on team `x`. Stated for schedules `p :: σ`
with `p_j` at position `m` (the response of `p_j` is that of its operation applied to the value
reached by the processes before it). -/
def IsDiscerning (n : ℕ) (S : ObjSpec) : Prop :=
  ∃ (u : S.State) (team : Fin n → Bool) (o : Fin n → S.Op),
    (∃ p, team p = false) ∧ (∃ p, team p = true) ∧
    ∀ (σ τ : List (Fin n)) (j : Fin n) (m m' : ℕ) (hm : m < σ.length) (hm' : m' < τ.length),
      σ.Nodup → τ.Nodup → (hσ : σ ≠ []) → (hτ : τ ≠ []) → team (σ.head hσ) = false →
      team (τ.head hτ) = true → σ[m] = j → τ[m'] = j →
      ((S.δ (apply S u o (σ.take m)) (o j)).2, apply S u o σ) ≠
        ((S.δ (apply S u o (τ.take m')) (o j)).2, apply S u o τ)

/-- `S` is readable: some operation returns the current value (without changing it). -/
def Readable (S : ObjSpec) : Prop :=
  ∃ o : S.Op, (∀ s, (S.δ s o).1 = s) ∧ Function.Injective (fun s => (S.δ s o).2)

/-- Read/write-like objects: every operation is read-only, or a blind write whose new value and
response do not depend on the current value. -/
def IsRW (S : ObjSpec) : Prop :=
  ∀ o : S.Op, (∀ s, (S.δ s o).1 = s) ∨ (∀ s s', S.δ s o = S.δ s' o)

lemma isRW_register (V : Type) (v₀ : V) : IsRW (register V v₀) := by
  intro o
  cases o with
  | read => left; intro s; rfl
  | write v => right; intro s s'; rfl

/-- The objects of an algorithm that uses read/write objects `R j` (`j : ιR`) and objects of type
`S` (indexed by `ιS`). -/
abbrev withRW {ιR ιS : Type} (R : ιR → ObjSpec) (S : ObjSpec) : ιR ⊕ ιS → ObjSpec :=
  Sum.elim R (fun _ => S)

/-- Wait-free binary consensus among `n` processes can be solved using objects of type `S` and
read/write objects. -/
def WFSolvable (S : ObjSpec) (n : ℕ) : Prop :=
  ∃ (ιR ιS : Type) (_ : DecidableEq ιR) (_ : DecidableEq ιS) (R : ιR → ObjSpec)
    (_ : ∀ j, IsRW (R j)) (A : Alg n (withRW (ιS := ιS) R S)), WFConsensus A

/-- Recoverable wait-free binary consensus among `n` processes (individual crashes) can be solved
using objects of type `S` and read/write objects. -/
def RecSolvable (S : ObjSpec) (n : ℕ) : Prop :=
  ∃ (ιR ιS : Type) (_ : DecidableEq ιR) (_ : DecidableEq ιS) (R : ιR → ObjSpec)
    (_ : ∀ j, IsRW (R j)) (A : Alg n (withRW (ιS := ιS) R S)), RecConsensus A

/-- `S` has consensus number `n`: solvable for `n` processes, not for `m > n` processes. -/
def ConsensusNumber (S : ObjSpec) (n : ℕ) : Prop := WFSolvable S n ∧ ∀ m > n, ¬ WFSolvable S m

/-- `S` has recoverable consensus number `n`. -/
def RecConsensusNumber (S : ObjSpec) (n : ℕ) : Prop := RecSolvable S n ∧ ∀ m > n, ¬ RecSolvable S m

/-! ## The type `T_{n,n'}` (Section 4) -/

/-- Values of `T_{n,n'}`: `s`, `s⊥`, and `s_{x,i}` for `x ∈ {0,1}`, `1 ≤ i ≤ n-1`
(`sv x i` stands for `s_{x,i+1}`). There are exactly `2n` values. -/
inductive TVal (n : ℕ) where
  | s
  | bot
  | sv (x : Bool) (i : Fin (n - 1))
  deriving DecidableEq

/-- Operations of `T_{n,n'}`: `op₀`, `op₁` (`op x`) and `opR`. -/
inductive TOp where
  | op (x : Bool)
  | opR
  deriving DecidableEq

/-- Responses of `T_{n,n'}`: a bit, a value, or `⊥`. -/
inductive TResp (n : ℕ) where
  | bit (x : Bool)
  | val (u : TVal n)
  | bot
  deriving DecidableEq

/-- The transition function of `T_{n,n'}` (Section 4, Figure 3). -/
def tδ (n n' : ℕ) : TVal n → TOp → TVal n × TResp n
  | .bot, _ => (.bot, .bot)
  | .s, .op x => if h : 0 < n - 1 then (.sv x ⟨0, h⟩, .bit x) else (.bot, .bit x)
  | .sv x i, .op _ => if h : i.val + 1 < n - 1 then (.sv x ⟨i.val + 1, h⟩, .bit x)
      else (.bot, .bit x)
  | .s, .opR => (.s, .val .s)
  | .sv x i, .opR => if i.val + 1 ≤ n' then (.sv x i, .val (.sv x i)) else (.bot, .bot)

/-- The type `T_{n,n'}` of Section 4 (initial value `s`). -/
abbrev Tnn (n n' : ℕ) : ObjSpec where
  State := TVal n
  Op := TOp
  Resp := TResp n
  init := .s
  δ := tδ n n'

end Cslib.SharedMemory.Recoverable.Ovens
