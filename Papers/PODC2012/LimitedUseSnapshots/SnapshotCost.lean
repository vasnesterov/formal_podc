import Papers.PODC2012.LimitedUseSnapshots.SnapshotDefs
import Mathlib.Data.Nat.Log

/-!
# Lemma 4.3 of Aspnes–Attiya–Censor-Hillel–Ellen: step complexity of Algorithm 3

Step complexity is counted as a *weighted* number of base-object accesses: an access to a base
object costs what one operation on its implementation costs (`Costs`: `MaxUpdate`, `MaxScan`,
`WriteMax`, `ReadMax`; register accesses cost `1`). With the max arrays and the max register as
atomic base objects, `Costs` with all weights `1` counts the accesses.

* `lemma_4_3_scan`: a `Scan` costs at most `ReadMax + 1`;
* `lemma_4_3_update`: an `Update` of process `p` costs at most
  `depth(leaf_p) · (MaxUpdate + MaxScan + 3) + WriteMax + 1`: one iteration per ancestor of the
  leaf, each with one `MaxUpdate`, one `MaxScan` and three register accesses, plus the leaf write
  and the final `WriteMax`;
* `depth_balanced_le`: for the balanced tree `balanced l` on `n` leaves every leaf has depth at
  most `⌈log₂ n⌉` (`Nat.clog 2 n`);
* `lemma_4_3_asymptotic`: with the costs of Section 3 (`MaxUpdate`, `MaxScan` = `O(log² b)`,
  `WriteMax`, `ReadMax` = `O(log b)`) this gives the paper's `O(log b)` for `Scan` and
  `O(log² b · log n)` for `Update`. The erratum of the paper raises the cost of `MaxUpdate₁` of
  the 2-component max array from `O(log b)` to `O(log k log h) = O(log² b)`, the same order as
  `MaxScan`, so the bound `O(log² b log n)` survives.

The general cost lemma `Impl.tauCost_add_le` (a potential on local states that drops by at least
the cost of every access bounds the total cost of a process's accesses) does not depend on
Algorithm 3. -- CSLib candidate
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

/-! ### Weighted step complexity from a potential (generic) -/

section Generic

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  (I : Impl A B P L) (cost : (i : ι) → (B i).Op → ℕ)

/-- The cost of an action (`0` for a response). -/
def accCost : Action A B L → ℕ
  | .access i o _ => cost i o
  | .ret _ _ => 0

/-- The total cost of the base-object accesses of `p` along the labels `γ` from `C`. -/
noncomputable def tauCost (p : P) : Config A B P L → List (Label P A) → ℕ
  | _, [] => 0
  | C, ℓ :: γ => (if ℓ.isTauOf p then accCost cost (I.act p (C.loc p)) else 0) +
      match I.step C ℓ with
      | some C' => tauCost p C' γ
      | none => 0

/-- **Weighted step complexity from a potential.** If the potential `μ` of the local state of a
process drops by at least the cost of each of its accesses, then along a fragment in which `p`
is pending and does not return, the total cost of `p`'s accesses is at most the drop of `μ`.
-- CSLib candidate -/
theorem tauCost_add_le (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) + cost i o ≤ μ p l) (p : P) :
    ∀ (γ : List (Label P A)) (C C' : Config A B P L), I.runFrom C γ = some C' →
      C.pend p ≠ none → (∀ r, .ret p r ∉ γ) →
      tauCost I cost p C γ + μ p (C'.loc p) ≤ μ p (C.loc p)
  | [], C, C', h, _, _ => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; simp [tauCost]
  | ℓ :: γ, C, C', h, hp, hr => by
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hr' : ∀ r, .ret p r ∉ γ := fun r hm => hr r (List.mem_cons_of_mem _ hm)
      have hp₁ : C₁.pend p ≠ none := by
        by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv hs).1 hp
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
          | tau q => rw [(Impl.step_tau hs).2.1]; exact hp
        · rw [(Impl.step_other hs hq).2]; exact hp
      have ih := tauCost_add_le μ hμ p γ C₁ C' h hp₁ hr'
      simp only [tauCost, hs]
      by_cases ht : ℓ = .tau p
      · subst ht
        obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
        have h1 := hμ p _ i o k hact ((B i).δ (C.mem i) o).2
        rw [hloc, Function.update_self] at ih
        have ht : (Label.tau p : Label P A).isTauOf p = true := Label.isTauOf_eq_true_iff.2 rfl
        simp only [ht, ite_true, hact, accCost]
        omega
      · have hf : ℓ.isTauOf p = false := by
          cases h' : ℓ.isTauOf p
          · rfl
          · exact absurd (Label.isTauOf_eq_true_iff.1 h') ht
        have hq : ℓ.proc ≠ p := by
          intro hq
          cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact (Impl.step_inv hs).1 |> hp |>.elim
          | ret q r =>
            simp only [Label.proc] at hq; subst hq; exact absurd List.mem_cons_self (hr r)
          | tau q => simp only [Label.proc] at hq; exact ht (hq ▸ rfl)
        rw [(Impl.step_other hs hq).1] at ih
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        omega

/-- The cost of the accesses of an operation: after `p` invokes `o` (configuration `C₁`), in
any continuation `γ` in which `p` does not return, `p`'s accesses cost at most
`μ p (C₁.loc p)`. -/
theorem tauCost_le_of_inv (μ : P → L → ℕ)
    (hμ : ∀ p l i o k, I.act p l = .access i o k → ∀ x, μ p (k x) + cost i o ≤ μ p l)
    {α γ : List (Label P A)} {p : P} {o : A.Op} {C₁ C' : Config A B P L}
    (h₁ : I.run (α ++ [.inv p o]) = some C₁) (h : I.runFrom C₁ γ = some C')
    (hret : ∀ r, .ret p r ∉ γ) :
    tauCost I cost p C₁ γ ≤ μ p (C₁.loc p) := by
  have hp : C₁.pend p ≠ none := by
    rw [I.run_concat] at h₁
    cases hα : I.run α with
    | none => simp [hα] at h₁
    | some C₀ =>
      simp only [hα, Option.bind_some] at h₁
      rw [(Impl.step_inv h₁).2.2.1]; simp
  have := tauCost_add_le I cost μ hμ p γ C₁ C' h hp hret
  omega

end Generic

/-! ### Algorithm 3 -/

/-- Costs of the operations on the base objects of Algorithm 3 (registers cost `1`). -/
structure Costs where
  /-- `MaxUpdate₀` / `MaxUpdate₁` on a max array. -/
  upd : ℕ
  /-- `MaxScan` on a max array. -/
  scan : ℕ
  /-- `WriteMax` on the root max register. -/
  wmax : ℕ
  /-- `ReadMax` on the root max register. -/
  rmax : ℕ

variable {P V : Type} [DecidableEq P] (T : BTree P) (v₀ : P → V) (K : Costs)

/-- The cost of a primitive operation of Algorithm 3. -/
def opCost : (o : Obj) → (objSpec P V v₀ o).Op → ℕ
  | .ma _, .scan => K.scan
  | .ma _, _ => K.upd
  | .mr, .writeMax _ => K.wmax
  | .mr, .readMax => K.rmax
  | .view _ _, _ => 1

/-- The cost of one iteration of the loop of `Update` (Lines 7–16). -/
def Costs.iter : ℕ := K.upd + K.scan + 3

/-- The remaining cost of an operation of process `i` in local state `l`. -/
def μ (i : P) (l : Loc P V) : ℕ :=
  match l.pc with
  | .idle => 0
  | .lw _ => 1 + (T.path i).length * K.iter + K.wmax
  | .up a _ => a.length * K.iter + K.wmax
  | .sc q => K.scan + 3 + q.length * K.iter + K.wmax
  | .rl q _ _ => 3 + q.length * K.iter + K.wmax
  | .rr q _ _ _ => 2 + q.length * K.iter + K.wmax
  | .wv q _ _ => 1 + q.length * K.iter + K.wmax
  | .wm _ => K.wmax
  | .ackU => 0
  | .s0 => K.rmax + 1
  | .s1 _ => 1
  | .retS _ => 0

lemma μ_cont (i : P) (n : ℕ) (q : List Bool) (k : ℕ) :
    μ T K i (⟨n, cont q k⟩ : Loc P V) = q.length * K.iter + K.wmax := by
  unfold cont; split_ifs with h
  · subst h; simp [μ]
  · simp [μ]

lemma μ_drop (i : P) (l : Loc P V) {o : Obj} {op : (objSpec P V v₀ o).Op}
    {k : (objSpec P V v₀ o).Resp → Loc P V} (h : act T v₀ i l = .access o op k) (x) :
    μ T K i (k x) + opCost v₀ K o op ≤ μ T K i l := by
  rcases l with ⟨n, pc⟩
  cases pc with
  | idle | ackU | retS _ => simp only [act] at h; cases h
  | lw v =>
    simp only [act] at h; cases h
    rw [μ_cont]; simp [μ, opCost]; omega
  | up a ptr =>
    cases a with
    | nil => simp only [act] at h; cases h; simp [μ, opCost]
    | cons b q =>
      simp only [act] at h; cases h
      cases b <;> simp [μ, opCost, Costs.iter] <;> (rw [Nat.add_mul, one_mul]; omega)
  | sc q => simp only [act] at h; cases h; simp [μ, opCost]; omega
  | rl q x y => simp only [act] at h; cases h; simp [μ, opCost]; omega
  | rr q x y lv => simp only [act] at h; cases h; simp [μ, opCost]; omega
  | wv q k' val =>
    simp only [act] at h; cases h
    rw [μ_cont]; simp [μ, opCost]; omega
  | wm d => simp only [act] at h; cases h; simp [μ, opCost]
  | s0 => simp only [act] at h; cases h; simp [μ, opCost]; omega
  | s1 c => simp only [act] at h; cases h; simp [μ, opCost]

lemma loc_after_inv {α : List (Label P (swSnap P V v₀))} {p : P} {o : SOp P V}
    {C₁ : Config (swSnap P V v₀) (objSpec P V v₀) P (Loc P V)}
    (h₁ : (alg3 T v₀).run (α ++ [.inv p o]) = some C₁) :
    ∃ n, C₁.loc p = ⟨n, match o with | .update _ v => .lw v | .scan => .s0⟩ := by
  rw [Impl.run_concat] at h₁
  cases hα : (alg3 T v₀).run α with
  | none => simp [hα] at h₁
  | some C₀ =>
    simp only [hα, Option.bind_some] at h₁
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h₁
    refine ⟨(C₀.loc p).cnt, ?_⟩
    rw [hloc, Function.update_self]; cases o <;> rfl

/-- **Lemma 4.3** of [Aspnes–Attiya–Censor-Hillel–Ellen], `Update`: after process `p` invokes
`Update(v)`, its base-object accesses (until it returns) cost at most
`depth(leaf_p) · (MaxUpdate + MaxScan + 3) + WriteMax + 1`. -/
theorem lemma_4_3_update {α γ : List (Label P (swSnap P V v₀))} {p : P} {v : V}
    {C₁ C' : Config (swSnap P V v₀) (objSpec P V v₀) P (Loc P V)}
    (h₁ : (alg3 T v₀).run (α ++ [.inv p (.update p v)]) = some C₁)
    (h : (alg3 T v₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg3 T v₀) (opCost v₀ K) p C₁ γ ≤
      (T.path p).length * (K.upd + K.scan + 3) + K.wmax + 1 := by
  have hb := tauCost_le_of_inv (alg3 T v₀) (opCost v₀ K) (μ T K)
    (fun i l _ _ _ h x => μ_drop T v₀ K i l h x) h₁ h hret
  obtain ⟨n, hn⟩ := loc_after_inv T v₀ h₁
  rw [hn] at hb
  simp only [μ, Costs.iter] at hb
  omega

/-- **Lemma 4.3** of [Aspnes–Attiya–Censor-Hillel–Ellen], `Scan`: one `ReadMax` and one register
read. -/
theorem lemma_4_3_scan {α γ : List (Label P (swSnap P V v₀))} {p : P}
    {C₁ C' : Config (swSnap P V v₀) (objSpec P V v₀) P (Loc P V)}
    (h₁ : (alg3 T v₀).run (α ++ [.inv p .scan]) = some C₁)
    (h : (alg3 T v₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg3 T v₀) (opCost v₀ K) p C₁ γ ≤ K.rmax + 1 := by
  have hb := tauCost_le_of_inv (alg3 T v₀) (opCost v₀ K) (μ T K)
    (fun i l _ _ _ h x => μ_drop T v₀ K i l h x) h₁ h hret
  obtain ⟨n, hn⟩ := loc_after_inv T v₀ h₁
  rw [hn] at hb
  simpa only [μ] using hb

/-! ### Depth of the tree -/

omit [DecidableEq P] in
lemma BTree.depth_node_left (l r : BTree P) : l.depth + 1 ≤ (BTree.node l r).depth := by
  simp [BTree.depth]

lemma BTree.path_length_le_depth : ∀ (t : BTree P) (j : P), (t.path j).length ≤ t.depth
  | .leaf _, _ => by simp [BTree.path, BTree.depth]
  | .node l r, j => by
    have hl := BTree.path_length_le_depth l j
    have hr := BTree.path_length_le_depth r j
    simp only [BTree.path, BTree.depth]
    split_ifs <;> simp <;> omega

/-- The balanced tree on the leaves `l` (`d` is only used for the empty list): the first
`⌈|l|/2⌉` leaves go left, the others right. -/
def balanced (d : P) (l : List P) : BTree P :=
  if l.length ≤ 1 then .leaf (l.headD d)
  else .node (balanced d (l.take ((l.length + 1) / 2))) (balanced d (l.drop ((l.length + 1) / 2)))
termination_by l.length
decreasing_by all_goals simp; omega

omit [DecidableEq P] in
lemma leaves_balanced (d : P) (l : List P) (hl : l ≠ []) : (balanced d l).leaves = l := by
  rw [balanced]
  split_ifs with h
  · match l, hl, h with
    | [a], _, _ => rfl
  · have h1 : l.take ((l.length + 1) / 2) ≠ [] := by
      intro he; have := congrArg List.length he
      rw [List.length_take] at this; simp at this
      rcases this with h' | h'; omega; exact hl h'
    have h2 : l.drop ((l.length + 1) / 2) ≠ [] := by
      intro he; have := congrArg List.length he; rw [List.length_drop] at this; simp at this; omega
    simp only [BTree.leaves, leaves_balanced d _ h1, leaves_balanced d _ h2, List.take_append_drop]
termination_by l.length
decreasing_by all_goals simp; omega

omit [DecidableEq P] in
/-- The balanced tree on `n` leaves has depth at most `⌈log₂ n⌉`. -/
theorem depth_balanced_le (d : P) (l : List P) : (balanced d l).depth ≤ Nat.clog 2 l.length := by
  rw [balanced]
  split_ifs with h
  · simp [BTree.depth]
  · have hn : 2 ≤ l.length := by omega
    have h1 := depth_balanced_le d (l.take ((l.length + 1) / 2))
    have h2 := depth_balanced_le d (l.drop ((l.length + 1) / 2))
    rw [List.length_take, min_eq_left (by omega)] at h1
    rw [List.length_drop] at h2
    have h3 := Nat.clog_mono_right 2 (show l.length - (l.length + 1) / 2 ≤ (l.length + 1) / 2 by
      omega)
    rw [Nat.clog_of_two_le Nat.one_lt_two hn]
    have e : (l.length + 2 - 1) / 2 = (l.length + 1) / 2 := by omega
    rw [e]
    simp only [BTree.depth]
    omega
termination_by l.length
decreasing_by all_goals simp; omega

omit [DecidableEq P] in
/-- The balanced tree on a duplicate-free enumeration of the processes is well formed. -/
lemma balanced_wf (d : P) (l : List P) (hnd : l.Nodup) (hall : ∀ p, p ∈ l) :
    (balanced d l).WF := by
  have hl : l ≠ [] := fun h => by simpa [h] using hall d
  exact ⟨by rw [leaves_balanced d l hl]; exact hnd, fun p => by
    rw [leaves_balanced d l hl]; exact hall p⟩

/-- **Lemma 4.3** for the paper's balanced tree on `n` processes: an `Update` costs at most
`⌈log₂ n⌉ · (MaxUpdate + MaxScan + 3) + WriteMax + 1`. -/
theorem lemma_4_3_update_balanced (d : P) (l : List P) {α γ : List (Label P (swSnap P V v₀))}
    {p : P} {v : V} {C₁ C' : Config (swSnap P V v₀) (objSpec P V v₀) P (Loc P V)}
    (h₁ : (alg3 (balanced d l) v₀).run (α ++ [.inv p (.update p v)]) = some C₁)
    (h : (alg3 (balanced d l) v₀).runFrom C₁ γ = some C') (hret : ∀ r, .ret p r ∉ γ) :
    tauCost (alg3 (balanced d l) v₀) (opCost v₀ K) p C₁ γ ≤
      Nat.clog 2 l.length * (K.upd + K.scan + 3) + K.wmax + 1 := by
  have h := lemma_4_3_update (balanced d l) v₀ K h₁ h hret
  have hd := (BTree.path_length_le_depth (balanced d l) p).trans (depth_balanced_le d l)
  have := Nat.mul_le_mul_right (K.upd + K.scan + 3) hd
  omega

/-- **Lemma 4.3**, asymptotic form: if the max-array operations cost `O(log² b)` and the
max-register operations `O(log b)` (Section 3 and its erratum), with constant `c`, then an
`Update` on the balanced tree costs `O(log² b · log n)` and a `Scan` costs `O(log b)`. -/
theorem lemma_4_3_asymptotic (c b n : ℕ) (hupd : K.upd ≤ c * Nat.log 2 b ^ 2)
    (hscan : K.scan ≤ c * Nat.log 2 b ^ 2) (hw : K.wmax ≤ c * Nat.log 2 b)
    (hr : K.rmax ≤ c * Nat.log 2 b) :
    Nat.clog 2 n * (K.upd + K.scan + 3) + K.wmax + 1 ≤
        Nat.clog 2 n * (2 * c * Nat.log 2 b ^ 2 + 3) + c * Nat.log 2 b + 1 ∧
      K.rmax + 1 ≤ c * Nat.log 2 b + 1 := by
  refine ⟨?_, by omega⟩
  have : K.upd + K.scan + 3 ≤ 2 * c * Nat.log 2 b ^ 2 + 3 := by
    have := Nat.add_le_add hupd hscan
    have e : 2 * c * Nat.log 2 b ^ 2 = c * Nat.log 2 b ^ 2 + c * Nat.log 2 b ^ 2 := by
      rw [Nat.mul_assoc, Nat.two_mul]
    omega
  have := Nat.mul_le_mul_left (Nat.clog 2 n) this
  omega

end Podc.LimitedUseSnapshots.Snapshot
