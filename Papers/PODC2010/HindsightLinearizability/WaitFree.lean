import Papers.PODC2010.HindsightLinearizability.Invariants
import Cslib.Computability.Distributed.SharedMemory.Potential

/-!
# Theorem 6.4: wait-freedom of `contains`

**Theorem 6.4** of the paper: the `contains` operation of the optimistic set algorithm is
wait-free, i.e. every invocation of `contains` returns after finitely many steps of its own
thread, whatever the other threads do. We state it over infinite executions
(`Cslib.SharedMemory.Impl.InfExec`): a thread whose `contains k` stays pending forever takes only
finitely many steps (`theorem_6_4`).

As in the paper, the proof uses only `ϕ<` (keys strictly increase along links, here via the
local invariant `LocInv`: at `test p c`, `p.k < c.k`), `δk` (keys of allocated nodes are
immutable, `MemEffect.key_eq`) and the code of `locate`: the key of the node `p` held by the
traversal strictly increases and stays below `k`. Formally, we use the lexicographic potential
`containsPot` (a phase counter for the steps through the head node `H = 1`, whose key is `-∞`,
followed by the distance `k - p.k`), which never increases at the steps of other threads and
strictly decreases at every step of the thread itself.
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory

/-- The integer value of a finite key (`0` for `±∞`). -/
def keyZ : Key → ℤ
  | some (some z) => z
  | _ => 0

@[simp] lemma keyZ_fin (z : ℤ) : keyZ (fin z) = z := rfl

/-- The potential of a thread executing `contains k` in local state `l` with memory `m`:
`(3, 0)` at `start`, `(2, 0)` / `(1, 0)` at `cross H` / `test H c`, and
`(0, 2 (k - p.k) + 1)` / `(0, 2 (k - p.k))` at `cross p` / `test p c` for `p ≠ H`. -/
def containsPot (m : Mem) (k : ℤ) : Loc → ℕ ×ₗ ℕ
  | .start _ => toLex (3, 0)
  | .cross _ p => if p = 1 then toLex (2, 0) else toLex (0, 2 * (k - keyZ (m.key p)).toNat + 1)
  | .test _ p _ => if p = 1 then toLex (1, 0) else toLex (0, 2 * (k - keyZ (m.key p)).toNat)
  | _ => toLex (0, 0)

/-- The potential depends only on the keys of allocated nodes. -/
lemma containsPot_congr {m m' : Mem} {o : SetOp} {l : Loc} (hl : LocInv m o l) (k : ℤ)
    (hk : ∀ u < m.cnt, m'.key u = m.key u) : containsPot m' k l = containsPot m k l := by
  cases l with
  | cross o' p => simp only [containsPot, hk p hl.2.1]
  | test o' p c => simp only [containsPot, hk p hl.2.1]
  | _ => rfl

/-- Every step of a thread executing `contains k` strictly decreases its potential. -/
lemma containsPot_lt {m : Mem} (hm : MemInv m) {k : ℤ} {l : Loc}
    (hl : LocInv m (.contains k) l) {op : HOp} {κ : HResp → Loc}
    (hact : act l = .access () op κ) :
    containsPot (heapδ m op).1 k (κ (heapδ m op).2) < containsPot m k l := by
  cases l with
  | idle => exact hl.elim
  | err => exact hl.elim
  | done b => simp [act] at hact
  | sec o p c => exact absurd rfl (hl.2.1 k)
  | start o =>
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    simp [heapδ, hm.H_eq, containsPot, Prod.Lex.toLex_lt_toLex]
  | cross o p =>
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hp, hpk⟩ := hl
    obtain ⟨v, -, hv, -⟩ := hm.next_lt p hp (hm.ne_zero_of_key_lt hpk)
    simp only [heapδ, hv, containsPot]
    split_ifs <;> simp [Prod.Lex.toLex_lt_toLex]
  | test o p c =>
    simp only [act] at hact
    obtain ⟨rfl, rfl⟩ := hact
    obtain ⟨rfl, hp, hc, hpk, hpc⟩ := hl
    simp only [SetOp.key] at hpk
    simp only [heapδ, afterKey, SetOp.key]
    have hc1 : c ≠ 1 := by
      rintro rfl; rw [hm.keyH] at hpc; exact absurd hpc (not_lt.2 bot_le)
    by_cases hck : m.key c < fin k
    · simp only [hck, ite_true]
      obtain ⟨z', hz'⟩ := hm.key_fin c hc (hm.ne_zero_of_key_lt hck) hc1
      by_cases hp1 : p = 1
      · simp [containsPot, hp1, hc1, Prod.Lex.toLex_lt_toLex]
      · obtain ⟨z, hz⟩ := hm.key_fin p hp (hm.ne_zero_of_key_lt hpk) hp1
        rw [hz, hz', fin_lt_fin] at hpc
        rw [hz', fin_lt_fin] at hck
        simp only [containsPot, hc1, hp1, ite_false, hz, hz', keyZ_fin, Prod.Lex.toLex_lt_toLex,
          lt_self_iff_false, true_and, false_or]
        omega
    · simp only [hck, ite_false]
      by_cases hp1 : p = 1
      · simp [containsPot, hp1, Prod.Lex.toLex_lt_toLex]
      · obtain ⟨z, hz⟩ := hm.key_fin p hp (hm.ne_zero_of_key_lt hpk) hp1
        rw [hz, fin_lt_fin] at hpk
        simp only [containsPot, hp1, ite_false, hz, keyZ_fin, Prod.Lex.toLex_lt_toLex,
          lt_self_iff_false, true_and, false_or]
        omega

variable {P : Type} [DecidableEq P]

/-- The invariant holds along every infinite execution. -/
lemma inv_infExec (e : (impl P).InfExec) (t : ℕ) : Inv (e.cfg t) := by
  induction t with
  | zero => rw [e.cfg_zero]; exact inv_init
  | succ t ih => exact inv_step ih (e.step_eq t)

/-- **Theorem 6.4 (wait-freedom of contains).** In every infinite execution, a thread whose
`contains k` operation stays pending forever takes only finitely many steps: every invocation of
`contains` returns after finitely many steps of its own thread, whatever the other threads do. -/
theorem theorem_6_4 (e : (impl P).InfExec) (q : P) (n : ℕ) (k : ℤ)
    (h : ∀ m ≥ n, (e.cfg m).pend q = some (.contains k)) :
    ∃ N, ∀ m ≥ N, e.lbl m ≠ .tau q := by
  let f : ℕ → ℕ ×ₗ ℕ := fun t => containsPot ((e.cfg t).mem ()) k ((e.cfg t).loc q)
  have hstep : ∀ t ≥ n, f (t + 1) ≤ f t ∧ (e.lbl t = .tau q → f (t + 1) < f t) := by
    intro t ht
    have hI := inv_infExec e t
    have hs := e.step_eq t
    have hl := hI.2 q |>.2 _ (h t ht)
    have hp : (e.cfg t).pend q ≠ none := by simp [h t ht]
    have hp' : (e.cfg (t + 1)).pend q ≠ none := by simp [h (t + 1) (by omega)]
    rcases (impl P).step_tau_or_other hs hp hp' with hτ | ⟨-, hloc⟩
    · rw [hτ] at hs
      obtain ⟨-, -, op, κ, hact, hmem, hloc⟩ := step_tau' hs
      have : f (t + 1) < f t := by
        simp only [f, hloc, Function.update_self, hmem]
        exact containsPot_lt hI.1 hl hact
      exact ⟨this.le, fun _ => this⟩
    · have heff := memEffect_of_step hI hs
      have : f (t + 1) = f t := by
        simp only [f, hloc]
        exact containsPot_congr hl k fun u hu => heff.key_eq hu
      refine ⟨this.le, fun hτ => ?_⟩
      rw [hτ] at hs
      have := (step_tau' hs).2.2
      obtain ⟨op, κ, hact, hmem, hloc'⟩ := this
      have hlt : f (t + 1) < f t := by
        simp only [f, hloc', Function.update_self, hmem]
        exact containsPot_lt hI.1 hl hact
      exact absurd this hlt.ne
  obtain ⟨T, hT, hc⟩ := WellFoundedLT.eventually_const_of_succ_le fun t ht => (hstep t ht).1
  refine ⟨T, fun t ht hτ => ?_⟩
  have := (hstep t (by omega)).2 hτ
  rw [hc t ht, hc (t + 1) (by omega)] at this
  exact lt_irrefl _ this

end Podc.HindsightLinearizability
