import Papers.PODC2019.CryptoConsensusNumber.Fig1Defs

/-!
# Figure 1 as written (`ops_p` a set) is not linearizable

In Figure 1 of Guerraoui et al. (PODC 2019) every process keeps the *set* `ops_p` of its
successful transfers and publishes it in the snapshot (`ops_p := ops_p ∪ {(a, b, x)}`), and
`balance(a, S)` sums over the transfers in the snapshot. Two successful transfers with the same
arguments `(a, b, x)` by the same process are then recorded only once, so the second one is not
debited.

Counterexample (`literalImpl`): one process (the owner of account `0`), accounts `0` and `1`,
initial balances `2` and `0`. The process performs `transfer(0, 1, 1)` three times in a solo run.
After the first one the snapshot holds `{(0, 1, 1)}` and `balance(0) = 1`, which stays so
forever: all three transfers return `true`. Three successful withdrawals of `1` from a balance of
`2` are not legal in any order, so the execution has no linearization at all.

The fix (`impl` in `Fig1Defs.lean`, proved correct in `Fig1.lean`) records transfers in a
sequence (equivalently: tag each transfer with a sequence number).
-/

namespace CryptoCons.Fig1.Bug

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj

/-- Process `()` owns account `0`; account `1` has no owner. -/
def μ : Fin 2 → Finset Unit := fun a => if a = 0 then {()} else ∅

/-- Initial balances: `2` on account `0`, `0` on account `1`. -/
def q₀ : Fin 2 → ℕ := fun a => if a = 0 then 2 else 0

/-- Single owner per account: the hypothesis of Theorem 1 holds. -/
lemma μ_single : ∀ a, (μ a).card ≤ 1 := by decide

/-- `transfer(0, 1, 1)` invoked by `()`. -/
abbrev t : (atSpec Unit (Fin 2) μ q₀).Op := ATOp.transfer () 0 1 1

/-- One complete `transfer(0, 1, 1)`: invocation, snapshot, update, response `true`. -/
abbrev block : List (Label Unit (atSpec Unit (Fin 2) μ q₀)) :=
  [.inv () t, .tau (), .tau (), .ret () (.inl true)]

/-- The solo execution with three successful `transfer(0, 1, 1)`. -/
abbrev α : List (Label Unit (atSpec Unit (Fin 2) μ q₀)) := block ++ block ++ block

/-- `α` is an execution of the literal Figure 1 (all three transfers return `true`). -/
theorem valid : (literalImpl μ q₀).Valid α := by
  rw [Impl.Valid, ← Option.isSome_iff_exists]
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, literalImpl, implGen, allowedOp, balance,
    inflow, outflow, inAmt, outAmt, μ, q₀]

/-- Sanity check: in the fixed implementation the same schedule is not an execution (the third
transfer returns `false`). -/
theorem not_valid_fixed : ¬ (impl μ q₀).Valid α := by
  rw [Impl.Valid, ← Option.isSome_iff_exists]
  simp [Impl.run, Impl.runFrom, Impl.step, Impl.initCfg, impl, implGen, allowedOp, balance,
    inflow, outflow, inAmt, outAmt, μ, q₀]

lemma opsOf_α : opsOf α () = List.replicate 3 t := rfl

lemma respsOf_α : respsOf α () = List.replicate 3 (.inl true : (atSpec Unit (Fin 2) μ q₀).Resp) :=
  rfl

/-- A legal sequential history consisting only of successful `transfer(0, 1, 1)` has at most as
many entries as the initial balance of account `0`. -/
lemma length_le_of_seqOK (L : List (OpId Unit × (atSpec Unit (Fin 2) μ q₀).Op))
    (hL : ∀ y ∈ L, y.2 = t ∧ respOf α y.1 = some (.inl true)) (q : Fin 2 → ℕ)
    (hseq : SeqOK α q L) : L.length ≤ q 0 := by
  induction L generalizing q with
  | nil => simp
  | cons y L ih =>
    obtain ⟨x, o⟩ := y
    obtain ⟨ho, hr⟩ := hL (x, o) (by simp)
    simp only at ho hr; subst ho
    obtain ⟨h1, h2⟩ := hseq
    have hresp := h1 _ hr
    have hle := ih (fun y hy => hL y (by simp [hy])) _ h2
    by_cases hc : () ∈ μ 0 ∧ 1 ≤ q 0
    · rw [atSpec_transfer_pos hc] at hle
      simp only [moveFunds_apply, ↓reduceIte] at hle
      simp only [List.length_cons]
      have : (1 : Fin 2) ≠ 0 := by decide
      simp only [Ne.symm this, ↓reduceIte] at hle
      omega
    · rw [atSpec_transfer_neg hc] at hresp; cases hresp

/-- `α` has no linearization. -/
theorem no_linearization (L : List (OpId Unit × (atSpec Unit (Fin 2) μ q₀).Op)) :
    ¬ IsLinearization α L := by
  intro hL
  have hall : ∀ y ∈ L, y.2 = t ∧ respOf α y.1 = some (.inl true) := by
    intro y hy
    obtain ⟨⟨u, k⟩, o⟩ := y
    cases u
    have h := hL.op_eq _ hy
    simp only [opOf, opsOf_α, List.getElem?_replicate] at h
    split_ifs at h with hk
    simp only [Option.some.injEq] at h
    refine ⟨h.symm, ?_⟩
    simp only [respOf, respsOf_α, List.getElem?_replicate, hk, ↓reduceIte]
  have hlen := length_le_of_seqOK L hall q₀ hL.seq
  have hsub : [((), 0), ((), 1), ((), 2)] ⊆ L.map Prod.fst := by
    intro z hz
    apply hL.complete
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> simp [Completed]
  have h3 := ((List.nodup_cons.2 ⟨by simp, by simp⟩ : [((), 0), ((), 1), ((), 2)].Nodup).subperm
    hsub).length_le
  simp [q₀] at hlen h3
  omega

/-- **Figure 1 as written is not linearizable**, even with a single owner per account
(`μ_single`): the literal algorithm, where `ops_p` is a set, admits the execution `α` with three
successful `transfer(0, 1, 1)` from a balance of `2`, which has no linearization. -/
theorem literal_not_linearizable : ¬ (literalImpl μ q₀).Linearizable := by
  rintro ⟨h, hh⟩
  exact no_linearization _ (hh α valid)

end CryptoCons.Fig1.Bug
