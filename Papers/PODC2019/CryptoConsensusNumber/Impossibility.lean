import Papers.PODC2019.CryptoConsensusNumber.System

/-!
# `k`-shared asset transfer cannot solve consensus for more than `k` processes

The "at most `k`" half of Theorem 2 (and Corollary 1 for `k = 1`). The paper derives it from
Lemma 2 (a wait-free implementation of `k`-shared asset transfer from registers, an atomic
snapshot and `k`-consensus objects), the cited fact that `k`-consensus objects cannot solve
`(k+1)`-process consensus, and (implicitly) composition of linearizable implementations. We give
a direct valency proof instead.

Proof. Take a critical configuration (CSLib: `biv_initial`, `exists_crit`); all processes are
poised on the same object (`Crit.poised`), and some process `p` is on team `0`, some `q` on
team `1`.
* A read/write object is impossible (`crit_overwrite`: a read or failing operation followed by
  anything, or two blind writes).
* On an asset-transfer object: if `p`'s operation is a read or a failing transfer it does not
  change the state (`crit_overwrite`); likewise for `q`. So both are successful transfers, by
  their callers (`Honest`), hence `p` and `q` own the source accounts. If the source accounts
  differ, the two transfers commute (`crit_commute`). So **every** pair of processes on opposite
  teams withdraws from one common account `a`, and then every process (being on some team) owns
  `a`: `|μ(a)| ≥ n > k`.
-/

namespace CryptoCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {n : ℕ} {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec}
  {Acct : Type} [DecidableEq Acct] {μ : ιS → Acct → Finset (Fin n)}

/-- Two processes on opposite teams at a critical execution, poised on the same asset-transfer
object, are both poised on successful transfers (under their own identity) from one common
account, which they both own. -/
theorem at_pair {A : Alg n (atSys R μ)} (hA : WFConsensus A) (hH : Honest R μ A)
    {x : Fin n → Bool} {α : List (Ev n)} (hc : Crit 0 (initCfg A x) α)
    {p q : Fin n} {v w : Bool} (hp : Team 0 (initCfg A x) α p v)
    (hq : Team 0 (initCfg A x) α q w) (hvw : w ≠ v) {j : ιS} {o o' : ATOp (Fin n) Acct}
    {κ κ' : (Bool ⊕ ℕ) → A.L}
    (hpa : A.act ((run (initCfg A x) α).loc p) = .access (.inr j) o κ)
    (hqa : A.act ((run (initCfg A x) α).loc q) = .access (.inr j) o' κ') :
    ∃ a b y b' y', o = .transfer p a b y ∧ o' = .transfer q a b' y' ∧ p ∈ μ j a ∧ q ∈ μ j a := by
  have hC : Reach A CrashFree (initCfg A x) := Reach.initial admOK_crashFree x
  have hcf : CrashFree α := crashFree_of_inE_zero hc.1.inE
  have hwv : v ≠ w := Ne.symm hvw
  set E := run (initCfg A x) α with hE
  set s : Acct → ℕ := E.mem (.inr j) with hs
  -- the transitions of the object at `s`
  let S := atSpec (Fin n) Acct (μ j) (fun _ => 0)
  -- `p`'s operation changes the state
  cases o with
  | read a =>
    exact (crit_overwrite hA hC hc hp hq hvw hpa hqa rfl).elim
  | transfer p' a b y =>
    have hp' : p' = p := hH x α hcf p j p' a b y κ hpa
    subst hp'
    by_cases hok : p' ∈ μ j a ∧ y ≤ s a
    swap
    · exact (crit_overwrite hA hC hc hp hq hvw hpa hqa
        (by rw [show ((atSys R μ (.inr j)).δ (E.mem (.inr j)) (.transfer p' a b y)).1 =
          E.mem (.inr j) from congrArg Prod.fst (atSpec_transfer_neg (q₀ := fun _ => 0) hok)])).elim
    cases o' with
    | read a' =>
      exact (crit_overwrite hA hC hc hq hp hwv hqa hpa rfl).elim
    | transfer q' a' b' y' =>
      have hq' : q' = q := hH x α hcf q j q' a' b' y' κ' hqa
      subst hq'
      by_cases hok' : q' ∈ μ j a' ∧ y' ≤ s a'
      swap
      · exact (crit_overwrite hA hC hc hq hp hwv hqa hpa
          (by rw [show ((atSys R μ (.inr j)).δ (E.mem (.inr j)) (.transfer q' a' b' y')).1 =
            E.mem (.inr j) from congrArg Prod.fst (atSpec_transfer_neg (q₀ := fun _ => 0) hok')])).elim
      by_cases haa : a = a'
      · subst haa
        exact ⟨a, b, y, b', y', rfl, rfl, hok.1, hok'.1⟩
      · exfalso
        have e1 : S.δ s (.transfer p' a b y) = (moveFunds s a b y, .inl true) :=
          atSpec_transfer_pos hok
        have e2 : S.δ s (.transfer q' a' b' y') = (moveFunds s a' b' y', .inl true) :=
          atSpec_transfer_pos hok'
        have e3 : S.δ (moveFunds s a b y) (.transfer q' a' b' y') =
            (moveFunds (moveFunds s a b y) a' b' y', .inl true) :=
          atSpec_transfer_pos ⟨hok'.1, hok'.2.trans (le_moveFunds_of_ne s y (Ne.symm haa))⟩
        have e4 : S.δ (moveFunds s a' b' y') (.transfer p' a b y) =
            (moveFunds (moveFunds s a' b' y') a b y, .inl true) :=
          atSpec_transfer_pos ⟨hok.1, hok.2.trans (le_moveFunds_of_ne s y' haa)⟩
        refine crit_commute hA hC hc hp hq hvw hpa hqa ?_ ?_
        · change (S.δ (S.δ s (.transfer p' a b y)).1 (.transfer q' a' b' y')).1 =
            (S.δ (S.δ s (.transfer q' a' b' y')).1 (.transfer p' a b y)).1
          rw [e1, e2, e3, e4]
          exact moveFunds_comm s b b' haa hok.2 hok'.2
        · change (S.δ s (.transfer p' a b y)).2 =
            (S.δ (S.δ s (.transfer q' a' b' y')).1 (.transfer p' a b y)).2
          rw [e1, e2, e4]

/-- **Theorem 2, "at most `k`" (Corollary 1 for `k = 1`).** For `n > k` (and `n ≥ 2`), there is
no wait-free consensus algorithm for `n` processes using read/write objects and any number of
asset-transfer objects in which every account has at most `k` owners. -/
theorem no_consensus {k : ℕ} (hn : 2 ≤ n) (hkn : k < n) (hR : ∀ j, (R j).RWLike)
    (hμ : ∀ j, KShared (μ j) k) (A : Alg n (atSys R μ)) (hH : Honest R μ A) :
    ¬ WFConsensus A := by
  intro hA
  have hn0 : 0 < n := by omega
  let x : Fin n → Bool := fun p => decide (p.val = 1)
  have hb := biv_initial (z := 0) hA admOK_crashFree x ⟨⟨0, hn0⟩, by simp [x]⟩
    ⟨⟨1, by omega⟩, by simp [x]⟩
  have hC : Reach A CrashFree (initCfg A x) := Reach.initial admOK_crashFree x
  obtain ⟨α, hc⟩ := exists_crit hA admOK_crashFree hC hb
  obtain ⟨i, hi⟩ := hc.poised hA admOK_crashFree hC hn0
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hc.teams hA admOK_crashFree hC hn0
  rcases i with j | j
  · -- all processes poised on a read/write object
    obtain ⟨o, κ, ho⟩ := hi p
    obtain ⟨o', κ', ho'⟩ := hi q
    set s := (run (initCfg A x) α).mem (.inl j)
    rcases hR j o with hro | hbw
    · exact crit_overwrite hA hC hc hp hq (by simp) ho ho'
        (congrArg (fun t => (atSys R μ (.inl j)).δ t o') (hro s))
    · rcases hR j o' with hro' | hbw'
      · exact crit_overwrite hA hC hc hq hp (by simp) ho' ho
          (congrArg (fun t => (atSys R μ (.inl j)).δ t o) (hro' s))
      · exact crit_overwrite hA hC hc hp hq (by simp) ho ho' (hbw' _ _)
  · -- all processes poised on the asset-transfer object `j`
    choose o κ ho using hi
    obtain ⟨a, b, y, b', y', hpo, hqo, -, -⟩ := at_pair hA hH hc hp hq (by simp) (ho p) (ho q)
    have hall : ∀ r, r ∈ μ j a := by
      intro r
      obtain ⟨w, hw⟩ := hc.team r
      cases w
      · obtain ⟨a₁, _, _, _, _, -, hq₁, hr₁, -⟩ := at_pair hA hH hc hw hq (by simp) (ho r) (ho q)
        rw [hqo] at hq₁
        cases hq₁
        exact hr₁
      · obtain ⟨a₁, _, _, _, _, hp₁, -, -, hr₁⟩ := at_pair hA hH hc hp hw (by simp) (ho p) (ho r)
        rw [hpo] at hp₁
        cases hp₁
        exact hr₁
    have : (Finset.univ : Finset (Fin n)) ⊆ μ j a := fun r _ => hall r
    have := Finset.card_le_card this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have := hμ j a
    omega

end CryptoCons
