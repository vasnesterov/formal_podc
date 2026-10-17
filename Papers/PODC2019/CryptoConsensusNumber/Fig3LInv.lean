import Papers.PODC2019.CryptoConsensusNumber.Fig3MStep
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Podc.Computability.Distributed.SharedMemory.History
import Podc.Computability.Distributed.SharedMemory.Model

/-!
# Figure 3: the linearization invariant

`LInv α C K gid L`: `L` is a linearization of the execution `α` (ending in `C`), built with the
linearization points of the paper's proof of Lemma 2 (with the fixes listed in
`differencies.md`):

* `read(a)`: at its snapshot (line 19);
* `transfer` by a non-owner: at its invocation (the paper gives it no linearization point);
* a transfer decided *successful* by `kC_a[r]`: at the first `AS.update` (line 11) containing
  it, by whichever process performs it;
* a transfer decided *failed* by `kC_a[r]`: retroactively, at the snapshot (line 8) of the
  process `q_o` whose proposal was decided, i.e. inserted into the middle of `L` when `q_o`
  invokes `kC_a[r]` first.

`gid t` is the index of the operation instance of `t.p` that created the tuple `t` (ghost).
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct]

/-! ## Generic facts about executions -/

section Exec

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

lemma not_completed_of_eq {α : List (Label P A)} {x : OpId P} (h : x.2 = (respsOf α x.1).length) :
    ¬ Completed α x := by
  simp [Completed, h]

end Exec

/-! ## Notation -/

variable (μ : Acct → Finset (Fin n)) (q₀ : Acct → ℕ) (k : ℕ)

/-- The implemented object. -/
abbrev AT := atSpec (Fin n) Acct μ q₀

/-- Executions. -/
abbrev Hst := List (Label (Fin n) (AT μ q₀))

/-- Sequential histories. -/
abbrev LinL (n : ℕ) (Acct : Type) := List (OpId (Fin n) × ATOp (Fin n) Acct)

variable {μ q₀ k}

/-- The balances after a sequential history. -/
abbrev lst (L : LinL n Acct) : Acct → ℕ := linState (A := AT μ q₀) L

/-- The response of an instance in a sequential history. -/
abbrev lrs (L : LinL n Acct) (x : OpId (Fin n)) : Option (Bool ⊕ ℕ) :=
  (AT μ q₀).respIn (AT μ q₀).init L x

variable (μ q₀)

/-- The linearization invariant. -/
structure LInv (α : Hst μ q₀) (C : Cfg μ q₀ k) (K : Set (Tx n Acct)) (gid : Tx n Acct → ℕ)
    (L : LinL n Acct) : Prop where
  opK : ∀ t ∈ K, opOf α (t.p, gid t) = some (ATOp.transfer t.p t.a t.b t.x)
  inj : ∀ t ∈ K, ∀ t' ∈ K, t.p = t'.p → gid t = gid t' → t = t'
  gidLe : ∀ t ∈ K, gid t < (respsOf α t.p).length ∨ (gid t = (respsOf α t.p).length ∧
    ((C.loc t.p).pc.tx? = some t ∨ ∃ r, (C.loc t.p).pc = .ret r))
  gidCur : ∀ q tx, (C.loc q).pc.tx? = some tx → gid tx = (respsOf α q).length
  lin : IsLinearization α L
  bal : ∀ c, lst (μ := μ) (q₀ := q₀) L c + outSum c (U C.mem) = q₀ c + inSum c (U C.mem)
  memL : ∀ y ∈ L, (∃ a, opOf α y.1 = some (ATOp.read a)) ∨
    (∃ p' a b x, opOf α y.1 = some (ATOp.transfer p' a b x) ∧ y.1.1 ∉ μ a) ∨
    (∃ t ∈ K, y.1 = (t.p, gid t) ∧ (t ∈ U C.mem ∨ ∃ r, Dec C.mem t.a r = some (t, false)))
  respS : ∀ t ∈ K, t ∈ U C.mem → lrs (μ := μ) (q₀ := q₀) L (t.p, gid t) = some (.inl true)
  respF : ∀ t ∈ K, ∀ r, Dec C.mem t.a r = some (t, false) →
    lrs (μ := μ) (q₀ := q₀) L (t.p, gid t) = some (.inl false)
  retR : ∀ q r, (C.loc q).pc = .ret r → lrs (μ := μ) (q₀ := q₀) L (q, (respsOf α q).length) = some r
  rscan : ∀ q a, (C.loc q).pc = .rscan a → (q, (respsOf α q).length) ∉ L.map Prod.fst
  decP : ∀ a r t, Dec C.mem a r = some (t, true) → t ∉ U C.mem →
    t.x ≤ lst (μ := μ) (q₀ := q₀) L a
  propI : ∀ q tx c t res, (C.loc q).pc = .prop tx c (t, res) →
    Dec C.mem tx.a ((C.loc q).rnd tx.a) = none →
    (res = true → t.x ≤ lst (μ := μ) (q₀ := q₀) L t.a) ∧
    (res = false → ∃ S₁ S₂, L = S₁ ++ S₂ ∧ lst (μ := μ) (q₀ := q₀) S₁ t.a < t.x ∧
      ∀ y ∈ S₂, ¬ Precedes α y.1 (t.p, gid t))

variable {μ q₀}

/-! ## Balances -/

lemma inSum_insert {T : Finset (Tx n Acct)} {t : Tx n Acct} (ht : t ∉ T) (c : Acct) :
    inSum c (insert t T) = inSum c T + if t.b = c then t.x else 0 := by
  unfold inSum
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp [ht])]; omega
  · rfl

lemma outSum_insert {T : Finset (Tx n Acct)} {t : Tx n Acct} (ht : t ∉ T) (c : Acct) :
    outSum c (insert t T) = outSum c T + if t.a = c then t.x else 0 := by
  unfold outSum
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp [ht])]; omega
  · rfl

lemma succ_update_union (S : Fin n → Hist n Acct) (q : Fin n) (d : Tx n Acct × Bool) :
    succ (Function.update S q (S q ∪ {d})) = if d.2 = true then insert d.1 (succ S) else succ S := by
  ext t
  simp only [mem_succ]
  have key : (∃ q', (t, true) ∈ Function.update S q (S q ∪ {d}) q') ↔
      (∃ q', (t, true) ∈ S q') ∨ (t, true) = d := by
    constructor
    · rintro ⟨q', hq'⟩
      by_cases h : q' = q
      · subst h
        rw [Function.update_self, Finset.mem_union, Finset.mem_singleton] at hq'
        rcases hq' with h | h
        · exact Or.inl ⟨q', h⟩
        · exact Or.inr h
      · rw [Function.update_of_ne h] at hq'; exact Or.inl ⟨q', hq'⟩
    · rintro (⟨q', hq'⟩ | h)
      · by_cases hh : q' = q
        · subst hh; exact ⟨q', by rw [Function.update_self]; exact Finset.mem_union_left _ hq'⟩
        · exact ⟨q', by rw [Function.update_of_ne hh]; exact hq'⟩
      · exact ⟨q, by rw [Function.update_self, h]; simp⟩
  rw [key]
  obtain ⟨t', b'⟩ := d
  cases b' <;> simp [mem_succ, Prod.ext_iff, or_comm]

/-- The response of an operation appended to a sequential history. -/
lemma lrs_concat_self (L : LinL n Acct) (x : OpId (Fin n)) (o : ATOp (Fin n) Acct)
    (hx : x ∉ L.map Prod.fst) :
    lrs (μ := μ) (q₀ := q₀) (L ++ [(x, o)]) x =
      some ((AT μ q₀).δ (lst (μ := μ) (q₀ := q₀) L) o).2 :=
  ObjSpec.respIn_concat_self (A := AT μ q₀) (q := (AT μ q₀).init) hx o

lemma lst_transfer_true (L : LinL n Acct) (x : OpId (Fin n)) {p : Fin n} {a b : Acct} {v : ℕ}
    (hp : p ∈ μ a) (hv : v ≤ lst (μ := μ) (q₀ := q₀) L a) :
    lst (μ := μ) (q₀ := q₀) (L ++ [(x, ATOp.transfer p a b v)]) = moveFunds (lst (μ := μ) (q₀ := q₀) L) a b v := by
  show linState (A := AT μ q₀) (L ++ _) = _
  rw [linState_concat]
  exact congrArg Prod.fst (atSpec_transfer_pos (q₀ := q₀) ⟨hp, hv⟩)

lemma lrs_transfer_true (L : LinL n Acct) (x : OpId (Fin n)) {p : Fin n} {a b : Acct} {v : ℕ}
    (hp : p ∈ μ a) (hv : v ≤ lst (μ := μ) (q₀ := q₀) L a) (hx : x ∉ L.map Prod.fst) :
    lrs (μ := μ) (q₀ := q₀) (L ++ [(x, ATOp.transfer p a b v)]) x = some (.inl true) := by
  rw [lrs_concat_self _ _ _ hx]
  exact congrArg (fun r => some r.2) (atSpec_transfer_pos (q₀ := q₀) ⟨hp, hv⟩)

/-! ## Initial configuration -/

lemma LInv.init (gid : Tx n Acct → ℕ) :
    LInv μ q₀ ([] : Hst μ q₀) ((impl μ q₀ k).initCfg) ∅ gid [] where
  opK := by simp
  inj := by simp
  gidLe := by simp
  gidCur := by simp [Impl.initCfg, impl, PC.tx?]
  lin := ⟨by simp, by simp, fun a ha => by simp [Completed] at ha,
    fun a b hab hb => by simp at hb, trivial⟩
  bal := by
    intro c
    have : U (impl μ q₀ k).initCfg.mem = ∅ := by
      ext t; simp [mem_U, Impl.initCfg, impl, AS, memInit]
    simp [this, inSum, outSum, lst, linState]; rfl
  memL := by simp
  respS := by simp
  respF := by simp
  retR := by simp [Impl.initCfg, impl]
  rscan := by simp [Impl.initCfg, impl]
  decP := by simp [Impl.initCfg, impl, Dec, KC, memInit]
  propI := by simp [Impl.initCfg, impl]

/-! ## Derived facts -/

section Derived

variable {α : Hst μ q₀} {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {gid : Tx n Acct → ℕ}
  {L : LinL n Acct}

/-- An undecided tuple is not linearized. -/
lemma LInv.not_mem (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) {t : Tx n Acct} (ht : t ∈ K)
    (hU : t ∉ U C.mem) (hF : ∀ r, Dec C.mem t.a r ≠ some (t, false)) :
    (t.p, gid t) ∉ L.map Prod.fst := by
  intro hm
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 hm
  have hop := hL.opK t ht
  rcases hL.memL y hy with ⟨a, ha⟩ | ⟨p', a, b, x, ha, hμ⟩ | ⟨t', ht', hyt, h⟩
  · rw [hy1, hop] at ha; cases ha
  · rw [hy1, hop] at ha
    simp only [Option.some.injEq, ATOp.transfer.injEq] at ha
    obtain ⟨-, rfl, -, -⟩ := ha
    rw [hy1] at hμ
    exact hμ (hM.kOwn t ht)
  · rw [hy1] at hyt
    simp only [Prod.mk.injEq] at hyt
    have := hL.inj t ht t' ht' hyt.1 hyt.2
    subst this
    rcases h with h | ⟨r, hr⟩
    · exact hU h
    · exact hF r hr

/-- A tuple that its originator has not committed yet belongs to the originator's pending
operation. -/
lemma LInv.pending (hL : LInv μ q₀ α C K gid L) (hM : MInv μ C K) {t : Tx n Acct} (ht : t ∈ K)
    (hc : t ∉ (C.loc t.p).com t.a) :
    (C.loc t.p).pc.tx? = some t ∧ gid t = (respsOf α t.p).length := by
  have h1 := ((hM.proc t.p).kCur t ht rfl).resolve_right hc
  exact ⟨h1, hL.gidCur _ _ h1⟩

/-- A tuple that is undecided is not committed by its originator. -/
lemma MInv.not_com_of_undec (hM : MInv μ C K) {t : Tx n Acct}
    (h : ∀ r b, Dec C.mem t.a r ≠ some (t, b)) : t ∉ (C.loc t.p).com t.a := by
  intro hc
  obtain ⟨r, -, b, hb⟩ := ((hM.proc t.p).com t.a t).1 hc
  exact h r b hb

/-- A tuple that is decided successful and not in `AS` is not committed by its originator. -/
lemma MInv.not_com_of_notU (hM : MInv μ C K) {t : Tx n Acct} {r : ℕ}
    (hd : Dec C.mem t.a r = some (t, true)) (hU : t ∉ U C.mem) :
    t ∉ (C.loc t.p).com t.a := by
  intro hc
  obtain ⟨r', hr', b, hb⟩ := ((hM.proc t.p).com t.a t).1 hc
  obtain ⟨d, hd', hm⟩ := (hM.proc t.p).asAll t.a r' hr'
  rw [hb] at hd'; cases hd'
  have : b = true := hM.dec_res hb hd
  subst this
  exact hU (mem_U.2 ⟨t.p, hm⟩)

end Derived

end CryptoCons.Fig3
