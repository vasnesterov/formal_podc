import Papers.PODC2012.TMLiveness.Safety

/-!
# The environment's strategy and why `p₁` never commits

The environment plays against a TM ensuring strict serializability with two distinguished
processes `p₁`, `p₂` and one t-variable `x`; all other processes only ever read `x` and never try
to commit. This generalizes Strategies 1 and 2 of the paper (Algorithms 1 and 2 of the PODC
version) so that it works under *any* scheduler, in particular a fair (round-robin) one: idle
processes that are not "active" invoke filler reads of `x`.

* `p₁` starts a transaction `T₁` by reading `x` (value `a`). It then keeps reading `x` until it is
  *ready*: some transaction of `p₂` that had not completed when `T₁` began has committed, the last
  such one wrote a value `d ≠ a` to `x`, and `p₂` has no pending commit request. Then `p₁` writes
  to `x` a value `b` that none of these transactions of `p₂` read first, and invokes `tryC`.
* `p₂` starts each transaction by reading `x`. While `T₁` has read `a` and `p₁` is not ready, `p₂`
  writes `bump a ≠ a` to `x` and invokes `tryC`; otherwise it keeps reading `x`.

The scripts depend on the current history only (via `info`). The invariant `Good` is preserved by
every step allowed by the scripts and the TM, except a commit event for `p₁`; and such a commit
would make the history not even serializable (`not_serializable_commit`): this is the paper's argument
that "Algorithm 1 never terminates", for an arbitrary schedule. Hence in every run of the strategy
`p₁` is never returned a commit event (`run_ne_commit₁`).
-/

namespace Podc.TMLiveness

variable {P X V : Type*} [DecidableEq P] [DecidableEq X] [DecidableEq V]

/-- The value of the first operation of a transaction, if it is a read. -/
def firstRead : List (Op X V) → Option V
  | .read _ v :: _ => some v
  | _ => none

/-- The parameters of the environment's strategy. -/
structure Setup (P X V : Type*) where
  /-- The t-variable all processes access. -/
  x : X
  /-- The process that will never commit. -/
  p₁ : P
  /-- The process whose commits make `p₁` abort. -/
  p₂ : P
  hp : p₁ ≠ p₂
  /-- A value different from a given one (the paper's `v + 1`). -/
  bump : V → V
  bump_ne : ∀ v, bump v ≠ v
  /-- A value outside a given list. -/
  pick : List V → V
  pick_not_mem : ∀ l, pick l ∉ l

namespace Setup

variable (S : Setup P X V) (I : HInfo P X V)

/-- The current transaction `T₁` of `p₁`. -/
def T₁ : TxId P := (S.p₁, I.cnt S.p₁)

/-- The value `T₁` first read, if any. -/
def a : Option V := firstRead (I.ops (S.T₁ I))

/-- The transactions of `p₂` numbered `≥ j₀` had not completed when `T₁` began. -/
def j₀ : ℕ := I.snap (S.T₁ I) S.p₂

/-- The committed transactions of `p₂` that had not completed when `T₁` began, in order. -/
def chain : List ℕ :=
  (List.range (I.cnt S.p₂)).filter (fun j => decide (S.j₀ I ≤ j) && I.committed (S.p₂, j))

/-- All committed transactions of `p₂`, in order. -/
def allc : List ℕ := (List.range (I.cnt S.p₂)).filter (fun j => I.committed (S.p₂, j))

/-- The values first read by the committed transactions of `p₂`. -/
def cs : List V := (S.allc I).filterMap (fun j => firstRead (I.ops (S.p₂, j)))

/-- The value last written to `x` by the last chain transaction. -/
def dlast : Option V := (S.chain I).getLast?.bind (fun j => lastWrite S.x (I.ops (S.p₂, j)))

/-- `p₁` is ready to write and commit. -/
def Ready : Prop :=
  ∃ a d, S.a I = some a ∧ S.dlast I = some d ∧ d ≠ a ∧ I.pend S.p₂ ≠ some .tryC

open Classical in
/-- The operation an idle process invokes. -/
noncomputable def script (k : P) : Inv X V :=
  if k = S.p₁ then
    match S.a I with
    | none => .read S.x
    | some _ =>
      if S.Ready I then
        (if lastWrite S.x (I.ops (S.T₁ I)) = none then .write S.x (S.pick (S.cs I)) else .tryC)
      else .read S.x
  else if k = S.p₂ then
    if I.began (S.p₂, I.cnt S.p₂) = false then .read S.x
    else
      match S.a I with
      | some a =>
        if S.Ready I then .read S.x
        else if lastWrite S.x (I.ops (S.p₂, I.cnt S.p₂)) = some (S.bump a) then .tryC
        else .write S.x (S.bump a)
      | none => .read S.x
  else .read S.x

/-- Events allowed by the strategy and a TM: an idle process invokes its scripted operation; a
process with a pending invocation receives a fitting response. -/
def StratEv : Ev P X V → Prop
  | .inv k i => I.pend k = none ∧ i = S.script I k
  | .res k i r => I.pend k = some i ∧ r.Fits i

/-- The invariant of runs of the strategy. -/
structure Good : Prop where
  p₁_uncommitted : ∀ j, I.committed (S.p₁, j) = false
  others : ∀ k, k ≠ S.p₁ → k ≠ S.p₂ → (∀ j, I.committed (k, j) = false) ∧ I.pend k ≠ some .tryC
  ops_shape : ∀ t, I.ops t = [] ∨ ∃ c r, I.ops t = .read S.x c :: r
  idle_ops : ∀ k, I.began (k, I.cnt k) = true → I.pend k = none → I.ops (k, I.cnt k) ≠ []
  committed_ops : ∀ j, I.committed (S.p₂, j) = true → I.ops (S.p₂, j) ≠ []
  write_ready : ∀ b, (I.pend S.p₁ = some (.write S.x b) ∨ lastWrite S.x (I.ops (S.T₁ I)) = some b) →
    S.Ready I ∧ b ∉ S.cs I
  tryC_wrote : I.pend S.p₁ = some .tryC → lastWrite S.x (I.ops (S.T₁ I)) ≠ none
  pend_x : ∀ k i, I.pend k = some i → i = .read S.x ∨ (∃ v, i = .write S.x v) ∨ i = .tryC
  pend_ops : ∀ k i, I.pend k = some i → i ≠ .read S.x → I.ops (k, I.cnt k) ≠ []

end Setup

/-! ### List lemmas -/

omit [DecidableEq P] in
theorem lastWrite_append (x : X) :
    ∀ l l' : List (Op X V), lastWrite x (l ++ l') = (lastWrite x l').or (lastWrite x l)
  | [], l' => by simp [lastWrite]
  | .read y v :: l, l' => by simp [lastWrite, lastWrite_append x l l']
  | .write y v :: l, l' => by simp [lastWrite, lastWrite_append x l l', Option.or_assoc]

omit [DecidableEq P] in
@[simp] theorem lastWrite_append_read (x y : X) (v : V) (l : List (Op X V)) :
    lastWrite x (l ++ [.read y v]) = lastWrite x l := by
  simp [lastWrite_append, lastWrite]

omit [DecidableEq P] in
@[simp] theorem lastWrite_append_write (x : X) (v : V) (l : List (Op X V)) :
    lastWrite x (l ++ [.write x v]) = some v := by
  simp [lastWrite_append, lastWrite]

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem firstRead_append {l : List (Op X V)} (hl : l ≠ []) (l' : List (Op X V)) :
    firstRead (l ++ l') = firstRead l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l => cases o <;> rfl

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem eq_read_of_firstRead {x : X} {l : List (Op X V)} {a : V}
    (hs : l = [] ∨ ∃ c r, l = .read x c :: r) (ha : firstRead l = some a) :
    ∃ r, l = .read x a :: r := by
  rcases hs with rfl | ⟨c, r, rfl⟩
  · simp [firstRead] at ha
  · simp only [firstRead, Option.some.injEq] at ha
    exact ⟨r, by rw [ha]⟩

theorem le_of_mem_getLast {l : List ℕ} (hl : l.Pairwise (· < ·)) {m : ℕ}
    (hm : l.getLast? = some m) : ∀ j ∈ l, j ≤ m := by
  obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 hm
  intro j hj
  rw [List.pairwise_append] at hl
  rcases List.mem_append.1 hj with hj | hj
  · exact (hl.2.2 j hj m (by simp)).le
  · simp at hj; omega

namespace Setup

variable (S : Setup P X V)

theorem chain_pairwise (I : HInfo P X V) : (S.chain I).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem mem_chain {I : HInfo P X V} {j : ℕ} :
    j ∈ S.chain I ↔ j < I.cnt S.p₂ ∧ S.j₀ I ≤ j ∧ I.committed (S.p₂, j) = true := by
  simp [chain]

/-- The chain only depends on which transactions of `p₂` are in it. -/
theorem chain_eq {I J : HInfo P X V} (h : ∀ j, j ∈ S.chain I ↔ j ∈ S.chain J) :
    S.chain I = S.chain J :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => by omega) (S.chain_pairwise I)
    (S.chain_pairwise J)
    ((List.perm_ext_iff_of_nodup (S.chain_pairwise I).nodup (S.chain_pairwise J).nodup).2 h)

theorem allc_pairwise (I : HInfo P X V) : (S.allc I).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem mem_allc {I : HInfo P X V} {j : ℕ} :
    j ∈ S.allc I ↔ j < I.cnt S.p₂ ∧ I.committed (S.p₂, j) = true := by
  simp [allc]

theorem allc_eq {I J : HInfo P X V} (h : ∀ j, j ∈ S.allc I ↔ j ∈ S.allc J) :
    S.allc I = S.allc J :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => by omega) (S.allc_pairwise I)
    (S.allc_pairwise J)
    ((List.perm_ext_iff_of_nodup (S.allc_pairwise I).nodup (S.allc_pairwise J).nodup).2 h)

/-- `cs` and `dlast` agree in two states that agree on `T₁`, on when `T₁` began, and on the
committed transactions of `p₂` and their operations. -/
theorem cs_dlast_of_agree {I J : HInfo P X V} (hT : S.T₁ J = S.T₁ I)
    (hsn : J.snap (S.T₁ I) S.p₂ = I.snap (S.T₁ I) S.p₂)
    (hcm : ∀ j, J.committed (S.p₂, j) = I.committed (S.p₂, j))
    (hcnt : I.cnt S.p₂ ≤ J.cnt S.p₂)
    (hnew : ∀ j, I.cnt S.p₂ ≤ j → j < J.cnt S.p₂ → I.committed (S.p₂, j) = false)
    (hops : ∀ j, j < I.cnt S.p₂ → J.ops (S.p₂, j) = I.ops (S.p₂, j)) :
    S.cs J = S.cs I ∧ S.dlast J = S.dlast I := by
  have hj0 : S.j₀ J = S.j₀ I := by simp only [Setup.j₀, hT, hsn]
  have hmem : ∀ j, (j < J.cnt S.p₂ ∧ J.committed (S.p₂, j) = true) ↔
      (j < I.cnt S.p₂ ∧ I.committed (S.p₂, j) = true) := by
    intro j
    rw [hcm]
    constructor
    · rintro ⟨h1, h3⟩
      refine ⟨?_, h3⟩
      by_contra h
      rw [hnew j (by omega) h1] at h3
      simp at h3
    · rintro ⟨h1, h3⟩
      exact ⟨by omega, h3⟩
  have hchain : S.chain J = S.chain I := by
    apply S.chain_eq
    intro j
    rw [S.mem_chain, S.mem_chain, hj0]
    have := hmem j
    tauto
  have hallc : S.allc J = S.allc I := S.allc_eq (fun j => by rw [S.mem_allc, S.mem_allc]; exact hmem j)
  constructor
  · unfold cs
    rw [hallc]
    exact List.filterMap_congr (fun j hj => by rw [hops j (S.mem_allc.1 hj).1])
  · unfold dlast
    rw [hchain]
    cases hl : (S.chain I).getLast? with
    | none => rfl
    | some m =>
      have : m ∈ S.chain I := List.mem_of_getLast? hl
      simp [hops m (S.mem_chain.1 this).1]

theorem a_of_agree {I J : HInfo P X V} (hT : S.T₁ J = S.T₁ I)
    (hops : J.ops (S.T₁ I) = I.ops (S.T₁ I) ∨
      (I.ops (S.T₁ I) ≠ [] ∧ ∃ l, J.ops (S.T₁ I) = I.ops (S.T₁ I) ++ l)) : S.a J = S.a I := by
  simp only [Setup.a, hT]
  rcases hops with h | ⟨hne, l, h⟩
  · rw [h]
  · rw [h, firstRead_append hne]

/-! ### What the scripts invoke -/

variable {S}

theorem a_ne_none_of_ready {I : HInfo P X V} (h : S.Ready I) : S.a I ≠ none := by
  obtain ⟨a, d, ha, -⟩ := h; simp [ha]

/-- Case analysis on the script. -/
theorem script_cases (I : HInfo P X V) (k : P) :
    (S.script I k = .read S.x) ∨
    (k = S.p₁ ∧ S.Ready I ∧ lastWrite S.x (I.ops (S.T₁ I)) = none ∧
      S.script I k = .write S.x (S.pick (S.cs I))) ∨
    (k = S.p₁ ∧ S.Ready I ∧ lastWrite S.x (I.ops (S.T₁ I)) ≠ none ∧ S.script I k = .tryC) ∨
    (k = S.p₂ ∧ I.began (S.p₂, I.cnt S.p₂) = true ∧ ¬ S.Ready I ∧ ∃ a, S.a I = some a ∧
      (S.script I k = .write S.x (S.bump a) ∨ S.script I k = .tryC)) := by
  by_cases h1 : k = S.p₁
  · subst h1
    cases ha : S.a I with
    | none => left; simp [script, ha]
    | some a =>
      by_cases hr : S.Ready I
      · by_cases hl : lastWrite S.x (I.ops (S.T₁ I)) = none
        · right; left; simp [script, ha, hr, hl]
        · right; right; left; simp [script, ha, hr, hl]
      · left; simp [script, ha, hr]
  · by_cases h2 : k = S.p₂
    · subst h2
      by_cases hb : I.began (S.p₂, I.cnt S.p₂) = false
      · left; simp [script, hb, h1]
      · cases ha : S.a I with
        | none => left; simp [script, ha, h1]
        | some a =>
          by_cases hr : S.Ready I
          · left; simp [script, ha, hr, h1]
          · right; right; right
            refine ⟨rfl, by simpa using hb, hr, a, rfl, ?_⟩
            by_cases hl : lastWrite S.x (I.ops (S.p₂, I.cnt S.p₂)) = some (S.bump a)
            · right; simp [script, ha, hr, h1, hl, hb]
            · left; simp [script, ha, hr, h1, hl, hb]
    · left; simp [script, h1, h2]

theorem script_read {I : HInfo P X V} {k : P} {y : X} (h : S.script I k = .read y) : y = S.x := by
  rcases S.script_cases I k with h' | ⟨-, -, -, h'⟩ | ⟨-, -, -, h'⟩ | ⟨-, -, -, a, -, h' | h'⟩ <;>
    rw [h'] at h <;> simp_all

theorem script_write {I : HInfo P X V} {k : P} {y : X} {v : V} (h : S.script I k = .write y v) :
    y = S.x ∧ ((k = S.p₁ ∧ S.Ready I ∧ lastWrite S.x (I.ops (S.T₁ I)) = none ∧ v = S.pick (S.cs I)) ∨
      (k = S.p₂ ∧ I.began (S.p₂, I.cnt S.p₂) = true ∧ ¬ S.Ready I ∧
        ∃ a, S.a I = some a ∧ v = S.bump a)) := by
  rcases S.script_cases I k with h' | ⟨h1, h2, h3, h'⟩ | ⟨-, -, -, h'⟩ | ⟨h1, h2, h3, a, ha, h' | h'⟩ <;>
    rw [h'] at h <;> simp only [Inv.write.injEq, reduceCtorEq] at h
  · exact ⟨h.1.symm, Or.inl ⟨h1, h2, h3, h.2.symm⟩⟩
  · exact ⟨h.1.symm, Or.inr ⟨h1, h2, h3, a, ha, h.2.symm⟩⟩

theorem script_tryC {I : HInfo P X V} {k : P} (h : S.script I k = .tryC) :
    (k = S.p₁ ∧ S.Ready I ∧ lastWrite S.x (I.ops (S.T₁ I)) ≠ none) ∨
      (k = S.p₂ ∧ I.began (S.p₂, I.cnt S.p₂) = true ∧ ¬ S.Ready I) := by
  rcases S.script_cases I k with h' | ⟨h1, h2, h3, h'⟩ | ⟨h1, h2, h3, h'⟩ | ⟨h1, h2, h3, a, ha, h' | h'⟩ <;>
    rw [h'] at h <;> simp only [reduceCtorEq] at h
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h1, h2, h3⟩

theorem script_p₂_eq {I : HInfo P X V} (hb : I.began (S.p₂, I.cnt S.p₂) = true) {a : V}
    (ha : S.a I = some a) (hr : ¬ S.Ready I) :
    S.script I S.p₂ = if lastWrite S.x (I.ops (S.p₂, I.cnt S.p₂)) = some (S.bump a) then .tryC
      else .write S.x (S.bump a) := by
  simp [script, Ne.symm S.hp, hb, ha, hr]

theorem script_p₂_tryC {I : HInfo P X V} (h : S.script I S.p₂ = .tryC) :
    ∃ a, S.a I = some a ∧ ¬ S.Ready I ∧
      lastWrite S.x (I.ops (S.p₂, I.cnt S.p₂)) = some (S.bump a) := by
  rcases S.script_tryC h with ⟨h1, -⟩ | ⟨-, hb, hr⟩
  · exact absurd h1.symm S.hp
  · cases ha : S.a I with
    | none => simp [script, Ne.symm S.hp, ha] at h
    | some a =>
      rw [S.script_p₂_eq hb ha hr] at h
      refine ⟨a, rfl, hr, ?_⟩
      by_contra hl; simp [hl] at h

theorem script_other {I : HInfo P X V} {k : P} (h1 : k ≠ S.p₁) (h2 : k ≠ S.p₂) :
    S.script I k = .read S.x := by
  simp [script, h1, h2]

theorem script_p₁_none {I : HInfo P X V} (h : S.a I = none) : S.script I S.p₁ = .read S.x := by
  simp [script, h]

theorem script_p₂_closed {I : HInfo P X V} (h : I.began (S.p₂, I.cnt S.p₂) = false) :
    S.script I S.p₂ = .read S.x := by
  simp [script, h, Ne.symm S.hp]

/-! ### Preservation of the invariant -/

omit [DecidableEq P] [DecidableEq V] in
theorem ne_nil_of_lastWrite {x : X} {l : List (Op X V)} (h : lastWrite x l ≠ none) : l ≠ [] := by
  rintro rfl; simp [lastWrite] at h

theorem ops_ne_nil_of_a {I : HInfo P X V} (h : S.a I ≠ none) : I.ops (S.T₁ I) ≠ [] := by
  intro h'; apply h; simp [Setup.a, h', firstRead]

theorem began_of_a {I : HInfo P X V} (hwf : WF I) (h : S.a I ≠ none) : I.began (S.T₁ I) = true := by
  by_contra hb
  exact S.ops_ne_nil_of_a h (hwf.ops_nil S.p₁ (by simpa [Setup.T₁] using hb))

theorem ready_congr {I J : HInfo P X V} (ha : S.a J = S.a I) (hd : S.dlast J = S.dlast I)
    (hp : J.pend S.p₂ = some .tryC ↔ I.pend S.p₂ = some .tryC) : S.Ready J ↔ S.Ready I := by
  simp only [Setup.Ready, ha, hd, ne_eq, hp]

theorem good_step_inv {I : HInfo P X V} (hwf : WF I) (hg : S.Good I) {k : P} {i : Inv X V}
    (hpk : I.pend k = none) (hi : i = S.script I k) : S.Good (I.step (.inv k i)) := by
  have hT : S.T₁ (I.step (.inv k i)) = S.T₁ I := rfl
  have ha : S.a (I.step (.inv k i)) = S.a I := rfl
  have hj0 : (k ≠ S.p₁ ∨ S.a I ≠ none) → S.j₀ (I.step (.inv k i)) = S.j₀ I := by
    intro h
    simp only [Setup.j₀, hT, step_inv_snap]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases h with h | h
    · exact h (congrArg Prod.fst h1).symm
    · rw [S.began_of_a hwf h] at h2; simp at h2
  have hcd : (k ≠ S.p₁ ∨ S.a I ≠ none) →
      S.cs (I.step (.inv k i)) = S.cs I ∧ S.dlast (I.step (.inv k i)) = S.dlast I := by
    intro h
    exact S.cs_dlast_of_agree hT (hj0 h) (fun _ => rfl) le_rfl
      (fun j h1 h2 => by simp at h2; omega) (fun _ _ => rfl)
  have hpend : ∀ k', k' ≠ k → (I.step (.inv k i)).pend k' = I.pend k' := by
    intro k' hk'; simp [Function.update_of_ne hk']
  have hready : (k ≠ S.p₁ ∨ S.a I ≠ none) → (k = S.p₂ → i ≠ .tryC) →
      (S.Ready (I.step (.inv k i)) ↔ S.Ready I) := by
    intro h h2
    refine S.ready_congr ha (hcd h).2 ?_
    by_cases hk : k = S.p₂
    · subst hk; simp [hpk, h2 rfl]
    · rw [hpend _ (Ne.symm hk)]
  constructor
  · exact hg.p₁_uncommitted
  · intro k' h1 h2
    refine ⟨(hg.others k' h1 h2).1, ?_⟩
    by_cases hk : k' = k
    · subst hk; simp [hi, S.script_other h1 h2]
    · rw [hpend _ hk]; exact (hg.others k' h1 h2).2
  · exact hg.ops_shape
  · intro k' hb hp
    by_cases hk : k' = k
    · subst hk; simp at hp
    · rw [hpend _ hk] at hp
      have hb' : I.began (k', I.cnt k') = true := by
        simpa [step_inv_began, hk] using hb
      exact hg.idle_ops k' hb' hp
  · exact hg.committed_ops
  · intro b hb
    by_cases hk1 : k = S.p₁
    · subst hk1
      simp only [step_inv_pend, Function.update_self, Option.some.injEq, hT] at hb
      rcases S.script_cases I S.p₁ with h | ⟨-, hr, hl, h⟩ | ⟨-, hr, hl, h⟩ | ⟨h, -⟩
      · rw [hi, h] at hb
        have hb' : lastWrite S.x ((I.step (.inv S.p₁ i)).ops (S.T₁ I)) = some b := by
          simpa using hb
        obtain ⟨hr, hbc⟩ := hg.write_ready b (Or.inr hb')
        have h' : S.p₁ ≠ S.p₁ ∨ S.a I ≠ none := Or.inr (S.a_ne_none_of_ready hr)
        exact ⟨(hready h' (fun h => absurd h S.hp)).2 hr, (hcd h').1 ▸ hbc⟩
      · rw [hi, h] at hb
        have h' : S.p₁ ≠ S.p₁ ∨ S.a I ≠ none := Or.inr (S.a_ne_none_of_ready hr)
        have hbp : b = S.pick (S.cs I) := by
          rcases hb with hb | hb
          · simp at hb; exact hb.symm
          · simp [hl] at hb
        refine ⟨(hready h' (fun h => absurd h S.hp)).2 hr, ?_⟩
        rw [(hcd h').1, hbp]; exact S.pick_not_mem _
      · rw [hi, h] at hb
        have hb' : lastWrite S.x ((I.step (.inv S.p₁ i)).ops (S.T₁ I)) = some b := by
          simpa using hb
        have h' : S.p₁ ≠ S.p₁ ∨ S.a I ≠ none := Or.inr (S.a_ne_none_of_ready hr)
        obtain ⟨hr, hbc⟩ := hg.write_ready b (Or.inr hb')
        exact ⟨(hready h' (fun h => absurd h S.hp)).2 hr, (hcd h').1 ▸ hbc⟩
      · exact absurd h S.hp
    · rw [hpend _ (Ne.symm hk1), hT] at hb
      obtain ⟨hr, hbc⟩ := hg.write_ready b hb
      refine ⟨(hready (Or.inl hk1) ?_).2 hr, (hcd (Or.inl hk1)).1 ▸ hbc⟩
      rintro rfl htc
      rcases S.script_tryC (hi ▸ htc) with ⟨h, -⟩ | ⟨-, -, hnr⟩
      · exact hk1 h
      · exact hnr hr
  · intro htc
    by_cases hk1 : k = S.p₁
    · subst hk1
      simp only [step_inv_pend, Function.update_self, Option.some.injEq] at htc
      rcases S.script_tryC (hi ▸ htc) with ⟨-, -, hl⟩ | ⟨h, -⟩
      · exact hl
      · exact absurd h S.hp
    · rw [hpend _ (Ne.symm hk1)] at htc
      exact hg.tryC_wrote htc
  · intro k' i' h
    by_cases hk : k' = k
    · subst hk
      simp only [step_inv_pend, Function.update_self, Option.some.injEq] at h
      subst h
      rcases S.script_cases I k' with h | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, a, -, h | h⟩ <;>
        rw [hi, h] <;> simp
    · rw [hpend _ hk] at h; exact hg.pend_x k' i' h
  · intro k' i' h hne
    by_cases hk : k' = k
    · subst hk
      simp only [step_inv_pend, Function.update_self, Option.some.injEq] at h
      subst h
      show I.ops (k', I.cnt k') ≠ []
      rcases S.script_cases I k' with h | ⟨rfl, hr, -, h⟩ | ⟨rfl, -, hl, h⟩ | ⟨rfl, hb, -, a, -, h | h⟩ <;>
        rw [hi, h] at hne
      · exact absurd rfl hne
      · exact S.ops_ne_nil_of_a (S.a_ne_none_of_ready hr)
      · exact ne_nil_of_lastWrite hl
      · exact hg.idle_ops _ hb hpk
      · exact hg.idle_ops _ hb hpk
    · rw [hpend _ hk] at h; exact hg.pend_ops k' i' h hne

theorem hpx_cases {I : HInfo P X V} (hg : S.Good I) {k : P} {i : Inv X V}
    (h : I.pend k = some i) : i = .read S.x ∨ (∃ v, i = .write S.x v) ∨ i = .tryC :=
  hg.pend_x k i h

omit [DecidableEq X] [DecidableEq V] in
theorem step_res_cnt_ne {I : HInfo P X V} {k k' : P} {i : Inv X V} {r : Res V} (h : k' ≠ k) :
    (I.step (.res k i r)).cnt k' = I.cnt k' := by
  simp only [step_res_cnt]; split_ifs <;> simp [Function.update_of_ne h]

omit [DecidableEq X] [DecidableEq V] in
theorem step_res_cnt_self {I : HInfo P X V} {k : P} {i : Inv X V} {r : Res V} :
    (I.step (.res k i r)).cnt k = if r.isEnd then I.cnt k + 1 else I.cnt k := by
  simp only [step_res_cnt]; split_ifs <;> simp

omit [DecidableEq P] [DecidableEq X] [DecidableEq V] in
theorem opOf_eq_write {i : Inv X V} {r : Res V} {y : X} {v : V}
    (h : opOf i r = some (.write y v)) : i = .write y v := by
  cases i <;> cases r <;> simp_all [opOf]

omit [DecidableEq P] in
theorem lastWrite_append_opOf_read {x : X} {i : Inv X V} {r : Res V} {o : Op X V}
    (h : opOf i r = some o) (hw : ∀ y v, o ≠ .write y v) (l : List (Op X V)) :
    lastWrite x (l ++ [o]) = lastWrite x l := by
  cases o with
  | read y v => simp
  | write y v => exact absurd rfl (hw y v)

omit [DecidableEq X] [DecidableEq V] in
theorem opOf_some_of_fits {i : Inv X V} {r : Res V} (hf : r.Fits i) (hr : r.isEnd = false) :
    ∃ o, opOf i r = some o := by
  cases i <;> rcases hf with rfl | h <;> simp_all [Res.isEnd, opOf]
  · obtain ⟨v, rfl⟩ := h; simp [opOf]

theorem good_step_res {I : HInfo P X V} (hwf : WF I) (hg : S.Good I) {k : P} {i : Inv X V}
    {r : Res V} (hpk : I.pend k = some i) (hf : r.Fits i) (hnc : k = S.p₁ → r ≠ .commit) :
    S.Good (I.step (.res k i r)) := by
  set J := I.step (.res k i r) with hJ
  have hops : ∀ t, J.ops t = I.ops t ++ (if t = (k, I.cnt k) then (opOf i r).toList else []) := by
    intro t; simp only [hJ, step_res_ops]; split_ifs <;> simp
  have hpend : ∀ k', k' ≠ k → J.pend k' = I.pend k' := by
    intro k' hk'; simp [hJ, Function.update_of_ne hk']
  have hcommit : r = .commit → i = .tryC := by
    rintro rfl; cases i <;> simp_all [Res.Fits]
  have hcom : ∀ t, J.committed t = true ↔ I.committed t = true ∨ (t = (k, I.cnt k) ∧ r = .commit) := by
    intro t; cases r <;> simp [hJ, Res.isCommit]
  have hnotcom : ∀ j, I.committed (k, I.cnt k + j) = false := fun j => by
    by_contra h
    have := (hwf.committed_began _ (by simpa using h)).2
    simp at this
  -- the shape of the current transaction of `k` is preserved
  have hshape_k : J.ops (k, I.cnt k) = [] ∨ ∃ c r, J.ops (k, I.cnt k) = .read S.x c :: r := by
    rw [hops, if_pos rfl]
    rcases hopr : opOf i r with _ | o
    · simpa using hg.ops_shape (k, I.cnt k)
    · simp only [Option.toList_some]
      rcases hg.ops_shape (k, I.cnt k) with h0 | ⟨c, l, hl⟩
      · rw [h0]
        rcases S.hpx_cases hg hpk with rfl | ⟨v, rfl⟩ | rfl
        · cases r <;> simp_all [opOf] <;> exact ⟨_, hopr.symm⟩
        · exfalso
          exact hg.pend_ops k _ hpk (by simp) h0
        · cases r <;> simp_all [opOf]
      · exact Or.inr ⟨c, l ++ [o], by simp [hl]⟩
  have hne_ops : ∀ t, I.ops t ≠ [] → J.ops t ≠ [] := by
    intro t ht; rw [hops]; simp [ht]
  constructor
  · intro j
    by_contra h
    rcases (hcom _).1 (by simpa using h) with h' | ⟨h', hr⟩
    · simp [hg.p₁_uncommitted j] at h'
    · exact hnc (congrArg Prod.fst h').symm hr
  · intro k' h1 h2
    refine ⟨fun j => ?_, ?_⟩
    · by_contra h
      rcases (hcom _).1 (by simpa using h) with h' | ⟨h', hr⟩
      · simp [(hg.others k' h1 h2).1 j] at h'
      · have hkk : k' = k := congrArg Prod.fst h'
        subst hkk
        exact (hg.others k' h1 h2).2 (hpk.trans (by rw [hcommit hr]))
    · by_cases hk : k' = k
      · subst hk; simp [hJ]
      · rw [hpend _ hk]; exact (hg.others k' h1 h2).2
  · intro t
    by_cases ht : t = (k, I.cnt k)
    · subst ht; exact hshape_k
    · rw [hops, if_neg ht, List.append_nil]; exact hg.ops_shape t
  · intro k' hb hp
    by_cases hk : k' = k
    · subst hk
      by_cases hend : r.isEnd = true
      · have hc : J.cnt k' = I.cnt k' + 1 := by simp [hJ, step_res_cnt_self, hend]
        rw [hc] at hb
        have := (hwf.future (k', I.cnt k' + 1) (by simp)).1
        simp [hJ, this] at hb
      · have hc : J.cnt k' = I.cnt k' := by simp [hJ, step_res_cnt_self, hend]
        rw [hc, hops, if_pos rfl]
        obtain ⟨o, ho⟩ := opOf_some_of_fits hf (by simpa using hend)
        simp [ho]
    · have hc : J.cnt k' = I.cnt k' := step_res_cnt_ne hk
      rw [hc] at hb ⊢
      rw [hpend _ hk] at hp
      have hne : ((k', I.cnt k') : TxId P) ≠ (k, I.cnt k) := by simp [hk]
      rw [hops, if_neg hne, List.append_nil]
      exact hg.idle_ops k' (by simpa [hJ] using hb) hp
  · intro j hj
    rcases (hcom _).1 hj with h' | ⟨h', hr⟩
    · exact hne_ops _ (hg.committed_ops j h')
    · apply hne_ops
      rw [h']
      exact hg.pend_ops k _ hpk (by rw [hcommit hr]; simp)
  · -- `write_ready`
    intro b hb
    by_cases hk1 : k = S.p₁
    · subst hk1
      by_cases hend : r.isEnd = true
      · exfalso
        have hT : S.T₁ J = (S.p₁, I.cnt S.p₁ + 1) := by
          simp [Setup.T₁, hJ, step_res_cnt_self, hend]
        have hne : ((S.p₁, I.cnt S.p₁ + 1) : TxId P) ≠ (S.p₁, I.cnt S.p₁) := by simp
        rw [hT, hops, if_neg hne, List.append_nil,
          (hwf.future (S.p₁, I.cnt S.p₁ + 1) (by simp)).2.1] at hb
        simp [hJ, lastWrite] at hb
      · have hcnt : J.cnt = I.cnt := by
          funext k'
          by_cases hk : k' = S.p₁
          · subst hk; simp [hJ, step_res_cnt_self, hend]
          · exact step_res_cnt_ne hk
        have hT : S.T₁ J = S.T₁ I := by simp [Setup.T₁, hcnt]
        have hcm : J.committed = I.committed := by
          funext t
          have : r.isCommit = false := by cases r <;> simp_all [Res.isEnd, Res.isCommit]
          simp [hJ, this]
        have hcd := S.cs_dlast_of_agree hT rfl (fun j => by rw [hcm]) (by rw [hcnt])
          (fun j h1 h2 => by rw [hcnt] at h2; omega)
          (fun j _ => by rw [hops, if_neg (by simp [Ne.symm S.hp]), List.append_nil])
        have hp2 : J.pend S.p₂ = I.pend S.p₂ := hpend _ (Ne.symm S.hp)
        have hb' : lastWrite S.x (J.ops (S.T₁ I)) = some b := by
          rcases hb with hb | hb
          · simp [hJ] at hb
          · rwa [hT] at hb
        have hT' : S.T₁ I = (S.p₁, I.cnt S.p₁) := rfl
        rw [hops, hT', if_pos rfl] at hb'
        obtain ⟨o, ho⟩ := opOf_some_of_fits hf (by simpa using hend)
        rw [ho, Option.toList_some] at hb'
        -- `a` is unchanged once `T₁` has an operation
        have haJ : I.ops (S.T₁ I) ≠ [] → S.a J = S.a I := by
          intro hne
          simp only [Setup.a, hT, hops, hT', if_pos rfl]
          exact firstRead_append hne _
        by_cases hw : ∃ y v, o = .write y v
        · obtain ⟨y, v, rfl⟩ := hw
          have hi' := opOf_eq_write ho
          subst hi'
          rcases hg.pend_x _ _ hpk with h | ⟨v', h⟩ | h <;> simp only [reduceCtorEq,
            Inv.write.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp only [lastWrite_append_write, Option.some.injEq] at hb'
          subst hb'
          obtain ⟨hr, hbc⟩ := hg.write_ready _ (Or.inl hpk)
          have hne : I.ops (S.T₁ I) ≠ [] := hg.pend_ops _ _ hpk (by simp)
          exact ⟨(S.ready_congr (haJ hne) hcd.2 (by rw [hp2])).2 hr, hcd.1.symm ▸ hbc⟩
        · push Not at hw
          rw [lastWrite_append_opOf_read ho hw] at hb'
          obtain ⟨hr, hbc⟩ := hg.write_ready _ (Or.inr hb')
          have hne : I.ops (S.T₁ I) ≠ [] := S.ops_ne_nil_of_a (S.a_ne_none_of_ready hr)
          exact ⟨(S.ready_congr (haJ hne) hcd.2 (by rw [hp2])).2 hr, hcd.1.symm ▸ hbc⟩
    · -- `k ≠ p₁`: the side of `p₁` is unchanged
      have hT : S.T₁ J = S.T₁ I := by simp [Setup.T₁, hJ, step_res_cnt_ne (Ne.symm hk1)]
      have hopsT : J.ops (S.T₁ I) = I.ops (S.T₁ I) := by
        rw [hops, if_neg (by simp [Setup.T₁, Ne.symm hk1]), List.append_nil]
      have haJ : S.a J = S.a I := by simp only [Setup.a, hT, hopsT]
      have hb' : I.pend S.p₁ = some (.write S.x b) ∨ lastWrite S.x (I.ops (S.T₁ I)) = some b := by
        rwa [hpend _ (Ne.symm hk1), hT, hopsT] at hb
      obtain ⟨hr, hbc⟩ := hg.write_ready b hb'
      obtain ⟨a, d, ha, hd, hda, hp2⟩ := hr
      have hrc : r ≠ .commit := by
        intro hrc
        by_cases hk2 : k = S.p₂
        · subst hk2; exact hp2 (hpk.trans (by rw [hcommit hrc]))
        · exact (hg.others k hk1 hk2).2 (hpk.trans (by rw [hcommit hrc]))
      have hcmJ : ∀ t, J.committed t = I.committed t := by
        intro t
        have : r.isCommit = false := by cases r <;> simp_all [Res.isCommit]
        simp [hJ, this]
      have hcd : S.cs J = S.cs I ∧ S.dlast J = S.dlast I := by
        by_cases hk2 : k = S.p₂
        · subst hk2
          have hc0 := hnotcom 0
          simp only [Nat.add_zero] at hc0
          have hcJ : J.cnt S.p₂ = if r.isEnd then I.cnt S.p₂ + 1 else I.cnt S.p₂ :=
            step_res_cnt_self
          exact S.cs_dlast_of_agree hT rfl (fun j => hcmJ _) (by rw [hcJ]; split_ifs <;> omega)
            (fun j h1 h2 => by
              rw [hcJ] at h2
              have : j = I.cnt S.p₂ := by split_ifs at h2 <;> omega
              rw [this, hc0])
            (fun j hj => by rw [hops, if_neg (by simp; omega), List.append_nil])
        · exact S.cs_dlast_of_agree hT rfl (fun j => hcmJ _)
            (by rw [step_res_cnt_ne (Ne.symm hk2)])
            (fun j h1 h2 => by rw [step_res_cnt_ne (Ne.symm hk2)] at h2; omega)
            (fun j _ => by rw [hops, if_neg (by simp [Ne.symm hk2]), List.append_nil])
      refine ⟨⟨a, d, haJ ▸ ha, hcd.2 ▸ hd, hda, ?_⟩, hcd.1.symm ▸ hbc⟩
      by_cases hk2 : k = S.p₂
      · subst hk2; simp [hJ]
      · rwa [hpend _ (Ne.symm hk2)]
  · -- `tryC_wrote`
    intro htc
    by_cases hk1 : k = S.p₁
    · subst hk1; simp [hJ] at htc
    · have hT : S.T₁ J = S.T₁ I := by simp [Setup.T₁, hJ, step_res_cnt_ne (Ne.symm hk1)]
      have hopsT : J.ops (S.T₁ I) = I.ops (S.T₁ I) := by
        rw [hops, if_neg (by simp [Setup.T₁, Ne.symm hk1]), List.append_nil]
      rw [hT, hopsT]
      exact hg.tryC_wrote (by rwa [hpend _ (Ne.symm hk1)] at htc)
  · intro k' i' h
    by_cases hk : k' = k
    · subst hk; simp [hJ] at h
    · rw [hpend _ hk] at h; exact hg.pend_x k' i' h
  · intro k' i' h hne
    by_cases hk : k' = k
    · subst hk; simp [hJ] at h
    · rw [hpend _ hk] at h
      rw [step_res_cnt_ne hk, hops, if_neg (by simp [hk]), List.append_nil]
      exact hg.pend_ops k' i' h hne

/-! ### The last commit of `p₁` is impossible -/

/-- If `p₁` has a pending commit request in a history satisfying the invariant, a commit event for
`p₁` would make the history not serializable. -/
theorem not_serializable_commit {init : X → V} {h : List (Ev P X V)} (hwf : WF (info h))
    (hg : S.Good (info h)) (hpk : (info h).pend S.p₁ = some .tryC) :
    ¬ Serializable init (h ++ [.res S.p₁ .tryC .commit]) := by
  set I := info h with hI
  have hJ : info (h ++ [.res S.p₁ .tryC .commit]) = I.step (.res S.p₁ .tryC .commit) := by
    simp [hI]
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hg.tryC_wrote hpk)
  obtain ⟨⟨a, d, ha, hd, hda, hp2⟩, hbc⟩ := hg.write_ready b (Or.inr hb)
  obtain ⟨jₗ, hjl, hdj⟩ := Option.bind_eq_some_iff.1 hd
  have hjlm := S.mem_chain.1 (List.mem_of_getLast? hjl)
  have hopsJ : ∀ t, txOps (h ++ [.res S.p₁ .tryC .commit]) t = I.ops t := by
    intro t; simp only [txOps, hJ, step_res_ops]; split_ifs <;> simp [opOf]
  have hcomJ : ∀ t, Committed (h ++ [.res S.p₁ .tryC .commit]) t ↔
      I.committed t = true ∨ t = (S.p₁, I.cnt S.p₁) := by
    intro t; simp [Committed, hJ, Res.isCommit]
  have hc₂ : ∀ j, Committed (h ++ [.res S.p₁ .tryC .commit]) (S.p₂, j) →
      I.committed (S.p₂, j) = true := by
    intro j hc
    rcases (hcomJ _).1 hc with h | h
    · exact h
    · exact absurd (congrArg Prod.fst h) (Ne.symm S.hp)
  refine not_serializable_of_conflict S.x S.hp (c₁ := I.cnt S.p₁) (jₗ := jₗ)
    (a := a) (b := b) (d := d) ((hcomJ _).2 (Or.inr rfl))
    ?_ (by rw [hopsJ]; exact hb) ?_ ?_ ?_ ((hcomJ _).2 (Or.inl hjlm.2.2)) ?_
    (by rw [hopsJ]; exact hdj) hda
  · rw [hopsJ]
    exact eq_read_of_firstRead (hg.ops_shape _) ha
  · rintro ⟨k, j⟩ ht
    rcases (hcomJ _).1 ht with ht | ht
    · by_cases h1 : k = S.p₁
      · subst h1; simp [hg.p₁_uncommitted j] at ht
      · by_cases h2 : k = S.p₂
        · exact Or.inr h2
        · simp [(hg.others k h1 h2).1 j] at ht
    · exact Or.inl ht
  · rintro ⟨k, j⟩ ⟨-, hpt⟩
    simp only [hJ, step_res_pend] at hpt
    by_cases h1 : k = S.p₁
    · subst h1; simp at hpt
    · rw [Function.update_of_ne h1] at hpt
      by_cases h2 : k = S.p₂
      · subst h2; exact hp2 hpt
      · exact (hg.others k h1 h2).2 hpt
  · intro j hc
    have hc' := hc₂ j hc
    rw [hopsJ]
    obtain ⟨c, r, hcr⟩ := (hg.ops_shape (S.p₂, j)).resolve_left (hg.committed_ops j hc')
    refine ⟨c, r, hcr, ?_⟩
    rintro rfl
    apply hbc
    have hjc : j ∈ S.allc I := S.mem_allc.2 ⟨(hwf.committed_began _ hc').2, hc'⟩
    exact List.mem_filterMap.2 ⟨j, hjc, by simp [hcr, firstRead]⟩
  · intro j hc
    have hc' := hc₂ j hc
    by_cases hj : S.j₀ I ≤ j
    · exact le_of_mem_getLast (S.chain_pairwise I) hjl j
        (S.mem_chain.2 ⟨(hwf.committed_began _ hc').2, hj, hc'⟩)
    · have := hjlm.2.1; omega

/-! ### How `Ready` evolves -/

/-- `Ready` persists as long as `T₁` goes on. -/
theorem ready_step {I : HInfo P X V} (hwf : WF I) (hg : S.Good I) {e : Ev P X V}
    (he : S.StratEv I e) (hend : ∀ i r, e = .res S.p₁ i r → r.isEnd = false) (hr : S.Ready I) :
    S.Ready (I.step e) := by
  have haI := S.a_ne_none_of_ready hr
  obtain ⟨a, d, ha, hd, hda, hp2⟩ := hr
  cases e with
  | inv k i =>
    obtain ⟨hpk, hi⟩ := he
    have hT : S.T₁ (I.step (.inv k i)) = S.T₁ I := rfl
    have hsn : (I.step (.inv k i)).snap (S.T₁ I) S.p₂ = I.snap (S.T₁ I) S.p₂ := by
      simp [S.began_of_a hwf haI]
    have hcd := S.cs_dlast_of_agree hT hsn (fun _ => rfl) le_rfl (fun j h1 h2 => by simp at h2; omega)
      (fun _ _ => rfl)
    refine ⟨a, d, (S.a_of_agree hT (Or.inl rfl)).trans ha, hcd.2.trans hd, hda, ?_⟩
    by_cases hk : k = S.p₂
    · subst hk
      simp only [step_inv_pend, Function.update_self, ne_eq, Option.some.injEq]
      rintro rfl
      rcases S.script_tryC hi.symm with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact S.hp h.symm
      · exact h ⟨a, d, ha, hd, hda, hp2⟩
    · simpa [Function.update_of_ne (Ne.symm hk)] using hp2
  | res k i r =>
    obtain ⟨hpk, hf⟩ := he
    have hops : ∀ t, (I.step (.res k i r)).ops t =
        I.ops t ++ (if t = (k, I.cnt k) then (opOf i r).toList else []) := by
      intro t; simp only [step_res_ops]; split_ifs <;> simp
    by_cases hk1 : k = S.p₁
    · subst hk1
      have hne := hend i r rfl
      have hcnt : (I.step (.res S.p₁ i r)).cnt = I.cnt := by
        funext k'
        by_cases hk : k' = S.p₁
        · subst hk; simp [step_res_cnt_self, hne]
        · exact step_res_cnt_ne hk
      have hT : S.T₁ (I.step (.res S.p₁ i r)) = S.T₁ I := by simp [Setup.T₁, hcnt]
      have hcm : ∀ t, (I.step (.res S.p₁ i r)).committed t = I.committed t := by
        intro t
        have : r.isCommit = false := by cases r <;> simp_all [Res.isEnd, Res.isCommit]
        simp [this]
      have hcd := S.cs_dlast_of_agree hT rfl (fun _ => hcm _) (by rw [hcnt])
        (fun j h1 h2 => by rw [hcnt] at h2; omega)
        (fun j _ => by rw [hops, if_neg (by simp [Ne.symm S.hp]), List.append_nil])
      have haJ := S.a_of_agree hT (Or.inr ⟨S.ops_ne_nil_of_a haI, _, hops _⟩)
      refine ⟨a, d, haJ.trans ha, hcd.2.trans hd, hda, ?_⟩
      simpa [Function.update_of_ne (Ne.symm S.hp)] using hp2
    · have hT : S.T₁ (I.step (.res k i r)) = S.T₁ I := by
        simp [Setup.T₁, step_res_cnt_ne (Ne.symm hk1)]
      have hopsT : (I.step (.res k i r)).ops (S.T₁ I) = I.ops (S.T₁ I) := by
        rw [hops, if_neg (by simp [Setup.T₁, Ne.symm hk1]), List.append_nil]
      have haJ := S.a_of_agree hT (Or.inl hopsT)
      by_cases hk2 : k = S.p₂
      · subst hk2
        have hrc : r.isCommit = false := by
          cases r <;> simp [Res.isCommit]
          have : i = .tryC := by cases i <;> simp_all [Res.Fits]
          exact hp2 (hpk.trans (by rw [this]))
        have hc0 : I.committed (S.p₂, I.cnt S.p₂) = false := by
          by_contra h
          have := (hwf.committed_began _ (by simpa using h)).2
          simp at this
        have hcd := S.cs_dlast_of_agree hT rfl (fun j => by simp [hrc])
          (by rw [step_res_cnt_self]; split_ifs <;> omega)
          (fun j h1 h2 => by
            rw [step_res_cnt_self] at h2
            have : j = I.cnt S.p₂ := by split_ifs at h2 <;> omega
            rw [this, hc0])
          (fun j hj => by rw [hops, if_neg (by simp; omega), List.append_nil])
        exact ⟨a, d, haJ.trans ha, hcd.2.trans hd, hda, by simp⟩
      · have hcd := S.cs_dlast_of_agree hT rfl
          (fun j => by simp [Ne.symm hk2])
          (by rw [step_res_cnt_ne (Ne.symm hk2)])
          (fun j h1 h2 => by rw [step_res_cnt_ne (Ne.symm hk2)] at h2; omega)
          (fun j _ => by rw [hops, if_neg (by simp [Ne.symm hk2]), List.append_nil])
        refine ⟨a, d, haJ.trans ha, hcd.2.trans hd, hda, ?_⟩
        simpa [Function.update_of_ne (Ne.symm hk2)] using hp2

/-- Events of `p₂` other than responses to `tryC` neither change `a` nor `Ready`. -/
theorem ready_step_p₂ {I : HInfo P X V} (hwf : WF I) {e : Ev P X V}
    (hp : e.proc = S.p₂) (he : ValidEv I e) (hp2 : I.pend S.p₂ ≠ some .tryC)
    (hp2' : (I.step e).pend S.p₂ ≠ some .tryC) (hf : ∀ i r, e = .res S.p₂ i r → r.Fits i) :
    S.a (I.step e) = S.a I ∧ (S.Ready (I.step e) ↔ S.Ready I) := by
  cases e with
  | inv k i =>
    simp only [Ev.proc] at hp
    subst hp
    have hT : S.T₁ (I.step (.inv S.p₂ i)) = S.T₁ I := rfl
    have hsn : (I.step (.inv S.p₂ i)).snap (S.T₁ I) S.p₂ = I.snap (S.T₁ I) S.p₂ := by
      simp [Setup.T₁, S.hp]
    have hcd := S.cs_dlast_of_agree hT hsn (fun _ => rfl) le_rfl (fun j h1 h2 => by simp at h2; omega)
      (fun _ _ => rfl)
    have haJ := S.a_of_agree hT (Or.inl rfl)
    refine ⟨haJ, ?_⟩
    simp only [Setup.Ready, haJ, hcd.2]
    constructor
    · rintro ⟨a, d, h1, h2, h3, -⟩; exact ⟨a, d, h1, h2, h3, hp2⟩
    · rintro ⟨a, d, h1, h2, h3, -⟩; exact ⟨a, d, h1, h2, h3, hp2'⟩
  | res k i r =>
    simp only [Ev.proc] at hp
    subst hp
    have hpk : I.pend S.p₂ = some i := he
    have hops : ∀ t, (I.step (.res S.p₂ i r)).ops t =
        I.ops t ++ (if t = (S.p₂, I.cnt S.p₂) then (opOf i r).toList else []) := by
      intro t; simp only [step_res_ops]; split_ifs <;> simp
    have hT : S.T₁ (I.step (.res S.p₂ i r)) = S.T₁ I := by
      simp [Setup.T₁, step_res_cnt_ne S.hp]
    have hopsT : (I.step (.res S.p₂ i r)).ops (S.T₁ I) = I.ops (S.T₁ I) := by
      rw [hops, if_neg (by simp [Setup.T₁, S.hp]), List.append_nil]
    have haJ := S.a_of_agree hT (Or.inl hopsT)
    have hrc : r.isCommit = false := by
      have hfi := hf i r rfl
      cases r <;> simp [Res.isCommit]
      have : i = .tryC := by cases i <;> simp_all [Res.Fits]
      exact hp2 (hpk.trans (by rw [this]))
    have hc0 : I.committed (S.p₂, I.cnt S.p₂) = false := by
      by_contra h
      have := (hwf.committed_began _ (by simpa using h)).2
      simp at this
    have hcd := S.cs_dlast_of_agree hT rfl (fun j => by simp [hrc])
      (by rw [step_res_cnt_self]; split_ifs <;> omega)
      (fun j h1 h2 => by
        rw [step_res_cnt_self] at h2
        have : j = I.cnt S.p₂ := by split_ifs at h2 <;> omega
        rw [this, hc0])
      (fun j hj => by rw [hops, if_neg (by simp; omega), List.append_nil])
    refine ⟨haJ, ?_⟩
    simp only [Setup.Ready, haJ, hcd.2]
    constructor
    · rintro ⟨a, d, h1, h2, h3, -⟩; exact ⟨a, d, h1, h2, h3, hp2⟩
    · rintro ⟨a, d, h1, h2, h3, -⟩; exact ⟨a, d, h1, h2, h3, hp2'⟩

theorem good_init : S.Good (HInfo.init : HInfo P X V) where
  p₁_uncommitted := by simp [HInfo.init]
  others := by simp [HInfo.init]
  ops_shape := by simp [HInfo.init]
  idle_ops := by simp [HInfo.init]
  committed_ops := by simp [HInfo.init]
  write_ready := by simp [HInfo.init, lastWrite]
  tryC_wrote := by simp [HInfo.init]
  pend_x := by simp [HInfo.init]
  pend_ops := by simp [HInfo.init]

end Setup

/-! ### Runs of the strategy -/

/-- A choice of the TM's step (the TM is nondeterministic; any resolution will do). -/
noncomputable def TM.choice (M : TM P X V) (h : List (Step P X V)) (k : P) : Option (Res V) :=
  (M.next_nonempty h k).some

/-- The next step of the run: the scheduled process invokes its scripted operation if idle;
otherwise the TM takes a step for it. -/
noncomputable def stratStep (M : TM P X V) (S : Setup P X V) (sched : List (Step P X V) → P)
    (h : List (Step P X V)) : Step P X V :=
  match pending h (sched h) with
  | none => .ev (.inv (sched h) (S.script (info (hist h)) (sched h)))
  | some i =>
    match M.choice h (sched h) with
    | some r => .ev (.res (sched h) i r)
    | none => .tau (sched h)

/-- The first `t` steps of the run. -/
noncomputable def stratPre (M : TM P X V) (S : Setup P X V) (sched : List (Step P X V) → P) :
    ℕ → List (Step P X V)
  | 0 => []
  | t + 1 => stratPre M S sched t ++ [stratStep M S sched (stratPre M S sched t)]

/-- The run of the strategy against `M` under the scheduler `sched`. -/
noncomputable def stratRun (M : TM P X V) (S : Setup P X V) (sched : List (Step P X V) → P)
    (t : ℕ) : Step P X V :=
  stratStep M S sched (stratPre M S sched t)

variable {M : TM P X V} {S : Setup P X V} {sched : List (Step P X V) → P}

theorem prefixOf_stratRun (t : ℕ) : prefixOf (stratRun M S sched) t = stratPre M S sched t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [prefixOf, stratPre, ih, stratRun]

theorem stratStep_cases (h : List (Step P X V)) :
    (pending h (sched h) = none ∧
      stratStep M S sched h = .ev (.inv (sched h) (S.script (info (hist h)) (sched h)))) ∨
    (∃ i r, pending h (sched h) = some i ∧ some r ∈ M.next h (sched h) ∧
      stratStep M S sched h = .ev (.res (sched h) i r)) ∨
    (∃ i, pending h (sched h) = some i ∧ none ∈ M.next h (sched h) ∧
      stratStep M S sched h = .tau (sched h)) := by
  unfold stratStep
  cases hp : pending h (sched h) with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some i =>
    have hc : M.choice h (sched h) ∈ M.next h (sched h) := (M.next_nonempty h (sched h)).some_mem
    cases hr : M.choice h (sched h) with
    | none => exact Or.inr (Or.inr ⟨i, rfl, hr ▸ hc, rfl⟩)
    | some r => exact Or.inr (Or.inl ⟨i, r, rfl, hr ▸ hc, rfl⟩)

theorem stratStep_valid (h : List (Step P X V)) : ValidStep M h (stratStep M S sched h) := by
  rcases stratStep_cases (M := M) (S := S) (sched := sched) h with ⟨hp, he⟩ | ⟨i, r, hp, hr, he⟩ |
    ⟨i, hp, hr, he⟩ <;> rw [he]
  · exact hp
  · exact ⟨hp, hr⟩
  · exact ⟨by simp [hp], hr⟩

theorem isExec_stratRun : IsExec M (stratRun M S sched) := by
  intro t; rw [prefixOf_stratRun]; exact stratStep_valid _

theorem reachable_stratPre (t : ℕ) : Reachable M (stratPre M S sched t) := by
  induction t with
  | zero => exact .nil
  | succ t ih => exact .snoc ih (stratStep_valid _)

/-- A step of the run that would return a commit event to `p₁` is impossible. -/
theorem stratRun_ne_commit_of_good (hM : EnsuresSafety M (Serializable init)) {t : ℕ}
    (hwf : WF (info (hist (stratPre M S sched t)))) (hg : S.Good (info (hist (stratPre M S sched t))))
    (i : Inv X V) : stratRun M S sched t ≠ .ev (.res S.p₁ i .commit) := by
  intro he
  have hv := stratStep_valid (M := M) (S := S) (sched := sched) (stratPre M S sched t)
  rw [show stratStep M S sched (stratPre M S sched t) = stratRun M S sched t from rfl, he] at hv
  have hf : Res.commit.Fits i := M.next_fits _ _ _ _ hv.1 hv.2
  have hi : i = .tryC := by cases i <;> simp_all [Res.Fits]
  subst hi
  have hss := hM _ (reachable_stratPre (M := M) (S := S) (sched := sched) (t + 1))
  simp only [stratPre, show stratStep M S sched (stratPre M S sched t) = stratRun M S sched t
    from rfl, he, hist_append_ev] at hss
  exact S.not_serializable_commit hwf hg hv.1 hss

/-- Along a run against a serializable TM, the invariant holds. -/
theorem good_stratPre (hM : EnsuresSafety M (Serializable init)) (t : ℕ) :
    WF (info (hist (stratPre M S sched t))) ∧ S.Good (info (hist (stratPre M S sched t))) := by
  induction t with
  | zero => exact ⟨WF.init, S.good_init⟩
  | succ t ih =>
    obtain ⟨hwf, hg⟩ := ih
    have hnc := stratRun_ne_commit_of_good hM hwf hg
    simp only [stratPre]
    have hrun : stratStep M S sched (stratPre M S sched t) = stratRun M S sched t := rfl
    rw [hrun]
    rw [← hrun]
    rcases stratStep_cases (M := M) (S := S) (sched := sched) (stratPre M S sched t) with
      ⟨hp, he⟩ | ⟨i, r, hp, hr, he⟩ | ⟨i, hp, -, he⟩ <;> rw [he]
    · have hv : ValidEv (info (hist (stratPre M S sched t)))
          (.inv (sched (stratPre M S sched t))
            (S.script (info (hist (stratPre M S sched t))) (sched (stratPre M S sched t)))) := hp
      simp only [hist_append_ev, info_append_single]
      exact ⟨hwf.step hv, S.good_step_inv hwf hg hp rfl⟩
    · have hf : r.Fits i := M.next_fits _ _ _ _ hp hr
      have hv : ValidEv (info (hist (stratPre M S sched t))) (.res _ i r) := hp
      simp only [hist_append_ev, info_append_single]
      refine ⟨hwf.step hv, S.good_step_res hwf hg hp hf ?_⟩
      rintro hk rfl
      exact hnc i (by rw [← hrun, he, hk])
    · simpa using ⟨hwf, hg⟩

/-- **`p₁` never commits** (the paper's "Algorithm 1 never terminates"), under any scheduler. -/
theorem stratRun_ne_commit₁ (hM : EnsuresSafety M (Serializable init)) (t : ℕ)
    (i : Inv X V) : stratRun M S sched t ≠ .ev (.res S.p₁ i .commit) :=
  have h := good_stratPre (sched := sched) (S := S) hM t
  stratRun_ne_commit_of_good hM h.1 h.2 i

/-- The other processes never invoke `tryC`, so they never commit either. -/
theorem stratRun_ne_commit_other (hM : EnsuresSafety M (Serializable init)) (t : ℕ)
    {k : P} (h1 : k ≠ S.p₁) (h2 : k ≠ S.p₂) (i : Inv X V) :
    stratRun M S sched t ≠ .ev (.res k i .commit) := by
  intro he
  obtain ⟨-, hg⟩ := good_stratPre (sched := sched) (S := S) hM t
  have hv := stratStep_valid (M := M) (S := S) (sched := sched) (stratPre M S sched t)
  rw [show stratStep M S sched (stratPre M S sched t) = stratRun M S sched t from rfl, he] at hv
  have hf : Res.commit.Fits i := M.next_fits _ _ _ _ hv.1 hv.2
  have hi : i = .tryC := by cases i <;> simp_all [Res.Fits]
  subst hi
  exact (hg.others k h1 h2).2 hv.1

end Podc.TMLiveness