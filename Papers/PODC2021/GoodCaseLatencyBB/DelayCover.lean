import Papers.PODC2021.GoodCaseLatencyBB.Tokens

/-!
# Covering systems with uniform message delay

A time-dependent generalization of CSLib's `Cslib.Byzantine.PartialSync.CoverSystem` (FLM.lean),
for **synchronous runs in which every batch has the same delay**. A `DCover P Q V` is a network of
*nodes* `x : Q`; node `x` runs the code of process `proc x` with proposal `inp x`, and at every
time `σ` it listens, as messages from sender `q`, to what node `nbr σ x q` sends at time `σ`
(nothing if `nbr σ x q = none`). With delivery offset `e` (a batch sent at `σ` is delivered at
`σ + e`, i.e. it is visible in the state at time `σ + e + 1`: *effective delay* `e + 1`), the
node states `DCover.st A e C τ x` are computed independently of any run.

* `DCover.run`: the run in which every faulty process `q` sends to `p` what node
  `nbr σ (lift p) q` sends, all batches delivered with offset `e`.
* `DCover.st_run` (covering lemma): if `lift` is compatible with `nbr` on correct processes, the
  correct processes have the states of their lifts.
* `DCover.st_eq_of_level` (locality): two systems that agree near a node have the same states at
  that node for a while; the "distance" is measured by a level function, one level per message
  delay.
* `DCover.token_origin`, `DCover.run_authValid`: with unforgeable signatures, every token emitted
  by a node was first emitted by a node of its signer; hence the covering run respects
  unforgeability if every correct process has a unique node (in a part of the system closed under
  `nbr`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

-- CSLib candidate
/-- A covering system with time-dependent neighbourhoods: node `x` runs the code of `proc x` with
proposal `inp x` and receives, as the messages sent by `q` at time `σ`, what node `nbr σ x q`
sends at time `σ` (nothing for `none`). -/
structure DCover (P Q V : Type*) where
  /-- The process whose code node `x` runs. -/
  proc : Q → P
  /-- The proposal of node `x`. -/
  inp : Q → V
  /-- `nbr σ x q`: the node whose messages sent at time `σ` node `x` receives as messages from
  `q`. -/
  nbr : ℕ → Q → P → Option Q

namespace DCover

variable {P Q M S V K : Type*} (A : Algorithm P M S V V) (e : ℕ) (C : DCover P Q V)

/-- The states of the nodes of a covering system, when every batch sent at `σ` is processed in
the step at `σ + e`. -/
def st : ℕ → Q → S
  | 0, x => A.init (C.proc x) (C.inp x)
  | τ + 1, x => A.step (C.proc x) (st τ x) fun q =>
      if e ≤ τ then (C.nbr (τ - e) x q).elim [] fun y => A.send q (st (τ - e) y) (C.proc x)
      else []
termination_by τ => τ
decreasing_by all_goals omega

/-- What a node `o` (if any) sends at time `σ` to `r`, running the code of `q`. -/
def msg (o : Option Q) (q : P) (σ : ℕ) (r : P) : List M :=
  o.elim [] fun y => A.send q (C.st A e σ y) r

@[simp] theorem msg_none (q : P) (σ : ℕ) (r : P) : C.msg A e none q σ r = [] := rfl

@[simp] theorem msg_some (y : Q) (q : P) (σ : ℕ) (r : P) :
    C.msg A e (some y) q σ r = A.send q (C.st A e σ y) r := rfl

@[simp] theorem st_zero (x : Q) : C.st A e 0 x = A.init (C.proc x) (C.inp x) := by
  rw [st]

theorem st_succ (τ : ℕ) (x : Q) :
    C.st A e (τ + 1) x = A.step (C.proc x) (C.st A e τ x) fun q =>
      if e ≤ τ then C.msg A e (C.nbr (τ - e) x q) q (τ - e) (C.proc x) else [] := by
  rw [st]; rfl

/-- `a < b` from `σ + Δ * a < Δ * b`. -/
theorem lt_of_add_mul_lt {σ Δ a b : ℕ} (h : σ + Δ * a < Δ * b) : a < b :=
  Nat.lt_of_mul_lt_mul_left (by omega : Δ * a < Δ * b)

/-- **Locality.** Let `lvl : Q → ℕ` be a level function and `T` a horizon. If the two systems
have the same code, the same proposals at nodes `x` with `(e+1) * lvl x < T`, and the same
neighbours of `x` at times `σ` with `σ + (e+1) * (lvl x + 1) < T`, these neighbours having level
`≤ lvl x + 1`, then every node `x` has the same state in both systems at times `τ` with
`τ + (e+1) * lvl x < T`. -/
theorem st_eq_of_level {C' : DCover P Q V} (hp : C'.proc = C.proc) (lvl : Q → ℕ) (T : ℕ)
    (hn : ∀ σ x q, σ + (e + 1) * (lvl x + 1) < T →
      C'.nbr σ x q = C.nbr σ x q ∧ ∀ y, C.nbr σ x q = some y → lvl y ≤ lvl x + 1)
    (hi : ∀ x, (e + 1) * lvl x < T → C'.inp x = C.inp x) :
    ∀ τ x, τ + (e + 1) * lvl x < T → C'.st A e τ x = C.st A e τ x := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro x hx
    rcases τ with _ | τ
    · simp only [st_zero, hp, hi x (by omega)]
    · rw [st_succ, st_succ, hp, ih τ (by omega) x (by omega)]
      congr 1
      funext q
      split_ifs with he
      · have hσ : τ - e + (e + 1) * (lvl x + 1) < T := by
          rw [Nat.mul_add]; omega
        obtain ⟨h1, h2⟩ := hn (τ - e) x q hσ
        rw [h1]
        cases hy : C.nbr (τ - e) x q with
        | none => rfl
        | some y =>
          simp only [msg_some]
          rw [ih (τ - e) (by omega) y]
          have := Nat.mul_le_mul_left (e + 1) (h2 y hy)
          rw [Nat.mul_add] at hσ this
          omega
      · rfl

/-! ### Runs with uniform delivery offset -/

/-- `(range n).flatMap` of a function supported at one point. -/
theorem flatMap_range_ite {α : Type*} (L : ℕ → List α) (j : ℕ) :
    ∀ n, (List.range n).flatMap (fun i => if i = j then L i else []) =
      if j < n then L j else [] := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases hj : j = n
    · subst hj; simp
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Ne.symm hj, ite_false]
      by_cases h : j < n
      · simp [h, show j < n + 1 by omega]
      · simp [h, show ¬ j < n + 1 by omega]

/-- In a run where every batch is delivered with offset `e`, the inbox at time `τ` is what was
sent at time `τ - e`. -/
theorem inbox_of_dl_add [DecidableEq P] {VO : Type*} (A : Algorithm P M S V VO) {R : Run P M V}
    {e : ℕ} (h : ∀ q σ p, R.dl q σ p = σ + e) (p : P) (τ : ℕ) (q : P) :
    R.inbox A p τ q = if e ≤ τ then R.out A q (τ - e) p else [] := by
  rw [Run.inbox_eq_flatMap]
  simp only [Run.dlv, h]
  by_cases he : e ≤ τ
  · rw [ite_eq_left he]
    have : (fun τ' => if τ' + e = τ then R.out A q τ' p else []) =
        fun τ' => if τ' = τ - e then R.out A q τ' p else [] := by
      funext τ'
      by_cases h' : τ' = τ - e
      · simp [h', show τ - e + e = τ by omega]
      · simp [h', show τ' + e ≠ τ by omega]
    rw [this, flatMap_range_ite, ite_eq_left (by omega)]
  · rw [ite_eq_right he]
    simp only [List.flatMap_eq_nil_iff, List.mem_range]
    intro τ' _
    simp [show τ' + e ≠ τ by omega]

variable [DecidableEq P]

/-- The run in which the processes of `F` are Byzantine and every Byzantine `q` sends to `p` (at
time `σ`) what node `nbr σ (lift p) q` sends; every batch is delivered with offset `e`. -/
def run (F : Finset P) (lift : P → Q) : Run P M V where
  faulty := F
  inp p := C.inp (lift p)
  gst := 0
  byz q σ p := C.msg A e (C.nbr σ (lift p) q) q σ p
  dl _ σ _ := σ + e

@[simp] theorem run_faulty (F : Finset P) (lift : P → Q) : (C.run A e F lift).faulty = F := rfl

@[simp] theorem run_inp (F : Finset P) (lift : P → Q) (p : P) :
    (C.run A e F lift).inp p = C.inp (lift p) := rfl

/-- **Covering lemma.** Let `X` be a set of processes, each running the code of its lift and
listening to the lifts of the correct processes, which belong to `X`. Then the processes of `X`
(correct or not) have the states of their lifts. -/
theorem st_run {F : Finset P} {lift : P → Q} (X : Set P)
    (hX : ∀ p ∈ X, C.proc (lift p) = p ∧
      ∀ q ∉ F, q ∈ X ∧ ∀ σ, C.nbr σ (lift p) q = some (lift q)) :
    ∀ τ, ∀ p ∈ X, (C.run A e F lift).st A τ p = C.st A e τ (lift p) := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro p hp
    obtain ⟨hpr, hq⟩ := hX p hp
    rcases τ with _ | τ
    · simp [hpr, run]
    · rw [Run.st_succ, st_succ, hpr, ih τ (by omega) p hp]
      congr 1
      funext q
      rw [inbox_of_dl_add A (fun _ _ _ => rfl)]
      split_ifs with he
      · by_cases hqF : q ∈ F
        · rw [Run.out_of_faulty A _ hqF]; rfl
        · obtain ⟨hqX, hn⟩ := hq q hqF
          rw [Run.out_of_correct A _ hqF, ih (τ - e) (by omega) q hqX, hn, msg_some]
      · rfl

/-- The covering lemma for the correct processes. -/
theorem st_run_correct {F : Finset P} {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q)) :
    ∀ τ, ∀ p ∉ F, (C.run A e F lift).st A τ p = C.st A e τ (lift p) := fun τ p hp =>
  C.st_run A e {p | p ∉ F}
    (fun p hp => ⟨(hcov p hp).1, fun q hq => ⟨hq, (hcov p hp).2 q hq⟩⟩) τ p hp

theorem decides_run_iff {F : Finset P} {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q))
    {p : P} (hp : p ∉ F) {v : V} :
    (C.run A e F lift).Decides A p v ↔ ∃ τ, A.decide p (C.st A e τ (lift p)) = some v := by
  simp only [Run.Decides, C.st_run_correct A e hcov _ p hp]

/-- The covering run is a synchronous run with effective delay `e + 1`. -/
theorem run_syncValid {f : ℕ} {F : Finset P} (hF : F.card ≤ f) (lift : P → Q) :
    SyncValid f (e + 1) (C.run A e F lift) where
  card_faulty := hF
  dl_ge _ _ _ _ _ := by simp [run]
  dl_lt _ _ _ _ _ := by simp [run]

/-! ### Signatures -/

/-- **Nodes are unforging**: a token sent by node `x` is signed by `proc x` or was received
before, from a neighbour. -/
theorem node_unforging [Fintype P] {Au : Auth P M K} (hU : A.Unforging Au) (x : Q) (τ : ℕ)
    (r : P) (m : M) (hm : m ∈ A.send (C.proc x) (C.st A e τ x) r) (t : K)
    (ht : t ∈ Au.tokens m) :
    Au.signer t = C.proc x ∨ ∃ σ < τ, ∃ q y, C.nbr σ x q = some y ∧
      ∃ m' ∈ A.send q (C.st A e σ y) (C.proc x), t ∈ Au.tokens m' := by
  set R := C.run A e univ (fun _ => x)
  have hst := C.st_run A e (F := univ) (lift := fun _ => x) {C.proc x}
    (fun p hp => ⟨by simp only [Set.mem_singleton_iff] at hp; exact hp.symm,
      fun q hq => absurd (mem_univ q) hq⟩) τ (C.proc x) rfl
  rw [← hst] at hm
  rcases hU R (C.proc x) τ r m hm t ht with h | ⟨τ', hτ', q, m', hm', ht'⟩
  · exact Or.inl h
  · obtain ⟨σ, hσ, -, hm''⟩ := Run.mem_inbox.mp hm'
    rw [Run.out_of_faulty A _ (mem_univ q)] at hm''
    change m' ∈ C.msg A e (C.nbr σ x q) q σ (C.proc x) at hm''
    cases hy : C.nbr σ x q with
    | none => rw [hy] at hm''; simp at hm''
    | some y =>
      rw [hy, msg_some] at hm''
      exact Or.inr ⟨σ, by omega, q, y, hy, m', hm'', ht'⟩

/-- **Origin of tokens.** In a part `N` of the system closed under `nbr` (where neighbours run
the code of the sender they stand for), every token sent by a node was emitted earlier by a node
of `N` running the code of its signer. -/
theorem token_origin [Fintype P] {Au : Auth P M K} (hU : A.Unforging Au) (N : Set Q)
    (hN : ∀ x ∈ N, ∀ σ q y, C.nbr σ x q = some y → y ∈ N ∧ C.proc y = q) :
    ∀ τ, ∀ x ∈ N, ∀ r, ∀ m ∈ A.send (C.proc x) (C.st A e τ x) r, ∀ t ∈ Au.tokens m,
      ∃ z ∈ N, C.proc z = Au.signer t ∧ ∃ σ ≤ τ, ∃ r', ∃ m' ∈ A.send (C.proc z) (C.st A e σ z) r',
        t ∈ Au.tokens m' := by
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
    intro x hx r m hm t ht
    rcases C.node_unforging A e hU x τ r m hm t ht with h | ⟨σ, hσ, q, y, hy, m', hm', ht'⟩
    · exact ⟨x, hx, h.symm, τ, le_rfl, r, m, hm, ht⟩
    · obtain ⟨hyN, hyp⟩ := hN x hx σ q y hy
      rw [← hyp] at hm'
      obtain ⟨z, hz, hzp, σ', hσ', r', m'', hm'', ht''⟩ := ih σ hσ y hyN _ m' hm' t ht'
      exact ⟨z, hz, hzp, σ', by omega, r', m'', hm'', ht''⟩

/-- **The covering run respects unforgeability** if, in a part `N` of the system closed under
`nbr` and containing the lifts of the correct processes, every node running the code of a
correct process is its lift. -/
theorem run_authValid [Fintype P] {Au : Auth P M K} (hU : A.Unforging Au) {F : Finset P}
    {lift : P → Q}
    (hcov : ∀ p ∉ F, C.proc (lift p) = p ∧ ∀ q ∉ F, ∀ σ, C.nbr σ (lift p) q = some (lift q))
    (N : Set Q) (hN : ∀ x ∈ N, ∀ σ q y, C.nbr σ x q = some y → y ∈ N ∧ C.proc y = q)
    (hlift : ∀ p ∉ F, lift p ∈ N) (huniq : ∀ z ∈ N, C.proc z ∉ F → z = lift (C.proc z)) :
    (C.run A e F lift).AuthValid Au A := by
  intro b _ τ r hr m hm t ht
  change m ∈ C.msg A e (C.nbr τ (lift r) b) b τ r at hm
  cases hy : C.nbr τ (lift r) b with
  | none => rw [hy] at hm; simp at hm
  | some y =>
    rw [hy, msg_some] at hm
    obtain ⟨hyN, hyp⟩ := hN _ (hlift r hr) τ b y hy
    rw [← hyp] at hm
    obtain ⟨z, hz, hzp, σ, hσ, r', m', hm', ht'⟩ := C.token_origin A e hU N hN τ y hyN r m hm t ht
    by_cases hsF : Au.signer t ∈ F
    · exact Or.inl hsF
    · right
      have hzl : z = lift (Au.signer t) := hzp ▸ huniq z hz (hzp ▸ hsF)
      refine ⟨σ, hσ, Au.signer t, hsF, r', m', ?_, ht'⟩
      rw [Run.out_of_correct A _ hsF, C.st_run_correct A e hcov σ _ hsF, ← hzl, ← hzp]
      exact hm'

end DCover

end GoodCaseLatencyBB
