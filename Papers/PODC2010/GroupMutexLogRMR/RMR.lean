import Papers.PODC2010.GroupMutexLogRMR.Model

/-!
# The RMR bound of Theorem 1 / Lemma 5 fails: unboundedly many RMRs at line 8

Lemma 5 of the paper claims that the busy-waiting loops at lines 8 and 12 cost O(1) RMRs
("By the Claims 6 and 8 … RMR associated with these loops is indeed just 2"). In the
cache-coherent model every write to `Out[s]` by another process invalidates the cached copy of a
process spinning on `Out[s]`, so its next read is remote, even if the written value is the same.
Line 7 (`Out[s] ← d`) is executed by every process that finds `S = (s, d, s)` at line 6, and such
processes may keep coming while a fellow process of the *other* side waits at line 8.

Four processes, two sessions (`S = (0,0,0)` initially, `In[0] = 1`):

* `r = 0` (session 0) joins side 0 (lines 1.5–1.6, since `S = (0, 0̄̄, −)`), takes time-stamp 1 at
  line 3 and pauses before enqueuing;
* `q = 1` (session 1, side 1, time-stamp 2) enqueues; it cannot promote (`C[0,0] = 1` because of `r`)
  and waits at line 8;
* `p = 2` (session 0) reads `In[0] = 1`, finds `Min(Q) = (1,1)` at line 1.4 and keeps side 1
  (time-stamp 3); it waits at line 8 for `Out[0] = 1`;
* `r` enqueues (it is now the smallest element), finds `S = (0,0,0)` at line 6, writes
  `Out[0] ← 0` and enters the CS, where it stays;
* round: `f = 3` (session 0) finds `Min(Q) = (0,0)` (= `r`) at line 1.4 and `S = (0,0,−)` at line 1.5,
  joins side 0, writes `Out[0] ← 0` at line 7, passes the CS and leaves (no flip at line 14, since
  `Min(Q) = (0,−)`; no promotion, since `C[0,0] = 1`). Then `p` re-reads `Out[0]` at line 8: a
  remote reference. The round leaves the configuration unchanged except for `G`.

After `K` rounds, `p` has made `K` remote reads in a single attempt, while `n = 4` and the point
contention is at most 4. So no bound of the form O(min(log n, k)) — indeed no bound depending
only on `n` — holds for the number of RMRs per attempt.

## Cost model

`Cost.next` is the standard write-invalidate cache-coherent model restricted to the `Out`
variables and to the reads of one process `p` at line 8 (a lower bound on `p`'s RMRs): a read of
`Out[s]` at line 8 by `p` is remote iff `p` has no valid cached copy; afterwards it has one; a
write to `Out[x]` (lines 5.5, 7, 16.11, 16.13) by another process invalidates `p`'s copy of
`Out[x]`. The counter `cnt` is reset when `p` starts a new attempt, so it counts the remote reads
of `p`'s current attempt.
-/

namespace Podc.GroupMutexLogRMR

section Cost

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- The variable `Out[x]` written by the next step of `q`, if any. -/
def Cfg.outWrite (c : Cfg n J) (q : Fin n) : Option J :=
  match (c.loc q).pc with
  | .l5_5 => (c.loc q).b.map Prod.fst
  | .l7 => some (c.loc q).s
  | .l16_11 => (c.loc q).b.map Prod.fst
  | .l16_13 => some (c.loc q).a.1
  | _ => none

/-- Ghost cost state for process `p`: valid cached copies of the `Out` variables, and the number
of remote reads of `Out` at line 8 in `p`'s current attempt. -/
structure Cost (n : ℕ) (J : Type) where
  /-- `cache r x`: process `r` holds a valid cached copy of `Out[x]` -/
  cache : Fin n → J → Bool
  /-- remote reads at line 8 by `p` in its current attempt -/
  cnt : ℕ

/-- Update of the cost state by the event `e` in configuration `c` (before the step). -/
def Cost.next (p : Fin n) (c : Cfg n J) (γ : Cost n J) (e : Ev n J) : Cost n J :=
  let q := e.1
  let γ₁ : Cost n J := match c.outWrite q with
    | some x => { γ with cache := fun r y => if y = x ∧ r ≠ q then false else γ.cache r y }
    | none => γ
  if q = p then
    match (c.loc p).pc with
    | .rem => { γ₁ with cnt := 0 }
    | .l8 =>
      if γ₁.cache p (c.loc p).s then γ₁
      else { cache := fun r y => if r = p ∧ y = (c.loc p).s then true else γ₁.cache r y,
             cnt := γ₁.cnt + 1 }
    | _ => γ₁
  else γ₁

/-- Run with cost accounting for `p`. -/
def costRun (p : Fin n) (cγ : Cfg n J × Cost n J) (es : List (Ev n J)) : Cfg n J × Cost n J :=
  es.foldl (fun cγ e => (cγ.1.step e.1 e.2, Cost.next p cγ.1 cγ.2 e)) cγ

theorem costRun_fst (p : Fin n) (cγ : Cfg n J × Cost n J) (es : List (Ev n J)) :
    (costRun p cγ es).1 = run cγ.1 es := by
  induction es generalizing cγ with
  | nil => rfl
  | cons e es ih => exact ih _

theorem costRun_append (p : Fin n) (cγ : Cfg n J × Cost n J) (es es' : List (Ev n J)) :
    costRun p cγ (es ++ es') = costRun p (costRun p cγ es) es' := List.foldl_append

/-- The initial cost state: no cached copies. -/
def Cost.init (n : ℕ) (J : Type) : Cost n J := ⟨fun _ _ => false, 0⟩

end Cost

/-- Prefix: `r = 0` takes a time-stamp and pauses before enqueuing; `q = 1` (session 1) and
`p = 2` (session 0, side 1) wait at line 8; `r` enqueues and enters the CS. -/
def rmrPre : List (Ev 4 (Fin 2)) :=
  [(0, 0)] ++ List.replicate 9 (0, 0) ++
  [(1, 1)] ++ List.replicate 13 (1, 1) ++
  [(2, 0)] ++ List.replicate 12 (2, 0) ++
  List.replicate 10 (0, 0)

/-- One round: `f = 3` (session 0) runs a whole attempt, writing `Out[0]` at line 7; then `p`
re-reads `Out[0]` at line 8. -/
def rmrLoop : List (Ev 4 (Fin 2)) :=
  [(3, 0)] ++ List.replicate 30 (3, 0) ++ [(2, 0)]

attribute [ext] Cfg

theorem cfg_ext_iff' {c c' : Cfg 4 (Fin 2)} :
    c = c' ↔ c.S = c'.S ∧ c.Ex = c'.Ex ∧ c.G = c'.G ∧ (∀ s, c.In s = c'.In s) ∧ (∀ s, c.Out s = c'.Out s) ∧
      (∀ s, c.Exclear s = c'.Exclear s) ∧ (∀ s d, c.C s d = c'.C s d) ∧ (∀ q, c.Q q = c'.Q q) ∧
      (∀ q, c.linkS q = c'.linkS q) ∧ (∀ q, c.linkEx q = c'.linkEx q) ∧ (∀ q, c.loc q = c'.loc q) := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    cases c; cases c'
    simp only [Cfg.mk.injEq]
    exact ⟨h1, h2, h3, funext h4, funext h5, funext h6, funext fun s => funext (h7 s), funext h8,
      funext h9, funext h10, funext h11⟩

theorem cost_ext_iff' {γ γ' : Cost 4 (Fin 2)} :
    γ = γ' ↔ (∀ r x, γ.cache r x = γ'.cache r x) ∧ γ.cnt = γ'.cnt := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩
    cases γ; cases γ'
    simp only [Cost.mk.injEq]
    exact ⟨funext fun r => funext (h1 r), h2⟩

/-- Proves `c = c'` for explicit configurations, field by field. -/
macro "cfg_tac" : tactic => `(tactic| (
  rw [cfg_ext_iff']
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  (intro x; try intro y) <;> fin_cases x <;> (try cases y) <;> rfl))

/-- Proves `γ = γ'` for explicit cost states. -/
macro "cost_tac" : tactic => `(tactic| (
  rw [cost_ext_iff']
  refine ⟨?_, rfl⟩
  intro x y; fin_cases x <;> fin_cases y <;> rfl))

/-- `p`'s valid cached copy of `Out[0]`, and `m` remote reads so far. -/
def cacheP (m : ℕ) : Cost 4 (Fin 2) := ⟨fun r y => decide (r = 2 ∧ y = 0), m⟩

/-- No valid cached copies, `m` remote reads so far. -/
def cacheW (m : ℕ) : Cost 4 (Fin 2) := ⟨fun _ _ => false, m⟩

/-- The configuration at the start of a round (`G = g`): `r` in the CS, `q` and `p` at line 8, `f` in the remainder section. -/
def rc0 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.rem, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 1 steps of a round. -/
def rc1 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_1, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 2 steps of a round. -/
def rc2 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_2, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 3 steps of a round. -/
def rc3 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 2 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_3, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 4 steps of a round. -/
def rc4 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 2 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_4, 0, true, g, (0, false), some (0, false)⟩]

/-- The configuration after 5 steps of a round. -/
def rc5 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 2 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_5, 0, true, g, (0, false), some (0, false)⟩]

/-- The configuration after 6 steps of a round. -/
def rc6 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 2 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_6, 0, true, g, (0, false), some (0, false)⟩]

/-- The configuration after 7 steps of a round. -/
def rc7 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 2 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l1_7, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 8 steps of a round. -/
def rc8 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := g
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l2, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 9 steps of a round. -/
def rc9 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l3, 0, false, g, (0, false), some (0, false)⟩]

/-- The configuration after 10 steps of a round. -/
def rc10 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l4, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 11 steps of a round. -/
def rc11 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l5_1, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 12 steps of a round. -/
def rc12 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l5_2, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 13 steps of a round. -/
def rc13 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l5_3, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 14 steps of a round. -/
def rc14 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l6, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 15 steps of a round. -/
def rc15 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l7, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 16 steps of a round. -/
def rc16 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l8, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 17 steps of a round. -/
def rc17 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l9, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 18 steps of a round. -/
def rc18 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l10, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 19 steps of a round. -/
def rc19 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, false]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l11, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 20 steps of a round. -/
def rc20 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.cs, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 21 steps of a round. -/
def rc21 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), some (0, false, (g + 1))]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l13, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 22 steps of a round. -/
def rc22 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l14, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 23 steps of a round. -/
def rc23 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_1, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 24 steps of a round. -/
def rc24 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_2, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 25 steps of a round. -/
def rc25 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, false]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_3, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 26 steps of a round. -/
def rc26 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_4, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 27 steps of a round. -/
def rc27 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_5, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 28 steps of a round. -/
def rc28 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 2) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_6, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 29 steps of a round. -/
def rc29 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_7, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 30 steps of a round. -/
def rc30 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.l16_8, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 31 steps of a round. -/
def rc31 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.rem, 0, false, (g + 1), (0, false), some (0, false)⟩]

/-- The configuration after 32 steps of a round. -/
def rc32 (g : ℕ) : Cfg 4 (Fin 2) where
  S := (0, false, 0)
  Ex := none
  G := (g + 1)
  In := ![true, true]
  Out := ![false, false]
  Exclear := ![false, true]
  C s d := if s = 0 then (if d then 1 else 1) else (if d then 1 else 0)
  Q := ![some (0, false, 1), some (1, true, 2), some (0, true, 3), none]
  linkS := ![true, true, true, true]
  linkEx := ![false, false, false, true]
  loc := ![⟨.cs, 0, false, 1, (0, false), some (0, false)⟩, ⟨.l8, 1, true, 2, (0, false), some (1, true)⟩, ⟨.l8, 0, true, 3, (0, false), some (1, true)⟩, ⟨.rem, 0, false, (g + 1), (0, false), some (0, false)⟩]

theorem rstep0 (g : ℕ) : (rc0 g).step (3 : Fin 4) 0 = rc1 g := by cfg_tac
theorem rstep1 (g : ℕ) : (rc1 g).step (3 : Fin 4) 0 = rc2 g := by cfg_tac
theorem rstep2 (g : ℕ) : (rc2 g).step (3 : Fin 4) 0 = rc3 g := by cfg_tac
theorem rstep3 (g : ℕ) : (rc3 g).step (3 : Fin 4) 0 = rc4 g := by cfg_tac
theorem rstep4 (g : ℕ) : (rc4 g).step (3 : Fin 4) 0 = rc5 g := by cfg_tac
theorem rstep5 (g : ℕ) : (rc5 g).step (3 : Fin 4) 0 = rc6 g := by cfg_tac
theorem rstep6 (g : ℕ) : (rc6 g).step (3 : Fin 4) 0 = rc7 g := by cfg_tac
theorem rstep7 (g : ℕ) : (rc7 g).step (3 : Fin 4) 0 = rc8 g := by cfg_tac
theorem rstep8 (g : ℕ) : (rc8 g).step (3 : Fin 4) 0 = rc9 g := by cfg_tac
theorem rstep9 (g : ℕ) : (rc9 g).step (3 : Fin 4) 0 = rc10 g := by cfg_tac
theorem rstep10 (g : ℕ) : (rc10 g).step (3 : Fin 4) 0 = rc11 g := by cfg_tac
theorem rstep11 (g : ℕ) : (rc11 g).step (3 : Fin 4) 0 = rc12 g := by cfg_tac
theorem rstep12 (g : ℕ) : (rc12 g).step (3 : Fin 4) 0 = rc13 g := by cfg_tac
theorem rstep13 (g : ℕ) : (rc13 g).step (3 : Fin 4) 0 = rc14 g := by cfg_tac
theorem rstep14 (g : ℕ) : (rc14 g).step (3 : Fin 4) 0 = rc15 g := by cfg_tac
theorem rstep15 (g : ℕ) : (rc15 g).step (3 : Fin 4) 0 = rc16 g := by cfg_tac
theorem rstep16 (g : ℕ) : (rc16 g).step (3 : Fin 4) 0 = rc17 g := by cfg_tac
theorem rstep17 (g : ℕ) : (rc17 g).step (3 : Fin 4) 0 = rc18 g := by cfg_tac
theorem rstep18 (g : ℕ) : (rc18 g).step (3 : Fin 4) 0 = rc19 g := by cfg_tac
theorem rstep19 (g : ℕ) : (rc19 g).step (3 : Fin 4) 0 = rc20 g := by cfg_tac
theorem rstep20 (g : ℕ) : (rc20 g).step (3 : Fin 4) 0 = rc21 g := by cfg_tac
theorem rstep21 (g : ℕ) : (rc21 g).step (3 : Fin 4) 0 = rc22 g := by cfg_tac
theorem rstep22 (g : ℕ) : (rc22 g).step (3 : Fin 4) 0 = rc23 g := by cfg_tac
theorem rstep23 (g : ℕ) : (rc23 g).step (3 : Fin 4) 0 = rc24 g := by cfg_tac
theorem rstep24 (g : ℕ) : (rc24 g).step (3 : Fin 4) 0 = rc25 g := by cfg_tac
theorem rstep25 (g : ℕ) : (rc25 g).step (3 : Fin 4) 0 = rc26 g := by cfg_tac
theorem rstep26 (g : ℕ) : (rc26 g).step (3 : Fin 4) 0 = rc27 g := by cfg_tac
theorem rstep27 (g : ℕ) : (rc27 g).step (3 : Fin 4) 0 = rc28 g := by cfg_tac
theorem rstep28 (g : ℕ) : (rc28 g).step (3 : Fin 4) 0 = rc29 g := by cfg_tac
theorem rstep29 (g : ℕ) : (rc29 g).step (3 : Fin 4) 0 = rc30 g := by cfg_tac
theorem rstep30 (g : ℕ) : (rc30 g).step (3 : Fin 4) 0 = rc31 g := by cfg_tac
theorem rstep31 (g : ℕ) : (rc31 g).step (2 : Fin 4) 0 = rc32 g := by cfg_tac

theorem cstep0 (g m : ℕ) : Cost.next 2 (rc0 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep1 (g m : ℕ) : Cost.next 2 (rc1 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep2 (g m : ℕ) : Cost.next 2 (rc2 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep3 (g m : ℕ) : Cost.next 2 (rc3 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep4 (g m : ℕ) : Cost.next 2 (rc4 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep5 (g m : ℕ) : Cost.next 2 (rc5 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep6 (g m : ℕ) : Cost.next 2 (rc6 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep7 (g m : ℕ) : Cost.next 2 (rc7 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep8 (g m : ℕ) : Cost.next 2 (rc8 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep9 (g m : ℕ) : Cost.next 2 (rc9 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep10 (g m : ℕ) : Cost.next 2 (rc10 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep11 (g m : ℕ) : Cost.next 2 (rc11 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep12 (g m : ℕ) : Cost.next 2 (rc12 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep13 (g m : ℕ) : Cost.next 2 (rc13 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep14 (g m : ℕ) : Cost.next 2 (rc14 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheP m := by cost_tac
theorem cstep15 (g m : ℕ) : Cost.next 2 (rc15 g) (cacheP m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep16 (g m : ℕ) : Cost.next 2 (rc16 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep17 (g m : ℕ) : Cost.next 2 (rc17 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep18 (g m : ℕ) : Cost.next 2 (rc18 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep19 (g m : ℕ) : Cost.next 2 (rc19 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep20 (g m : ℕ) : Cost.next 2 (rc20 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep21 (g m : ℕ) : Cost.next 2 (rc21 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep22 (g m : ℕ) : Cost.next 2 (rc22 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep23 (g m : ℕ) : Cost.next 2 (rc23 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep24 (g m : ℕ) : Cost.next 2 (rc24 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep25 (g m : ℕ) : Cost.next 2 (rc25 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep26 (g m : ℕ) : Cost.next 2 (rc26 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep27 (g m : ℕ) : Cost.next 2 (rc27 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep28 (g m : ℕ) : Cost.next 2 (rc28 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep29 (g m : ℕ) : Cost.next 2 (rc29 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep30 (g m : ℕ) : Cost.next 2 (rc30 g) (cacheW m) ((3 : Fin 4), (0 : Fin 2)) = cacheW m := by cost_tac
theorem cstep31 (g m : ℕ) : Cost.next 2 (rc31 g) (cacheW m) ((2 : Fin 4), (0 : Fin 2)) = cacheP (m + 1) := by cost_tac

theorem rc32_eq (g : ℕ) : rc32 g = rc0 (g + 1) := by cfg_tac

/-- One round: `G` grows by one, and `p` makes one more remote read. -/
theorem round (g m : ℕ) : costRun 2 (rc0 g, cacheP m) rmrLoop = (rc0 (g + 1), cacheP (m + 1)) := by
  simp only [rmrLoop, List.replicate, List.cons_append, List.nil_append, costRun,
    List.foldl_cons, List.foldl_nil]
  simp only [rstep0, cstep0, rstep1, cstep1, rstep2, cstep2, rstep3, cstep3, rstep4, cstep4, rstep5,
    cstep5, rstep6, cstep6, rstep7, cstep7, rstep8, cstep8, rstep9, cstep9, rstep10, cstep10, rstep11,
    cstep11, rstep12, cstep12, rstep13, cstep13, rstep14, cstep14, rstep15, cstep15, rstep16, cstep16,
    rstep17, cstep17, rstep18, cstep18, rstep19, cstep19, rstep20, cstep20, rstep21, cstep21, rstep22,
    cstep22, rstep23, cstep23, rstep24, cstep24, rstep25, cstep25, rstep26, cstep26, rstep27, cstep27,
    rstep28, cstep28, rstep29, cstep29, rstep30, cstep30, rstep31, cstep31, rc32_eq]

theorem prefix_round :
    costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) (rmrPre ++ rmrLoop) = (rc0 4, cacheP 1) := by
  rw [Prod.ext_iff, cfg_ext_iff', cost_ext_iff']
  decide +kernel

/-- The schedule with `K + 1` rounds. -/
def rmrSched (K : ℕ) : List (Ev 4 (Fin 2)) :=
  rmrPre ++ rmrLoop ++ (List.replicate K rmrLoop).flatten

theorem costRun_rmrSched (K : ℕ) :
    costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) (rmrSched K) = (rc0 (4 + K), cacheP (1 + K)) := by
  induction K with
  | zero => simpa [rmrSched] using prefix_round
  | succ K ih =>
    have : rmrSched (K + 1) = rmrSched K ++ rmrLoop := by
      simp [rmrSched, List.replicate_succ', List.flatten_append]
    rw [this, costRun_append, ih, round]
    rfl

/-- **Theorem 1 / Lemma 5 of the paper (RMR complexity) are false**: with `n = 4` processes and
two sessions, for every `K` there is an execution in which process `p = 2` is still in the
trying section (waiting at line 8) of a single attempt and has already made more than `K` remote
reads of `Out[0]` in it. Hence the number of RMRs of an attempt is not bounded by any function of
`n` (let alone `O(min(log n, k))`, `k ≤ n = 4`). -/
theorem rmr_unbounded (K : ℕ) :
    ∃ es : List (Ev 4 (Fin 2)),
      ((costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) es).1.loc 2).pc = .l8 ∧
      K < (costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) es).2.cnt := by
  refine ⟨rmrSched K, ?_, ?_⟩ <;> rw [costRun_rmrSched]
  · rfl
  · show K < 1 + K; omega

/-- No bound on the RMRs of an attempt in terms of `n` (here `n = 4`). -/
theorem not_bounded_rmr :
    ¬ ∃ B : ℕ, ∀ es : List (Ev 4 (Fin 2)),
      (costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) es).2.cnt ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨es, -, h⟩ := rmr_unbounded B
  exact absurd (hB es) (by omega)

/-- The finishing events: `r` leaves (switching `S` to `(1,1,0)`), `q` passes the CS and leaves
(switching `S` to `(0,1,1)`), and `p` enters the CS. -/
def rmrFin : List (Ev 4 (Fin 2)) :=
  List.replicate 17 (0, 0) ++ List.replicate 21 (1, 1) ++ List.replicate 4 (2, 0)

/-- Sanity check: after 3 rounds the attempt of `p` completes (it enters the CS), with 4 remote
reads at line 8 in that attempt. -/
theorem rmr_completes :
    ((costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) (rmrSched 3 ++ rmrFin)).1.loc 2).pc = .cs ∧
    4 ≤ (costRun 2 (Cfg.init 4 0, Cost.init 4 (Fin 2)) (rmrSched 3 ++ rmrFin)).2.cnt := by
  decide +kernel

end Podc.GroupMutexLogRMR
