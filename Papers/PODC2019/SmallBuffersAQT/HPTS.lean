import Papers.PODC2019.SmallBuffersAQT.Hierarchy

/-!
# Algorithm HPTS (Section 4.2): one forwarding round

A configuration `c : ℕ → ℕ → ℕ` gives the number `c i w` of packets stored at node `i` with final
destination `w` (packets inside a pseudo-buffer are interchangeable for buffer sizes). The
pseudo-buffer `L_{j,k}(i)` of the paper is `pb c i (j, x)` where `x` is its intermediate destination.

A round of HPTS at level `lam` (Algorithm 3, one value of `λ`):
* `fpAct c lam`: the activation of `FormPaths` (Algorithm 4) in all level-`lam` intervals. We use the
  following closed form of the loop of Algorithm 4 (equivalently Algorithm 2, PPTS): node `v` activates
  the level-`lam` pseudo-buffer whose intermediate destination `x` is the largest among the bad
  (size `≥ 2`) level-`lam` pseudo-buffers at nodes `u ≤ v` with `x > v`. (In the loop, the interval
  `[i_k, min(i'-1, w_k-1)]` of destination `w_k` contains `v` iff `w_k` is that largest one.)
* `preBadStep j`: `ActivatePreBad(A, j)` (Algorithm 5) for all level-`j` intervals `[a, b]`: if the
  packet that `a - 1` forwards into `a` is pre-bad at level `j` (Definition 4.6: its new pseudo-buffer
  `(j, x)` at `a` is nonempty) and `a` is inactive, then the pseudo-buffers `(j, x)` of the inactive
  prefix `[a, e]` of `[a, x - 1]` are activated. The levels are processed for `j = lam-1, …, 0`.
* `sel i q`: which packet (destination) a pseudo-buffer forwards; arbitrary (`ValidSel`), since the
  paper makes no assumption on the priority inside pseudo-buffers.
-/

namespace Podc.SmallBuffersAQT

open Finset

/-- A configuration: `c i w` packets at node `i` with destination `w`. -/
abbrev Config := ℕ → ℕ → ℕ

/-- A pseudo-buffer: (level, intermediate destination). -/
abbrev Key := ℕ × ℕ

variable (m ℓ : ℕ)

/-- Size of the pseudo-buffer `q` of node `i`. -/
def pb (c : Config) (i : ℕ) (q : Key) : ℕ :=
  ∑ w ∈ (range (m ^ ℓ)).filter (fun w => i < w ∧ key m ℓ i w = q), c i w

/-- The universe of pseudo-buffer names. -/
def KS : Finset Key := range ℓ ×ˢ range (m ^ ℓ)

/-- Badness of node `i` restricted to the levels in `L` (Definitions 4.4, 4.5): the number of bad
packets in pseudo-buffers at nodes `u ≤ i` whose level is in `L` and whose intermediate destination
is beyond `i` (packets that still have to cross `i` in their current segment). -/
def Bad (c : Config) (L : Finset ℕ) (i : ℕ) : ℕ :=
  ∑ q ∈ (KS m ℓ).filter (fun q => q.1 ∈ L ∧ i < q.2), ∑ u ∈ range (i + 1), (pb m ℓ c u q - 1)

/-- The badness `B(i)` of node `i` (all levels). -/
def badness (c : Config) (i : ℕ) : ℕ := Bad m ℓ c (range ℓ) i

/-- The packet arriving at node `i` (its destination), when `f` describes what each node forwards;
a packet arriving at its destination is delivered and does not arrive in a buffer. -/
def arrival (f : ℕ → Option ℕ) : ℕ → Option ℕ
  | 0 => none
  | i + 1 => match f i with
    | some w => if i + 1 < w then some w else none
    | none => none

/-- The configuration after every node `i` with `f i = some w` forwards one packet with
destination `w` to `i + 1`. -/
def fwd (c : Config) (f : ℕ → Option ℕ) : Config := fun i w =>
  c i w - (if f i = some w then 1 else 0) + (if arrival f i = some w then 1 else 0)

/-- A valid choice of the packet forwarded by each nonempty pseudo-buffer. -/
def ValidSel (c : Config) (sel : ℕ → Key → ℕ) : Prop :=
  ∀ i q, 1 ≤ pb m ℓ c i q →
    1 ≤ c i (sel i q) ∧ i < sel i q ∧ sel i q < m ^ ℓ ∧ key m ℓ i (sel i q) = q

/-- What node `v` forwards under the activation `act`: the selected packet of its active
pseudo-buffer, if that is nonempty. -/
def fwdOf (c : Config) (sel : ℕ → Key → ℕ) (act : ℕ → Option Key) (v : ℕ) : Option ℕ :=
  match act v with
  | some q => if 1 ≤ pb m ℓ c v q then some (sel v q) else none
  | none => none

/-- `FormPaths` at level `lam` in every level-`lam` interval (Algorithm 4, in closed form). -/
def fpAct (c : Config) (lam v : ℕ) : Option Key :=
  if h : ((range (m ^ ℓ)).filter
      (fun x => v < x ∧ ((range (v + 1)).filter (fun u => 2 ≤ pb m ℓ c u (lam, x))).Nonempty)).Nonempty then
    some (lam, ((range (m ^ ℓ)).filter
      (fun x => v < x ∧ ((range (v + 1)).filter (fun u => 2 ≤ pb m ℓ c u (lam, x))).Nonempty)).max' h)
  else none

/-- `ActivatePreBad(A, j)` (Algorithm 5) for all level-`j` intervals at once. -/
def preBadStep (c : Config) (sel : ℕ → Key → ℕ) (j : ℕ) (act : ℕ → Option Key) (v : ℕ) :
    Option Key :=
  match act v with
  | some q => some q
  | none =>
    if 0 < lvl m j v then
      match fwdOf m ℓ c sel act (lvl m j v - 1) with
      | some w =>
        if lvl m j v < w ∧ lv m ℓ (lvl m j v) w = j ∧ 1 ≤ pb m ℓ c (lvl m j v) (key m ℓ (lvl m j v) w)
            ∧ v < xd m ℓ (lvl m j v) w ∧ ∀ u ∈ Icc (lvl m j v) v, act u = none then
          some (key m ℓ (lvl m j v) w)
        else none
      | none => none
    else none

/-- The activation after `FormPaths` at level `lam` and `k` calls of `ActivatePreBad` (levels
`lam-1, …, lam-k`). -/
def actIter (c : Config) (sel : ℕ → Key → ℕ) (lam : ℕ) : ℕ → ℕ → Option Key
  | 0 => fpAct m ℓ c lam
  | k + 1 => preBadStep m ℓ c sel (lam - 1 - k) (actIter c sel lam k)

/-- The activation once all levels `≥ j` have been processed (`j ≤ lam`). -/
def actLv (c : Config) (sel : ℕ → Key → ℕ) (lam j : ℕ) : ℕ → Option Key :=
  actIter m ℓ c sel lam (lam - j)

/-- One round of HPTS at level `lam` (Algorithm 3, lines 6–12). -/
def hptsStep (lam : ℕ) (c : Config) (sel : ℕ → Key → ℕ) : Config :=
  fwd c (fwdOf m ℓ c sel (actLv m ℓ c sel lam 0))

end Podc.SmallBuffersAQT
