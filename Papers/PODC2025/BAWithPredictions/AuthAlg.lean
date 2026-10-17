import Papers.PODC2025.BAWithPredictions.RoundModel
import Cslib.Computability.Distributed.Byzantine.PartialSync.RoundAuth

/-!
# Authenticated Byzantine Agreement with classification (Section 8) — the algorithm

Ben-David, Dzulfikar, Ellen, Gilbert, *Byzantine Agreement with Predictions*, PODC 2025
(arXiv:2505.01793), Section 8: Algorithm 6 (Byzantine broadcast with an implicit committee) run
in `n` parallel instances inside Algorithm 7 (authenticated Byzantine agreement with
classification).

## Signatures

Signatures are the abstract tokens of CSLib's `Auth` (`RoundAuth.lean`):
* `Tok.vote j i`: `sign_j(⟨committee, p_i⟩)`;
* `Tok.link j s x`: `p_j`'s signature on a link of a message chain for value `x` started by `p_s`
  (the token abstracts the signature on the whole prefix of the chain; a coarser token only gives
  the adversary more power).

A **committee certificate** for `p_i` (Definition 1) is a set `cc` of at least `t + 1` processes,
carried in a message together with the tokens `Tok.vote j i`, `j ∈ cc`.
A **message chain** (Definition 2) is `⟨s, x, links⟩` where `links` is the list of pairs
(signer, committee certificate of the signer), in signing order; it carries the tokens
`Tok.link j s x` of its signers and the vote tokens of its certificates. It is valid in round `r`
(`ChainOK t r`) if it has length `r`, starts with `s`, its signers are distinct and all its
certificates have at least `t + 1` voters.

## Rounds of `alg k t` (Algorithm 7)

* round `0` (lines 1–6): `p` sends `Tok.vote p j` to every `j` among the first `2k+1` positions
  of `π(c_p)`; at the end of the round `p` has a certificate iff it received `≥ t + 1` votes (we
  keep all received votes rather than the `t + 1` smallest);
* rounds `1, …, k+1` (lines 7–8, Algorithm 6 for all senders `s` in parallel): round `r` of the
  broadcast instances; the chains of all instances sent to one receiver are bundled into one
  message (`Msg.chains`); at the end of round `r`, `p` adds to `X_p[s]` (as long as
  `|X_p[s]| < 2`, smallest values first) the values of valid round-`r` chains for instance `s`
  that `p` has not signed (whoever delivered them: the paper only listens to senders with a
  certificate, but every signer of a valid chain has one), and, if it has a certificate, relays
  one such chain per newly added value (extended by its own link) in round `r + 1`;
* round `k+2` (lines 9–11): every process with a certificate broadcasts its plurality value
  together with its certificate; at the end of the round it decides (lines 12–14).

The decision is exhibited at the beginning of round `k + 3`, i.e. after `k + 3` rounds.

Defaults for cases the paper leaves open (they never occur under the hypotheses of Theorem 6):
if all broadcast outputs are `⊥`, the plurality value is the own input; if no valid plurality
message is received, the decision is the own input.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.AuthBA

open Finset Cslib.Byzantine.PartialSync

/-! ### Plurality with smallest-value tie-breaking -/

section PlurMin

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

/-- The value `f j` of a most frequent value on `X` (helper for `plurMin`). -/
theorem exists_max_cnt {X : Finset ι} (f : ι → α) (h : X.Nonempty) :
    ((X.filter fun j => cnt X f (f j) = X.sup fun j => cnt X f (f j)).image f).Nonempty := by
  obtain ⟨j, hj, he⟩ := X.exists_mem_eq_sup h (fun j => cnt X f (f j))
  exact ⟨f j, mem_image.mpr ⟨j, mem_filter.mpr ⟨hj, he.symm⟩, rfl⟩⟩

-- CSLib candidate
/-- **The smallest value that occurs the largest number of times** among the values of `f` on `X`
(`d` if `X = ∅`). -/
def plurMin (X : Finset ι) (f : ι → α) (d : α) : α :=
  if h : X.Nonempty then
    ((X.filter fun j => cnt X f (f j) = X.sup fun j => cnt X f (f j)).image f).min'
      (exists_max_cnt f h)
  else d

/-- A value occurring on a strict majority of `X` is the plurality. -/
theorem plurMin_eq_of_majority {X : Finset ι} {f : ι → α} {d w : α}
    (h : X.card < 2 * cnt X f w) : plurMin X f d = w := by
  have hne : X.Nonempty := by
    rw [← card_pos]; have := card_le_card (filter_subset (fun j => f j = w) X); unfold cnt Finset.countEq at h
    omega
  unfold plurMin
  simp only [hne, ↓reduceDIte]
  have key : ∀ a ∈ (X.filter fun j => cnt X f (f j) = X.sup fun j => cnt X f (f j)).image f,
      a = w := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    obtain ⟨hjX, hjM⟩ := mem_filter.mp hj
    by_contra hne'
    obtain ⟨j', hj'X, hj'w⟩ : ∃ j', j' ∈ X ∧ f j' = w := by
      have : (X.filter fun j => f j = w).Nonempty := by
        rw [← card_pos]; unfold cnt Finset.countEq at h; omega
      obtain ⟨j', hj'⟩ := this
      exact ⟨j', (mem_filter.mp hj').1, (mem_filter.mp hj').2⟩
    have h1 : cnt X f (f j') ≤ X.sup fun j => cnt X f (f j) :=
      le_sup (f := fun j => cnt X f (f j)) hj'X
    rw [hj'w] at h1
    have h2 := cnt_add_cnt_le (X := X) (f := f) hne'
    omega
  exact key _ (min'_mem _ _)

end PlurMin

/-! ### Tokens, chains, messages -/

/-- Signature tokens. -/
inductive Tok (P V : Type*) where
  /-- `sign_j(⟨committee, p_i⟩)`. -/
  | vote (j i : P)
  /-- `p_j`'s signature on a link of a message chain for value `x` started by `p_s`. -/
  | link (j s : P) (x : V)
  deriving DecidableEq

/-- The signer of a token. -/
def Tok.signer {P V : Type*} : Tok P V → P
  | .vote j _ => j
  | .link j _ _ => j

/-- A message chain for value `x` started by `p_s`: the list of links (signer, certificate). -/
structure Chain (P V : Type*) where
  /-- The process that started the chain (the instance). -/
  s : P
  /-- The value. -/
  x : V
  /-- The links: (signer, set of voters of its committee certificate), in signing order. -/
  links : List (P × Finset P)
  deriving DecidableEq

variable {P V : Type*}

/-- The signers of a chain, in signing order. -/
def Chain.signers (ch : Chain P V) : List P := ch.links.map Prod.fst

/-- The tokens carried by a chain: the link signatures and the votes of the certificates. -/
def Chain.tokens (ch : Chain P V) : Set (Tok P V) :=
  {k | (∃ j ∈ ch.signers, k = .link j ch.s ch.x) ∨ ∃ l ∈ ch.links, ∃ j ∈ l.2, k = .vote j l.1}

/-- Messages. -/
inductive Msg (P V : Type*) where
  /-- Round `0`: the vote `sign_j(⟨committee, p_i⟩)` (sent by `j` to `i`). -/
  | vote (j i : P)
  /-- Rounds `1 … k+1`: the chains (of all broadcast instances) sent to one receiver. -/
  | chains (S : Finset (Chain P V))
  /-- Round `k+2`: `⟨plurality_i, cc_i⟩` (with the sender `i` whose certificate it is). -/
  | plur (i : P) (v : V) (cc : Finset P)
  deriving DecidableEq

/-- The tokens carried by a message. -/
def Msg.tokens : Msg P V → Set (Tok P V)
  | .vote j i => {.vote j i}
  | .chains S => {k | ∃ ch ∈ S, k ∈ ch.tokens}
  | .plur i _ cc => {k | ∃ j ∈ cc, k = .vote j i}

/-- The signature structure. -/
def auth : Auth P (Msg P V) (Tok P V) := ⟨Tok.signer, Msg.tokens⟩

/-- **Definition 2** (validity). A chain is valid in round `r` if it has length `r`, starts with
its instance `s`, has distinct signers and every link carries a committee certificate
(**Definition 1**: at least `t + 1` voters). -/
def ChainOK (t r : ℕ) (ch : Chain P V) : Prop :=
  ch.links.length = r ∧ ch.signers.head? = some ch.s ∧ ch.signers.Nodup ∧
    ∀ l ∈ ch.links, t + 1 ≤ l.2.card

/-! ### Local steps -/

section Steps

variable [LinearOrder V]

/-- Add the smallest value of `A ∖ X` to `X`, if `|X| < 2`. -/
def add1 (A X : Finset V) : Finset V :=
  if h : (A \ X).Nonempty ∧ X.card < 2 then insert ((A \ X).min' h.1) X else X

/-- Lines 7–9 / 12–13 of Algorithm 6: add values of `A` to `X` while `|X| < 2`. -/
def step (A X : Finset V) : Finset V := add1 A (add1 A X)

theorem subset_add1 (A X : Finset V) : X ⊆ add1 A X := by
  unfold add1; split_ifs
  · exact subset_insert _ _
  · exact subset_rfl

theorem add1_subset (A X : Finset V) : add1 A X ⊆ X ∪ A := by
  unfold add1; split_ifs with h
  · exact insert_subset (mem_union_right _ (mem_sdiff.mp (min'_mem _ h.1)).1) subset_union_left
  · exact subset_union_left

theorem card_add1 (A X : Finset V) (h : X.card ≤ 2) : (add1 A X).card ≤ 2 := by
  unfold add1; split_ifs with h'
  · exact (card_insert_le _ _).trans (by omega)
  · exact h

theorem add1_spec {A X : Finset V} {a : V} (ha : a ∈ A) :
    a ∈ add1 A X ∨ 2 ≤ X.card ∨ (add1 A X).card = X.card + 1 := by
  unfold add1; split_ifs with h
  · right; right
    exact card_insert_of_notMem (mem_sdiff.mp (min'_mem _ h.1)).2
  · by_cases hX : 2 ≤ X.card
    · exact Or.inr (Or.inl hX)
    · left
      by_contra haX
      exact h ⟨⟨a, mem_sdiff.mpr ⟨ha, haX⟩⟩, by omega⟩

theorem subset_step (A X : Finset V) : X ⊆ step A X :=
  (subset_add1 A X).trans (subset_add1 A _)

theorem step_subset (A X : Finset V) : step A X ⊆ X ∪ A := by
  intro a ha
  rcases mem_union.mp (add1_subset A _ ha) with h | h
  · exact add1_subset A X h
  · exact mem_union_right _ h

theorem card_step (A X : Finset V) (h : X.card ≤ 2) : (step A X).card ≤ 2 :=
  card_add1 _ _ (card_add1 _ _ h)

/-- Every value of `A` is in `step A X`, unless `step A X` already has two values. -/
theorem mem_step_or {A X : Finset V} {a : V} (ha : a ∈ A) :
    a ∈ step A X ∨ 2 ≤ (step A X).card := by
  have hs : ∀ Y : Finset V, Y ⊆ add1 A Y := subset_add1 A
  unfold step
  rcases add1_spec (X := X) ha with h | h | h
  · exact Or.inl (hs _ h)
  · exact Or.inr (h.trans (card_le_card ((hs _).trans (hs _))))
  · rcases add1_spec (X := add1 A X) ha with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (h'.trans (card_le_card (hs _)))
    · right; omega

end Steps

/-! ### The algorithm -/

section Alg

variable [Fintype P] [LinearOrder P] [LinearOrder V]

/-- `ch` is a valid round-`r` chain not signed by `p`, received by `p` in a `chains` message. -/
def Got (t r : ℕ) (p : P) (rcv : P → Option (Msg P V)) (ch : Chain P V) : Prop :=
  ∃ q S, rcv q = some (.chains S) ∧ ch ∈ S ∧ ChainOK t r ch ∧ p ∉ ch.signers

open Classical in
/-- The values of the valid round-`r` chains of instance `s` (not signed by `p`) received by
`p` (the set `R_i` of Algorithm 6, by value). -/
noncomputable def accSet (t r : ℕ) (p : P) (rcv : P → Option (Msg P V)) (s : P) : Finset V :=
  univ.biUnion fun q => match rcv q with
    | some (.chains S) =>
      (S.filter fun ch => ch.s = s ∧ ChainOK t r ch ∧ p ∉ ch.signers).image Chain.x
    | _ => ∅

theorem mem_accSet {t r : ℕ} {p : P} {rcv : P → Option (Msg P V)} {s : P} {x : V} :
    x ∈ accSet t r p rcv s ↔ ∃ ch, Got t r p rcv ch ∧ ch.s = s ∧ ch.x = x := by
  classical
  unfold accSet
  simp only [mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq⟩
    cases h : rcv q with
    | none => rw [h] at hq; simp at hq
    | some m =>
      rw [h] at hq
      cases m with
      | vote => simp at hq
      | plur => simp at hq
      | chains S =>
        simp only [mem_image, mem_filter] at hq
        obtain ⟨ch, ⟨hS, hs, hok, hp⟩, rfl⟩ := hq
        exact ⟨ch, ⟨q, S, h, hS, hok, hp⟩, hs, rfl⟩
  · rintro ⟨ch, ⟨q, S, h, hS, hok, hp⟩, hs, rfl⟩
    refine ⟨q, ?_⟩
    rw [h]
    simp only [mem_image, mem_filter]
    exact ⟨ch, ⟨hS, hs, hok, hp⟩, rfl⟩

/-- The links of the chain that `p` relays for a newly added value `x` of instance `s`. -/
noncomputable def relayLinks (t r : ℕ) (p : P) (rcv : P → Option (Msg P V)) (s : P) (x : V) :
    List (P × Finset P) :=
  Classical.epsilon fun l => Got t r p rcv ⟨s, x, l⟩

open Classical in
/-- Line 10 of Algorithm 6: the chains relayed by `p` (one per newly added value), extended by
`p`'s link with its certificate `cc`. -/
noncomputable def relayOut (t r : ℕ) (p : P) (rcv : P → Option (Msg P V)) (X X' : P → Finset V)
    (cc : Finset P) : Finset (Chain P V) :=
  univ.biUnion fun s => (X' s \ X s).image fun x => ⟨s, x, relayLinks t r p rcv s x ++ [(p, cc)]⟩

/-- Local state. -/
structure St (P V : Type*) where
  /-- Input value. -/
  x : V
  /-- Classification vector. -/
  c : P → Bool
  /-- Committee certificate (set of voters), if any. -/
  cc : Option (Finset P)
  /-- `X[s]`: the set `X_i` of the broadcast instance with sender `s`. -/
  X : P → Finset V
  /-- Chains to send in the next round. -/
  out : Finset (Chain P V)
  /-- Decision. -/
  dec : Option V

/-- Return value of Algorithm 6 (lines 14–16): `x` if `X = {x}`, `⊥` (`none`) otherwise. -/
def bbOut (X : Finset V) : Option V :=
  if h : X.card = 1 then some (X.min' (card_pos.mp (by omega))) else none

/-- Line 10 of Algorithm 7: the smallest value other than `⊥` that occurs the largest number of
times among the outputs of the broadcast instances (own input if all are `⊥`). -/
noncomputable def plurality (st : St P V) : V :=
  plurMin (univ.filter fun s => (bbOut (st.X s)).isSome) (fun s => (bbOut (st.X s)).getD st.x) st.x

/-- The value of a valid round-`(k+2)` message from `q` (line 12): `⟨plurality_q, cc_q⟩` with a
committee certificate for `q`. -/
def plurVal (t : ℕ) (q : P) : Option (Msg P V) → Option V
  | some (.plur i v cc) => if i = q ∧ t + 1 ≤ cc.card then some v else none
  | _ => none

/-- Lines 12–13 of Algorithm 7 (own input if no valid message was received). -/
noncomputable def decision (t : ℕ) (x : V) (rcv : P → Option (Msg P V)) : V :=
  plurMin (univ.filter fun q => (plurVal t q (rcv q)).isSome) (fun q => (plurVal t q (rcv q)).getD x)
    x

/-- Line 5 of Algorithm 7: the processes that sent `p` their vote. -/
def voters (p : P) (rcv : P → Option (Msg P V)) : Finset P :=
  univ.filter fun j => rcv j = some (.vote j p)

/-- End of round `0` (lines 4–6 of Algorithm 7, lines 1–4 of Algorithm 6). -/
def trans0 (t : ℕ) (p : P) (st : St P V) (rcv : P → Option (Msg P V)) : St P V :=
  if t + 1 ≤ (voters p rcv).card then
    { st with cc := some (voters p rcv), X := fun s => if s = p then {st.x} else ∅,
              out := {⟨p, st.x, [(p, voters p rcv)]⟩} }
  else st

/-- End of round `r ∈ [1, k+1]` (lines 6–13 of Algorithm 6, for all instances). -/
noncomputable def transBB (t r : ℕ) (p : P) (st : St P V) (rcv : P → Option (Msg P V)) :
    St P V :=
  { st with X := fun s => step (accSet t r p rcv s) (st.X s),
            out := match st.cc with
              | some cc => relayOut t r p rcv st.X (fun s => step (accSet t r p rcv s) (st.X s)) cc
              | none => ∅ }

/-- **Algorithm 7** (with `n` parallel instances of **Algorithm 6** in rounds `1 … k+1`).
Inputs: `(x_i, c_i)`. -/
noncomputable def alg (k t : ℕ) : RoundAlgorithm P (Msg P V) (St P V) (V × (P → Bool)) V where
  init _ xc := ⟨xc.1, xc.2, none, fun _ => ∅, ∅, none⟩
  send r p st q :=
    if r = 0 then (if pos st.c q ≤ 2 * k + 1 then some (.vote p q) else none)
    else if r ≤ k + 1 then (if st.out.Nonempty then some (.chains st.out) else none)
    else if r = k + 2 then st.cc.map fun cc => .plur p (plurality st) cc
    else none
  trans r p st rcv :=
    if r = 0 then trans0 t p st rcv
    else if r ≤ k + 1 then transBB t r p st rcv
    else if r = k + 2 then { st with dec := some (decision t st.x rcv) }
    else st
  decide _ st := st.dec

end Alg

/-! ### Basic facts about executions -/

section Exec

variable [Fintype P] [LinearOrder P] [LinearOrder V] {k t : ℕ} {F : Finset P}
  {inp : P → V × (P → Bool)} (E : RoundRun (alg (P := P) (V := V) k t) F inp)

omit [Fintype P] [LinearOrder P] [LinearOrder V] in
theorem ifn {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

omit [Fintype P] [LinearOrder P] [LinearOrder V] in
theorem ifp {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem send_eq (r : ℕ) (p : P) (st : St P V) (q : P) : (alg k t).send r p st q =
    if r = 0 then (if pos st.c q ≤ 2 * k + 1 then some (.vote p q) else none)
    else if r ≤ k + 1 then (if st.out.Nonempty then some (.chains st.out) else none)
    else if r = k + 2 then st.cc.map fun cc => .plur p (plurality st) cc
    else none := rfl

theorem s_zero' (p : P) : E.s 0 p = ⟨(inp p).1, (inp p).2, none, fun _ => ∅, ∅, none⟩ :=
  E.s_zero p

theorem s_succ' (r : ℕ) (p : P) : E.s (r + 1) p =
    if r = 0 then trans0 t p (E.s r p) (E.rcv r p)
    else if r ≤ k + 1 then transBB t r p (E.s r p) (E.rcv r p)
    else if r = k + 2 then { E.s r p with dec := some (decision t (E.s r p).x (E.rcv r p)) }
    else E.s r p := E.s_succ r p

theorem s_one (p : P) : E.s 1 p = trans0 t p (E.s 0 p) (E.rcv 0 p) := by
  rw [s_succ']; simp

theorem s_succ_bb {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) (p : P) :
    E.s (r + 1) p = transBB t r p (E.s r p) (E.rcv r p) := by
  rw [s_succ', ifn (by omega), ifp h2]

theorem s_succ_dec (p : P) : E.s (k + 3) p =
    { E.s (k + 2) p with dec := some (decision t (E.s (k + 2) p).x (E.rcv (k + 2) p)) } := by
  rw [s_succ', ifn (by omega), ifn (by omega), ifp rfl]

theorem s_succ_late {r : ℕ} (h : k + 2 < r) (p : P) : E.s (r + 1) p = E.s r p := by
  rw [s_succ', ifn (by omega), ifn (by omega), ifn (by omega)]

theorem x_eq (r : ℕ) (p : P) : (E.s r p).x = (inp p).1 := by
  induction r with
  | zero => rw [s_zero']
  | succ r ih =>
    rw [s_succ']
    split_ifs
    · unfold trans0; split_ifs <;> exact ih
    · exact ih
    · exact ih
    · exact ih

theorem c_eq (r : ℕ) (p : P) : (E.s r p).c = (inp p).2 := by
  induction r with
  | zero => rw [s_zero']
  | succ r ih =>
    rw [s_succ']
    split_ifs
    · unfold trans0; split_ifs <;> exact ih
    · exact ih
    · exact ih
    · exact ih

/-- The certificate obtained in round `0` (`cc_i` of line 6). -/
def cert (p : P) : Option (Finset P) := (E.s 1 p).cc

theorem cert_eq (p : P) : cert E p =
    if t + 1 ≤ (voters p (E.rcv 0 p)).card then some (voters p (E.rcv 0 p)) else none := by
  unfold cert; rw [s_one, s_zero']; unfold trans0; split_ifs <;> rfl

theorem cert_some {p : P} {S : Finset P} (h : cert E p = some S) :
    S = voters p (E.rcv 0 p) ∧ t + 1 ≤ S.card := by
  rw [cert_eq] at h
  split_ifs at h with h'
  cases h
  exact ⟨rfl, h'⟩

theorem cc_eq {r : ℕ} (hr : 1 ≤ r) (p : P) : (E.s r p).cc = cert E p := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [s_succ', ifn (by omega)]
    split_ifs <;> exact ih

theorem X_one (p s : P) : (E.s 1 p).X s =
    if (cert E p).isSome ∧ s = p then {(inp p).1} else ∅ := by
  rw [cert_eq]; rw [s_one, s_zero']; unfold trans0
  split_ifs with h1 h2 h2 <;> simp_all

theorem out_one (p : P) : (E.s 1 p).out =
    match cert E p with
    | some S => {⟨p, (inp p).1, [(p, S)]⟩}
    | none => ∅ := by
  rw [cert_eq]; rw [s_one, s_zero']; unfold trans0
  split_ifs <;> rfl

theorem X_zero (p s : P) : (E.s 0 p).X s = ∅ := by rw [s_zero']

theorem out_zero (p : P) : (E.s 0 p).out = ∅ := by rw [s_zero']

theorem X_succ_bb {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) (p s : P) :
    (E.s (r + 1) p).X s = step (accSet t r p (E.rcv r p) s) ((E.s r p).X s) := by
  rw [s_succ_bb E h1 h2]; rfl

theorem out_succ_bb {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) (p : P) :
    (E.s (r + 1) p).out = match cert E p with
      | some cc => relayOut t r p (E.rcv r p) (E.s r p).X
          (fun s => step (accSet t r p (E.rcv r p) s) ((E.s r p).X s)) cc
      | none => ∅ := by
  rw [s_succ_bb E h1 h2, ← cc_eq E h1]; rfl

theorem X_late {r : ℕ} (hr : k + 2 ≤ r) (p : P) : (E.s r p).X = (E.s (k + 2) p).X := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [s_succ', ifn (by omega), ifn (by omega)]
    split_ifs <;> exact ih

theorem out_late {r : ℕ} (hr : k + 2 ≤ r) (p : P) : (E.s r p).out = (E.s (k + 2) p).out := by
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    rw [s_succ', ifn (by omega), ifn (by omega)]
    split_ifs <;> exact ih

theorem dec_early {r : ℕ} (hr : r ≤ k + 2) (p : P) : (E.s r p).dec = none := by
  induction r with
  | zero => rw [s_zero']
  | succ r ih =>
    rw [s_succ']
    split_ifs with h0 h1 h2
    · unfold trans0; split_ifs <;> exact ih (by omega)
    · exact ih (by omega)
    · omega
    · exact ih (by omega)

theorem dec_eq {r : ℕ} (hr : k + 3 ≤ r) (p : P) :
    (E.s r p).dec = some (decision t (inp p).1 (E.rcv (k + 2) p)) := by
  induction r, hr using Nat.le_induction with
  | base => rw [s_succ_dec, x_eq]
  | succ r hr ih => rw [s_succ_late E (by omega), ih]

end Exec

end BAWithPredictions.AuthBA
