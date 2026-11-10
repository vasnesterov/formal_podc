import Papers.PODC2012.OrderPreservingByzRenaming.ConstTime

/-!
# Algorithm 2 of arXiv:1205.0477v1/v2 (order-preserving renaming for `N > 3t`)

A `LockStep` state machine on `Fin n` (as in `Alg5.lean`):

* Epoch 1 (LockStep rounds 0, 1): Algorithm 1 (ids, echoes; `counter`, `newId`, the known ids `V`);
  `minOffset[id] := max(counter − t, 0)` (Lines 04–05).
* Vote epochs `k = 1, …, K` (rounds `2k`, `2k + 1`): Round 1 broadcast `vote(V)` (the list of
  `⟨id, newId⟩`); Round 2 echo every vote received; then process: a vote `vᵢ` received on link `i`
  is used iff it was echoed (same content) by at least `N − t` links and `isValid(vᵢ, Skew)`
  (Algorithm 4). For every `id ∈ V`, `proposedNewIds` collects `vᵢ[id]` (or `predecessorNewId(vᵢ, id)`
  if `id ∉ vᵢ`), and `newId := avg(proposedNewIds)` (Algorithm 5). The first vote epoch is
  Algorithm 6, which also recomputes `minOffset` from the offsets of the accepted votes.
* `Skew` of vote epoch `k` is `3t² (2t/N)^(k-1)`. The output is
  `⌈newId[my id] / (N − t − Skew)⌉` with the final `Skew = 3t² (2t/N)^K`.

arXiv v2 has `K = 4⌈log t⌉ + 2` vote epochs (epoch 2: Algorithm 6, epochs `3, …, 4⌈log t⌉ + 3`:
Algorithm 5). arXiv v1 has a separate local epoch for the minimum offsets and one vote epoch less
(`K = 4⌈log t⌉ + 1`). Both are instances of `alg2 n t K`.
-/

namespace Podc.OrderPreservingByzRenaming.Alg2

open Cslib.Byzantine.LockStep

/-- Messages: epoch 1 uses Algorithm 1's messages; then votes and echoed votes. -/
inductive Msg
  | base (m : TwoRound.Msg)
  | vote (v : List (ℕ × ℚ))
  | echoVotes (vs : List (List (ℕ × ℚ)))

/-- Local state. -/
structure St (n : ℕ) where
  /-- The Round-1 inbox of Algorithm 1 (own message included). -/
  ib1 : Fin n → Option TwoRound.Msg := fun _ => none
  /-- The known ids `V`, increasing. -/
  ids : List ℕ := []
  counter : ℕ → ℕ := fun _ => 0
  newId : ℕ → ℚ := fun _ => 0
  minOff : ℕ → ℚ := fun _ => 0
  /-- The votes received in the first round of the current vote epoch, per link. -/
  votes : Fin n → Option (List (ℕ × ℚ)) := fun _ => none

variable (n t : ℕ)

/-- The Algorithm-1 message carried by a message (if any). -/
def baseOf : Option Msg → Option TwoRound.Msg
  | some (.base m) => some m
  | _ => none

/-- An increasing list of the elements of a finset of naturals. -/
def sortedOf (S : Finset ℕ) : List ℕ := (List.range (S.sup id + 1)).filter (· ∈ S)

/-- `predecessorNewId(v, id)` (Algorithm 3): the value of the largest id `< id` in `v`, or `0`. -/
def pred (v : List (ℕ × ℚ)) (i : ℕ) : ℚ :=
  match ((v.map Prod.fst).filter (· < i)).max? with
  | some k => (v.lookup k).getD 0
  | none => 0

/-- The value used for `id` from the vote `v` (`v[id]`, or the predecessor's value). -/
def valOf (v : List (ℕ × ℚ)) (i : ℕ) : ℚ := (v.lookup i).getD (pred v i)

/-- `isValid(v, Skew)` (Algorithm 4), at a process in state `st`. -/
def IsValid (st : St n) (v : List (ℕ × ℚ)) (skew : ℚ) : Prop :=
  ∀ i ∈ st.ids, valOf v i ≤ n ^ 2 + n * t ∧ |valOf v i - st.newId i| ≤ skew ∧
    st.minOff i ≤ valOf v i - pred v i

instance (st : St n) (v : List (ℕ × ℚ)) (skew : ℚ) : Decidable (IsValid n t st v skew) := by
  unfold IsValid; infer_instance

/-- Average of a list (`0` for the empty list). -/
def avg (l : List ℚ) : ℚ := l.sum / l.length

/-- The Skew used in vote epoch `k` (from `1`): `3t² (2t/N)^(k-1)`; `skew n t (K + 1)` is final. -/
def skew (k : ℕ) : ℚ := 3 * t ^ 2 * (2 * t / n) ^ (k - 1)

/-- `vote(V)`. -/
def voteOf (st : St n) : List (ℕ × ℚ) := st.ids.map fun i => (i, st.newId i)

/-- What a process broadcasts in round `r` (from `0`). -/
def out (x : ℕ) (st : St n) (r : ℕ) : Option Msg :=
  match r with
  | 0 => some (.base (.ident x))
  | 1 => some (.base (.echo (TwoRound.timely st.ib1)))
  | r + 2 => if r % 2 = 0 then some (.vote (voteOf n st))
      else some (.echoVotes ((List.finRange n).filterMap st.votes))

/-- Whether a message is an echo containing the vote `v`. -/
def echoHas (m : Option Msg) (v : List (ℕ × ℚ)) : Bool :=
  match m with
  | some (.echoVotes vs) => decide (v ∈ vs)
  | _ => false

/-- Number of links that echoed the vote `v`. -/
def echoCount (ib : Fin n → Option Msg) (v : List (ℕ × ℚ)) : ℕ :=
  (Finset.univ.filter fun j => echoHas (ib j) v = true).card

/-- The accepted votes of a vote epoch with skew `sk`. -/
def accVotes (st : St n) (ib : Fin n → Option Msg) (sk : ℚ) : List (List (ℕ × ℚ)) :=
  (List.finRange n).filterMap fun i => match st.votes i with
    | some v => if n - t ≤ echoCount n ib v ∧ IsValid n t st v sk then some v else none
    | none => none

/-- Lines 18–24 of Algorithm 6: the new `minOffset` of an id from the offsets of accepted votes. -/
def newMinOff (st : St n) (A : List (List (ℕ × ℚ))) (i : ℕ) : ℚ :=
  if t < st.counter i then
    let o := A.map fun v => match v.lookup i with
      | some y => y - pred v i
      | none => 0
    let miss := n - o.length
    let o' := (o ++ List.replicate miss (max ((st.counter i : ℚ) - 2 * t) 0)).insertionSort (· ≤ ·)
    let o'' := o'.take (o'.length - (t - miss))
    min (st.counter i : ℚ) (avg o'')
  else st.minOff i

/-- The state transition of round `r` with the full inbox `ib` (own message included). -/
def step (r : ℕ) (st : St n) (ib : Fin n → Option Msg) : St n :=
  match r with
  | 0 => { st with ib1 := fun j => baseOf (ib j) }
  | 1 =>
    let ib2 : Fin n → Option TwoRound.Msg := fun j => baseOf (ib j)
    let cnt := TwoRound.counter t st.ib1 ib2
    let ids := sortedOf (TwoRound.timely st.ib1 ∪ TwoRound.accepted t st.ib1 ib2)
    { st with
      ids := ids
      counter := cnt
      newId := fun i => (((ids.filter (· ≤ i)).map fun z => ConstTime.off n t (cnt z)).sum : ℕ)
      minOff := fun i => ((cnt i - t : ℕ) : ℚ) }
  | r + 2 =>
    if r % 2 = 0 then
      { st with votes := fun j => match ib j with
          | some (.vote v) => some v
          | _ => none }
    else
      let A := accVotes n t st ib (skew n t (r / 2 + 1))
      { st with
        newId := fun i => avg (A.map fun v => valOf v i)
        minOff := if r / 2 = 0 then newMinOff n t st A else st.minOff }

/-- The state after a history. -/
def stateOf (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) : St n :=
  (h.foldl (fun (a : ℕ × St n) ib =>
    (a.1 + 1, step n t a.1 a.2 (Function.update ib p (out n x a.2 a.1)))) (0, {})).2

/-- **Algorithm 2** with `K` vote epochs, as a `LockStep` protocol. -/
def alg2 (K : ℕ) : Protocol (Fin n) ℕ Msg ℕ where
  send p x h _ := out n x (stateOf n t p x h) h.length
  decide p x h :=
    if h.length = 2 * K + 2 then
      some (Int.ceil ((stateOf n t p x h).newId x / (n - t - skew n t (K + 1)))).toNat
    else none

lemma alg2_decide (K : ℕ) (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) :
    (alg2 n t K).decide p x h = if h.length = 2 * K + 2 then
      some (Int.ceil ((stateOf n t p x h).newId x / (n - t - skew n t (K + 1)))).toNat
    else none := rfl

/-! ### Runs -/

/-- The states of a run with Byzantine set `F`. -/
def run (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) :
    ℕ → Fin n → St n
  | 0, _ => {}
  | r + 1, p => step n t r (run F x adv r p) fun j =>
      if j = p then out n (x p) (run F x adv r p) r
      else if j ∈ F then adv r j p else out n (x j) (run F x adv r j) r

lemma stateOf_append (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) (ib : Inbox (Fin n) Msg) :
    stateOf n t p x (h ++ [ib]) =
      step n t h.length (stateOf n t p x h)
        (Function.update ib p (out n x (stateOf n t p x h) h.length)) := by
  have key : ∀ (h : History (Fin n) Msg) (a : ℕ × St n),
      (h.foldl (fun (a : ℕ × St n) ib =>
        (a.1 + 1, step n t a.1 a.2 (Function.update ib p (out n x a.2 a.1)))) a).1 =
        a.1 + h.length := by
    intro h
    induction h with
    | nil => intro a; simp
    | cons b h ih => intro a; simp [ih]; omega
  unfold stateOf
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [key]; simp

variable {n t}

/-- **Run lemma**: honest processes are in the states `run` predicts. -/
theorem stateOf_hist {K : ℕ} {s : Scenario (Fin n) ℕ Msg} (hs : s.Reliable) {F : Finset (Fin n)}
    (hF : ∀ j, j ∈ s.byz ↔ j ∈ F) :
    ∀ r p, p ∉ s.byz →
      stateOf n t p (s.input p) (hist ⊤ (alg2 n t K) s r p) = run n t F s.input s.adv r p := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [hist_succ, stateOf_append, length_hist, ih p hp, run]
    congr 1
    funext j
    by_cases hj : j = p
    · subst hj; simp
    · rw [Function.update_of_ne hj]
      have hadj : (⊤ : SimpleGraph (Fin n)).Adj j p := by simpa using hj
      by_cases hb : j ∈ s.byz
      · simp [deliver, hadj, hb, hj, (hF j).1 hb]
      · have hjF : j ∉ F := fun h => hb ((hF j).2 h)
        simp only [deliver, hadj, hb, hj, hjF, hs r j p, if_true, if_false]
        show out n (s.input j) (stateOf n t j (s.input j) (hist ⊤ (alg2 n t K) s r j))
          (hist ⊤ (alg2 n t K) s r j).length = _
        rw [length_hist]
        exact congrArg (fun st => out n (s.input j) st r) (ih j hb)

/-- An honest process decides after `2K + 2` rounds, on `⌈newId[my id] / (N − t − Skew)⌉`. -/
theorem decides_iff {K : ℕ} {s : Scenario (Fin n) ℕ Msg} (hs : s.Reliable) {F : Finset (Fin n)}
    (hF : ∀ j, j ∈ s.byz ↔ j ∈ F) {p : Fin n} (hp : p ∉ s.byz) (o : ℕ) :
    Decides ⊤ (alg2 n t K) s p o ↔
      o = (Int.ceil ((run n t F s.input s.adv (2 * K + 2) p).newId (s.input p) /
        (n - t - skew n t (K + 1)))).toNat := by
  rw [decides_iff_firstSome, firstSome_iff_of_ne (2 * K + 2)]
  · simp only [status]
    rw [alg2_decide, length_hist, if_pos rfl, stateOf_hist hs hF _ p hp]
    simp [eq_comm]
  · intro r hr
    simp only [status]
    rw [alg2_decide, length_hist, if_neg hr]

end Podc.OrderPreservingByzRenaming.Alg2
