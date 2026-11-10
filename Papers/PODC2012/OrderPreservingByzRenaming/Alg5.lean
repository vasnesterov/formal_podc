import Papers.PODC2012.OrderPreservingByzRenaming.Spec

/-!
# Algorithm 5: id selection + parallel approximate agreements (§6.1)

Algorithm 5 (with the procedures `isValid`, Algorithm 6, and `approximate`, Algorithm 7) as a
`LockStep` protocol on `Fin n`, as a state machine over the history. LockStep round `r` (counting
from `0`) is the paper's Round `r + 1`. A process receives its own broadcast through the self-loop
(link `n` in the paper); here it adds its own message to its inbox (`Function.update`).

* Round 1: broadcast `⟨ID, my id⟩`; `Ids` := ids received.
* Round 2: broadcast `⟨Echo, id⟩` for `id ∈ Ids`; the ids echoed by at least `n - t` links are
  "considered for the following round" (text of §6.1.1; see `differencies.md` for the pseudocode,
  which keeps the Round-1 ids in `Ids`).
* Round 3: broadcast `⟨Ready, id⟩` for these ids; `timely` := ids with `≥ n - t` Ready messages,
  `accepted` := ids with `≥ n - 2t`; `ranks[id] := rank(accepted, id) · δ`, `δ = 1 + 1/(3(n+t))`.
* Rounds `≥ 4`: broadcast `⟨AA, ranks⟩` (the domain of `ranks` is `accepted`); keep the votes
  `R` with `isValid(timely, R)` (both ids of every pair `id < id'` of `timely` are in `R` and
  `R[id'] - R[id] ≥ δ`), and run `approximate`: `votes[id]` = multiset of the valid votes for `id`;
  `accepted := {id ∈ accepted : |votes[id]| ≥ n - t}`; for these ids fill `votes[id]` up to `n`
  with the own value, drop the `t` largest and `t` smallest, and average `select_t` of the rest.
* After `L` rounds (paper: `L = 2⌈log t⌉ + 8`; §6.2: `L = 7`) return `round(ranks[my id])`.

The choice function `select_t` is a parameter `sel`; `selPaper` is the formula of §6.1.2 (elements
`it + 1`, `0 ≤ i < ⌊|set|/t⌋`), `selDLPSW` the one of Dolev et al. (elements `it + 1` while
`it < |set|`, i.e. "the smallest and each `t`-th element after it").
-/

namespace Podc.OrderPreservingByzRenaming.Alg5

open Cslib.Byzantine.LockStep

/-- Messages of Algorithm 5 (the Echo/Ready messages of a round are bundled per link). -/
inductive Msg
  | ident (v : ℕ)
  | echo (s : Finset ℕ)
  | ready (s : Finset ℕ)
  /-- `⟨AA, ranks⟩`: the domain and the values of `ranks`. -/
  | aa (dom : Finset ℕ) (val : ℕ → ℚ)

/-- Local state. -/
structure St where
  /-- `Ids` after Round 1. -/
  ids : Finset ℕ := ∅
  /-- The ids echoed by at least `n - t` links in Round 2 (broadcast in Round 3). -/
  rdy : Finset ℕ := ∅
  timely : Finset ℕ := ∅
  /-- `accepted` = the domain of `ranks`. -/
  acc : Finset ℕ := ∅
  /-- The values of `ranks`. -/
  val : ℕ → ℚ := fun _ => 0

/-- The stretch factor `δ = 1 + 1/(3(n+t))`. -/
def δ (n t : ℕ) : ℚ := 1 + 1 / (3 * (n + t))

/-- What a process broadcasts in round `r` (from `0`). -/
def out (x : ℕ) (st : St) (r : ℕ) : Option Msg :=
  match r with
  | 0 => some (.ident x)
  | 1 => some (.echo st.ids)
  | 2 => some (.ready st.rdy)
  | _ => some (.aa st.acc st.val)

/-- `isValid(timely, R)` (Algorithm 6). -/
def IsValid (n t : ℕ) (timely dom : Finset ℕ) (val : ℕ → ℚ) : Prop :=
  ∀ a ∈ timely, ∀ b ∈ timely, a < b → a ∈ dom ∧ b ∈ dom ∧ δ n t ≤ val b - val a

instance (n t : ℕ) (timely dom : Finset ℕ) (val : ℕ → ℚ) : Decidable (IsValid n t timely dom val) := by
  unfold IsValid; infer_instance

/-- `select_t` as in §6.1.2: elements with (0-based) index `i t` for `0 ≤ i < ⌊|l|/t⌋`. -/
def selPaper (t : ℕ) (l : List ℚ) : List ℚ :=
  (List.range (l.length / t)).filterMap fun i => l[i * t]?

/-- `select_t` of Dolev et al.: elements with index `i t < |l|` (the smallest and every `t`-th
after it). -/
def selDLPSW (t : ℕ) (l : List ℚ) : List ℚ :=
  (List.range l.length).filterMap fun i => if i % t = 0 then l[i]? else none

/-- Average of a list (`0` for the empty list). -/
def avg (l : List ℚ) : ℚ := l.sum / l.length

variable (n t : ℕ) (sel : ℕ → List ℚ → List ℚ)

/-- The valid votes of round `r ≥ 3` (Algorithm 5, Lines 25–27). -/
def validVotes (timely : Finset ℕ) (ib : Fin n → Option Msg) : List (Finset ℕ × (ℕ → ℚ)) :=
  (List.finRange n).filterMap fun j =>
    match ib j with
    | some (.aa d f) => if IsValid n t timely d f then some (d, f) else none
    | _ => none

/-- `votes[id]`: the multiset (list) of valid votes for `id`. -/
def votesFor (V : List (Finset ℕ × (ℕ → ℚ))) (id : ℕ) : List ℚ :=
  V.filterMap fun R => if id ∈ R.1 then some (R.2 id) else none

/-- Lines 9–16 of `approximate` for one id: fill with the own value up to `n`, remove the `t`
largest and `t` smallest values, average `select_t` of the rest. -/
def newVal (mine : ℚ) (vs : List ℚ) : ℚ :=
  avg (sel t (((vs ++ List.replicate (n - vs.length) mine).insertionSort (· ≤ ·)).drop t |>.take
    (n - 2 * t)))

/-- Number of links on which `v` is in the set carried by the message. -/
def cnt (sets : Fin n → Finset ℕ) (v : ℕ) : ℕ := (Finset.univ.filter fun j => v ∈ sets j).card

/-- The id carried by a Round-1 message. -/
def identOf : Option Msg → Finset ℕ
  | some (.ident v) => {v}
  | _ => ∅

/-- The set carried by an Echo message. -/
def echoOf : Option Msg → Finset ℕ
  | some (.echo s) => s
  | _ => ∅

/-- The set carried by a Ready message. -/
def readyOf : Option Msg → Finset ℕ
  | some (.ready s) => s
  | _ => ∅

/-- The ids carried by at least `k` of the sets. -/
def atLeast (sets : Fin n → Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.univ.biUnion sets).filter fun v => k ≤ cnt n sets v

/-- The state transition of round `r` with the full inbox `ib` (own message included). -/
def step (r : ℕ) (st : St) (ib : Fin n → Option Msg) : St :=
  match r with
  | 0 => { st with ids := Finset.univ.biUnion fun j => identOf (ib j) }
  | 1 => { st with rdy := atLeast n (fun j => echoOf (ib j)) (n - t) }
  | 2 =>
    { st with
      timely := atLeast n (fun j => readyOf (ib j)) (n - t)
      acc := atLeast n (fun j => readyOf (ib j)) (n - 2 * t)
      val := fun v =>
        (((atLeast n (fun j => readyOf (ib j)) (n - 2 * t)).filter (· ≤ v)).card : ℚ) * δ n t }
  | _ =>
    { st with
      acc := st.acc.filter fun id => n - t ≤ (votesFor (validVotes n t st.timely ib) id).length
      val := fun id => newVal n t sel (st.val id) (votesFor (validVotes n t st.timely ib) id) }

/-- The state after a history (the round number is the length of the history). -/
def stateOf (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) : St :=
  (h.foldl (fun (a : ℕ × St) ib =>
    (a.1 + 1, step n t sel a.1 a.2 (Function.update ib p (out x a.2 a.1)))) (0, {})).2

/-- **Algorithm 5** as a `LockStep` protocol, deciding after `L` rounds. -/
def alg (L : ℕ) : Protocol (Fin n) ℕ Msg ℕ where
  send p x h _ := out x (stateOf n t sel p x h) h.length
  decide p x h :=
    if h.length = L then
      let st := stateOf n t sel p x h
      if x ∈ st.acc then some (round (st.val x)).toNat else none
    else none

/-! ### Runs -/

/-- The states of a run with Byzantine set `F` (honest processes follow the algorithm; the
states of Byzantine processes are irrelevant). -/
def run (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) :
    ℕ → Fin n → St
  | 0, _ => {}
  | r + 1, p => step n t sel r (run F x adv r p) fun j =>
      if j = p then out (x p) (run F x adv r p) r
      else if j ∈ F then adv r j p else out (x j) (run F x adv r j) r

lemma stateOf_append (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) (ib : Inbox (Fin n) Msg) :
    stateOf n t sel p x (h ++ [ib]) =
      step n t sel h.length (stateOf n t sel p x h)
        (Function.update ib p (out x (stateOf n t sel p x h) h.length)) := by
  have key : ∀ (h : History (Fin n) Msg) (a : ℕ × St),
      (h.foldl (fun (a : ℕ × St) ib =>
        (a.1 + 1, step n t sel a.1 a.2 (Function.update ib p (out x a.2 a.1)))) a).1 =
        a.1 + h.length := by
    intro h
    induction h with
    | nil => intro a; simp
    | cons b h ih => intro a; simp [ih]; omega
  unfold stateOf
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [key]; simp

variable {n t sel}

/-- **Run lemma**: honest processes are in the states `run` predicts. -/
theorem stateOf_hist {L : ℕ} {s : Scenario (Fin n) ℕ Msg} (hs : s.Reliable) {F : Finset (Fin n)}
    (hF : ∀ j, j ∈ s.byz ↔ j ∈ F) :
    ∀ r p, p ∉ s.byz →
      stateOf n t sel p (s.input p) (hist ⊤ (alg n t sel L) s r p) = run n t sel F s.input s.adv r p := by
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
        show out (s.input j) (stateOf n t sel j (s.input j) (hist ⊤ (alg n t sel L) s r j))
          (hist ⊤ (alg n t sel L) s r j).length = _
        rw [length_hist]
        exact congrArg (fun st => out (s.input j) st r) (ih j hb)

/-- An honest process decides only after `L` rounds, and only if its own id is still in
`accepted`. -/
theorem not_decides_of_not_mem {L : ℕ} {s : Scenario (Fin n) ℕ Msg} (hs : s.Reliable)
    {F : Finset (Fin n)} (hF : ∀ j, j ∈ s.byz ↔ j ∈ F) {p : Fin n} (hp : p ∉ s.byz)
    (h : s.input p ∉ (run n t sel F s.input s.adv L p).acc) (o : ℕ) :
    ¬ Decides ⊤ (alg n t sel L) s p o := by
  rintro ⟨r, hr, -⟩
  simp only [status, alg, length_hist] at hr
  split_ifs at hr with h1 h2
  subst h1
  rw [← stateOf_hist (L := r) hs hF r p hp] at h
  exact h h2

/-- `accepted` only shrinks during the approximation phase. -/
lemma run_acc_subset (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg)
    {r : ℕ} (hr : 3 ≤ r) (p : Fin n) :
    (run n t sel F x adv (r + 1) p).acc ⊆ (run n t sel F x adv r p).acc := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  simp only [run, step]
  exact Finset.filter_subset _ _

lemma run_acc_mono (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg)
    {r r' : ℕ} (hr : 3 ≤ r) (hrr : r ≤ r') (p : Fin n) :
    (run n t sel F x adv r' p).acc ⊆ (run n t sel F x adv r p).acc := by
  induction r', hrr using Nat.le_induction with
  | base => exact le_rfl
  | succ r' hr' ih => exact (run_acc_subset F x adv (by omega) p).trans ih

end Podc.OrderPreservingByzRenaming.Alg5
