import Papers.PODC2016.UniformDeploymentRings.Model
import Papers.PODC2016.UniformDeploymentRings.Alg1Targets

/-!
# Algorithm 1 and Theorem 3

Algorithm 1 of [Shibata et al., PODC 2016] (with the extension of Section 3.1.1 to `n ≠ ck`), as
an `Algorithm` of our model, for agents that know `k`:

* *selection phase*: release the token at the home node, then walk once around the ring (until
  `k` token nodes have been seen), recording the distances `D` between consecutive token nodes;
* *deployment phase*: move `moves1 D` more times (`disBase` to the base node, then the offset of
  the target, `rank × n/k` when `k ∣ n`) and halt.

We prove Theorem 3 (correctness): in every fair execution from every initial configuration all
agents halt, and then they are uniformly deployed (`theorem_3`). Each agent performs exactly
`n + moves1 (D) < 3n` moves (`alg1_moves_lt`), so the total number of moves is `< 3kn = O(kn)`.

The proof follows each agent along its (schedule-independent) trajectory `traj`: the only
interaction is through tokens, and an agent reaching the home node of another agent always finds
its token there, because every agent starts in the incoming buffer of its home node and links are
FIFO (`Inv`, field `head`).
-/

namespace Podc.UniformDeploymentRings

open Function

/-- States of Algorithm 1. -/
inductive A1State
  /-- initial state (at the home node, holding the token) -/
  | init
  /-- selection phase: `dis` moves since the last token node, distances `D` recorded so far -/
  | sel (dis : ℕ) (D : List ℕ)
  /-- deployment phase: `r` more moves after the current one -/
  | dep (r : ℕ)
  /-- halt state -/
  | halt
  deriving DecidableEq

/-- One atomic action of Algorithm 1: the new state and whether the agent leaves, given whether
the current node holds a token. -/
def a1next (k : ℕ) : A1State → Bool → A1State × Bool
  | .init, _ => (.sel 0 [], true)
  | .sel dis D, tk =>
    if tk then
      if (D ++ [dis + 1]).length = k then
        if moves1 (D ++ [dis + 1]) = 0 then (.halt, false)
        else (.dep (moves1 (D ++ [dis + 1]) - 1), true)
      else (.sel 0 (D ++ [dis + 1]), true)
    else (.sel (dis + 1) D, true)
  | .dep r, _ => if r = 0 then (.halt, false) else (.dep (r - 1), true)
  | .halt, _ => (.halt, false)

/-- Algorithm 1 for agents knowing the number `k` of agents. The token is released in the first
action (state `init`); no messages are used. -/
def alg1 (k : ℕ) : Algorithm where
  S := A1State
  M := Unit
  init := .init
  halted s := decide (s = .halt)
  act s _ tok _ :=
    ⟨(a1next k s (decide (0 < tok))).1, decide (s = .init), none, (a1next k s (decide (0 < tok))).2⟩

/-! ### The trajectory of one agent -/

variable {n : ℕ} (k : ℕ) (H : Finset (ZMod n)) (h : ZMod n)

/-- The state of the agent with home `h` after `p` actions, when it finds a token exactly at the
home nodes `H`. Action `p + 1` takes place at node `h + p`. -/
def traj : ℕ → A1State
  | 0 => .init
  | p + 1 => (a1next k (traj p) (decide (h + (p : ZMod n) ∈ H))).1

/-- Whether the agent leaves in its action `p + 1`. -/
def trajMove (p : ℕ) : Bool := (a1next k (traj k H h p) (decide (h + (p : ZMod n) ∈ H))).2

/-- Number of actions of the agent until it halts: one at home, `n` arrivals around the ring,
then `moves1 D` more arrivals. -/
def lifetime : ℕ := n + 1 + moves1 (distSeq H h)

variable [NeZero n] {k H h}

theorem take_succ_distSeq (hh : h ∈ H) {j : ℕ} (hj : j < H.card) :
    (distSeq H h).take (j + 1) = (distSeq H h).take j ++ [pos H h (j + 1) - pos H h j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj)]
  congr
  simp [distSeq_eq_map_step hh, homeGap]

theorem traj_sel (hh : h ∈ H) (hk : H.card = k) :
    ∀ p < n, ∃ j < k, pos H h j ≤ p ∧ p < pos H h (j + 1) ∧
      traj k H h (p + 1) = .sel (p - pos H h j) ((distSeq H h).take j) := by
  have hk0 : 0 < k := hk ▸ card_pos_of_mem hh
  have hmono := pos_strictMono hh
  intro p hp
  induction p with
  | zero =>
    have h01 := hmono (show 0 < 1 by norm_num)
    rw [pos_zero hh] at h01
    refine ⟨0, hk0, by rw [pos_zero hh], by simpa using h01, ?_⟩
    simp [traj, a1next, pos_zero hh]
  | succ p ih =>
    obtain ⟨j, hj, h1, h2, h3⟩ := ih (by omega)
    have hpj : pos H h j < p + 1 := by omega
    have hstep : traj k H h (p + 1 + 1) =
        (a1next k (traj k H h (p + 1)) (decide (h + ((p + 1 : ℕ) : ZMod n) ∈ H))).1 := rfl
    by_cases hhome : h + ((p + 1 : ℕ) : ZMod n) ∈ H
    · have heq : p + 1 = pos H h (j + 1) := by
        by_contra hne
        exact not_isHomeAt_of_lt_pos_succ j (p + 1) hpj (by omega) hhome
      have hjk : j + 1 < k := by
        by_contra hjk
        have : j + 1 = k := by omega
        rw [this, pos_card hh hk] at heq; omega
      have hj2 : pos H h (j + 1) < pos H h (j + 1 + 1) := hmono (by omega)
      refine ⟨j + 1, hjk, heq.ge, by omega, ?_⟩
      have htake := take_succ_distSeq hh (show j < H.card by omega)
      have hdis : p - pos H h j + 1 = pos H h (j + 1) - pos H h j := by omega
      rw [hstep, h3]
      simp only [a1next, hhome, decide_true, ↓reduceIte, hdis, ← htake,
        List.length_take, length_distSeq, hk, min_eq_left (by omega : j + 1 ≤ k)]
      simp [show j + 1 ≠ k by omega, heq]
    · have hne : p + 1 ≠ pos H h (j + 1) := by
        intro he; apply hhome; rw [he]; exact pos_mem hh _
      refine ⟨j, hj, by omega, by omega, ?_⟩
      rw [hstep, h3]
      simp only [a1next, hhome, decide_false, Bool.false_eq_true, ↓reduceIte]
      congr 1; omega

theorem traj_circuit (hh : h ∈ H) (hk : H.card = k) :
    traj k H h (n + 1) = (if moves1 (distSeq H h) = 0 then .halt
      else .dep (moves1 (distSeq H h) - 1)) ∧
    trajMove k H h n = decide (moves1 (distSeq H h) ≠ 0) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmono := pos_strictMono hh
  obtain ⟨j, hj, h1, h2, h3⟩ := traj_sel hh hk (n - 1) (by omega)
  have hhome : h + ((n : ℕ) : ZMod n) ∈ H := by simpa using hh
  have heq : n = pos H h (j + 1) := by
    by_contra hne
    exact not_isHomeAt_of_lt_pos_succ j n (by omega) (by omega) hhome
  have hjk : j + 1 = k := by
    have hpk := pos_card hh hk
    have : pos H h k = pos H h (j + 1) := by omega
    exact (hmono.injective this).symm
  have htake := take_succ_distSeq hh (show j < H.card by omega)
  have hdis : n - 1 - pos H h j + 1 = pos H h (j + 1) - pos H h j := by omega
  have hD : (distSeq H h).take j ++ [n - 1 - pos H h j + 1] = distSeq H h := by
    rw [hdis, ← htake, hjk, ← hk, ← length_distSeq H h, List.take_length]
  have hlen : (distSeq H h).length = k := by rw [length_distSeq, hk]
  have e1 : traj k H h n = traj k H h (n - 1 + 1) := congrArg _ (by omega)
  have key : a1next k (traj k H h n) (decide (h + ((n : ℕ) : ZMod n) ∈ H)) =
      (if moves1 (distSeq H h) = 0 then (A1State.halt, false)
        else (A1State.dep (moves1 (distSeq H h) - 1), true)) := by
    rw [e1, h3]
    simp only [a1next, hhome, decide_true, ↓reduceIte, hD, hlen]
  constructor
  · show (a1next k (traj k H h n) (decide (h + ((n : ℕ) : ZMod n) ∈ H))).1 = _
    rw [key]; split_ifs <;> rfl
  · show (a1next k (traj k H h n) (decide (h + ((n : ℕ) : ZMod n) ∈ H))).2 = _
    rw [key]; split_ifs <;> simp_all

theorem traj_dep (hh : h ∈ H) (hk : H.card = k) (i : ℕ) :
    traj k H h (n + 1 + i) = (if moves1 (distSeq H h) ≤ i then .halt
      else .dep (moves1 (distSeq H h) - 1 - i)) := by
  induction i with
  | zero =>
    rw [(traj_circuit hh hk).1]; simp
  | succ i ih =>
    rw [← add_assoc, traj, ih]
    by_cases h1 : moves1 (distSeq H h) ≤ i
    · simp [h1, a1next, show moves1 (distSeq H h) ≤ i + 1 by omega]
    · by_cases h2 : moves1 (distSeq H h) ≤ i + 1
      · simp [h1, h2, a1next, show moves1 (distSeq H h) - 1 - i = 0 by omega]
      · simp [h1, h2, a1next, show moves1 (distSeq H h) - 1 - i ≠ 0 by omega]
        omega

theorem traj_lifetime_le (hh : h ∈ H) (hk : H.card = k) {p : ℕ} (hp : lifetime H h ≤ p) :
    traj k H h p = .halt := by
  unfold lifetime at hp
  obtain ⟨i, rfl⟩ : ∃ i, p = n + 1 + i := ⟨p - (n + 1), by omega⟩
  rw [traj_dep hh hk]; simp; omega

theorem traj_ne_halt (hh : h ∈ H) (hk : H.card = k) {p : ℕ} (hp : p < lifetime H h) :
    traj k H h p ≠ .halt := by
  unfold lifetime at hp
  rcases Nat.lt_or_ge p (n + 1) with hp1 | hp1
  · rcases p with _ | p
    · simp [traj]
    · obtain ⟨j, -, -, -, h3⟩ := traj_sel hh hk p (by omega)
      rw [h3]; simp
  · obtain ⟨i, rfl⟩ : ∃ i, p = n + 1 + i := ⟨p - (n + 1), by omega⟩
    rw [traj_dep hh hk]; simp; omega

theorem trajMove_eq (hh : h ∈ H) (hk : H.card = k) {p : ℕ} (hp : p < lifetime H h) :
    trajMove k H h p = decide (p + 1 < lifetime H h) := by
  have hne := traj_ne_halt hh hk hp
  have hne' : p + 1 < lifetime H h → traj k H h (p + 1) ≠ .halt := traj_ne_halt hh hk
  have hle : lifetime H h ≤ p + 1 → traj k H h (p + 1) = .halt := traj_lifetime_le hh hk
  -- the move flag is `true` exactly when the new state is not `halt`
  have key : ∀ s b, s ≠ .halt → (a1next k s b).2 = decide ((a1next k s b).1 ≠ .halt) := by
    intro s b hs
    cases s with
    | init => simp [a1next]
    | sel dis D =>
      cases b <;> simp only [a1next] <;> split_ifs <;> simp
    | dep r => simp only [a1next]; split_ifs <;> simp
    | halt => exact absurd rfl hs
  unfold trajMove
  rw [key _ _ hne]
  change decide (traj k H h (p + 1) ≠ .halt) = _
  by_cases h1 : p + 1 < lifetime H h
  · simp [h1, hne' h1]
  · simp [h1, hle (by omega)]

omit [NeZero n] in
theorem lifetime_pos : 0 < lifetime H h := by unfold lifetime; omega

/-- Each agent moves `n + moves1 D < 3n` times in total: it leaves in each of its actions except the
last one (`trajMove_eq`). -/
theorem alg1_moves_lt (hh : h ∈ H) : lifetime H h - 1 = n + moves1 (distSeq H h) ∧
    n + moves1 (distSeq H h) < 3 * n := by
  have := moves1_lt hh
  unfold lifetime; omega

/-! ### The global invariant -/

section Invariant

variable {k : ℕ} (home : Fin k → ZMod n)

/-- The set of home nodes. -/
def homes : Finset (ZMod n) := Finset.univ.image home

/-- The invariant of an execution of Algorithm 1, where agent `b` has taken `p b` actions. -/
structure Inv (C : Config (alg1 k) n (Fin k)) (p : Fin k → ℕ) : Prop where
  queue : ∀ w, ∀ x ∈ (C w).queue, p x.id < lifetime (homes home) (home x.id) ∧
    w = home x.id + (p x.id : ZMod n) ∧ x.st = traj k (homes home) (home x.id) (p x.id)
  stay : ∀ w, ∀ x ∈ (C w).stay, p x.id = lifetime (homes home) (home x.id) ∧
    w = home x.id + ((lifetime (homes home) (home x.id) - 1 : ℕ) : ZMod n) ∧ x.st = .halt
  tok : ∀ w, (C w).tok = (Finset.univ.filter fun b => home b = w ∧ 0 < p b).card
  head : ∀ b, p b = 0 → ((C (home b)).queue.head?).map Agent.id = some b
  le : ∀ b, p b ≤ lifetime (homes home) (home b)
  ids : allIds C = allIds (initConfig (alg1 k) k home)

variable {home}

omit [NeZero n] in
theorem card_homes (hinj : Injective home) : (homes home).card = k := by
  rw [homes, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

omit [NeZero n] in
theorem home_mem_homes (b : Fin k) : home b ∈ homes home := Finset.mem_image_of_mem _ (by simp)

theorem inv_init (hinj : Injective home) : Inv home (initConfig (alg1 k) k home) 0 where
  queue w x hx := by
    simp only [initConfig, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨lifetime_pos, by simp [hb], rfl⟩
  stay w x hx := by simp [initConfig] at hx
  tok w := by simp [initConfig]
  head b _ := by
    have := filter_finRange_eq_singleton (fun a => decide (home a = home b)) b
      (fun a => by simp [hinj.eq_iff])
    simp [initConfig, this]
  le b := Nat.zero_le _
  ids := rfl

theorem Inv.nodup {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ} (hI : Inv home C p) :
    (allIds C).Nodup := by
  rw [hI.ids]; exact allIds_initConfig_nodup home

/-- An agent that is not at the head of a queue cannot act. -/
theorem Inv.step_eq_self {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ} (hI : Inv home C p)
    {a : Fin k} (ha : ∀ w x, (C w).queue.head? = some x → x.id ≠ a) : step (alg1 k) C a = C := by
  unfold step
  split
  · rename_i hex
    obtain ⟨y, hy, hyid⟩ := Option.map_eq_some_iff.1 hex.choose_spec
    generalize hex.choose = q at hy hyid
    obtain ⟨v, s⟩ := q
    cases s with
    | head => exact absurd hyid (ha v y hy)
    | stay i =>
      apply stepAt_of_act_none
      apply Local.act_eq_none_of_halted hy
      have hmem : y ∈ (C v).stay := List.mem_of_getElem? hy
      simp [alg1, (hI.stay v y hmem).2.2]
  · rfl

theorem a1next_ne_init (s : A1State) (b : Bool) : (a1next k s b).1 ≠ .init := by
  cases s with
  | init => simp [a1next]
  | sel dis D => cases b <;> simp only [a1next] <;> split_ifs <;> simp
  | dep r => simp only [a1next]; split_ifs <;> simp
  | halt => simp [a1next]

omit [NeZero n] in
theorem traj_eq_init_iff {H : Finset (ZMod n)} {h : ZMod n} (p : ℕ) :
    traj k H h p = .init ↔ p = 0 := by
  cases p with
  | zero => simp [traj]
  | succ p => simp only [traj, a1next_ne_init, false_iff]; omega

/-- The local configuration of node `w` after the action of the agent `a` at the head of its
queue: `mv` says whether it leaves, `new` is its new record. -/
def headResult (L : Local (alg1 k) (Fin k)) (rel mv : Bool) (new : Agent (alg1 k) (Fin k)) :
    Local (alg1 k) (Fin k) :=
  ⟨L.tok + (if rel then 1 else 0), if mv then L.stay else L.stay ++ [new], L.queue.tail⟩

theorem Inv.act_head (hinj : Injective home) {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ}
    (hI : Inv home C p) {w : ZMod n} {a : Fin k} {xs : A1State} {xm : List Unit}
    (hx : (C w).queue.head? = some ⟨a, xs, xm⟩) :
    (C w).act (alg1 k) .head = some (headResult (C w) (decide (p a = 0))
      (decide (p a + 1 < lifetime (homes home) (home a)))
      ⟨a, traj k (homes home) (home a) (p a + 1), []⟩,
      if p a + 1 < lifetime (homes home) (home a)
        then some ⟨a, traj k (homes home) (home a) (p a + 1), []⟩ else none) := by
  have hHk : (homes home).card = k := card_homes hinj
  have hha : home a ∈ homes home := home_mem_homes a
  obtain ⟨hpl, hw, hst⟩ := hI.queue w _ (List.mem_of_mem_head? hx)
  simp only at hpl hw hst
  subst hst
  have hobs : a1next k (traj k (homes home) (home a) (p a)) (decide (0 < (C w).tok)) =
      a1next k (traj k (homes home) (home a) (p a))
        (decide (home a + (p a : ZMod n) ∈ homes home)) := by
    by_cases hp0 : p a = 0
    · rw [hp0]; simp [traj, a1next]
    · congr 1
      rw [hI.tok w, ← hw]
      simp only [decide_eq_decide, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨b, rfl, -⟩; exact home_mem_homes b
      · intro hwH
        obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hwH
        refine ⟨b, rfl, Nat.pos_of_ne_zero fun hb0 => ?_⟩
        have := hI.head b hb0
        rw [hx] at this
        simp only [Option.map_some, Option.some.injEq] at this
        subst this
        exact hp0 hb0
  have hmv := trajMove_eq hha hHk hpl
  unfold trajMove at hmv
  have hnh : (alg1 k).halted (traj k (homes home) (home a) (p a)) = false := by
    simp [alg1, traj_ne_halt hha hHk hpl]
  simp only [Local.act, Local.actor, hx, hnh, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  simp only [Local.result, alg1, Local.others, Local.rest, deliver, hobs, hmv, traj_eq_init_iff,
    headResult, decide_eq_true_eq]
  rfl

/-- The agent at the head of a queue takes its next action along its trajectory. -/
theorem Inv.step_head (hinj : Injective home) {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ}
    (hI : Inv home C p) {w : ZMod n} {x : Agent (alg1 k) (Fin k)}
    (hx : (C w).queue.head? = some x) :
    Inv home (step (alg1 k) C x.id) (Function.update p x.id (p x.id + 1)) := by
  rcases x with ⟨a, xs, xm⟩
  simp only
  have hHk : (homes home).card = k := card_homes hinj
  have hha : home a ∈ homes home := home_mem_homes a
  have hxq : (⟨a, xs, xm⟩ : Agent (alg1 k) (Fin k)) ∈ (C w).queue := List.mem_of_mem_head? hx
  obtain ⟨hpl, hw, hst⟩ := hI.queue w _ hxq
  simp only at hpl hw hst
  have hstep : step (alg1 k) C a = stepAt (alg1 k) C w .head :=
    step_eq_stepAt (x := ⟨a, xs, xm⟩) hI.nodup (by simpa [Local.actor] using hx)
  have hact := hI.act_head hinj hx
  set L := lifetime (homes home) (home a) with hLdef
  set new : Agent (alg1 k) (Fin k) := ⟨a, traj k (homes home) (home a) (p a + 1), []⟩ with hnew
  set R := headResult (C w) (decide (p a = 0)) (decide (p a + 1 < L)) new with hR
  have hC' : ∀ u, stepAt (alg1 k) C w .head u =
      if u = w + 1 then (if u = w then R else C u).push _ (if p a + 1 < L then some new else none)
      else if u = w then R else C u := by
    intro u; simp only [stepAt, hact]
  -- `a` occurs nowhere else
  have hnd := Local.ids_nodup_of_allIds hI.nodup w
  obtain ⟨q, hq⟩ : ∃ q, (C w).queue = ⟨a, xs, xm⟩ :: q := by
    cases hL : (C w).queue with
    | nil => simp [hL] at hx
    | cons z q => simp [hL] at hx; exact ⟨q, by rw [hx]⟩
  have hnotail : ∀ y ∈ (C w).queue.tail, y.id ≠ a := by
    intro y hy hya
    rw [hq, List.tail_cons] at hy
    have hq' := (Multiset.nodup_add.1 hnd).2.1
    rw [hq] at hq'
    simp only [List.map_cons, Multiset.coe_nodup, List.nodup_cons, List.mem_map] at hq'
    exact hq'.1 ⟨y, hy, hya⟩
  have hother : ∀ u, u ≠ w → ∀ y ∈ (C u).queue, y.id ≠ a := by
    intro u hu y hy hya
    obtain ⟨-, hu', -⟩ := hI.queue u y hy
    rw [hya, ← hw] at hu'; exact hu hu'
  have hpa : Function.update p a (p a + 1) a = p a + 1 := by simp
  have hpb : ∀ b, b ≠ a → Function.update p a (p a + 1) b = p b := fun b hb => by
    simp [hb]
  have hstay_ne : ∀ u, ∀ y ∈ (C u).stay, y.id ≠ a := by
    intro u y hy hya
    have := (hI.stay u y hy).1
    rw [hya] at this; omega
  have hRq : R.queue = (C w).queue.tail := rfl
  have hRs : R.stay = if p a + 1 < L then (C w).stay else (C w).stay ++ [new] := by
    simp only [hR, headResult, decide_eq_true_eq]
  have hRt : R.tok = (C w).tok + if p a = 0 then 1 else 0 := by
    simp only [hR, headResult, decide_eq_true_eq]
  rw [hstep]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- queues
    intro u y hy
    rw [hC' u] at hy
    have hold : ∀ y ∈ (if u = w then R else C u).queue,
        Function.update p a (p a + 1) y.id < lifetime (homes home) (home y.id) ∧
        u = home y.id + (Function.update p a (p a + 1) y.id : ZMod n) ∧
        y.st = traj k (homes home) (home y.id) (Function.update p a (p a + 1) y.id) := by
      intro y hy
      by_cases huw : u = w
      · subst huw
        simp only [↓reduceIte, hRq] at hy
        rw [hpb _ (hnotail y hy)]
        exact hI.queue u y (List.mem_of_mem_tail hy)
      · simp only [huw, ↓reduceIte] at hy
        rw [hpb _ (hother u huw y hy)]
        exact hI.queue u y hy
    by_cases hu1 : u = w + 1
    · simp only [hu1, ↓reduceIte] at hy
      by_cases hmv : p a + 1 < L
      · simp only [hmv, ↓reduceIte, Local.push, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hold y (by rw [hu1]; exact hy)
        · simp only [hnew, hpa]
          exact ⟨hmv, by rw [hu1, hw]; push_cast; ring, rfl⟩
      · simp only [hmv, ↓reduceIte, Local.push] at hy
        exact hold y (by rw [hu1]; exact hy)
    · simp only [hu1, ↓reduceIte] at hy
      exact hold y hy
  · -- stays
    intro u y hy
    have hstay_eq : (stepAt (alg1 k) C w .head u).stay = (if u = w then R else C u).stay := by
      rw [hC' u]; split_ifs <;> cases (decide (p a + 1 < L)) <;> simp [Local.push]
    rw [hstay_eq] at hy
    have hold : ∀ y ∈ (C u).stay,
        Function.update p a (p a + 1) y.id = lifetime (homes home) (home y.id) ∧
        u = home y.id + ((lifetime (homes home) (home y.id) - 1 : ℕ) : ZMod n) ∧ y.st = .halt := by
      intro y hy; rw [hpb _ (hstay_ne u y hy)]; exact hI.stay u y hy
    by_cases huw : u = w
    · subst huw
      simp only [↓reduceIte, hRs] at hy
      by_cases hmv : p a + 1 < L
      · simp only [hmv, ↓reduceIte] at hy; exact hold y hy
      · simp only [hmv, ↓reduceIte, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hold y hy
        · have hL : p a + 1 = L := by omega
          simp only [hnew, hpa]
          refine ⟨hL, ?_, ?_⟩
          · rw [hw, show lifetime (homes home) (home a) - 1 = p a by omega]
          · rw [hL]; exact traj_lifetime_le hha hHk le_rfl
    · simp only [huw, ↓reduceIte] at hy; exact hold y hy
  · -- tokens
    intro u
    have htok_eq : (stepAt (alg1 k) C w .head u).tok =
        (C u).tok + if u = w ∧ p a = 0 then 1 else 0 := by
      rw [hC' u]
      by_cases huw : u = w
      · subst huw
        have : (if u = u + 1 then R.push (alg1 k) (if p a + 1 < L then some new else none)
            else R).tok = R.tok := by split_ifs <;> cases (decide (p a + 1 < L)) <;> simp [Local.push]
        simp only [↓reduceIte, this, hRt, true_and]
      · simp only [huw, ↓reduceIte, false_and, add_zero]
        split_ifs <;> simp [Local.push]
    rw [htok_eq, hI.tok u]
    by_cases hcase : u = w ∧ p a = 0
    · obtain ⟨huw, hp0⟩ := hcase
      rw [show (if u = w ∧ p a = 0 then 1 else 0) = 1 by simp [huw, hp0], huw]
      have hau : home a = w := by rw [hw, hp0]; simp
      rw [show (Finset.univ.filter fun b => home b = w ∧ 0 < Function.update p a (p a + 1) b) =
          insert a (Finset.univ.filter fun b => home b = w ∧ 0 < p b) by
        ext b
        by_cases hba : b = a
        · subst hba; simp [hau, hp0]
        · simp [hba]]
      rw [Finset.card_insert_of_notMem (by simp [hp0])]
    · simp only [hcase, ↓reduceIte, add_zero]
      congr 1
      ext b
      by_cases hba : b = a
      · subst hba
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpa]
        constructor
        · rintro ⟨hb, -⟩; exact ⟨hb, by omega⟩
        · rintro ⟨hb, -⟩
          refine ⟨hb, Nat.pos_of_ne_zero fun hp0 => hcase ⟨?_, hp0⟩⟩
          rw [hw, hp0, ← hb]; simp
      · simp [hba]
  · -- heads
    intro b hb
    have hba : b ≠ a := by rintro rfl; simp at hb
    rw [hpb b hba] at hb
    have hhd := hI.head b hb
    have hbw : home b ≠ w := by
      rintro hbw; rw [hbw, hx] at hhd; simp at hhd; exact hba hhd.symm
    obtain ⟨z, hz⟩ : ∃ z, (C (home b)).queue.head? = some z := by
      cases h' : (C (home b)).queue.head? with
      | none => rw [h'] at hhd; simp at hhd
      | some z => exact ⟨z, rfl⟩
    rw [hC' (home b)]
    by_cases h1 : home b = w + 1
    · simp only [h1, ↓reduceIte, show w + 1 ≠ w from fun h => hbw (h1.trans h)]
      rw [← h1]
      by_cases hmv : p a + 1 < L
      · simp only [hmv, ↓reduceIte, Local.push, List.head?_append, hz]
        simpa [hz] using hhd
      · simp only [hmv, ↓reduceIte, Local.push]; exact hhd
    · simp only [h1, hbw, ↓reduceIte]; exact hhd
  · intro b
    by_cases hba : b = a
    · subst hba; rw [hpa]; exact hpl
    · rw [hpb b hba]; exact hI.le b
  · rw [allIds_stepAt]; exact hI.ids

theorem Inv.step_cases (hinj : Injective home) {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ}
    (hI : Inv home C p) (a : Fin k) :
    (step (alg1 k) C a = C ∧ Inv home C p) ∨
      (Inv home (step (alg1 k) C a) (Function.update p a (p a + 1)) ∧
        p a < lifetime (homes home) (home a)) := by
  by_cases h : ∃ w x, (C w).queue.head? = some x ∧ x.id = a
  · obtain ⟨w, x, hx, rfl⟩ := h
    exact Or.inr ⟨hI.step_head hinj hx, (hI.queue w x (List.mem_of_mem_head? hx)).1⟩
  · push Not at h
    exact Or.inl ⟨hI.step_eq_self fun w x hx => h w x hx, hI⟩

theorem inv_exec (hinj : Injective home) (σ : ℕ → Fin k) :
    ∀ t, ∃ p, Inv home (exec (alg1 k) (initConfig (alg1 k) k home) σ t) p
  | 0 => ⟨0, inv_init hinj⟩
  | t + 1 => by
    obtain ⟨p, hp⟩ := inv_exec hinj σ t
    rcases hp.step_cases hinj (σ t) with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨p, by rw [exec, h]; exact hp⟩
    · exact ⟨_, by rw [exec]; exact h⟩

/-- The potential: the number of actions remaining to all agents. -/
def potential (home : Fin k → ZMod n) (p : Fin k → ℕ) : ℕ :=
  ∑ b, (lifetime (homes home) (home b) - p b)

omit [NeZero n] in
theorem potential_update_lt {p : Fin k → ℕ} {a : Fin k} (ha : p a < lifetime (homes home) (home a)) :
    potential home (Function.update p a (p a + 1)) < potential home p := by
  unfold potential
  apply Finset.sum_lt_sum
  · intro b _
    by_cases hba : b = a
    · subst hba; simp; omega
    · simp [hba]
  · exact ⟨a, Finset.mem_univ _, by simp; omega⟩

theorem mem_allIds_init (b : Fin k) : b ∈ allIds (initConfig (alg1 k) k home) := by
  unfold allIds
  rw [Multiset.mem_sum]
  refine ⟨home b, Finset.mem_univ _, ?_⟩
  simp [initConfig, Local.ids]

theorem Inv.exists_mem {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ} (hI : Inv home C p)
    (b : Fin k) : ∃ v, ∃ x ∈ (C v).stay ++ (C v).queue, x.id = b := by
  have hb := mem_allIds_init (home := home) b
  rw [← hI.ids] at hb
  unfold allIds at hb
  obtain ⟨v, -, hv⟩ := Multiset.mem_sum.1 hb
  simp only [Local.ids, Multiset.mem_add, Multiset.mem_coe, List.mem_map] at hv
  rcases hv with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · exact ⟨v, x, List.mem_append_left _ hx, rfl⟩
  · exact ⟨v, x, List.mem_append_right _ hx, rfl⟩

theorem Inv.allHalted {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ} (hI : Inv home C p)
    (h0 : potential home p = 0) : AllHalted (alg1 k) C := by
  have hpL : ∀ b, p b = lifetime (homes home) (home b) := by
    intro b
    have := (Finset.sum_eq_zero_iff.1 h0) b (Finset.mem_univ _)
    have := hI.le b; omega
  intro v x hx
  rcases List.mem_append.1 hx with hx | hx
  · simp [alg1, (hI.stay v x hx).2.2]
  · have := (hI.queue v x hx).1; rw [hpL] at this; omega

/-- Progress under a fair schedule: the potential eventually decreases. -/
theorem progress (hinj : Injective home) {σ : ℕ → Fin k} (hσ : Fair σ) {t : ℕ}
    {p : Fin k → ℕ} (hI : Inv home (exec (alg1 k) (initConfig (alg1 k) k home) σ t) p)
    (hpos : potential home p ≠ 0) :
    ∃ t' p', Inv home (exec (alg1 k) (initConfig (alg1 k) k home) σ t') p' ∧
      potential home p' < potential home p := by
  set E := exec (alg1 k) (initConfig (alg1 k) k home) σ with hE
  obtain ⟨b, hb⟩ : ∃ b, p b < lifetime (homes home) (home b) := by
    by_contra hcon
    push Not at hcon
    apply hpos
    exact Finset.sum_eq_zero fun b _ => by have := hcon b; omega
  obtain ⟨v, x, hx, rfl⟩ := hI.exists_mem b
  have hxq : x ∈ (E t v).queue := by
    rcases List.mem_append.1 hx with hx' | hx'
    · have := (hI.stay v x hx').1; omega
    · exact hx'
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, (E t v).queue.head? = some x₀ := by
    cases h' : (E t v).queue with
    | nil => simp [h'] at hxq
    | cons y _ => exact ⟨y, rfl⟩
  obtain ⟨t₁, ht₁, hσt₁⟩ := hσ x₀.id t
  have key : ∀ d, t + d ≤ t₁ → E (t + d) = E t ∨
      ∃ t' p', Inv home (E t') p' ∧ potential home p' < potential home p := by
    intro d
    induction d with
    | zero => intro _; exact Or.inl rfl
    | succ d ih =>
      intro hd
      rcases ih (by omega) with h | h
      · have hI' : Inv home (E (t + d)) p := h ▸ hI
        rcases hI'.step_cases hinj (σ (t + d)) with ⟨h1, -⟩ | ⟨h1, h2⟩
        · left; rw [← Nat.add_assoc, hE, exec, ← hE, h1, h]
        · right
          exact ⟨t + d + 1, _, h1, potential_update_lt h2⟩
      · exact Or.inr h
  rcases key (t₁ - t) (by omega) with h | h
  · rw [show t + (t₁ - t) = t₁ by omega] at h
    have hI₁ : Inv home (E t₁) p := h ▸ hI
    have hx₁ : (E t₁ v).queue.head? = some x₀ := by rw [h]; exact hx₀
    refine ⟨t₁ + 1, _, ?_, potential_update_lt (hI₁.queue v x₀ (List.mem_of_mem_head? hx₁)).1⟩
    rw [hE, exec, ← hE, hσt₁]
    exact hI₁.step_head hinj hx₁
  · exact h

theorem eventually_allHalted (hinj : Injective home) {σ : ℕ → Fin k} (hσ : Fair σ) :
    ∃ t, AllHalted (alg1 k) (exec (alg1 k) (initConfig (alg1 k) k home) σ t) := by
  suffices ∀ M t p, Inv home (exec (alg1 k) (initConfig (alg1 k) k home) σ t) p →
      potential home p ≤ M → ∃ t, AllHalted (alg1 k) (exec (alg1 k) (initConfig (alg1 k) k home) σ t) by
    obtain ⟨p, hp⟩ := inv_exec hinj σ 0
    exact this _ 0 p hp le_rfl
  intro M
  induction M with
  | zero => intro t p hp h0; exact ⟨t, hp.allHalted (by omega)⟩
  | succ M ih =>
    intro t p hp hM
    by_cases h0 : potential home p = 0
    · exact ⟨t, hp.allHalted h0⟩
    · obtain ⟨t', p', hp', hlt⟩ := progress hinj hσ hp h0
      exact ih t' p' hp' (by omega)

omit [NeZero n] in
theorem home_add_lifetime (b : Fin k) :
    home b + ((lifetime (homes home) (home b) - 1 : ℕ) : ZMod n) =
      alg1Target (homes home) (home b) := by
  unfold lifetime alg1Target
  rw [show n + 1 + moves1 (distSeq (homes home) (home b)) - 1 =
    n + moves1 (distSeq (homes home) (home b)) by omega]
  push_cast; simp

theorem Inv.occ_eq (hinj : Injective home) {C : Config (alg1 k) n (Fin k)} {p : Fin k → ℕ}
    (hI : Inv home C p) (hq : QueuesEmpty (alg1 k) C) (v : ZMod n) :
    occ (alg1 k) C v = if v ∈ (homes home).image (alg1Target (homes home)) then 1 else 0 := by
  have hnd : ((C v).stay.map Agent.id).Nodup := by
    have := Local.ids_nodup_of_allIds hI.nodup v
    exact Multiset.coe_nodup.1 (Multiset.nodup_add.1 this).1
  have hpos : ∀ u, ∀ x ∈ (C u).stay, alg1Target (homes home) (home x.id) = u := by
    intro u x hx
    rw [(hI.stay u x hx).2.1, home_add_lifetime]
  unfold occ
  split_ifs with hv
  · obtain ⟨h₀, hh₀, hv'⟩ := Finset.mem_image.1 hv
    have hTinj : Injective fun b => alg1Target (homes home) (home b) := fun b c hbc =>
      hinj (alg1_targets_injOn ⟨h₀, hh₀⟩ (home_mem_homes b) (home_mem_homes c) hbc)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hh₀
    obtain ⟨u, x, hx, rfl⟩ := hI.exists_mem b
    rw [hq u, List.append_nil] at hx
    have hu := hpos u x hx
    rw [hv'] at hu
    subst hu
    apply le_antisymm
    · rw [← List.length_map (f := Agent.id), ← List.toFinset_card_of_nodup hnd]
      calc _ ≤ ({x.id} : Finset (Fin k)).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [List.mem_toFinset, List.mem_map] at hc
            obtain ⟨y, hy, rfl⟩ := hc
            simp only [Finset.mem_singleton]
            exact hTinj ((hpos _ y hy).trans hv'.symm)
        _ = 1 := Finset.card_singleton _
    · exact List.length_pos_of_mem hx
  · rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
    intro x hx
    apply hv
    rw [← hpos v x hx]
    exact Finset.mem_image_of_mem _ (home_mem_homes x.id)

end Invariant

/-- **Theorem 3** of [Shibata et al., PODC 2016] (correctness): for agents knowing `k`,
Algorithm 1 solves the uniform deployment problem with termination detection, from every initial
configuration (agents at distinct nodes) and under every fair schedule. -/
theorem theorem_3 {n k : ℕ} (home : Fin k → ZMod n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hinj : Injective home) : SolvesTD (alg1 k) n k home := by
  have : NeZero n := ⟨by omega⟩
  intro σ hσ
  refine ⟨eventually_allHalted hinj hσ, fun t ht => ?_⟩
  obtain ⟨p, hp⟩ := inv_exec hinj σ t
  have hq : QueuesEmpty (alg1 k) (exec (alg1 k) (initConfig (alg1 k) k home) σ t) := by
    intro v
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have h1 := ht v x (List.mem_append_right _ hx)
    obtain ⟨hlt, -, hst⟩ := hp.queue v x hx
    simp only [alg1, decide_eq_true_eq] at h1
    rw [hst] at h1
    exact traj_ne_halt (home_mem_homes x.id) (card_homes hinj) hlt h1
  refine ⟨hq, ?_⟩
  have hHne : (homes home).Nonempty := ⟨home ⟨0, by omega⟩, home_mem_homes _⟩
  have huni := alg1_targets_uniform hHne (card_homes hinj)
  unfold IsUniformSet at huni
  convert huni using 1
  funext v
  exact hp.occ_eq hinj hq v

end Podc.UniformDeploymentRings
