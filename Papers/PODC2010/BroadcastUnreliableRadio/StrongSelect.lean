import Papers.PODC2010.BroadcastUnreliableRadio.Model

/-!
# The strong select algorithm (Section 5 of the paper): model and schedule

Kuhn, Lynch, Newport, Oshman, Richa. *Broadcasting in Unreliable Radio Networks.* PODC 2010.

Section 5 works in the weakest setting of the paper: a **directed** dual graph `(G, G')`
(`DualGraph V`), **collision rule CR4** (a node reached by exactly one message receives it, a
node reached by two or more messages receives an arbitrary one of them or nothing; no collision
detection) and **asynchronous start** (a node is inactive, and silent, until it first receives
the broadcast message). Nodes have access to a global round counter (footnote 1 of the paper:
w.l.o.g., since the round number can be piggy-backed on the broadcast message).

## Strongly selective families (Definition 6)

`StronglySelective F ℓ k`: the sequence of sets `F 0, …, F (ℓ - 1)` is `(n, k)`-strongly
selective, i.e. every element `z` of every `Z` with `|Z| ≤ k` is *isolated* by some `F j`:
`Z ∩ F j = {z}`. We identify the id set `[n]` with the node set `V` (the placement of processes on
nodes is an arbitrary bijection, and all statements below quantify over all networks; so a family
of id sets is transported to a family of node sets along the placement).

## The algorithm

Parameters (`StrongSelect V`): `smax ≥ 1`, the log factor `f`, and families `F s` for
`s = 1, …, smax`. Family `F s` consists of **exactly** `ℓ s = 4 ^ s * f` sets
`F s 0, …, F s (ℓ s - 1)` (the paper has `ℓ_s ≤ k_s² f(n)` with `k_s = 2 ^ s`; a smaller family
is padded by repeating sets, which keeps it strongly selective, and the exact size is needed for
`ℓ'_s = 2 ℓ'_{s-1}` in the proof of Theorem 10).

Rounds are numbered `1, 2, …` and divided into epochs of `L = 2 ^ smax - 1` rounds. Round `r`
has (0-based) position `pos r = (r - 1) % L` in epoch `epoch r = (r - 1) / L`. The positions
`2 ^ (s - 1) - 1, …, 2 ^ s - 2` of every epoch are dedicated to `F s` (`fam r = s`); they use the
sets of `F s` cyclically: the `slot r`-th use of `F s` overall (counted from 0) uses the set
`F s (idx r)` with `idx r = slot r % ℓ s`, in the iteration `iter r = slot r / ℓ s` of `F s`.
This is the paper's formula `F_{⌊log r⌋+1}[((e - 2) 2^{⌊log r⌋} + r) mod ℓ + 1]` with 0-based
indices. Iteration `m` of `F s` occupies exactly the rounds `m ℓ'_s + 1, …, (m + 1) ℓ'_s` with
`ℓ'_s = 2 ^ (s + 1) f L = ℓ_s L / 2 ^ (s - 1)` (`exists_round`).

A node informed (for the first time) at the end of round `t` participates, for every `s`, in
exactly one iteration of `F s`: the first iteration that starts after round `t` (the source,
informed "at the end of round 0", participates in iteration `0`). A participant of iteration `m`
of `F s` sends in round `r` of that iteration iff it belongs to `F s (idx r)`. Strong select is
oblivious, so sending only depends on the id, on the round and on the time the node got the
message. Only informed nodes send, so every message is the broadcast message.

## Executions (`Execution`)

An execution is described abstractly by the sets `inf t` of nodes holding the message at the end
of round `t` (`inf 0 = {src}`, monotone). The senders of round `r` are computed from `inf` by the
rules above (`Sends`). The **only** progress guarantee is: if exactly one node `u` sends in round
`r`, then every `G`-out-neighbour of `u` holds the message at the end of round `r` (it is reached
by `u`'s message and by no other message, so it receives it under CR4 — or it is `u` itself or
another node that already has the message). Any additional informing is allowed: the adversary
may deliver messages over `G'`-links, and CR4 may resolve collisions to a message. Every CR4
execution of strong select with asynchronous start yields such an `inf`, so bounds proved for all
`Execution`s are at least as strong as the paper's claim.
-/

namespace Podc.BroadcastUnreliableRadio.StrongSelect

open Finset

variable {V : Type*}

/-- Definition 6 of the paper: the sequence `F 0, …, F (ℓ - 1)` of node sets is a
`(n, k)`-strongly selective family (`n = |V|`): for every set `Z` of at most `k` nodes and every
`z ∈ Z` some `F j` isolates `z`, i.e. `Z ∩ F j = {z}`. -/
def StronglySelective [DecidableEq V] (F : ℕ → Finset V) (ℓ k : ℕ) : Prop :=
  ∀ Z : Finset V, Z.card ≤ k → ∀ z ∈ Z, ∃ j < ℓ, Z ∩ F j = {z}

/-- The parameters of strong select: `smax`, the log factor `f` and the families `F s j`
(`s ∈ [1, smax]`, `j < ℓ s`). -/
structure Params (V : Type*) where
  /-- The number of selective families. -/
  smax : ℕ
  /-- The log factor `f(n)` in the sizes `ℓ s = 4 ^ s * f` of the families. -/
  f : ℕ
  /-- `F s j` is the `j`-th set (0-based) of the family `F_s`. -/
  F : ℕ → ℕ → Finset V

namespace Params

variable (A : Params V)

/-- The length of an epoch, `2 ^ smax - 1`. -/
def L : ℕ := 2 ^ A.smax - 1

/-- The number of sets of family `F s`, `ℓ_s = k_s ^ 2 f = 4 ^ s f`. -/
def ℓ (s : ℕ) : ℕ := 4 ^ s * A.f

/-- The number of rounds of one iteration of `F s`, `ℓ'_s = ℓ_s L / 2 ^ (s - 1) = 2 ^ (s+1) f L`. -/
def ℓ' (s : ℕ) : ℕ := 2 ^ (s + 1) * A.f * A.L

/-- The 0-based position of round `r ≥ 1` within its epoch. -/
def pos (r : ℕ) : ℕ := (r - 1) % A.L

/-- The 0-based epoch of round `r ≥ 1`. -/
def epoch (r : ℕ) : ℕ := (r - 1) / A.L

/-- The family used in round `r`: positions `2 ^ (s-1) - 1, …, 2 ^ s - 2` belong to `F s`. -/
def fam (r : ℕ) : ℕ := Nat.log 2 (A.pos r + 1) + 1

/-- How many rounds of family `fam r` precede round `r` (0-based global slot of `F (fam r)`). -/
def slot (r : ℕ) : ℕ :=
  A.epoch r * 2 ^ (A.fam r - 1) + (A.pos r + 1 - 2 ^ (A.fam r - 1))

/-- The iteration of `F (fam r)` that round `r` belongs to. -/
def iter (r : ℕ) : ℕ := A.slot r / A.ℓ (A.fam r)

/-- The index of the set of `F (fam r)` used in round `r`. -/
def idx (r : ℕ) : ℕ := A.slot r % A.ℓ (A.fam r)

/-- Node `v` participates in iteration `m` of `F s`: iteration `m` is the first iteration of
`F s` starting after `v` got the message, i.e. `m` is least with `v ∈ inf (m ℓ'_s)`. -/
def Participates (inf : ℕ → Finset V) (v : V) (s m : ℕ) : Prop :=
  v ∈ inf (m * A.ℓ' s) ∧ ∀ m' < m, v ∉ inf (m' * A.ℓ' s)

/-- Node `v` sends in round `r` (given the informed sets `inf`): it participates in the current
iteration of the current family and belongs to the current set. -/
def Sends (inf : ℕ → Finset V) (r : ℕ) (v : V) : Prop :=
  A.Participates inf v (A.fam r) (A.iter r) ∧ v ∈ A.F (A.fam r) (A.idx r)

/-! ## The schedule -/

lemma ℓ_eq (i : ℕ) : A.ℓ (i + 1) = 2 ^ i * (2 ^ (i + 2) * A.f) := by
  unfold ℓ
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← mul_assoc, ← pow_add]
  ring_nf

lemma ℓ'_succ (s : ℕ) : A.ℓ' (s + 1) = 2 * A.ℓ' s := by
  unfold ℓ'; ring

lemma L_pos (h : 1 ≤ A.smax) : 0 < A.L := by
  unfold L
  have : 2 ≤ 2 ^ A.smax := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A.smax := Nat.pow_le_pow_right (by norm_num) h
  omega

lemma ℓ'_pos (h : 1 ≤ A.smax) (hf : 1 ≤ A.f) (s : ℕ) : 0 < A.ℓ' s := by
  unfold ℓ'
  have := A.L_pos h
  positivity

/-- Every set `F s j` of every iteration `m` of `F s` is used in some round of the iteration,
and iteration `m` lies within the rounds `m ℓ'_s + 1, …, (m + 1) ℓ'_s`. -/
lemma exists_round {s : ℕ} (hs1 : 1 ≤ s) (hs : s ≤ A.smax) (m : ℕ) {j : ℕ} (hj : j < A.ℓ s) :
    ∃ r, m * A.ℓ' s < r ∧ r ≤ (m + 1) * A.ℓ' s ∧ A.fam r = s ∧ A.iter r = m ∧ A.idx r = j := by
  obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
  set a := 2 ^ i with ha
  set K := 2 ^ (i + 2) * A.f with hK
  have hℓ : A.ℓ (i + 1) = a * K := A.ℓ_eq i
  have hℓ' : A.ℓ' (i + 1) = K * A.L := by
    simp only [ℓ', hK]
  have ha0 : 0 < a := by positivity
  have hL : 2 * a - 1 ≤ A.L := by
    have : 2 * a ≤ 2 ^ A.smax := by
      rw [ha, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hs
    unfold L; omega
  set g := m * A.ℓ (i + 1) + j with hg
  set e := g / a with he
  set o := g % a with ho
  have hoa : o < a := Nat.mod_lt _ ha0
  set p := a - 1 + o with hp
  have hpL : p < A.L := by omega
  refine ⟨e * A.L + p + 1, ?_⟩
  have hpos : A.pos (e * A.L + p + 1) = p := by
    simp only [pos, Nat.add_sub_cancel]
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hpL
  have hep : A.epoch (e * A.L + p + 1) = e := by
    simp only [epoch, Nat.add_sub_cancel]
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hpL]; simp
  have hfam : A.fam (e * A.L + p + 1) = i + 1 := by
    simp only [fam, hpos]
    congr 1
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ]; omega
  have hslot : A.slot (e * A.L + p + 1) = g := by
    simp only [slot, hpos, hep, hfam, Nat.add_sub_cancel]
    rw [← ha]
    have : p + 1 - a = o := by omega
    rw [this, he, ho, Nat.mul_comm]; exact Nat.div_add_mod g a
  have hjK : j / a < K := by
    rw [Nat.div_lt_iff_lt_mul ha0]; rw [hℓ] at hj; linarith
  have he' : e = m * K + j / a := by
    rw [he, hg, hℓ, show m * (a * K) = a * (m * K) by ring, Nat.mul_add_div ha0]
  refine ⟨?_, ?_, hfam, ?_, ?_⟩
  · rw [hℓ', he']
    have : m * (K * A.L) ≤ (m * K + j / a) * A.L := by
      rw [add_mul, ← mul_assoc]; exact Nat.le_add_right _ _
    omega
  · rw [hℓ', he']
    have h1 : (m * K + j / a) * A.L + A.L ≤ (m + 1) * (K * A.L) := by
      have : m * K + j / a + 1 ≤ (m + 1) * K := by rw [add_mul]; omega
      calc (m * K + j / a) * A.L + A.L = (m * K + j / a + 1) * A.L := by ring
        _ ≤ ((m + 1) * K) * A.L := Nat.mul_le_mul_right _ this
        _ = (m + 1) * (K * A.L) := by ring
    omega
  · simp only [iter, hslot, hfam, hg]
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; simp
  · simp only [idx, hslot, hfam, hg]
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj

end Params

/-- An execution of strong select (with parameters `A`) in the network `N` under CR4 with
asynchronous start, described by the sets `inf t` of nodes holding the broadcast message at the end
of round `t` (see the module docstring). -/
structure Execution [DecidableEq V] (N : DualGraph V) (A : Params V) where
  /-- The nodes holding the message at the end of round `t` (`t = 0`: initially). -/
  inf : ℕ → Finset V
  /-- Initially only the source holds the message. -/
  init : inf 0 = {N.src}
  /-- Nodes never forget the message. -/
  mono : ∀ t, inf t ⊆ inf (t + 1)
  /-- If `u` is the only sender of round `r`, all its `G`-out-neighbours get the message. -/
  progress : ∀ r, 1 ≤ r → ∀ u, (∀ w, A.Sends inf r w ↔ w = u) → ∀ w, N.E u w → w ∈ inf r

namespace Execution

variable [DecidableEq V] {N : DualGraph V} {A : Params V} (ex : Execution N A)

lemma mono' {a b : ℕ} (h : a ≤ b) : ex.inf a ⊆ ex.inf b :=
  (monotone_nat_of_le_succ ex.mono : Monotone ex.inf) h

lemma src_mem (t : ℕ) : N.src ∈ ex.inf t :=
  ex.mono' (Nat.zero_le t) (by rw [ex.init]; exact mem_singleton_self _)

end Execution

end Podc.BroadcastUnreliableRadio.StrongSelect
