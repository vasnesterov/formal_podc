import Papers.PODC2026.PartialAuthBC.Model

/-!
# The binary gradecast protocol Π_GC (Figure 1)

Parties `P`, registered parties `Reg` (`s = Reg.ncard`), registered sender `snd ∈ Reg`, input bit `b`
of the sender. The protocol runs `s` super rounds of 4 lock-step rounds each (round `r` belongs to
super round `k = r / 4 + 1`, phase `r % 4`):

* round `4(k-1)`     — *Extension*: a registered party that accepted a `(k-1)`-chain `c` sends
  `c ++ [i]` (its signature on `c`); the sender with `b = 1` "accepted the 0-chain `[]`";
* round `4(k-1) + 1` — *Echo1* from unregistered parties that changed `(v, g)` on an Extension;
* round `4(k-1) + 2` — *Echo2* from unregistered parties that set `v := 1` on an Echo1;
* round `4(k-1) + 3` — *Echo3* (to registered parties only) from unregistered parties that set
  `g := 0` on an Echo2.

A message is `(kind, chain)` where `kind` is the phase in which it is sent (`0` = Extension,
`1`/`2`/`3` = Echo1/2/3), and a chain is the list of its signers, sender first. The signature tokens
of a message are the nonempty prefixes of its chain whose last signer is registered (prefix `τ` is
the signature of `τ.getLast` on the chain before it). A chain `c` is a *valid `k`-chain for `i`* if
it has length `k`, starts with the sender, has distinct signers, all registered, and does not
contain `i` (Definition 3.1).

**Reading of Phase 2.** For an unregistered party receiving a valid Extension we use the
*sequential* reading of the two bullets of Figure 1 ("if `v = 0` set `v := 1`; if (now) `v = 1` and
`g = 0` set `g := 1`"), i.e. the party ends with `(v, g) = (1, 1)` and echoes the chain if anything
changed. This is the reading the proof of Lemma 3.10 uses; see `differencies.md` for why the
exclusive reading breaks Lemma 3.10.
-/

namespace PartialAuthBC

open Cslib.Byzantine.LockStep

variable {P : Type}

/-- Messages of Π_GC: `(kind, chain)`. -/
abbrev GMsg (P : Type) := ℕ × List P

/-- Local state of a party in Π_GC. -/
structure GSt (P : Type) where
  /-- number of rounds processed -/
  rnd : ℕ
  /-- current value -/
  v : Bool
  /-- current grade -/
  g : Bool
  /-- the accepted chain (registered parties) -/
  acc : Option (List P)
  /-- the chain to echo in the next round (unregistered parties) -/
  out : Option (List P)

section Defs

variable (Reg : Set P) (snd : P)

/-- `c` is a valid `k`-chain for party `i` (Definition 3.1). -/
def ValidFor (i : P) (k : ℕ) (c : List P) : Prop :=
  c.length = k ∧ c.head? = some snd ∧ c.Nodup ∧ (∀ x ∈ c, x ∈ Reg) ∧ i ∉ c

/-- The valid `k`-chains for `i` received in an inbox in messages of kind `ph`. -/
def validRecv (i : P) (k ph : ℕ) (ib : Inbox P (GMsg P)) : Set (List P) :=
  {c | (∃ q, ib q = some (ph, c)) ∧ ValidFor Reg snd i k c}

open Classical in
/-- Initial state of party `i` with input `b` (only the sender's input matters). -/
noncomputable def ginit (i : P) (b : Bool) : GSt P where
  rnd := 0
  v := decide (i = snd ∧ b = true)
  g := true
  acc := if i = snd ∧ b = true then some [] else none
  out := none

/-- The valid chains relevant for the step of `i` from state `st`. -/
def gE (i : P) (st : GSt P) (ib : Inbox P (GMsg P)) : Set (List P) :=
  validRecv Reg snd i (st.rnd / 4 + 1) (st.rnd % 4) ib

open Classical in
/-- Processing the inbox of round `st.rnd` (Figure 1, phases 2 and 3 and "end of phase 3"). -/
noncomputable def gstep (i : P) (st : GSt P) (ib : Inbox P (GMsg P)) : GSt P :=
  if h : (gE Reg snd i st ib).Nonempty then
    if i ∈ Reg then
      (if st.v then { st with rnd := st.rnd + 1, out := none }
       else { st with rnd := st.rnd + 1, out := none, v := true, acc := some h.some })
    else if st.rnd % 4 = 0 then
      (if st.v ∧ st.g then { st with rnd := st.rnd + 1, out := none }
       else { st with rnd := st.rnd + 1, v := true, g := true, out := some h.some })
    else if st.rnd % 4 = 1 then
      (if st.v then { st with rnd := st.rnd + 1, out := none }
       else { st with rnd := st.rnd + 1, v := true, g := false, out := some h.some })
    else if st.rnd % 4 = 2 then
      (if st.v then { st with rnd := st.rnd + 1, out := none }
       else { st with rnd := st.rnd + 1, g := false, out := some h.some })
    else { st with rnd := st.rnd + 1, out := none }
  else { st with rnd := st.rnd + 1, out := none }

/-- The state of `i` after processing history `h`. -/
noncomputable def gstOf (i : P) (b : Bool) (h : History P (GMsg P)) : GSt P :=
  h.foldl (gstep Reg snd i) (ginit snd i b)

open Classical in
/-- **Π_GC** (Figure 1) as a lock-step protocol with input bit and output `(v, g)`. -/
noncomputable def gc : Protocol P Bool (GMsg P) (Bool × Bool) where
  send i b h q :=
    let st := gstOf Reg snd i b h
    if h.length < 4 * Reg.ncard then
      if h.length % 4 = 0 then
        st.acc.bind fun c =>
          if i ∈ Reg ∧ c.length = h.length / 4 then some (0, c ++ [i]) else none
      else if i ∉ Reg ∧ (h.length % 4 ≠ 3 ∨ q ∈ Reg) then
        st.out.map fun c => (h.length % 4, c)
      else none
    else none
  decide i b h :=
    if 4 * Reg.ncard ≤ h.length then
      some ((gstOf Reg snd i b (h.take (4 * Reg.ncard))).v,
        (gstOf Reg snd i b (h.take (4 * Reg.ncard))).g)
    else none

/-- Signature tokens: nonempty prefixes of the chain whose last signer is registered. -/
def gAuth : Auth P (GMsg P) (List P) where
  signer τ := τ.getLastD snd
  tokens m := {τ | τ ≠ [] ∧ τ <+: m.2 ∧ τ.getLastD snd ∈ Reg}

lemma gAuth_registered : RegisteredSigners Reg (gAuth Reg snd) := fun _ _ hτ => hτ.2.2

end Defs

/-! ### Local invariants (hold for every history) -/

section Local

variable {Reg : Set P} {snd : P}

/-- Chains occurring in a history. -/
def chainsOf (h : History P (GMsg P)) : Set (List P) :=
  {c | ∃ ib ∈ h, ∃ q ph, ib q = some (ph, c)}

lemma gstOf_append (i : P) (b : Bool) (h : History P (GMsg P)) (ib : Inbox P (GMsg P)) :
    gstOf Reg snd i b (h ++ [ib]) = gstep Reg snd i (gstOf Reg snd i b h) ib := by
  simp [gstOf, List.foldl_append]

@[simp] lemma gstOf_nil (i : P) (b : Bool) : gstOf Reg snd i b [] = ginit snd i b := rfl

lemma gstep_rnd (i : P) (st : GSt P) (ib) : (gstep Reg snd i st ib).rnd = st.rnd + 1 := by
  unfold gstep; split_ifs <;> rfl

lemma gstOf_rnd (i : P) (b : Bool) (h : History P (GMsg P)) :
    (gstOf Reg snd i b h).rnd = h.length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h ib ih => simp [gstOf_append, gstep_rnd, ih]

section Step

variable (i : P) (st : GSt P) (ib : Inbox P (GMsg P))

local notation "E" => gE Reg snd i st ib
local notation "S'" => gstep Reg snd i st ib

lemma gstep_v_mono (h : st.v = true) : (S').v = true := by
  unfold gstep; split_ifs <;> simp_all

lemma gstep_v_true (hE : (E).Nonempty) (h : i ∈ Reg ∨ st.rnd % 4 = 0 ∨ st.rnd % 4 = 1) :
    (S').v = true := by
  unfold gstep; split_ifs <;> simp_all

lemma gstep_v_change (h0 : st.v = false) (h1 : (S').v = true) :
    (E).Nonempty ∧ (i ∈ Reg ∨ st.rnd % 4 = 0 ∨ st.rnd % 4 = 1) := by
  unfold gstep at h1; split_ifs at h1 <;> simp_all

lemma gstep_acc : (S').acc = st.acc ∨
    (i ∈ Reg ∧ st.v = false ∧ ∃ c ∈ E, (S').acc = some c ∧ (S').v = true) := by
  unfold gstep; split_ifs with h1 h2 h3 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_v_acc_reg (hi : i ∈ Reg) (h0 : st.v = false) (h1 : (S').v = true) :
    ∃ c ∈ E, (S').acc = some c := by
  unfold gstep at h1 ⊢; split_ifs at h1 ⊢ with h2 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_g_reg (hi : i ∈ Reg) : (S').g = st.g := by
  unfold gstep; split_ifs <;> simp_all

lemma gstep_out : (S').out = none ∨ ∃ c ∈ E, (S').out = some c := by
  unfold gstep; split_ifs with h1 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_vg_ph0 (hi : i ∉ Reg) (hph : st.rnd % 4 = 0) (hE : (E).Nonempty) :
    (S').v = true ∧ (S').g = true := by
  unfold gstep; split_ifs <;> simp_all

lemma gstep_out_v (hi : i ∉ Reg) (h0 : st.v = false) (h1 : (S').v = true) :
    ∃ c ∈ E, (S').out = some c := by
  unfold gstep at h1 ⊢; split_ifs at h1 ⊢ with h2 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_g_ph1 (hi : i ∉ Reg) (h0 : st.v = false) (h1 : (S').v = true)
    (hph : st.rnd % 4 = 1) : (S').g = false := by
  unfold gstep at h1 ⊢; split_ifs at h1 ⊢ <;> simp_all

lemma gstep_g_up (hi : i ∉ Reg) (h0 : st.g = false) (h1 : (S').g = true) :
    st.rnd % 4 = 0 ∧ (S').v = true ∧ ∃ c ∈ E, (S').out = some c := by
  unfold gstep at h1 ⊢; split_ifs at h1 ⊢ with h2 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_g_down (h1 : (S').g = false) (h0 : st.g = true) :
    st.v = false ∧ i ∉ Reg ∧ (st.rnd % 4 = 1 ∨ st.rnd % 4 = 2) ∧
      ∃ c ∈ E, (S').out = some c := by
  unfold gstep at h1 ⊢; split_ifs at h1 ⊢ with h2 <;> simp_all [Set.Nonempty.some_mem]

lemma gstep_g_ph2 (hi : i ∉ Reg) (h0 : st.v = false) (hph : st.rnd % 4 = 2)
    (hE : (E).Nonempty) : (S').g = false := by
  unfold gstep; split_ifs <;> simp_all

lemma gstep_E_empty (hE : ¬ (E).Nonempty) : (S').v = st.v ∧ (S').g = st.g := by
  unfold gstep; split_ifs; all_goals simp_all

end Step

lemma chainsOf_mono (h : History P (GMsg P)) (ib : Inbox P (GMsg P)) :
    chainsOf h ⊆ chainsOf (h ++ [ib]) := by
  rintro c ⟨ib', hib', q, ph, hq⟩
  exact ⟨ib', List.mem_append_left _ hib', q, ph, hq⟩

lemma mem_chainsOf_of_gE {i : P} {st : GSt P} {h : History P (GMsg P)} {ib : Inbox P (GMsg P)}
    {c : List P} (hc : c ∈ gE Reg snd i st ib) : c ∈ chainsOf (h ++ [ib]) := by
  obtain ⟨⟨q, hq⟩, -⟩ := hc
  exact ⟨ib, by simp, q, _, hq⟩

lemma validFor_of_gE {i : P} {st : GSt P} {ib : Inbox P (GMsg P)} {c : List P}
    (hc : c ∈ gE Reg snd i st ib) : ValidFor Reg snd i c.length c := by
  obtain ⟨-, hv⟩ := hc
  have hl := hv.1
  rw [hl]; exact hv

/-- Registered parties: `v = 1` iff a chain has been accepted; the grade stays `1`. -/
lemma gstOf_reg (i : P) (hi : i ∈ Reg) (b : Bool) (h : History P (GMsg P)) :
    ((gstOf Reg snd i b h).v = true ↔ (gstOf Reg snd i b h).acc.isSome) ∧
      (gstOf Reg snd i b h).g = true := by
  induction h using List.reverseRecOn with
  | nil => simp only [gstOf_nil, ginit]; split_ifs <;> simp_all
  | append_singleton h ib ih =>
    rw [gstOf_append]
    refine ⟨?_, by rw [gstep_g_reg _ _ _ hi]; exact ih.2⟩
    rcases gstep_acc (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | ⟨-, h0, c, -, h1, h2⟩
    · rw [h1]
      rcases Bool.eq_false_or_eq_true (gstOf Reg snd i b h).v with hv | hv
      · rw [gstep_v_mono _ _ _ hv]; exact ⟨fun _ => ih.1.1 hv, fun _ => rfl⟩
      · rcases Bool.eq_false_or_eq_true (gstep Reg snd i (gstOf Reg snd i b h) ib).v with hv' | hv'
        · obtain ⟨c, -, hc⟩ := gstep_v_acc_reg i _ ib hi hv hv'
          rw [hc] at h1; rw [← h1]; simp [hv']
        · rw [hv']; have := ih.1; rw [hv] at this; simpa using this
    · rw [h1, h2]; simp

/-- Unregistered parties never accept chains. -/
lemma gstOf_acc_unreg (i : P) (hi : i ∉ Reg) (b : Bool) (h : History P (GMsg P)) :
    (gstOf Reg snd i b h).acc = (ginit snd i b).acc := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h ib ih =>
    rw [gstOf_append]
    rcases gstep_acc (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | h1
    · rw [h1, ih]
    · exact absurd h1.1 hi

/-- Accepted chains persist. -/
lemma gstep_acc_persist {i : P} {b : Bool} {h : History P (GMsg P)} {c : List P}
    (hc : (gstOf Reg snd i b h).acc = some c) (ib : Inbox P (GMsg P)) :
    (gstep Reg snd i (gstOf Reg snd i b h) ib).acc = some c := by
  rcases gstep_acc (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | ⟨hi, h0, -⟩
  · rw [h1, hc]
  · have := ((gstOf_reg (snd := snd) i hi b h).1).2 (by simp [hc])
    rw [h0] at this; exact absurd this (by simp)

lemma gstOf_acc_persist {i : P} {b : Bool} {h : History P (GMsg P)} {c : List P}
    (hc : (gstOf Reg snd i b h).acc = some c) (h' : History P (GMsg P)) :
    (gstOf Reg snd i b (h ++ h')).acc = some c := by
  induction h' using List.reverseRecOn with
  | nil => simpa using hc
  | append_singleton h' ib ih =>
    rw [← List.append_assoc, gstOf_append]; exact gstep_acc_persist ih ib

/-- Accepted chains are the initial `[]` of the sender with input `1`, or received valid chains. -/
lemma gstOf_acc_spec (i : P) (b : Bool) (h : History P (GMsg P)) {c : List P}
    (hc : (gstOf Reg snd i b h).acc = some c) :
    (c = [] ∧ i = snd ∧ b = true) ∨ (ValidFor Reg snd i c.length c ∧ c ∈ chainsOf h) := by
  induction h using List.reverseRecOn generalizing c with
  | nil =>
    simp only [gstOf_nil, ginit] at hc; split_ifs at hc with h1
    · simp at hc; exact Or.inl ⟨hc, h1⟩
  | append_singleton h ib ih =>
    rw [gstOf_append] at hc
    rcases gstep_acc (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | ⟨-, -, c', hc', h1, -⟩
    · rw [h1] at hc
      rcases ih hc with h2 | ⟨h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h2, chainsOf_mono h ib h3⟩
    · rw [h1] at hc; cases hc
      exact Or.inr ⟨validFor_of_gE hc', mem_chainsOf_of_gE hc'⟩

/-- Chains scheduled for echoing were received. -/
lemma gstOf_out_spec (i : P) (b : Bool) (h : History P (GMsg P)) {c : List P}
    (hc : (gstOf Reg snd i b h).out = some c) : c ∈ chainsOf h := by
  induction h using List.reverseRecOn generalizing c with
  | nil => simp [ginit] at hc
  | append_singleton h ib ih =>
    rw [gstOf_append] at hc
    rcases gstep_out (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | ⟨c', hc', h1⟩
    · rw [h1] at hc; cases hc
    · rw [h1] at hc; cases hc; exact mem_chainsOf_of_gE hc'

/-- A chain accepted at some point was accepted by the end of its super round. -/
lemma gstOf_acc_take (i : P) (b : Bool) (h : History P (GMsg P)) {c : List P}
    (hc : (gstOf Reg snd i b h).acc = some c) :
    (gstOf Reg snd i b (h.take (4 * c.length))).acc = some c := by
  induction h using List.reverseRecOn generalizing c with
  | nil => simpa using hc
  | append_singleton h ib ih =>
    by_cases hprev : (gstOf Reg snd i b h).acc = some c
    · by_cases hle : 4 * c.length ≤ h.length
      · rw [List.take_append_of_le_length hle]; exact ih hprev
      · rw [List.take_of_length_le (by simp; omega), gstOf_append]
        exact gstep_acc_persist hprev ib
    · rw [gstOf_append] at hc
      rcases gstep_acc (Reg := Reg) (snd := snd) i (gstOf Reg snd i b h) ib with h1 | ⟨-, -, c', hc', h1, -⟩
      · rw [h1] at hc; exact absurd hc hprev
      · rw [h1] at hc; cases hc
        have hl := hc'.2.1
        rw [gstOf_rnd] at hl
        rw [List.take_of_length_le (by simp; omega), gstOf_append, h1]

/-! ### Unforgeability -/

lemma gc_send_cases {i : P} {b : Bool} {h : History P (GMsg P)} {q : P} {m : GMsg P}
    (hm : (gc Reg snd).send i b h q = some m) :
    h.length < 4 * Reg.ncard ∧
    ((h.length % 4 = 0 ∧ i ∈ Reg ∧ ∃ c, (gstOf Reg snd i b h).acc = some c ∧
        c.length = h.length / 4 ∧ m = (0, c ++ [i])) ∨
      (h.length % 4 ≠ 0 ∧ i ∉ Reg ∧ (h.length % 4 ≠ 3 ∨ q ∈ Reg) ∧
        ∃ c, (gstOf Reg snd i b h).out = some c ∧ m = (h.length % 4, c))) := by
  simp only [gc] at hm
  split_ifs at hm with h1 h2 h3
  · refine ⟨h1, Or.inl ⟨h2, ?_⟩⟩
    obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.mp hm
    split_ifs at hm with h4
    · cases hm; exact ⟨h4.1, c, hc, h4.2, rfl⟩
  · refine ⟨h1, Or.inr ⟨h2, h3.1, h3.2, ?_⟩⟩
    obtain ⟨c, hc, hm⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨c, hc, hm.symm⟩

lemma tokens_of_mem_chainsOf {h : History P (GMsg P)} {c τ : List P} (hc : c ∈ chainsOf h)
    (hτ : τ ≠ [] ∧ τ <+: c ∧ τ.getLastD snd ∈ Reg) : τ ∈ (gAuth Reg snd).histTokens h := by
  obtain ⟨ib, hib, q, ph, hq⟩ := hc
  exact ⟨ib, hib, q, (ph, c), hq, hτ⟩

/-- Honest parties only emit their own signature and relayed signatures. -/
theorem gc_unforging : (gc Reg snd).Unforging (gAuth Reg snd) := by
  intro i b h q m hm τ hτ
  obtain ⟨-, ⟨-, hi, c, hc, -, rfl⟩ | ⟨-, -, -, c, hc, rfl⟩⟩ := gc_send_cases hm
  · obtain ⟨hne, hpre, hreg⟩ := hτ
    rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
    · left; simp [gAuth]
    · right
      rcases gstOf_acc_spec i b h hc with ⟨rfl, -, -⟩ | ⟨-, hch⟩
      · exact absurd (List.prefix_nil.mp hpre') hne
      · exact tokens_of_mem_chainsOf hch ⟨hne, hpre', hreg⟩
  · exact Or.inr (tokens_of_mem_chainsOf (gstOf_out_spec i b h hc) hτ)

end Local

/-! ### Generic facts about lock-step histories -- CSLib candidates -/

section Generic

variable {P I M O : Type*} (G : SimpleGraph P) (alg : Protocol P I M O) (s : Scenario P I M)

/-- Earlier histories are prefixes of later ones. -- CSLib candidate -/
lemma hist_take {r r' : ℕ} (h : r' ≤ r) (p : P) :
    (hist G alg s r p).take r' = hist G alg s r' p := by
  induction r with
  | zero => simp_all
  | succ r ih =>
    rcases Nat.lt_or_ge r' (r + 1) with h' | h'
    · rw [hist_succ, List.take_append_of_le_length (by simp; omega), ih (by omega)]
    · rw [show r' = r + 1 by omega, List.take_of_length_le (by simp)]

/-- An inbox in a history is the inbox of an earlier round. -- CSLib candidate -/
lemma mem_hist {r : ℕ} {p : P} {ib : Inbox P M} (h : ib ∈ hist G alg s r p) :
    ∃ r' < r, ib = fun q => deliver G alg s (hist G alg s r') r' q p := by
  induction r with
  | zero => simp at h
  | succ r ih =>
    rw [hist_succ, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨r', hr', e⟩ := ih h; exact ⟨r', by omega, e⟩
    · exact ⟨r, by omega, rfl⟩

lemma deliver_honest (hrel : s.Reliable) {r : ℕ} {q p : P} (hq : q ∉ s.byz) (hadj : G.Adj q p) :
    deliver G alg s (hist G alg s r) r q p = alg.send q (s.input q) (hist G alg s r q) p := by
  simp [deliver, hadj, hq, hrel r q p]

lemma deliver_byz {r : ℕ} {q p : P} (hq : q ∈ s.byz) (hadj : G.Adj q p) :
    deliver G alg s (hist G alg s r) r q p = s.adv r q p := by
  simp [deliver, hadj, hq]

end Generic

/-! ### Runs of Π_GC -/

section Run

variable {Reg : Set P} {snd : P} (s : Scenario P Bool (GMsg P))

/-- History of `p` after `r` rounds of Π_GC in scenario `s`. -/
noncomputable abbrev gH (Reg : Set P) (snd : P) (r : ℕ) (p : P) : History P (GMsg P) :=
  hist ⊤ (gc Reg snd) s r p

/-- State of `p` after `r` rounds of Π_GC in scenario `s`. -/
noncomputable def gS (Reg : Set P) (snd : P) (r : ℕ) (p : P) : GSt P :=
  gstOf Reg snd p (s.input p) (gH s Reg snd r p)

/-- The inbox of `p` in round `r`. -/
noncomputable def gIB (Reg : Set P) (snd : P) (r : ℕ) (p : P) : Inbox P (GMsg P) :=
  fun q => deliver ⊤ (gc Reg snd) s (hist ⊤ (gc Reg snd) s r) r q p

lemma gS_succ (r : ℕ) (p : P) :
    gS s Reg snd (r + 1) p = gstep Reg snd p (gS s Reg snd r p) (gIB s Reg snd r p) := by
  simp only [gS, gH, hist_succ, gstOf_append]; rfl

@[simp] lemma gS_rnd (r : ℕ) (p : P) : (gS s Reg snd r p).rnd = r := by
  simp [gS, gstOf_rnd]

lemma gS_zero (p : P) : gS s Reg snd 0 p = ginit snd p (s.input p) := rfl

lemma gS_v_mono {r r' : ℕ} (hr : r ≤ r') {p : P} (h : (gS s Reg snd r p).v = true) :
    (gS s Reg snd r' p).v = true := by
  induction r', hr using Nat.le_induction with
  | base => exact h
  | succ r' _ ih => rw [gS_succ]; exact gstep_v_mono _ _ _ ih

lemma gS_acc_persist {r r' : ℕ} (hr : r ≤ r') {p : P} {c : List P}
    (h : (gS s Reg snd r p).acc = some c) : (gS s Reg snd r' p).acc = some c := by
  have e : gH s Reg snd r' p = gH s Reg snd r p ++ (gH s Reg snd r' p).drop r := by
    simp only [gH]; rw [← hist_take ⊤ (gc Reg snd) s hr p, List.take_append_drop]
  unfold gS; rw [e]; exact gstOf_acc_persist h _

/-- A chain accepted by round `r` is held from round `4 |c|` on. -/
lemma gS_acc_from {r r' : ℕ} {p : P} {c : List P} (h : (gS s Reg snd r p).acc = some c)
    (hr' : 4 * c.length ≤ r') : (gS s Reg snd r' p).acc = some c := by
  rcases le_or_gt (4 * c.length) r with hle | hlt
  · have h1 := gstOf_acc_take p (s.input p) _ h
    rw [hist_take ⊤ (gc Reg snd) s hle p] at h1
    exact gS_acc_persist s hr' h1
  · exact gS_acc_persist s (by omega) h

lemma gS_reg {p : P} (hp : p ∈ Reg) (r : ℕ) :
    ((gS s Reg snd r p).v = true ↔ (gS s Reg snd r p).acc.isSome) ∧ (gS s Reg snd r p).g = true :=
  gstOf_reg p hp _ _

lemma gS_acc_spec {r : ℕ} {p : P} {c : List P} (h : (gS s Reg snd r p).acc = some c) :
    (c = [] ∧ p = snd ∧ s.input p = true) ∨
      (ValidFor Reg snd p c.length c ∧ c ∈ chainsOf (gH s Reg snd r p)) :=
  gstOf_acc_spec p _ _ h

/-! #### Messages between honest parties -/

variable (hrel : s.Reliable)
include hrel

lemma gIB_honest {r : ℕ} {q p : P} (hq : q ∉ s.byz) (hqp : q ≠ p) :
    gIB s Reg snd r p q = (gc Reg snd).send q (s.input q) (gH s Reg snd r q) p :=
  deliver_honest ⊤ _ s hrel hq hqp

lemma gIB_ext {r : ℕ} {q p : P} (hq : q ∉ s.byz) (hqp : q ≠ p) (hqR : q ∈ Reg)
    (hr : r < 4 * Reg.ncard) (hr4 : r % 4 = 0) {c : List P}
    (hc : (gS s Reg snd r q).acc = some c) (hl : c.length = r / 4) :
    gIB s Reg snd r p q = some (0, c ++ [q]) := by
  rw [gIB_honest s hrel hq hqp]
  have hlen : (gH s Reg snd r q).length = r := length_hist _ _ _ _ _
  unfold gS at hc
  generalize gH s Reg snd r q = h at hc hlen
  subst hlen
  simp [gc, hr, hr4, hc, hqR, hl]

lemma gIB_echo {r : ℕ} {q p : P} (hq : q ∉ s.byz) (hqp : q ≠ p) (hqR : q ∉ Reg)
    (hr : r < 4 * Reg.ncard) (hr4 : r % 4 ≠ 0) (hr3 : r % 4 ≠ 3 ∨ p ∈ Reg) {c : List P}
    (hc : (gS s Reg snd r q).out = some c) :
    gIB s Reg snd r p q = some (r % 4, c) := by
  rw [gIB_honest s hrel hq hqp]
  have hlen : (gH s Reg snd r q).length = r := length_hist _ _ _ _ _
  unfold gS at hc
  generalize gH s Reg snd r q = h at hc hlen
  subst hlen
  simp [gc, hr, hr4, hc, hqR, hr3]

/-! #### Origin of signatures -/

/-- The token `τ` (signed by `i = τ.getLastD snd`) is `c ++ [i]` for a chain `c` that `i` held at
round `4 |c|`, no later than round `r`. -/
def gOrigin (Reg : Set P) (snd : P) (r : ℕ) (τ : List P) : Prop :=
  ∃ c, τ = c ++ [τ.getLastD snd] ∧ 4 * c.length ≤ r ∧
    (gS s Reg snd (4 * c.length) (τ.getLastD snd)).acc = some c

omit hrel in
lemma gOrigin_mono {r r' : ℕ} (h : r ≤ r') {τ : List P} (ho : gOrigin s Reg snd r τ) :
    gOrigin s Reg snd r' τ := by
  obtain ⟨c, h1, h2, h3⟩ := ho; exact ⟨c, h1, by omega, h3⟩

variable (hV : s.AuthValid ⊤ (gc Reg snd) (gAuth Reg snd))
include hV

lemma recv_aux (r : ℕ)
    (IH : ∀ r' < r, ∀ q, q ∉ s.byz → ∀ p, q ≠ p → ∀ m,
      (gc Reg snd).send q (s.input q) (gH s Reg snd r' q) p = some m →
      ∀ τ ∈ (gAuth Reg snd).tokens m, τ.getLastD snd ∉ s.byz → gOrigin s Reg snd r' τ)
    {p : P} (hp : p ∉ s.byz) {τ : List P}
    (hτ : τ ∈ (gAuth Reg snd).histTokens (gH s Reg snd r p)) (hs : τ.getLastD snd ∉ s.byz) :
    ∃ r' < r, gOrigin s Reg snd r' τ := by
  obtain ⟨ib, hib, q, m, hq, hτm⟩ := hτ
  obtain ⟨r', hr', rfl⟩ := mem_hist _ _ _ hib
  simp only at hq
  by_cases hqp : q = p
  · subst hqp; simp [deliver] at hq
  by_cases hqb : q ∈ s.byz
  · rw [deliver_byz _ _ _ hqb hqp] at hq
    rcases hV r' q p m hqb hp hqp hq τ hτm with h | ⟨r'', hr'', q', hq', p', hadj, m', hm', hτ'⟩
    · exact absurd h hs
    · exact ⟨r'', by omega, IH r'' (by omega) q' hq' p' hadj m' hm' τ hτ' hs⟩
  · rw [deliver_honest _ _ _ hrel hqb hqp] at hq
    exact ⟨r', hr', IH r' hr' q hqb p hqp m hq τ hτm hs⟩

/-- Every signature of an honest party emitted by an honest party originates from an Extension. -/
lemma emit_origin (r : ℕ) : ∀ q, q ∉ s.byz → ∀ p, q ≠ p → ∀ m,
    (gc Reg snd).send q (s.input q) (gH s Reg snd r q) p = some m →
    ∀ τ ∈ (gAuth Reg snd).tokens m, τ.getLastD snd ∉ s.byz → gOrigin s Reg snd r τ := by
  induction r using Nat.strong_induction_on with
  | _ r IH =>
  intro q hq p hqp m hm τ hτ hs
  obtain ⟨-, ⟨h4, hqR, c, hc, hl, rfl⟩ | ⟨-, -, -, c, hc, rfl⟩⟩ := gc_send_cases hm
  · rw [length_hist] at h4 hl
    obtain ⟨hne, hpre, hreg⟩ := hτ
    rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
    · refine ⟨c, by simp, by omega, ?_⟩
      rw [List.getLastD_concat, show 4 * c.length = r by omega]; exact hc
    · rcases gstOf_acc_spec q _ _ hc with ⟨rfl, -, -⟩ | ⟨-, hch⟩
      · exact absurd (List.prefix_nil.mp hpre') hne
      · obtain ⟨r', hr', ho⟩ := recv_aux s hrel hV r IH hq
          (tokens_of_mem_chainsOf hch ⟨hne, hpre', hreg⟩) hs
        exact gOrigin_mono s hr'.le ho
  · obtain ⟨r', hr', ho⟩ := recv_aux s hrel hV r IH hq
      (tokens_of_mem_chainsOf (gstOf_out_spec q _ _ hc) hτ) hs
    exact gOrigin_mono s hr'.le ho

lemma recv_origin {r : ℕ} {p : P} (hp : p ∉ s.byz) {τ : List P}
    (hτ : τ ∈ (gAuth Reg snd).histTokens (gH s Reg snd r p)) (hs : τ.getLastD snd ∉ s.byz) :
    ∃ r' < r, gOrigin s Reg snd r' τ :=
  recv_aux s hrel hV r (fun r' _ => emit_origin s hrel hV r') hp hτ hs

/-- If an honest party has received a chain containing the signature of an honest registered
party `i`, then `i` had already accepted a chain (so `v_i = 1`). -/
lemma signed_v {r : ℕ} {p i : P} (hp : p ∉ s.byz) (hi : i ∉ s.byz) (hiR : i ∈ Reg)
    {c : List P} (hc : c ∈ chainsOf (gH s Reg snd r p)) (hcR : ∀ x ∈ c, x ∈ Reg) (hic : i ∈ c) :
    (gS s Reg snd r i).v = true := by
  obtain ⟨c₁, c₂, rfl⟩ := List.append_of_mem hic
  have hτ : c₁ ++ [i] ∈ (gAuth Reg snd).histTokens (gH s Reg snd r p) :=
    tokens_of_mem_chainsOf hc ⟨by simp, ⟨c₂, by simp⟩, by rw [List.getLastD_concat]; exact hiR⟩
  obtain ⟨r', hr', c', -, hle, hacc⟩ := recv_origin s hrel hV hp hτ (by rw [List.getLastD_concat]; exact hi)
  rw [List.getLastD_concat] at hacc
  have hv := ((gS_reg (snd := snd) s hiR (4 * c'.length)).1).2 (by simp [hacc])
  exact gS_v_mono s (by omega) hv

/-- If an honest party has received a chain starting with the honest sender's signature, the
sender's input is `1`. -/
lemma signed_sender {r : ℕ} {p : P} (hp : p ∉ s.byz) (hsnd : snd ∉ s.byz) (hsR : snd ∈ Reg)
    {c : List P} (hc : c ∈ chainsOf (gH s Reg snd r p)) (hhead : c.head? = some snd) :
    s.input snd = true := by
  obtain ⟨c₂, rfl⟩ : ∃ c₂, c = snd :: c₂ := by
    cases c with
    | nil => simp at hhead
    | cons a c₂ => simp at hhead; exact ⟨c₂, by rw [hhead]⟩
  have hτ : [snd] ∈ (gAuth Reg snd).histTokens (gH s Reg snd r p) :=
    tokens_of_mem_chainsOf hc ⟨by simp, ⟨c₂, by simp⟩, by simpa using hsR⟩
  obtain ⟨r', -, c', he, -, hacc⟩ := recv_origin s hrel hV hp hτ (by simpa using hsnd)
  have : c' = [] := by
    have := congrArg List.length he; simp at this; exact this
  subst this
  simp only [List.length_nil, mul_zero] at hacc
  rw [show ([snd] : List P).getLastD snd = snd by rfl, gS_zero] at hacc
  simp only [ginit] at hacc
  split_ifs at hacc with h1
  · exact h1.2

end Run

/-! ### Properties of Π_GC -/

/-- A change point of a Boolean sequence. -/
lemma exists_change {f : ℕ → Bool} {a b : ℕ} (hab : a ≤ b) (ha : f a = false) (hb : f b = true) :
    ∃ r, a ≤ r ∧ r < b ∧ f r = false ∧ f (r + 1) = true := by
  induction b, hab using Nat.le_induction with
  | base => simp_all
  | succ b hab ih =>
    rcases Bool.eq_false_or_eq_true (f b) with h | h
    · obtain ⟨r, h1, h2, h3, h4⟩ := ih h; exact ⟨r, h1, by omega, h3, h4⟩
    · exact ⟨b, hab, by omega, h, hb⟩

/-- A valid chain for a registered party is shorter than `s`. -/
lemma validFor_length_lt [Finite P] {Reg : Set P} {snd i : P} {k : ℕ} {c : List P}
    (h : ValidFor Reg snd i k c) (hi : i ∈ Reg) : k < Reg.ncard := by
  classical
  obtain ⟨hl, -, hnd, hR, hic⟩ := h
  have h1 : ((c.toFinset : Finset P) : Set P) ⊆ Reg \ {i} := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset] at hx
    exact ⟨hR x hx, by rintro rfl; exact hic hx⟩
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h2
  have h3 := Set.ncard_sdiff_singleton_lt_of_mem hi (Set.toFinite Reg)
  omega

section Props

variable [Finite P] {Reg : Set P} {snd : P} (s : Scenario P Bool (GMsg P))
  (hrel : s.Reliable) (hV : s.AuthValid ⊤ (gc Reg snd) (gAuth Reg snd)) (hsR : snd ∈ Reg)

local notation "T" => 4 * Reg.ncard

lemma ncard_pos (hsR : snd ∈ Reg) : 0 < Reg.ncard :=
  Set.ncard_pos (Set.toFinite _) |>.mpr ⟨snd, hsR⟩

omit [Finite P] in
lemma mem_chainsOf_succ {r : ℕ} {p q : P} {ph : ℕ} {c : List P}
    (h : gIB s Reg snd r p q = some (ph, c)) : c ∈ chainsOf (gH s Reg snd (r + 1) p) :=
  ⟨gIB s Reg snd r p, by simp [gH, hist_succ]; right; rfl, q, ph, h⟩

omit [Finite P] in
lemma mem_gE {r : ℕ} {p q : P} {c : List P} (h : gIB s Reg snd r p q = some (r % 4, c))
    (hv : ValidFor Reg snd p (r / 4 + 1) c) :
    c ∈ gE Reg snd p (gS s Reg snd r p) (gIB s Reg snd r p) := by
  simp only [gE, gS_rnd]; exact ⟨⟨q, h⟩, hv⟩

omit [Finite P] in
lemma mem_chainsOf_of_mem_gE {r : ℕ} {p : P} {c : List P}
    (h : c ∈ gE Reg snd p (gS s Reg snd r p) (gIB s Reg snd r p)) :
    c ∈ chainsOf (gH s Reg snd (r + 1) p) := by
  obtain ⟨⟨q, hq⟩, -⟩ := h; exact mem_chainsOf_succ s hq

omit [Finite P] in
lemma validFor_of_mem_gE {r : ℕ} {p : P} {c : List P}
    (h : c ∈ gE Reg snd p (gS s Reg snd r p) (gIB s Reg snd r p)) :
    ValidFor Reg snd p (r / 4 + 1) c := by
  have := h.2; simpa only [gS_rnd] using this

omit [Finite P] in
lemma gS_v_unreg_zero {p : P} (hp : p ∉ Reg) (hsR : snd ∈ Reg) : (gS s Reg snd 0 p).v = false := by
  have : p ≠ snd := by rintro rfl; exact hp hsR
  simp [gS_zero, ginit, this]

include hrel hV hsR

/-- An honest registered party holding a chain `c` extends it in super round `|c| + 1`, and every
honest party has `v = 1` after that round. -/
lemma reg_extends {r : ℕ} {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg) {c : List P}
    (hacc : (gS s Reg snd r k).acc = some c) :
    c.length < Reg.ncard ∧ ∀ j, j ∉ s.byz →
      (gS s Reg snd (4 * c.length + 1) j).v = true ∧
      (j ∉ c ++ [k] → j ≠ k → c ++ [k] ∈ gE Reg snd j (gS s Reg snd (4 * c.length) j)
        (gIB s Reg snd (4 * c.length) j)) := by
  have hacc' : (gS s Reg snd (4 * c.length) k).acc = some c := gS_acc_from s hacc le_rfl
  have key : c.length < Reg.ncard ∧ (∀ x ∈ c ++ [k], x ∈ Reg) ∧ (c ++ [k]).Nodup ∧
      (c ++ [k]).head? = some snd := by
    rcases gS_acc_spec s hacc with ⟨rfl, rfl, -⟩ | ⟨hv, -⟩
    · exact ⟨ncard_pos hsR, by simpa using hkR, by simp, rfl⟩
    · obtain ⟨-, hh, hnd, hR, hkc⟩ := id hv
      refine ⟨validFor_length_lt hv hkR, ?_, ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with hx | rfl; exacts [hR x hx, hkR]
      · simp [List.nodup_append, hnd]; intro x hx rfl; exact hkc hx
      · cases c with
        | nil => simp at hh
        | cons a c => simpa using hh
  obtain ⟨hlt, hR, hnd, hh⟩ := key
  have hval : ∀ j, j ∉ c ++ [k] → ValidFor Reg snd j (4 * c.length / 4 + 1) (c ++ [k]) :=
    fun j hj => ⟨by simp, hh, hnd, hR, hj⟩
  refine ⟨hlt, fun j hj => ?_⟩
  have hrecv : j ≠ k → gIB s Reg snd (4 * c.length) j k = some (0, c ++ [k]) := fun hjk =>
    gIB_ext s hrel hk (Ne.symm hjk) hkR (by omega) (by omega) hacc' (by omega)
  have hE : j ∉ c ++ [k] → j ≠ k → c ++ [k] ∈ gE Reg snd j (gS s Reg snd (4 * c.length) j)
      (gIB s Reg snd (4 * c.length) j) := fun hjc hjk =>
    mem_gE s (by rw [hrecv hjk]; congr 2; omega) (hval j hjc)
  refine ⟨?_, hE⟩
  by_cases hjk : j = k
  · subst hjk
    exact gS_v_mono s (Nat.le_succ _) (((gS_reg s hkR _).1).2 (by simp [hacc']))
  by_cases hjc : j ∈ c ++ [k]
  · have hjR : j ∈ Reg := hR j hjc
    exact signed_v s hrel hV hj hj hjR (mem_chainsOf_succ s (hrecv hjk)) hR hjc
  · rw [gS_succ]
    exact gstep_v_true _ _ _ ⟨_, hE hjc hjk⟩ (Or.inr (Or.inl (by simp)))

/-- **Lemma 3.3.** If an honest registered party ends with `v = 1`, every honest party does. -/
lemma lemma33 {r : ℕ} {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg)
    (hv : (gS s Reg snd r k).v = true) {j : P} (hj : j ∉ s.byz) : (gS s Reg snd T j).v = true := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (((gS_reg s hkR r).1).1 hv)
  obtain ⟨hlt, h⟩ := reg_extends s hrel hV hsR hk hkR hc
  exact gS_v_mono s (by omega) (h j hj).1

omit [Finite P] hV hsR in
/-- An echo sent by an honest unregistered party in phase `r % 4 + 1` is a valid chain for every
honest receiver not on it. -/
lemma echo_recv {r : ℕ} {j p : P} (hj : j ∉ s.byz) (hjR : j ∉ Reg) (hr : r < T) (h4 : r % 4 ≠ 3)
    {c : List P} (hout : (gS s Reg snd (r + 1) j).out = some c)
    (hc : c ∈ gE Reg snd j (gS s Reg snd r j) (gIB s Reg snd r j))
    (hpj : j ≠ p) (hpc : p ∉ c) (h3 : r % 4 ≠ 2 ∨ p ∈ Reg) :
    c ∈ gE Reg snd p (gS s Reg snd (r + 1) p) (gIB s Reg snd (r + 1) p) := by
  have hrecv := gIB_echo s hrel hj hpj hjR (r := r + 1) (by omega) (by omega)
    (h3.imp (fun _ => by omega) id) hout
  obtain ⟨hl, hh, hnd, hR, -⟩ := validFor_of_mem_gE s hc
  exact mem_gE s hrecv ⟨by rw [hl]; omega, hh, hnd, hR, hpc⟩

/-- **Lemma 3.4.** If an honest registered party ends with `v = 0`, every honest party does. -/
lemma lemma34 {i : P} (hi : i ∉ s.byz) (hiR : i ∈ Reg) (hv : (gS s Reg snd T i).v = false)
    {j : P} (hj : j ∉ s.byz) : (gS s Reg snd T j).v = false := by
  by_contra hvj
  rw [Bool.not_eq_false] at hvj
  by_cases hjR : j ∈ Reg
  · have := lemma33 s hrel hV hsR hj hjR hvj hi; simp_all
  obtain ⟨r, -, hr, h0, h1⟩ := exists_change (f := fun r => (gS s Reg snd r j).v) (Nat.zero_le T)
    (gS_v_unreg_zero s hjR hsR) hvj
  rw [gS_succ] at h1
  obtain ⟨-, hph⟩ := gstep_v_change _ _ _ h0 h1
  obtain ⟨c, hc, hout⟩ := gstep_out_v _ _ _ hjR h0 h1
  rw [← gS_succ] at hout
  simp only [gS_rnd] at hph
  have hph' : r % 4 = 0 ∨ r % 4 = 1 := by tauto
  by_cases hic : i ∈ c
  · have := signed_v s hrel hV hj hi hiR (mem_chainsOf_of_mem_gE s hc)
      (validFor_of_mem_gE s hc).2.2.2.1 hic
    have := gS_v_mono s (show r + 1 ≤ T by omega) this
    simp_all
  have hE := echo_recv s hrel hj hjR hr (by omega) hout hc (by rintro rfl; exact hjR hiR)
    hic (Or.inr hiR)
  have h2 : (gS s Reg snd (r + 2) i).v = true := by
    rw [gS_succ]; exact gstep_v_true _ _ _ ⟨_, hE⟩ (Or.inl hiR)
  have := gS_v_mono s (show r + 2 ≤ T by omega) h2
  simp_all

omit [Finite P] hrel hV hsR in
/-- Once `v = g = 1`, the grade stays `1`. -/
lemma g_stays {r r' : ℕ} {j : P} (hv : (gS s Reg snd r j).v = true)
    (hg : (gS s Reg snd r j).g = true) (hr : r ≤ r') : (gS s Reg snd r' j).g = true := by
  induction r', hr using Nat.le_induction with
  | base => exact hg
  | succ r' hr ih =>
    by_contra h
    rw [Bool.not_eq_true, gS_succ] at h
    have := (gstep_g_down _ _ _ h ih).1
    rw [gS_v_mono s hr hv] at this; simp at this

/-- **Lemma 3.5.** If some registered party is honest, all honest parties end with its value. -/
lemma lemma35 {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg) {j : P} (hj : j ∉ s.byz) :
    (gS s Reg snd T j).v = (gS s Reg snd T k).v := by
  rcases Bool.eq_false_or_eq_true (gS s Reg snd T k).v with h | h
  · rw [h]; exact lemma33 s hrel hV hsR hk hkR h hj
  · rw [h]; exact lemma34 s hrel hV hsR hk hkR h hj

/-- **Lemma 3.6 (validity).** With an honest sender, every honest party ends with
`(v, g) = (b, 1)`. -/
lemma lemma36 (hsnd : snd ∉ s.byz) {j : P} (hj : j ∉ s.byz) :
    (gS s Reg snd T j).v = s.input snd ∧ (gS s Reg snd T j).g = true := by
  rcases Bool.eq_false_or_eq_true (s.input snd) with hb | hb
  · have h0 : (gS s Reg snd 0 snd).acc = some [] := by simp [gS_zero, ginit, hb]
    obtain ⟨hlt, h⟩ := reg_extends s hrel hV hsR hsnd hsR h0
    simp only [List.length_nil, mul_zero, zero_add, List.nil_append] at h
    have hv1 := (h j hj).1
    refine ⟨by rw [hb]; exact gS_v_mono s (by omega) hv1, ?_⟩
    by_cases hjR : j ∈ Reg
    · exact (gS_reg s hjR T).2
    have hE := (h j hj).2 (by simp; rintro rfl; exact hjR hsR) (by rintro rfl; exact hjR hsR)
    have hg1 : (gS s Reg snd 1 j).g = true := by
      rw [gS_succ]; exact (gstep_vg_ph0 _ _ _ hjR (by simp) ⟨_, hE⟩).2
    exact g_stays s hv1 hg1 (by omega)
  · -- no honest party ever receives a valid chain
    have hempty : ∀ r, ¬ (gE Reg snd j (gS s Reg snd r j) (gIB s Reg snd r j)).Nonempty := by
      rintro r ⟨c, hc⟩
      have := signed_sender s hrel hV hj hsnd hsR (mem_chainsOf_of_mem_gE s hc)
        (validFor_of_mem_gE s hc).2.1
      rw [hb] at this; simp at this
    have key : ∀ r, (gS s Reg snd r j).v = (gS s Reg snd 0 j).v ∧ (gS s Reg snd r j).g = true := by
      intro r
      induction r with
      | zero => exact ⟨rfl, rfl⟩
      | succ r ih =>
        rw [gS_succ]
        obtain ⟨h1, h2⟩ := gstep_E_empty _ _ _ (hempty r)
        exact ⟨h1.trans ih.1, h2.trans ih.2⟩
    refine ⟨?_, (key T).2⟩
    rw [(key T).1, hb]
    by_cases hjs : j = snd
    · subst hjs; simp [gS_zero, ginit, hb]
    · simp [gS_zero, ginit, hjs]

omit [Finite P] hrel hV in
/-- An unregistered honest party with `v = 1` echoed a chain in an Echo1 message (phase 1), unless
it set `v = 1` in phase 1 (then its grade became `0`). -/
lemma unreg_echo1 {i : P} (hiR : i ∉ Reg) (hv : (gS s Reg snd T i).v = true)
    (hg : (gS s Reg snd T i).g = true) :
    ∃ r < T, r % 4 = 0 ∧ ∃ c ∈ gE Reg snd i (gS s Reg snd r i) (gIB s Reg snd r i),
      (gS s Reg snd (r + 1) i).out = some c := by
  obtain ⟨r, -, hr, h0, h1⟩ := exists_change (f := fun r => (gS s Reg snd r i).v) (Nat.zero_le T)
    (gS_v_unreg_zero s hiR hsR) hv
  try simp only at h0 h1
  rw [gS_succ] at h1
  obtain ⟨-, hph⟩ := gstep_v_change _ _ _ h0 h1
  obtain ⟨c, hc, hout⟩ := gstep_out_v _ _ _ hiR h0 h1
  simp only [gS_rnd] at hph
  rcases hph with hph | hph | hph
  · exact absurd hph hiR
  · exact ⟨r, hr, hph, c, hc, by rw [gS_succ]; exact hout⟩
  · have hg0 : (gS s Reg snd (r + 1) i).g = false := by
      rw [gS_succ]; exact gstep_g_ph1 _ _ _ hiR h0 h1 (by simpa using hph)
    obtain ⟨r', hr1, hr2, h2, h3⟩ := exists_change (f := fun r => (gS s Reg snd r i).g)
      (show r + 1 ≤ T by omega) hg0 hg
    try simp only at h2 h3
    rw [gS_succ] at h3
    obtain ⟨hph', -, c', hc', hout'⟩ := gstep_g_up _ _ _ hiR h2 h3
    exact ⟨r', hr2, by simpa using hph', c', hc', by rw [gS_succ]; exact hout'⟩

/-- **Lemma 3.7 (graded consistency).** -/
lemma lemma37 {i j : P} (hi : i ∉ s.byz) (hj : j ∉ s.byz) (hg : (gS s Reg snd T i).g = true) :
    (gS s Reg snd T j).v = (gS s Reg snd T i).v := by
  by_cases hk : ∃ k, k ∉ s.byz ∧ k ∈ Reg
  · obtain ⟨k, hk, hkR⟩ := hk
    rw [lemma35 s hrel hV hsR hk hkR hj, lemma35 s hrel hV hsR hk hkR hi]
  push Not at hk
  have hiR : i ∉ Reg := fun h => hk i hi h
  have hjR : j ∉ Reg := fun h => hk j hj h
  by_cases hij : i = j
  · rw [hij]
  rcases Bool.eq_false_or_eq_true (gS s Reg snd T i).v with hv | hv
  · -- Case 1: `v_i = 1`
    rw [hv]
    obtain ⟨r, hr, h4, c, hc, hout⟩ := unreg_echo1 s hsR hiR hv hg
    have hjc : j ∉ c := fun h => hjR ((validFor_of_mem_gE s hc).2.2.2.1 j h)
    have hE := echo_recv s hrel hi hiR hr (by omega) hout hc hij hjc (Or.inl (by omega))
    have h2 : (gS s Reg snd (r + 2) j).v = true := by
      rw [gS_succ]; exact gstep_v_true _ _ _ ⟨_, hE⟩ (Or.inr (Or.inr (by simp; omega)))
    exact gS_v_mono s (by omega) h2
  · -- Case 2: `v_i = 0`
    rw [hv]
    by_contra hvj
    rw [Bool.not_eq_false] at hvj
    obtain ⟨r, -, hr, h0, h1⟩ := exists_change (f := fun r => (gS s Reg snd r j).v)
      (Nat.zero_le T) (gS_v_unreg_zero s hjR hsR) hvj
    try simp only at h0 h1
    rw [gS_succ] at h1
    obtain ⟨-, hph⟩ := gstep_v_change _ _ _ h0 h1
    obtain ⟨c, hc, hout⟩ := gstep_out_v _ _ _ hjR h0 h1
    rw [← gS_succ] at hout
    simp only [gS_rnd] at hph
    replace hph := hph.resolve_left hjR
    have hic : i ∉ c := fun h => hiR ((validFor_of_mem_gE s hc).2.2.2.1 i h)
    have hE := echo_recv s hrel hj hjR hr (by omega) hout hc (Ne.symm hij) hic
      (Or.inl (by omega))
    have hvi1 : (gS s Reg snd (r + 1) i).v = false := by
      by_contra h; rw [Bool.not_eq_false] at h
      have := gS_v_mono s (show r + 1 ≤ T by omega) h; simp_all
    rcases hph with hph | hph
    · have h2 : (gS s Reg snd (r + 2) i).v = true := by
        rw [gS_succ]; exact gstep_v_true _ _ _ ⟨_, hE⟩ (Or.inr (Or.inr (by simp; omega)))
      have := gS_v_mono s (show r + 2 ≤ T by omega) h2; simp_all
    · have hg2 : (gS s Reg snd (r + 2) i).g = false := by
        rw [gS_succ]; exact gstep_g_ph2 _ _ _ hiR hvi1 (by simp; omega) ⟨_, hE⟩
      obtain ⟨r', -, hr2, h2, h3⟩ := exists_change (f := fun r => (gS s Reg snd r i).g)
        (show r + 2 ≤ T by omega) hg2 hg
      try simp only at h2 h3
      rw [gS_succ] at h3
      have h4 := (gstep_g_up _ _ _ hiR h2 h3).2.1
      rw [← gS_succ] at h4
      have := gS_v_mono s (show r' + 1 ≤ T by omega) h4; simp_all

/-- **Lemma 3.10 (special grade-1 property).** If some registered party is honest, every honest
party ends with grade `1`. -/
lemma lemma310 {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg) {j : P} (hj : j ∉ s.byz) :
    (gS s Reg snd T j).g = true := by
  by_cases hjR : j ∈ Reg
  · exact (gS_reg s hjR T).2
  have hjk : j ≠ k := by rintro rfl; exact hjR hkR
  rcases Bool.eq_false_or_eq_true (gS s Reg snd T k).v with hv | hv
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (((gS_reg s hkR T).1).1 hv)
    obtain ⟨hlt, h⟩ := reg_extends s hrel hV hsR hk hkR hc
    have hjc : j ∉ c ++ [k] := fun hm => hjR (by
      rcases gS_acc_spec s hc with ⟨rfl, -, -⟩ | ⟨hval, -⟩
      · simp at hm; rw [hm]; exact hkR
      · simp at hm; rcases hm with hm | rfl; exacts [hval.2.2.2.1 j hm, hkR])
    have hE := (h j hj).2 hjc hjk
    have hvg := gstep_vg_ph0 _ _ _ hjR (by simp) ⟨_, hE⟩
    rw [← gS_succ] at hvg
    exact g_stays s hvg.1 hvg.2 (by omega)
  · by_contra hg
    rw [Bool.not_eq_true] at hg
    have hvj : (gS s Reg snd T j).v = false := by rw [lemma35 s hrel hV hsR hk hkR hj, hv]
    obtain ⟨r, -, hr, h0, h1⟩ := exists_change (f := fun r => !(gS s Reg snd r j).g)
      (Nat.zero_le T) (by simp [gS_zero, ginit]) (by simp [hg])
    simp only [Bool.not_eq_false', Bool.not_eq_true'] at h0 h1
    rw [gS_succ] at h1
    obtain ⟨hv0, -, hph, c, hc, hout⟩ := gstep_g_down _ _ _ h1 h0
    rw [← gS_succ] at hout
    simp only [gS_rnd] at hph
    rcases hph with hph | hph
    · have h2 : (gS s Reg snd (r + 1) j).v = true := by
        rw [gS_succ]; exact gstep_v_true _ _ _ ⟨_, hc⟩ (Or.inr (Or.inr (by rw [gS_rnd]; exact hph)))
      have := gS_v_mono s (show r + 1 ≤ T by omega) h2; simp_all
    · by_cases hkc : k ∈ c
      · have := signed_v s hrel hV hj hk hkR (mem_chainsOf_of_mem_gE s hc)
          (validFor_of_mem_gE s hc).2.2.2.1 hkc
        have := gS_v_mono s (show r + 1 ≤ T by omega) this; simp_all
      have hE := echo_recv s hrel hj hjR hr (by omega) hout hc hjk hkc (Or.inr hkR)
      have h2 : (gS s Reg snd (r + 2) k).v = true := by
        rw [gS_succ]; exact gstep_v_true _ _ _ ⟨_, hE⟩ (Or.inl hkR)
      have := gS_v_mono s (show r + 2 ≤ T by omega) h2; simp_all

end Props



/-! ### Decisions and the main theorems -/

/-- Π_GC decides at round `4s` the final state `(v, g)`. -/
lemma gc_decides {Reg : Set P} {snd : P} (s : Scenario P Bool (GMsg P)) (p : P) (o : Bool × Bool) :
    Decides ⊤ (gc Reg snd) s p o ↔
      o = ((gS s Reg snd (4 * Reg.ncard) p).v, (gS s Reg snd (4 * Reg.ncard) p).g) := by
  have hst : ∀ r, status ⊤ (gc Reg snd) s r p =
      if 4 * Reg.ncard ≤ r then some ((gS s Reg snd (4 * Reg.ncard) p).v,
        (gS s Reg snd (4 * Reg.ncard) p).g) else none := by
    intro r
    simp only [status, gc, length_hist]
    split_ifs with h
    · rw [hist_take _ _ _ h]; rfl
    · rfl
  constructor
  · rintro ⟨r, hr, -⟩
    rw [hst] at hr; split_ifs at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl
    refine ⟨4 * Reg.ncard, by rw [hst]; simp, fun r' hr' => ?_⟩
    rw [hst]; simp; omega

variable [Finite P] {Reg : Set P} {snd : P}

/-- **Theorem 3.9.** Π_GC is a gradecast protocol for a registered sender, against **any** number
of Byzantine parties (in the partially authenticated setting: Π_GC is unforging and only
registered parties sign, `gc_unforging`, `gAuth_registered`). -/
theorem theorem39 (hsR : snd ∈ Reg) :
    SolvesAuth ⊤ (gc Reg snd) (gAuth Reg snd) Set.univ (Gradecast snd) := by
  intro s _ hrel hV
  refine ⟨fun p _ => ⟨_, (gc_decides s p _).2 rfl⟩, fun hsnd p hp => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := lemma36 s hrel hV hsR hsnd hp
    rw [gc_decides, h1, h2]
  · intro p hp q hq v w g hpv hqw
    rw [gc_decides] at hpv hqw
    simp only [Prod.mk.injEq] at hpv hqw
    rw [hpv.1, hqw.1]
    exact (lemma37 s hrel hV hsR hp hq hpv.2.symm).symm

/-- **Lemma 3.10** (as a statement about decisions): if some registered party is honest, every
honest party outputs grade `1`. -/
theorem lemma310_decides (hsR : snd ∈ Reg) (s : Scenario P Bool (GMsg P)) (hrel : s.Reliable)
    (hV : s.AuthValid ⊤ (gc Reg snd) (gAuth Reg snd)) {k : P} (hk : k ∉ s.byz) (hkR : k ∈ Reg)
    {p : P} (hp : p ∉ s.byz) {o : Bool × Bool} (ho : Decides ⊤ (gc Reg snd) s p o) : o.2 = true := by
  rw [gc_decides] at ho; rw [ho]; exact lemma310 s hrel hV hsR hk hkR hp

/-- Π_GC in the partially authenticated setting: gradecast is solvable with a registered sender,
for any number of corruptions. -/
theorem gradecast_solvablePA (hsR : snd ∈ Reg) : SolvablePA Reg Set.univ (Gradecast (V := Bool) snd) :=
  ⟨_, _, gAuth Reg snd, gc Reg snd, gAuth_registered Reg snd, gc_unforging, theorem39 hsR⟩

end PartialAuthBC
