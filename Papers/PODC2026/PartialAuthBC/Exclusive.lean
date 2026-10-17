import Papers.PODC2026.PartialAuthBC.Broadcast

/-!
# Π_GC under the *exclusive* reading of Phase 2: Lemma 3.10 fails

Figure 1, Phase 2, for an unregistered party `P_i` receiving a valid Extension:
"– if `v_i = 0`, set `v_i = 1` and send Echo1; – if `v_i = 1` and `g_i = 0`, set `g_i = 1` and send
Echo1". `Gradecast.lean` formalizes the *sequential* reading (the party always ends with
`(v, g) = (1, 1)`). Here we formalize the *exclusive* (else-if) reading, `gstepX`/`gcX`: a party with
`(v, g) = (0, 0)` ends with `(1, 0)`. Everything else (messages, sends, decisions, tokens) is as in
`gc`.

**Counterexample to Lemma 3.10** ("if some registered party is honest, every honest party outputs
grade 1") under that reading: `P = Fin 4`, `Reg = {0, 1}` (`s = 2`, `8` rounds), sender `0`,
Byzantine set `{0, 3}`, all inputs `0`. The only Byzantine message is party 3's Echo2 `(2, [0])`
(chain = the Byzantine sender's own signature) to party 2 in round 2. Run:

* round 2: party 2 (`v = 0`) receives a valid Echo2 and sets `g := 0`, scheduling Echo3 `[0]`;
* round 3: party 2 sends Echo3 `(3, [0])` to the registered parties; party 1 accepts `[0]`;
* round 4: party 1 sends Extension `(0, [0, 1])`; party 2 (`v = g = 0`) receives the valid
  2-chain and, under the exclusive reading, sets `v := 1` but keeps `g = 0`;
* round 5: party 2 echoes `[0, 1]`, which is not valid for party 1 (it is on the chain); nothing
  changes afterwards.

Party 1 is honest and registered, but honest party 2 outputs `(1, 0)` (`lemma310_fails_exclusive`).
In the same scenario the sequential protocol `gc` gives party 2 grade 1 (`gc_contrast`, via
`lemma310_decides`). The adversary respects unforgeability (`scen_authValid`): its only token is the
signature `[0]` of the Byzantine sender. `gcX` is unforging (`gcX_unforging`).

**Π_BC breaks too (Theorem 3.13).** `bcX` is Π_BC (`bc`, Figure 2) built on `gcX`. Take as the
black-box agreement among `N = {2, 3}` the "AND exchange" `andBA` (each party sends its value and
after one round decides the AND of its value and the values received); with `|N| = 2` the only
admissible Byzantine set (`3|B| < |N|`) is `∅`, and then `andBA` solves agreement (`andBA_BA`).
With the same scenario plus party 3 sending `0` to party 2 in the first agreement round, honest
registered party 1 outputs `1` while honest party 2 (grade `0`) outputs `1 ∧ 0 = 0`
(`exclusive_bc_run`); `t = 2 < s + ⌈(n - s)/3⌉ = 3`. Hence `theorem313_fails_exclusive`: the
statement of `theorem313` is false for `bcX`.
-/

namespace PartialAuthBC

namespace Exclusive

open Cslib.Byzantine.LockStep

variable {P : Type}

section Defs

variable (Reg : Set P) (snd : P)

open Classical in
/-- The state change of `i` on a valid chain `c` (Figure 1, Phase 2 and 3), with the *exclusive*
reading of the two bullets of Phase 2 for unregistered parties. -/
noncomputable def gstepC (i : P) (st : GSt P) (c : List P) : GSt P :=
  if i ∈ Reg then
    (if st.v then { st with rnd := st.rnd + 1, out := none }
     else { st with rnd := st.rnd + 1, out := none, v := true, acc := some c })
  else if st.rnd % 4 = 0 then
    (if st.v = false then { st with rnd := st.rnd + 1, v := true, out := some c }
     else if st.g = false then { st with rnd := st.rnd + 1, g := true, out := some c }
     else { st with rnd := st.rnd + 1, out := none })
  else if st.rnd % 4 = 1 then
    (if st.v then { st with rnd := st.rnd + 1, out := none }
     else { st with rnd := st.rnd + 1, v := true, g := false, out := some c })
  else if st.rnd % 4 = 2 then
    (if st.v then { st with rnd := st.rnd + 1, out := none }
     else { st with rnd := st.rnd + 1, g := false, out := some c })
  else { st with rnd := st.rnd + 1, out := none }

open Classical in
/-- Processing the inbox of round `st.rnd`: as `gstep`, but with the exclusive reading. -/
noncomputable def gstepX (i : P) (st : GSt P) (ib : Inbox P (GMsg P)) : GSt P :=
  if h : (gE Reg snd i st ib).Nonempty then gstepC Reg i st h.some
  else { st with rnd := st.rnd + 1, out := none }

/-- The state of `i` after processing history `h` (exclusive reading). -/
noncomputable def gstOfX (i : P) (b : Bool) (h : History P (GMsg P)) : GSt P :=
  h.foldl (gstepX Reg snd i) (ginit snd i b)

open Classical in
/-- The message `i` sends to `q` after `n` rounds in state `st` (the send rule of `gc`). -/
noncomputable def sendOf (i : P) (n : ℕ) (st : GSt P) (q : P) : Option (GMsg P) :=
  if n < 4 * Reg.ncard then
    if n % 4 = 0 then
      st.acc.bind fun c => if i ∈ Reg ∧ c.length = n / 4 then some (0, c ++ [i]) else none
    else if i ∉ Reg ∧ (n % 4 ≠ 3 ∨ q ∈ Reg) then st.out.map fun c => (n % 4, c)
    else none
  else none

/-- The send rule of `gc` is `sendOf` applied to the (sequential) state. -/
lemma gc_send_eq (i : P) (b : Bool) (h : History P (GMsg P)) (q : P) :
    (gc Reg snd).send i b h q = sendOf Reg i h.length (gstOf Reg snd i b h) q := rfl

/-- **Π_GC with the exclusive reading of Phase 2**: same send and decision rules as `gc`. -/
noncomputable def gcX : Protocol P Bool (GMsg P) (Bool × Bool) where
  send i b h q := sendOf Reg i h.length (gstOfX Reg snd i b h) q
  decide i b h :=
    if 4 * Reg.ncard ≤ h.length then
      some ((gstOfX Reg snd i b (h.take (4 * Reg.ncard))).v,
        (gstOfX Reg snd i b (h.take (4 * Reg.ncard))).g)
    else none

/-- The two readings agree except for unregistered parties in phase 0 (Extension). -/
lemma gstepX_eq_gstep (i : P) (st : GSt P) (ib : Inbox P (GMsg P))
    (h : i ∈ Reg ∨ st.rnd % 4 ≠ 0) : gstepX Reg snd i st ib = gstep Reg snd i st ib := by
  unfold gstepX gstep gstepC
  split_ifs <;> simp_all

end Defs

/-! ### Basic facts -/

section Basic

variable {Reg : Set P} {snd : P}

lemma gstOfX_append (i : P) (b : Bool) (h : History P (GMsg P)) (ib : Inbox P (GMsg P)) :
    gstOfX Reg snd i b (h ++ [ib]) = gstepX Reg snd i (gstOfX Reg snd i b h) ib := by
  simp [gstOfX, List.foldl_append]

lemma gstepX_of_none {i : P} {st : GSt P} {ib : Inbox P (GMsg P)} (h : ∀ q, ib q = none) :
    gstepX Reg snd i st ib = { st with rnd := st.rnd + 1, out := none } := by
  unfold gstepX
  split_ifs with hne
  · obtain ⟨c, ⟨q, hq⟩, -⟩ := hne
    simp [h] at hq
  · rfl

open Classical in
lemma gstepX_of_one [DecidableEq P] {i : P} {st : GSt P} {ib : Inbox P (GMsg P)} {q₀ : P} {k : ℕ} {c : List P}
    (h : ∀ q, ib q = if q = q₀ then some (k, c) else none) :
    gstepX Reg snd i st ib =
      if k = st.rnd % 4 ∧ ValidFor Reg snd i (st.rnd / 4 + 1) c then gstepC Reg i st c
      else { st with rnd := st.rnd + 1, out := none } := by
  have key : ∀ c', c' ∈ gE Reg snd i st ib ↔
      c' = c ∧ k = st.rnd % 4 ∧ ValidFor Reg snd i (st.rnd / 4 + 1) c := by
    intro c'
    simp only [gE, validRecv, Set.mem_ofPred_eq, h]
    constructor
    · rintro ⟨⟨q, hq⟩, hv⟩
      split_ifs at hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨h1, rfl⟩ := hq
      exact ⟨rfl, h1, hv⟩
    · rintro ⟨rfl, hk, hv⟩
      exact ⟨⟨q₀, by simp [hk]⟩, hv⟩
  unfold gstepX
  split_ifs with hne hc hc
  · rw [((key _).1 hne.some_mem).1]
  · exact absurd ((key _).1 hne.some_mem).2 hc
  · exact absurd ⟨c, (key c).2 ⟨rfl, hc⟩⟩ hne
  · rfl

lemma gstOfX_rnd (i : P) (b : Bool) (h : History P (GMsg P)) :
    (gstOfX Reg snd i b h).rnd = h.length := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h ib ih =>
    rw [gstOfX_append]
    unfold gstepX gstepC
    split_ifs <;> simp [ih]

end Basic

/-! ### Unforgeability -/

section Unforging

variable {Reg : Set P} {snd : P}

lemma gstepX_acc (i : P) (st : GSt P) (ib : Inbox P (GMsg P)) :
    (gstepX Reg snd i st ib).acc = st.acc ∨
      ∃ c ∈ gE Reg snd i st ib, (gstepX Reg snd i st ib).acc = some c := by
  unfold gstepX
  split_ifs with h
  · unfold gstepC; split_ifs <;> simp [Set.Nonempty.some_mem]
  · simp

lemma gstepX_out (i : P) (st : GSt P) (ib : Inbox P (GMsg P)) :
    (gstepX Reg snd i st ib).out = none ∨
      ∃ c ∈ gE Reg snd i st ib, (gstepX Reg snd i st ib).out = some c := by
  unfold gstepX
  split_ifs with h
  · unfold gstepC; split_ifs <;> simp [Set.Nonempty.some_mem]
  · simp

lemma gstOfX_acc_spec (i : P) (b : Bool) (h : History P (GMsg P)) {c : List P}
    (hc : (gstOfX Reg snd i b h).acc = some c) : c = [] ∨ c ∈ chainsOf h := by
  induction h using List.reverseRecOn generalizing c with
  | nil =>
    simp only [gstOfX, List.foldl_nil, ginit] at hc
    split_ifs at hc
    · simp at hc; exact Or.inl hc
  | append_singleton h ib ih =>
    rw [gstOfX_append] at hc
    rcases gstepX_acc (Reg := Reg) (snd := snd) i (gstOfX Reg snd i b h) ib with h1 | ⟨c', hc', h1⟩
    · rw [h1] at hc
      exact (ih hc).imp_right (chainsOf_mono h ib ·)
    · rw [h1] at hc; cases hc
      exact Or.inr (mem_chainsOf_of_gE hc')

lemma gstOfX_out_spec (i : P) (b : Bool) (h : History P (GMsg P)) {c : List P}
    (hc : (gstOfX Reg snd i b h).out = some c) : c ∈ chainsOf h := by
  induction h using List.reverseRecOn generalizing c with
  | nil => simp [gstOfX, ginit] at hc
  | append_singleton h ib ih =>
    rw [gstOfX_append] at hc
    rcases gstepX_out (Reg := Reg) (snd := snd) i (gstOfX Reg snd i b h) ib with h1 | ⟨c', hc', h1⟩
    · rw [h1] at hc; cases hc
    · rw [h1] at hc; cases hc; exact mem_chainsOf_of_gE hc'

/-- `gcX` only emits its own signature and relayed signatures. -/
theorem gcX_unforging : (gcX Reg snd).Unforging (gAuth Reg snd) := by
  intro i b h q m hm τ hτ
  simp only [gcX, sendOf] at hm
  split_ifs at hm with h1 h2 h3
  · obtain ⟨c, hc, hm⟩ := Option.bind_eq_some_iff.mp hm
    split_ifs at hm with h4
    cases hm
    obtain ⟨hne, hpre, hreg⟩ := hτ
    rcases List.prefix_concat_iff.mp hpre with rfl | hpre'
    · left; simp [gAuth]
    · right
      rcases gstOfX_acc_spec i b h hc with rfl | hch
      · exact absurd (List.prefix_nil.mp hpre') hne
      · exact tokens_of_mem_chainsOf hch ⟨hne, hpre', hreg⟩
  · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact Or.inr (tokens_of_mem_chainsOf (gstOfX_out_spec i b h hc) hτ)

end Unforging

/-! ### Runs of `gcX` -/

section Run

variable (s : Scenario P Bool (GMsg P)) (Reg : Set P) (snd : P)

/-- State of `p` after `r` rounds of `gcX` in scenario `s`. -/
noncomputable def gSX (r : ℕ) (p : P) : GSt P :=
  gstOfX Reg snd p (s.input p) (hist ⊤ (gcX Reg snd) s r p)

lemma gSX_succ (r : ℕ) (p : P) :
    gSX s Reg snd (r + 1) p = gstepX Reg snd p (gSX s Reg snd r p)
      (fun q => deliver ⊤ (gcX Reg snd) s (hist ⊤ (gcX Reg snd) s r) r q p) := by
  simp only [gSX, hist_succ, gstOfX_append]

open Classical in
lemma deliver_gcX (r : ℕ) (q p : P) :
    deliver ⊤ (gcX Reg snd) s (hist ⊤ (gcX Reg snd) s r) r q p =
      if q = p then none else if q ∈ s.byz then s.adv r q p
      else if s.drop r q p then none else sendOf Reg q r (gSX s Reg snd r q) p := by
  by_cases h : q = p
  · simp [deliver, h]
  · simp only [deliver, SimpleGraph.top_adj, ne_eq, h, not_false_eq_true, ↓reduceIte]
    simp only [gcX, length_hist]
    rfl

/-- `gcX` outputs from round `4s` on the final state `(v, g)`. -/
lemma gcX_status (r : ℕ) (p : P) :
    status ⊤ (gcX Reg snd) s r p =
      if 4 * Reg.ncard ≤ r then some ((gSX s Reg snd (4 * Reg.ncard) p).v,
        (gSX s Reg snd (4 * Reg.ncard) p).g) else none := by
  simp only [status, gcX, length_hist]
  split_ifs with h
  · rw [take_hist _ _ _ h]; rfl
  · rfl

/-- `gcX` decides at round `4s` the final state `(v, g)`. -/
lemma gcX_decides (p : P) (o : Bool × Bool) :
    Decides ⊤ (gcX Reg snd) s p o ↔
      o = ((gSX s Reg snd (4 * Reg.ncard) p).v, (gSX s Reg snd (4 * Reg.ncard) p).g) := by
  have hst := fun r => gcX_status s Reg snd r p
  constructor
  · rintro ⟨r, hr, -⟩
    rw [hst] at hr; split_ifs at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl
    refine ⟨4 * Reg.ncard, by rw [hst]; simp, fun r' hr' => ?_⟩
    rw [hst]; simp; omega

end Run

/-! ### The counterexample -/

/-- The registered parties `{0, 1}`. -/
def Reg4 : Set (Fin 4) := {0, 1}

lemma mem_Reg4 {q : Fin 4} : q ∈ Reg4 ↔ q = 0 ∨ q = 1 := by simp [Reg4]

lemma Reg4_ncard : Reg4.ncard = 2 := Set.ncard_pair (by decide)

/-- The scenario: Byzantine `{0, 3}` (`0` is the sender), all inputs `0`; the only Byzantine
message is party 3's Echo2 `(2, [0])` to party 2 in round 2. No omissions. -/
def scen : Scenario (Fin 4) Bool (GMsg (Fin 4)) where
  byz := {0, 3}
  input := fun _ => false
  adv := fun r q p => if r = 2 ∧ q = 3 ∧ p = 2 then some (2, [0]) else none

lemma scen_reliable : scen.Reliable := fun _ _ _ h => h

/-- The adversary respects unforgeability (for any protocol): its only token is `[0]`, the
signature of the Byzantine sender. -/
lemma scen_authValid {O : Type*} (alg : Protocol (Fin 4) Bool (GMsg (Fin 4)) O) :
    scen.AuthValid ⊤ alg (gAuth Reg4 0) := by
  intro r b q m hb hq _ hm τ hτ
  left
  simp only [scen] at hm
  split_ifs at hm with h
  cases hm
  obtain ⟨hne, hpre, -⟩ := hτ
  rcases List.prefix_concat_iff.mp (show τ <+: [] ++ [(0 : Fin 4)] from hpre) with rfl | h'
  · simp [gAuth, scen]
  · exact absurd (List.prefix_nil.mp h') hne

lemma fin4 : ∀ q : Fin 4, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by decide

local notation "S" => gSX scen Reg4 0

lemma deliver_scen (r : ℕ) (q p : Fin 4) :
    deliver ⊤ (gcX Reg4 0) scen (hist ⊤ (gcX Reg4 0) scen r) r q p =
      if q = p then none
      else if q = 0 ∨ q = 3 then (if r = 2 ∧ q = 3 ∧ p = 2 then some (2, [0]) else none)
      else sendOf Reg4 q r (S r q) p := by
  rw [deliver_gcX]
  simp only [scen, Set.mem_insert_iff, Set.mem_singleton_iff]
  split_ifs <;> simp_all

lemma step_none {r : ℕ} {p : Fin 4} {st : GSt (Fin 4)} (hst : S r p = st)
    (hib : ∀ q, deliver ⊤ (gcX Reg4 0) scen (hist ⊤ (gcX Reg4 0) scen r) r q p = none) :
    S (r + 1) p = { st with rnd := st.rnd + 1, out := none } := by
  rw [gSX_succ, hst, gstepX_of_none hib]

open Classical in
lemma step_one {r : ℕ} {p : Fin 4} {st : GSt (Fin 4)} (hst : S r p = st) {q₀ : Fin 4} {k : ℕ}
    {c : List (Fin 4)}
    (hib : ∀ q, deliver ⊤ (gcX Reg4 0) scen (hist ⊤ (gcX Reg4 0) scen r) r q p =
      if q = q₀ then some (k, c) else none) :
    S (r + 1) p =
      if k = st.rnd % 4 ∧ ValidFor Reg4 0 p (st.rnd / 4 + 1) c then gstepC Reg4 p st c
      else { st with rnd := st.rnd + 1, out := none } := by
  rw [gSX_succ, hst, gstepX_of_one hib]

/-- Computes an inbox entry of round `r` from the states of the honest parties `1, 2`. -/
macro "ibtac" h1:term:max h2:term:max : tactic =>
  `(tactic| (intro q; rw [deliver_scen]; rcases fin4 q with hq | hq | hq | hq <;> subst hq <;>
    simp [sendOf, mem_Reg4, Reg4_ncard, $h1:term, $h2:term]))

/-! States of the honest parties `1` (registered) and `2` (unregistered). -/

lemma S0 : S 0 1 = ⟨0, false, true, none, none⟩ ∧ S 0 2 = ⟨0, false, true, none, none⟩ := by
  simp [gSX, gstOfX, ginit, scen]

lemma S1 : S 1 1 = ⟨1, false, true, none, none⟩ ∧ S 1 2 = ⟨1, false, true, none, none⟩ :=
  ⟨(step_none S0.1 (by ibtac S0.1 S0.2)).trans rfl, (step_none S0.2 (by ibtac S0.1 S0.2)).trans rfl⟩

lemma S2 : S 2 1 = ⟨2, false, true, none, none⟩ ∧ S 2 2 = ⟨2, false, true, none, none⟩ :=
  ⟨(step_none S1.1 (by ibtac S1.1 S1.2)).trans rfl, (step_none S1.2 (by ibtac S1.1 S1.2)).trans rfl⟩

/-- Round 2: party 2 receives the Byzantine Echo2 `[0]` and sets `g := 0`. -/
lemma S3 : S 3 1 = ⟨3, false, true, none, none⟩ ∧ S 3 2 = ⟨3, false, false, none, some [0]⟩ := by
  refine ⟨(step_none S2.1 (by ibtac S2.1 S2.2)).trans rfl, ?_⟩
  refine (step_one S2.2 (q₀ := 3) (k := 2) (c := [0]) (by ibtac S2.1 S2.2)).trans ?_
  simp [gstepC, ValidFor, mem_Reg4]

/-- Round 3: party 2 sends Echo3 `[0]`; party 1 accepts `[0]`. -/
lemma S4 : S 4 1 = ⟨4, true, true, some [0], none⟩ ∧ S 4 2 = ⟨4, false, false, none, none⟩ := by
  refine ⟨?_, (step_none S3.2 (by ibtac S3.1 S3.2)).trans rfl⟩
  refine (step_one S3.1 (q₀ := 2) (k := 3) (c := [0]) (by ibtac S3.1 S3.2)).trans ?_
  simp [gstepC, ValidFor, mem_Reg4]

/-- Round 4: party 1 sends Extension `[0, 1]`; party 2 sets `v := 1` but keeps `g = 0`. -/
lemma S5 : S 5 1 = ⟨5, true, true, some [0], none⟩ ∧ S 5 2 = ⟨5, true, false, none, some [0, 1]⟩ := by
  refine ⟨(step_none S4.1 (by ibtac S4.1 S4.2)).trans rfl, ?_⟩
  refine (step_one S4.2 (q₀ := 1) (k := 0) (c := [0, 1]) (by ibtac S4.1 S4.2)).trans ?_
  simp [gstepC, ValidFor, mem_Reg4]

/-- Round 5: party 2's Echo1 `[0, 1]` is not valid for party 1. -/
lemma S6 : S 6 1 = ⟨6, true, true, some [0], none⟩ ∧ S 6 2 = ⟨6, true, false, none, none⟩ := by
  refine ⟨?_, (step_none S5.2 (by ibtac S5.1 S5.2)).trans rfl⟩
  refine (step_one S5.1 (q₀ := 2) (k := 1) (c := [0, 1]) (by ibtac S5.1 S5.2)).trans ?_
  simp [ValidFor]

lemma S7 : S 7 1 = ⟨7, true, true, some [0], none⟩ ∧ S 7 2 = ⟨7, true, false, none, none⟩ :=
  ⟨(step_none S6.1 (by ibtac S6.1 S6.2)).trans rfl, (step_none S6.2 (by ibtac S6.1 S6.2)).trans rfl⟩

lemma S8 : S 8 1 = ⟨8, true, true, some [0], none⟩ ∧ S 8 2 = ⟨8, true, false, none, none⟩ :=
  ⟨(step_none S7.1 (by ibtac S7.1 S7.2)).trans rfl, (step_none S7.2 (by ibtac S7.1 S7.2)).trans rfl⟩

/-- In the run of `gcX`, honest registered party 1 outputs `(1, 1)` and honest unregistered party 2
outputs `(1, 0)`. -/
theorem exclusive_run :
    Decides ⊤ (gcX Reg4 0) scen 1 (true, true) ∧ Decides ⊤ (gcX Reg4 0) scen 2 (true, false) := by
  simp only [gcX_decides, Reg4_ncard, S8.1, S8.2]
  exact ⟨trivial, trivial⟩

/-- **Lemma 3.10 fails under the exclusive reading of Figure 1, Phase 2.** The statement of
`lemma310_decides` (with registered sender, reliable channels and an unforgeability-respecting
adversary) is false for `gcX` on `4` parties. -/
theorem lemma310_fails_exclusive :
    ¬ ∀ (Reg : Set (Fin 4)) (snd : Fin 4) (s : Scenario (Fin 4) Bool (GMsg (Fin 4))),
      snd ∈ Reg → s.Reliable → s.AuthValid ⊤ (gcX Reg snd) (gAuth Reg snd) →
      ∀ k, k ∉ s.byz → k ∈ Reg → ∀ p, p ∉ s.byz → ∀ o,
        Decides ⊤ (gcX Reg snd) s p o → o.2 = true := by
  intro H
  have := H Reg4 0 scen (by simp [Reg4]) scen_reliable (scen_authValid _) 1 (by simp [scen])
    (by simp [Reg4]) 2 (by simp [scen]) _ exclusive_run.2
  simp at this

/-- Contrast: in the same scenario, the sequential reading `gc` gives party 2 grade `1`
(Lemma 3.10). -/
theorem gc_contrast {o : Bool × Bool} (ho : Decides ⊤ (gc Reg4 0) scen 2 o) : o.2 = true :=
  lemma310_decides (by simp [Reg4]) scen scen_reliable (scen_authValid _) (k := 1)
    (by simp [scen]) (by simp [Reg4]) (by simp [scen]) ho

/-! ### Π_BC with the exclusive reading: Theorem 3.13 fails too -/

section BcDefs

variable (Reg : Set P) (snd : P) {M' : Type} (ba : Protocol (Unreg Reg) Bool M' Bool)

/-- **Π_BC** (Figure 2) built on `gcX` instead of `gc` (otherwise identical to `bc`). -/
noncomputable abbrev bcX : Protocol P Bool (GMsg P ⊕ M') Bool := bcWith Reg ba (gcX Reg snd)

theorem bcX_unforging : (bcX Reg snd ba).Unforging (bcAuth Reg snd M') :=
  bcWith_unforging Reg snd ba gcX_unforging

omit snd in
/-- `gcX` decides the state after the first `4s` rounds. -/
lemma gcX_firstDecide {snd p : P} {x : Bool} {h : History P (GMsg P)}
    (hl : h.length = 4 * Reg.ncard) :
    (gcX Reg snd).firstDecide p x h =
      some ((gstOfX Reg snd p x h).v, (gstOfX Reg snd p x h).g) := by
  rw [Protocol.firstDecide, hl]
  refine firstUpTo_of_firstSome (r := 4 * Reg.ncard) ?_ (fun r hr => ?_) le_rfl
  · have ht : h.take (4 * Reg.ncard) = h := List.take_of_length_le hl.le
    simp [gcX, hl, ht]
  · simp only [gcX, List.length_take, hl]
    split_ifs <;> first | rfl | omega

open Classical in
/-- `bcX` is the protocol of Figure 2 built on `gcX` (as `bc_send_decide`, with the state
`gstOfX` of the exclusive reading). -/
theorem bcX_send_decide (p q : P) (x : Bool) (h : History P (GMsg P ⊕ M')) :
    let st := gstOfX Reg snd p x (histL (h.take (4 * Reg.ncard)))
    let hba := restrictHist Regᶜ (histR (h.drop (4 * Reg.ncard)))
    (bcX Reg snd ba).send p x h q =
      (if h.length < 4 * Reg.ncard then ((gcX Reg snd).send p x (histL h) q).map Sum.inl
       else if hp : p ∈ Regᶜ then
         if hq : q ∈ Regᶜ then (ba.send ⟨p, hp⟩ st.v hba ⟨q, hq⟩).map Sum.inr else none
       else none) ∧
    (bcX Reg snd ba).decide p x h =
      (if 4 * Reg.ncard ≤ h.length then
         if hp : p ∈ Regᶜ then (if st.g then some st.v else ba.decide ⟨p, hp⟩ st.v hba)
         else some st.v
       else none) :=
  bcWith_send_decide Reg ba (gstOfX Reg snd) (fun _ _ _ hl => gcX_firstDecide Reg hl) p q x h

end BcDefs

section BcRuns

variable {Reg : Set P} {snd : P} {M' : Type} {ba : Protocol (Unreg Reg) Bool M' Bool}
  (s : Scenario P Bool (GMsg P ⊕ M'))

local notation "T" => 4 * Reg.ncard

/-- The agreement scenario among the unregistered parties (rounds `≥ 4s`), exclusive reading. -/
noncomputable abbrev sc₂X (Reg : Set P) (snd : P) (s : Scenario P Bool (GMsg P ⊕ M')) :
    Scenario (Unreg Reg) Bool M' :=
  sc₂With Reg s fun q => (gSX (sc₁ Reg s) Reg snd (4 * Reg.ncard) q.1).v

lemma seqInputs_bcX (p : P) :
    seqInputs ⊤ (gcX Reg snd) (4 * Reg.ncard) bcIn s p =
      ((gSX (sc₁ Reg s) Reg snd T p).v, (gSX (sc₁ Reg s) Reg snd T p).g) :=
  seqInputs_bcWith s (by rw [gcX_status]; simp) fun r hr => by rw [gcX_status]; simp; omega

/-- Registered parties and parties with grade `1` decide their gradecast value. -/
lemma bcX_decides_of_g {p : P} (hp : p ∈ Reg ∨ (gSX (sc₁ Reg s) Reg snd T p).g = true) (o : Bool) :
    Decides ⊤ (bcX Reg snd ba) s p o ↔ o = (gSX (sc₁ Reg s) Reg snd T p).v := by
  rw [bcWith_decides_of_g s (by rwa [seqInputs_bcX s]), seqInputs_bcX s]

/-- Unregistered parties with grade `0` decide what `ba` decides. -/
lemma bcX_decides_of_g0 (p : Unreg Reg) (hp : (gSX (sc₁ Reg s) Reg snd T p.1).g = false)
    (o : Bool) :
    Decides ⊤ (bcX Reg snd ba) s p.1 o ↔ Decides ⊤ ba (sc₂X Reg snd s) p o := by
  rw [bcWith_decides_of_g0 s p (by rw [seqInputs_bcX s]; exact hp)]
  simp only [seqInputs_bcX s]

end BcRuns

/-! #### The "AND" exchange -/

section AndBA

variable (N : Type)

open Classical in
/-- Every party sends its value; after one round it decides the AND of its own value and the
values received. With no Byzantine party this is Byzantine agreement. -/
noncomputable def andBA : Protocol N Bool Bool Bool where
  send _ x _ _ := some x
  decide _ x h := match h with
    | [] => none
    | ib :: _ => some (x && decide (∀ q, ib q ≠ some false))

variable {N}

open Classical in
lemma andBA_decides (s : Scenario N Bool Bool) (p : N) (o : Bool) :
    Decides ⊤ (andBA N) s p o ↔ o = (s.input p && decide (∀ q,
      deliver ⊤ (andBA N) s (hist ⊤ (andBA N) s 0) 0 q p ≠ some false)) := by
  have hst : ∀ r, status ⊤ (andBA N) s (r + 1) p = some (s.input p && decide (∀ q,
      deliver ⊤ (andBA N) s (hist ⊤ (andBA N) s 0) 0 q p ≠ some false)) := by
    intro r
    have h1 := take_hist ⊤ (andBA N) s (show 1 ≤ r + 1 by omega) p
    obtain ⟨ib, l, hl⟩ : ∃ ib l, hist ⊤ (andBA N) s (r + 1) p = ib :: l := by
      cases h : hist ⊤ (andBA N) s (r + 1) p with
      | nil => have := length_hist ⊤ (andBA N) s (r + 1) p; rw [h] at this; simp at this
      | cons ib l => exact ⟨ib, l, rfl⟩
    rw [hl] at h1
    simp only [List.take_succ_cons, List.take_zero, hist_succ, hist_zero, List.nil_append,
      List.cons.injEq, and_true] at h1
    subst h1; rw [status, hl]; rfl
  constructor
  · rintro ⟨r, hr, -⟩
    cases r with
    | zero => simp [status, andBA] at hr
    | succ r => rw [hst] at hr; exact (Option.some_injective _ hr).symm
  · rintro rfl
    exact ⟨1, hst 0, fun r hr => by
      obtain rfl : r = 0 := by omega
      simp [status, andBA]⟩

/-- Without Byzantine parties, `andBA` solves Byzantine agreement. -/
lemma andBA_BA (s : Scenario N Bool Bool) (hrel : s.Reliable) (hB : s.byz = ∅) :
    BA s.input s.honest (Decides ⊤ (andBA N) s) := by
  classical
  have key : ∀ p o, Decides ⊤ (andBA N) s p o ↔ o = decide (∀ q, s.input q = true) := by
    intro p o
    rw [andBA_decides]
    have hdel : ∀ q, q ≠ p →
        deliver ⊤ (andBA N) s (hist ⊤ (andBA N) s 0) 0 q p = some (s.input q) := by
      intro q hqp
      rw [deliver_honest ⊤ _ s hrel (by simp [hB]) hqp]; rfl
    have hself : deliver ⊤ (andBA N) s (hist ⊤ (andBA N) s 0) 0 p p = none := by simp [deliver]
    suffices (s.input p && decide (∀ q,
        deliver ⊤ (andBA N) s (hist ⊤ (andBA N) s 0) 0 q p ≠ some false))
        = decide (∀ q, s.input q = true) by rw [this]
    rcases Bool.eq_false_or_eq_true (s.input p) with h | h
    · simp only [h, Bool.true_and, decide_eq_decide]
      constructor
      · intro H q
        by_cases hqp : q = p
        · subst hqp; exact h
        · have := H q; rw [hdel q hqp] at this; simpa using this
      · intro H q
        by_cases hqp : q = p
        · subst hqp; rw [hself]; simp
        · rw [hdel q hqp, H q]; simp
    · simp only [h, Bool.false_and]
      exact (decide_eq_false (fun H => by simp [H p] at h)).symm
  refine ⟨fun p _ => ⟨_, (key p _).2 rfl⟩, fun v hv p hp => (key p v).2 ?_,
    fun p _ q _ v w hv hw => by rw [(key p v).1 hv, (key q w).1 hw]⟩
  have hall : ∀ q, s.input q = v := fun q => hv q (by simp [Scenario.honest, hB])
  rcases Bool.eq_false_or_eq_true v with h | h
  · subst h; simp [hall]
  · subst h
    exact (decide_eq_false (fun H => by have := H p; rw [hall p] at this; simp at this)).symm

end AndBA

/-! #### The counterexample for Π_BC -/

/-- The broadcast scenario: as `scen` in the gradecast part, plus party 3's agreement message
`0` to party 2 in the first round of the agreement phase (round `8`). -/
def scenB : Scenario (Fin 4) Bool (GMsg (Fin 4) ⊕ Bool) where
  byz := {0, 3}
  input := fun _ => false
  adv := fun r q p => if r = 2 ∧ q = 3 ∧ p = 2 then some (Sum.inl (2, [0]))
    else if r = 8 ∧ q = 3 ∧ p = 2 then some (Sum.inr false) else none

lemma scenB_reliable : scenB.Reliable := fun _ _ _ h => h

lemma scenB_authValid {O : Type*} (alg : Protocol (Fin 4) Bool (GMsg (Fin 4) ⊕ Bool) O) :
    scenB.AuthValid ⊤ alg (bcAuth Reg4 0 Bool) := by
  intro r b q m hb hq _ hm τ hτ
  left
  simp only [scenB] at hm
  split_ifs at hm with h1 h2
  · cases hm
    obtain ⟨hne, hpre, -⟩ := hτ
    rcases List.prefix_concat_iff.mp (show τ <+: [] ++ [(0 : Fin 4)] from hpre) with rfl | h'
    · simp [bcAuth, gAuth, scenB]
    · exact absurd (List.prefix_nil.mp h') hne
  · cases hm
    simp [bcAuth] at hτ

lemma sc₁_scenB : sc₁ Reg4 scenB = scen := by
  have h : (fun r b q => if r < 4 * Reg4.ncard then (scenB.adv r b q).bind Sum.getLeft? else none)
      = scen.adv := by
    funext r b q
    rw [Reg4_ncard]
    simp only [scenB, scen]
    split_ifs <;> simp_all
  simp only [sc₁, Scenario.seqFst, h]
  rfl

lemma two_mem : (2 : Fin 4) ∈ Reg4ᶜ := by simp [Reg4]
lemma three_mem : (3 : Fin 4) ∈ Reg4ᶜ := by simp [Reg4]

/-- In the run of `bcX` with the AND exchange, honest registered party 1 outputs `1` and honest
unregistered party 2 outputs `0`. -/
theorem exclusive_bc_run :
    Decides ⊤ (bcX Reg4 0 (andBA (Unreg Reg4))) scenB 1 true ∧
      Decides ⊤ (bcX Reg4 0 (andBA (Unreg Reg4))) scenB 2 false := by
  constructor
  · rw [bcX_decides_of_g scenB (Or.inl (by simp [Reg4])), Reg4_ncard, sc₁_scenB, S8.1]
  · rw [show (2 : Fin 4) = (⟨2, two_mem⟩ : Unreg Reg4).1 from rfl,
      bcX_decides_of_g0 scenB ⟨2, two_mem⟩ (by rw [Reg4_ncard, sc₁_scenB, S8.2]), andBA_decides]
    have hd : deliver ⊤ (andBA (Unreg Reg4)) (sc₂X Reg4 0 scenB)
        (hist ⊤ (andBA (Unreg Reg4)) (sc₂X Reg4 0 scenB) 0) 0 ⟨3, three_mem⟩ ⟨2, two_mem⟩ =
          some false := by
      rw [deliver_byz ⊤ _ _ (by simp [scenB]) (by simp)]
      simp [sc₂With_adv, scenB, Reg4_ncard]
    rw [@decide_eq_false _ (Classical.propDecidable _) (fun H => H _ hd), Bool.and_false]

/-- **Theorem 3.13 fails under the exclusive reading of Figure 1, Phase 2.** For `n = 4`,
`Reg = {0, 1}` (`s = 2`), the black box `andBA` solves agreement among the two unregistered
parties against every admissible Byzantine set (`3|B| < 2`, i.e. `B = ∅`), and `t = 2` satisfies
`t < s + ⌈(n - s)/3⌉`; but `bcX` violates consistency. -/
theorem theorem313_fails_exclusive :
    ¬ ∀ (Reg : Set (Fin 4)) (snd : Fin 4) (ba : Protocol (Unreg Reg) Bool Bool Bool),
      snd ∈ Reg → Solves ⊤ ba {B | 3 * B.ncard < Nat.card (Unreg Reg)} BA → ∀ t : ℕ,
      t < Reg.ncard + (Nat.card (Fin 4) - Reg.ncard + 2) / 3 →
      SolvesAuth ⊤ (bcX Reg snd ba) (bcAuth Reg snd Bool) (atMost t) (BB snd) := by
  intro H
  have hc : Nat.card (Unreg Reg4) = 2 := by rw [nat_card_unreg, Reg4_ncard]; simp
  have hba : Solves ⊤ (andBA (Unreg Reg4)) {B | 3 * B.ncard < Nat.card (Unreg Reg4)} BA := by
    intro s hs hrel
    refine andBA_BA s hrel ?_
    have hs' : 3 * s.byz.ncard < Nat.card (Unreg Reg4) := hs
    exact (Set.ncard_eq_zero (Set.toFinite _)).mp (by omega)
  have hbyz : scenB.byz ∈ atMost (P := Fin 4) 2 := by
    show ({0, 3} : Set (Fin 4)).ncard ≤ 2
    rw [Set.ncard_pair (by decide)]
  obtain ⟨-, -, hagr⟩ := H Reg4 0 (andBA _) (by simp [Reg4]) hba 2 (by rw [Reg4_ncard]; simp)
    scenB hbyz scenB_reliable (scenB_authValid _)
  have := hagr 1 (by simp [scenB, Scenario.honest]) 2 (by simp [scenB, Scenario.honest]) true false
    exclusive_bc_run.1 exclusive_bc_run.2
  simp at this

end Exclusive

end PartialAuthBC
