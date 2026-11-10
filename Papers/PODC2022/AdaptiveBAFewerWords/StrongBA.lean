import Papers.PODC2022.AdaptiveBAFewerWords.Basic

/-!
# Algorithm 5 of [CKS22]: binary strong BA, linear in the failure-free case

[CKS22] S. Cohen, I. Keidar, A. Spiegelman. *Make Every Word Count: Adaptive Byzantine Agreement with
Fewer Words.* PODC 2022; full version arXiv:2202.09123v2, Section 7 and Appendix C.

## Model

* Processes `p_1, …, p_n`, `n = 2t + 1`, are `Fin (2t+1)`; `p_i` is index `i - 1`, so the leader
  `p_1` is `0`. A static set `F` of Byzantine processes, `|F| ≤ t`. Algorithm 5 is deterministic,
  so an adaptive adversary corrupting processes during the run is no stronger than one choosing the
  same set `F` up front (the run is a function of the adversary's choices).
* Signatures and threshold signatures are ideal and *symbolic*. Unforgeability is a validity
  condition on the adversary (`AdvValid`): the adversary may use the round-1 signature `⟨v⟩_p` of a
  correct `p` (it is sent in round 1; we let the adversary see every message, also those sent to a
  correct leader), so `QC_propose(v)` is available iff `t + 1` processes are Byzantine or correct
  with input `v` (`QCproposeAvail`); `QC_decide(v)` is available iff every correct process has sent
  `⟨decide, v⟩` (Byzantine shares are always available) (`QCdecideAvail`).
* **Rounds 1–5** are lock-step. A Byzantine leader delivers to each process at most one valid
  propose message (`Adversary.r2`) and at most one decide certificate (`Adversary.r4`). Reading of
  line 7: a correct process sends `⟨decide, v⟩` for at most one `v` (the first valid propose it
  accepts); if it accepted several, the adversary could equally have sent only the accepted one, so
  "at most one propose per receiver" loses no generality. A correct leader checks `v = 0` first
  (any fixed tie-break works).
* **Fallback hand-off (lines 16–28)** in real, discrete time `ℕ`: round 5 ends at time `0` for all
  correct processes (synchronised clocks), and fallback messages received earlier are processed at
  time `0`. Each correct process sends exactly one fallback message, at its *first-hearing time*
  `fbTime p`: time `0` if undecided after round 5 (line 17), otherwise the first time it receives a
  fallback message (line 26). The adversary fixes the delay `d p q ∈ [0, δ]` of the (unique)
  fallback message from `p` to `q`, and sends Byzantine fallback messages to anyone at any time,
  carrying a valid `QC_decide(v)` (only if available) or no proof. First-hearing is the inductive
  reachability predicate `Hears` (a shortest-path computation with zero delays allowed); this is the
  operational semantics of the loop at lines 20–27, not an axiomatisation.
  `fallback_start = fbTime + 2δ` (lines 18, 27).
* **Adoption (lines 21–24)**: an undecided process (with `fallback_start = 2δ`) adopts `v` if it
  receives, at a time in its window `[0, 2δ]`, a fallback message with a valid `QC_decide(v)`.
* **The fallback `A_fallback`** (Momose–Ren) is a black box: `FallbackSpec` says that *if* all
  correct processes start it, at most `δ` apart (the hypothesis that Lemma 18 turns into a correct
  synchronous run with `δ' = 2δ`), then its outputs satisfy agreement, termination and strong
  unanimity w.r.t. the inputs `bu_decision`.

## Readings (slips of the printed Algorithm 5)

We formalise the *intended* code (`Reading.intended`):
* `bu_decision` starts as the input `v_i` (printed: `⊥`, and line 19 sets `bu_decision ← decision`
  unconditionally, so an undecided process would enter the fallback with `⊥`);
* a decided process attaches its decision certificate `proof` to its echo (printed: `bu_proof`,
  which is `⊥` for a decided process) — parameter `Reading.attachProof`;
* messages arriving exactly at `fallback_start` are still processed (printed:
  `while fallback_start > now`, which drops them) — parameter `Reading.closedWindow`.
-/

namespace Podc.AdaptiveBAFewerWords.StrongBA

open Finset

/-- Processes `p_1, …, p_n` with `n = 2t + 1`; `p_i` is the `Fin` index `i - 1`. -/
abbrev Proc (t : ℕ) := Fin (2 * t + 1)

/-- The leader `p_1` (line 1). -/
def leader (t : ℕ) : Proc t := 0

/-- The adversary's choices. Fields concerning a correct sender are ignored. -/
structure Adversary (t : ℕ) where
  /-- The Byzantine processes. -/
  F : Finset (Proc t)
  /-- Round 1: Byzantine `p` sends `⟨v⟩_p` to the leader for each `v ∈ r1 p`. -/
  r1 : Proc t → Finset Bool
  /-- Round 2 (Byzantine leader): the value of the propose message delivered to `p`, if any. -/
  r2 : Proc t → Option Bool
  /-- Round 3: Byzantine `p` sends `⟨decide, v⟩_p` to the leader for each `v ∈ r3 p`. -/
  r3 : Proc t → Finset Bool
  /-- Round 4 (Byzantine leader): the value of the decide certificate delivered to `p`, if any. -/
  r4 : Proc t → Option Bool
  /-- Delay of the fallback message from `p` to `q` (each process sends at most one). -/
  d : Proc t → Proc t → ℕ
  /-- Byzantine fallback messages `(sender, receiver, arrival time, certificate)`; certificate
  `some v` is a valid `QC_decide(v)`, `none` is no (or an invalid) proof. -/
  fb : Set (Proc t × Proc t × ℕ × Option Bool)

/-- Readings of the hand-off code. -/
structure Reading where
  /-- A decided process attaches its decide certificate to its echo (line 26). -/
  attachProof : Bool
  /-- Messages arriving exactly at `fallback_start` are processed (line 20). -/
  closedWindow : Bool

/-- The intended reading. -/
def Reading.intended : Reading := ⟨true, true⟩

variable {t : ℕ} (inp : Proc t → Bool) (A : Adversary t)

/-- The correct processes. -/
def correct : Set (Proc t) := {p | p ∉ A.F}

/-! ### Rounds 1–5 -/

/-- Signers of the messages `⟨v⟩` a correct leader receives in round 1. -/
def recv1 (v : Bool) : Finset (Proc t) :=
  univ.filter fun p => (p ∉ A.F ∧ inp p = v) ∨ (p ∈ A.F ∧ v ∈ A.r1 p)

/-- Lines 3–6 for a correct leader: the value it proposes, if any. -/
def leaderProp : Option Bool :=
  if t + 1 ≤ (recv1 inp A false).card then some false
  else if t + 1 ≤ (recv1 inp A true).card then some true else none

/-- Line 7: the value of the valid propose message a correct process receives (and, line 8, the
value of the decide message it signs). -/
def rprop (p : Proc t) : Option Bool :=
  if leader t ∈ A.F then A.r2 p else leaderProp inp A

/-- Signers of the messages `⟨decide, v⟩` a correct leader receives in round 4. -/
def recv3 (v : Bool) : Finset (Proc t) :=
  univ.filter fun p => (p ∉ A.F ∧ rprop inp A p = some v) ∨ (p ∈ A.F ∧ v ∈ A.r3 p)

/-- Lines 9–12 for a correct leader: the value of the decide certificate it broadcasts. -/
def leaderCert : Option Bool :=
  if (recv3 inp A false).card = 2 * t + 1 then some false
  else if (recv3 inp A true).card = 2 * t + 1 then some true else none

/-- Lines 13–15: the decision of a correct process after round 5. -/
def dec5 (p : Proc t) : Option Bool :=
  if leader t ∈ A.F then A.r4 p else leaderCert inp A

/-- Round-1 signatures `⟨v⟩_p` available to the adversary. -/
def sigAvail (v : Bool) : Finset (Proc t) := univ.filter fun p => p ∈ A.F ∨ inp p = v

/-- `QC_propose(v)` (a `(t+1, n)`-threshold signature) can be formed. -/
def QCproposeAvail (v : Bool) : Prop := t + 1 ≤ (sigAvail inp A v).card

/-- `QC_decide(v)` (an `(n, n)`-threshold signature) can be formed: every correct process signed
`⟨decide, v⟩`. -/
def QCdecideAvail (v : Bool) : Prop := ∀ p, p ∉ A.F → rprop inp A p = some v

/-- Validity of the adversary: at most `t` Byzantine processes, unforgeability, synchrony. -/
structure AdvValid (δ : ℕ) : Prop where
  card_F : A.F.card ≤ t
  r2 : leader t ∈ A.F → ∀ p v, A.r2 p = some v → QCproposeAvail inp A v
  r4 : leader t ∈ A.F → ∀ p v, A.r4 p = some v → QCdecideAvail inp A v
  delay : ∀ p q, A.d p q ≤ δ
  fb : ∀ s q τ c, (s, q, τ, c) ∈ A.fb → s ∈ A.F ∧ ∀ v, c = some v → QCdecideAvail inp A v

/-! ### The fallback hand-off (lines 16–28) -/

/-- `Hears q τ`: process `q` has sent its fallback message by time `τ` (for a correct `q`), i.e.
it is undecided after round 5 (line 17), or it has received a fallback message by `τ` (line 26):
from a Byzantine process, or from a correct process `p` that sent its own at `τ'` with
`τ' + d p q ≤ τ`. -/
inductive Hears : Proc t → ℕ → Prop
  | start {q τ} : q ∉ A.F → dec5 inp A q = none → Hears q τ
  | byz {s q τ' τ c} : (s, q, τ', c) ∈ A.fb → τ' ≤ τ → Hears q τ
  | relay {p q τ' τ} : p ∉ A.F → Hears p τ' → τ' + A.d p q ≤ τ → Hears q τ

open Classical in
/-- The time a correct process sends its (unique) fallback message, `none` = never
(`fallback_start = ∞`). -/
noncomputable def fbTime (q : Proc t) : Option ℕ :=
  if h : ∃ τ, Hears inp A q τ then some (Nat.find h) else none

/-- `fallback_start` (lines 18, 27): the time `A_fallback` is started. -/
noncomputable def fbStart (δ : ℕ) (q : Proc t) : Option ℕ := (fbTime inp A q).map (· + 2 * δ)

/-- An arrival time `τ` lies in the window `[0, fallback_start]` of an undecided process
(`fallback_start = 2δ`); the right end is included iff `R.closedWindow`. -/
def InWindow (R : Reading) (δ τ : ℕ) : Prop := τ ≤ 2 * δ ∧ (R.closedWindow = true ∨ τ < 2 * δ)

/-- An undecided process `q` receives, in its window, a fallback message carrying a valid
`QC_decide(v)` (lines 21–22): from a Byzantine process, or the echo of a decided correct process. -/
def RecvProof (R : Reading) (δ : ℕ) (q : Proc t) (v : Bool) : Prop :=
  (∃ s τ, (s, q, τ, some v) ∈ A.fb ∧ InWindow R δ τ) ∨
  (R.attachProof = true ∧ ∃ p, p ∉ A.F ∧ dec5 inp A p = some v ∧
    ∃ τ, fbTime inp A p = some τ ∧ InWindow R δ (τ + A.d p q))

open Classical in
/-- `bu_decision`: the input of `A_fallback` (line 28). Decided processes use their decision; an
undecided one adopts a certified value (line 23) or keeps its input (intended initial value). -/
noncomputable def bu (R : Reading) (δ : ℕ) (q : Proc t) : Bool :=
  match dec5 inp A q with
  | some v => v
  | none => if RecvProof inp A R δ q true then true
    else if RecvProof inp A R δ q false then false else inp q

/-- The final decision (lines 14 and 29–30), given the outputs `out` of `A_fallback`. -/
noncomputable def decision (out : Proc t → Option Bool) (q : Proc t) : Option Bool :=
  match dec5 inp A q with
  | some v => some v
  | none => if (fbTime inp A q).isSome then out q else none

/-- **Black-box specification of `A_fallback`** (a strong BA protocol, run with `δ' = 2δ`): if all
correct processes start it, at most `δ` apart, then the outputs of the correct processes satisfy
agreement, termination and strong unanimity w.r.t. their inputs. -/
def FallbackSpec {P : Type*} (δ : ℕ) (C : Set P) (start : P → Option ℕ) (fin : P → Bool)
    (out : P → Option Bool) : Prop :=
  (∀ p ∈ C, ∃ a, start p = some a) →
  (∀ p ∈ C, ∀ q ∈ C, ∀ a b, start p = some a → start q = some b → a ≤ b + δ) →
  Agreement C out ∧ Termination C out ∧ StrongUnanimity C fin out

/-! ### Basic facts -/

variable {inp A}

lemma exists_correct {δ : ℕ} (hA : AdvValid inp A δ) : ∃ p, p ∉ A.F := by
  by_contra h
  push Not at h
  have : (univ : Finset (Proc t)) ⊆ A.F := fun p _ => h p
  have := card_le_card this
  simp at this
  have := hA.card_F
  omega

lemma leaderProp_some {v : Bool} (h : leaderProp inp A = some v) :
    t + 1 ≤ (recv1 inp A v).card := by
  unfold leaderProp at h
  split_ifs at h with h1 h2 <;> cases h <;> assumption

lemma leaderCert_some {v : Bool} (h : leaderCert inp A = some v) :
    (recv3 inp A v).card = 2 * t + 1 := by
  unfold leaderCert at h
  split_ifs at h with h1 h2 <;> cases h <;> assumption

/-- A correct process decides at line 14 only on a value with an available `QC_decide`. -/
lemma dec5_avail {δ : ℕ} (hA : AdvValid inp A δ) {p : Proc t} {v : Bool}
    (h : dec5 inp A p = some v) : QCdecideAvail inp A v := by
  unfold dec5 at h
  split_ifs at h with hl
  · exact hA.r4 hl p v h
  · have hc := leaderCert_some h
    have huniv : recv3 inp A v = univ := eq_univ_of_card _ (by simpa using hc)
    intro q hq
    have : q ∈ recv3 inp A v := huniv ▸ mem_univ q
    simp only [recv3, mem_filter, mem_univ, true_and] at this
    tauto

/-- Uniqueness of decide certificates: correct processes sign one decide message only. -/
lemma qcd_unique {δ : ℕ} (hA : AdvValid inp A δ) {v w : Bool}
    (hv : QCdecideAvail inp A v) (hw : QCdecideAvail inp A w) : v = w := by
  obtain ⟨c, hc⟩ := exists_correct hA
  have := (hv c hc).symm.trans (hw c hc)
  simpa using this

lemma recvProof_avail {δ : ℕ} (hA : AdvValid inp A δ) {R : Reading} {q : Proc t} {v : Bool}
    (h : RecvProof inp A R δ q v) : QCdecideAvail inp A v := by
  rcases h with ⟨s, τ, hm, -⟩ | ⟨-, p, -, hp, -⟩
  · exact (hA.fb _ _ _ _ hm).2 v rfl
  · exact dec5_avail hA hp

/-- If all correct processes have input `v`, the only value a correct process can sign a decide
message for is `v` (no `QC_propose(¬v)` exists). -/
lemma rprop_unanimous {δ : ℕ} (hA : AdvValid inp A δ) {v w : Bool}
    (hv : ∀ p, p ∉ A.F → inp p = v) {p : Proc t} (hp : rprop inp A p = some w) : w = v := by
  by_contra hwv
  unfold rprop at hp
  split_ifs at hp with hl
  · have h1 := hA.r2 hl p w hp
    have hsub : sigAvail inp A w ⊆ A.F := by
      intro q hq
      simp only [sigAvail, mem_filter, mem_univ, true_and] at hq
      by_contra hqF
      exact hwv ((hq.resolve_left hqF).symm.trans (hv q hqF))
    have := card_le_card hsub
    unfold QCproposeAvail at h1
    have := hA.card_F
    omega
  · have h1 := leaderProp_some hp
    have hsub : recv1 inp A w ⊆ A.F := by
      intro q hq
      simp only [recv1, mem_filter, mem_univ, true_and] at hq
      rcases hq with ⟨hqF, hq⟩ | ⟨hqF, -⟩
      · exact absurd (hq.symm.trans (hv q hqF)) hwv
      · exact hqF
    have := card_le_card hsub
    have := hA.card_F
    omega

lemma qcd_unanimous {δ : ℕ} (hA : AdvValid inp A δ) {v w : Bool}
    (hv : ∀ p, p ∉ A.F → inp p = v) (hw : QCdecideAvail inp A w) : w = v := by
  obtain ⟨c, hc⟩ := exists_correct hA
  exact rprop_unanimous hA hv (hw c hc)

/-! ### Hearing times -/

lemma Hears.mono {q : Proc t} {τ τ' : ℕ} (h : Hears inp A q τ) (hle : τ ≤ τ') :
    Hears inp A q τ' := by
  cases h with
  | start h1 h2 => exact .start h1 h2
  | byz hm h => exact .byz hm (h.trans hle)
  | relay hp hh h => exact .relay hp hh (h.trans hle)

open Classical in
lemma fbTime_some {q : Proc t} {τ : ℕ} (h : fbTime inp A q = some τ) : Hears inp A q τ := by
  unfold fbTime at h
  split_ifs at h with hex
  cases h
  exact Nat.find_spec hex

open Classical in
lemma fbTime_le {q : Proc t} {τ : ℕ} (h : Hears inp A q τ) :
    ∃ τ₀, fbTime inp A q = some τ₀ ∧ τ₀ ≤ τ := by
  have hex : ∃ τ, Hears inp A q τ := ⟨τ, h⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex h⟩
  simp [fbTime, hex]

lemma fbTime_undecided {q : Proc t} (hq : q ∉ A.F) (h : dec5 inp A q = none) :
    fbTime inp A q = some 0 := by
  obtain ⟨τ₀, h1, h2⟩ := fbTime_le (Hears.start (τ := 0) hq h)
  rw [h1, Nat.le_zero.mp h2]

/-- Core of Lemma 25: if a correct `p` sends its fallback message at `a`, every correct `q` sends
its own by `a + δ`. -/
lemma fbTime_spread {δ : ℕ} (hA : AdvValid inp A δ) {p q : Proc t} (hp : p ∉ A.F) {a : ℕ}
    (ha : fbTime inp A p = some a) : ∃ b, fbTime inp A q = some b ∧ b ≤ a + δ := by
  obtain ⟨b, hb, hle⟩ :=
    fbTime_le (Hears.relay (q := q) (τ := a + A.d p q) hp (fbTime_some ha) le_rfl)
  exact ⟨b, hb, hle.trans (by have := hA.delay p q; omega)⟩

/-- **Lemma 25** of [CKS22]: if some correct process executes the fallback algorithm, all correct
processes do, and their start times are at most `δ` apart. -/
theorem lemma25 {δ : ℕ} (hA : AdvValid inp A δ) (h : ∃ p ∈ correct A, ∃ a, fbStart inp A δ p = some a) :
    (∀ q ∈ correct A, ∃ b, fbStart inp A δ q = some b) ∧
    (∀ p ∈ correct A, ∀ q ∈ correct A, ∀ a b,
      fbStart inp A δ p = some a → fbStart inp A δ q = some b → a ≤ b + δ) := by
  obtain ⟨p, hp, a, ha⟩ := h
  simp only [fbStart, Option.map_eq_some_iff] at ha
  obtain ⟨a', ha', -⟩ := ha
  refine ⟨fun q _ => ?_, fun p₁ _ q₁ hq₁ a b ha hb => ?_⟩
  · obtain ⟨b, hb, -⟩ := fbTime_spread (q := q) hA hp ha'
    exact ⟨b + 2 * δ, by simp [fbStart, hb]⟩
  · simp only [fbStart, Option.map_eq_some_iff] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c, hc, hle⟩ := fbTime_spread (q := p₁) hA hq₁ hb₀
    rw [ha₀] at hc
    cases hc
    omega


/-! ### Agreement, termination, strong unanimity (Lemmas 26–29, Theorem 7/30) -/

lemma decision_decided {out : Proc t → Option Bool} {q : Proc t} {v : Bool}
    (h : dec5 inp A q = some v) : decision inp A out q = some v := by
  simp [decision, h]

lemma decision_undecided {out : Proc t → Option Bool} {q : Proc t} (hq : q ∉ A.F)
    (h : dec5 inp A q = none) : decision inp A out q = out q := by
  simp [decision, h, fbTime_undecided hq h]

/-- If a correct `p` decided `v` at line 14, every correct `q` that did not decide receives `p`'s
certified echo in its safety window: `p` hears `q`'s line-17 message by `δ` and its echo reaches
`q` by `2δ`. -/
lemma recvProof_of_decided {δ : ℕ} (hA : AdvValid inp A δ) {p q : Proc t} (hp : p ∉ A.F)
    (hq : q ∉ A.F) {v : Bool} (hpv : dec5 inp A p = some v) (hqu : dec5 inp A q = none) :
    RecvProof inp A .intended δ q v := by
  right
  refine ⟨rfl, p, hp, hpv, ?_⟩
  obtain ⟨a, ha, hle⟩ :=
    fbTime_le (Hears.relay (q := p) (τ := 0 + A.d q p) hq (Hears.start hq hqu) le_rfl)
  refine ⟨a, ha, ?_, Or.inl rfl⟩
  have := hA.delay q p
  have := hA.delay p q
  omega

/-- If a correct process decided `v` at line 14, all correct processes run `A_fallback` (if at
all) with input `v`. -/
lemma bu_eq_of_decided {δ : ℕ} (hA : AdvValid inp A δ) {p : Proc t} (hp : p ∉ A.F) {v : Bool}
    (hpv : dec5 inp A p = some v) {q : Proc t} (hq : q ∉ A.F) : bu inp A .intended δ q = v := by
  cases hq5 : dec5 inp A q with
  | some w =>
    simp only [bu, hq5]
    exact qcd_unique hA (dec5_avail hA hq5) (dec5_avail hA hpv)
  | none =>
    have h1 := recvProof_of_decided hA hp hq hpv hq5
    have h2 : ¬ RecvProof inp A .intended δ q (!v) := fun h =>
      by simpa using qcd_unique hA (recvProof_avail hA h) (dec5_avail hA hpv)
    cases v <;> simp_all [bu]

/-- If all correct processes have input `v`, they all run `A_fallback` with input `v`. -/
lemma bu_unanimous {δ : ℕ} (hA : AdvValid inp A δ) {v : Bool} (hv : ∀ p, p ∉ A.F → inp p = v)
    {q : Proc t} (hq : q ∉ A.F) : bu inp A .intended δ q = v := by
  cases hq5 : dec5 inp A q with
  | some w =>
    simp only [bu, hq5]
    exact qcd_unanimous hA hv (dec5_avail hA hq5)
  | none =>
    simp only [bu, hq5]
    split_ifs with h1 h2
    · exact qcd_unanimous hA hv (recvProof_avail hA h1)
    · exact qcd_unanimous hA hv (recvProof_avail hA h2)
    · exact hv q hq

/-- If some correct process is undecided after round 5, the black-box guarantees of
`A_fallback` apply (by Lemma 25). -/
lemma fallback_runs {δ : ℕ} (hA : AdvValid inp A δ) {q : Proc t} (hq : q ∉ A.F)
    (hu : dec5 inp A q = none) {fin : Proc t → Bool} {out : Proc t → Option Bool}
    (hfb : FallbackSpec δ (correct A) (fbStart inp A δ) fin out) :
    Agreement (correct A) out ∧ Termination (correct A) out ∧
      StrongUnanimity (correct A) fin out := by
  have h := lemma25 hA ⟨q, hq, 2 * δ, by simp [fbStart, fbTime_undecided hq hu]⟩
  exact hfb h.1 h.2

variable (inp A) in
/-- The black-box hypothesis of the main theorem: the outputs `out` of `A_fallback`, started with
inputs `bu_decision` at times `fallback_start`, satisfy the strong BA specification whenever
Lemma 18 applies. -/
abbrev FallbackOK (δ : ℕ) (out : Proc t → Option Bool) : Prop :=
  FallbackSpec δ (correct A) (fbStart inp A δ) (bu inp A .intended δ) out

/-- **Lemma 26** of [CKS22] (Agreement). -/
theorem lemma26 {δ : ℕ} (hA : AdvValid inp A δ) {out : Proc t → Option Bool}
    (hfb : FallbackOK inp A δ out) : Agreement (correct A) (decision inp A out) := by
  intro p hp q hq a b ha hb
  simp only [correct, Set.mem_ofPred_eq] at hp hq
  cases hp5 : dec5 inp A p with
  | none =>
    rw [decision_undecided hp hp5] at ha
    cases hq5 : dec5 inp A q with
    | none =>
      rw [decision_undecided hq hq5] at hb
      exact (fallback_runs hA hp hp5 hfb).1 p hp q hq a b ha hb
    | some w =>
      rw [decision_decided hq5] at hb
      cases hb
      exact (fallback_runs hA hp hp5 hfb).2.2 b
        (fun r hr => bu_eq_of_decided hA hq hq5 hr) p hp a ha
  | some w =>
    rw [decision_decided hp5] at ha
    cases ha
    cases hq5 : dec5 inp A q with
    | none =>
      rw [decision_undecided hq hq5] at hb
      exact ((fallback_runs hA hq hq5 hfb).2.2 a
        (fun r hr => bu_eq_of_decided hA hp hp5 hr) q hq b hb).symm
    | some w' =>
      rw [decision_decided hq5] at hb
      cases hb
      exact qcd_unique hA (dec5_avail hA hp5) (dec5_avail hA hq5)

/-- **Lemma 27** of [CKS22] (Termination). -/
theorem lemma27 {δ : ℕ} (hA : AdvValid inp A δ) {out : Proc t → Option Bool}
    (hfb : FallbackOK inp A δ out) : Termination (correct A) (decision inp A out) := by
  intro p hp
  simp only [correct, Set.mem_ofPred_eq] at hp
  cases hp5 : dec5 inp A p with
  | none =>
    rw [decision_undecided hp hp5]
    exact (fallback_runs hA hp hp5 hfb).2.1 p hp
  | some w => exact ⟨w, decision_decided hp5⟩

/-- **Lemma 28** of [CKS22] (Validity = strong unanimity). -/
theorem lemma28 {δ : ℕ} (hA : AdvValid inp A δ) {out : Proc t → Option Bool}
    (hfb : FallbackOK inp A δ out) : StrongUnanimity (correct A) inp (decision inp A out) := by
  intro v hv p hp a ha
  have hv' : ∀ p, p ∉ A.F → inp p = v := fun p hp => hv p hp
  simp only [correct, Set.mem_ofPred_eq] at hp
  cases hp5 : dec5 inp A p with
  | none =>
    rw [decision_undecided hp hp5] at ha
    exact (fallback_runs hA hp hp5 hfb).2.2 v (fun r hr => bu_unanimous hA hv' hr) p hp a ha
  | some w =>
    rw [decision_decided hp5] at ha
    cases ha
    exact qcd_unanimous hA hv' (dec5_avail hA hp5)

/-- **Lemma 29** of [CKS22]: a correct process decides at most once — a decision taken at
line 14 is the final decision, whatever `A_fallback` outputs; otherwise the decision is the
fallback output (taken once, line 30). -/
theorem lemma29 (out : Proc t → Option Bool) (q : Proc t) :
    (∀ v, dec5 inp A q = some v → decision inp A out q = some v) ∧
    (dec5 inp A q = none → decision inp A out q = out q ∨ decision inp A out q = none) := by
  refine ⟨fun v h => decision_decided h, fun h => ?_⟩
  simp only [decision, h]
  split_ifs <;> simp

/-- **Theorem 7 / Theorem 30** of [CKS22]: Algorithm 5 (intended reading) solves binary strong BA
with `n = 2t + 1`, for every valid adversary and every behaviour of `A_fallback` allowed by its
strong BA specification. -/
theorem theorem7 {δ : ℕ} (hA : AdvValid inp A δ) {out : Proc t → Option Bool}
    (hfb : FallbackOK inp A δ out) :
    Agreement (correct A) (decision inp A out) ∧ Termination (correct A) (decision inp A out) ∧
      StrongUnanimity (correct A) inp (decision inp A out) :=
  ⟨lemma26 hA hfb, lemma27 hA hfb, lemma28 hA hfb⟩

/-! ### Complexity (Lemma 8, Section 7.1) -/

variable (inp A) in
/-- Words sent by correct processes in rounds 1–5 (one word per message: a value with a
(threshold) signature): round 1 (each correct process to the leader), round 2 (a correct leader's
propose broadcast), round 3 (decide messages), round 4 (a correct leader's certificate broadcast). -/
def wordsRounds : ℕ :=
  (univ.filter fun p : Proc t => p ∉ A.F).card
  + (if leader t ∉ A.F ∧ (leaderProp inp A).isSome then 2 * t + 1 else 0)
  + (univ.filter fun p => p ∉ A.F ∧ (rprop inp A p).isSome).card
  + (if leader t ∉ A.F ∧ (leaderCert inp A).isSome then 2 * t + 1 else 0)

variable (inp A) in
open Classical in
/-- Words sent by correct processes in the hand-off: each sends at most one fallback broadcast
(line 17 or line 26). The words of `A_fallback` itself are not counted (black box, `O(n²)`). -/
noncomputable def wordsHandoff : ℕ :=
  (2 * t + 1) * (univ.filter fun p : Proc t => p ∉ A.F ∧ (fbTime inp A p).isSome).card

variable (inp A) in
lemma wordsRounds_le : wordsRounds inp A ≤ 4 * (2 * t + 1) := by
  unfold wordsRounds
  have h1 := card_le_univ (univ.filter fun p : Proc t => p ∉ A.F)
  have h2 := card_le_univ (univ.filter fun p => p ∉ A.F ∧ (rprop inp A p).isSome)
  simp only [Fintype.card_fin] at h1 h2
  split_ifs <;> omega

variable (inp A) in
lemma wordsHandoff_le : wordsHandoff inp A ≤ (2 * t + 1) * (2 * t + 1) := by
  unfold wordsHandoff
  have := card_le_univ (univ.filter fun p : Proc t => p ∉ A.F ∧ (fbTime inp A p).isSome)
  simp only [Fintype.card_fin] at this
  exact Nat.mul_le_mul_left _ this

/-- In a failure-free run every process decides at line 14 (on a value proposed by `t + 1`
processes). -/
lemma dec5_failureFree (hF : A.F = ∅) :
    ∃ w, ∀ p, dec5 inp A p = some w := by
  have hl : leader t ∉ A.F := by simp [hF]
  have hr1 : ∀ v, recv1 inp A v = univ.filter fun p => inp p = v := by
    intro v; ext p; simp [recv1, hF]
  -- one of the two values has `t + 1` supporters
  have hsum : (recv1 inp A true).card + (recv1 inp A false).card = 2 * t + 1 := by
    rw [hr1, hr1]
    have := card_filter_add_card_filter_not (s := (univ : Finset (Proc t)))
      (fun p => inp p = true)
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w, leaderProp inp A = some w := by
    unfold leaderProp
    split_ifs <;> first | exact ⟨_, rfl⟩ | omega
  have hrp : ∀ p, rprop inp A p = some w := fun p => by simp [rprop, hl, hw]
  have hr3 : ∀ v, recv3 inp A v = if w = v then univ else ∅ := by
    intro v; ext p; split_ifs with h <;> simp [recv3, hF, hrp, h]
  refine ⟨w, fun p => ?_⟩
  simp only [dec5, hl, ite_false, leaderCert, hr3]
  cases w <;> simp

/-- **Lemma 8** of [CKS22] and the complexity claim of Section 7.1: if `f = 0`, no correct process
runs the fallback (nor sends a fallback message), every process decides at line 14, and the
correct processes send at most `4n` words. -/
theorem lemma8 {δ : ℕ} (hA : AdvValid inp A δ) (hF : A.F = ∅) :
    (∀ p, fbTime inp A p = none) ∧ (∃ w, ∀ p, dec5 inp A p = some w) ∧
      wordsRounds inp A + wordsHandoff inp A ≤ 4 * (2 * t + 1) := by
  obtain ⟨w, hw⟩ := dec5_failureFree (inp := inp) hF
  have hno : ∀ q τ, ¬ Hears inp A q τ := by
    intro q τ h
    induction h with
    | start _ h2 => simp [hw] at h2
    | byz hm _ => simpa [hF] using (hA.fb _ _ _ _ hm).1
    | relay _ _ _ ih => exact ih
  have hfb : ∀ p, fbTime inp A p = none := fun p => by simp [fbTime, hno]
  refine ⟨hfb, ⟨w, hw⟩, ?_⟩
  have : wordsHandoff inp A = 0 := by simp [wordsHandoff, hfb]
  have := wordsRounds_le inp A
  omega

variable (inp A) in
/-- In every run the correct processes send at most `4n + n²` words outside `A_fallback`
(Section 7.1: "otherwise the complexity is that of the fallback algorithm, `O(n²)`"). -/
theorem words_le : wordsRounds inp A + wordsHandoff inp A ≤ 4 * (2 * t + 1) + (2 * t + 1) ^ 2 := by
  have := wordsRounds_le inp A
  have := wordsHandoff_le inp A
  nlinarith

end Podc.AdaptiveBAFewerWords.StrongBA
