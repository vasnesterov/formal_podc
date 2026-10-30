import Papers.PODC2022.ClockSyncSignatures.APA
import Cslib.Computability.Distributed.Byzantine.LockStep.Auth
import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement
import Cslib.Computability.Distributed.Byzantine.Specs
import Cslib.Computability.Distributed.ApproxConsensus.Contraction
import Cslib.Foundations.Data.Real.Logb

/-!
# Iterated APA with signature-based crusader broadcast in the synchronous model

Lenzen–Loss, *Optimal Clock Synchronization with Signatures* (PODC 2022): Algorithm CB (Figure 4),
Algorithm APA (Figure 1), Theorem 9 and Corollary 2.

## The protocol

We use CSLib's synchronous lock-step model (`Cslib.Byzantine.LockStep`) on the complete network
`⊤` of the `n = Fintype.card P` nodes, with ideal signatures (`LockStep.Auth`: abstract tokens;
honest nodes are `Unforging`, the rushing adversary only uses signatures of corrupted nodes or
signatures already emitted by honest nodes, `Scenario.AuthValid`).

A signature token `(d, j, v)` is `d`'s signature on "my value in iteration `j` is `v`" (the
iteration number prevents replaying old signatures). `alg f K` runs `K` iterations of APA; iteration
`j` takes rounds `2j` and `2j + 1` and runs `n` crusader-broadcast instances in parallel, one per
dealer:

* round `2j` (CB step 1): every node `p` signs its current value `val_j(p)` and sends
  `init (p, j, val_j(p))` to all;
* round `2j + 1` (CB step 2): every node forwards to all, for every dealer `d`, the token it received
  from `d` in round `2j` (`echo`);
* after round `2j + 1`, node `w` computes the output of the instance of dealer `d` (`cbOut`): `⊥` if
  the token received from `d` is not a valid signature of `d` on iteration `j`, or if some echo
  contains a valid signature of `d` on iteration `j` with a different value; otherwise the signed
  value. Then (APA) `val_{j+1}(w) = apaOut f (cbOut …)` (`APA.lean`).

After `2K` rounds every node decides `val_K`.

## Main results

* `cb_isCrusader`: in every iteration, the CB outputs satisfy validity and crusader consistency
  (Definition 6) for any number of corrupted nodes.
* `theorem_9`: `alg f 1` (with `f = ⌈n/2⌉ - 1`) is an `(ℓ, ℓ/2, ⌈n/2⌉ - 1)`-secure two-round
  protocol for approximate agreement, for every `ℓ`.
* `corollary_2`: `K = ⌈log₂(ℓ/ε)⌉` iterations give an `(ℓ, ε, ⌈n/2⌉ - 1)`-secure protocol running in
  `2K` rounds.
-/

open Cslib.Byzantine Cslib.Byzantine.LockStep

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Podc.ClockSyncSignatures

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### Messages and signatures -/

/-- A signature token `(d, j, v)`: the signature of `d` on "my value in iteration `j` is `v`". -/
abbrev Tok (P : Type*) := P × ℕ × ℝ

/-- Messages: a signed value (first CB round) or a vector of forwarded tokens, one per dealer
(second CB round). -/
inductive Msg (P : Type*)
  | init (σ : Tok P)
  | echo (e : P → Option (Tok P))

/-- The signature structure: a token is signed by its first component. -/
def auth : LockStep.Auth P (Msg P) (Tok P) where
  signer τ := τ.1
  tokens
    | .init σ => {σ}
    | .echo e => {τ | ∃ d, e d = some τ}

/-- The token carried by a first-round message. -/
def Msg.initTok : Msg P → Option (Tok P)
  | .init σ => some σ
  | .echo _ => none

/-- The token forwarded for dealer `d` by a second-round message. -/
def Msg.echoTok (d : P) : Msg P → Option (Tok P)
  | .init _ => none
  | .echo e => e d

/-! ### The local computation -/

/-- The inbox of round `k` in a history (empty if not received yet). -/
def inboxAt (h : History P (Msg P)) (k : ℕ) : Inbox P (Msg P) := h[k]?.getD fun _ => none

/-- The token node `p` (with own current value `own`) received from dealer `d` in the first round of
iteration `j`; for `d = p` it is `p`'s own signed value (a node also sends to itself). -/
def recvInit (p : P) (own : ℝ) (h : History P (Msg P)) (j : ℕ) (d : P) : Option (Tok P) :=
  if d = p then some (p, j, own) else (inboxAt h (2 * j) d).bind Msg.initTok

/-- Some echo of iteration `j` contains a valid signature of `d` on iteration `j` with a value
different from `b`. -/
def Conflict (h : History P (Msg P)) (j : ℕ) (d : P) (b : ℝ) : Prop :=
  ∃ u σ, (inboxAt h (2 * j + 1) u).bind (Msg.echoTok d) = some σ ∧ σ.1 = d ∧ σ.2.1 = j ∧ σ.2.2 ≠ b

/-- Algorithm CB (Figure 4) at node `p`, instance of dealer `d`, iteration `j`: output `⊥` if the
token received from `d` is not a valid signature of `d` (for iteration `j`) or if a conflicting
valid signature was echoed; otherwise output the signed value. -/
def cbOut (p : P) (own : ℝ) (h : History P (Msg P)) (j : ℕ) (d : P) : Option ℝ :=
  (recvInit p own h j d).bind fun σ =>
    if σ.1 = d ∧ σ.2.1 = j ∧ ¬ Conflict h j d σ.2.2 then some σ.2.2 else none

/-- The value of node `p` (input `x`) in iteration `j`, computed from its history: `val 0 = x`,
`val (j + 1)` is the APA output on the CB outputs of iteration `j`. -/
def val (f : ℕ) (p : P) (x : ℝ) (h : History P (Msg P)) : ℕ → ℝ
  | 0 => x
  | j + 1 => apaOut f (cbOut p (val f p x h j) h j)

/-- `K` iterations of APA over CB, tolerating `f` faults; two rounds per iteration. -/
def alg (f K : ℕ) : Protocol P ℝ (Msg P) ℝ where
  send p x h _ :=
    if h.length < 2 * K then
      if h.length % 2 = 0 then some (.init (p, h.length / 2, val f p x h (h.length / 2)))
      else some (.echo (recvInit p (val f p x h (h.length / 2)) h (h.length / 2)))
    else none
  decide p x h := if 2 * K ≤ h.length then some (val f p x h K) else none

/-! ### Locality: values only depend on the relevant inboxes -/

theorem recvInit_congr {p : P} {own : ℝ} {h h' : History P (Msg P)} {j : ℕ}
    (hh : inboxAt h (2 * j) = inboxAt h' (2 * j)) : recvInit p own h j = recvInit p own h' j := by
  funext d; simp only [recvInit, hh]

theorem conflict_congr {h h' : History P (Msg P)} {j : ℕ} {d : P} {b : ℝ}
    (hh : inboxAt h (2 * j + 1) = inboxAt h' (2 * j + 1)) : Conflict h j d b ↔ Conflict h' j d b := by
  simp only [Conflict, hh]

theorem cbOut_congr {p : P} {own : ℝ} {h h' : History P (Msg P)} {j : ℕ}
    (h0 : inboxAt h (2 * j) = inboxAt h' (2 * j))
    (h1 : inboxAt h (2 * j + 1) = inboxAt h' (2 * j + 1)) : cbOut p own h j = cbOut p own h' j := by
  funext d
  simp only [cbOut, recvInit_congr (p := p) (own := own) h0]
  congr 1; funext σ
  simp only [conflict_congr (d := d) (b := σ.2.2) h1]

theorem val_congr {f : ℕ} {p : P} {x : ℝ} {h h' : History P (Msg P)} {j : ℕ}
    (hh : ∀ k < 2 * j, inboxAt h k = inboxAt h' k) : val f p x h j = val f p x h' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [val]
    rw [ih fun k hk => hh k (by omega), cbOut_congr (hh _ (by omega)) (hh _ (by omega))]

/-! ### Runs -/

variable (f K : ℕ) (s : Scenario P ℝ (Msg P))

/-- The complete network. -/
abbrev net : SimpleGraph P := ⊤

/-- The history of `p` after `r` rounds. -/
abbrev H (r : ℕ) (p : P) : History P (Msg P) := hist net (alg f K) s r p

/-- The value of `p` in iteration `j` of the run. -/
def V (j : ℕ) (p : P) : ℝ := val f p (s.input p) (H f K s (2 * j) p) j

/-- The CB outputs of iteration `j` at node `w` (instance of dealer `d`). -/
def O (j : ℕ) (w d : P) : Option ℝ := cbOut w (V f K s j w) (H f K s (2 * j + 2) w) j d

variable {f K s}

theorem inboxAt_hist {k R : ℕ} (hk : k < R) (p : P) :
    inboxAt (H f K s R p) k = fun q => deliver net (alg f K) s (H f K s k) k q p := by
  simp [inboxAt, H, getElem?_hist _ _ s hk]

theorem inboxAt_hist_eq {k R R' : ℕ} (hk : k < R) (hk' : k < R') (p : P) :
    inboxAt (H f K s R p) k = inboxAt (H f K s R' p) k := by
  rw [inboxAt_hist hk, inboxAt_hist hk']

theorem val_hist {j R : ℕ} (hR : 2 * j ≤ R) (p : P) :
    val f p (s.input p) (H f K s R p) j = V f K s j p :=
  val_congr fun k hk => inboxAt_hist_eq (by omega) hk p

theorem V_succ (j : ℕ) (w : P) : V f K s (j + 1) w = apaOut f (O f K s j w) := by
  simp only [V, val]
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, val_hist (by omega)]
  rfl

theorem send_init {j : ℕ} (hj : j < K) (p : P) (x : ℝ) (h : History P (Msg P))
    (hl : h.length = 2 * j) (q : P) :
    (alg f K).send p x h q = some (.init (p, j, val f p x h j)) := by
  have h2 : h.length / 2 = j := by omega
  simp [alg, hl, show 2 * j < 2 * K by omega]

theorem send_echo {j : ℕ} (hj : j < K) (p : P) (x : ℝ) (h : History P (Msg P))
    (hl : h.length = 2 * j + 1) (q : P) :
    (alg f K).send p x h q = some (.echo (recvInit p (val f p x h j) h j)) := by
  have h2 : h.length / 2 = j := by omega
  have h3 : h.length % 2 ≠ 0 := by omega
  simp only [alg]
  simp only [show h.length < 2 * K by omega, h3, ↓reduceIte, h2]

/-! ### Unforgeability -/


theorem mem_tokens_send {p : P} {x : ℝ} {h : History P (Msg P)} {q : P} {m : Msg P}
    (hm : (alg f K).send p x h q = some m) {τ : Tok P} (hτ : τ ∈ auth.tokens m) :
    τ = (p, h.length / 2, val f p x h (h.length / 2)) ∨
      h.length % 2 = 1 ∧
        ∃ d, d ≠ p ∧ (inboxAt h (2 * (h.length / 2)) d).bind Msg.initTok = some τ := by
  simp only [alg] at hm
  split_ifs at hm with h1 h2
  · cases hm; exact Or.inl hτ
  · cases hm
    obtain ⟨d, hd⟩ := hτ
    simp only [recvInit] at hd
    split_ifs at hd with hdp
    · cases hd; exact Or.inl rfl
    · exact Or.inr ⟨by omega, d, hdp, hd⟩

theorem mem_histTokens_of_initTok {h : History P (Msg P)} {k : ℕ} (hk : k < h.length) {d : P}
    {τ : Tok P} (hτ : (inboxAt h k d).bind Msg.initTok = some τ) :
    τ ∈ LockStep.Auth.histTokens auth h := by
  obtain ⟨m, hm, hmτ⟩ := Option.bind_eq_some_iff.1 hτ
  refine ⟨h[k], List.getElem_mem hk, d, m, ?_, ?_⟩
  · simpa [inboxAt, List.getElem?_eq_getElem hk] using hm
  · cases m with
    | init σ => cases hmτ; rfl
    | echo e => cases hmτ

/-- Honest nodes only emit their own signatures and signatures they received. -/
theorem alg_unforging : (alg (P := P) f K).Unforging auth := by
  intro p x h q m hm τ hτ
  rcases mem_tokens_send hm hτ with rfl | ⟨hodd, d, -, hd⟩
  · exact Or.inl rfl
  · exact Or.inr (mem_histTokens_of_initTok (by omega) hd)

theorem mem_histTokens_of_inboxAt {h : History P (Msg P)} {k : ℕ} (hk : k < h.length) {u : P}
    {m : Msg P} (hm : inboxAt h k u = some m) {τ : Tok P} (hτ : τ ∈ (auth (P := P)).tokens m) :
    τ ∈ LockStep.Auth.histTokens auth h :=
  ⟨h[k], List.getElem_mem hk, u, m, by simpa [inboxAt, List.getElem?_eq_getElem hk] using hm, hτ⟩

theorem mem_tokens_of_echoTok {d : P} {m : Msg P} {τ : Tok P} (h : m.echoTok d = some τ) :
    τ ∈ (auth (P := P)).tokens m := by
  cases m with
  | init σ => cases h
  | echo e => exact ⟨d, h⟩

/-! ### The token invariant: honest signatures are never forged -/

variable (f K s) in
/-- A token is *good* if, when its signer is honest, it carries the signer's actual value in the
token's iteration. -/
def Good (τ : Tok P) : Prop := τ.1 ∉ s.byz → τ.2.2 = V f K s τ.2.1 τ.1

theorem good_of_send {r : ℕ} {p : P}
    (hinv : ∀ τ ∈ LockStep.Auth.histTokens auth (H f K s r p), Good f K s τ) {q : P} {m : Msg P}
    (hm : (alg f K).send p (s.input p) (H f K s r p) q = some m) {τ : Tok P}
    (hτ : τ ∈ (auth (P := P)).tokens m) : Good f K s τ := by
  rcases mem_tokens_send hm hτ with rfl | ⟨hodd, d, -, hd⟩
  · intro _
    show val f p (s.input p) (H f K s r p) ((H f K s r p).length / 2) =
      V f K s ((H f K s r p).length / 2) p
    rw [show (H f K s r p).length = r from length_hist _ _ _ _ _]
    exact val_hist (by omega) p
  · exact hinv τ (mem_histTokens_of_initTok (by omega) hd)

/-- Every token in the history of an honest node is good. -/
theorem good_hist (hauth : s.AuthValid net (alg f K) auth) :
    ∀ r q, q ∉ s.byz → ∀ τ ∈ LockStep.Auth.histTokens auth (H f K s r q), Good f K s τ := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro q hq τ hτ
  cases r with
  | zero => simp [LockStep.Auth.histTokens] at hτ
  | succ r =>
    rw [H, hist_succ, LockStep.Auth.histTokens_append] at hτ
    rcases hτ with hτ | hτ
    · exact ih r (by omega) q hq τ hτ
    · obtain ⟨ib, hib, p, m, hm, hτm⟩ := hτ
      simp only [List.mem_singleton] at hib
      subst hib
      simp only [deliver] at hm
      split_ifs at hm with hadj hpb hdrop
      · rcases hauth r p q m hpb hq hadj hm τ hτm with hs | ⟨r', hr', p', hp', q', -, m', hm', hτ'⟩
        · exact fun h => absurd hs h
        · exact good_of_send (ih r' (by omega) p' hp') hm' hτ'
      · exact good_of_send (ih r (by omega) p hpb) hm hτm

/-! ### Crusader broadcast: validity and crusader consistency (Definition 6) -/

theorem inboxAt_init (hrel : s.Reliable) {j : ℕ} (hj : j < K) {d w : P} (hd : d ∉ s.byz)
    (hdw : d ≠ w) {R : ℕ} (hR : 2 * j < R) :
    inboxAt (H f K s R w) (2 * j) d = some (.init (d, j, V f K s j d)) := by
  rw [inboxAt_hist hR]
  simp only
  rw [deliver_honest _ _ s hrel hd (by simpa using hdw), send_init hj _ _ _ (by simp)]
  rfl

theorem inboxAt_echo (hrel : s.Reliable) {j : ℕ} (hj : j < K) {u w : P} (hu : u ∉ s.byz)
    (huw : u ≠ w) {R : ℕ} (hR : 2 * j + 1 < R) :
    inboxAt (H f K s R w) (2 * j + 1) u =
      some (.echo (recvInit u (V f K s j u) (H f K s R u) j)) := by
  rw [inboxAt_hist hR]
  simp only
  rw [deliver_honest _ _ s hrel hu (by simpa using huw), send_echo hj _ _ _ (by simp),
    val_hist (R := 2 * j + 1) (by omega),
    recvInit_congr (inboxAt_hist_eq (k := 2 * j) (R := 2 * j + 1) (R' := R) (by omega) (by omega) u)]

/-- In every iteration `j < K`, the outputs of the `n` parallel CB instances satisfy validity and
crusader consistency (Definition 6), whatever the number of corrupted nodes. -/
theorem cb_isCrusader (hrel : s.Reliable) (hauth : s.AuthValid net (alg f K) auth) {F : Finset P}
    (hF : (F : Set P) = s.byz) {j : ℕ} (hj : j < K) : IsCrusader F (V f K s j) (O f K s j) := by
  have hmem : ∀ p, p ∈ F ↔ p ∈ s.byz := fun p => by rw [← hF]; rfl
  constructor
  · intro w hw d hd
    rw [hmem] at hw hd
    have hrecv : recvInit w (V f K s j w) (H f K s (2 * j + 2) w) j d = some (d, j, V f K s j d) := by
      unfold recvInit
      split_ifs with hdw
      · subst hdw; rfl
      · rw [inboxAt_init hrel hj hd hdw (by omega)]; rfl
    have hnc : ¬ Conflict (H f K s (2 * j + 2) w) j d (V f K s j d) := by
      rintro ⟨u, σ, hσ, h1, h2, h3⟩
      obtain ⟨m, hm, hmσ⟩ := Option.bind_eq_some_iff.1 hσ
      have := good_hist hauth _ w hw σ
        (mem_histTokens_of_inboxAt (by simp) hm (mem_tokens_of_echoTok hmσ))
      have := this (by rw [h1]; exact hd)
      rw [h1, h2] at this
      exact h3 this
    simp [O, cbOut, hrecv, hnc]
  · intro u hu w hw d a b hua hwb
    rw [hmem] at hu hw
    by_cases huw : u = w
    · subst huw; rw [hua] at hwb; exact Option.some_injective _ hwb
    simp only [O, cbOut] at hua hwb
    obtain ⟨σ, hσ, hσa⟩ := Option.bind_eq_some_iff.1 hua
    obtain ⟨σ', hσ', hσb⟩ := Option.bind_eq_some_iff.1 hwb
    split_ifs at hσa with hc
    split_ifs at hσb with hc'
    cases hσa; cases hσb
    by_contra hab
    refine hc'.2.2 ⟨u, σ, ?_, hc.1, hc.2.1, hab⟩
    rw [inboxAt_echo hrel hj hu huw (by omega)]
    simpa [Msg.echoTok] using hσ

/-! ### Decisions -/

theorem decides_V (p : P) : Decides net (alg f K) s p (V f K s K p) := by
  refine ⟨2 * K, ?_, fun r hr => ?_⟩
  · simp only [status, alg, length_hist, le_refl, ↓reduceIte]
    exact congrArg some (val_hist le_rfl p)
  · simp only [status, alg, length_hist]
    simp only [show ¬ 2 * K ≤ r by omega, ↓reduceIte]

theorem decides_iff (p : P) (o : ℝ) : Decides net (alg f K) s p o ↔ o = V f K s K p :=
  ⟨fun h => h.unique _ _ (decides_V p), fun h => h ▸ decides_V p⟩

theorem terminatesBy : TerminatesBy net (alg f K) s (2 * K) :=
  fun p _ => ⟨2 * K, le_rfl, val f p (s.input p) (H f K s (2 * K) p) K, by
    simp only [status, alg, length_hist, le_refl, ↓reduceIte]; rfl⟩

/-! ### Approximate agreement -/

/-- **Definition 1** (with the resilience given by the adversary structure): if the honest inputs
have range at most `ℓ`, then every honest node decides (termination), every honest decision lies
between two honest inputs (validity) and any two honest decisions are at most `ε` apart
(`ε`-consistency). -/
def AASpec (ℓ ε : ℝ) : Spec P ℝ ℝ := fun inp Hs dec =>
  (∀ p ∈ Hs, ∀ q ∈ Hs, inp p - inp q ≤ ℓ) → Problem.ApproxAgreement ε inp Hs dec

/-- `A` is an `(ℓ, ε, t)`-secure protocol for approximate agreement running in `T` rounds: it is
unforging and solves `AASpec ℓ ε` against every unforgeability-respecting adversary corrupting at
most `t` nodes, and all honest nodes decide within `T` rounds. -/
def Secure (t : ℕ) (ℓ ε : ℝ) (A : Protocol P ℝ (Msg P) ℝ) (T : ℕ) : Prop :=
  A.Unforging auth ∧ SolvesAuth net A auth (atMost t) (AASpec ℓ ε) ∧
    ∀ s : Scenario P ℝ (Msg P), s.byz ∈ atMost t → s.Reliable → s.AuthValid net A auth →
      TerminatesBy net A s T

/-- Range contraction over the iterations: by Theorem 9 (`apa_step`) each iteration keeps the
honest values in `[a, b]` and halves their spread. -/
theorem iterate_range (hrel : s.Reliable) (hauth : s.AuthValid net (alg f K) auth)
    (hf : s.byz.ncard ≤ f) (hn : 2 * f < Fintype.card P) {a b : ℝ} (hab : a ≤ b)
    (hin : ∀ p, p ∉ s.byz → s.input p ∈ Set.Icc a b) :
    (∀ p, p ∉ s.byz → V f K s K p ∈ Set.Icc a b) ∧
      ∀ p, p ∉ s.byz → ∀ q, q ∉ s.byz → |V f K s K p - V f K s K q| ≤ (1 / 2) ^ K * (b - a) := by
  set F : Finset P := s.byz.toFinset with hFdef
  have hF : (F : Set P) = s.byz := by simp [F]
  have hFc : F.card ≤ f := by
    rw [← Set.ncard_coe_finset, hF]; exact hf
  have hmem : ∀ p, p ∈ F ↔ p ∈ s.byz := fun p => by rw [← hF]; rfl
  have key := Cslib.ApproxConsensus.mem_Icc_and_abs_sub_le_pow_mul_of_step
    (H := fun t => {p | t ≤ K ∧ p ∉ s.byz}) (x := fun t p => V f K s t p) (c := 1 / 2)
    (by norm_num) hab (fun p hp => hin p hp.2) ?_ K
  · exact ⟨fun p hp => key.1 p ⟨le_rfl, hp⟩, fun p hp q hq => key.2 p ⟨le_rfl, hp⟩ q ⟨le_rfl, hq⟩⟩
  intro t a' b' _ hval
  by_cases ht : t + 1 ≤ K
  · have hcr := cb_isCrusader hrel hauth hF (show t < K by omega)
    obtain ⟨h1, h2⟩ := apa_step hFc hn hcr (a := a') (b := b')
      (fun p hp => hval p ⟨by omega, (hmem p).not.1 hp⟩)
    refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
    · simp only [V_succ]; exact h1 p ((hmem p).not.2 hp.2)
    · simp only [V_succ]
      have := h2 p ((hmem p).not.2 hp.2) q ((hmem q).not.2 hq.2); linarith
  · exact ⟨fun p hp => absurd hp.1 ht, fun p hp => absurd hp.1 ht⟩

/-- `K` iterations of APA: an `(ℓ, ℓ/2^K, f)`-secure protocol running in `2K` rounds, for every
`f` with `2f < n`. -/
theorem alg_secure (hn : 2 * f < Fintype.card P) (K : ℕ) (ℓ : ℝ) :
    Secure (P := P) f ℓ ((1 / 2) ^ K * ℓ) (alg f K) (2 * K) := by
  refine ⟨alg_unforging, fun s hZ hrel hauth hℓ => ?_, fun s _ _ _ => terminatesBy⟩
  have hf : s.byz.ncard ≤ f := hZ
  -- the honest parties form a nonempty finite set
  have hne : (Finset.univ.filter (· ∉ s.byz)).Nonempty := by
    by_contra hall
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hall
    have : s.byz = Set.univ := Set.eq_univ_of_forall fun p => by
      simpa using hall (Finset.mem_univ p)
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card] at hf; omega
  obtain ⟨pmin, hpmin, hmin⟩ := Finset.exists_min_image _ s.input hne
  obtain ⟨pmax, hpmax, hmax⟩ := Finset.exists_max_image _ s.input hne
  have hpmin' : pmin ∉ s.byz := (Finset.mem_filter.1 hpmin).2
  have hpmax' : pmax ∉ s.byz := (Finset.mem_filter.1 hpmax).2
  have hin : ∀ p, p ∉ s.byz → s.input p ∈ Set.Icc (s.input pmin) (s.input pmax) := fun p hp =>
    ⟨hmin p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩),
      hmax p (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)⟩
  obtain ⟨h1, h2⟩ := iterate_range hrel hauth hf hn (hin pmin hpmin').2 hin
  have hℓ' : s.input pmax - s.input pmin ≤ ℓ := hℓ pmax hpmax' pmin hpmin'
  refine ⟨fun p _ => ⟨_, decides_V p⟩, fun p hp v hv => ?_, fun p hp q hq v w hv hw => ?_⟩
  · rw [decides_iff] at hv; subst hv
    exact ⟨⟨pmin, hpmin', (h1 p hp).1⟩, pmax, hpmax', (h1 p hp).2⟩
  · rw [decides_iff] at hv hw; subst hv hw
    exact (h2 p hp q hq).trans (mul_le_mul_of_nonneg_left hℓ' (by positivity))

/-- `⌈n/2⌉ - 1` (as `(n + 1)/2 - 1` in `ℕ`) satisfies `2f < n` for `n ≥ 1`. -/
theorem two_mul_ceil_half_sub_one_lt [Nonempty P] :
    2 * ((Fintype.card P + 1) / 2 - 1) < Fintype.card P := by
  have := Fintype.card_pos (α := P); omega

/-- **Theorem 9.** Algorithm APA (one iteration of `alg`, i.e. two rounds: the two rounds of CB)
is an `(ℓ, ℓ/2, ⌈n/2⌉ - 1)`-secure two-round protocol for approximate agreement, for every `ℓ`. -/
theorem theorem_9 [Nonempty P] (ℓ : ℝ) :
    Secure (P := P) ((Fintype.card P + 1) / 2 - 1) ℓ (ℓ / 2) (alg ((Fintype.card P + 1) / 2 - 1) 1) 2 := by
  have := alg_secure (P := P) two_mul_ceil_half_sub_one_lt 1 ℓ
  rwa [pow_one, one_div_mul_eq_div] at this

/-- **Corollary 2.** For `ε > 0`, `⌈log₂(ℓ/ε)⌉` iterations of APA form an
`(ℓ, ε, ⌈n/2⌉ - 1)`-secure protocol for approximate agreement running in `2⌈log₂(ℓ/ε)⌉` rounds. -/
theorem corollary_2 [Nonempty P] (ℓ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Secure (P := P) ((Fintype.card P + 1) / 2 - 1) ℓ ε
      (alg ((Fintype.card P + 1) / 2 - 1) ⌈Real.logb 2 (ℓ / ε)⌉₊)
      (2 * ⌈Real.logb 2 (ℓ / ε)⌉₊) := by
  obtain ⟨hU, hS, hT⟩ := alg_secure (P := P) two_mul_ceil_half_sub_one_lt ⌈Real.logb 2 (ℓ / ε)⌉₊ ℓ
  refine ⟨hU, fun s hZ hrel hauth hℓ => ?_, hT⟩
  obtain ⟨h1, h2, h3⟩ := hS s hZ hrel hauth hℓ
  refine ⟨h1, h2, h3.mono ?_⟩
  have h := Real.le_pow_natCeil_logb_div_mul (b := 2) (by norm_num) ℓ hε
  set k := ⌈Real.logb 2 (ℓ / ε)⌉₊
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [one_div_pow, one_div_mul_eq_div, div_le_iff₀ hk]
  linarith

/-- Non-vacuity of the adversary hypotheses of `Secure`: for any Byzantine set `B` and inputs, the
scenario in which the corrupted nodes stay silent is reliable and respects unforgeability. -/
theorem exists_authValid (B : Set P) (x : P → ℝ) (f K : ℕ) :
    ∃ s : Scenario P ℝ (Msg P), s.byz = B ∧ s.input = x ∧ s.Reliable ∧
      s.AuthValid net (alg f K) auth :=
  ⟨{ byz := B, input := x, adv := fun _ _ _ => none }, rfl, rfl, fun _ _ _ h => h,
    fun _ _ _ _ _ _ _ hm => by simp at hm⟩

end Podc.ClockSyncSignatures

end
