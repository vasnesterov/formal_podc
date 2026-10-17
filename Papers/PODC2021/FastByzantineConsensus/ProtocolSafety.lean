import Papers.PODC2021.FastByzantineConsensus.ProtocolInvariants

/-!
# Safety (consistency) of the generalized fast Byzantine consensus protocol

Lemmas 3.1–3.5, A.1, A.2, Corollary A.3, Theorems 3.6 / A.4 of Kuznetsov–Tonkikh–Zhang
(PODC 2021, arXiv:2102.12825v3), for the transition system of `Protocol.lean`.

The proof works for any token set `E` satisfying the invariants `TokInv` (proved for reachable
states in `ProtocolInvariants.lean`):
* counting lemmas (quorum intersection);
* Lemmas A.1, A.2 and Corollary A.3 (uniqueness of decisions / commit certificates in a view);
* Lemmas 3.1–3.5: a correct process signs `CertAck(x, v)` only if `x` is *safe* in view `v`,
  i.e. no other value is decided in a view `< v`; proved by strong induction on `v`
  (`safe_of_certified`);
* Theorem A.4 (`consistency`).
-/

namespace FastByzantineConsensus.Protocol

open Finset Classical

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-! ### Counting -/

section Counting

omit [Fintype P] in
/-- If `X ⊆ S \ {ℓ}` with `ℓ ∈ B`, then at most `|B| - 1` members of `X` are in `B`. -/
theorem card_add_one_le_card_sdiff_add {X S B : Finset P} {ℓ : P} (hX : X ⊆ S.erase ℓ)
    (hℓ : ℓ ∈ B) : X.card + 1 ≤ (X \ B).card + B.card := by
  have h1 := card_sdiff_add_card_inter X B
  have h2 : X ∩ B ⊆ B.erase ℓ := fun c hc =>
    mem_erase.2 ⟨(mem_erase.1 (hX (mem_inter.1 hc).1)).1, (mem_inter.1 hc).2⟩
  have h3 := card_le_card h2
  rw [card_erase_of_mem hℓ] at h3
  have : 1 ≤ B.card := card_pos.2 ⟨ℓ, hℓ⟩
  omega

end Counting

omit [DecidableEq P] in
theorem mem_ackers {E : Set (Tok P V)} {c : P} {x : V} {u : ℕ} :
    c ∈ ackers E x u ↔ Tok.ack c x u ∈ E := by
  simp [ackers]

omit [DecidableEq P] in
theorem mem_committers {E : Set (Tok P V)} {c : P} {x : V} {u : ℕ} :
    c ∈ committers E x u ↔ Tok.commit c x u ∈ E := by
  simp [committers]

omit [DecidableEq P] in
theorem mem_certAckers {E : Set (Tok P V)} {c : P} {x : V} {u : ℕ} :
    c ∈ certAckers E x u ↔ Tok.certAck c x u ∈ E := by
  simp [certAckers]

/-- The resilience assumptions of the generalized protocol: at most `f` Byzantine processes,
`1 ≤ t ≤ f`, `n ≥ 3f + 2t − 1`. -/
structure Resilient (pr : Params P) (B : Finset P) : Prop where
  hB : B.card ≤ pr.f
  ht : 1 ≤ pr.t
  htf : pr.t ≤ pr.f
  hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P

variable {pr : Params P} {B : Finset P} {E : Set (Tok P V)}

omit [DecidableEq P] in
theorem Resilient.qc_ge (hR : Resilient pr B) : 2 * pr.f + pr.t ≤ pr.qc := by
  have := hR.hn; have := hR.ht; unfold Params.qc; omega

omit [DecidableEq P] in
theorem Resilient.two_qc (hR : Resilient pr B) : Fintype.card P + pr.f + 1 ≤ 2 * pr.qc := by
  have := hR.hn; unfold Params.qc; omega

omit [DecidableEq P] in
theorem Resilient.arith (hR : Resilient pr B) :
    B.card ≤ pr.f ∧ 1 ≤ pr.t ∧ pr.t ≤ pr.f ∧ 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P ∧
      2 * pr.f + pr.t ≤ pr.qc ∧ Fintype.card P + pr.f + 1 ≤ 2 * pr.qc :=
  ⟨hR.hB, hR.ht, hR.htf, hR.hn, hR.qc_ge, hR.two_qc⟩

/-- Put all arithmetic consequences of `Resilient` in the context (for `omega`). -/
local macro "resilient_facts" hR:term : tactic =>
  `(tactic| (obtain ⟨_, _, _, _, _, _⟩ := ($hR).arith))

/-! ### Lemmas A.1, A.2, Corollary A.3 -/

section Quorum

variable (hR : Resilient pr B) (hI : TokInv pr B E)
include hR hI

/-- If `y` is decided in view `u`, then every set `C` that is large enough (`|C| ≥ f + t + 1`
and `|C| + qc ≥ n + f + 1`, e.g. a set of `n − f` votes) contains a correct process that
acknowledged `(y, u)`. -/
theorem exists_correct_acker_of_decided {y : V} {u : ℕ} (h : DecidedIn pr E y u) (C : Finset P)
    (hC1 : pr.f + pr.t + 1 ≤ C.card) (hC2 : Fintype.card P + pr.f + 1 ≤ C.card + pr.qc) :
    ∃ c ∈ C, c ∉ B ∧ Tok.ack c y u ∈ E := by
  resilient_facts hR
  rcases h with h | h
  · obtain ⟨c, hc, hcC, hcB⟩ :=
      exists_mem_inter_notMem_of_card_le (s := ackers E y u) (t := C) hR.hB (by omega)
    exact ⟨c, hcC, hcB, mem_ackers.1 hc⟩
  · obtain ⟨c₀, hc₀, hc₀B⟩ := exists_mem_notMem_of_card_lt_card (t := committers E y u) (s := B)
      (by omega)
    have hcc := hI.commit_valid c₀ hc₀B y u (mem_committers.1 hc₀)
    rw [hasCC_iff] at hcc
    obtain ⟨c, hc, hcC, hcB⟩ :=
      exists_mem_inter_notMem_of_card_le (s := ackers E y u) (t := C) hR.hB (by omega)
    exact ⟨c, hcC, hcB, mem_ackers.1 hc⟩

/-- The ack set of a decided value is large. -/
theorem card_ackers_of_decided {y : V} {u : ℕ} (h : DecidedIn pr E y u) :
    pr.f + pr.t + 1 ≤ (ackers E y u).card ∧
      Fintype.card P + pr.f + 1 ≤ (ackers E y u).card + pr.qc := by
  resilient_facts hR
  rcases h with h | h
  · constructor <;> omega
  · obtain ⟨c₀, hc₀, hc₀B⟩ := exists_mem_notMem_of_card_lt_card (t := committers E y u) (s := B)
      (by have := hR.hB; omega)
    have hcc := hI.commit_valid c₀ hc₀B y u (mem_committers.1 hc₀)
    rw [hasCC_iff] at hcc
    constructor <;> omega

/-- **Lemma A.1 of [KTZ21].** A value with a commit certificate (or a decided value) in view `u`
was validly proposed in view `u`: it has the leader's proposal signature and, unless `u` is the
first view, a progress certificate. -/
theorem certified_of_hasCC {x : V} {u : ℕ} (h : HasCC pr E x u) :
    Tok.propose (pr.leader u) x u ∈ E ∧ (u = 0 ∨ Certified pr E x u) := by
  resilient_facts hR
  obtain ⟨c, hcB, hc⟩ := h.exists_correct_signer hR.hB (by omega)
  exact hI.ack_valid c hcB x u hc

/-- Lemma A.1 for decided values. -/
theorem certified_of_decided {x : V} {u : ℕ} (h : DecidedIn pr E x u) :
    Tok.propose (pr.leader u) x u ∈ E ∧ (u = 0 ∨ Certified pr E x u) := by
  resilient_facts hR
  obtain ⟨c, -, hcB, hc⟩ := exists_correct_acker_of_decided hR hI h univ
    (by rw [card_univ]; have := hR.hn; have := hR.ht; have := hR.htf; omega)
    (by rw [card_univ]; omega)
  exact hI.ack_valid c hcB x u hc

/-- **Lemma A.2 of [KTZ21].** A commit certificate for `(x, u)` and a decision of `y` in the same
view `u` agree: `x = y`. -/
theorem hasCC_decided_eq {x y : V} {u : ℕ} (hx : HasCC pr E x u) (hy : DecidedIn pr E y u) :
    x = y := by
  resilient_facts hR
  rw [hasCC_iff] at hx
  obtain ⟨c, hc, hcB, hcy⟩ := exists_correct_acker_of_decided hR hI hy (ackers E x u)
    (by have := hR.ht; omega) (by omega)
  exact hI.ack_uniq c hcB x y u (mem_ackers.1 hc) hcy

/-- Two commit certificates in the same view are for the same value. -/
theorem hasCC_eq {x y : V} {u : ℕ} (hx : HasCC pr E x u) (hy : HasCC pr E y u) : x = y := by
  have h2 := hR.two_qc
  obtain ⟨c, hcB, hcx, hcy⟩ := hx.common_correct_signer hy hR.hB (by omega)
  exact hI.ack_uniq c hcB x y u hcx hcy

/-- **Corollary A.3 of [KTZ21].** No two different values are decided in the same view. -/
theorem decidedIn_unique {x y : V} {u : ℕ} (hx : DecidedIn pr E x u) (hy : DecidedIn pr E y u) :
    x = y := by
  obtain ⟨h1, h2⟩ := card_ackers_of_decided hR hI hx
  obtain ⟨c, hc, hcB, hcy⟩ := exists_correct_acker_of_decided hR hI hy (ackers E x u) h1 h2
  exact hI.ack_uniq c hcB x y u (mem_ackers.1 hc) hcy

end Quorum

/-! ### Lemmas 3.1–3.5: certified values are safe -/

/-- `SafeBelow pr E v`: every value with a progress certificate in a view `w < v` is *safe* in
`w`, i.e. no other value is decided in a view `< w`. (Induction hypothesis of Lemmas 3.3–3.5.) -/
def SafeBelow (pr : Params P) (E : Set (Tok P V)) (v : ℕ) : Prop :=
  ∀ w < v, ∀ z, Certified pr E z w → ∀ u < w, ∀ y, DecidedIn pr E y u → y = z

section Selection

variable {v : ℕ} {S : Finset P} {bal cc : P → Option (V × ℕ)}

omit [DecidableEq P] in
theorem ValidVotes.ballot (hS : ValidVotes pr E v S bal cc) {s : P} (hs : s ∈ S) {z : V} {w : ℕ}
    (h : bal s = some (z, w)) :
    w < v ∧ Tok.propose (pr.leader w) z w ∈ E ∧ (w = 0 ∨ Certified pr E z w) := by
  have := (hS.2 s hs).2.1
  rw [h] at this
  exact this

omit [DecidableEq P] in
theorem ValidVotes.commitCert (hS : ValidVotes pr E v S bal cc) {s : P} (hs : s ∈ S) {z : V}
    {w : ℕ} (h : cc s = some (z, w)) : w < v ∧ HasCC pr E z w := by
  have := (hS.2 s hs).2.2
  rw [h] at this
  exact this

variable (hR : Resilient pr B) (hI : TokInv pr B E)
include hR hI

/-- Core of Lemmas 3.1 and 3.2: if `y` is decided in a view `u < v`, a valid vote set for view
`v` contains a correct voter that acknowledged `(y, u)`; its vote reports a proposal `(y', u')`
with `u ≤ u'` (and `y' = y` if `u' = u`). -/
theorem exists_correct_voter_of_decided (hS : ValidVotes pr E v S bal cc) {y : V} {u : ℕ}
    (hy : DecidedIn pr E y u) (huv : u < v) :
    ∃ c ∈ S, c ∉ B ∧ ∃ y' u', bal c = some (y', u') ∧ u ≤ u' ∧ (u' = u → y' = y) := by
  resilient_facts hR
  have := hS.1
  obtain ⟨c, hcS, hcB, hcack⟩ := exists_correct_acker_of_decided hR hI hy S (by omega) (by omega)
  exact ⟨c, hcS, hcB, hI.vote_ack c hcB v (bal c) (cc c) y u (hS.2 c hcS).1 hcack huv⟩

/-- **Lemma 3.1 of [KTZ21].** If some value is decided in a view `u < v`, then a valid vote set
for view `v` does not consist of `nil` votes only. -/
theorem not_all_nil_of_decided (hS : ValidVotes pr E v S bal cc) {y : V} {u : ℕ}
    (hy : DecidedIn pr E y u) (huv : u < v) : ¬ ∀ s ∈ S, bal s = none := by
  intro h
  obtain ⟨c, hcS, -, y', u', hbc, -⟩ := exists_correct_voter_of_decided hR hI hS hy huv
  rw [h c hcS] at hbc
  cases hbc

/-- **Lemma 3.2 of [KTZ21].** If `y` is decided in a view `u < v` and `w` is the highest view of
a vote in a valid vote set for view `v`, then `u ≤ w`. -/
theorem decided_view_le (hS : ValidVotes pr E v S bal cc) {y : V} {u w : ℕ}
    (hy : DecidedIn pr E y u) (huv : u < v)
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w) : u ≤ w := by
  obtain ⟨c, hcS, -, y', u', hbc, huu', -⟩ := exists_correct_voter_of_decided hR hI hS hy huv
  exact huu'.trans (hmax c hcS y' u' hbc)

/-- **Lemma 3.3 of [KTZ21].** If a single value `x` has votes in the highest view `w` of a valid
vote set for view `v` (and certified values below `v` are safe), then `x` is safe in `v`. -/
theorem safe_of_single (hS : ValidVotes pr E v S bal cc) (IH : SafeBelow pr E v) {w : ℕ} {x : V}
    (hw : ∃ s ∈ S, ∃ z, bal s = some (z, w))
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w)
    (hsingle : ∀ s ∈ S, ∀ z, bal s = some (z, w) → z = x) {u : ℕ} (huv : u < v) {y : V}
    (hy : DecidedIn pr E y u) : y = x := by
  obtain ⟨c, hcS, -, y', u', hbc, huu', hyy'⟩ := exists_correct_voter_of_decided hR hI hS hy huv
  obtain ⟨s0, hs0, z0, hb0⟩ := hw
  have hu'w := hmax c hcS y' u' hbc
  rcases lt_or_eq_of_le (huu'.trans hu'w) with huw | huw
  · obtain ⟨hwv, -, hzc⟩ := hS.ballot hs0 hb0
    rw [IH w hwv z0 (hzc.resolve_left (by omega)) u huw y hy]
    exact hsingle s0 hs0 z0 hb0
  · subst huw
    obtain rfl : u' = u := le_antisymm hu'w huu'
    rw [hyy' rfl] at hbc
    exact hsingle c hcS y hbc

omit hR in
/-- If two different values have valid votes in view `w`, the leader of `w` equivocated, so it is
Byzantine. -/
theorem leader_mem_of_equivocation (hS : ValidVotes pr E v S bal cc) {s₁ s₂ : P} {y₁ y₂ : V}
    {w : ℕ} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S) (hb₁ : bal s₁ = some (y₁, w))
    (hb₂ : bal s₂ = some (y₂, w)) (hne : y₁ ≠ y₂) : pr.leader w ∈ B := by
  by_contra hl
  exact hne (hI.propose_uniq _ hl y₁ y₂ w (hS.ballot hs₁ hb₁).2.1 (hS.ballot hs₂ hb₂).2.1)

/-- In the equivocation case (two different values with votes in the highest view `w`), a value
decided in a view `u < v` is decided in view `w` (by Lemma 3.2 and the induction hypothesis). -/
theorem decided_view_eq_of_equivocation (hS : ValidVotes pr E v S bal cc)
    (IH : SafeBelow pr E v) {s₁ s₂ : P} {y₁ y₂ : V} {w : ℕ} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S)
    (hb₁ : bal s₁ = some (y₁, w)) (hb₂ : bal s₂ = some (y₂, w)) (hne : y₁ ≠ y₂)
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w) {u : ℕ} (huv : u < v) {y : V}
    (hy : DecidedIn pr E y u) : u = w := by
  have huw := decided_view_le hR hI hS hy huv hmax
  by_contra hne'
  have hlt : u < w := lt_of_le_of_ne huw hne'
  obtain ⟨hwv, -, hc₁⟩ := hS.ballot hs₁ hb₁
  obtain ⟨-, -, hc₂⟩ := hS.ballot hs₂ hb₂
  exact hne ((IH w hwv y₁ (hc₁.resolve_left (by omega)) u hlt y hy).symm.trans
    (IH w hwv y₂ (hc₂.resolve_left (by omega)) u hlt y hy))

/-- A slow-path decision in the highest view `w` (with a Byzantine leader of `w`) leaves a commit
certificate for view `w` in the vote of some process of `S \ {leader w}`. -/
theorem exists_cc_of_slow (hS : ValidVotes pr E v S bal cc) {w : ℕ} {y : V}
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w) (hlB : pr.leader w ∈ B)
    (hwv : w < v) (hcom : pr.qc ≤ (committers E y w).card) :
    ∃ s ∈ S.erase (pr.leader w), ∃ z, cc s = some (z, w) := by
  resilient_facts hR
  have := hS.1
  obtain ⟨c₂, hc₂com, hc₂S, hc₂B⟩ :=
    exists_mem_inter_notMem_of_card_le (s := committers E y w) (t := S) hR.hB (by omega)
  obtain ⟨z, u'', hcc2, hwu'', hzcc⟩ := hI.vote_commit c₂ hc₂B v (bal c₂) (cc c₂) y w
    (hS.2 c₂ hc₂S).1 (mem_committers.1 hc₂com) hwv
  have hc₂S' : c₂ ∈ S.erase (pr.leader w) := mem_erase.2 ⟨fun h => hc₂B (h ▸ hlB), hc₂S⟩
  rcases lt_or_eq_of_le hwu'' with hlt | heq
  · exfalso
    have hu''v := (hS.commitCert hc₂S hcc2).1
    rw [hasCC_iff] at hzcc
    obtain ⟨c₃, hc₃ack, hc₃S, hc₃B⟩ :=
      exists_mem_inter_notMem_of_card_le (s := ackers E z u'') (t := S) hR.hB (by omega)
    obtain ⟨z3, u3, hb3, hu3, -⟩ := hI.vote_ack c₃ hc₃B v (bal c₃) (cc c₃) z u''
      (hS.2 c₃ hc₃S).1 (mem_ackers.1 hc₃ack) hu''v
    have := hmax c₃ hc₃S z3 u3 hb3
    omega
  · exact ⟨c₂, hc₂S', z, heq ▸ hcc2⟩

/-- Selection case (1) of the equivocation branch: a value with a commit certificate for the
highest view `w` (by Lemma A.2). -/
theorem safe_of_cc (hS : ValidVotes pr E v S bal cc) {s : P} (hs : s ∈ S) {x y : V} {w : ℕ}
    (hcc : cc s = some (x, w)) (hy : DecidedIn pr E y w) : y = x :=
  (hasCC_decided_eq hR hI (hS.commitCert hs hcc).2 hy).symm

/-- **Lemma 3.4 of [KTZ21].** Selection case (2) of the equivocation branch: no commit certificate
for the highest view `w` in `S' = S \ {leader w}` and at least `f + t` votes `(x, w)` in `S'`;
then `x` is the only value that can be decided in view `w`. -/
theorem safe_of_many_votes (hS : ValidVotes pr E v S bal cc) {w : ℕ} {x y : V}
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w) (hlB : pr.leader w ∈ B)
    (hwv : w < v) (hnocc : ∀ s ∈ S.erase (pr.leader w), ∀ z, cc s ≠ some (z, w))
    (hbig : pr.f + pr.t ≤ ((S.erase (pr.leader w)).filter fun s => bal s = some (x, w)).card)
    (hy : DecidedIn pr E y w) : y = x := by
  resilient_facts hR
  rcases hy with hfast | hslow
  · set F := (S.erase (pr.leader w)).filter fun s => bal s = some (x, w) with hF
    have h1 := card_add_card_le_card_inter_add_card_univ F (ackers E y w)
    have h2 := card_add_one_le_card_sdiff_add (X := F ∩ ackers E y w) (S := S)
      (ℓ := pr.leader w) (fun s hs => (mem_filter.1 (mem_inter.1 hs).1).1) hlB
    obtain ⟨c, hc⟩ := card_pos.1 (by omega : 0 < ((F ∩ ackers E y w) \ B).card)
    obtain ⟨hcFA, hcB⟩ := mem_sdiff.1 hc
    obtain ⟨hcF, hcA⟩ := mem_inter.1 hcFA
    obtain ⟨hcS', hbc⟩ := mem_filter.1 hcF
    have hcS := mem_of_mem_erase hcS'
    have hxack := hI.vote_bal c hcB v (bal c) (cc c) x w (hS.2 c hcS).1 hbc
    exact (hI.ack_uniq c hcB x y w hxack (mem_ackers.1 hcA)).symm
  · obtain ⟨s, hs, z, hz⟩ := exists_cc_of_slow hR hI hS hmax hlB hwv hslow
    exact absurd hz (hnocc s hs z)

/-- **Lemma 3.5 of [KTZ21].** Selection case (3) of the equivocation branch: no commit
certificate for the highest view `w` in `S' = S \ {leader w}` and fewer than `f + t` votes
`(y, w)` in `S'` for every `y`; then no value is decided in view `w`. -/
theorem not_decided_of_few_votes (hS : ValidVotes pr E v S bal cc) {w : ℕ} {y : V}
    (hmax : ∀ s ∈ S, ∀ z u', bal s = some (z, u') → u' ≤ w) (hlB : pr.leader w ∈ B)
    (hwv : w < v) (hS' : Fintype.card P - pr.f ≤ (S.erase (pr.leader w)).card)
    (hnocc : ∀ s ∈ S.erase (pr.leader w), ∀ z, cc s ≠ some (z, w))
    (hsmall : ((S.erase (pr.leader w)).filter fun s => bal s = some (y, w)).card < pr.f + pr.t)
    (hy : DecidedIn pr E y w) : False := by
  resilient_facts hR
  rcases hy with hfast | hslow
  · have h1 := card_add_card_le_card_inter_add_card_univ (ackers E y w) (S.erase (pr.leader w))
    set X := ackers E y w ∩ S.erase (pr.leader w) with hX
    have h2 := card_add_one_le_card_sdiff_add (X := X) (S := S) (ℓ := pr.leader w)
      (fun s hs => (mem_inter.1 hs).2) hlB
    have hsub : X \ B ⊆ (S.erase (pr.leader w)).filter fun s => bal s = some (y, w) := by
      intro c hc
      obtain ⟨hcX, hcB⟩ := mem_sdiff.1 hc
      obtain ⟨hcA, hcS'⟩ := mem_inter.1 hcX
      have hcS := mem_of_mem_erase hcS'
      obtain ⟨y', u', hbc, hwu', hyy'⟩ := hI.vote_ack c hcB v (bal c) (cc c) y w
        (hS.2 c hcS).1 (mem_ackers.1 hcA) hwv
      have hu'w := hmax c hcS y' u' hbc
      obtain rfl : u' = w := le_antisymm hu'w hwu'
      rw [hyy' rfl] at hbc
      exact mem_filter.2 ⟨hcS', hbc⟩
    have h3 := card_le_card hsub
    omega
  · obtain ⟨s, hs, z, hz⟩ := exists_cc_of_slow hR hI hS hmax hlB hwv hslow
    exact hnocc s hs z hz

/-- **Safety of the selection (Lemmas 3.1–3.5 of [KTZ21]).** If certified values below `v` are
safe and the selection algorithm may output `x` on a valid vote set for view `v`, then no value
other than `x` is decided in a view `< v`. -/
theorem safe_of_selects (hS : ValidVotes pr E v S bal cc) (IH : SafeBelow pr E v) {x : V}
    (hsel : Selects pr v S bal cc x) {u : ℕ} (huv : u < v) {y : V} (hy : DecidedIn pr E y u) :
    y = x := by
  rcases hsel with hnil | ⟨w, hw, hmax, hcase⟩
  · exact absurd hnil (not_all_nil_of_decided hR hI hS hy huv)
  rcases hcase with hsingle | ⟨⟨s₁, hs₁, s₂, hs₂, y₁, y₂, hb₁, hb₂, hne⟩, hS', hcase⟩
  · exact safe_of_single hR hI hS IH hw hmax hsingle huv hy
  have hlB := leader_mem_of_equivocation hI hS hs₁ hs₂ hb₁ hb₂ hne
  obtain rfl := decided_view_eq_of_equivocation hR hI hS IH hs₁ hs₂ hb₁ hb₂ hne hmax huv hy
  rcases hcase with ⟨s, hs, hccs⟩ | ⟨hnocc, hbig⟩ | ⟨hnocc, hsmall⟩
  · exact safe_of_cc hR hI hS (mem_of_mem_erase hs) hccs hy
  · exact safe_of_many_votes hR hI hS hmax hlB huv hnocc hbig hy
  · exact (not_decided_of_few_votes hR hI hS hmax hlB huv hS' hnocc (hsmall y) hy).elim

end Selection

section Main

variable (hR : Resilient pr B) (hI : TokInv pr B E)
include hR hI

/-- **Main lemma (Lemmas 3.3–3.5 by induction on the view).** A value with a progress certificate
for view `v` is safe in `v`: no other value is decided in a view `< v`. -/
theorem safe_of_certified (v : ℕ) : ∀ x, Certified pr E x v →
    ∀ u < v, ∀ y, DecidedIn pr E y u → y = x := by
  induction v using Nat.strong_induction_on with
  | _ v IH =>
  intro x hcert u huv y hy
  resilient_facts hR
  obtain ⟨q, hqB, hq⟩ := hcert.exists_correct_signer hR.hB (Nat.lt_succ_self _)
  obtain ⟨S, bal, cc, hS, hsel⟩ := hI.certAck_valid q hqB x v hq
  exact safe_of_selects hR hI hS (fun w hw => IH w hw) hsel huv hy

/-- Safety of decisions in different views: if `x` is decided in view `v` and `y` in a view
`v' < v`, then `x = y`. -/
theorem decided_eq_of_lt {x y : V} {v v' : ℕ} (hx : DecidedIn pr E x v)
    (hy : DecidedIn pr E y v') (h : v' < v) : x = y := by
  have hc := (certified_of_decided hR hI hx).2.resolve_left (by omega)
  exact (safe_of_certified hR hI v x hc v' h y hy).symm

end Main

/-- **Theorem A.4 (and Theorem 3.6 for `t = f`) of [KTZ21].** In every reachable state of the
generalized protocol with `n ≥ 3f + 2t − 1`, `1 ≤ t ≤ f` and at most `f` Byzantine processes, no
two different values are decided. -/
theorem consistency (pr : Params P) (B : Finset P) (inp : P → V) (hB : B.card ≤ pr.f)
    (ht : 1 ≤ pr.t) (htf : pr.t ≤ pr.f) (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P)
    {s : State P V} (hs : Reachable pr B inp s) {x y : V} (hx : Decided pr s.E x)
    (hy : Decided pr s.E y) : x = y := by
  have hI := (Inv.of_reachable hs).toTokInv
  have hR : Resilient pr B := ⟨hB, ht, htf, hn⟩
  obtain ⟨v, hv⟩ := hx
  obtain ⟨v', hv'⟩ := hy
  rcases lt_trichotomy v v' with h | rfl | h
  · exact (decided_eq_of_lt hR hI hv' hv h).symm
  · exact decidedIn_unique hR hI hv hv'
  · exact decided_eq_of_lt hR hI hv hv' h

end FastByzantineConsensus.Protocol

namespace FastByzantineConsensus.Protocol

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- **Theorem 3.6** (the `n ≥ 5f − 1` protocol of Section 3 is the case `t = f`; its executions
are the executions of this system in which correct processes never take `commit` steps, see
`differencies.md`). -/
theorem consistency_five_f (pr : Params P) (B : Finset P) (inp : P → V) (hB : B.card ≤ pr.f)
    (hf : 1 ≤ pr.f) (htf : pr.t = pr.f) (hn : 5 * pr.f - 1 ≤ Fintype.card P)
    {s : State P V} (hs : Reachable pr B inp s) {x y : V} (hx : Decided pr s.E x)
    (hy : Decided pr s.E y) : x = y :=
  consistency pr B inp hB (by omega) htf.le (by omega) hs hx hy

end FastByzantineConsensus.Protocol
