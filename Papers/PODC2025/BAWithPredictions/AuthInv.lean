import Papers.PODC2025.BAWithPredictions.AuthAlg

/-!
# Authenticated BA with classification — invariants and unforgeability

Invariants of executions of `AuthBA.alg` (Algorithm 7 with the `n` parallel instances of
Algorithm 6): monotonicity and size of the sets `X_p[s]`, validity of the relayed chains
(`out_inv`), the origin of the tokens a process sends (`send_tokens`), unforgeability of the
algorithm (`alg_unforging`), and the two token-origin facts used by the correctness proofs:
* `vote_sent`: an honest `p` only ever sends its vote token for `j` if `j` is among the first
  `2k+1` positions of `π(c_p)`;
* `link_sent`: a link token of `p` for `(s, v)` only occurs in chains for `(s, v)` that `p` sent.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.AuthBA

open Finset Cslib.Byzantine.PartialSync

variable {P V : Type*}

/-! ### Chains -/

theorem Chain.eta (ch : Chain P V) : (⟨ch.s, ch.x, ch.links⟩ : Chain P V) = ch := rfl

/-- Extending a valid round-`r` chain not signed by `p` by `p`'s link gives a valid round-`(r+1)`
chain. -/
theorem chainOK_extend {t r : ℕ} {p : P} {ch : Chain P V} (hok : ChainOK t r ch)
    (hp : p ∉ ch.signers) (hr : 1 ≤ r) {cc : Finset P} (hcc : t + 1 ≤ cc.card) :
    ChainOK t (r + 1) ⟨ch.s, ch.x, ch.links ++ [(p, cc)]⟩ := by
  obtain ⟨hl, hh, hn, hc⟩ := hok
  have hne : ch.signers ≠ [] := by
    intro h; have := congrArg List.length h; simp [Chain.signers, hl] at this; omega
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · simp only [Chain.signers, List.map_append, List.map_cons, List.map_nil] at hh ⊢
    rw [List.head?_append, hh]; rfl
  · simp only [Chain.signers, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨hn, List.nodup_singleton _, fun a ha b hb hab => hp ?_⟩
    rw [List.mem_singleton.mp hb] at hab
    exact hab ▸ ha
  · intro l hl'
    rcases List.mem_append.mp hl' with h | h
    · exact hc l h
    · rw [List.mem_singleton.mp h]; exact hcc

theorem mem_signers_of_head {t r : ℕ} {ch : Chain P V} (hok : ChainOK t r ch) :
    ch.s ∈ ch.signers := List.mem_of_mem_head? hok.2.1

theorem link_mem_tokens {ch : Chain P V} {j : P} (hj : j ∈ ch.signers) :
    Tok.link j ch.s ch.x ∈ ch.tokens := Or.inl ⟨j, hj, rfl⟩

theorem vote_mem_tokens {ch : Chain P V} {l : P × Finset P} (hl : l ∈ ch.links) {j : P}
    (hj : j ∈ l.2) : Tok.vote j l.1 ∈ ch.tokens := Or.inr ⟨l, hl, j, hj, rfl⟩

theorem link_mem_tokens_iff {ch : Chain P V} {j s : P} {v : V} :
    Tok.link j s v ∈ ch.tokens ↔ j ∈ ch.signers ∧ s = ch.s ∧ v = ch.x := by
  constructor
  · rintro (⟨j', hj', h⟩ | ⟨l, -, j', -, h⟩)
    · cases h; exact ⟨hj', rfl, rfl⟩
    · cases h
  · rintro ⟨hj, rfl, rfl⟩; exact link_mem_tokens hj

theorem vote_mem_tokens_iff {ch : Chain P V} {j i : P} :
    Tok.vote j i ∈ ch.tokens ↔ ∃ cc, (i, cc) ∈ ch.links ∧ j ∈ cc := by
  constructor
  · rintro (⟨j', hj', h⟩ | ⟨l, hl, j', hj', h⟩)
    · cases h
    · cases h; exact ⟨l.2, hl, hj'⟩
  · rintro ⟨cc, hl, hj⟩; exact vote_mem_tokens hl hj

/-! ### Relaying -/

section Relay

variable [Fintype P] [LinearOrder P] [LinearOrder V]

theorem relay_got {t r : ℕ} {p : P} {rcv : P → Option (Msg P V)} {s : P} {v : V}
    (h : v ∈ accSet t r p rcv s) : Got t r p rcv ⟨s, v, relayLinks t r p rcv s v⟩ := by
  obtain ⟨ch, hG, rfl, rfl⟩ := mem_accSet.mp h
  exact Classical.epsilon_spec (p := fun l => Got t r p rcv ⟨ch.s, ch.x, l⟩) ⟨ch.links, hG⟩

theorem mem_relayOut {t r : ℕ} {p : P} {rcv : P → Option (Msg P V)} {X X' : P → Finset V}
    {cc : Finset P} {ch : Chain P V} :
    ch ∈ relayOut t r p rcv X X' cc ↔
      ∃ s v, v ∈ X' s ∧ v ∉ X s ∧ ch = ⟨s, v, relayLinks t r p rcv s v ++ [(p, cc)]⟩ := by
  classical
  unfold relayOut
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_sdiff]
  constructor
  · rintro ⟨s, v, ⟨h1, h2⟩, rfl⟩; exact ⟨s, v, h1, h2, rfl⟩
  · rintro ⟨s, v, h1, h2, rfl⟩; exact ⟨s, v, ⟨h1, h2⟩, rfl⟩

end Relay

/-! ### Invariants -/

section Inv

variable [Fintype P] [LinearOrder P] [LinearOrder V] {k t : ℕ} {F : Finset P}
  {inp : P → V × (P → Bool)} (E : RoundRun (alg (P := P) (V := V) k t) F inp)

theorem X_mono_succ (r : ℕ) (p s : P) : (E.s r p).X s ⊆ (E.s (r + 1) p).X s := by
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [X_zero]; exact empty_subset _
  rcases Nat.lt_or_ge (k + 1) r with h | h
  · rw [X_late E (r := r) (by omega), X_late E (r := r + 1) (by omega)]
  · rw [X_succ_bb E h0 h]; exact subset_step _ _

theorem X_mono {r r' : ℕ} (h : r ≤ r') (p s : P) : (E.s r p).X s ⊆ (E.s r' p).X s := by
  induction r', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ r' _ ih => exact ih.trans (X_mono_succ E r' p s)

theorem X_card (r : ℕ) (p s : P) : ((E.s r p).X s).card ≤ 2 := by
  induction r with
  | zero => rw [X_zero]; simp
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | h0
    · rw [X_one]; split_ifs <;> simp
    rcases Nat.lt_or_ge (k + 1) r with h | h
    · rw [X_late E (by omega)]; rw [X_late E (by omega)] at ih; exact ih
    · rw [X_succ_bb E h0 h]; exact card_step _ _ ih

/-- The values in `X_p[s]`: the own input (if `p = s` has a certificate), or values of valid
chains received in rounds `1 … k+1`. -/
theorem X_cases {r : ℕ} {p s : P} {v : V} (hv : v ∈ (E.s r p).X s) :
    (s = p ∧ v = (inp p).1 ∧ (cert E p).isSome) ∨
      ∃ r', 1 ≤ r' ∧ r' < r ∧ r' ≤ k + 1 ∧ ∃ ch, Got t r' p (E.rcv r' p) ch ∧ ch.s = s ∧ ch.x = v := by
  induction r with
  | zero => rw [X_zero] at hv; simp at hv
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | h0
    · rw [X_one] at hv
      split_ifs at hv with h
      · exact Or.inl ⟨h.2, mem_singleton.mp hv, h.1⟩
      · simp at hv
    rcases Nat.lt_or_ge (k + 1) r with h | h
    · rw [X_late E (by omega)] at hv; rw [X_late E (by omega)] at ih
      rcases ih hv with h' | ⟨r', h1, h2, h3, h4⟩
      · exact Or.inl h'
      · exact Or.inr ⟨r', h1, by omega, h3, h4⟩
    · rw [X_succ_bb E h0 h] at hv
      rcases mem_union.mp (step_subset _ _ hv) with hv | hv
      · rcases ih hv with h' | ⟨r', h1, h2, h3, h4⟩
        · exact Or.inl h'
        · exact Or.inr ⟨r', h1, by omega, h3, h4⟩
      · exact Or.inr ⟨r, h0, by omega, h, mem_accSet.mp hv⟩

/-- A value newly added to `X_p[s]` at the end of round `r` comes from a valid round-`r` chain,
and is relayed in round `r + 1` if `p` has a certificate. -/
theorem X_new {r : ℕ} (h1 : 1 ≤ r) {p s : P} {v : V} (hv : v ∈ (E.s (r + 1) p).X s)
    (hv' : v ∉ (E.s r p).X s) :
    r ≤ k + 1 ∧ v ∈ accSet t r p (E.rcv r p) s ∧
      ∀ cc, cert E p = some cc → ∃ ch ∈ (E.s (r + 1) p).out, ch.s = s ∧ ch.x = v := by
  have hr : r ≤ k + 1 := by
    by_contra h
    rw [X_late E (by omega)] at hv; rw [X_late E (by omega)] at hv'
    exact hv' hv
  refine ⟨hr, ?_, ?_⟩
  · rw [X_succ_bb E h1 hr] at hv
    rcases mem_union.mp (step_subset _ _ hv) with h | h
    · exact absurd h hv'
    · exact h
  · intro cc hcc
    rw [out_succ_bb E h1 hr, hcc]
    refine ⟨_, mem_relayOut.mpr ⟨s, v, ?_, hv', rfl⟩, rfl, rfl⟩
    rw [← X_succ_bb E h1 hr]; exact hv

/-- **Chains sent by a process**: valid for the round, for a value in `X_p[s]`, signed by `p`,
and `p` has a certificate. -/
theorem out_inv {r : ℕ} (hr : r ≤ k + 2) {p : P} {ch : Chain P V} (h : ch ∈ (E.s r p).out) :
    1 ≤ r ∧ ChainOK t r ch ∧ ch.x ∈ (E.s r p).X ch.s ∧ (cert E p).isSome ∧ p ∈ ch.signers := by
  rcases r with _ | r
  · rw [out_zero] at h; simp at h
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · rw [out_one] at h
    cases hc : cert E p with
    | none => rw [hc] at h; simp at h
    | some S =>
      rw [hc] at h
      rw [mem_singleton.mp h]
      refine ⟨le_rfl, ⟨rfl, rfl, List.nodup_singleton _, ?_⟩, ?_, rfl, ?_⟩
      · intro l hl; rw [List.mem_singleton.mp hl]; exact (cert_some E hc).2
      · rw [X_one, hc]; simp
      · simp [Chain.signers]
  · rw [out_succ_bb E h0 (by omega)] at h
    cases hc : cert E p with
    | none => rw [hc] at h; simp at h
    | some cc =>
      rw [hc] at h
      obtain ⟨s, v, hv, hv', rfl⟩ := mem_relayOut.mp h
      have hX := X_succ_bb E h0 (by omega) p s
      have hacc : v ∈ accSet t r p (E.rcv r p) s := by
        rcases mem_union.mp (step_subset _ _ hv) with h | h
        · exact absurd h hv'
        · exact h
      have hG := relay_got hacc
      obtain ⟨-, -, -, -, hok, hp⟩ := hG
      refine ⟨by omega, chainOK_extend hok hp h0 (cert_some E hc).2, ?_, rfl, ?_⟩
      · rw [hX]; exact hv
      · simp [Chain.signers]

theorem out_succ_late {r : ℕ} (h : k + 2 ≤ r) (p : P) : (E.s (r + 1) p).out = (E.s r p).out := by
  rw [out_late E h, out_late E (by omega)]

/-- Tokens of the chains a process sends are its own link tokens or tokens received in an earlier
round. -/
theorem out_tokens {r : ℕ} {p : P} {ch : Chain P V} (h : ch ∈ (E.s r p).out) {x : Tok P V}
    (hx : x ∈ ch.tokens) : (∃ s v, x = .link p s v) ∨
      ∃ r' < r, ∃ q m, E.rcv r' p q = some m ∧ x ∈ m.tokens := by
  induction r generalizing ch with
  | zero => rw [out_zero] at h; simp at h
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | h0
    · rw [out_one] at h
      cases hc : cert E p with
      | none => rw [hc] at h; simp at h
      | some S =>
        rw [hc] at h
        rw [mem_singleton.mp h] at hx
        obtain ⟨hSv, -⟩ := cert_some E hc
        rcases hx with ⟨j, hj, rfl⟩ | ⟨l, hl, j, hj, rfl⟩
        · simp only [Chain.signers, List.map_cons, List.map_nil, List.mem_singleton] at hj
          subst hj; exact Or.inl ⟨_, _, rfl⟩
        · rw [List.mem_singleton.mp hl] at hj ⊢
          rw [hSv] at hj
          have := (mem_filter.mp hj).2
          exact Or.inr ⟨0, by omega, j, _, this, rfl⟩
    rcases Nat.lt_or_ge (k + 1) r with hk | hk
    · rw [out_succ_late E (by omega)] at h
      obtain h' | ⟨r', hr', h'⟩ := ih h hx
      · exact Or.inl h'
      · exact Or.inr ⟨r', by omega, h'⟩
    · rw [out_succ_bb E h0 hk] at h
      cases hc : cert E p with
      | none => rw [hc] at h; simp at h
      | some cc =>
        rw [hc] at h
        obtain ⟨s, v, hv, hv', rfl⟩ := mem_relayOut.mp h
        have hacc : v ∈ accSet t r p (E.rcv r p) s := by
          rcases mem_union.mp (step_subset _ _ hv) with h | h
          · exact absurd h hv'
          · exact h
        obtain ⟨q, S', hq, hS', -, -⟩ := relay_got hacc
        have hrec : ∀ y ∈ (⟨s, v, relayLinks t r p (E.rcv r p) s v⟩ : Chain P V).tokens,
            ∃ r' < r + 1, ∃ q m, E.rcv r' p q = some m ∧ y ∈ m.tokens :=
          fun y hy => ⟨r, by omega, q, _, hq, _, hS', hy⟩
        rcases hx with ⟨j, hj, rfl⟩ | ⟨l, hl, j, hj, rfl⟩
        · simp only [Chain.signers, List.map_append, List.map_cons, List.map_nil,
            List.mem_append, List.mem_singleton] at hj
          rcases hj with hj | rfl
          · exact Or.inr (hrec _ (link_mem_tokens (ch := ⟨s, v, _⟩) hj))
          · exact Or.inl ⟨_, _, rfl⟩
        · rcases List.mem_append.mp hl with hl | hl
          · exact Or.inr (hrec _ (vote_mem_tokens (ch := ⟨s, v, _⟩) hl hj))
          · rw [List.mem_singleton.mp hl] at hj ⊢
            rw [(cert_some E hc).1] at hj
            exact Or.inr ⟨0, by omega, j, _, (mem_filter.mp hj).2, rfl⟩

/-- **Origin of the tokens a process sends.** -/
theorem send_tokens {r : ℕ} {p w : P} {m : Msg P V}
    (hm : (alg k t).send r p (E.s r p) w = some m) {x : Tok P V} (hx : x ∈ m.tokens) :
    (r = 0 ∧ x = .vote p w ∧ pos (inp p).2 w ≤ 2 * k + 1) ∨ (∃ s v, x = .link p s v) ∨
      ∃ r' < r, ∃ q m', E.rcv r' p q = some m' ∧ x ∈ m'.tokens := by
  change (if r = 0 then (if pos (E.s r p).c w ≤ 2 * k + 1 then some (.vote p w) else none)
    else if r ≤ k + 1 then (if (E.s r p).out.Nonempty then some (.chains (E.s r p).out) else none)
    else if r = k + 2 then (E.s r p).cc.map fun cc => .plur p (plurality (E.s r p)) cc
    else none) = some m at hm
  split_ifs at hm with h0 h1 h2 h3 h4
  · cases hm
    rw [c_eq] at h1
    exact Or.inl ⟨h0, hx, h1⟩
  · cases hm
    obtain ⟨ch, hch, hx⟩ := hx
    exact Or.inr (out_tokens E hch hx)
  · rw [cc_eq E (by omega)] at hm
    cases hc : cert E p with
    | none => rw [hc] at hm; simp at hm
    | some S =>
      rw [hc] at hm
      cases hm
      obtain ⟨j, hj, rfl⟩ := hx
      rw [(cert_some E hc).1] at hj
      exact Or.inr (Or.inr ⟨0, by omega, j, _, (mem_filter.mp hj).2, rfl⟩)

/-- **The algorithm is unforging.** -/
theorem alg_unforging (k t : ℕ) :
    (alg (P := P) (V := V) k t).Unforging auth := by
  intro F inp E r p q m hm x hx
  rcases send_tokens E hm hx with ⟨-, rfl, -⟩ | ⟨s, v, rfl⟩ | h
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr h

/-- Link tokens only occur in `chains` messages, in chains for the same instance and value. -/
theorem link_sent {r : ℕ} {p w : P} {m : Msg P V}
    (hm : (alg k t).send r p (E.s r p) w = some m) {j s : P} {v : V}
    (hx : Tok.link j s v ∈ m.tokens) :
    1 ≤ r ∧ r ≤ k + 1 ∧ ∃ ch ∈ (E.s r p).out, ch.s = s ∧ ch.x = v := by
  change (if r = 0 then (if pos (E.s r p).c w ≤ 2 * k + 1 then some (.vote p w) else none)
    else if r ≤ k + 1 then (if (E.s r p).out.Nonempty then some (.chains (E.s r p).out) else none)
    else if r = k + 2 then (E.s r p).cc.map fun cc => .plur p (plurality (E.s r p)) cc
    else none) = some m at hm
  split_ifs at hm with h0 h1 h2 h3 h4
  · cases hm; cases hx
  · cases hm
    obtain ⟨ch, hch, hx⟩ := hx
    obtain ⟨-, rfl, rfl⟩ := link_mem_tokens_iff.mp hx
    exact ⟨by omega, h2, ch, hch, rfl, rfl⟩
  · cases hc : (E.s r p).cc with
    | none => rw [hc] at hm; simp at hm
    | some S =>
      rw [hc] at hm; cases hm
      obtain ⟨j, -, h⟩ := hx
      cases h

end Inv

/-! ### Token origins in authenticated executions -/

section Origin

variable [Fintype P] [LinearOrder P] [LinearOrder V] {k t : ℕ} {F : Finset P}
  {inp : P → V × (P → Bool)} (E : RoundRun (alg (P := P) (V := V) k t) F inp)
  (hA : E.AuthValid auth)

include hA

/-- An honest process only sends its vote token for `j` if `j` is among the first `2k+1`
positions of its ordering `π(c_p)` (line 3 of Algorithm 7). -/
theorem vote_sent {r : ℕ} {p w : P} (hp : p ∉ F) {m : Msg P V}
    (hm : (alg k t).send r p (E.s r p) w = some m) {j : P} (hx : Tok.vote p j ∈ m.tokens) :
    pos (inp p).2 j ≤ 2 * k + 1 := by
  induction r using Nat.strong_induction_on generalizing w m with
  | _ r ih =>
    rcases send_tokens E hm hx with ⟨-, h, hpos⟩ | ⟨s, v, h⟩ | ⟨r', hr', q, m', hm', hx'⟩
    · cases h; exact hpos
    · cases h
    · obtain ⟨r'', hr'', w'', m'', hs, hx''⟩ :=
        E.tokens_origin_rcv (alg_unforging k t) hA hp hm' hx' hp
      exact ih r'' (by omega) hs hx''

/-- A vote token of an honest `j` received by an honest process was cast by `j` (line 3). -/
theorem vote_rcv {r : ℕ} {p q : P} (hp : p ∉ F) {m : Msg P V} (hm : E.rcv r p q = some m)
    {j i : P} (hj : j ∉ F) (hx : Tok.vote j i ∈ m.tokens) : pos (inp j).2 i ≤ 2 * k + 1 := by
  obtain ⟨r', -, w, m', hs, hx'⟩ := E.tokens_origin_rcv (alg_unforging k t) hA hp hm hx hj
  exact vote_sent E hA hj hs hx'

/-- A link token of an honest `j` for `(s, v)` received by an honest process: `j` sent a chain for
`(s, v)` in some round `r' ∈ [1, min r (k+1)]`. -/
theorem link_rcv {r : ℕ} {p q : P} (hp : p ∉ F) {m : Msg P V} (hm : E.rcv r p q = some m)
    {j s : P} {v : V} (hj : j ∉ F) (hx : Tok.link j s v ∈ m.tokens) :
    ∃ r' ≤ r, 1 ≤ r' ∧ r' ≤ k + 1 ∧ ∃ ch ∈ (E.s r' j).out, ch.s = s ∧ ch.x = v := by
  obtain ⟨r', hr', w, m', hs, hx'⟩ := E.tokens_origin_rcv (alg_unforging k t) hA hp hm hx hj
  obtain ⟨h1, h2, h3⟩ := link_sent E hs hx'
  exact ⟨r', hr', h1, h2, h3⟩

end Origin

end BAWithPredictions.AuthBA
