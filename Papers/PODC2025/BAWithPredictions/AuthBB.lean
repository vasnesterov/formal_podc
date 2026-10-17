import Papers.PODC2025.BAWithPredictions.AuthInv

/-!
# Byzantine broadcast with an implicit committee (Algorithm 6, Lemmas 21–23)

The `n` instances of Algorithm 6 run in rounds `1 … k+1` of `AuthBA.alg`; `bb E p s` is the
value returned by process `p` in the instance with sender `p_s` (`none` is `⊥`).

* `Csup k F inp`: the processes that received the vote of at least one honest process. Every
  committee certificate for `p_i` that an honest process ever sees (`t + 1` distinct vote tokens,
  `|F| ≤ t`) contains an honest vote, so `i ∈ Csup` (`mem_Csup_of_cert`); hence `Csup ⊇ C`, the
  set of processes that have a committee certificate in the paper. Honest processes with a
  certificate are in `Csup` (`cert_mem_Csup`).
* `CH E`: the honest processes with a certificate (`C ∩ H`).
* `lemma21` (validity with sender certificate), `lemma22_honest` / `lemma22_faulty` (default
  without sender certificate), `lemma23` (committee agreement, assuming at most `k` faulty
  processes in `Csup`), all for synchronous authenticated executions.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions.AuthBA

open Finset Cslib.Byzantine.PartialSync

variable {P V : Type*} [Fintype P] [LinearOrder P] [LinearOrder V]

/-- The processes that received the committee vote of some honest process: `j ∈ L_i` for some
honest `i` (a superset of the paper's `C`). -/
def Csup (k : ℕ) (F : Finset P) (inp : P → V × (P → Bool)) : Finset P :=
  univ.filter fun i => ∃ p ∉ F, pos (inp p).2 i ≤ 2 * k + 1

section BB

variable {k t : ℕ} {F : Finset P} {inp : P → V × (P → Bool)}
  (E : RoundRun (alg (P := P) (V := V) k t) F inp)

/-- The honest processes that have a committee certificate (`C ∩ H`). -/
def CH : Finset P := univ.filter fun i => i ∉ F ∧ (cert E i).isSome

/-- `X_p[s]` at the end of Algorithm 6 (after round `k + 1`). -/
def Xf (p s : P) : Finset V := (E.s (k + 2) p).X s

/-- `bb_p[s]`: the value returned by `p` in the broadcast instance with sender `p_s`
(`none` = `⊥`). -/
def bb (p s : P) : Option V := bbOut (Xf E p s)

theorem mem_Csup {i : P} : i ∈ Csup k F inp ↔ ∃ p ∉ F, pos (inp p).2 i ≤ 2 * k + 1 := by
  simp [Csup]

variable (hF : F.card ≤ t) (hsync : E.SyncFrom 0) (hA : E.AuthValid auth)

include hF hA in
/-- Every committee certificate seen by an honest process contains an honest vote, so its owner is
in `Csup`. -/
theorem mem_Csup_of_cert {r : ℕ} {p q : P} (hp : p ∉ F) {m : Msg P V}
    (hm : E.rcv r p q = some m) {i : P} {cc : Finset P} (hcc : t + 1 ≤ cc.card)
    (hx : ∀ j ∈ cc, Tok.vote j i ∈ m.tokens) : i ∈ Csup k F inp := by
  obtain ⟨j, hj, hjF⟩ : ∃ j ∈ cc, j ∉ F := by
    by_contra h
    push Not at h
    have := card_le_card (show cc ⊆ F from h)
    omega
  exact mem_Csup.mpr ⟨j, hjF, vote_rcv E hA hp hm hjF (hx j hj)⟩

include hF hA in
/-- Honest processes with a certificate are in `Csup`. -/
theorem cert_mem_Csup {p : P} (hp : p ∉ F) (h : (cert E p).isSome) : p ∈ Csup k F inp := by
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨hSv, hcard⟩ := cert_some E hS
  obtain ⟨j, hj, hjF⟩ : ∃ j ∈ S, j ∉ F := by
    by_contra h
    push Not at h
    have := card_le_card (show S ⊆ F from h)
    omega
  rw [hSv] at hj
  have hrcv := (mem_filter.mp hj).2
  exact mem_Csup.mpr ⟨j, hjF, vote_rcv E hA hp hrcv hjF rfl⟩

include hF hA in
/-- The signers of a valid chain received by an honest process are in `Csup`. -/
theorem signers_mem_Csup {r : ℕ} {p q : P} (hp : p ∉ F) {S : Finset (Chain P V)}
    (hm : E.rcv r p q = some (.chains S)) {ch : Chain P V} (hch : ch ∈ S) {r' : ℕ}
    (hok : ChainOK t r' ch) {j : P} (hj : j ∈ ch.signers) : j ∈ Csup k F inp := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
  exact mem_Csup_of_cert E hF hA hp hm (hok.2.2.2 l hl)
    (fun j' hj' => ⟨ch, hch, vote_mem_tokens hl hj'⟩)

include hA hsync in
/-- A chain sent by an honest process in round `r ∈ [1, k+1]` reaches every honest process `q`,
which then has its value in `X_q[s]` or already two values. -/
theorem spread {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) {j : P} (hj : j ∉ F) {ch : Chain P V}
    (hch : ch ∈ (E.s r j).out) {q : P} (hq : q ∉ F) :
    ch.x ∈ (E.s (r + 1) q).X ch.s ∨ 2 ≤ ((E.s (r + 1) q).X ch.s).card := by
  obtain ⟨-, hok, -, -, -⟩ := out_inv E (by omega) hch
  have hrcv : E.rcv r q j = some (Msg.chains (E.s r j).out) := by
    rw [hsync r (Nat.zero_le _) q j hq hj]
    change (if r = 0 then _ else if r ≤ k + 1 then
      (if (E.s r j).out.Nonempty then some (Msg.chains (E.s r j).out) else none) else _) = _
    rw [ite_eq_right (by omega), ite_eq_left h2, ite_eq_left ⟨ch, hch⟩]
  by_cases hqs : q ∈ ch.signers
  · obtain ⟨r', hr', h1', h2', ch', hch', hs, hv⟩ :=
      link_rcv E hA hq hrcv hq (s := ch.s) (v := ch.x) ⟨ch, hch, link_mem_tokens hqs⟩
    obtain ⟨-, -, hX, -, -⟩ := out_inv E (by omega) hch'
    rw [hs, hv] at hX
    exact Or.inl (X_mono E (by omega) q ch.s hX)
  · have hacc : ch.x ∈ accSet t r q (E.rcv r q) ch.s :=
      mem_accSet.mpr ⟨ch, ⟨j, _, hrcv, hch, hok, hqs⟩, rfl, rfl⟩
    rw [X_succ_bb E h1 h2]
    exact mem_step_or hacc

include hA hsync in
theorem spread_final {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ k + 1) {j : P} (hj : j ∉ F)
    {ch : Chain P V} (hch : ch ∈ (E.s r j).out) {q : P} (hq : q ∉ F) :
    ch.x ∈ Xf E q ch.s ∨ 2 ≤ (Xf E q ch.s).card := by
  have hmono := X_mono E (show r + 1 ≤ k + 2 by omega) q ch.s
  rcases spread E hsync hA h1 h2 hj hch hq with h | h
  · exact Or.inl (hmono h)
  · exact Or.inr (h.trans (card_le_card hmono))

include hF hA hsync in
/-- The key step of **Lemma 23**: if at most `k` faulty processes are in `Csup` and an honest
process `i` with a certificate has `v ∈ X_i[s]`, then every honest `q` has `v ∈ X_q[s]` or two
values in `X_q[s]`. -/
theorem lemma23_core (hCF : (F.filter (· ∈ Csup k F inp)).card ≤ k) {i : P} (hi : i ∉ F)
    (hci : (cert E i).isSome) {s : P} {q : P} (hq : q ∉ F) :
    ∀ r, ∀ v ∈ (E.s r i).X s, v ∈ Xf E q s ∨ 2 ≤ (Xf E q s).card := by
  intro r
  induction r with
  | zero => intro v hv; rw [X_zero] at hv; simp at hv
  | succ r ih =>
    intro v hv
    by_cases hold : v ∈ (E.s r i).X s
    · exact ih v hold
    rcases Nat.eq_zero_or_pos r with rfl | h0
    · rw [X_one] at hv
      split_ifs at hv with h
      · obtain ⟨-, rfl⟩ := h
        rw [mem_singleton.mp hv]
        obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hci
        have hch : (⟨s, (inp s).1, [(s, S)]⟩ : Chain P V) ∈ (E.s 1 s).out := by
          rw [out_one, hS]; exact mem_singleton_self _
        exact spread_final E hsync hA le_rfl (by omega) hi hch hq
      · simp at hv
    obtain ⟨hrk, hacc, hout⟩ := X_new E h0 hv hold
    rcases Nat.lt_or_ge r (k + 1) with hlt | hge
    · obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hci
      obtain ⟨ch, hch, rfl, rfl⟩ := hout S hS
      exact spread_final E hsync hA (by omega) (by omega) hi hch hq
    · obtain ⟨ch, ⟨q', S', hrcv, hchS, hok, -⟩, rfl, rfl⟩ := mem_accSet.mp hacc
      obtain ⟨j, hjs, hjF⟩ : ∃ j ∈ ch.signers, j ∉ F := by
        by_contra hall
        push Not at hall
        have hsub : ch.signers.toFinset ⊆ F.filter (· ∈ Csup k F inp) := by
          intro j hj
          have hj' := List.mem_toFinset.mp hj
          exact mem_filter.mpr ⟨hall j hj', signers_mem_Csup E hF hA hi hrcv hchS hok hj'⟩
        have h1 := card_le_card hsub
        rw [List.toFinset_card_of_nodup hok.2.2.1] at h1
        have h2 : ch.signers.length = r := by simp [Chain.signers, hok.1]
        omega
      obtain ⟨r', hr', h1', h2', ch', hch', hs, hv'⟩ :=
        link_rcv E hA hi hrcv hjF ⟨ch, hchS, link_mem_tokens hjs⟩
      have := spread_final E hsync hA h1' h2' hjF hch' hq
      rwa [hs, hv'] at this

omit [Fintype P] [LinearOrder P] in
/-- Two sets of size `≤ 2` such that every element of one is in the other unless the other has two
elements give the same return value. -/
theorem bbOut_eq_of {A B : Finset V} (hA2 : A.card ≤ 2) (hB2 : B.card ≤ 2)
    (hAB : ∀ v ∈ A, v ∈ B ∨ 2 ≤ B.card) (hBA : ∀ v ∈ B, v ∈ A ∨ 2 ≤ A.card) :
    bbOut A = bbOut B := by
  have key : ∀ {A B : Finset V}, (∀ v ∈ A, v ∈ B ∨ 2 ≤ B.card) → B.card < 2 → A ⊆ B :=
    fun hAB hB v hv => (hAB v hv).resolve_right (by omega)
  by_cases hA' : 2 ≤ A.card
  · by_cases hB' : 2 ≤ B.card
    · unfold bbOut
      simp only [show A.card ≠ 1 by omega, show B.card ≠ 1 by omega, ↓reduceDIte]
    · have := card_le_card (key hAB (by omega)); omega
  · by_cases hB' : 2 ≤ B.card
    · have := card_le_card (key hBA (by omega)); omega
    · rw [subset_antisymm (key hAB (by omega)) (key hBA (by omega))]

include hF hA hsync in
/-- **Lemma 23 (Committee Agreement).** If at most `k` faulty processes are in `Csup` (in
particular, if `|F ∩ C| ≤ k`), all honest processes that have a committee certificate return the
same value in each broadcast instance. -/
theorem lemma23 (hCF : (F.filter (· ∈ Csup k F inp)).card ≤ k) {i j : P} (hi : i ∈ CH E)
    (hj : j ∈ CH E) (s : P) : bb E i s = bb E j s := by
  simp only [CH, mem_filter, mem_univ, true_and] at hi hj
  exact bbOut_eq_of (X_card E _ _ _) (X_card E _ _ _)
    (lemma23_core E hF hsync hA hCF hi.1 hi.2 hj.1 _)
    (lemma23_core E hF hsync hA hCF hj.1 hj.2 hi.1 _)

include hA in
/-- For an honest sender `s`, every value in `X_q[s]` of an honest `q` is the input of `s`. -/
theorem X_honest_sender {s : P} (hs : s ∉ F) :
    ∀ r, ∀ q ∉ F, ∀ v ∈ (E.s r q).X s, v = (inp s).1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro q hq v hv
    rcases X_cases E hv with ⟨rfl, rfl, -⟩ | ⟨r', -, hr', -, ch, ⟨q', S', hrcv, hchS, hok, -⟩,
      rfl, rfl⟩
    · rfl
    · obtain ⟨r'', hr'', -, h2, ch', hch', hs', hv'⟩ :=
        link_rcv E hA hq hrcv hs ⟨ch, hchS, link_mem_tokens (mem_signers_of_head hok)⟩
      obtain ⟨-, -, hX, -, -⟩ := out_inv E (by omega) hch'
      rw [hs', hv'] at hX
      exact ih r'' (by omega) _ hs _ hX

omit [Fintype P] [LinearOrder P] in
theorem bbOut_singleton (x : V) : bbOut ({x} : Finset V) = some x := by
  simp [bbOut]

include hA hsync in
/-- **Lemma 21 (Validity with Sender Certificate).** If the sender `p_s` is honest and has a
committee certificate, every honest process returns its input `x_s`. -/
theorem lemma21 {s : P} (hs : s ∈ CH E) {q : P} (hq : q ∉ F) : bb E q s = some (inp s).1 := by
  simp only [CH, mem_filter, mem_univ, true_and] at hs
  have hsub : Xf E q s ⊆ {(inp s).1} := fun v hv =>
    mem_singleton.mpr (X_honest_sender E hA hs.1 _ q hq v hv)
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hs.2
  have hch : (⟨s, (inp s).1, [(s, S)]⟩ : Chain P V) ∈ (E.s 1 s).out := by
    rw [out_one, hS]; exact mem_singleton_self _
  have hmem : (inp s).1 ∈ Xf E q s := by
    rcases spread_final E hsync hA le_rfl (by omega) hs.1 hch hq with h | h
    · exact h
    · change 2 ≤ (Xf E q s).card at h
      have := card_le_card hsub; simp at this; omega
  unfold bb
  rw [subset_antisymm hsub (singleton_subset_iff.mpr hmem), bbOut_singleton]

omit [Fintype P] [LinearOrder P] in
theorem bbOut_empty : bbOut (∅ : Finset V) = none := by
  simp [bbOut]

include hA in
/-- An honest sender without a certificate starts no chain: `X_q[s] = ∅` for honest `q`. -/
theorem Xf_empty_honest {s : P} (hs : s ∉ F) (hc : cert E s = none) {q : P} (hq : q ∉ F) :
    Xf E q s = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro v hv
  rcases X_cases E hv with ⟨rfl, -, h⟩ | ⟨r', -, hr', -, ch, ⟨q', S', hrcv, hchS, hok, -⟩,
    rfl, rfl⟩
  · rw [hc] at h; simp at h
  · obtain ⟨r'', hr'', -, h2, ch', hch', -, -⟩ :=
      link_rcv E hA hq hrcv hs ⟨ch, hchS, link_mem_tokens (mem_signers_of_head hok)⟩
    obtain ⟨-, -, -, h, -⟩ := out_inv E (by omega) hch'
    rw [hc] at h; simp at h

include hF hA in
/-- No valid chain is started by a process outside `Csup`: `X_q[s] = ∅` for honest `q`. -/
theorem Xf_empty_of_notMem_Csup {s : P} (hs : s ∉ Csup k F inp) {q : P} (hq : q ∉ F) :
    Xf E q s = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro v hv
  rcases X_cases E hv with ⟨rfl, -, h⟩ | ⟨r', -, hr', -, ch, ⟨q', S', hrcv, hchS, hok, -⟩,
    rfl, rfl⟩
  · exact hs (cert_mem_Csup E hF hA hq h)
  · exact hs (signers_mem_Csup E hF hA hq hrcv hchS hok (mem_signers_of_head hok))

include hA in
/-- **Lemma 22 (Default without Sender Certificate)**, honest sender: if the honest sender `p_s`
does not have a committee certificate, every honest process returns `⊥`. -/
theorem lemma22_honest {s : P} (hs : s ∉ F) (hc : cert E s = none) {q : P} (hq : q ∉ F) :
    bb E q s = none := by
  unfold bb; rw [Xf_empty_honest E hA hs hc hq, bbOut_empty]

include hF hA in
/-- **Lemma 22 (Default without Sender Certificate)**, any sender: if no honest process voted for
`p_s` (so no committee certificate for `p_s` can exist), every honest process returns `⊥`. -/
theorem lemma22_faulty {s : P} (hs : s ∉ Csup k F inp) {q : P} (hq : q ∉ F) :
    bb E q s = none := by
  unfold bb; rw [Xf_empty_of_notMem_Csup E hF hA hs hq, bbOut_empty]

end BB

end BAWithPredictions.AuthBA
