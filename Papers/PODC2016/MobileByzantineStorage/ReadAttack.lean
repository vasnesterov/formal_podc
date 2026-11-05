import Papers.PODC2016.MobileByzantineStorage.Model

/-!
# The read operations of the paper's protocols can be fooled (Theorems 8/9 and 11/12 are false)

The `read()` of the `(ΔS, CAM)` protocol (Fig. 24) broadcasts `read(i)`, waits `2δ`, and returns the
pair chosen by `select_value(reply_i)`: among the pairs `⟨v, sn⟩` that occur (from distinct servers)
at least `#reply_CAM` times in the set `reply_i` of triples `⟨j, ⟨v, sn⟩⟩` received during the wait, the
one with the highest sequence number (Section 5.1). The `(ΔS, CUM)` read (Fig. 27) is the same with a
`3δ` wait and threshold `#reply_CUM`.

The paper bounds the number of servers that can send a wrong reply during a read `[t, t+2δ]` by
`MaxB̃(t, t+2δ)`, "as if each message to/from them is delivered instantaneously" (Section 5.2). But a
message sent by a faulty server at a time `τ ∈ (t - δ, t)` can be delivered at any time of
`(τ, τ + δ]`, hence *during* the read. Counting these servers too, the adversary gets up to
`(⌈3δ/Δ⌉ + 1) f` distinct liars against a CAM read, which reaches `#reply_CAM = (k+1) f + 1` for
`2δ ≤ Δ < 3δ` (`k = 1`: `3f` liars) and for `δ ≤ Δ < 3δ/2` (`k = 2`: `4f` liars). They all report the
same never-written pair with a sequence number larger than any written one, so `select_value` returns it.

Model of a read (only what the counterexample needs):
* `Reply`: a `reply` message to the reader, with its sender, sending time, delay and the set of pairs it
  carries; `collected M t D` is `reply_i` at the end of a read invoked at `t` that waits `D`
  (messages delivered in `(t, t + D]`);
* `SelectValue thr R p`: `p` is a possible result of `select_value` (any tie-breaking);
* `Schedule.ByzReply`: a reply that a faulty server may send (it is faulty at the sending time, and the
  delay is in `(0, δ]` as for every message of the round-free synchronous model, Section 2).

The replies of the non-faulty servers are arbitrary (universally quantified); we only assume their
sequence numbers are at most `N`, the number of writes so far. This holds in the counterexample
executions because the faulty servers send nothing to the servers, so non-faulty servers only ever store
written pairs (and `⟨⊥, 0⟩`).
-/

namespace Podc.MobileByzantineStorage

open Finset Classical

variable {n f : ℕ} {V : Type*}

/-- A `reply` message to the reader: sender, sending time, delay, and the pairs `⟨v, sn⟩` it carries. -/
structure Reply (n : ℕ) (V : Type*) where
  sender : Fin n
  sendTime : ℝ
  delay : ℝ
  payload : Finset (V × ℕ)

/-- Delivery time of a reply. -/
def Reply.arrival (m : Reply n V) : ℝ := m.sendTime + m.delay

/-- `reply_i` at the end of a read invoked at time `t` that waits `D` (Fig. 24/27, lines 01–03,
07–09): the triples `⟨j, ⟨v, sn⟩⟩` of all replies delivered during `(t, t + D]`. -/
noncomputable def collected (M : Finset (Reply n V)) (t D : ℝ) : Finset (Fin n × (V × ℕ)) :=
  (M.filter fun m => t < m.arrival ∧ m.arrival ≤ t + D).biUnion
    fun m => m.payload.image fun p => (m.sender, p)

theorem mem_collected {M : Finset (Reply n V)} {t D : ℝ} {x : Fin n × (V × ℕ)} :
    x ∈ collected M t D ↔
      ∃ m ∈ M, (t < m.arrival ∧ m.arrival ≤ t + D) ∧ x.1 = m.sender ∧ x.2 ∈ m.payload := by
  simp only [collected, mem_biUnion, mem_filter, mem_image]
  constructor
  · rintro ⟨m, ⟨hm, hw⟩, p, hp, rfl⟩; exact ⟨m, hm, hw, rfl, hp⟩
  · rintro ⟨m, hm, hw, h1, h2⟩; exact ⟨m, ⟨hm, hw⟩, x.2, h2, by ext <;> simp [h1]⟩

/-- Number of occurrences (i.e. of distinct senders) of the pair `p` in `reply_i`. -/
noncomputable def occ (R : Finset (Fin n × (V × ℕ))) (p : V × ℕ) : ℕ := (R.filter fun x => x.2 = p).card

/-- `select_value(reply_i)` (Section 5.1, 6.1): `p` is a possible result iff it occurs at least `thr`
times and has the highest sequence number among the pairs occurring at least `thr` times. -/
def SelectValue (thr : ℕ) (R : Finset (Fin n × (V × ℕ))) (p : V × ℕ) : Prop :=
  thr ≤ occ R p ∧ ∀ q, thr ≤ occ R q → q.2 ≤ p.2

/-- If `m ≥ thr` distinct servers report the pair `fake` during the read, the other replies only carry
pairs with smaller sequence numbers, then `fake` is the only possible result of `select_value`. -/
theorem selectValue_iff_eq_fake {byz honest : Finset (Reply n V)} {t D : ℝ} {fake : V × ℕ}
    {m thr : ℕ} (hm : m ≤ n) (hthr : thr ≤ m) (hthr1 : 1 ≤ thr)
    (hcov : ∀ s : Fin n, s.val < m → ∃ r ∈ byz, r.sender = s ∧ fake ∈ r.payload ∧
      t < r.arrival ∧ r.arrival ≤ t + D)
    (hbyz : ∀ r ∈ byz, r.payload = {fake}) (hhon : ∀ r ∈ honest, ∀ q ∈ r.payload, q.2 < fake.2)
    (q : V × ℕ) : SelectValue thr (collected (honest ∪ byz) t D) q ↔ q = fake := by
  set R := collected (honest ∪ byz) t D
  -- `fake` occurs at least `m` times
  have hfake : thr ≤ occ R fake := by
    refine hthr.trans ?_
    have hsub : (univ.filter fun s : Fin n => s.val < m).image (fun s => (s, fake)) ⊆
        R.filter fun x => x.2 = fake := by
      intro x hx
      simp only [mem_image, mem_filter, mem_univ, true_and] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨r, hr, hsend, hp, hw⟩ := hcov s hs
      exact mem_filter.2 ⟨mem_collected.2 ⟨r, mem_union_right _ hr, hw, hsend.symm, hp⟩, rfl⟩
    have := card_le_card hsub
    rw [card_image_of_injective _ (fun a b h => by simpa using h), card_filter_val_lt,
      min_eq_right hm] at this
    exact this
  -- every other pair occurring at least once has a smaller sequence number
  have hother : ∀ q, 1 ≤ occ R q → q = fake ∨ q.2 < fake.2 := by
    intro q hq
    obtain ⟨x, hx⟩ := card_pos.1 hq
    obtain ⟨hxR, rfl⟩ := mem_filter.1 hx
    obtain ⟨r, hr, -, -, hp⟩ := mem_collected.1 hxR
    rcases mem_union.1 hr with hr | hr
    · exact Or.inr (hhon r hr _ hp)
    · rw [hbyz r hr, mem_singleton] at hp; exact Or.inl hp
  constructor
  · rintro ⟨hq, hmax⟩
    rcases hother q (hthr1.trans hq) with h | h
    · exact h
    · exact absurd (hmax fake hfake) (not_le.2 h)
  · rintro rfl
    refine ⟨hfake, fun q hq => ?_⟩
    rcases hother q (hthr1.trans hq) with h | h
    · rw [h]
    · exact h.le

/-- The attack, generically: the agents occupy the disjoint blocks `0, …, p-1` of `f` servers during
the periods `0, …, p-1`; every server `s` of block `j` sends one reply carrying `fake` at time `τ j`
with delay `d j`. If these replies are admissible and delivered during the read, `fake` is the only
possible result of the read. -/
theorem attack {p thr : ℕ} (hf : 0 < f) (hn : p * f ≤ n) (hthr : thr ≤ p * f) (hthr1 : 1 ≤ thr)
    (Adm : Fin n → ℝ → ℝ → Prop) (τ d : ℕ → ℝ) {t D : ℝ}
    (hadm : ∀ s : Fin n, s.val < p * f → Adm s (τ (s.val / f)) (d (s.val / f)))
    (harr : ∀ j < p, t < τ j + d j ∧ τ j + d j ≤ t + D) (fake : V × ℕ) :
    ∃ byz : Finset (Reply n V), (∀ r ∈ byz, Adm r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply n V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 < fake.2) →
        ∀ q, SelectValue thr (collected (honest ∪ byz) t D) q ↔ q = fake := by
  let mk : Fin n → Reply n V := fun s => ⟨s, τ (s.val / f), d (s.val / f), {fake}⟩
  refine ⟨(univ.filter fun s : Fin n => s.val < p * f).image mk, ?_, fun honest hhon q => ?_⟩
  · intro r hr
    simp only [mem_image, mem_filter, mem_univ, true_and] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    exact hadm s hs
  · refine selectValue_iff_eq_fake hn hthr hthr1 (fun s hs => ⟨mk s, ?_, rfl, mem_singleton_self _,
      harr _ ((Nat.div_lt_iff_lt_mul hf).2 hs)⟩) ?_ hhon q
    · exact mem_image.2 ⟨s, mem_filter.2 ⟨mem_univ _, hs⟩, rfl⟩
    · intro r hr
      simp only [mem_image, mem_filter, mem_univ, true_and] at hr
      obtain ⟨s, -, rfl⟩ := hr
      rfl

/-! ### The `(ΔS, CAM)` protocol (Section 5) -/

/-- A reply that a faulty server may send: it hosts an agent at the sending time, and the message
delay is in `(0, δ]`. -/
def Schedule.ByzReply (S : Schedule n f) (t₀ Δ δ : ℝ) (s : Fin n) (τ d : ℝ) : Prop :=
  S.Faulty t₀ Δ s τ ∧ 0 < d ∧ d ≤ δ

/-- **Theorem 8/9 are false for `k = 1`** (`2δ ≤ Δ < 3δ`, `#reply_CAM = 2f + 1`, in particular for
`n = 4f + 1` as in Table 1): `3f` faulty servers (one block before the read, two during it) make the
read return a never-written pair, whatever the other servers reply. -/
theorem theorem9_false_k1 (hf : 0 < f) (hn : 3 * f ≤ n) {δ Δ : ℝ} (hδ : 0 < δ) (h1 : 2 * δ ≤ Δ)
    (h2 : Δ < 3 * δ) (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule n f) (t : ℝ) (byz : Finset (Reply n V)),
      (∀ r ∈ byz, S.ByzReply t₀ Δ δ r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply n V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue (2 * f + 1) (collected (honest ∪ byz) t (2 * δ)) q ↔ q = (v', N + 1) := by
  have hΔ : 0 < Δ := by linarith
  set t := t₀ + (3 * Δ - δ) / 2
  let τ : ℕ → ℝ := fun j => if j = 0 then (t - δ + t₀ + Δ) / 2 else if j = 1 then t else t₀ + 2 * Δ
  let d : ℕ → ℝ := fun j => if j = 0 then δ else if j = 1 then δ else (t + 2 * δ - (t₀ + 2 * Δ)) / 2
  have hper : ∀ j < 3, period t₀ Δ (τ j) = j ∧ 0 < d j ∧ d j ≤ δ ∧
      t < τ j + d j ∧ τ j + d j ≤ t + 2 * δ := by
    intro j hj
    interval_cases j <;>
      refine ⟨(period_eq_iff hΔ _).2 ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [τ, d, t] <;> norm_num <;>
      linarith
  obtain ⟨byz, hadm, hsel⟩ := attack (p := 3) (thr := 2 * f + 1) hf hn (by omega) (by omega)
    ((blocks n f 3).ByzReply t₀ Δ δ) τ d (t := t) (D := 2 * δ)
    (fun s hs => by
      have hj := (Nat.div_lt_iff_lt_mul hf).2 hs
      obtain ⟨hp, hd⟩ := hper _ hj
      exact ⟨(blocks_faulty_iff hf).2 ⟨hs, hp.symm⟩, hd.1, hd.2.1⟩)
    (fun j hj => (hper j hj).2.2.2) (v', N + 1)
  exact ⟨blocks n f 3, t, byz, hadm, fun honest hhon =>
    hsel honest fun r hr q hq => Nat.lt_succ_of_le (hhon r hr q hq)⟩

/-- **Theorem 8/9 are false for `k = 2` when `δ ≤ Δ < 3δ/2`** (`#reply_CAM = 3f + 1`, in particular for
`n = 5f + 1` as in Table 1): `4f` faulty servers (one block before the read, three during it) make the
read return a never-written pair, whatever the other servers reply. -/
theorem theorem9_false_k2 (hf : 0 < f) (hn : 4 * f ≤ n) {δ Δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ Δ)
    (h2 : 2 * Δ < 3 * δ) (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule n f) (t : ℝ) (byz : Finset (Reply n V)),
      (∀ r ∈ byz, S.ByzReply t₀ Δ δ r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply n V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue (3 * f + 1) (collected (honest ∪ byz) t (2 * δ)) q ↔ q = (v', N + 1) := by
  have hΔ : 0 < Δ := by linarith
  set t := t₀ + 2 * Δ - δ / 2
  let τ : ℕ → ℝ := fun j => if j = 0 then t₀ + (3 * Δ - 3 * δ / 2) / 2 else t₀ + j * Δ
  let d : ℕ → ℝ := fun j => if j = 0 then δ else if j = 1 then δ else if j = 2 then δ / 2
    else (3 * δ / 2 - Δ) / 2
  have hper : ∀ j < 4, period t₀ Δ (τ j) = j ∧ 0 < d j ∧ d j ≤ δ ∧
      t < τ j + d j ∧ τ j + d j ≤ t + 2 * δ := by
    intro j hj
    interval_cases j <;>
      refine ⟨(period_eq_iff hΔ _).2 ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [τ, d, t] <;> norm_num <;>
      linarith
  obtain ⟨byz, hadm, hsel⟩ := attack (p := 4) (thr := 3 * f + 1) hf hn (by omega) (by omega)
    ((blocks n f 4).ByzReply t₀ Δ δ) τ d (t := t) (D := 2 * δ)
    (fun s hs => by
      have hj := (Nat.div_lt_iff_lt_mul hf).2 hs
      obtain ⟨hp, hd⟩ := hper _ hj
      exact ⟨(blocks_faulty_iff hf).2 ⟨hs, hp.symm⟩, hd.1, hd.2.1⟩)
    (fun j hj => (hper j hj).2.2.2) (v', N + 1)
  exact ⟨blocks n f 4, t, byz, hadm, fun honest hhon =>
    hsel honest fun r hr q hq => Nat.lt_succ_of_le (hhon r hr q hq)⟩

/-- **Theorem 9 is false** at the parameters of Table 1 (`n = (k+3) f + 1`, `#reply_CAM = (k+1) f + 1`,
`kΔ ≥ 2δ`), for `k = 1, 2δ ≤ Δ < 3δ` and for `k = 2, δ ≤ Δ < 3δ/2`: some read with no concurrent
write returns a value `v' ≠ v` that was never written (`v` being the last written value), violating
even the safe-register specification. -/
theorem theorem9_false (k : ℕ) (hf : 0 < f) {δ Δ : ℝ} (hδ : 0 < δ)
    (hk : (k = 1 ∧ 2 * δ ≤ Δ ∧ Δ < 3 * δ) ∨ (k = 2 ∧ δ ≤ Δ ∧ 2 * Δ < 3 * δ))
    (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule ((k + 3) * f + 1) f) (t : ℝ) (byz : Finset (Reply ((k + 3) * f + 1) V)),
      (∀ r ∈ byz, S.ByzReply t₀ Δ δ r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply ((k + 3) * f + 1) V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue ((k + 1) * f + 1) (collected (honest ∪ byz) t (2 * δ)) q ↔
          q = (v', N + 1) := by
  rcases hk with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · simpa [show (1 + 1) * f = 2 * f by ring] using
      theorem9_false_k1 (n := (1 + 3) * f + 1) hf (by omega) hδ h1 h2 t₀ v' N
  · simpa [show (2 + 1) * f = 3 * f by ring] using
      theorem9_false_k2 (n := (2 + 3) * f + 1) hf (by omega) hδ h1 h2 t₀ v' N

/-! ### The `(ΔS, CUM)` protocol (Section 6) -/

/-- A server is a *lying cured* server at time `τ` (CUM model) if it is not faulty at `τ` but was faulty
during `[τ - 2δ, τ)`. By Lemma 18 (and the proof of Theorem 11) such a server may answer a `read` with a
non-valid value: the agent can leave an entry `⟨⟨v', sn'⟩, 2δ⟩` in `W_i` (Fig. 25/26), and the
reply `conCut(V_i, Vsafe_i, W_i)` (Fig. 27, line 11) contains it as long as it has not expired, since
`sn'` is the highest sequence number. -/
def Schedule.CuredLiar (S : Schedule n f) (t₀ Δ δ : ℝ) (s : Fin n) (τ : ℝ) : Prop :=
  ¬ S.Faulty t₀ Δ s τ ∧ ∃ τ' ∈ Set.Ico (τ - 2 * δ) τ, S.Faulty t₀ Δ s τ'

/-- A reply carrying a non-valid value in a CUM read invoked at time `t`: either sent by a faulty
server, or sent by a lying cured server when the `read` request reaches it (at a time in `(t, t + δ]`);
the delay is in `(0, δ]`. -/
def Schedule.LyingReply (S : Schedule n f) (t₀ Δ δ t : ℝ) (s : Fin n) (τ d : ℝ) : Prop :=
  (S.Faulty t₀ Δ s τ ∨ (S.CuredLiar t₀ Δ δ s τ ∧ t < τ ∧ τ ≤ t + δ)) ∧ 0 < d ∧ d ≤ δ

/-- A server of block `j` whose agent left at the end of period `j` is a lying cured server at `τ`
if it was still faulty at some time of `[τ - 2δ, τ)`. -/
theorem blocks_curedLiar (hf : 0 < f) {p j : ℕ} {t₀ Δ δ τ τ' : ℝ} (hΔ : 0 < Δ) {s : Fin n}
    (hs : s.val / f = j) (hjp : j < p) (h1 : t₀ + (j + 1) * Δ ≤ τ) (h2 : τ - 2 * δ ≤ τ')
    (h3 : t₀ + j * Δ ≤ τ') (h4 : τ' < t₀ + (j + 1) * Δ) :
    (blocks n f p).CuredLiar t₀ Δ δ s τ := by
  have hsp : s.val < p * f := (Nat.div_lt_iff_lt_mul hf).1 (hs ▸ hjp)
  refine ⟨fun h => ?_, τ', ⟨h2, by linarith⟩, (blocks_faulty_iff hf).2 ⟨hsp, ?_⟩⟩
  · obtain ⟨-, h⟩ := (blocks_faulty_iff hf).1 h
    rw [hs, eq_comm, period_eq_iff hΔ] at h
    push_cast at h
    linarith [h.2]
  · rw [hs, eq_comm, period_eq_iff hΔ]
    push_cast
    exact ⟨h3, h4⟩

theorem blocks_curedLiar_zero (hf : 0 < f) {p : ℕ} {t₀ Δ δ τ τ' : ℝ} (hΔ : 0 < Δ) {s : Fin n}
    (hs : s.val < f) (h1 : t₀ + Δ ≤ τ) (h2 : τ - 2 * δ ≤ τ') (h3 : t₀ ≤ τ') (h4 : τ' < t₀ + Δ)
    (hp : 0 < p) : (blocks n f p).CuredLiar t₀ Δ δ s τ := by
  have hs0 : s.val / f = 0 := Nat.div_eq_of_lt hs
  have hsp : s.val < p * f := lt_of_lt_of_le hs (Nat.le_mul_of_pos_left f hp)
  refine ⟨fun h => ?_, τ', ⟨h2, by linarith⟩, (blocks_faulty_iff hf).2 ⟨hsp, ?_⟩⟩
  · obtain ⟨-, h⟩ := (blocks_faulty_iff hf).1 h
    rw [hs0, Nat.cast_zero, eq_comm, period_eq_iff hΔ] at h
    push_cast at h
    linarith [h.2]
  · rw [hs0, Nat.cast_zero, eq_comm, period_eq_iff hΔ]
    push_cast
    constructor <;> linarith

/-- **Theorems 11/12 are false for `k = 1` when `2δ ≤ Δ < 5δ/2`** (`#reply_CUM = 3f + 1`, Table 3,
in particular for `n = 5f + 1`): `3f` faulty servers and `f` lying cured servers make the `3δ` read return
a never-written pair. -/
theorem theorem12_false_k1 (hf : 0 < f) (hn : 4 * f ≤ n) {δ Δ : ℝ} (hδ : 0 < δ) (h1 : 2 * δ ≤ Δ)
    (h2 : 2 * Δ < 5 * δ) (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule n f) (t : ℝ) (byz : Finset (Reply n V)),
      (∀ r ∈ byz, S.LyingReply t₀ Δ δ t r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply n V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue (3 * f + 1) (collected (honest ∪ byz) t (3 * δ)) q ↔ q = (v', N + 1) := by
  have hΔ : 0 < Δ := by linarith
  set t := t₀ + 2 * Δ - δ / 2
  let τ : ℕ → ℝ := fun j => if j = 0 then t + (5 * δ / 2 - Δ) / 2 else if j = 1 then t
    else t₀ + j * Δ
  let d : ℕ → ℝ := fun j => if j = 3 then (5 * δ / 2 - Δ) / 2 else δ
  have hdel : ∀ j < 4, 0 < d j ∧ d j ≤ δ ∧ t < τ j + d j ∧ τ j + d j ≤ t + 3 * δ := by
    intro j hj
    interval_cases j <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [τ, d, t] <;> norm_num <;> linarith
  have hper : ∀ j, 1 ≤ j → j < 4 → period t₀ Δ (τ j) = j := by
    intro j hj1 hj
    interval_cases j <;> refine (period_eq_iff hΔ _).2 ⟨?_, ?_⟩ <;> simp only [τ, t] <;>
      norm_num <;> linarith
  obtain ⟨byz, hadm, hsel⟩ := attack (p := 4) (thr := 3 * f + 1) hf hn (by omega) (by omega)
    ((blocks n f 4).LyingReply t₀ Δ δ t) τ d (t := t) (D := 3 * δ)
    (fun s hs => by
      have hj := (Nat.div_lt_iff_lt_mul hf).2 hs
      obtain ⟨hd0, hd1, -⟩ := hdel _ hj
      refine ⟨?_, hd0, hd1⟩
      rcases Nat.eq_zero_or_pos (s.val / f) with h0 | h0
      · right
        have hs' : s.val < f := by
          by_contra h; exact absurd h0 (Nat.div_pos (not_lt.1 h) hf).ne'
        rw [h0]
        refine ⟨blocks_curedLiar_zero hf hΔ hs' (τ' := τ 0 - 2 * δ) ?_ le_rfl ?_ ?_ (by norm_num),
          ?_, ?_⟩ <;> simp only [τ, t] <;> norm_num <;> linarith
      · left
        exact (blocks_faulty_iff hf).2 ⟨hs, (hper _ h0 hj).symm⟩)
    (fun j hj => (hdel j hj).2.2) (v', N + 1)
  exact ⟨blocks n f 4, t, byz, hadm, fun honest hhon =>
    hsel honest fun r hr q hq => Nat.lt_succ_of_le (hhon r hr q hq)⟩

/-- **Theorems 11/12 are false for `k = 2` when `δ ≤ Δ < 5δ/4`** (`#reply_CUM = 5f + 1`, Table 3,
in particular for `n = 8f + 1`): `4f` faulty servers and `2f` lying cured servers make the `3δ` read
return a never-written pair. No reply is sent before the read starts: every lying reply comes from a
server that is faulty, or a cured liar in the sense of Lemma 18, during the read. -/
theorem theorem12_false_k2 (hf : 0 < f) (hn : 6 * f ≤ n) {δ Δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ Δ)
    (h2 : 4 * Δ < 5 * δ) (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule n f) (t : ℝ) (byz : Finset (Reply n V)),
      (∀ r ∈ byz, S.LyingReply t₀ Δ δ t r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply n V), (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue (5 * f + 1) (collected (honest ∪ byz) t (3 * δ)) q ↔ q = (v', N + 1) := by
  have hΔ : 0 < Δ := by linarith
  set t := t₀ + 3 * Δ - δ / 2
  let τ : ℕ → ℝ := fun j => if j = 0 ∨ j = 1 then t + (5 * δ / 2 - 2 * Δ) / 2 else t₀ + j * Δ
  let d : ℕ → ℝ := fun j => if j = 5 then (5 * δ / 2 - 2 * Δ) / 2 else δ
  have hdel : ∀ j < 6, 0 < d j ∧ d j ≤ δ ∧ t < τ j + d j ∧ τ j + d j ≤ t + 3 * δ := by
    intro j hj
    interval_cases j <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [τ, d, t] <;> norm_num <;> linarith
  have hper : ∀ j, 2 ≤ j → j < 6 → period t₀ Δ (τ j) = j := by
    intro j hj1 hj
    interval_cases j <;> refine (period_eq_iff hΔ _).2 ⟨?_, ?_⟩ <;> simp only [τ, t] <;>
      norm_num <;> linarith
  obtain ⟨byz, hadm, hsel⟩ := attack (p := 6) (thr := 5 * f + 1) hf hn (by omega) (by omega)
    ((blocks n f 6).LyingReply t₀ Δ δ t) τ d (t := t) (D := 3 * δ)
    (fun s hs => by
      have hj := (Nat.div_lt_iff_lt_mul hf).2 hs
      obtain ⟨hd0, hd1, -⟩ := hdel _ hj
      refine ⟨?_, hd0, hd1⟩
      obtain h0 | h0 | h0 : s.val / f = 0 ∨ s.val / f = 1 ∨ 2 ≤ s.val / f := by
        generalize s.val / f = l; omega
      · right
        rw [h0]
        refine ⟨blocks_curedLiar hf hΔ h0 (by norm_num) (τ' := τ 0 - 2 * δ) ?_ le_rfl ?_ ?_,
          ?_, ?_⟩ <;> simp only [τ, t] <;> norm_num <;> linarith
      · right
        rw [h0]
        refine ⟨blocks_curedLiar hf hΔ h0 (by norm_num) (τ' := t₀ + Δ) ?_ ?_ ?_ ?_,
          ?_, ?_⟩ <;> (try simp only [τ, t]) <;> norm_num <;> linarith
      · left
        exact (blocks_faulty_iff hf).2 ⟨hs, (hper _ h0 hj).symm⟩)
    (fun j hj => (hdel j hj).2.2) (v', N + 1)
  exact ⟨blocks n f 6, t, byz, hadm, fun honest hhon =>
    hsel honest fun r hr q hq => Nat.lt_succ_of_le (hhon r hr q hq)⟩

/-- **Theorem 12 is false** at the parameters of Table 3 (`n = (3k+2) f + 1`,
`#reply_CUM = (2k+1) f + 1`), for `k = 1, 2δ ≤ Δ < 5δ/2` and for `k = 2, δ ≤ Δ < 5δ/4`. (Theorem 12
itself states the weaker hypothesis `n ≥ 2(k+1) f + 1`; the counterexamples need only `4f` resp.
`6f` servers, so they refute both readings.) -/
theorem theorem12_false (k : ℕ) (hf : 0 < f) {δ Δ : ℝ} (hδ : 0 < δ)
    (hk : (k = 1 ∧ 2 * δ ≤ Δ ∧ 2 * Δ < 5 * δ) ∨ (k = 2 ∧ δ ≤ Δ ∧ 4 * Δ < 5 * δ))
    (t₀ : ℝ) (v' : V) (N : ℕ) :
    ∃ (S : Schedule ((3 * k + 2) * f + 1) f) (t : ℝ) (byz : Finset (Reply ((3 * k + 2) * f + 1) V)),
      (∀ r ∈ byz, S.LyingReply t₀ Δ δ t r.sender r.sendTime r.delay) ∧
      ∀ honest : Finset (Reply ((3 * k + 2) * f + 1) V),
        (∀ r ∈ honest, ∀ q ∈ r.payload, q.2 ≤ N) →
        ∀ q, SelectValue ((2 * k + 1) * f + 1) (collected (honest ∪ byz) t (3 * δ)) q ↔
          q = (v', N + 1) := by
  rcases hk with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · simpa [show (2 * 1 + 1) * f = 3 * f by ring] using
      theorem12_false_k1 (n := (3 * 1 + 2) * f + 1) hf (by omega) hδ h1 h2 t₀ v' N
  · simpa [show (2 * 2 + 1) * f = 5 * f by ring] using
      theorem12_false_k2 (n := (3 * 2 + 2) * f + 1) hf (by omega) hδ h1 h2 t₀ v' N

end Podc.MobileByzantineStorage
