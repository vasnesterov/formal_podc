import Papers.PODC2016.MobileByzantineStorage.Model

/-!
# Lower bounds for a `2δ`-type read in the `(ΔS, CAM)` model (Theorems 3 and 5, repaired)

Section 4.4 proves the lower bounds by exhibiting two executions `E₁` (register value `1`) and `E₀`
(value `0`) of a read with no concurrent write in which "the reader collects the same set of replies".
In the paper's executions the agents follow the *same* schedule, so the reader receives, e.g., `1` from
`s₀` in `E₁` and `0` from `s₀` in `E₀`: only the multisets of values coincide, while communication is
authenticated (Section 2) and the reader knows who sent what. We repair the argument: the two
executions use different schedules, and the reader's whole view — the set of triples
(sender, value, delivery time) — is the same.

The model is the paper's lower-bound scenario (Section 4.4), with the paper's assumptions on correct
servers and the most general adversary allowed by the system model:
* the read is invoked at time `t`; the request reaches every server `s` at a time `req s ∈ (t, t+δ]`;
* a server that is *correct* (neither faulty nor cured) when the request arrives replies once, with the
  register value, delay `dly s ∈ (0, δ]`; a faulty or cured server does not reply (the paper: "each
  cured server (in the CAM model) does not reply as long as it is cured"); a server is *cured* during
  `γ` time after its agent left (the constructions never use this: the silent servers are faulty
  when the request reaches them, so the results hold for every `γ`);
* faulty servers send arbitrary replies (sender, value, sending time while faulty, delay in `(0, δ]`).

`theorem3` (`n ≤ 5f`, `δ ≤ Δ < 2δ`) and `theorem5` (`n ≤ 4f`, `2δ ≤ Δ < 3δ`) hold for every read
duration `D`, for every `γ`, and for every decision rule of the reader. Since correct servers reply
only once, the views are equal as sets of all messages, so the duration does not matter; this is the
paper's "waiting more does not bring any new way to break symmetry", valid in this restricted model.
-/

namespace Podc.MobileByzantineStorage

open Finset Classical

variable {n f : ℕ}

/-- One execution of a read with no concurrent write in the lower-bound scenario of Section 4.4. -/
structure ReadExec (n f : ℕ) where
  /-- The register value (the last written value). -/
  val : Bool
  /-- The agents' schedule. -/
  sched : Schedule n f
  /-- Arrival time of the read request at each server. -/
  req : Fin n → ℝ
  /-- Delay of the reply of each server that replies correctly. -/
  dly : Fin n → ℝ
  /-- Replies sent by faulty servers: (sender, value, sending time, delay). -/
  byz : Finset (Fin n × Bool × ℝ × ℝ)

namespace ReadExec

variable (E : ReadExec n f) (t₀ Δ δ γ t : ℝ)

/-- `s` is cured at `τ` (CAM): not faulty, but faulty at some time of `[τ - γ, τ)`. -/
def Cured (s : Fin n) (τ : ℝ) : Prop :=
  ¬ E.sched.Faulty t₀ Δ s τ ∧ ∃ τ' ∈ Set.Ico (τ - γ) τ, E.sched.Faulty t₀ Δ s τ'

/-- `s` is correct at `τ`: neither faulty nor cured. -/
def Correct (s : Fin n) (τ : ℝ) : Prop := ¬ E.sched.Faulty t₀ Δ s τ ∧ ¬ E.Cured t₀ Δ γ s τ

/-- Admissibility of a read invoked at time `t` (synchronous round-free system with delay bound `δ`). -/
structure Admissible : Prop where
  req_mem : ∀ s, t < E.req s ∧ E.req s ≤ t + δ
  dly_mem : ∀ s, 0 < E.dly s ∧ E.dly s ≤ δ
  byz_mem : ∀ m ∈ E.byz, E.sched.Faulty t₀ Δ m.1 m.2.2.1 ∧ 0 < m.2.2.2 ∧ m.2.2.2 ≤ δ

/-- All replies delivered to the reader: (sender, value, delivery time). -/
noncomputable def msgs : Finset (Fin n × Bool × ℝ) :=
  (univ.filter fun s => E.Correct t₀ Δ γ s (E.req s)).image (fun s => (s, E.val, E.req s + E.dly s)) ∪
    E.byz.image fun m => (m.1, m.2.1, m.2.2.1 + m.2.2.2)

/-- The reader's view of a read invoked at `t` that lasts `D`: the replies delivered in `(t, t + D]`. -/
noncomputable def view (D : ℝ) : Finset (Fin n × Bool × ℝ) :=
  (E.msgs t₀ Δ γ).filter fun x => t < x.2.2 ∧ x.2.2 ≤ t + D

end ReadExec

/-- Schedule used in the lower bounds: during period `0` the agents occupy the servers with label
(`s / f`) `a`, during period `1` those with label `b`, during period `2` those with label `c`. -/
def lbSched (hf : 0 < f) (a b c : ℕ) : Schedule n f where
  pos i := univ.filter fun s : Fin n =>
    (i = 0 ∧ s.val / f = a) ∨ (i = 1 ∧ s.val / f = b) ∨ (i = 2 ∧ s.val / f = c)
  card_pos_le i := by
    by_cases h0 : i = 0
    · refine (card_le_card fun s hs => ?_).trans (card_block_le n f a)
      simp only [mem_filter, mem_univ, true_and] at hs
      exact (mem_block hf).2 (by omega)
    by_cases h1 : i = 1
    · refine (card_le_card fun s hs => ?_).trans (card_block_le n f b)
      simp only [mem_filter, mem_univ, true_and] at hs
      exact (mem_block hf).2 (by omega)
    · refine (card_le_card fun s hs => ?_).trans (card_block_le n f c)
      simp only [mem_filter, mem_univ, true_and] at hs
      exact (mem_block hf).2 (by omega)

theorem lbSched_faulty (hf : 0 < f) {a b c : ℕ} {t₀ Δ τ : ℝ} {s : Fin n} :
    (lbSched hf a b c).Faulty t₀ Δ s τ ↔ (period t₀ Δ τ = 0 ∧ s.val / f = a) ∨
      (period t₀ Δ τ = 1 ∧ s.val / f = b) ∨ (period t₀ Δ τ = 2 ∧ s.val / f = c) := by
  simp [Schedule.Faulty, lbSched]

/-- Label of the servers faulty in period `0` of the execution with value `b`. -/
def aL : Bool → ℕ
  | true => 0
  | false => 2

/-- Label of the servers faulty in period `1` of the execution with value `b`. -/
def bL : Bool → ℕ
  | true => 1
  | false => 3

/-- The two indistinguishable executions. Labels (`s / f`): `0`, `1` are the servers faulty in periods
`0`, `1` of `E₁`; `2`, `3` those of `E₀`; label `4` (only if `n > 4f`) are faulty in period `2` of both.
The read starts at `t = t₀ + Δ - μ`, i.e. `μ` before the first move. -/
theorem indist (hf : 0 < f) (hn : n ≤ 5 * f) {t₀ Δ δ γ μ : ℝ} (hδ : 0 < δ) (hμ : 0 < μ)
    (hμδ : μ ≤ δ) (hμΔ : μ ≤ Δ) (hΔ : δ < μ + Δ) (hC : n ≤ 4 * f ∨ μ + Δ < 2 * δ) :
    ∃ E₀ E₁ : ReadExec n f, E₀.Admissible t₀ Δ δ (t₀ + Δ - μ) ∧ E₁.Admissible t₀ Δ δ (t₀ + Δ - μ) ∧
      E₀.val = false ∧ E₁.val = true ∧ E₀.msgs t₀ Δ γ = E₁.msgs t₀ Δ γ := by
  have hΔ0 : 0 < Δ := by linarith
  set t := t₀ + Δ - μ with ht
  have hL : ∀ s : Fin n, s.val / f < 5 := fun s =>
    (Nat.div_lt_iff_lt_mul hf).2 (by have := s.2; omega)
  have hL4 : ∀ s : Fin n, s.val / f = 4 → μ + Δ < 2 * δ := by
    intro s hs
    rcases hC with h | h
    · have := (Nat.div_lt_iff_lt_mul hf).2 (show s.val < 4 * f by have := s.2; omega)
      omega
    · exact h
  -- request times, reply delays, and the common delivery time of each server's (true or fake) reply
  let req : Fin n → ℝ := fun s => if s.val / f = 0 ∨ s.val / f = 2 then t + μ / 2 else t + δ
  let dly : Fin n → ℝ := fun s => if s.val / f = 0 ∨ s.val / f = 2 then μ / 4
    else if s.val / f = 1 ∨ s.val / f = 3 then δ / 2 else δ
  let arr : Fin n → ℝ := fun s => req s + dly s
  -- sending time and delay of the fake reply of a faulty server
  let st : Fin n → ℝ := fun s => if s.val / f = 4 then t₀ + 2 * Δ else req s
  let sd : Fin n → ℝ := fun s => if s.val / f = 4 then arr s - (t₀ + 2 * Δ) else dly s
  have harr : ∀ s, st s + sd s = arr s := by
    intro s; simp only [st, sd]; split_ifs <;> ring
  let mk : Bool → ReadExec n f := fun b =>
    { val := b
      sched := lbSched hf (aL b) (bL b) 4
      req := req
      dly := dly
      byz := (univ.filter fun s : Fin n => s.val / f = aL b ∨ s.val / f = bL b ∨ s.val / f = 4).image
        fun s => (s, !b, st s, sd s) }
  -- periods of the relevant times
  have pA : ∀ s : Fin n, (s.val / f = 0 ∨ s.val / f = 2) → period t₀ Δ (req s) = 0 := by
    intro s hs; simp only [req, hs, ↓reduceIte]
    rw [period_eq_iff hΔ0]; push_cast; constructor <;> linarith
  have pB : ∀ s : Fin n, ¬ (s.val / f = 0 ∨ s.val / f = 2) → period t₀ Δ (req s) = 1 := by
    intro s hs; simp only [req, hs, ↓reduceIte]
    rw [period_eq_iff hΔ0]; push_cast; constructor <;> linarith
  have pC : period t₀ Δ (t₀ + 2 * Δ) = 2 := by
    rw [period_eq_iff hΔ0]; push_cast; constructor <;> linarith
  have hreq : ∀ s, t < req s ∧ req s ≤ t + δ := by
    intro s; simp only [req]; split_ifs <;> constructor <;> linarith
  -- faultiness up to the request time
  have hFreq : ∀ b s, (mk b).sched.Faulty t₀ Δ s (req s) ↔ (s.val / f = aL b ∨ s.val / f = bL b) := by
    intro b s
    have := hL s
    simp only [mk, lbSched_faulty]
    by_cases hA : (s.val / f = 0 ∨ s.val / f = 2)
    · rw [pA s hA]; generalize s.val / f = l at hA this ⊢
      cases b <;> simp only [aL, bL, true_and] <;> omega
    · rw [pB s hA]; generalize s.val / f = l at hA this ⊢
      cases b <;> simp only [aL, bL, true_and] <;> omega
  have hFbefore : ∀ b s τ', τ' ≤ req s → (mk b).sched.Faulty t₀ Δ s τ' →
      (s.val / f = aL b ∨ s.val / f = bL b) := by
    intro b s τ' hτ' h
    have hp := period_mono (t₀ := t₀) hΔ0 hτ'
    simp only [mk, lbSched_faulty] at h
    by_cases hA : (s.val / f = 0 ∨ s.val / f = 2)
    · rw [pA s hA] at hp; generalize s.val / f = l at hA h ⊢
      cases b <;> simp only [aL, bL] at h ⊢ <;> omega
    · rw [pB s hA] at hp; generalize s.val / f = l at hA h ⊢
      cases b <;> simp only [aL, bL] at h ⊢ <;> omega
  -- the servers correct at their request time in the execution with value `b`
  have hcorr : ∀ b s, (mk b).Correct t₀ Δ γ s ((mk b).req s) ↔
      ¬ (s.val / f = aL b ∨ s.val / f = bL b) := by
    intro b s
    simp only [ReadExec.Correct, ReadExec.Cured]
    change ¬ (mk b).sched.Faulty t₀ Δ s (req s) ∧ ¬ (¬ (mk b).sched.Faulty t₀ Δ s (req s) ∧
      ∃ τ' ∈ Set.Ico (req s - γ) (req s), (mk b).sched.Faulty t₀ Δ s τ') ↔ _
    rw [hFreq]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro ⟨-, τ', hτ', h'⟩
      exact h (hFbefore b s τ' hτ'.2.le h')
  -- the messages of the execution with value `b`
  have hmsgs : ∀ b x, x ∈ (mk b).msgs t₀ Δ γ ↔ ∃ s, (s, x.2.1, arr s) = x ∧
      ((x.2.1 = b ∧ ¬ (s.val / f = aL b ∨ s.val / f = bL b)) ∨
        (x.2.1 = !b ∧ (s.val / f = aL b ∨ s.val / f = bL b ∨ s.val / f = 4))) := by
    intro b x
    simp only [ReadExec.msgs, mem_union, mem_image, mem_filter, mem_univ, true_and, hcorr]
    constructor
    · rintro (⟨s, hs, rfl⟩ | ⟨m, hm, rfl⟩)
      · exact ⟨s, rfl, Or.inl ⟨rfl, hs⟩⟩
      · simp only [mk, mem_image, mem_filter, mem_univ, true_and] at hm
        obtain ⟨s, hs, rfl⟩ := hm
        exact ⟨s, by simp [harr], Or.inr ⟨rfl, hs⟩⟩
    · rintro ⟨s, hx, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩
      · left
        refine ⟨s, h4, ?_⟩
        rw [← hx, h3]
      · right
        refine ⟨(s, !b, st s, sd s), ?_, ?_⟩
        · simp only [mk, mem_image, mem_filter, mem_univ, true_and]; exact ⟨s, h4, rfl⟩
        · rw [← hx, h3]; simp [harr]
  refine ⟨mk false, mk true, ?_, ?_, rfl, rfl, ?_⟩
  rotate_right
  · ext x
    rw [hmsgs, hmsgs]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    have := hL s
    generalize s.val / f = l at this ⊢
    cases x.2.1 <;> simp [aL, bL] <;> omega
  all_goals
    refine ⟨hreq, fun s => ?_, ?_⟩
    · simp only [mk, dly]; split_ifs <;> constructor <;> linarith
    · intro m hm
      simp only [mk, mem_image, mem_filter, mem_univ, true_and] at hm
      obtain ⟨s, hs, rfl⟩ := hm
      simp only [mk, lbSched_faulty]
      by_cases h4 : (s.val / f = 4)
      · have := hL4 s h4
        simp only [st, sd, arr, req, dly, h4]
        norm_num
        refine ⟨Or.inr (Or.inr pC), ?_, ?_⟩ <;> linarith
      · simp only [st, sd, h4, ↓reduceIte]
        by_cases hA : (s.val / f = 0 ∨ s.val / f = 2)
        · refine ⟨Or.inl ⟨pA s hA, ?_⟩, ?_⟩
          · generalize s.val / f = l at hs hA h4 ⊢
            simp only [aL, bL] at hs ⊢; omega
          · simp only [dly, hA, ↓reduceIte]; constructor <;> linarith
        · refine ⟨Or.inr (Or.inl ⟨pB s hA, ?_⟩), ?_⟩
          · generalize s.val / f = l at hs hA h4 ⊢
            simp only [aL, bL] at hs ⊢; omega
          · have hB : s.val / f = 1 ∨ s.val / f = 3 := by
              generalize s.val / f = l at hs hA h4 ⊢
              simp only [aL, bL] at hs; omega
            simp only [dly, hA, ↓reduceIte, hB, ↓reduceIte]; constructor <;> linarith

/-- From two executions with different values and equal message sets, any reader fails in one. -/
theorem fooled_of_indist {t₀ Δ δ γ t : ℝ} {E₀ E₁ : ReadExec n f}
    (h₀ : E₀.Admissible t₀ Δ δ t) (h₁ : E₁.Admissible t₀ Δ δ t) (hv₀ : E₀.val = false)
    (hv₁ : E₁.val = true) (hm : E₀.msgs t₀ Δ γ = E₁.msgs t₀ Δ γ) (D : ℝ)
    (dec : Finset (Fin n × Bool × ℝ) → Bool) :
    ∃ E : ReadExec n f, E.Admissible t₀ Δ δ t ∧ dec (E.view t₀ Δ γ t D) ≠ E.val := by
  have hv : E₀.view t₀ Δ γ t D = E₁.view t₀ Δ γ t D := by simp only [ReadExec.view, hm]
  cases h : dec (E₁.view t₀ Δ γ t D)
  · exact ⟨E₁, h₁, by rw [h, hv₁]; decide⟩
  · exact ⟨E₀, h₀, by rw [hv, h, hv₀]; decide⟩

/-- **Theorem 3** (repaired, in the model of Section 4.4): if `δ ≤ Δ < 2δ` and `n ≤ 5f` (`f ≥ 1`), no
reader can implement a safe register in the `(ΔS, CAM)` model: for every read duration `D` and every
decision rule `dec` there is an admissible read with no concurrent write whose result differs from the
register value. -/
theorem theorem3 (hf : 0 < f) (hn : n ≤ 5 * f) {t₀ Δ δ γ : ℝ} (hδ : 0 < δ)
    (h1 : δ ≤ Δ) (h2 : Δ < 2 * δ) (D : ℝ) (dec : Finset (Fin n × Bool × ℝ) → Bool) :
    ∃ (E : ReadExec n f) (t : ℝ), E.Admissible t₀ Δ δ t ∧ dec (E.view t₀ Δ γ t D) ≠ E.val := by
  obtain ⟨E₀, E₁, h₀, h₁, hv₀, hv₁, hm⟩ := indist (t₀ := t₀) (Δ := Δ) (δ := δ) (γ := γ) (μ := (2 * δ - Δ) / 2) hf hn
    hδ (by linarith) (by linarith) (by linarith) (by linarith) (Or.inr (by linarith))
  obtain ⟨E, hE, hd⟩ := fooled_of_indist h₀ h₁ hv₀ hv₁ hm D dec
  exact ⟨E, _, hE, hd⟩

/-- **Theorem 5** (repaired, in the model of Section 4.4): if `2δ ≤ Δ < 3δ` and `n ≤ 4f` (`f ≥ 1`), no
reader can implement a safe register in the `(ΔS, CAM)` model. (The proof only uses `Δ ≥ δ/2`.) -/
theorem theorem5 (hf : 0 < f) (hn : n ≤ 4 * f) {t₀ Δ δ γ : ℝ} (hδ : 0 < δ)
    (h1 : 2 * δ ≤ Δ) (D : ℝ) (dec : Finset (Fin n × Bool × ℝ) → Bool) :
    ∃ (E : ReadExec n f) (t : ℝ), E.Admissible t₀ Δ δ t ∧ dec (E.view t₀ Δ γ t D) ≠ E.val := by
  obtain ⟨E₀, E₁, h₀, h₁, hv₀, hv₁, hm⟩ := indist (t₀ := t₀) (Δ := Δ) (δ := δ) (γ := γ) (μ := δ / 2) hf (by omega)
    hδ (by linarith) (by linarith) (by linarith) (by linarith) (Or.inl hn)
  obtain ⟨E, hE, hd⟩ := fooled_of_indist h₀ h₁ hv₀ hv₁ hm D dec
  exact ⟨E, _, hE, hd⟩

end Podc.MobileByzantineStorage
