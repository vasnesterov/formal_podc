import Papers.PODC2025.LanguageDecidability.Canonical

/-!
# Generic facts about executions and their inputs

Algorithm-independent lemmas used in the proof of Lemma 5.3 (`CounterA.lean`):

* `symCount s t` — the number of send/receive events before time `t`; at a send/receive event
  `t`, the symbol produced is `x (symCount s t)` (`IsInput.sym_eq`).
* `IsExec.exists_next` — every process takes a further step, and its program counter does not
  change before that step; `IsExec.exists_send`, `IsExec.exists_sym`.
* `wf_of_exec` — the input of every (fair, failure-free) execution is well-formed
  (Definition 2.1); this is implicit in the paper.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type}

/-- `ι` enumerates the send/receive events of `s`, which produce the input `x`. -/
structure IsInput (s : ℕ → Ev I O) (x : Word I O) (ι : ℕ → ℕ) : Prop where
  mono : StrictMono ι
  cover : ∀ t, (s t).sym.isSome → ∃ k, ι k = t
  sym : ∀ k, (s (ι k)).sym = some (x k)

lemma hasInput_iff {s : ℕ → Ev I O} {x : Word I O} : HasInput s x ↔ ∃ ι, IsInput s x ι :=
  ⟨fun ⟨ι, a, b, c⟩ => ⟨ι, a, b, c⟩, fun ⟨ι, ⟨a, b, c⟩⟩ => ⟨ι, a, b, c⟩⟩

/-- The number of send/receive events before time `t`. -/
def symCount (s : ℕ → Ev I O) (t : ℕ) : ℕ := Nat.count (fun t' => (s t').sym.isSome = true) t

lemma symCount_succ (s : ℕ → Ev I O) (t : ℕ) :
    symCount s (t + 1) = symCount s t + if (s t).sym.isSome = true then 1 else 0 := by
  simp only [symCount, Nat.count_succ]

lemma symCount_succ_of_isSome {s : ℕ → Ev I O} {t : ℕ} (h : (s t).sym.isSome = true) :
    symCount s (t + 1) = symCount s t + 1 := by
  rw [symCount_succ]; simp [h]

lemma symCount_succ_of_isNone {s : ℕ → Ev I O} {t : ℕ} (h : (s t).sym = none) :
    symCount s (t + 1) = symCount s t := by
  rw [symCount_succ]; simp [h]

lemma symCount_mono (s : ℕ → Ev I O) : Monotone (symCount s) := Nat.count_monotone _

lemma Ev.sym_fst {e : Ev I O} {a : Sym I O} (h : e.sym = some a) : a.1 = e.proc := by
  cases e <;> simp [Ev.sym] at h <;> subst h <;> rfl

namespace IsInput

variable {s : ℕ → Ev I O} {x : Word I O} {ι : ℕ → ℕ}

lemma symCount_iota (h : IsInput s x ι) (k : ℕ) : symCount s (ι k) = k := by
  rw [symCount, Nat.count_eq_card_filter_range]
  have : (Finset.range (ι k)).filter (fun t' => (s t').sym.isSome = true) =
      (Finset.range k).image ι := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ht, hs⟩
      obtain ⟨j, rfl⟩ := h.cover t hs
      exact ⟨j, h.mono.lt_iff_lt.1 ht, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨h.mono hj, by simp [h.sym j]⟩
  rw [this, Finset.card_image_of_injective _ h.mono.injective, Finset.card_range]

/-- At a send/receive event, the produced symbol is `x (symCount s t)`. -/
lemma sym_eq (h : IsInput s x ι) {t : ℕ} (ht : (s t).sym.isSome = true) :
    (s t).sym = some (x (symCount s t)) := by
  obtain ⟨k, rfl⟩ := h.cover t ht
  rw [h.symCount_iota, h.sym]

lemma iota_symCount (h : IsInput s x ι) {t : ℕ} (ht : (s t).sym.isSome = true) :
    ι (symCount s t) = t := by
  obtain ⟨k, rfl⟩ := h.cover t ht
  rw [h.symCount_iota]

lemma lt_symCount (h : IsInput s x ι) {k t : ℕ} (ht : ι k < t) : k < symCount s t := by
  have h1 : symCount s (ι k + 1) = k + 1 := by
    rw [symCount_succ_of_isSome (by simp [h.sym k]), h.symCount_iota]
  have := symCount_mono s (show ι k + 1 ≤ t by omega)
  omega

lemma symCount_le (h : IsInput s x ι) {k t : ℕ} (ht : t ≤ ι k) : symCount s t ≤ k := by
  have := symCount_mono s ht
  rwa [h.symCount_iota] at this

end IsInput

/-! ### Program counters -/

variable {s : ℕ → Ev I O}

lemma phs_succ (s : ℕ → Ev I O) (t : ℕ) : phs s (t + 1) = phStep (phs s t) (s t) := rfl

lemma phs_succ_of_ne {t : ℕ} {p : Fin n} (h : (s t).proc ≠ p) : phs s (t + 1) p = phs s t p :=
  phStep_of_ne (Ne.symm h)

lemma phs_const {t t' : ℕ} {p : Fin n} (htt : t ≤ t')
    (h : ∀ u, t ≤ u → u < t' → (s u).proc ≠ p) : phs s t' p = phs s t p := by
  induction t', htt using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    rw [phs_succ_of_ne (h u hu (by omega)), ih (fun v h1 h2 => h v h1 (by omega))]

/-- Every process takes a further step; its program counter is unchanged until then. -/
lemma IsExec.exists_next (hs : IsExec s) (p : Fin n) (t : ℕ) :
    ∃ t', t ≤ t' ∧ (s t').proc = p ∧ phs s t' p = phs s t p := by
  classical
  have hex : ∃ u, t ≤ u ∧ (s u).proc = p := by
    obtain ⟨u, hu, w, hw⟩ := hs.fair p t
    exact ⟨u, hu, by rw [hw]; rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  exact phs_const (Nat.find_spec hex).1 fun u h1 h2 h3 => Nat.find_min hex h2 ⟨h1, h3⟩

/-- The step of process `p` enabled by its program counter. -/
lemma IsExec.ev_of_phase (hs : IsExec s) {t : ℕ} {p : Fin n} (hp : (s t).proc = p) :
    (phs s t p = .idle → ∃ v, s t = .pre p v) ∧
    (∀ v, phs s t p = .ready v → s t = .send p v) ∧
    (phs s t p = .waiting → ∃ w, s t = .recv p w) ∧
    (∀ w, phs s t p = .got w → s t = .post p w) := by
  have hv := hs.valid t
  rcases h : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> rw [h] at hp hv <;>
    simp only [Ev.proc] at hp <;> subst hp <;> simp only [Enabled, Ev.need, Ev.proc] at hv <;>
    rw [hv] <;> simp

lemma IsExec.exists_send (hs : IsExec s) {t : ℕ} {p : Fin n} {v : I p}
    (h : phs s t p = .ready v) : ∃ t', t ≤ t' ∧ s t' = .send p v := by
  obtain ⟨t', ht, hp, hph⟩ := hs.exists_next p t
  exact ⟨t', ht, (hs.ev_of_phase hp).2.1 v (hph.trans h)⟩

lemma IsExec.exists_post (hs : IsExec s) {t : ℕ} {p : Fin n} {w : O p}
    (h : phs s t p = .got w) : ∃ t', t ≤ t' ∧ s t' = .post p w := by
  obtain ⟨t', ht, hp, hph⟩ := hs.exists_next p t
  exact ⟨t', ht, (hs.ev_of_phase hp).2.2.2 w (hph.trans h)⟩

lemma IsExec.exists_send_of_idle (hs : IsExec s) {t : ℕ} {p : Fin n} (h : phs s t p = .idle) :
    ∃ t', t ≤ t' ∧ ∃ v, s t' = .send p v := by
  obtain ⟨t', ht, hp, hph⟩ := hs.exists_next p t
  obtain ⟨v, hv⟩ := (hs.ev_of_phase hp).1 (hph.trans h)
  have : phs s (t' + 1) p = .ready v := by rw [phs_succ, hv]; simp
  obtain ⟨t'', ht'', h''⟩ := hs.exists_send this
  exact ⟨t'', by omega, v, h''⟩

/-- Every process has send/receive events arbitrarily late. -/
lemma IsExec.exists_sym (hs : IsExec s) (p : Fin n) (t : ℕ) :
    ∃ t', t ≤ t' ∧ (s t').proc = p ∧ (s t').sym.isSome = true := by
  obtain ⟨t', ht, hp, -⟩ := hs.exists_next p t
  rcases h : s t' with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> rw [h] at hp <;>
    simp only [Ev.proc] at hp <;> subst hp
  · have : phs s (t' + 1) q = .ready v := by rw [phs_succ, h]; simp
    obtain ⟨t'', ht'', h''⟩ := hs.exists_send this
    exact ⟨t'', by omega, by rw [h'']; rfl, by rw [h'']; rfl⟩
  · exact ⟨t', ht, by rw [h]; rfl, by rw [h]; rfl⟩
  · exact ⟨t', ht, by rw [h]; rfl, by rw [h]; rfl⟩
  · have : phs s (t' + 1) q = .idle := by rw [phs_succ, h]; simp
    obtain ⟨t'', ht'', v, h''⟩ := hs.exists_send_of_idle this
    exact ⟨t'', by omega, by rw [h'']; rfl, by rw [h'']; rfl⟩

/-! ### The input of an execution is well-formed -/

/-- The program counter is not waiting for a response. -/
def PhEven {A B : Type} : Phase A B → Prop
  | .waiting => False
  | _ => True

lemma parity_inv (hs : IsExec s) {x : Word I O} {ι : ℕ → ℕ} (hx : IsInput s x ι) :
    ∀ t p, (Even (cnt x p (symCount s t)) ↔ PhEven (phs s t p)) := by
  intro t
  induction t with
  | zero => intro p; simp [symCount, cnt, phs, PhEven]
  | succ t ih =>
    intro p
    by_cases hp : (s t).proc = p
    · have hv := hs.valid t
      rcases h : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> rw [h] at hp hv <;>
        simp only [Ev.proc] at hp <;> subst hp <;>
        simp only [Enabled, Ev.need, Ev.proc] at hv <;> have ih := ih q <;> rw [hv] at ih
      · rw [symCount_succ_of_isNone (by rw [h]; rfl), phs_succ, h]; simpa [PhEven] using ih
      · have hs' : (s t).sym.isSome = true := by rw [h]; rfl
        have hxk := hx.sym_eq hs'
        rw [h] at hxk; simp only [Ev.sym, Option.some.injEq] at hxk
        rw [symCount_succ_of_isSome hs', phs_succ, h, cnt_succ, ← hxk]
        simp only [ite_true, phStep_send_self, PhEven, iff_false, Nat.not_even_iff_odd,
          Nat.odd_add_one, Nat.not_odd_iff_even]
        simpa [PhEven] using ih
      · have hs' : (s t).sym.isSome = true := by rw [h]; rfl
        have hxk := hx.sym_eq hs'
        rw [h] at hxk; simp only [Ev.sym, Option.some.injEq] at hxk
        rw [symCount_succ_of_isSome hs', phs_succ, h, cnt_succ, ← hxk]
        simp only [ite_true, phStep_recv_self, PhEven, iff_true, Nat.even_add_one]
        simpa [PhEven] using ih
      · rw [symCount_succ_of_isNone (by rw [h]; rfl), phs_succ, h]; simpa [PhEven] using ih
    · rw [phs_succ_of_ne hp]
      have hc : cnt x p (symCount s (t + 1)) = cnt x p (symCount s t) := by
        rw [symCount_succ]
        split_ifs with hsome
        · have hq : (x (symCount s t)).1 ≠ p := by
            rw [Ev.sym_fst (hx.sym_eq hsome)]; exact hp
          simp [cnt_succ, hq]
        · rfl
      rw [hc]; exact ih p

-- CSLib candidate
/-- The input of a fair failure-free execution is well-formed (implicit in the paper). -/
theorem wf_of_exec {x : Word I O} (hs : IsExec s) (hx : HasInput s x) : WF x := by
  obtain ⟨ι, hι⟩ := hasInput_iff.1 hx
  refine ⟨fun p N => ?_, fun m => ?_⟩
  · obtain ⟨t', ht', hp, hsome⟩ := hs.exists_sym p (ι N + 1)
    obtain ⟨m, rfl⟩ := hι.cover t' hsome
    refine ⟨m, ?_, ?_⟩
    · by_contra hlt; push Not at hlt
      have := hι.mono hlt; omega
    · rw [← hp]; exact Ev.sym_fst (hι.sym m)
  · have hv := hs.valid (ι m)
    have hsym := hι.sym m
    have hpar := parity_inv hs hι (ι m)
    rw [hι.symCount_iota] at hpar
    rcases h : s (ι m) with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩ <;> rw [h] at hv hsym <;>
      simp only [Ev.sym, reduceCtorEq, Option.some.injEq] at hsym <;> rw [← hsym] <;>
      simp only [Enabled, Ev.need, Ev.proc] at hv
    · rw [hpar q, hv]; simp [PhEven]
    · rw [hpar q, hv]; simp [PhEven]

end Podc2025.LanguageDecidability
