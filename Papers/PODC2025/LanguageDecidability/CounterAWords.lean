import Papers.PODC2025.LanguageDecidability.CounterDefs

/-!
# Sequential counter words used for Lemma 5.2 and for `SEC_COUNT ∉ RTO`

* `seqW op` — the sequential history of the operations `op 0, op 1, …` (each operation is a
  process, an invocation and a response; the invocation of `op u` is at `2u`, its response at
  `2u + 1`); it is well-formed if every process has infinitely many operations (`wf_seqW`).
* `cw hn f` — process `0` increments once, then the processes read in round-robin
  (the `u`-th read is by process `u mod n` and returns `f u (u mod n)`).
* `cw hn gBad` — process `0` reads `1`, every other process reads `0` forever: not in
  `WEC_COUNT` for `n ≥ 2` (property (3) fails), `cw_bad_not_mem`.
* `cw hn (gGood J)` — the same for the first `J` reads, then every read returns `1`:
  in `SEC_COUNT ⊆ WEC_COUNT` (`cw_good_mem`).

The paper's word `<⁺₁ >₁ <₂ >⁰₂ <₁ >⁰₁ …` (proof of Lemma 5.2) cannot be used: `p₁` reads `0`
after its own completed `inc`, which violates property (1), so its continuations
`x(F) <₁ >¹₁ <₂ >¹₂ …` are not in `WEC_COUNT` either. In `cw hn gBad`, the incrementing process
reads `1`.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability

variable {n : ℕ}

lemma invAt_unique {x : CWord n} {r i i' : ℕ} (h : invAt x r i) (h' : invAt x r i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hlt
  · exact absurd h'.2.1 (h.2.2 i' hlt h'.1)
  · exact heq
  · exact absurd h.2.1 (h'.2.2 i hlt h.1)

lemma ownIncs_le_incs (x : CWord n) (p : Fin n) : ∀ m, ownIncs x p m ≤ incs x m
  | 0 => le_rfl
  | m + 1 => by
    have := ownIncs_le_incs x p m
    simp only [ownIncs, incs]
    by_cases h : IsInc (x m) <;> by_cases h' : (x m).1 = p <;> simp [h, h'] <;> omega

/-! ### Sequential words -/

/-- The sequential history of the operations `op u = (process, invocation, response)`. -/
def seqW (op : ℕ → Fin n × CInv × CRes) : CWord n := fun m =>
  if m % 2 = 0 then ⟨(op (m / 2)).1, .inl (op (m / 2)).2.1⟩
  else ⟨(op (m / 2)).1, .inr (op (m / 2)).2.2⟩

section seqW

variable {op : ℕ → Fin n × CInv × CRes}

lemma seqW_even (u : ℕ) : seqW op (2 * u) = ⟨(op u).1, .inl (op u).2.1⟩ := by
  simp [seqW]

lemma seqW_odd (u : ℕ) : seqW op (2 * u + 1) = ⟨(op u).1, .inr (op u).2.2⟩ := by
  have h1 : (2 * u + 1) % 2 = 1 := by omega
  have h2 : (2 * u + 1) / 2 = u := by omega
  simp [seqW, h1, h2]

lemma seqW_fst (m : ℕ) : (seqW op m).1 = (op (m / 2)).1 := by
  unfold seqW; split_ifs <;> rfl

lemma seqW_eq_inr {r : ℕ} {p : Fin n} {w : CRes} (h : seqW op r = ⟨p, .inr w⟩) :
    ∃ u, r = 2 * u + 1 ∧ (op u).1 = p ∧ (op u).2.2 = w := by
  obtain ⟨u, rfl | rfl⟩ : ∃ u, r = 2 * u ∨ r = 2 * u + 1 := ⟨r / 2, by omega⟩
  · rw [seqW_even] at h; simp at h
  · rw [seqW_odd] at h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact ⟨u, rfl, rfl, by simpa using h2⟩

lemma isInc_seqW {m : ℕ} : IsInc (seqW op m) ↔ m % 2 = 0 ∧ (op (m / 2)).2.1 = .inc := by
  unfold IsInc seqW; split_ifs with h <;> simp [h]

lemma cnt_seqW_even (q : Fin n) : ∀ u, Even (cnt (seqW op) q (2 * u))
  | 0 => by simp [cnt]
  | u + 1 => by
    have e : 2 * (u + 1) = 2 * u + 1 + 1 := by ring
    have ih := cnt_seqW_even q u
    rw [e, cnt_succ, cnt_succ, seqW_odd, seqW_even]
    by_cases h : (op u).1 = q
    · simp only [h, ite_true]
      rw [add_assoc]; exact ih.add (by decide)
    · simp only [h, ite_false, add_zero]; exact ih

lemma wf_seqW (hrel : ∀ q N, ∃ u, N ≤ u ∧ (op u).1 = q) : WF (seqW op) := by
  refine ⟨fun q N => ?_, fun m => ?_⟩
  · obtain ⟨u, hu, hq⟩ := hrel q N
    exact ⟨2 * u, by omega, by rw [seqW_fst]; simpa using hq⟩
  · obtain ⟨u, rfl | rfl⟩ : ∃ u, m = 2 * u ∨ m = 2 * u + 1 := ⟨m / 2, by omega⟩
    · rw [seqW_even]; simpa using cnt_seqW_even (op := op) (op u).1 u
    · rw [seqW_odd, cnt_succ, seqW_even]
      simp only [ite_true, Sum.isLeft_inr, Bool.false_eq_true, false_iff, Nat.even_add_one,
        not_not]
      exact cnt_seqW_even _ u

lemma invAt_seqW {u i : ℕ} (h : invAt (seqW op) (2 * u + 1) i) : i = 2 * u := by
  refine invAt_unique h ⟨by omega, ?_, fun m h1 h2 => by omega⟩
  rw [seqW_fst, seqW_fst]; congr 2; omega

lemma typed_seqW (h : ∀ u, ((op u).2.1 = .inc ∧ (op u).2.2 = .ack) ∨
    ((op u).2.1 = .read ∧ ∃ v, (op u).2.2 = .val v)) : Typed (seqW op) := by
  intro r i p w hr hi
  obtain ⟨u, rfl, hp, hw⟩ := seqW_eq_inr hr
  rw [invAt_seqW hi, seqW_even, hp, ← hw]
  rcases h u with ⟨h1, h2⟩ | ⟨h1, v, h2⟩
  · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
  · right; rw [h1, h2]; exact ⟨rfl, v, rfl⟩

end seqW

/-! ### One `inc`, then round-robin reads -/

/-- Process `0` increments, then the `u`-th read is by process `u mod n` and returns
`f u (u mod n)`. -/
def opA (hn : 0 < n) (f : ℕ → Fin n → ℕ) : ℕ → Fin n × CInv × CRes
  | 0 => (⟨0, hn⟩, .inc, .ack)
  | u + 1 => (⟨u % n, Nat.mod_lt _ hn⟩, .read, .val (f u ⟨u % n, Nat.mod_lt _ hn⟩))

/-- The word of `opA`. -/
def cw (hn : 0 < n) (f : ℕ → Fin n → ℕ) : CWord n := seqW (opA hn f)

section cw

variable (hn : 0 < n) (f : ℕ → Fin n → ℕ)

lemma cw_zero : cw hn f 0 = ⟨⟨0, hn⟩, .inl .inc⟩ := by
  rw [cw]; exact seqW_even (op := opA hn f) 0

lemma cw_read (u : ℕ) : cw hn f (2 * u + 2) = ⟨⟨u % n, Nat.mod_lt _ hn⟩, .inl .read⟩ := by
  rw [show 2 * u + 2 = 2 * (u + 1) by ring, cw, seqW_even]; rfl

lemma cw_val (u : ℕ) : cw hn f (2 * u + 3) =
    ⟨⟨u % n, Nat.mod_lt _ hn⟩, .inr (.val (f u ⟨u % n, Nat.mod_lt _ hn⟩))⟩ := by
  rw [show 2 * u + 3 = 2 * (u + 1) + 1 by ring, cw, seqW_odd]; rfl

lemma cw_wf : WF (cw hn f) := by
  refine wf_seqW fun q N => ⟨n * N + q.val + 1, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_left N hn; omega
  · simp only [opA]; ext; simp [Nat.mod_eq_of_lt q.isLt]

lemma cw_typed : Typed (cw hn f) := by
  refine typed_seqW fun u => ?_
  cases u with
  | zero => left; exact ⟨rfl, rfl⟩
  | succ u => right; exact ⟨rfl, _, rfl⟩

lemma isInc_cw {m : ℕ} : IsInc (cw hn f m) ↔ m = 0 := by
  rw [cw, isInc_seqW]
  constructor
  · rintro ⟨h1, h2⟩
    rcases hm : m / 2 with _ | k
    · omega
    · rw [hm] at h2; simp [opA] at h2
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma incs_cw : ∀ m, incs (cw hn f) m = if m = 0 then 0 else 1
  | 0 => rfl
  | m + 1 => by
    rw [incs, incs_cw m]
    by_cases h : m = 0
    · subst h; simp [(isInc_cw hn f).2 rfl]
    · simp [h, (isInc_cw hn f).not.2 h]

lemma ownIncs_cw_of_ne {q : Fin n} (hq : q.val ≠ 0) : ∀ m, ownIncs (cw hn f) q m = 0
  | 0 => rfl
  | m + 1 => by
    rw [ownIncs, ownIncs_cw_of_ne hq m]
    by_cases h : m = 0
    · subst h; rw [cw_zero]
      have : (⟨0, hn⟩ : Fin n) ≠ q := fun e => hq (by rw [← e])
      simp [this]
    · simp [(isInc_cw hn f).not.2 h]

lemma cw_eq_val {r : ℕ} {p : Fin n} {v : ℕ} (h : cw hn f r = ⟨p, .inr (.val v)⟩) :
    ∃ u, r = 2 * u + 3 ∧ p = ⟨u % n, Nat.mod_lt _ hn⟩ ∧ v = f u p := by
  obtain ⟨u', rfl, hp, hw⟩ := seqW_eq_inr h
  cases u' with
  | zero => simp [opA] at hw
  | succ u =>
    simp only [opA] at hp hw
    subst hp
    exact ⟨u, by ring, rfl, by simpa using hw.symm⟩

lemma cw_wec1 (hf : ∀ u, 1 ≤ f u ⟨0, hn⟩) : WEC1 (cw hn f) := by
  intro r p v h
  obtain ⟨u, -, -, rfl⟩ := cw_eq_val hn f h
  by_cases hp : p.val = 0
  · have : p = ⟨0, hn⟩ := Fin.ext hp
    subst this
    have h1 := ownIncs_le_incs (cw hn f) ⟨0, hn⟩ r
    rw [incs_cw] at h1
    have := hf u
    split_ifs at h1 <;> omega
  · rw [ownIncs_cw_of_ne hn f hp]; exact Nat.zero_le _

lemma cw_wec2 (hf : ∀ q u u', u ≤ u' → f u q ≤ f u' q) : WEC2 (cw hn f) := by
  intro r r' p v v' hlt h' h
  obtain ⟨u, rfl, -, rfl⟩ := cw_eq_val hn f h
  obtain ⟨u', rfl, -, rfl⟩ := cw_eq_val hn f h'
  exact hf p _ _ (by omega)

lemma cw_finIncs : FinIncs (cw hn f) 1 :=
  ⟨1, by rw [incs_cw]; rfl, fun m hm h => by rw [isInc_cw] at h; omega⟩

lemma cw_evReads {J S : ℕ} (hf : ∀ u, J ≤ u → ∀ q, f u q = S) : EvReads (cw hn f) S :=
  ⟨2 * J + 3, fun r p v hr h => by
    obtain ⟨u, rfl, -, rfl⟩ := cw_eq_val hn f h
    exact hf u (by omega) p⟩

lemma cw_sec4 (hf : ∀ u q, f u q ≤ 1) : SEC4 (cw hn f) := by
  intro r p v h
  obtain ⟨u, rfl, -, rfl⟩ := cw_eq_val hn f h
  rw [incs_cw]; simpa using hf u p

end cw

/-- Process `0` reads `1`, every other process reads `0`. -/
def gBad (_ : ℕ) (q : Fin n) : ℕ := if q.val = 0 then 1 else 0

/-- As `gBad` for the first `J` reads, then every read returns `1`. -/
def gGood (J u : ℕ) (q : Fin n) : ℕ := if u < J then gBad u q else 1

/-- The word `cw hn gBad` is not in `WEC_COUNT` (for `n ≥ 2`): property (3) fails. -/
lemma cw_bad_not_wec3 (hn2 : 1 < n) : ¬ WEC3 (cw (by omega) (gBad (n := n))) := by
  rintro ⟨S, -, N, hN⟩
  have hn : 0 < n := by omega
  have hNn := Nat.le_mul_of_pos_left N hn
  have h0 := hN (2 * (n * N) + 3) _ _ (by omega) (cw_val hn gBad (n * N))
  have h1 := hN (2 * (n * N + 1) + 3) _ _ (by omega) (cw_val hn gBad (n * N + 1))
  simp only [gBad, Nat.mul_mod_right, ite_true] at h0
  have : (n * N + 1) % n = 1 := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hn2]
  simp only [gBad, this, one_ne_zero, ite_false] at h1
  omega

lemma cw_bad_not_mem (hn2 : 1 < n) : cw (by omega) (gBad (n := n)) ∉ (WEC : Set (CWord n)) :=
  fun h => cw_bad_not_wec3 hn2 h.2.2.2.2

/-- The word `cw hn (gGood J)` is in `SEC_COUNT`. -/
lemma cw_good_mem (hn : 0 < n) (J : ℕ) : cw hn (gGood J) ∈ (SEC : Set (CWord n)) := by
  refine ⟨⟨cw_wf hn _, cw_typed hn _, cw_wec1 hn _ fun u => ?_, cw_wec2 hn _ fun q u u' h => ?_,
    1, cw_finIncs hn _, cw_evReads hn _ (J := J) fun u hu q => ?_⟩, cw_sec4 hn _ fun u q => ?_⟩
  · simp only [gGood, gBad]; split_ifs <;> simp
  · simp only [gGood, gBad]; split_ifs <;> omega
  · simp only [gGood]; simp [show ¬ u < J by omega]
  · simp only [gGood, gBad]; split_ifs <;> simp

/-- `cw hn (gGood J)` and `cw hn gBad` agree on the first `2 J + 2` symbols. -/
lemma cw_good_agree (hn : 0 < n) (J : ℕ) :
    ∀ m < 2 * J + 2, cw hn (gGood J) m = cw hn (gBad (n := n)) m := by
  intro m hm
  have hop : opA hn (gGood J) (m / 2) = opA hn (gBad (n := n)) (m / 2) := by
    rcases h : m / 2 with _ | u
    · rfl
    · simp only [opA, gGood]; simp [show u < J by omega]
  simp only [cw, seqW, hop]

end Podc2025.LanguageDecidability.Counter
