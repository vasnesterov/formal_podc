import Papers.PODC2025.ByzantineDownload.StaticDownload
import Papers.PODC2025.ByzantineDownload.Counting

/-!
# Correctness and complexity of Algorithm 6 (Lemmas 5.2–5.8, Theorem 5.9)
-/

set_option linter.unusedSectionVars false

namespace Podc.ByzantineDownload.Static

open Protocol

variable {k n : ℕ} [NeZero k]

/-! ### Basic facts about the model -/

lemma Pattern.alive_mono {π : Pattern k} {p : Fin k} {r r' : ℕ} (h : π.alive p r) (hr : r' ≤ r) :
    π.alive p r' := by
  unfold Pattern.alive at *
  split at * <;> simp_all; omega

lemma Pattern.alive_of_delivers {π : Pattern k} {p q : Fin k} {r : ℕ}
    (h : π.delivers p q (r + 1)) : π.alive p r := by
  unfold Pattern.alive Pattern.delivers at *
  split at * <;> simp_all; omega

lemma Pattern.delivers_of_alive {π : Pattern k} {p q : Fin k} {r : ℕ} (h : π.alive p r) :
    π.delivers p q r := by
  unfold Pattern.alive Pattern.delivers at *
  split at * <;> simp_all

lemma Pattern.alive_of_nonfaulty {π : Pattern k} {p : Fin k} (h : π.Nonfaulty p) (r : ℕ) :
    π.alive p r := by
  unfold Pattern.alive; rw [h]

lemma Pattern.alive_zero_of {π : Pattern k} {p : Fin k} (h : ∀ c, π.crash p = some c → 0 < c) :
    π.alive p 0 := by
  unfold Pattern.alive; split <;> simp_all

lemma Pattern.mem_faulty {π : Pattern k} {p : Fin k} : p ∈ π.faulty ↔ ¬ π.Nonfaulty p := by
  simp [Pattern.faulty, Pattern.Nonfaulty, Option.isSome_iff_ne_none]

/-- A peer that is alive at round `r` but not at round `r + 1` crashes in round `r + 1`. -/
lemma Pattern.crash_eq_of_alive {π : Pattern k} {p : Fin k} {r : ℕ} (h : π.alive p r)
    (h' : ¬ π.alive p (r + 1)) : π.crash p = some (r + 1) := by
  unfold Pattern.alive at *
  split at * <;> simp_all; omega

/-! ### Prefix arrays -/

/-- The output array that knows exactly the bits `< I`. -/
def pre (X : Fin n → Bool) (I : ℕ) : Fin n → Option Bool :=
  fun i => if i.val < I then some (X i) else none

lemma get_pre_self (X : Fin n → Bool) (I : ℕ) : get (pre X I) I = none := by
  unfold get pre; split <;> simp

lemma set_pre (X : Fin n → Bool) (I : ℕ) (h : I < n) :
    set (pre X I) I (X ⟨I, h⟩) = pre X (I + 1) := by
  funext i
  unfold set pre
  by_cases hi : i.val = I
  · have : i = ⟨I, h⟩ := Fin.ext hi
    subst this; simp
  · simp only [hi, ite_false]
    by_cases h2 : i.val < I
    · simp [h2, show i.val < I + 1 by omega]
    · simp [h2, show ¬ i.val < I + 1 by omega]

lemma get_pre_succ (X : Fin n → Bool) (I : ℕ) (h : I < n) :
    get (pre X (I + 1)) I = some (X ⟨I, h⟩) := by
  unfold get pre; simp [h]

lemma pre_n (X : Fin n → Bool) : pre X n = fun i => some (X i) := by
  funext i; simp [pre, i.isLt]

lemma set_pre_succ (X : Fin n → Bool) (I : ℕ) (h : I < n) :
    set (pre X (I + 1)) I (X ⟨I, h⟩) = pre X (I + 1) := by
  rw [← set_pre X I h]
  funext i; unfold set; split <;> simp_all

lemma get_pre_lt (X : Fin n → Bool) (I i : ℕ) (h : i < n) (hi : i < I) :
    get (pre X I) i = some (X ⟨i, h⟩) := by
  unfold get pre; simp [h, hi]

/-! ### One round inside a view -/

section Exec

variable (X : Fin n → Bool) (π : Pattern k) (f : ℕ)

/-- The state of a peer inside a view that started in the (common) state `σ`: iteration `s`,
and `b` = whether it knows `b_I`. -/
def mid (σ : St k n) (s : ℕ) (b : Bool) : St k n :=
  { σ with j := s, res := pre X (if b then σ.I + 1 else σ.I) }

/-- Whether `p` knows `b_I` after the query sub-round of iteration `s` (the leader queries at
iteration `0`). -/
def kq (σ : St k n) (s : ℕ) (K : Fin k → Bool) (p : Fin k) : Bool :=
  K p || (s == 0 && p == lead σ.view)

/-- Whether `q` knows `b_I` at the end of the round (iteration `s`, round `t + 1`). -/
def nextK (σ : St k n) (s t : ℕ) (K : Fin k → Bool) (q : Fin k) : Bool :=
  kq σ s K q || decide (∃ p, π.delivers p q (t + 1) = true ∧ kq σ s K p = true)

/-- The view change step (end of the last iteration), `b` = whether `b_I` is known. -/
def vchange (σ : St k n) (b : Bool) : St k n :=
  if b then { res := pre X (σ.I + 1), F := σ.F, I := σ.I + 1, view := nextView σ.F σ.view, j := 0 }
  else { res := pre X σ.I, F := insert (lead σ.view) σ.F, I := σ.I,
         view := nextView (insert (lead σ.view) σ.F) σ.view, j := 0 }

lemma known_mid (σ : St k n) (hI : σ.I < n) (s : ℕ) (K : Fin k → Bool)
    (p : Fin k) :
    known (mid X σ s (K p)) ((alg k n f).answers X p (mid X σ s (K p))) =
      if kq σ s K p then some (X ⟨σ.I, hI⟩) else none := by
  have hq : (alg k n f).query p (mid X σ s (K p)) =
      if s = 0 ∧ lead σ.view = p then {⟨σ.I, hI⟩} else ∅ := by
    simp [alg, mid, hI]
  simp only [known, Protocol.answers, hq]
  cases hK : K p
  · have : get (mid X σ s false).res (mid X σ s false).I = none := by
      simp [mid, get_pre_self]
    rw [this]
    by_cases h0 : s = 0 ∧ lead σ.view = p
    · simp [h0, kq, hK, ans, get, hI, eq_comm, mid]
    · simp only [h0, ite_false, kq, hK, Bool.false_or]
      have : ¬ (s == 0 && p == lead σ.view) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq, not_and]; intro h1 h2; exact h0 ⟨h1, h2.symm⟩
      simp [this, ans, get]
  · simp [mid, kq, hK, get_pre_succ X σ.I hI]

omit [NeZero k] in
lemma recv_const (v i : ℕ) (b : Bool) (P : Fin k → Prop) [DecidablePred P]
    (inbox : Fin k → Option (ℕ × ℕ × Bool))
    (h : ∀ p, inbox p = if P p then some (v, i, b) else none) :
    recv v inbox = if ∃ p, P p then some (i, b) else none := by
  unfold recv
  cases hf : (List.finRange k).findSome? (fun p => match inbox p with
    | some (v', i, b) => if v' = v then some (i, b) else none
    | none => none) with
  | none =>
    rw [List.findSome?_eq_none_iff] at hf
    have : ¬ ∃ p, P p := by
      rintro ⟨p, hp⟩
      have := hf p (List.mem_finRange p)
      rw [h p] at this; simp [hp] at this
    simp [this]
  | some x =>
    obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some hf
    rw [h p] at hp
    by_cases hP : P p
    · simp only [hP, ite_true] at hp
      simp at hp
      rw [if_pos ⟨p, hP⟩, ← hp]
    · simp [hP] at hp

lemma inbox_mid (σ : St k n) (hI : σ.I < n) (s t : ℕ) (K : Fin k → Bool)
    (hc : ∀ q, π.alive q t → (alg k n f).cfg X π t q = mid X σ s (K q)) (q p : Fin k) :
    (alg k n f).inbox X π (t + 1) ((alg k n f).cfg X π t) q p =
      if π.delivers p q (t + 1) = true ∧ kq σ s K p = true then
        some (σ.view, σ.I, X ⟨σ.I, hI⟩) else none := by
  unfold Protocol.inbox
  by_cases hd : π.delivers p q (t + 1) = true
  · rw [hc p (Pattern.alive_of_delivers hd)]
    have hk := known_mid X f σ hI s K p
    simp only [hd, ite_true, true_and]
    simp only [alg, mid] at hk ⊢
    simp only [hI, ite_true]
    rw [hk]
    split <;> simp
  · simp [hd]

lemma step_mid (σ : St k n) (hI : σ.I < n) (s : ℕ) (b : Bool) (q : Fin k)
    (a : Fin n → Option Bool) (inbox : Fin k → Option (ℕ × ℕ × Bool)) (kn rc : Bool)
    (hk : known (mid X σ s b) a = if kn then some (X ⟨σ.I, hI⟩) else none)
    (hr : recv (mid X σ s b).view inbox = if rc then some (σ.I, X ⟨σ.I, hI⟩) else none)
    (hb : b = true → kn = true) :
    (alg k n f).step q (mid X σ s b) a inbox =
      if s < f then mid X σ (s + 1) (kn || rc) else vchange X σ (kn || rc) := by
  have hI' : (mid X σ s b).I < n := hI
  simp only [alg, hI', ite_true, hk, hr]
  have e1 := set_pre X σ.I hI
  have e2 := set_pre_succ X σ.I hI
  have e3 := get_pre_self X σ.I
  have e4 := get_pre_succ X σ.I hI
  cases b <;> cases kn <;> cases rc <;> simp at hb <;>
    by_cases hs : s < f <;> simp [mid, vchange, hs, e1, e2, e3, e4]

lemma round_mid (σ : St k n) (hI : σ.I < n) (hres : σ.res = pre X σ.I) (s : ℕ) (hs : s ≤ f)
    (t : ℕ) (K : Fin k → Bool)
    (hc : ∀ q, π.alive q t → (alg k n f).cfg X π t q = mid X σ s (K q)) (q : Fin k)
    (hq : π.alive q (t + 1)) :
    (alg k n f).cfg X π (t + 1) q =
      if s < f then mid X σ (s + 1) (nextK π σ s t K q) else vchange X σ (nextK π σ s t K q) := by
  have hqt : π.alive q t := Pattern.alive_mono hq (by omega)
  rw [cfg_succ]
  simp only [Protocol.round, hq, ite_true]
  rw [hc q hqt]
  apply step_mid X f σ hI s (K q) q _ _ (kq σ s K q)
    (decide (∃ p, π.delivers p q (t + 1) = true ∧ kq σ s K p = true))
  · exact known_mid X f σ hI s K q
  · have := recv_const σ.view σ.I (X ⟨σ.I, hI⟩)
      (fun p => π.delivers p q (t + 1) = true ∧ kq σ s K p = true) _
      (inbox_mid X π f σ hI s t K hc q)
    simp only [mid]
    rw [this]
    simp
  · intro hb; simp [kq, hb]

/-- Who knows `b_I` after iteration `s` of the view starting at time `t0` in state `σ`. -/
def Kseq (σ : St k n) (t0 : ℕ) : ℕ → Fin k → Bool
  | 0 => fun _ => false
  | s + 1 => nextK π σ s (t0 + s) (Kseq σ t0 s)

lemma Kseq_succ_of (σ : St k n) (t0 s : ℕ) (q : Fin k) (h : kq σ s (Kseq π σ t0 s) q = true) :
    Kseq π σ t0 (s + 1) q = true := by
  simp [Kseq, nextK, h]

lemma Kseq_mono (σ : St k n) (t0 : ℕ) {s s' : ℕ} (hs : s ≤ s') (q : Fin k)
    (h : Kseq π σ t0 s q = true) : Kseq π σ t0 s' q = true := by
  induction s', hs using Nat.le_induction with
  | base => exact h
  | succ s' _ ih => exact Kseq_succ_of π σ t0 s' q (by simp [kq, ih])

lemma mid_zero (σ : St k n) (hres : σ.res = pre X σ.I) (hj : σ.j = 0) : mid X σ 0 false = σ := by
  cases σ; simp_all [mid]

/-- Inside a view (iterations `s ≤ f`), every live peer is in state `mid σ s (Kseq s)`. -/
lemma cfg_view (σ : St k n) (hI : σ.I < n) (hres : σ.res = pre X σ.I) (hj : σ.j = 0) (t0 : ℕ)
    (h0 : ∀ q, π.alive q t0 → (alg k n f).cfg X π t0 q = σ) :
    ∀ s ≤ f, ∀ q, π.alive q (t0 + s) → (alg k n f).cfg X π (t0 + s) q = mid X σ s (Kseq π σ t0 s q) := by
  intro s hs
  induction s with
  | zero =>
    intro q hq; simp only [add_zero] at hq ⊢
    rw [h0 q hq]; exact (mid_zero X σ hres hj).symm
  | succ s ih =>
    intro q hq
    have := round_mid X π f σ hI hres s (by omega) (t0 + s) (Kseq π σ t0 s) (ih (by omega)) q hq
    rw [if_pos (by omega)] at this
    exact this

/-- At the end of the view every live peer performs the view change with `Kseq (f + 1)`. -/
lemma cfg_view_end (σ : St k n) (hI : σ.I < n) (hres : σ.res = pre X σ.I) (hj : σ.j = 0) (t0 : ℕ)
    (h0 : ∀ q, π.alive q t0 → (alg k n f).cfg X π t0 q = σ) (q : Fin k)
    (hq : π.alive q (t0 + f + 1)) :
    (alg k n f).cfg X π (t0 + f + 1) q = vchange X σ (Kseq π σ t0 (f + 1) q) := by
  have := round_mid X π f σ hI hres f le_rfl (t0 + f) (Kseq π σ t0 f)
    (cfg_view X π f σ hI hres hj t0 h0 f le_rfl) q hq
  rw [if_neg (lt_irrefl f)] at this
  exact this

/-- **Lemma 5.7.** If the leader of the view is nonfaulty, every peer knows `b_I` at its end. -/
lemma lemma_5_7 (σ : St k n) (t0 : ℕ) (hl : π.Nonfaulty (lead σ.view)) (q : Fin k) :
    Kseq π σ t0 (f + 1) q = true := by
  apply Kseq_mono π σ t0 (show 1 ≤ f + 1 by omega)
  simp only [Kseq, nextK, Bool.or_eq_true]
  right
  exact decide_eq_true ⟨lead σ.view, Pattern.delivers_of_alive (Pattern.alive_of_nonfaulty hl _),
    by simp [kq]⟩

/-- If nobody alive at the start of iteration `s` knows `b_I`, nobody alive afterwards does. -/
lemma Kseq_none_succ (σ : St k n) (t0 s : ℕ)
    (h : ∀ p, π.alive p (t0 + s) → kq σ s (Kseq π σ t0 s) p = false) :
    ∀ p, π.alive p (t0 + s + 1) → Kseq π σ t0 (s + 1) p = false := by
  intro q hq
  simp only [Kseq, nextK, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists, not_and]
  refine ⟨h q (Pattern.alive_mono hq (by omega)), fun p hd hk => ?_⟩
  have := h p (Pattern.alive_of_delivers hd)
  simp_all

lemma Kseq_none (σ : St k n) (t0 s : ℕ)
    (h : ∀ p, π.alive p (t0 + s) → kq σ s (Kseq π σ t0 s) p = false) :
    ∀ s', s < s' → ∀ p, π.alive p (t0 + s') → Kseq π σ t0 s' p = false := by
  intro s' hs'
  induction s', hs' using Nat.le_induction with
  | base => exact Kseq_none_succ π σ t0 s h
  | succ s' hs' ih =>
    apply Kseq_none_succ π σ t0 s'
    intro p hp
    simp only [kq, ih p hp, Bool.false_or, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    left; omega

/-- **Lemma 5.2.** At the end of a view, either every peer knows `b_I` or no live peer does. -/
lemma lemma_5_2 (hπ : π.Admissible f) (σ : St k n) (t0 : ℕ) :
    (∀ q, Kseq π σ t0 (f + 1) q = true) ∨
      (∀ q, π.alive q (t0 + f + 1) → Kseq π σ t0 (f + 1) q = false) := by
  by_cases hA : ∃ s ≤ f, ∃ p, π.alive p (t0 + s + 1) ∧ kq σ s (Kseq π σ t0 s) p = true
  · obtain ⟨s, hs, p, hp, hk⟩ := hA
    left
    intro q
    apply Kseq_mono π σ t0 (show s + 1 ≤ f + 1 by omega)
    simp only [Kseq, nextK, Bool.or_eq_true]
    right
    exact decide_eq_true ⟨p, Pattern.delivers_of_alive hp, hk⟩
  · push Not at hA
    by_cases hE : ∃ s ≤ f, ∀ p, π.alive p (t0 + s) → kq σ s (Kseq π σ t0 s) p = false
    · obtain ⟨s, hs, h⟩ := hE
      right
      exact fun q hq => Kseq_none π σ t0 s h (f + 1) (by omega) q (by simpa [add_assoc] using hq)
    · exfalso
      push Not at hE
      choose g hg using hE
      -- `g s` crashes exactly in round `t0 + s + 1`
      have hcr : ∀ s (hs : s ≤ f), π.crash (g s hs) = some (t0 + s + 1) := by
        intro s hs
        obtain ⟨h1, h2⟩ := hg s hs
        exact Pattern.crash_eq_of_alive h1 (fun h3 => by
          have := hA s hs _ h3; simp_all)
      let G : ℕ → Fin k := fun s => if hs : s ≤ f then g s hs else 0
      have hinj : Set.InjOn G (Finset.range (f + 1)) := by
        intro a ha b hb hab
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb
        have h1 := hcr a (by omega)
        have h2 := hcr b (by omega)
        simp only [G, dif_pos (show a ≤ f by omega), dif_pos (show b ≤ f by omega)] at hab
        rw [hab] at h1; rw [h1] at h2; simp at h2; omega
      have hsub : (Finset.range (f + 1)).image G ⊆ π.faulty := by
        intro p hp
        simp only [Finset.mem_image, Finset.mem_range] at hp
        obtain ⟨a, ha, rfl⟩ := hp
        rw [Pattern.mem_faulty]
        simp only [G, dif_pos (show a ≤ f by omega), Pattern.Nonfaulty, hcr a (by omega)]
        simp
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
      exact absurd (this.trans hπ) (by omega)

end Exec

/-! ### From view to view (Lemma 5.4, Corollaries 5.3, 5.6, 5.8) -/

section Global

variable (X : Fin n → Bool) (π : Pattern k) (f : ℕ)

/-- The state of all peers at the start of a view: `res` knows exactly the bits `< I`, `F` contains
only faulty peers, and the leader of the current view is not in `F`. -/
structure Good (σ : St k n) : Prop where
  res : σ.res = pre X σ.I
  j : σ.j = 0
  I_le : σ.I ≤ n
  F_sub : σ.F ⊆ π.faulty
  lead_notMem : lead σ.view ∉ σ.F

/-- All live peers are in state `σ` at time `t` ("in sync"). -/
def VS (t : ℕ) (σ : St k n) : Prop := ∀ q, π.alive q t → (alg k n f).cfg X π t q = σ

lemma query_mid (σ : St k n) (hI : σ.I < n) (s : ℕ) (b : Bool) (p : Fin k) :
    (alg k n f).query p (mid X σ s b) = if s = 0 ∧ lead σ.view = p then {⟨σ.I, hI⟩} else ∅ := by
  simp [alg, mid, hI]

lemma query_done (σ : St k n) (hn : n ≤ σ.I) (p : Fin k) : (alg k n f).query p σ = ∅ := by
  simp [alg, not_lt.mpr hn]

lemma send_done (σ : St k n) (hn : n ≤ σ.I) (p : Fin k) (a) (q : Fin k) :
    (alg k n f).send p σ a q = none := by
  simp [alg, not_lt.mpr hn]

/-- A finished peer never changes its state. -/
lemma frozen (σ : St k n) (hn : n ≤ σ.I) (t : ℕ) (h : VS X π f t σ) :
    ∀ t' ≥ t, VS X π f t' σ := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => exact h
  | succ t' _ ih =>
    intro q hq
    rw [cfg_succ]
    simp only [Protocol.round, hq, ite_true]
    rw [ih q (Pattern.alive_mono hq (by omega))]
    simp [alg, not_lt.mpr hn]

lemma exists_notMem_of_sub (hf : f < k) (hπ : π.Admissible f) {F : Finset (Fin k)}
    (hF : F ⊆ π.faulty) : ∃ q, q ∉ F := by
  by_contra h
  push Not at h
  have : (Finset.univ : Finset (Fin k)) ⊆ π.faulty := fun q _ => hF (h q)
  have := (Finset.card_le_card this).trans hπ
  simp at this; omega

/-- One view (Corollaries 5.3, 5.6, 5.8 and the induction step of Lemma 5.4): if all live peers
start view `σ.view` in sync, they all end it in sync, in the state `vchange σ b`, where `b` says
whether `b_I` was downloaded; if it was not, the leader was faulty. -/
lemma view_step (hf : f < k) (hπ : π.Admissible f) (σ : St k n) (hg : Good X π σ)
    (hI : σ.I < n) (t0 : ℕ) (h : VS X π f t0 σ) (p0 : Fin k) (hp0 : π.Nonfaulty p0) :
    let τ := vchange X σ (Kseq π σ t0 (f + 1) p0)
    VS X π f (t0 + f + 1) τ ∧ Good X π τ ∧ τ.I + τ.F.card = σ.I + σ.F.card + 1 := by
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [cfg_view_end X π f σ hI hg.res hg.j t0 h q hq]
    congr 1
    rcases lemma_5_2 π f hπ σ t0 with hall | hnone
    · rw [hall q, hall p0]
    · rw [hnone q hq, hnone p0 (Pattern.alive_of_nonfaulty hp0 _)]
  · have hex := exists_notMem_of_sub π f hf hπ hg.F_sub
    unfold τ vchange
    split
    · exact ⟨by simp, rfl, by simp; omega, hg.F_sub, lead_nextView_notMem _ _ hex⟩
    · rename_i hb
      have hlf : lead σ.view ∈ π.faulty := by
        rw [Pattern.mem_faulty]; intro hl
        exact hb (lemma_5_7 π f σ t0 hl p0)
      have hsub : insert (lead σ.view) σ.F ⊆ π.faulty := Finset.insert_subset hlf hg.F_sub
      exact ⟨by simp [hg.res], rfl, hg.I_le, hsub,
        lead_nextView_notMem _ _ (exists_notMem_of_sub π f hf hπ hsub)⟩
  · unfold τ vchange
    split
    · simp; omega
    · simp [Finset.card_insert_of_notMem hg.lead_notMem]; omega

end Global

end Podc.ByzantineDownload.Static

namespace Podc.ByzantineDownload.Static

open Protocol

variable {k n : ℕ} [NeZero k]

/-! ### The sequence of views -/

section Main

variable (X : Fin n → Bool) (π : Pattern k) (f : ℕ)

/-- The common state at the start of the `m`-th view (`m = 0, 1, …`), read off a fixed peer `p0`. -/
def σs (p0 : Fin k) (m : ℕ) : St k n := (alg k n f).cfg X π (m * (f + 1)) p0

lemma σs_inv (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0) (m : ℕ) :
    Good X π (σs X π f p0 m) ∧ VS X π f (m * (f + 1)) (σs X π f p0 m) ∧
      ((σs X π f p0 m).I < n → (σs X π f p0 m).I + (σs X π f p0 m).F.card = m) := by
  induction m with
  | zero =>
    refine ⟨⟨?_, by simp [σs, alg, Protocol.cfg], by simp [σs, alg, Protocol.cfg],
      by simp [σs, alg, Protocol.cfg], by simp [σs, alg, Protocol.cfg]⟩,
      fun q _ => by simp [σs, alg, Protocol.cfg], fun _ => by simp [σs, alg, Protocol.cfg]⟩
    funext i; simp [σs, alg, Protocol.cfg, pre]
  | succ m ih =>
    obtain ⟨hg, hv, hc⟩ := ih
    have e : (m + 1) * (f + 1) = m * (f + 1) + f + 1 := by ring
    by_cases hI : (σs X π f p0 m).I < n
    · obtain ⟨hv', hg', hc'⟩ := view_step X π f hf hπ _ hg hI _ hv p0 hp0
      have hs : σs X π f p0 (m + 1) = vchange X (σs X π f p0 m)
          (Kseq π (σs X π f p0 m) (m * (f + 1)) (f + 1) p0) := by
        unfold σs; rw [e]; exact hv' p0 (Pattern.alive_of_nonfaulty hp0 _)
      rw [hs, e]
      refine ⟨hg', hv', fun _ => ?_⟩
      rw [hc', hc hI]
    · have hn : n ≤ (σs X π f p0 m).I := by omega
      have hv' := frozen X π f _ hn _ hv ((m + 1) * (f + 1)) (by rw [e]; omega)
      have hs : σs X π f p0 (m + 1) = σs X π f p0 m := hv' p0 (Pattern.alive_of_nonfaulty hp0 _)
      rw [hs]
      exact ⟨hg, hv', fun h => absurd h hI⟩

/-- **Correctness of Algorithm 6** (Lemma 5.4 + "after `n + f` views all bits are downloaded"):
at the start of view number `n + f` every live peer has finished, with `res = X`. -/
lemma σs_done (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0) :
    (σs X π f p0 (n + f)).I = n ∧ (σs X π f p0 (n + f)).res = fun i => some (X i) := by
  obtain ⟨hg, -, hc⟩ := σs_inv X π f hf hπ p0 hp0 (n + f)
  have hI : (σs X π f p0 (n + f)).I = n := by
    by_contra h
    have h1 := hc (lt_of_le_of_ne hg.I_le h)
    have h2 := (Finset.card_le_card hg.F_sub).trans hπ
    have h3 := hg.I_le
    omega
  exact ⟨hI, by rw [hg.res, hI, pre_n]⟩

lemma σs_succ_active (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0)
    (m : ℕ) (hI : (σs X π f p0 m).I < n) :
    σs X π f p0 (m + 1) = vchange X (σs X π f p0 m)
      (Kseq π (σs X π f p0 m) (m * (f + 1)) (f + 1) p0) := by
  obtain ⟨hg, hv, -⟩ := σs_inv X π f hf hπ p0 hp0 m
  obtain ⟨hv', -, -⟩ := view_step X π f hf hπ _ hg hI _ hv p0 hp0
  have e : (m + 1) * (f + 1) = m * (f + 1) + f + 1 := by ring
  unfold σs; rw [e]; exact hv' p0 (Pattern.alive_of_nonfaulty hp0 _)

lemma σs_succ_done (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0)
    (m : ℕ) (hn : n ≤ (σs X π f p0 m).I) : σs X π f p0 (m + 1) = σs X π f p0 m := by
  obtain ⟨-, hv, -⟩ := σs_inv X π f hf hπ p0 hp0 m
  have e : (m + 1) * (f + 1) = m * (f + 1) + f + 1 := by ring
  exact frozen X π f _ hn _ hv ((m + 1) * (f + 1)) (by rw [e]; omega) p0
    (Pattern.alive_of_nonfaulty hp0 _)

/-- Consecutive views: the next view is `nextView F' v` where `F'` is the new set of suspects. -/
lemma σs_view_succ (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0)
    (m : ℕ) (hI : (σs X π f p0 m).I < n) :
    (σs X π f p0 (m + 1)).view = nextView (σs X π f p0 (m + 1)).F (σs X π f p0 m).view := by
  rw [σs_succ_active X π f hf hπ p0 hp0 m hI]
  unfold vchange; split <;> rfl

/-- The state of a live peer at any time `t`, from the state at the start of its view. -/
lemma cfg_eq_σs (hf : f < k) (hπ : π.Admissible f) (p0 : Fin k) (hp0 : π.Nonfaulty p0)
    (t : ℕ) (q : Fin k) (hq : π.alive q t) :
    let m := t / (f + 1)
    ((σs X π f p0 m).I < n → ∃ b, (alg k n f).cfg X π t q = mid X (σs X π f p0 m) (t % (f + 1)) b) ∧
      (n ≤ (σs X π f p0 m).I → (alg k n f).cfg X π t q = σs X π f p0 m) := by
  intro m
  obtain ⟨hg, hv, -⟩ := σs_inv X π f hf hπ p0 hp0 m
  have ht : t = m * (f + 1) + t % (f + 1) := by
    have := Nat.div_add_mod t (f + 1); simp only [m]; linarith
  have hs : t % (f + 1) ≤ f := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by omega))
  refine ⟨fun hI => ?_, fun hn => ?_⟩
  · have := cfg_view X π f _ hI hg.res hg.j _ hv (t % (f + 1)) hs q (by rw [← ht]; exact hq)
    rw [← ht] at this
    exact ⟨_, this⟩
  · exact frozen X π f _ hn _ hv t (by omega) q hq

end Main

end Podc.ByzantineDownload.Static

namespace Podc.ByzantineDownload.Static

open Protocol

variable {k n : ℕ} [NeZero k]

/-! ### Theorem 5.9 -/

/-- **Theorem 5.9 (correctness and time).** With at most `f < k` crashes, Algorithm 6 solves
Download: from time `(n + f)(f + 1)` on (i.e. after `n + f` views of `f + 1` rounds), every
nonfaulty peer has `res = X` (and has stopped). -/
theorem theorem_5_9_correct (f : ℕ) (hf : f < k) :
    (alg k n f).SolvesWithin f ((n + f) * (f + 1)) := by
  intro X π hπ p hp t ht
  obtain ⟨hI, hres⟩ := σs_done X π f hf hπ p hp
  obtain ⟨-, hv, -⟩ := σs_inv X π f hf hπ p hp (n + f)
  have := frozen X π f _ hI.ge _ hv t ht p (Pattern.alive_of_nonfaulty hp _)
  rw [this]
  exact hres

lemma query_card (X : Fin n → Bool) (π : Pattern k) (f : ℕ) (hf : f < k) (hπ : π.Admissible f)
    (p : Fin k) (hp : π.Nonfaulty p) (t : ℕ) :
    ((alg k n f).query p ((alg k n f).cfg X π t p)).card =
      if t % (f + 1) = 0 ∧ (σs X π f p (t / (f + 1))).I < n ∧
        lead (σs X π f p (t / (f + 1))).view = p then 1 else 0 := by
  obtain ⟨h1, h2⟩ := cfg_eq_σs X π f hf hπ p hp t p (Pattern.alive_of_nonfaulty hp _)
  by_cases hI : (σs X π f p (t / (f + 1))).I < n
  · obtain ⟨b, hb⟩ := h1 hI
    rw [hb, query_mid X f _ hI]
    by_cases hc : t % (f + 1) = 0 ∧ lead (σs X π f p (t / (f + 1))).view = p
    · simp [hc, hI]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.2⟩)]; rfl
  · rw [h2 (by omega), query_done f _ (by omega), if_neg (fun h => hI h.2.1)]; rfl

/-- **Theorem 5.9 (query complexity).** Every nonfaulty peer queries at most `(n + k - 1)/(k - f)`
bits: the leaders rotate round-robin over the peers not known to be crashed, and there are at most
`n + f` views. With `f ≤ βk` this is `≤ 2n/(γk)` (`theorem_5_9`). -/
theorem theorem_5_9_queries (f : ℕ) (hf : f < k) (X : Fin n → Bool) (π : Pattern k)
    (hπ : π.Admissible f) (p : Fin k) (hp : π.Nonfaulty p) (T : ℕ) :
    (alg k n f).queries X π p T * (k - f) ≤ n + k - 1 := by
  classical
  set L := f + 1 with hL
  let act : ℕ → Prop := fun m => (σs X π f p m).I < n
  have hex : ∃ m, ¬ act m := ⟨n + f, by simp [act, (σs_done X π f hf hπ p hp).1]⟩
  set M := Nat.find hex with hMdef
  have hstay : ∀ m, M ≤ m → ¬ act m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact Nat.find_spec hex
    | succ m _ ih =>
      simp only [act, not_lt] at ih ⊢
      rw [σs_succ_done X π f hf hπ p hp m ih]; exact ih
  have hact : ∀ m, act m ↔ m < M := fun m =>
    ⟨fun h => by by_contra h'; exact hstay m (by omega) h, fun h => by
      have := Nat.find_min hex h; simpa using this⟩
  have hM : M ≤ n + f := Nat.find_le (by simp [act, (σs_done X π f hf hπ p hp).1])
  -- queries are counted by the views led by `p`
  let A := (Finset.range T).filter
    (fun t => t % L = 0 ∧ act (t / L) ∧ lead (σs X π f p (t / L)).view = p)
  let B := (Finset.range M).filter (fun m => lead (σs X π f p m).view = p)
  have hQA : (alg k n f).queries X π p T = A.card := by
    unfold Protocol.queries
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [query_card X π f hf hπ p hp t]
  have hAB : A.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun t => t / L)
    · intro t ht
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
      simp only [B, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      exact ⟨(hact _).1 ht.2.2.1, ht.2.2.2⟩
    · intro a ha b hb hab
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha hb
      simp only at hab
      have h1 := Nat.div_add_mod a L
      have h2 := Nat.div_add_mod b L
      rw [ha.2.1] at h1; rw [hb.2.1] at h2
      rw [← h1, ← h2, hab]
  have hrr := roundRobin_count π.faulty p (by rw [Pattern.mem_faulty]; exact not_not.mpr hp) M
    (fun m => (σs X π f p m).view)
    (fun m hm => by
      have hI : act m := (hact m).2 (by omega)
      rw [σs_view_succ X π f hf hπ p hp m hI]; exact lt_nextView _ _)
    (fun m hm u h1 h2 => by
      have hI : act m := (hact m).2 (by omega)
      rw [σs_view_succ X π f hf hπ p hp m hI] at h2
      exact (σs_inv X π f hf hπ p hp (m + 1)).1.F_sub (lead_mem_of_lt_of_lt_nextView _ h1 h2))
  have hfc : π.faulty.card ≤ f := hπ
  rw [hQA]
  set x := B.card with hx
  change (x - 1) * (k - π.faulty.card) ≤ M - 1 at hrr
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · have : A.card = 0 := by omega
    rw [this]; simp
  · have hM1 : 1 ≤ M := by
      by_contra h
      have : B = ∅ := by
        simp only [B, Finset.filter_eq_empty_iff, Finset.mem_range]; intro m hm; omega
      rw [hx, this] at hpos; simp at hpos
    have h3 : (x - 1) * (k - f) ≤ (x - 1) * (k - π.faulty.card) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : x * (k - f) = (x - 1) * (k - f) + (k - f) := by
      conv_lhs => rw [show x = (x - 1) + 1 by omega]
      ring
    calc A.card * (k - f) ≤ x * (k - f) := Nat.mul_le_mul_right _ hAB
      _ ≤ n + k - 1 := by omega

/-- **Theorem 5.9 (message complexity).** A nonfaulty peer sends at most `(k - 1)(n + f)(f + 1)`
messages in total (it stops after `n + f` views of `f + 1` rounds), so the total is
`O(k² f n)`. -/
theorem theorem_5_9_messages (f : ℕ) (hf : f < k) (X : Fin n → Bool) (π : Pattern k)
    (hπ : π.Admissible f) (p : Fin k) (hp : π.Nonfaulty p) (T : ℕ) :
    (alg k n f).msgsSent X π p T ≤ (k - 1) * ((n + f) * (f + 1)) := by
  classical
  set N := (n + f) * (f + 1)
  obtain ⟨hI, -⟩ := σs_done X π f hf hπ p hp
  obtain ⟨-, hv, -⟩ := σs_inv X π f hf hπ p hp (n + f)
  unfold Protocol.msgsSent
  calc _ ≤ ∑ t ∈ Finset.range T, if t < N then k - 1 else 0 := by
        apply Finset.sum_le_sum
        intro t _
        split
        · calc _ ≤ (Finset.univ.erase p).card := by
                apply Finset.card_le_card
                intro q hq
                simp only [Finset.mem_filter] at hq
                exact Finset.mem_erase.2 ⟨hq.2.1, Finset.mem_univ _⟩
            _ = k - 1 := by simp
        · have := frozen X π f _ hI.ge _ hv t (by omega) p (Pattern.alive_of_nonfaulty hp _)
          rw [this]
          simp [Protocol.answers, send_done f _ hI.ge]
    _ = ((Finset.range T).filter (· < N)).card * (k - 1) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    _ ≤ N * (k - 1) := by
        apply Nat.mul_le_mul_right
        calc _ ≤ (Finset.range N).card := by
              apply Finset.card_le_card
              intro t ht
              simp only [Finset.mem_filter] at ht
              exact Finset.mem_range.2 ht.2
          _ = N := Finset.card_range N
    _ = _ := by ring

/-- **Theorem 5.9.** In the synchronous model with `f ≤ βk` crash faults, `β < 1`, `γ = 1 - β`,
and `n ≥ k` (the paper's standing assumption), Algorithm 6 solves Download within
`T = (n + f)(f + 1) = O(nf)` rounds, every nonfaulty peer queries at most `2n/(γk) = O(n/(γk))` bits
and sends at most `(k - 1)(n + f)(f + 1)` messages (`M = O(k² f n)` in total). -/
theorem theorem_5_9 (f : ℕ) (β : ℝ) (hβ : β < 1) (hfβ : (f : ℝ) ≤ β * k) (hkn : k ≤ n) :
    (alg k n f).SolvesWithin f ((n + f) * (f + 1)) ∧
    ∀ (X : Fin n → Bool) (π : Pattern k), π.Admissible f → ∀ p, π.Nonfaulty p → ∀ T,
      ((alg k n f).queries X π p T : ℝ) ≤ 2 * n / ((1 - β) * k) ∧
      (alg k n f).msgsSent X π p T ≤ (k - 1) * ((n + f) * (f + 1)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_neZero k
  have hf : f < k := by
    have : (f : ℝ) < k := by nlinarith
    exact_mod_cast this
  refine ⟨theorem_5_9_correct f hf, fun X π hπ p hp T => ⟨?_, theorem_5_9_messages f hf X π hπ p hp T⟩⟩
  have hq := theorem_5_9_queries f hf X π hπ p hp T
  set Q := (alg k n f).queries X π p T
  have h1 : (Q : ℝ) * ((k : ℝ) - f) ≤ n + k - 1 := by
    have : Q * (k - f) ≤ n + k - 1 := hq
    have h' : ((Q * (k - f) : ℕ) : ℝ) ≤ ((n + k - 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub hf.le, Nat.cast_sub (show 1 ≤ n + k by have := Nat.pos_of_neZero k; omega)] at h'
    linarith
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hpos : 0 < (1 - β) * k := by nlinarith
  rw [le_div_iff₀ hpos]
  have : (1 - β) * k ≤ (k : ℝ) - f := by nlinarith
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  nlinarith

end Podc.ByzantineDownload.Static
