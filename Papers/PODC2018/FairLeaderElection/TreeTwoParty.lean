import Podc.Computability.Distributed.UniRing.Basic

/-!
# Lemma F.2 of [YM18]: two-party protocols cannot be resilient

[YM18] A. Yifrach, Y. Mansour. *Fair Leader Election for Rational Agents in Asynchronous Rings and
Networks.* PODC 2018 (arXiv:1805.04778v2), Appendix F.

Two processors `A` (index `0`) and `B` (index `1`) connected by one FIFO link in each direction form
the unidirectional ring of size `2` of `Cslib.UniRing`; in particular every processor has a single
incoming link, so the result of an execution does not depend on the (fair) schedule
(`Cslib.UniRing.terminates_iff`). `Agree a b o` says that both processors terminate with output `o`.

A two-party protocol with a product input space `I_A × I_B` is described by the finite *sets* of
processors `SA` (the strategies `S_A(i)`, `i ∈ I_A`) and `SB`. A processor *assures* a set of outputs
`Q` if some deviation of it makes both processors terminate with a common output in `Q`, against every
honest strategy of the other processor (Definition F.1; executions are schedule independent).

**Lemma F.2** (generalized, `lemma_F2`): if every honest pair of strategies terminates with a common
output in `Q₁ ∪ Q₂`, then `A` assures `Q₁` or `B` assures `Q₂`. The paper states this for outputs
`{0, 1}` (`Q₁ = {0}`, `Q₂ = {1}` and the symmetric statement) and assumes in addition "a bounded
amount of messages"; for finite input sets this bound follows from termination of the honest
executions (`exists_bdd`), so it is not needed as a hypothesis.

The proof is the paper's induction (on the maximal number of messages sent in an honest execution):
* if some honest `A` and some honest `B` send nothing at initialization, both terminate immediately
  with a common output `o₀`, and both assure `o₀`;
* otherwise one of them, say `A`, sends a first message `M` for every input; in the subprotocol `P_M`
  (`dropFirst`, `feed`) `B` has already received `M`, and the induction hypothesis either gives a
  strategy of `A` assuring `Q₁` after sending `M` (`prepend`), or for every `M` a strategy of `B`
  assuring `Q₂` in `P_M`, combined into "wait for the first message `M`, then play" (`waitFirst`).
-/

namespace Podc.FairLeaderElection.Trees

open Cslib.UniRing

variable {M O : Type*}

/-- The two-processor system `A = a` (index `0`), `B = b` (index `1`). -/
abbrev sys (a b : Proc M O) : Fin 2 → Proc M O := ![a, b]

/-- Both processors terminate with the common output `o` (in every fair execution). -/
def Agree (a b : Proc M O) (o : O) : Prop :=
  Terminates (sys a b) 0 o ∧ Terminates (sys a b) 1 o

theorem agree_iff_run {a b : Proc M O} {σ : ℕ → Fin 2} (hσ : Fair σ) {o : O} :
    Agree a b o ↔ (∃ t, a.out (run (sys a b) σ t 0) = some o) ∧
      ∃ t, b.out (run (sys a b) σ t 1) = some o := by
  unfold Agree
  rw [← terminates_iff hσ, ← terminates_iff hσ]
  rfl

/-! ### Auxiliary processors -/

theorem tail_prefix_tail {l l' : List M} (h : l <+: l') : l.tail <+: l'.tail := by
  obtain ⟨t, rfl⟩ := h
  cases l with
  | nil => exact List.nil_prefix
  | cons x l => exact ⟨t, by simp⟩

/-- `A` in the subprotocol after its first message has been taken out of the link. -/
def dropFirst (a : Proc M O) : Proc M O where
  sent h := (a.sent h).tail
  sent_snoc h m := tail_prefix_tail (a.sent_snoc h m)
  out := a.out

/-- `B` having received `M` (if it had not terminated at initialization). -/
def feedRaw (m₀ : M) (b : Proc M O) : Proc M O where
  sent h := b.sent (m₀ :: h)
  sent_snoc h m := by simpa using b.sent_snoc (m₀ :: h) m
  out h := b.out (m₀ :: h)

open Classical in
/-- `B` in the subprotocol `P_M`. -/
noncomputable def feed (m₀ : M) (b : Proc M O) : Proc M O :=
  if b.out [] = none then feedRaw m₀ b else b

/-- Send `m₀` first, then behave as `x`. -/
def prepend (m₀ : M) (x : Proc M O) : Proc M O where
  sent h := m₀ :: x.sent h
  sent_snoc h m := (List.prefix_cons_inj m₀).mpr (x.sent_snoc h m)
  out := x.out

/-- Wait for the first message `m`, then behave as `f m`. -/
def waitFirst (f : M → Proc M O) : Proc M O where
  sent h := match h with
    | [] => []
    | m :: h' => (f m).sent h'
  sent_snoc h m := by
    cases h with
    | nil => exact List.nil_prefix
    | cons m' h' => simpa using (f m').sent_snoc h' m
  out h := match h with
    | [] => none
    | m :: h' => (f m).out h'

/-- A processor that is silent and never terminates. -/
def idle : Proc M O where
  sent _ := []
  sent_snoc _ _ := List.nil_prefix
  out _ := none

theorem dropFirst_prepend (m₀ : M) (x : Proc M O) : dropFirst (prepend m₀ x) = x := by
  cases x; rfl

theorem feed_waitFirst (m₀ : M) (f : M → Proc M O) : feed m₀ (waitFirst f) = f m₀ := by
  unfold feed
  simp only [show (waitFirst f).out [] = none from rfl, ↓reduceIte]
  cases h : f m₀
  simp only [feedRaw, waitFirst, h]

/-! ### Executions without communication -/

theorem deliver_init (a b : Proc M O) (h0 : b.sent [] = [] ∨ a.out [] ≠ none)
    (h1 : a.sent [] = [] ∨ b.out [] ≠ none) (i : Fin 2) :
    deliver (sys a b) init i = init := by
  unfold deliver inbox
  fin_cases i
  · rcases h0 with h | h
    · split_ifs <;> simp [init, h]
    · simp only [init] at h ⊢; simp [h]
  · rcases h1 with h | h
    · split_ifs <;> simp [init, h]
    · simp only [init] at h ⊢; simp [h]

theorem run_eq_init (a b : Proc M O) (h0 : b.sent [] = [] ∨ a.out [] ≠ none)
    (h1 : a.sent [] = [] ∨ b.out [] ≠ none) (σ : ℕ → Fin 2) (t : ℕ) :
    run (sys a b) σ t = init := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, ih, deliver_init a b h0 h1]

/-- Without communication, agreement is agreement at initialization. -/
theorem agree_iff_of_silent {a b : Proc M O} (h0 : b.sent [] = [] ∨ a.out [] ≠ none)
    (h1 : a.sent [] = [] ∨ b.out [] ≠ none) {o : O} :
    Agree a b o ↔ a.out [] = some o ∧ b.out [] = some o := by
  rw [agree_iff_run fair_roundRobin]
  simp [run_eq_init a b h0 h1, init]

/-! ### Exchanging the roles of the two processors -/

/-- Exchange of the two indices. -/
def sw (i : Fin 2) : Fin 2 := i + 1

@[simp] theorem sw_zero : sw 0 = 1 := rfl
@[simp] theorem sw_one : sw 1 = 0 := rfl
@[simp] theorem neg_one_fin_two : (-1 : Fin 2) = 1 := rfl

theorem deliver_swap (a b : Proc M O) (c : Config 2 M) (i : Fin 2) :
    deliver (sys b a) (c ∘ sw) (sw i) = deliver (sys a b) c i ∘ sw := by
  funext j
  unfold deliver inbox
  fin_cases i <;> fin_cases j <;> simp <;> split_ifs <;> simp_all

theorem run_swap (a b : Proc M O) (σ : ℕ → Fin 2) (t : ℕ) :
    run (sys b a) (sw ∘ σ) t = run (sys a b) σ t ∘ sw := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, ih, Function.comp_apply, deliver_swap]

theorem fair_swap {σ : ℕ → Fin 2} (hσ : Fair σ) : Fair (sw ∘ σ) := by
  intro i N
  obtain ⟨t, ht, h⟩ := hσ (i + 1) N
  exact ⟨t, ht, by rw [Function.comp_apply, h]; fin_cases i <;> rfl⟩

theorem agree_swap {a b : Proc M O} {o : O} : Agree b a o ↔ Agree a b o := by
  rw [agree_iff_run (fair_swap fair_roundRobin), agree_iff_run (σ := roundRobin 2) fair_roundRobin]
  simp only [run_swap, Function.comp_apply, sw_zero, sw_one]
  exact And.comm

/-! ### The subprotocol `P_M` -/

/-- The schedule that first delivers to `B`, then follows `σ`. -/
def shift (σ : ℕ → Fin 2) : ℕ → Fin 2
  | 0 => 1
  | t + 1 => σ t

theorem fair_shift {σ : ℕ → Fin 2} (hσ : Fair σ) : Fair (shift σ) := by
  intro i N
  obtain ⟨t, ht, h⟩ := hσ i N
  exact ⟨t + 1, by omega, h⟩

/-- Embedding of configurations of `P_M` into configurations of `P`. -/
def embed (m₀ : M) (c : Config 2 M) : Config 2 M := ![c 0, m₀ :: c 1]

theorem deliver_embed {a b : Proc M O} {m₀ : M} (c : Config 2 M) (i : Fin 2) :
    deliver (sys a b) (embed m₀ c) i = embed m₀ (deliver (sys (dropFirst a) (feedRaw m₀ b)) c i) := by
  funext j
  unfold deliver inbox
  fin_cases i <;> fin_cases j <;> simp [embed, dropFirst, feedRaw] <;> split_ifs <;> simp_all

theorem run_shift {a b : Proc M O} {m₀ : M} (hb : b.out [] = none)
    (ha : (a.sent []).head? = some m₀) (σ : ℕ → Fin 2) (t : ℕ) :
    run (sys a b) (shift σ) (t + 1) = embed m₀ (run (sys (dropFirst a) (feedRaw m₀ b)) σ t) := by
  induction t with
  | zero =>
    show deliver (sys a b) init 1 = embed m₀ init
    funext j
    unfold deliver inbox
    obtain ⟨L, hL⟩ : ∃ L, a.sent [] = m₀ :: L := by
      cases h : a.sent [] with
      | nil => rw [h] at ha; simp at ha
      | cons x L => rw [h] at ha; simp at ha; exact ⟨L, by rw [ha]⟩
    fin_cases j <;> simp [embed, init, hb, hL]
  | succ t ih =>
    rw [run, ih]
    exact deliver_embed _ _

theorem exists_succ_iff {f : ℕ → Prop} (h : f 0 → f 1) : (∃ t, f t) ↔ ∃ t, f (t + 1) := by
  constructor
  · rintro ⟨t, ht⟩
    cases t with
    | zero => exact ⟨0, h ht⟩
    | succ t => exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩; exact ⟨t + 1, ht⟩

theorem agree_feedRaw {a b : Proc M O} {m₀ : M} (hb : b.out [] = none)
    (ha : (a.sent []).head? = some m₀) {o : O} :
    Agree a b o ↔ Agree (dropFirst a) (feedRaw m₀ b) o := by
  rw [agree_iff_run (fair_shift fair_roundRobin), agree_iff_run (σ := roundRobin 2) fair_roundRobin]
  have h0 : run (sys a b) (shift (roundRobin 2)) 0 = init := rfl
  have h1 := run_shift hb ha (roundRobin 2) 0
  rw [exists_succ_iff (f := fun t => a.out (run (sys a b) (shift (roundRobin 2)) t 0) = some o)
    (by
      intro h
      show a.out (run (sys a b) (shift (roundRobin 2)) (0 + 1) 0) = some o
      rw [h1]; simpa [embed, run, init] using h),
    exists_succ_iff (f := fun t => b.out (run (sys a b) (shift (roundRobin 2)) t 1) = some o)
    (by intro h; simp [h0, init, hb] at h)]
  simp only [run_shift hb ha]
  simp [embed, dropFirst, feedRaw]

theorem run_dropFirst {a b : Proc M O} (hb : b.out [] ≠ none) (σ : ℕ → Fin 2) (t : ℕ) :
    run (sys a b) σ t = run (sys (dropFirst a) b) σ t ∧ run (sys a b) σ t 1 = [] := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [run]
    rw [← ih1]
    set c := run (sys a b) σ t
    have e1 : deliver (sys a b) c 1 = c := by
      unfold deliver; simp [ih2, hb]
    have e1' : deliver (sys (dropFirst a) b) c 1 = c := by
      unfold deliver; simp [ih2, hb]
    generalize σ t = i
    fin_cases i
    · refine ⟨rfl, ?_⟩
      unfold deliver; split_ifs <;> simp [Function.update, ih2]
    · simp only [Fin.mk_one, Fin.isValue, e1, e1']
      exact ⟨trivial, ih2⟩

theorem agree_dropFirst {a b : Proc M O} (hb : b.out [] ≠ none) {o : O} :
    Agree a b o ↔ Agree (dropFirst a) b o := by
  rw [agree_iff_run (σ := roundRobin 2) fair_roundRobin,
    agree_iff_run (σ := roundRobin 2) fair_roundRobin]
  have e : ∀ t, run (sys a b) (roundRobin 2) t = run (sys (dropFirst a) b) (roundRobin 2) t :=
    fun t => (run_dropFirst hb _ t).1
  simp only [e]
  rfl

/-- **The subprotocol `P_M`.** If `A` sends `M` first, executions of `P` and of `P_M` agree. -/
theorem agree_feed {a b : Proc M O} {m₀ : M} (ha : (a.sent []).head? = some m₀) {o : O} :
    Agree a b o ↔ Agree (dropFirst a) (feed m₀ b) o := by
  unfold feed
  split_ifs with hb
  · exact agree_feedRaw hb ha
  · exact agree_dropFirst hb

/-! ### Bounds on the number of messages -/

/-- Every execution of `(a, b)` sends at most `N` messages in total. -/
def Bdd (a b : Proc M O) (N : ℕ) : Prop :=
  ∀ σ t, (a.sent (run (sys a b) σ t 0)).length + (b.sent (run (sys a b) σ t 1)).length ≤ N

theorem Bdd.mono {a b : Proc M O} {N N' : ℕ} (h : Bdd a b N) (hN : N ≤ N') : Bdd a b N' :=
  fun σ t => (h σ t).trans hN

theorem sw_sw (i : Fin 2) : sw (sw i) = i := by fin_cases i <;> rfl

theorem Bdd.swap {a b : Proc M O} {N : ℕ} (h : Bdd a b N) : Bdd b a N := by
  intro σ t
  have e : run (sys b a) σ t = run (sys a b) (sw ∘ σ) t ∘ sw := by
    rw [← run_swap]; congr 1; funext s; simp [sw_sw]
  rw [e]
  simpa [add_comm] using h (sw ∘ σ) t

theorem Bdd.subproto {a b : Proc M O} {m₀ : M} {N : ℕ} (h : Bdd a b N)
    (ha : (a.sent []).head? = some m₀) : Bdd (dropFirst a) (feed m₀ b) (N - 1) := by
  intro σ t
  have hpos : ∀ c : List M, 1 ≤ (a.sent c).length := by
    intro c
    have := ((a.sent_mono (List.nil_prefix (l := c))).length_le)
    cases hs : a.sent [] with
    | nil => rw [hs] at ha; simp at ha
    | cons x L => rw [hs] at this; simp at this; omega
  unfold feed
  split_ifs with hb
  · have h1 := h (shift σ) (t + 1)
    rw [run_shift hb ha] at h1
    set c := run (sys (dropFirst a) (feedRaw m₀ b)) σ t
    have h2 := hpos (c 0)
    show (a.sent (c 0)).tail.length + (b.sent (m₀ :: c 1)).length ≤ N - 1
    simp only [embed, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    rw [List.length_tail]; omega
  · have h1 := h σ t
    rw [(run_dropFirst hb σ t).1] at h1
    set c := run (sys (dropFirst a) b) σ t
    have h2 := hpos (c 0)
    show (a.sent (c 0)).tail.length + (b.sent (c 1)).length ≤ N - 1
    rw [List.length_tail]; omega

/-- A terminating pair of processors sends boundedly many messages. -/
theorem exists_bdd {a b : Proc M O} {o : O} (h : Agree a b o) : ∃ N, Bdd a b N := by
  obtain ⟨⟨c₀, hc₀, ho₀⟩, ⟨c₁, hc₁, ho₁⟩⟩ := h
  obtain ⟨r, hr, hle⟩ := exists_reach_ge (P := sys a b) ![c₀, c₁]
    (by intro j; fin_cases j <;> assumption)
  have hr0 : r 0 = c₀ 0 := eq_of_le_of_out hr.inv (hle 0) ho₀
  have hr1 : r 1 = c₁ 1 := eq_of_le_of_out hr.inv (hle 1) ho₁
  refine ⟨(a.sent (r 0)).length + (b.sent (r 1)).length, fun σ t => ?_⟩
  obtain ⟨r', hr', hle'⟩ := exists_reach_ge (P := sys a b) ![run (sys a b) σ t, r]
    (by intro j; fin_cases j; exacts [reach_run σ t, hr])
  have e0 : r' 0 = r 0 := eq_of_le_of_out (o := o) hr'.inv (hle' 1)
    (by show (sys a b 0).out (r 0) = some o; rw [hr0]; exact ho₀)
  have e1 : r' 1 = r 1 := eq_of_le_of_out (o := o) hr'.inv (hle' 1)
    (by show (sys a b 1).out (r 1) = some o; rw [hr1]; exact ho₁)
  have g0 : run (sys a b) σ t 0 <+: r 0 := by rw [← e0]; exact hle' 0 0
  have g1 : run (sys a b) σ t 1 <+: r 1 := by rw [← e1]; exact hle' 0 1
  exact add_le_add (a.sent_mono g0).length_le (b.sent_mono g1).length_le

/-! ### The induction -/

/-- `A` assures `Q`: some strategy of `A` agrees on an output in `Q` with every honest `B`
(Definition F.1). -/
def AssuresA (SB : Set (Proc M O)) (Q : Set O) : Prop := ∃ a', ∀ b ∈ SB, ∃ o ∈ Q, Agree a' b o

/-- `B` assures `Q`. -/
def AssuresB (SA : Set (Proc M O)) (Q : Set O) : Prop := ∃ b', ∀ a ∈ SA, ∃ o ∈ Q, Agree a b' o

variable (M O) in
/-- The statement of Lemma F.2 for protocols with at most `N` messages. -/
def Dichotomy (N : ℕ) : Prop := ∀ (SA SB : Set (Proc M O)) (Q₁ Q₂ : Set O),
  (∀ a ∈ SA, ∀ b ∈ SB, Bdd a b N) → (∀ a ∈ SA, ∀ b ∈ SB, ∃ o ∈ Q₁ ∪ Q₂, Agree a b o) →
  AssuresA SB Q₁ ∨ AssuresB SA Q₂

/-- The induction step when `A` sends a message at initialization for every input. -/
theorem dichotomy_step (N : ℕ) (ih : ∀ N' < N, Dichotomy M O N') (SA SB : Set (Proc M O))
    (Q₁ Q₂ : Set O) (hbdd : ∀ a ∈ SA, ∀ b ∈ SB, Bdd a b N)
    (hsucc : ∀ a ∈ SA, ∀ b ∈ SB, ∃ o ∈ Q₁ ∪ Q₂, Agree a b o)
    (hspeak : ∀ a ∈ SA, a.sent [] ≠ []) : AssuresA SB Q₁ ∨ AssuresB SA Q₂ := by
  classical
  rcases Set.eq_empty_or_nonempty SB with hSB | ⟨b₀, hb₀⟩
  · exact Or.inl ⟨idle, by simp [hSB]⟩
  have hR : ∀ m₀ : M, AssuresA (feed m₀ '' SB) Q₁ ∨ ∃ b', ∀ a ∈ SA,
      (a.sent []).head? = some m₀ → ∃ o ∈ Q₂, Agree (dropFirst a) b' o := by
    intro m₀
    by_cases hne : ∃ a ∈ SA, (a.sent []).head? = some m₀
    · obtain ⟨a₀, ha₀, -⟩ := hne
      have hN : 1 ≤ N := by
        have h0 := hbdd a₀ ha₀ b₀ hb₀ (roundRobin 2) 0
        have h1 := hspeak a₀ ha₀
        simp only [run, init] at h0
        have : 1 ≤ (a₀.sent []).length := by
          cases hs : a₀.sent [] with
          | nil => exact absurd hs h1
          | cons x L => simp
        omega
      have := ih (N - 1) (by omega) (dropFirst '' {a ∈ SA | (a.sent []).head? = some m₀})
        (feed m₀ '' SB) Q₁ Q₂
        (by
          rintro _ ⟨a, ⟨ha, hm⟩, rfl⟩ _ ⟨b, hb, rfl⟩
          exact (hbdd a ha b hb).subproto hm)
        (by
          rintro _ ⟨a, ⟨ha, hm⟩, rfl⟩ _ ⟨b, hb, rfl⟩
          obtain ⟨o, hoQ, hag⟩ := hsucc a ha b hb
          exact ⟨o, hoQ, (agree_feed hm).mp hag⟩)
      rcases this with h | ⟨b', hb'⟩
      · exact Or.inl h
      · exact Or.inr ⟨b', fun a ha hm => hb' _ ⟨a, ⟨ha, hm⟩, rfl⟩⟩
    · push Not at hne
      exact Or.inr ⟨idle, fun a ha hm => absurd hm (hne a ha)⟩
  by_cases hL : ∃ m₀, AssuresA (feed m₀ '' SB) Q₁
  · obtain ⟨m₀, a', ha'⟩ := hL
    refine Or.inl ⟨prepend m₀ a', fun b hb => ?_⟩
    obtain ⟨o, hoQ, hag⟩ := ha' _ ⟨b, hb, rfl⟩
    refine ⟨o, hoQ, ?_⟩
    rw [agree_feed (a := prepend m₀ a') (m₀ := m₀) (by simp [prepend]), dropFirst_prepend]
    exact hag
  · push Not at hL
    have h' : ∀ m₀ : M, ∃ b', ∀ a ∈ SA,
        (a.sent []).head? = some m₀ → ∃ o ∈ Q₂, Agree (dropFirst a) b' o :=
      fun m₀ => (hR m₀).resolve_left (hL m₀)
    choose f hf using h'
    refine Or.inr ⟨waitFirst f, fun a ha => ?_⟩
    obtain ⟨m₀, hm⟩ : ∃ m₀, (a.sent []).head? = some m₀ := by
      cases hs : a.sent [] with
      | nil => exact absurd hs (hspeak a ha)
      | cons x L => exact ⟨x, rfl⟩
    obtain ⟨o, hoQ, hag⟩ := hf m₀ a ha hm
    refine ⟨o, hoQ, ?_⟩
    rw [agree_feed hm, feed_waitFirst]
    exact hag

theorem dichotomy (N : ℕ) : Dichotomy M O N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro SA SB Q₁ Q₂ hbdd hsucc
  by_cases h1 : (∃ a ∈ SA, a.sent [] = []) ∧ ∃ b ∈ SB, b.sent [] = []
  · obtain ⟨⟨a₀, ha₀, hsa⟩, ⟨b₀, hb₀, hsb⟩⟩ := h1
    obtain ⟨o₀, ho₀, hag⟩ := hsucc a₀ ha₀ b₀ hb₀
    obtain ⟨hao, hbo⟩ := (agree_iff_of_silent (Or.inl hsb) (Or.inl hsa)).mp hag
    rcases ho₀ with hq | hq
    · refine Or.inl ⟨a₀, fun b hb => ?_⟩
      obtain ⟨o, -, hag'⟩ := hsucc a₀ ha₀ b hb
      have := ((agree_iff_of_silent (Or.inr (by simp [hao])) (Or.inl hsa)).mp hag').1
      rw [hao] at this; cases this
      exact ⟨o₀, hq, hag'⟩
    · refine Or.inr ⟨b₀, fun a ha => ?_⟩
      obtain ⟨o, -, hag'⟩ := hsucc a ha b₀ hb₀
      have := ((agree_iff_of_silent (Or.inl hsb) (Or.inr (by simp [hbo]))).mp hag').2
      rw [hbo] at this; cases this
      exact ⟨o₀, hq, hag'⟩
  · rw [not_and_or] at h1
    push Not at h1
    rcases h1 with h | h
    · exact dichotomy_step N ih SA SB Q₁ Q₂ hbdd hsucc h
    · rcases dichotomy_step N ih SB SA Q₂ Q₁ (fun b hb a ha => (hbdd a ha b hb).swap)
        (fun b hb a ha => by
          obtain ⟨o, ho, hag⟩ := hsucc a ha b hb
          exact ⟨o, Or.symm ho, agree_swap.mpr hag⟩) h with ⟨b', hb'⟩ | ⟨a', ha'⟩
      · refine Or.inr ⟨b', fun a ha => ?_⟩
        obtain ⟨o, ho, hag⟩ := hb' a ha
        exact ⟨o, ho, agree_swap.mp hag⟩
      · refine Or.inl ⟨a', fun b hb => ?_⟩
        obtain ⟨o, ho, hag⟩ := ha' b hb
        exact ⟨o, ho, agree_swap.mp hag⟩

/-- **Lemma F.2 of [YM18]** (generalized). For a two-party protocol with finite input sets (the
honest strategies of `A` form the finite set `SA`, those of `B` the finite set `SB`, the input space
being the product), if every honest execution terminates with a common output in `Q₁ ∪ Q₂`, then
`A` assures `Q₁` or `B` assures `Q₂`. With outputs `{0, 1}`: either `A` assures `0` or `B` assures
`1` (take `Q₁ = {0}`, `Q₂ = {1}`), and either `A` assures `1` or `B` assures `0`. No bound on the
number of messages is assumed: it follows from finiteness of the input sets. -/
theorem lemma_F2 {SA SB : Set (Proc M O)} (hA : SA.Finite) (hB : SB.Finite) {Q₁ Q₂ : Set O}
    (hsucc : ∀ a ∈ SA, ∀ b ∈ SB, ∃ o ∈ Q₁ ∪ Q₂, Agree a b o) :
    AssuresA SB Q₁ ∨ AssuresB SA Q₂ := by
  have : ∀ p : Proc M O × Proc M O, ∃ N, p.1 ∈ SA → p.2 ∈ SB → Bdd p.1 p.2 N := by
    intro p
    by_cases h : p.1 ∈ SA ∧ p.2 ∈ SB
    · obtain ⟨o, -, hag⟩ := hsucc _ h.1 _ h.2
      obtain ⟨N, hN⟩ := exists_bdd hag
      exact ⟨N, fun _ _ => hN⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose g hg using this
  obtain ⟨N, hN⟩ := ((hA.prod hB).image g).bddAbove
  exact dichotomy N SA SB Q₁ Q₂
    (fun a ha b hb => (hg (a, b) ha hb).mono (hN ⟨(a, b), ⟨ha, hb⟩, rfl⟩)) hsucc

end Podc.FairLeaderElection.Trees
