import Mathlib

/-!
# Distributed alphabets, well-formed ω-words and real-time oblivious languages (Section 2, §5.2)

Castañeda, Rodríguez, *Asynchronous Fault-Tolerant Language Decidability for Runtime
Verification of Distributed Systems*, PODC 2025 (arXiv 2502.00191v3).

* `Sym I O` — the distributed alphabet `Σ = ⋃ᵢ Σᵢ`, `Σᵢ = Σᵢ< ∪ Σᵢ>`: a symbol is a process `p`
  together with an invocation symbol (`I p`) or a response symbol (`O p`). Local alphabets are
  disjoint because the process is part of the symbol.
* `WF` — Definition 2.1 (well-formed ω-words). Condition (3) (fairness) is automatic for
  `ℕ`-indexed words.
* `RTO` — Definition 5.3 (real-time oblivious languages). The shuffle `α|1 ⧢ ⋯ ⧢ α|n`
  (Definition 5.2) is the set of words `α'` with `α'|p = α|p` for every process `p`.
* `rto_iff_swapClosed` — a language is real-time oblivious iff it is closed under transposing two
  adjacent symbols of different processes (at any finite position).
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type}

/-- Symbols of the distributed alphabet: a process and an invocation or a response symbol. -/
abbrev Sym (I O : Fin n → Type) := Σ p : Fin n, I p ⊕ O p

/-- ω-words over the distributed alphabet. -/
abbrev Word (I O : Fin n → Type) := ℕ → Sym I O

/-- `cnt x p k`: the number of symbols of process `p` among the first `k` symbols of `x`. -/
def cnt (x : Word I O) (p : Fin n) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cnt x p k + if (x k).1 = p then 1 else 0

/-- **Definition 2.1** (well-formed ω-words): every local word is infinite (reliability) and
alternates invocations and responses, starting with an invocation (sequentiality). -/
structure WF (x : Word I O) : Prop where
  reliable : ∀ p N, ∃ m, N ≤ m ∧ (x m).1 = p
  seq : ∀ m, (x m).2.isLeft = true ↔ Even (cnt x (x m).1 m)

/-- **Definition 2.2**: a distributed language is a set of well-formed ω-words. -/
def IsDistLang (L : Set (Word I O)) : Prop := ∀ x ∈ L, WF x

/-- The finite prefix of length `k`. -/
def pfx (x : Word I O) (k : ℕ) : List (Sym I O) := (List.range k).map x

/-- The suffix starting at position `k`. -/
def shift (x : Word I O) (k : ℕ) : Word I O := fun m => x (m + k)

/-- `app l y` is the ω-word `l y` (finite word followed by an ω-word). -/
def app (l : List (Sym I O)) (y : Word I O) : Word I O :=
  fun m => if h : m < l.length then l[m] else y (m - l.length)

/-- The local word of process `p` in a finite word. -/
def proj (p : Fin n) (l : List (Sym I O)) : List (Sym I O) := l.filter (fun a => decide (a.1 = p))

/-- **Definition 5.3** (real-time oblivious languages): for every `αβ ∈ L` with `α` finite and
every `α' ∈ α|1 ⧢ ⋯ ⧢ α|n` (i.e. `α'|p = α|p` for every `p`), `α'β ∈ L`. -/
def RTO (L : Set (Word I O)) : Prop :=
  ∀ x ∈ L, ∀ (k : ℕ) (α' : List (Sym I O)), (∀ p, proj p α' = proj p (pfx x k)) →
    app α' (shift x k) ∈ L

/-- Transposition of the symbols at positions `k` and `k + 1`. -/
def swapAt (x : Word I O) (k : ℕ) : Word I O := fun m => x (Equiv.swap k (k + 1) m)

/-- Closure under transposing two adjacent symbols of different processes. -/
def SwapClosed (L : Set (Word I O)) : Prop :=
  ∀ x ∈ L, ∀ k, (x k).1 ≠ (x (k + 1)).1 → swapAt x k ∈ L

/-! ### Basic lemmas on `app`, `pfx`, `shift` -/

@[simp] lemma length_pfx (x : Word I O) (k : ℕ) : (pfx x k).length = k := by simp [pfx]

lemma app_lt {l : List (Sym I O)} {y : Word I O} {m : ℕ} (h : m < l.length) :
    app l y m = l[m] := by simp [app, h]

lemma app_ge {l : List (Sym I O)} {y : Word I O} {m : ℕ} (h : l.length ≤ m) :
    app l y m = y (m - l.length) := by simp [app, Nat.not_lt.2 h]

lemma app_pfx_shift (x : Word I O) (k : ℕ) : app (pfx x k) (shift x k) = x := by
  funext m
  by_cases h : m < k
  · rw [app_lt (by simpa using h)]; simp [pfx]
  · rw [app_ge (by simpa using Nat.not_lt.1 h)]; simp [shift]; congr 1; omega

/-! ### Adjacent transpositions of finite words -/

/-- One transposition of two adjacent symbols of different processes. -/
def AdjSwap (l l' : List (Sym I O)) : Prop :=
  ∃ (u v : List (Sym I O)) (a b : Sym I O), a.1 ≠ b.1 ∧ l = u ++ a :: b :: v ∧ l' = u ++ b :: a :: v

lemma AdjSwap.cons {l l' : List (Sym I O)} (h : AdjSwap l l') (c : Sym I O) :
    AdjSwap (c :: l) (c :: l') := by
  obtain ⟨u, v, a, b, hab, rfl, rfl⟩ := h
  exact ⟨c :: u, v, a, b, hab, rfl, rfl⟩

lemma rtg_adjSwap_cons {l l' : List (Sym I O)} (h : Relation.ReflTransGen AdjSwap l l')
    (c : Sym I O) : Relation.ReflTransGen AdjSwap (c :: l) (c :: l') :=
  Relation.ReflTransGen.lift (c :: ·) (fun _ _ (h : AdjSwap _ _) => h.cons c) _ _ h

/-- Bubbling `b` to the front past symbols of other processes. -/
lemma rtg_bubble (b : Sym I O) (w : List (Sym I O)) :
    ∀ u : List (Sym I O), (∀ a ∈ u, a.1 ≠ b.1) →
      Relation.ReflTransGen AdjSwap (u ++ b :: w) (b :: (u ++ w))
  | [], _ => Relation.ReflTransGen.refl
  | c :: u, hu => by
    have ih := rtg_bubble b w u (fun a ha => hu a (List.mem_cons_of_mem _ ha))
    refine (rtg_adjSwap_cons ih c).tail ?_
    exact ⟨[], u ++ w, c, b, hu c List.mem_cons_self, rfl, rfl⟩

lemma proj_append (p : Fin n) (l l' : List (Sym I O)) :
    proj p (l ++ l') = proj p l ++ proj p l' := by simp [proj]

lemma proj_cons (p : Fin n) (a : Sym I O) (l : List (Sym I O)) :
    proj p (a :: l) = if a.1 = p then a :: proj p l else proj p l := by
  by_cases h : a.1 = p <;> simp [proj, h]

/-- Any word with the same local words as `α` is reachable from `α` by adjacent transpositions
of symbols of different processes ("bubble sort"). -/
theorem rtg_adjSwap_of_proj :
    ∀ (α' α : List (Sym I O)), (∀ p, proj p α' = proj p α) →
      Relation.ReflTransGen AdjSwap α α'
  | [], α, h => by
    cases α with
    | nil => exact Relation.ReflTransGen.refl
    | cons a α =>
      have := h a.1
      simp [proj] at this
  | b :: rest, α, h => by
    have hb := h b.1
    rw [proj_cons] at hb
    simp only [ite_true] at hb
    obtain ⟨u, w, rfl, hu, -, hw⟩ := List.filter_eq_cons_iff.1 hb.symm
    have hu' : ∀ a ∈ u, a.1 ≠ b.1 := fun a ha => by simpa using hu a ha
    have hrest : ∀ p, proj p rest = proj p (u ++ w) := by
      intro p
      have hp := h p
      rw [proj_cons, proj_append, proj_cons] at hp
      by_cases hbp : b.1 = p
      · subst hbp
        have hu0 : proj b.1 u = [] := by
          simp only [proj, List.filter_eq_nil_iff]; intro a ha; simpa using hu' a ha
        simp only [ite_true, hu0, List.nil_append, List.cons.injEq, true_and] at hp
        rw [proj_append, hu0, hp]; rfl
      · simp only [hbp, ite_false] at hp
        rw [hp, proj_append]
    exact (rtg_bubble b w u hu').trans (rtg_adjSwap_cons (rtg_adjSwap_of_proj rest _ hrest) b)

/-- An adjacent transposition inside the finite part of `app l y` is `swapAt`. -/
lemma app_adjSwap {u v : List (Sym I O)} {a b : Sym I O} (y : Word I O) :
    app (u ++ b :: a :: v) y = swapAt (app (u ++ a :: b :: v) y) u.length := by
  funext m
  simp only [swapAt]
  rcases lt_trichotomy m u.length with h | h | h
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    rw [app_lt (by simp; omega), app_lt (by simp; omega)]
    simp [List.getElem_append_left h]
  · subst h; rw [Equiv.swap_apply_left, app_lt (by simp), app_lt (by simp)]; simp
  · rcases Nat.lt_or_ge (u.length + 1) m with h' | h'
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      by_cases hm : m < (u ++ a :: b :: v).length
      · rw [app_lt (by simpa using hm), app_lt (by simpa using hm)]
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        obtain ⟨j, hj⟩ : ∃ j, m - u.length = j + 2 := ⟨m - u.length - 2, by omega⟩
        simp [hj]
      · rw [app_ge (by simp at hm ⊢; omega), app_ge (by simp at hm ⊢; omega)]; simp
    · have : m = u.length + 1 := by omega
      subst this; rw [Equiv.swap_apply_right, app_lt (by simp), app_lt (by simp)]; simp

/-- Closure under adjacent transpositions implies real-time obliviousness. -/
theorem rto_of_swapClosed {L : Set (Word I O)} (hL : SwapClosed L) : RTO L := by
  intro x hx k α' hα'
  have hrt := rtg_adjSwap_of_proj α' (pfx x k) hα'
  have key : ∀ l, Relation.ReflTransGen AdjSwap (pfx x k) l → app l (shift x k) ∈ L := by
    intro l hl
    induction hl with
    | refl => rwa [app_pfx_shift]
    | tail _ hs ih =>
      obtain ⟨u, v, a, b, hab, rfl, rfl⟩ := hs
      rw [app_adjSwap]
      refine hL _ ih _ ?_
      rw [app_lt (by simp), app_lt (by simp)]
      simpa using hab
  exact key α' hrt

lemma swapAt_apply_left (x : Word I O) (k : ℕ) : swapAt x k k = x (k + 1) := by
  simp [swapAt]

lemma swapAt_apply_right (x : Word I O) (k : ℕ) : swapAt x k (k + 1) = x k := by
  simp [swapAt]

lemma swapAt_apply_of_ne (x : Word I O) {k m : ℕ} (h1 : m ≠ k) (h2 : m ≠ k + 1) :
    swapAt x k m = x m := by
  simp [swapAt, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Real-time obliviousness implies closure under adjacent transpositions. -/
theorem swapClosed_of_rto {L : Set (Word I O)} (hL : RTO L) : SwapClosed L := by
  intro x hx k hk
  have hpfx : ∀ y : Word I O, pfx y (k + 2) = pfx y k ++ [y k, y (k + 1)] := by
    intro y; simp [pfx, List.range_succ]
  have h := hL x hx (k + 2) (pfx (swapAt x k) (k + 2)) ?_
  · convert h using 1
    have hs : shift (swapAt x k) (k + 2) = shift x (k + 2) := by
      funext m; simp only [shift]; rw [swapAt_apply_of_ne] <;> omega
    rw [← hs, app_pfx_shift]
  · intro p
    rw [hpfx, hpfx, proj_append, proj_append, swapAt_apply_left, swapAt_apply_right]
    have hpre : pfx (swapAt x k) k = pfx x k := by
      simp only [pfx, List.map_inj_left, List.mem_range]
      intro m hm; rw [swapAt_apply_of_ne] <;> omega
    rw [hpre]
    congr 1
    simp only [proj_cons]
    by_cases h1 : (x k).1 = p <;> by_cases h2 : (x (k + 1)).1 = p
    · exact absurd (h1.trans h2.symm) hk
    all_goals simp [h1, h2, proj]

/-- A language is real-time oblivious iff it is closed under adjacent transpositions of symbols
of different processes. -/
-- CSLib candidate
theorem rto_iff_swapClosed {L : Set (Word I O)} : RTO L ↔ SwapClosed L :=
  ⟨swapClosed_of_rto, rto_of_swapClosed⟩

/-! ### Counting lemmas -/

lemma cnt_succ (x : Word I O) (p : Fin n) (k : ℕ) :
    cnt x p (k + 1) = cnt x p k + if (x k).1 = p then 1 else 0 := rfl

lemma cnt_mono (x : Word I O) (p : Fin n) {k m : ℕ} (h : k ≤ m) : cnt x p k ≤ cnt x p m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [cnt_succ]; omega

end Podc2025.LanguageDecidability
