import Papers.PODC2016.CollaborativeListSpec.Model

/-!
# Generic happens-before facts

Facts about happens-before in executions (`Model.lean`) used for the correctness proof of RGA,
independent of the protocol:

* `HB.exists_send`: happens-before leaving a replica goes through a later send of that replica.
* `Known α m r q`: event `q` happens before (or is) some event of replica `r` among the first `m`
  events. How it evolves with one more event (`known_succ_*`); for a receive this uses causal
  broadcast (`known_succ_recv`).
* `Window α m r q`: `q` is an event of `r` after the last send of `r` before position `m` (the
  events whose effects are in the send buffer).

-- CSLib candidate: generic facts on happens-before / causal broadcast.
-/

namespace Podc.CollaborativeListSpec

variable {Rep Op : Type}

/-- Every receive of `α` refers to a send event (a consequence of well-formedness). -/
def RecvOfSend (α : List (Act Rep Op)) : Prop :=
  ∀ c r s, α[c]? = some (Act.recv r s) → s < c ∧ ∃ r', α[s]? = some (Act.send r')

/-- Event `q` is `≤hb` some event of replica `r` among the first `m` events. -/
def Known (α : List (Act Rep Op)) (m : ℕ) (r : Rep) (q : ℕ) : Prop :=
  ∃ e a, e < m ∧ α[e]? = some a ∧ a.rep = r ∧ (q = e ∨ HB α q e)

/-- Event `q` is an event of `r` before position `m` with no send of `r` in between. -/
def Window (α : List (Act Rep Op)) (m : ℕ) (r : Rep) (q : ℕ) : Prop :=
  q < m ∧ (∃ a, α[q]? = some a ∧ a.rep = r) ∧ ∀ j, q < j → j < m → α[j]? ≠ some (Act.send r)

variable {α : List (Act Rep Op)}

/-- Happens-before from `i` to an event of another replica goes through a send of the replica
of `i` at or after `i`. -/
theorem HB.exists_send (hR : RecvOfSend α) {i j : ℕ} (h : HB α i j) {a b : Act Rep Op}
    (ha : α[i]? = some a) (hb : α[j]? = some b) (hab : a.rep ≠ b.rep) :
    ∃ s, i ≤ s ∧ α[s]? = some (Act.send a.rep) ∧ HB α s j := by
  induction h using Relation.TransGen.head_induction_on generalizing a with
  | single h =>
    rename_i i
    obtain ⟨hij, a', b', ha', hb', hrel⟩ := h
    rw [ha, Option.some.injEq] at ha'; subst ha'
    rw [hb, Option.some.injEq] at hb'; subst hb'
    rcases hrel with hrel | hrel
    · exact absurd hrel hab
    · cases b with
      | doOp => cases hrel
      | send => cases hrel
      | recv r s =>
        simp only [Act.src?_recv, Option.some.injEq] at hrel; subst hrel
        obtain ⟨-, r', hr'⟩ := hR _ _ _ hb
        rw [ha, Option.some.injEq] at hr'; subst hr'
        exact ⟨s, le_rfl, ha, Relation.TransGen.single ⟨hij, _, _, ha, hb, Or.inr rfl⟩⟩
  | head h' h ih =>
    rename_i i c
    obtain ⟨hic, a', c', ha', hc', hrel⟩ := h'
    rw [ha, Option.some.injEq] at ha'; subst ha'
    by_cases hac : c'.rep = a.rep
    · obtain ⟨s, hcs, hs, hsj⟩ := ih hc' (by rwa [hac])
      exact ⟨s, by omega, by rw [hs, hac], hsj⟩
    · rcases hrel with hrel | hrel
      · exact absurd hrel.symm hac
      · cases c' with
        | doOp => cases hrel
        | send => cases hrel
        | recv r s =>
          simp only [Act.src?_recv, Option.some.injEq] at hrel; subst hrel
          obtain ⟨-, r', hr'⟩ := hR _ _ _ hc'
          rw [ha, Option.some.injEq] at hr'; subst hr'
          exact ⟨s, le_rfl, ha, Relation.TransGen.head ⟨hic, _, _, ha, hc', Or.inr rfl⟩ h⟩

theorem Known.mono {m m' : ℕ} {r : Rep} {q : ℕ} (h : Known α m r q) (hm : m ≤ m') :
    Known α m' r q := by
  obtain ⟨e, a, he, hea, har, hq⟩ := h
  exact ⟨e, a, by omega, hea, har, hq⟩

theorem Known.of_hb {m : ℕ} {r : Rep} {q q' : ℕ} (h : Known α m r q) (hq : HB α q' q) :
    Known α m r q' := by
  obtain ⟨e, a, he, hea, har, hqe⟩ := h
  refine ⟨e, a, he, hea, har, Or.inr ?_⟩
  rcases hqe with rfl | hqe
  · exact hq
  · exact hq.trans hqe

theorem known_succ_of_ne {m : ℕ} {r : Rep} {a : Act Rep Op} (hm : α[m]? = some a) (hr : a.rep ≠ r)
    (q : ℕ) : Known α (m + 1) r q ↔ Known α m r q := by
  refine ⟨fun ⟨e, b, he, heb, hbr, hq⟩ => ?_, fun h => h.mono (by omega)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
  · exact ⟨e, b, he, heb, hbr, hq⟩
  · rw [hm] at heb; cases heb; exact absurd hbr hr

/-- `q` is known at `r` after the event `p` of `r` (not a receive) iff `q ≤hb p`. -/
theorem known_succ_iff {p : ℕ} {a : Act Rep Op} (hp : α[p]? = some a) (q : ℕ) : Known α (p + 1) a.rep q ↔ q = p ∨ HB α q p := by
  constructor
  · rintro ⟨e, b, he, heb, hbr, hq⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · have hep : HB α e p := HB.of_rep he heb hp hbr
      right
      rcases hq with rfl | hq
      · exact hep
      · exact hq.trans hep
    · exact hq
  · intro h
    exact ⟨p, a, by omega, hp, rfl, h⟩

theorem known_succ_of_not_recv {m : ℕ} {a : Act Rep Op} (hm : α[m]? = some a)
    (hnr : a.src? = none) (q : ℕ) :
    Known α (m + 1) a.rep q ↔ Known α m a.rep q ∨ q = m := by
  rw [known_succ_iff hm]
  constructor
  · rintro (rfl | hq)
    · exact Or.inr rfl
    · obtain ⟨k, b, hk, hkb, hbr, hqk⟩ := hq.of_not_recv hm hnr
      exact Or.inl ⟨k, b, hk, hkb, hbr, hqk⟩
  · rintro (⟨e, b, he, heb, hbr, hq⟩ | rfl)
    · have hep : HB α e m := HB.of_rep he heb hm hbr
      right
      rcases hq with rfl | hq
      · exact hep
      · exact hq.trans hep
    · exact Or.inl rfl

/-- What a receive at `r` adds to the knowledge of `r` (for `do` events): exactly the events in
the send window of the received message. Uses causal broadcast. -/
theorem known_succ_recv (hR : RecvOfSend α) (hC : CausalBroadcast α) {m src : ℕ} {r r'' : Rep}
    (hm : α[m]? = some (Act.recv r src)) (hsrc : α[src]? = some (Act.send r''))
    {q : ℕ} {rq : Rep} {op : Op} (hq : α[q]? = some (Act.doOp rq op)) :
    Known α (m + 1) r q ↔ Known α m r q ∨ Window α src r'' q := by
  constructor
  · rintro ⟨e, b, he, heb, hbr, hqe⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | he
    · exact Or.inl ⟨e, b, he, heb, hbr, hqe⟩
    subst e
    rw [hm] at heb; cases heb
    rcases hqe with rfl | hqe
    · rw [hm] at hq; cases hq
    obtain ⟨k, hqk, hkm, c, d, hc, hd, hcd⟩ := hqe.cases_last
    rw [hm, Option.some.injEq] at hd; subst hd
    rcases hcd with hrep | hsk
    · exact Or.inl ⟨k, c, hkm, hc, hrep, hqk⟩
    simp only [Act.src?_recv, Option.some.injEq] at hsk; subst k
    rw [hsrc] at hc; cases hc
    rcases hqk with hqk | hqk
    · subst hqk; rw [hsrc] at hq; cases hq
    -- `q` happens before the send `src`, which is received at `m`
    have recv_of : ∀ j, α[j]? = some (Act.send rq) → q < j → HB α j src → Known α m r q := by
      intro j hj hqj hjk
      obtain ⟨q', hq'm, hq'⟩ := hC j src r m ⟨_, hj⟩ ⟨_, hsrc⟩ hjk hm
      have hjq' : HB α j q' := HB.of_recv (hR _ _ _ hq').1 hj hq'
      have hqj : HB α q j := HB.of_rep hqj hq hj rfl
      exact ⟨q', _, hq'm, hq', rfl, Or.inr (hqj.trans hjq')⟩
    by_cases hrq : rq = r''
    · subst hrq
      by_cases hw : ∀ j, q < j → j < src → α[j]? ≠ some (Act.send rq)
      · exact Or.inr ⟨hqk.lt, ⟨_, hq, rfl⟩, hw⟩
      · push Not at hw
        obtain ⟨j, hqj, hjk, hj⟩ := hw
        exact Or.inl (recv_of j hj hqj (HB.of_rep hjk hj hsrc rfl))
    · obtain ⟨s, hqs, hs, hsk⟩ := hqk.exists_send hR hq hsrc (by simpa using hrq)
      rcases Nat.lt_or_eq_of_le hqs with hqs | rfl
      · exact Or.inl (recv_of s hs hqs hsk)
      · rw [hs] at hq; cases hq
  · rintro (h | ⟨hqs, ⟨b, hb, hbr⟩, -⟩)
    · exact h.mono (by omega)
    · 
      exact ⟨m, _, by omega, hm, rfl, Or.inr ((HB.of_rep hqs hb hsrc (by simpa using hbr)).trans
        (HB.of_recv (hR _ _ _ hm).1 hsrc hm))⟩

theorem window_succ_of_ne {m : ℕ} {r : Rep} {a : Act Rep Op} (hm : α[m]? = some a)
    (hr : a.rep ≠ r) (q : ℕ) : Window α (m + 1) r q ↔ Window α m r q := by
  constructor
  · rintro ⟨hq, ⟨b, hb, hbr⟩, hw⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
    · exact ⟨hq, ⟨b, hb, hbr⟩, fun j h1 h2 => hw j h1 (by omega)⟩
    · subst q; rw [hm, Option.some.injEq] at hb; subst hb; exact absurd hbr hr
  · rintro ⟨hq, hb, hw⟩
    refine ⟨by omega, hb, fun j h1 h2 => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
    · exact hw j h1 h2
    · subst j; rw [hm]; intro h; rw [Option.some.injEq] at h; subst h; exact hr rfl

theorem window_succ_self {m : ℕ} {a : Act Rep Op} (hm : α[m]? = some a)
    (hs : ∀ r', a ≠ Act.send r') (q : ℕ) :
    Window α (m + 1) a.rep q ↔ Window α m a.rep q ∨ q = m := by
  constructor
  · rintro ⟨hq, hb, hw⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
    · exact Or.inl ⟨hq, hb, fun j h1 h2 => hw j h1 (by omega)⟩
    · exact Or.inr hq
  · rintro (⟨hq, hb, hw⟩ | rfl)
    · refine ⟨by omega, hb, fun j h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
      · exact hw j h1 h2
      · subst j; rw [hm]; intro h; rw [Option.some.injEq] at h; exact hs _ h
    · exact ⟨by omega, ⟨a, hm, rfl⟩, fun j h1 h2 => by omega⟩

theorem window_succ_send {m : ℕ} {r : Rep} (hm : α[m]? = some (Act.send r)) {q : ℕ}
    (h : Window α (m + 1) r q) : q = m := by
  obtain ⟨hq, -, hw⟩ := h
  by_contra hne
  exact hw m (by omega) (by omega) hm

end Podc.CollaborativeListSpec
