import Papers.PODC2013.CongestedCliqueRouting.Knowledge

/-!
# Composing intended runs

Tools used to build the sorting algorithm out of pieces:

* `ofList`/`toL`: packets given by lists of items (at most `B` of them);
* `mapRun`: applying an injective packet encoding round by round preserves locality
  (`isLocal_mapRun`); used for padding packets (`pad`) and for encoding messages `(x, w)`
  (a key together with its destination) as two items (`pairP`);
* `determined_segment`: a sub-run started at round `t₀` whose inputs are known at `t₀` is local.
-/

set_option linter.unusedSectionVars false

namespace CongestedCliqueRouting

open Finset

/-! ### Packets from lists -/

section Lists

variable {M : Type*} {B : ℕ}

/-- The packet whose slots are the items of `l` (truncated to `B`). -/
def ofList (l : List (Item M)) : Packet M B := fun i => l[i.val]?

/-- The items of a packet, in slot order. -/
def toL (p : Packet M B) : List (Item M) := (List.ofFn p).reduceOption

lemma ofFn_ofList {l : List (Item M)} (h : l.length ≤ B) :
    List.ofFn (ofList l : Packet M B) = l.map some ++ List.replicate (B - l.length) none := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, ofList]
    by_cases hi : i < l.length
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [hi]

lemma toL_ofList {l : List (Item M)} (h : l.length ≤ B) : toL (ofList l : Packet M B) = l := by
  unfold toL
  rw [ofFn_ofList h, List.reduceOption_append]
  have h1 : ∀ l : List (Item M), (l.map some).reduceOption = l := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [List.reduceOption_cons_of_some, ih]
  have h2 : ∀ k, (List.replicate k (none : Option (Item M))).reduceOption = [] := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, List.reduceOption_cons_of_none, ih]
  rw [h1, h2, List.append_nil]

lemma ofList_eq_some {l : List (Item M)} {i : Fin B} {x : Item M}
    (h : (ofList l : Packet M B) i = some x) : x ∈ l := by
  unfold ofList at h
  exact List.mem_of_getElem? h

lemma ofList_nil : (ofList [] : Packet M B) = fun _ => none := by
  funext i; simp [ofList]

end Lists

/-- Decoding a list of (message, number) pairs. -/
def pairsL {M : Type*} : List (Item M) → List (M × ℕ)
  | Item.msg x :: Item.num k :: rest => (x, k) :: pairsL rest
  | _ => []

lemma pairsL_flatten {M : Type*} (L : List (M × ℕ)) :
    pairsL (L.flatMap fun p => [Item.msg p.1, Item.num p.2]) = L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [pairsL, ih]

/-! ### Mapping packets round by round -/

section MapRun

variable {I V K M M' : Type*} {B B' : ℕ}

/-- Applying a packet encoding `F` to every packet of a run. -/
def mapRun (F : Packet M B → Packet M' B') (S : Run I V M B) : Run I V M' B' :=
  fun d t u v => F (S d t u v)

theorem isLocal_mapRun {inp : I → V → K} {S : Run I V M B} (hS : IsLocal inp S)
    {F : Packet M B → Packet M' B'} {G : Packet M' B' → Packet M B} (hFG : ∀ p, G (F p) = p) :
    IsLocal inp (mapRun F S) := by
  intro t v d d' hv
  have hsame : SameView inp S d d' t v :=
    ⟨hv.1, fun r hr u => by
      have := congrArg G (hv.2 r hr u)
      simpa [mapRun, hFG] using this⟩
  show (fun w => F (S d t v w)) = fun w => F (S d' t v w)
  have := hS t v d d' hsame
  simp only at this
  rw [this]

lemma Determined.of_mapRun {inp : I → V → K} {S : Run I V M B}
    {F : Packet M B → Packet M' B'} {G : Packet M' B' → Packet M B} (hFG : ∀ p, G (F p) = p)
    {t : ℕ} {v : V} {α : Sort*} {f : I → α} (h : Determined inp S t v f) :
    Determined inp (mapRun F S) t v f :=
  fun d d' hv => h d d' ⟨hv.1, fun r hr u => by
    have := congrArg G (hv.2 r hr u)
    simpa [mapRun, hFG] using this⟩

/-- Padding a packet with empty slots. -/
def pad (h : B ≤ B') (p : Packet M B) : Packet M B' :=
  fun i => if hi : i.val < B then p ⟨i.val, hi⟩ else none

/-- Removing padding. -/
def unpad (h : B ≤ B') (p : Packet M B') : Packet M B :=
  fun i => p ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma unpad_pad (h : B ≤ B') (p : Packet M B) : unpad h (pad h p) = p := by
  funext i; simp [pad, unpad]

lemma pad_eq_some {h : B ≤ B'} {p : Packet M B} {i : Fin B'} {x : Item M}
    (hp : pad h p i = some x) : ∃ j : Fin B, p j = some x := by
  unfold pad at hp
  split_ifs at hp with hi
  exact ⟨_, hp⟩

lemma pad_apply (h : B ≤ B') (p : Packet M B) (j : Fin B) :
    pad h p ⟨j.val, lt_of_lt_of_le j.isLt h⟩ = p j := by
  simp [pad]

end MapRun

/-! ### Encoding `(key, destination)` messages as two items -/

section Pair

variable {V M : Type*} {B : ℕ}

/-- Slot `(i, b)` of a paired packet. -/
def pslot (i : Fin B) (b : Fin 2) : Fin (B * 2) := finProdFinEquiv (i, b)

/-- Encode the message `(x, w)` as the two items `x`, `enc w`. -/
def pairP (enc : V → ℕ) (p : Packet (M × V) B) : Packet M (B * 2) := fun ℓ =>
  match p (finProdFinEquiv.symm ℓ).1, (finProdFinEquiv.symm ℓ).2 with
  | some (Item.msg (x, _)), 0 => some (Item.msg x)
  | some (Item.msg (_, w)), 1 => some (Item.num (enc w))
  | some (Item.num k), 0 => some (Item.num k)
  | _, _ => none

/-- Decoding. -/
def unpairP (dec : ℕ → Option V) (q : Packet M (B * 2)) : Packet (M × V) B := fun i =>
  match q (pslot i 0), q (pslot i 1) with
  | some (Item.msg x), some (Item.num k) => (dec k).map fun w => Item.msg (x, w)
  | some (Item.num k), _ => some (Item.num k)
  | _, _ => none

lemma pairP_slot (enc : V → ℕ) (p : Packet (M × V) B) (i : Fin B) (b : Fin 2) :
    pairP enc p (pslot i b) =
      match p i, b with
      | some (Item.msg (x, _)), 0 => some (Item.msg x)
      | some (Item.msg (_, w)), 1 => some (Item.num (enc w))
      | some (Item.num k), 0 => some (Item.num k)
      | _, _ => none := by
  simp [pairP, pslot]

lemma unpairP_pairP {enc : V → ℕ} {dec : ℕ → Option V} (hd : ∀ w, dec (enc w) = some w)
    (p : Packet (M × V) B) : unpairP dec (pairP enc p) = p := by
  funext i
  simp only [unpairP, pairP_slot]
  rcases h : p i with _ | ⟨⟨x, w⟩ | k⟩ <;> simp [hd]

lemma pairP_eq_some {enc : V → ℕ} {p : Packet (M × V) B} {ℓ : Fin (B * 2)} {y : Item M}
    (h : pairP enc p ℓ = some y) :
    (∃ i x w, p i = some (Item.msg (x, w)) ∧ (y = Item.msg x ∨ y = Item.num (enc w))) ∨
      ∃ i k, p i = some (Item.num k) ∧ y = Item.num k := by
  unfold pairP at h
  split at h
  · rename_i x w hp _
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨_, x, w, hp, Or.inl h.symm⟩
  · rename_i x w hp _
    simp only [Option.some.injEq] at h
    exact Or.inl ⟨_, x, w, hp, Or.inr h.symm⟩
  · rename_i k hp _
    simp only [Option.some.injEq] at h
    exact Or.inr ⟨_, k, hp, h.symm⟩
  · simp at h

lemma pairP_msg {enc : V → ℕ} {p : Packet (M × V) B} {i : Fin B} {x : M} {w : V}
    (h : p i = some (Item.msg (x, w))) : pairP enc p (pslot i 0) = some (Item.msg x) := by
  rw [pairP_slot, h]
  rfl

end Pair

/-! ### Sub-runs started at a later round -/

section Segment

variable {I V K K' M : Type*} {B : ℕ}

/-- Knowledge in a sub-run transfers to the embedding run. -/
theorem Determined.of_segment {inp : I → V → K} {inpSub : I → V → K'} {S Ssub : Run I V M B}
    {t0 len : ℕ} (heq : ∀ d r, r < len → S d (t0 + r) = Ssub d r)
    (hinp : ∀ v, Determined inp S t0 v fun d => inpSub d v) {r : ℕ} (hr : r ≤ len) {v : V}
    {α : Sort*} {f : I → α} (h : Determined inpSub Ssub r v f) :
    Determined inp S (t0 + r) v f := by
  intro d d' hv
  refine h d d' ⟨(hinp v).mono (Nat.le_add_right t0 r) d d' hv, fun r' hr' u => ?_⟩
  rw [← heq d r' (by omega), ← heq d' r' (by omega)]
  exact hv.2 (t0 + r') (by omega) u

/-- A sub-run `Ssub`, local w.r.t. inputs `inpSub` known at round `t₀`, embedded at rounds
`t₀, t₀ + 1, …` of `S`, is local there. -/
theorem determined_segment {inp : I → V → K} {inpSub : I → V → K'} {S Ssub : Run I V M B}
    {t0 len : ℕ} (hsub : IsLocal inpSub Ssub) (heq : ∀ d r, r < len → S d (t0 + r) = Ssub d r)
    (hinp : ∀ v, Determined inp S t0 v fun d => inpSub d v) {r : ℕ} (hr : r < len) (v : V) :
    Determined inp S (t0 + r) v fun d => S d (t0 + r) v := by
  intro d d' hv
  have hsame : SameView inpSub Ssub d d' r v := by
    refine ⟨(hinp v).mono (Nat.le_add_right t0 r) d d' hv, fun r' hr' u => ?_⟩
    rw [← heq d r' (by omega), ← heq d' r' (by omega)]
    exact hv.2 (t0 + r') (by omega) u
  show S d (t0 + r) v = S d' (t0 + r) v
  rw [heq d r hr, heq d' r hr]
  exact hsub r v d d' hsame

/-- Holding in a sub-run transfers to the embedding run. -/
lemma HoldsS.of_segment [DecidableEq M] {msgs msgsSub : I → V → Finset M} {S Ssub : Run I V M B}
    {t0 len : ℕ} (heq : ∀ d r, r < len → S d (t0 + r) = Ssub d r)
    (hinit : ∀ d v m, m ∈ msgsSub d v → HoldsS msgs S d t0 v m) {d : I} {r : ℕ} {v : V} {m : M}
    (hr : r ≤ len) (h : HoldsS msgsSub Ssub d r v m) : HoldsS msgs S d (t0 + r) v m := by
  rcases h with h | ⟨r', hr', u, i, h⟩
  · exact (hinit d v m h).mono (Nat.le_add_right _ _)
  · exact Or.inr ⟨t0 + r', by omega, u, i, by rw [heq d r' (by omega)]; exact h⟩

end Segment

end CongestedCliqueRouting
