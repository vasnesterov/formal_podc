import Papers.PODC2022.AnonymousMACConsensus.Model

/-!
# MAC-SC: the inductive invariant

The invariant `Inv` of reachable configurations of MAC-SC (with handler priority). It consists of

* `HInv`: well-formedness of the history (node `i`'s operations are numbered `0, 1, …` and are
  sequential) and facts recorded when a collect read its view (`PastOK`: every store or collect
  completed before the collect's invocation is reflected in the view it returns);
* knowledge facts (`Knows`): every completed operation's broadcast has reached every node that has
  not crashed (in its view or in its handler queue) — the "durable and timely" insight of the paper.
-/

namespace Podc.AnonymousMACConsensus

variable {ι V : Type*}

/-! ## List positions -/

lemma lt_length_of_getElem?_eq_some {α : Type*} {l : List α} {p : ℕ} {a : α}
    (hp : l[p]? = some a) : p < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at hp
  exact absurd hp (by simp)

lemma getElem?_append_of_lt {α : Type*} {l t : List α} {p : ℕ} (hp : p < l.length) :
    (l ++ t)[p]? = l[p]? := List.getElem?_append_left hp

lemma getElem?_append_of_eq_some {α : Type*} {l t : List α} {p : ℕ} {a : α}
    (hp : l[p]? = some a) : (l ++ t)[p]? = some a := by
  rw [getElem?_append_of_lt (lt_length_of_getElem?_eq_some hp), hp]

lemma getElem?_append_singleton {α : Type*} {l : List α} {e f : α} {p : ℕ} :
    (l ++ [e])[p]? = some f ↔ l[p]? = some f ∨ (p = l.length ∧ f = e) := by
  constructor
  · intro hp
    rcases lt_or_ge p l.length with h | h
    · left; rwa [getElem?_append_of_lt h] at hp
    · right
      rw [List.getElem?_append_right h] at hp
      have : p - l.length = 0 := by
        by_contra hc
        rw [List.getElem?_eq_none (by simp; omega)] at hp
        exact absurd hp (by simp)
      rw [this] at hp
      simp at hp
      exact ⟨by omega, hp.symm⟩
  · rintro (hp | ⟨rfl, rfl⟩)
    · exact getElem?_append_of_eq_some hp
    · simp

lemma mem_iff_getElem? {α : Type*} {l : List α} {a : α} : a ∈ l ↔ ∃ p : ℕ, l[p]? = some a :=
  List.mem_iff_getElem?

/-! ## Views -/

lemma key_newer (x y : Option (Entry V)) : key (newer x y) = max (key x) (key y) := by
  unfold newer; split_ifs <;> omega

lemma newer_cases (x y : Option (Entry V)) : newer x y = x ∨ newer x y = y := by
  unfold newer; split_ifs <;> simp

lemma newer_none_right (x : Option (Entry V)) : newer x none = x := by
  simp [newer, key]

lemma key_eq_zero {x : Option (Entry V)} : key x = 0 ↔ x = none := by
  rcases x with _ | ⟨m, v⟩ <;> simp [key]

lemma exists_of_key_pos {x : Option (Entry V)} (h : 0 < key x) : ∃ m v, x = some (m, v) ∧ key x = m + 1 := by
  rcases x with _ | ⟨m, v⟩
  · simp [key] at h
  · exact ⟨m, v, rfl, rfl⟩

/-! ## Invariant components -/

/-- Every entry of the view comes from a store operation invoked in the history. -/
def Valid (h : History ι V) (W : View ι V) : Prop :=
  ∀ j m v, W j = some (m, v) → Label.inv j m (.store v) ∈ h

/-- Views present in the system: local views, queued messages, pending `currentView`s. -/
def SysView (c : Config ι V) (W : View ι V) : Prop :=
  ∃ k, W = c.view k ∨ W ∈ c.queue k ∨ (c.phase k).cv? = some W

/-- Node `k` knows an entry of node `j` with key at least `s` (in its view or in its queue). -/
def Knows (c : Config ι V) (k j : ι) (s : ℕ) : Prop :=
  s ≤ key (c.view k j) ∨ ∃ W ∈ c.queue k, s ≤ key (W j)

/-- Facts about the collect `(i, n)` with view `W` that refer to the history before its
invocation. -/
def PastOK (h : History ι V) (i : ι) (n : ℕ) (W : View ι V) : Prop :=
  ∃ q₀ : ℕ, h[q₀]? = some (Label.inv i n .collect) ∧
    (∀ (p p' : ℕ) j m r v, p' < p → p < q₀ → h[p']? = some (Label.inv j m (.store v)) →
      h[p]? = some (Label.ret j m r) → m + 1 ≤ key (W j)) ∧
    (∀ (p : ℕ) i' n' W', p < q₀ → h[p]? = some (Label.ret i' n' (.view W')) → ∀ j, key (W' j) ≤ key (W j))

lemma PastOK.append {h : History ι V} {i n W} (hp : PastOK h i n W) (t : History ι V) :
    PastOK (h ++ t) i n W := by
  obtain ⟨q₀, hq₀, h1, h2⟩ := hp
  have hl := lt_length_of_getElem?_eq_some hq₀
  refine ⟨q₀, getElem?_append_of_eq_some hq₀, ?_, ?_⟩
  · intro p p' j m r v hpp hp hi hr
    rw [getElem?_append_of_lt (by omega)] at hi hr
    exact h1 p p' j m r v hpp hp hi hr
  · intro p i' n' W' hp hr
    rw [getElem?_append_of_lt (by omega)] at hr
    exact h2 p i' n' W' hp hr

/-- Invariant of the history, depending on the configuration only through the operation counters
and the pending operations. -/
structure HInv (cnt : ι → ℕ) (op : ι → Option (Op V)) (h : History ι V) : Prop where
  inv_idx : ∀ (p : ℕ) i m o, h[p]? = some (Label.inv i m o) → m < cnt i ∨ (m = cnt i ∧ op i = some o)
  ret_idx : ∀ (p : ℕ) i m r, h[p]? = some (Label.ret i m r) → m < cnt i
  cur_inv : ∀ i o, op i = some o → Label.inv i (cnt i) o ∈ h
  done_ret : ∀ i m, m < cnt i → ∃ r, Label.ret i m r ∈ h
  ret_before_inv : ∀ (q : ℕ) i m m' o, h[q]? = some (Label.inv i m' o) → m < m' →
    ∃ (p : ℕ) (r : Resp ι V), p < q ∧ h[p]? = some (Label.ret i m r)
  inv_before_ret : ∀ (q : ℕ) i m r, h[q]? = some (Label.ret i m r) → ∃ (p : ℕ) (o : Op V), p < q ∧ h[p]? = some (Label.inv i m o)
  inv_unique : ∀ (p q : ℕ) i m o o', h[p]? = some (Label.inv i m o) → h[q]? = some (Label.inv i m o') → p = q
  ret_mono : ∀ (p q : ℕ) i a b r r', p < q → h[p]? = some (Label.ret i a r) → h[q]? = some (Label.ret i b r') →
    a < b
  valid_ret : ∀ i n W, Label.ret i n (.view W) ∈ h → Valid h W
  done_inv : ∀ (q : ℕ) i n W, h[q]? = some (Label.ret i n (.view W)) → ∀ j m v, W j = some (m, v) →
    ∃ p : ℕ, p < q ∧ h[p]? = some (Label.inv j m (.store v))
  done : ∀ i n W, Label.ret i n (.view W) ∈ h → PastOK h i n W

/-- The inductive invariant of MAC-SC with handler priority. -/
structure Inv (c : Config ι V) (h : History ι V) : Prop where
  hinv : HInv c.cnt (fun i => (c.phase i).op?) h
  valid_sys : ∀ W, SysView c W → Valid h W
  key_le : ∀ i, (c.phase i).cv? = none → ∀ W, SysView c W → key (W i) ≤ c.cnt i
  store_cv : ∀ i v cv, (c.phase i).op? = some (.store v) → (c.phase i).cv? = some cv →
    cv i = some (c.cnt i, v)
  knows_bcast : ∀ i o cv got, c.phase i = .bcast o cv got → ∀ k ∈ got, k ∉ c.crashed →
    ∀ j, Knows c k j (key (cv j))
  knows_acked : ∀ i o cv, c.phase i = .acked o cv → ∀ k, k ∉ c.crashed →
    ∀ j, Knows c k j (key (cv j))
  knows_store : ∀ (p p' : ℕ) j m r v, h[p']? = some (Label.inv j m (.store v)) → h[p]? = some (Label.ret j m r) →
    ∀ k, k ∉ c.crashed → Knows c k j (m + 1)
  knows_collect : ∀ i n W, Label.ret i n (.view W) ∈ h → ∀ k, k ∉ c.crashed →
    ∀ j, Knows c k j (key (W j))
  pend : ∀ i cv, (c.phase i).op? = some .collect → (c.phase i).cv? = some cv →
    PastOK h i (c.cnt i) cv

end Podc.AnonymousMACConsensus
