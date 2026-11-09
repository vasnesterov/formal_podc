import Papers.PODC2017.DelayedTimestamps.Routing

/-!
# Lower bounds on the length of online vector timestamps (Lemmas 1–4)

Vaidya, Kulkarni, *Efficient Timestamps for Capturing Causality* (arXiv:1606.05962v1), the full
version of Kulkarni–Vaidya, *Effectiveness of Delaying Timestamp Computation* (PODC 2017).

An online algorithm (`IsOnlineTimestamping G A`) assigns to each event, when it occurs, a vector
`Fin s → α` (componentwise partial order `<` of Section 3), distinct for distinct events, with
`e → f ↔ τ(e) < τ(f)` on every execution over the communication graph `G`. The algorithm may
use the whole prefix of the execution (global knowledge), so the bounds hold a fortiori for
distributed algorithms.

* `card_le_of_online` (general form of Lemmas 1, 3, 4, any linear order `α`): if for every
  `k ∈ X` all other processes of `X` can reach a common process `r ≠ k` without passing through
  `k`, then `s ≥ |X|`.
* `card_lt_of_online_int` (general form of Lemma 2, integer entries): if moreover all of them
  reach the same `c ∉ X`, then `s ≥ |X| + 1`.
* Corollaries: `lemma_1` (star graph: `s ≥ n − 1`), `lemma_2` (star graph, integers: `s ≥ n`),
  `lemma_3` (vertex connectivity `≥ 2`: `s ≥ n`), `lemma_4` (non-cut vertices `X`: `s ≥ |X|`),
  `two_le_of_ne` (two processes: `s ≥ 2`).

The proof follows the paper: each process of `X` takes one step first; their timestamps are
fixed before the adversary chooses whose information is delayed. For each `k`, the execution
gathers the information of `X \ {k}` at `r` (`gather`), and the final event `e` of `r` satisfies
`τ(x) ≤ τ(e)` for all `x ∈ X \ {k}` but not `τ(a_k) < τ(e)`; so some coordinate of `τ(a_k)` is a
strict maximum (`exists_coord_gt`), and different `k` give different coordinates.
-/

namespace Podc.DelayedTimestamps

set_option linter.unusedSectionVars false

open Cslib.Causality

/-! ### Order-theoretic core -/

/-- If every vector of `S` is below `y` but `x` is neither below nor equal to `y`, then some
coordinate of `x` strictly exceeds that coordinate of every vector of `S`. -/
lemma exists_coord_gt {ι α : Type*} [LinearOrder α] {S : Set (ι → α)} {x y : ι → α}
    (hS : ∀ v ∈ S, v ≤ y) (hlt : ¬ x < y) (hne : x ≠ y) : ∃ l, ∀ v ∈ S, v l < x l := by
  by_contra h
  push Not at h
  apply hlt
  refine lt_of_le_of_ne (fun l => ?_) hne
  obtain ⟨v, hv, hvl⟩ := h l
  exact hvl.trans (hS v hv l)

variable {P : Type*} [DecidableEq P]

/-! ### Walks avoiding a vertex -/

lemma exists_walks {G : SimpleGraph P} {K : Set P} {r : P} (T : List P)
    (hT : ∀ j ∈ T, G.ReachableAvoiding K j r) :
    ∃ ws : List (Σ j : P, G.Walk j r), (∀ w ∈ ws, w.1 ∈ T ∧ ∀ x ∈ w.2.support, x ∉ K) ∧
      ∀ j ∈ T, ∃ w ∈ ws, w.1 = j := by
  induction T with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons j T ih =>
    obtain ⟨ws, h1, h2⟩ := ih (fun j' hj' => hT j' (List.mem_cons_of_mem _ hj'))
    obtain ⟨p, hp⟩ := hT j List.mem_cons_self
    refine ⟨⟨j, p⟩ :: ws, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨List.mem_cons_self, hp⟩
      · exact ⟨List.mem_cons_of_mem _ (h1 w hw).1, (h1 w hw).2⟩
    · intro j' hj'
      rcases List.mem_cons.1 hj' with rfl | hj'
      · exact ⟨_, List.mem_cons_self, rfl⟩
      · obtain ⟨w, hw, hw'⟩ := h2 j' hj'
        exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩

/-! ### The adversary -/

variable {V : Type*} [Preorder V]

lemma onlineTs_append (A : Exec P → V) (pre rest : Exec P) {i : ℕ} (hi : i < pre.length) :
    onlineTs A (pre ++ rest) i = A (pre.take (i + 1)) := by
  unfold onlineTs
  rw [List.take_append_of_le_length (by omega)]

/-- The core adversary argument. `pre` is an execution in which `k` takes its last step at
`pk` (a local step); the walks `ws` end at `r ≠ k` and avoid `k`. Extending `pre` by gathering
the information of the starts of the walks at `r`, followed by a step `e` of `r`, yields a
timestamp `y = τ(e)` above the timestamps of those starts and of all events of `r` in `pre`, but
not above `τ(pk)`. -/
theorem adversary {G : SimpleGraph P} {A : Exec P → V} (hA : IsOnlineTimestamping G A)
    {pre : Exec P} (hwf : pre.WF) (hG : pre.OnGraph G) {k r : P} (hrk : r ≠ k) {pk : ℕ}
    (hpk : pre[pk]? = some (.comp k)) (hlast : ∀ i, pk < i → pre.procAt i ≠ some k)
    (ws : List (Σ j : P, G.Walk j r)) (hws : ∀ w ∈ ws, k ∉ w.2.support) (pos : P → ℕ)
    (hpos : ∀ w ∈ ws, pos w.1 < pre.length ∧ pre.procAt (pos w.1) = some w.1) :
    ∃ y : V, (∀ w ∈ ws, A (pre.take (pos w.1 + 1)) ≤ y) ∧
      (∀ i, i < pre.length → pre.procAt i = some r → A (pre.take (i + 1)) ≤ y) ∧
      ¬ A (pre.take (pk + 1)) < y ∧ A (pre.take (pk + 1)) ≠ y := by
  obtain ⟨hwf', hG', ⟨rest, hrest⟩, hhb, hlastev, hnew⟩ := gather hwf hG ws pos hpos
  set ex := routeAll pre ws ++ [Act.comp r] with hex
  set e := (routeAll pre ws).length
  have hpkl : pk < pre.length := (List.getElem?_eq_some_iff.1 hpk).1
  have hel : e < ex.length := by simp [ex, e]
  have hpre_e : pre.length ≤ e := by
    obtain ⟨rest', h'⟩ := routeAll_prefix pre ws
    simp [e, h']
  have hτ : ∀ i, i < pre.length → onlineTs A ex i = A (pre.take (i + 1)) := by
    intro i hi
    rw [hrest]
    exact onlineTs_append A pre rest hi
  have hcap := hA ex hwf' hG'
  refine ⟨onlineTs A ex e, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have h := hhb w hw
    rw [← hτ _ (hpos w hw).1]
    exact ((hcap _ _ (h.lt hwf' |>.trans hel) hel).1.1 h).le
  · intro i hi hir
    have h : ex.HB i e := by
      refine Exec.hb_of_lt (p := r) (by omega) ?_ (Exec.procAt_of_get hlastev)
      rw [hrest, Exec.procAt_append_of_lt _ hi]
      exact hir
    rw [← hτ _ hi]
    exact ((hcap _ _ (by omega) hel).1.1 h).le
  · rw [← hτ _ hpkl]
    intro h
    refine not_hb_of_last hwf' (k := k) ?_ ?_ e ((hcap _ _ (by omega) hel).1.2 h)
    · rw [hrest, Exec.getElem?_append_of_lt _ hpkl]; exact hpk
    · intro i hi hik
      by_cases hil : i < pre.length
      · rw [hrest, Exec.procAt_append_of_lt _ hil] at hik
        exact hlast i hi hik
      · rcases hnew i k (by omega) hik with h | ⟨w, hw, hk⟩
        · exact hrk h.symm
        · exact hws w hw hk
  · rw [← hτ _ hpkl]
    exact (hcap _ _ (by omega) hel).2 (by omega)

/-! ### The initial events -/

/-- Every process of `X` takes one local step, in the order of `X.toList`. -/
noncomputable def initExec (X : Finset P) : Exec P := X.toList.map Act.comp

/-- The position of the initial step of `j`. -/
noncomputable def initPos (X : Finset P) (j : P) : ℕ := X.toList.idxOf j

lemma initExec_get (X : Finset P) (i : ℕ) : (initExec X)[i]? = X.toList[i]?.map Act.comp := by
  simp [initExec]

lemma initExec_wf (X : Finset P) : (initExec X).WF := by
  constructor
  · intro j p m h; rw [initExec_get] at h; simp at h
  · intro j p m h; rw [initExec_get] at h; simp at h
  · intro j j' p p' m h; rw [initExec_get] at h; simp at h

lemma initExec_onGraph (X : Finset P) (G : SimpleGraph P) : (initExec X).OnGraph G := by
  intro j p q h; rw [initExec_get] at h; simp at h

lemma initExec_pos {X : Finset P} {j : P} (hj : j ∈ X) :
    initPos X j < (initExec X).length ∧ (initExec X)[initPos X j]? = some (.comp j) := by
  have hm : j ∈ X.toList := Finset.mem_toList.2 hj
  refine ⟨by simpa [initExec, initPos] using List.idxOf_lt_length_of_mem hm, ?_⟩
  rw [initExec_get, initPos, List.getElem?_idxOf hm]
  rfl

lemma initExec_procAt {X : Finset P} {i : ℕ} {j : P} (h : (initExec X).procAt i = some j) :
    j ∈ X ∧ i = initPos X j := by
  obtain ⟨a, ha, rfl⟩ := Exec.procAt_eq_some.1 h
  rw [initExec_get] at ha
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ha
  obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.1 hx
  refine ⟨Finset.mem_toList.1 (hxi ▸ List.getElem_mem hi), ?_⟩
  simp only [Act.proc_comp, initPos, ← hxi]
  exact ((Finset.nodup_toList X).idxOf_getElem i hi).symm

/-! ### Lemmas 1, 3, 4 (real-valued, or any linearly ordered, entries) -/

/-- General form of Lemmas 1, 3 and 4: if for every `k ∈ X` the other processes of `X` can all
reach some process `r ≠ k` along walks avoiding `k`, then every online vector timestamping
algorithm uses vectors of length at least `|X|`. -/
theorem card_le_of_online {α : Type*} [LinearOrder α] {s : ℕ} (G : SimpleGraph P) (X : Finset P)
    (hX : ∀ k ∈ X, ∃ r, r ≠ k ∧ ∀ j ∈ X, j ≠ k → G.ReachableAvoiding {k} j r)
    (A : Exec P → (Fin s → α)) (hA : IsOnlineTimestamping G A) : X.card ≤ s := by
  set pre := initExec X
  let a : P → Fin s → α := fun j => A (pre.take (initPos X j + 1))
  have key : ∀ k ∈ X, ∃ l : Fin s, ∀ j ∈ X, j ≠ k → a j l < a k l := by
    intro k hk
    obtain ⟨r, hrk, hreach⟩ := hX k hk
    obtain ⟨ws, hws1, hws2⟩ := exists_walks (G := G) (K := {k}) (r := r) (X.erase k).toList
      (fun j hj => by
        rw [Finset.mem_toList, Finset.mem_erase] at hj
        exact hreach j hj.2 hj.1)
    obtain ⟨y, hy1, -, hy3, hy4⟩ := adversary hA (initExec_wf X) (initExec_onGraph X G) hrk
      (initExec_pos hk).2 (fun i hi hik => by
        have := (initExec_procAt hik).2; omega)
      ws (fun w hw hk' => (hws1 w hw).2 k hk' rfl) (initPos X) (fun w hw => by
        have hw1 : w.1 ∈ X := (Finset.mem_erase.1 (Finset.mem_toList.1 (hws1 w hw).1)).2
        exact ⟨(initExec_pos hw1).1, Exec.procAt_of_get (initExec_pos hw1).2⟩)
    obtain ⟨l, hl⟩ := exists_coord_gt (S := {v | ∃ j ∈ X, j ≠ k ∧ v = a j}) (x := a k) (y := y)
      (by
        rintro v ⟨j, hj, hjk, rfl⟩
        obtain ⟨w, hw, rfl⟩ := hws2 j (Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hjk, hj⟩))
        exact hy1 w hw) hy3 hy4
    exact ⟨l, fun j hj hjk => hl _ ⟨j, hj, hjk, rfl⟩⟩
  rcases X.eq_empty_or_nonempty with rfl | ⟨k0, hk0⟩
  · simp
  have : Nonempty (Fin s) := ⟨(key k0 hk0).choose⟩
  choose! f hf using key
  calc X.card ≤ (Finset.univ : Finset (Fin s)).card := by
        refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
        intro k hk k' hk' hkk
        by_contra hne
        have h1 := hf k hk k' hk' (Ne.symm hne)
        have h2 := hf k' hk' k hk hne
        rw [hkk] at h1
        exact lt_asymm h1 h2
    _ = s := by simp

/-! ### Lemma 2 (integer entries) -/

/-- An execution without messages is well formed and uses no channel. -/
lemma wf_of_comp {ex : Exec P} (h : ∀ a ∈ ex, ∃ p, a = .comp p) :
    ex.WF ∧ ∀ G : SimpleGraph P, ex.OnGraph G := by
  have key : ∀ {j : ℕ} {a : Act P}, ex[j]? = some a → ∃ p, a = .comp p :=
    fun hj => h _ (List.mem_of_getElem? hj)
  refine ⟨⟨fun hj => ?_, fun hj => ?_, fun hj _ => ?_⟩, fun G j p q hj => ?_⟩ <;>
    (obtain ⟨_, h'⟩ := key hj; cases h')

/-- General form of Lemma 2: with integer entries, if moreover all processes of `X` can reach a
common process `c ∉ X` along walks avoiding any one `k ∈ X`, then vectors have length at least
`|X| + 1`. -/
theorem card_lt_of_online_int {s : ℕ} (G : SimpleGraph P) (X : Finset P) (c : P) (hc : c ∉ X)
    (hX : ∀ k ∈ X, ∀ j ∈ X, j ≠ k → G.ReachableAvoiding {k} j c)
    (A : Exec P → (Fin s → ℤ)) (hA : IsOnlineTimestamping G A) : X.card + 1 ≤ s := by
  set pre0 := initExec X
  let a : P → Fin s → ℤ := fun j => A (pre0.take (initPos X j + 1))
  -- the chain of local steps of `c` after the initial steps
  let chain : ℕ → Exec P := fun N => pre0 ++ List.replicate N (Act.comp c)
  have hchain : ∀ N, (chain N).WF ∧ ∀ G : SimpleGraph P, (chain N).OnGraph G := by
    intro N
    apply wf_of_comp
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨p, rfl⟩
    · exact ⟨c, List.eq_of_mem_replicate hx⟩
  have hchain_get : ∀ N i, i < N → (chain N)[pre0.length + i]? = some (Act.comp c) := by
    intro N i hi
    simp [chain, hi]
  let t : ℕ → Fin s → ℤ := fun i => A (pre0 ++ List.replicate (i + 1) (Act.comp c))
  have ht : ∀ N i, i < N → onlineTs A (chain N) (pre0.length + i) = t i := by
    intro N i hi
    simp only [onlineTs, chain, t, add_assoc, List.take_append, List.take_replicate]
    rw [List.take_of_length_le (by omega), Nat.add_sub_cancel_left, min_eq_left (by omega)]
  have hmono : ∀ i, t i < t (i + 1) := by
    intro i
    have hcap := hA (chain (i + 2)) (hchain _).1 ((hchain _).2 G)
    have hl : (chain (i + 2)).length = pre0.length + (i + 2) := by simp [chain]
    have h := (hcap (pre0.length + i) (pre0.length + (i + 1)) (by omega) (by omega)).1.1
      (Exec.hb_of_lt (by omega) (Exec.procAt_of_get (hchain_get _ i (by omega)))
        (Exec.procAt_of_get (hchain_get _ (i + 1) (by omega))))
    rwa [ht _ _ (by omega), ht _ _ (by omega)] at h
  have hsum : ∀ i : ℕ, ∑ l, t 0 l + i ≤ ∑ l, t i l := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h := Pi.lt_def.1 (hmono i)
      have : ∑ l, t i l < ∑ l, t (i + 1) l :=
        Finset.sum_lt_sum (fun l _ => h.1 l) (let ⟨l, hl⟩ := h.2; ⟨l, Finset.mem_univ _, hl⟩)
      push_cast
      omega
  let M : ℤ := ∑ j ∈ X, ∑ l, |a j l|
  have haM : ∀ j ∈ X, ∀ l, a j l ≤ M := by
    intro j hj l
    calc a j l ≤ |a j l| := le_abs_self _
      _ ≤ ∑ l, |a j l| := Finset.single_le_sum (f := fun l => |a j l|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
      _ ≤ M := Finset.single_le_sum (f := fun j => ∑ l, |a j l|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hj
  set N := (s * M - ∑ l, t 0 l).toNat + 1
  obtain ⟨l0, hl0⟩ : ∃ l0, M < t N l0 := by
    by_contra hcon
    push Not at hcon
    have h1 : ∑ l, t N l ≤ ∑ _l : Fin s, M := Finset.sum_le_sum fun l _ => hcon l
    have h2 := hsum N
    have h3 := Int.self_le_toNat (s * M - ∑ l, t 0 l)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have : ((N : ℕ) : ℤ) = ((s * M - ∑ l, t 0 l).toNat : ℤ) + 1 := by simp [N]
    linarith
  have : Nonempty (Fin s) := ⟨l0⟩
  set pre := chain (N + 1)
  have hpre_take : ∀ i, i < pre0.length → pre.take (i + 1) = pre0.take (i + 1) := by
    intro i hi
    simp only [pre, chain]
    rw [List.take_append_of_le_length (by omega)]
  have key : ∀ k ∈ X, ∃ l : Fin s, (∀ j ∈ X, j ≠ k → a j l < a k l) ∧ t N l < a k l := by
    intro k hk
    have hck : c ≠ k := fun h => hc (h ▸ hk)
    obtain ⟨ws, hws1, hws2⟩ := exists_walks (G := G) (K := {k}) (r := c) (X.erase k).toList
      (fun j hj => by
        rw [Finset.mem_toList, Finset.mem_erase] at hj
        exact hX k hk j hj.2 hj.1)
    have hposX : ∀ j ∈ X, initPos X j < pre.length ∧ pre[initPos X j]? = some (Act.comp j) := by
      intro j hj
      obtain ⟨h1, h2⟩ := initExec_pos hj
      exact ⟨lt_of_lt_of_le h1 (by simp [pre, chain, pre0]), by
        simp only [pre, chain]; rw [Exec.getElem?_append_of_lt _ h1]; exact h2⟩
    obtain ⟨y, hy1, hy2, hy3, hy4⟩ := adversary hA (hchain _).1 ((hchain _).2 G) hck
      (hposX k hk).2
      (fun i hi hik => by
        by_cases hil : i < pre0.length
        · rw [Exec.procAt_append_of_lt _ hil] at hik
          have := (initExec_procAt hik).2; omega
        · obtain ⟨b, hb, hbk⟩ := Exec.procAt_eq_some.1 hik
          simp only [chain] at hb
          rw [List.getElem?_append_right (by omega)] at hb
          rw [List.getElem?_replicate] at hb
          split_ifs at hb
          cases hb
          exact hck hbk)
      ws (fun w hw hk' => (hws1 w hw).2 k hk' rfl) (initPos X) (fun w hw => by
        have hw1 : w.1 ∈ X := (Finset.mem_erase.1 (Finset.mem_toList.1 (hws1 w hw).1)).2
        exact ⟨(hposX _ hw1).1, Exec.procAt_of_get (hposX _ hw1).2⟩)
    have hpk := (initExec_pos hk).1
    rw [hpre_take _ hpk] at hy3 hy4
    have htN : t N ≤ y := by
      have h := hy2 (pre0.length + N) (by simp [chain])
        (Exec.procAt_of_get (hchain_get _ N (by omega)))
      have e : onlineTs A pre (pre0.length + N) = t N := ht _ _ (by omega)
      unfold onlineTs at e
      rwa [e] at h
    obtain ⟨l, hl⟩ := exists_coord_gt (S := {v | (∃ j ∈ X, j ≠ k ∧ v = a j) ∨ v = t N})
      (x := a k) (y := y)
      (by
        rintro v (⟨j, hj, hjk, rfl⟩ | rfl)
        · obtain ⟨w, hw, rfl⟩ := hws2 j (Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hjk, hj⟩))
          have h := hy1 w hw
          rwa [hpre_take _ (initExec_pos hj).1] at h
        · exact htN) hy3 hy4
    exact ⟨l, fun j hj hjk => hl _ (Or.inl ⟨j, hj, hjk, rfl⟩), hl _ (Or.inr rfl)⟩
  choose! f hf using key
  have hcard : X.card ≤ (Finset.univ.erase l0).card := by
    refine Finset.card_le_card_of_injOn f (fun k hk => ?_) ?_
    · refine Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩)
      have h1 := (hf k hk).2
      rw [h] at h1
      have h2 := haM k hk l0
      linarith
    · intro k hk k' hk' hkk
      by_contra hne
      have h1 := (hf k hk).1 k' hk' (Ne.symm hne)
      have h2 := (hf k' hk').1 k hk hne
      rw [hkk] at h1
      exact lt_asymm h1 h2
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcard
  have : 0 < s := Fin.pos l0
  omega

/-! ### The paper's statements -/

/-- The star graph on the processes `p_0, …, p_m` (`n = m + 1`) with central process `p_0`. -/
def star (m : ℕ) : SimpleGraph (Fin (m + 1)) := SimpleGraph.fromRel fun i _ => i = 0

lemma star_adj {m : ℕ} {i j : Fin (m + 1)} : (star m).Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0) := by
  simp [star]

lemma star_reach {m : ℕ} {k j : Fin (m + 1)} (hk : k ≠ 0) (hj : j ≠ 0) (hjk : j ≠ k) :
    (star m).ReachableAvoiding {k} j 0 :=
  ⟨.cons (star_adj.2 ⟨hj, Or.inr rfl⟩) .nil, by
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨hjk, Ne.symm hk⟩⟩

lemma card_radial (m : ℕ) : (Finset.univ.filter fun i : Fin (m + 1) => i ≠ 0).card = m := by
  rw [Finset.filter_ne' Finset.univ 0, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

/-- **Lemma 1** of [Vaidya–Kulkarni]: an online algorithm assigning distinct real-valued (more
generally: values in any linear order) vector timestamps that capture causality on the star graph
with `n = m + 1` processes uses vectors of length at least `n − 1 = m`. -/
theorem lemma_1 {α : Type*} [LinearOrder α] (m s : ℕ) (A : Exec (Fin (m + 1)) → (Fin s → α))
    (hA : IsOnlineTimestamping (star m) A) : m ≤ s := by
  have h := card_le_of_online (star m) (Finset.univ.filter fun i => i ≠ 0)
    (fun k hk => ⟨0, (Finset.mem_filter.1 hk).2.symm, fun j hj hjk =>
      star_reach (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hj).2 hjk⟩) A hA
  rwa [card_radial] at h

/-- **Lemma 2** of [Vaidya–Kulkarni]: with integer entries, vectors on the star graph with
`n = m + 1` processes have length at least `n`. -/
theorem lemma_2 (m s : ℕ) (A : Exec (Fin (m + 1)) → (Fin s → ℤ))
    (hA : IsOnlineTimestamping (star m) A) : m + 1 ≤ s := by
  have h := card_lt_of_online_int (star m) (Finset.univ.filter fun i => i ≠ 0) 0
    (by simp) (fun k hk j hj hjk =>
      star_reach (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hj).2 hjk) A hA
  rwa [card_radial] at h

/-- **Lemma 3** of [Vaidya–Kulkarni]: if the communication graph has vertex connectivity at
least `2`, online vector timestamps have length at least `n`. -/
theorem lemma_3 [Fintype P] {α : Type*} [LinearOrder α] {s : ℕ} (G : SimpleGraph P)
    (hG : G.IsVertexConnected 2) (A : Exec P → (Fin s → α)) (hA : IsOnlineTimestamping G A) :
    Fintype.card P ≤ s := by
  have h := card_le_of_online G Finset.univ (fun k _ => by
    obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card (by have := hG.1; omega) k
    refine ⟨r, hr, fun j _ hjk => ?_⟩
    have := hG.2 {k} (by simp) j r (by simpa using hjk) (by simpa using hr)
    simpa using this) A hA
  simpa using h

open Classical in
/-- The non-cut vertices of `G`: removing `k` leaves the other vertices connected. -/
noncomputable def nonCut [Fintype P] (G : SimpleGraph P) : Finset P :=
  Finset.univ.filter fun k => ∀ u v, u ≠ k → v ≠ k → G.ReachableAvoiding {k} u v

/-- **Lemma 4** of [Vaidya–Kulkarni]: for a connected graph (the paper assumes vertex
connectivity exactly `1`), online vector timestamps have length at least `|X|`, where `X` is the
set of processes that are not cut vertices. -/
theorem lemma_4 [Fintype P] {α : Type*} [LinearOrder α] {s : ℕ} (G : SimpleGraph P)
    (hG : G.IsVertexConnected 1) (A : Exec P → (Fin s → α)) (hA : IsOnlineTimestamping G A) :
    (nonCut G).card ≤ s :=
  card_le_of_online G (nonCut G) (fun k hk => by
    obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card hG.1 k
    have hk' : ∀ u v, u ≠ k → v ≠ k → G.ReachableAvoiding {k} u v := by simpa [nonCut] using hk
    exact ⟨r, hr, fun j _ hjk => hk' j r hjk hr⟩) A hA

/-- Two processes force vectors of length at least `2` (for `n = 2` the bound of Lemma 1 is not
tight: Appendix B.2, first paragraph). -/
theorem two_le_of_ne {α : Type*} [LinearOrder α] {s : ℕ} (G : SimpleGraph P) {u v : P}
    (huv : u ≠ v) (A : Exec P → (Fin s → α)) (hA : IsOnlineTimestamping G A) : 2 ≤ s := by
  set ex : Exec P := [.comp u, .comp v]
  obtain ⟨hwf, hG⟩ := wf_of_comp (ex := ex) (by simp [ex])
  have hcap := hA ex hwf (hG G)
  have h01 : ¬ ex.HB 0 1 := not_hb_of_last hwf (k := u) rfl (fun i hi h => by
    obtain ⟨a, ha, rfl⟩ := Exec.procAt_eq_some.1 h
    match i, hi, ha with
    | 1, _, ha => cases ha; exact huv.symm rfl) 1
  have h10 : ¬ ex.HB 1 0 := fun h => absurd (h.lt hwf) (by omega)
  have hne := (hcap 0 1 (by simp [ex]) (by simp [ex])).2 (by omega)
  have hlt01 := (hcap 0 1 (by simp [ex]) (by simp [ex])).1
  have hlt10 := (hcap 1 0 (by simp [ex]) (by simp [ex])).1
  by_contra hs
  set x := onlineTs A ex 0
  set y := onlineTs A ex 1
  interval_cases s
  · exact hne (Subsingleton.elim _ _)
  · have hne0 : x 0 ≠ y 0 := fun h => hne (funext fun i => by fin_cases i; exact h)
    rcases lt_or_gt_of_ne hne0 with h | h
    · exact h01 (hlt01.2 (Pi.lt_def.2 ⟨fun i => by fin_cases i; exact h.le, 0, h⟩))
    · exact h10 (hlt10.2 (Pi.lt_def.2 ⟨fun i => by fin_cases i; exact h.le, 0, h⟩))

end Podc.DelayedTimestamps
