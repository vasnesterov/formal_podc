import Papers.PODC2020.DetectableSpace.Lin
import Papers.PODC2020.DetectableSpace.Perturbing
import Mathlib.Data.Set.Card

/-!
# Theorem 1: a space lower bound for detectable CAS

*Ben-Baruch, Hendler, Rusanovsky, Upper and Lower Bounds on the Space Complexity of Detectable
Objects, PODC 2020, Section 4.2.*

**Statement** (`theorem1`). Let `A` be an obstruction-free implementation of the CAS object
`casRC V v₀` (operations `read` and `cas old new`) for `N = Fintype.card P` processes, which is
durably linearizable and detectable (`DurLinDet`), where `V` has at least `N` values. Then the
set of shared-memory states of reachable configurations has at least `2 ^ (N - 1)` elements,
i.e. `A` has `2 ^ (N - 1)` reachable configurations no two of which are memory-equivalent.
Only the *shared* non-volatile memory is counted (private NVM and local states are not), which
is what the paper claims. `theorem1_bits`: any encoding of the reachable shared-memory states
into `b` bits that is injective satisfies `N - 1 ≤ b`.

**Proof.** The paper argues by induction on `N`, applying the induction hypothesis to an
algorithm obtained by "fixing `C_ns` as an initial configuration" and halting `p_N`. We unroll
this induction into an explicit construction (`Gadget`): processes `p 0, …, p (m-1), q`
(`m = N - 1`), values `w 0 = v₀, …, w m`, and at level `i` the operation
`c i = cas (w i) (w (i+1))`. For a branch vector `b`, level `i` (`lvl`) runs: `p i` invokes
`c i` and takes `k` solo steps, then `q` runs `c i` solo to completion. Let `mstar` be the least
`k` after which `q`'s `c i` returns `false` (it exists by obstruction-freedom, and `mstar ≥ 1`);
branch `b i = false` takes `mstar - 1` steps (`q` returns `true`), branch `b i = true` takes
`mstar` steps (`q` returns `false`). The `mstar`-th step of `p i` (the *modifying step* `s`)
changes the shared memory (otherwise `q` could not tell the difference, `qr_eq_of_sh`), so it
is a shared-memory step: `p i` is still running and its private memory is the same in both
branches (`s_step`, `level_pv`). Linearizability facts about the chain of `cas` operations
(`run_ge`, `run_up`, `run_after`, `lin_first`, `lin_second`) determine `q`'s responses. If two
branches first differ at level `j` and end in configurations with the same shared memory, then
after a system-wide crash the recovery of `p j` returns the same value in both (`crash_recover`),
but it must not return `true` in the branch where `q`'s level-`j` operation succeeded
(`lin_final_ns`) and must return `true` in the other one (`lin_final_s`) — a contradiction
(`distinct_aux`). Hence the `2 ^ m` branches give pairwise different shared memories
(`lower_bound`).

Compared with the paper's text: the existence of the modifying step needs that `q`'s `c i` returns
`true` when `p i` has invoked its operation but taken no step; this is shown by transferring
`q`'s solo run from the configuration before `p i`'s invocation (`qr_zero`), since a pending
operation of `p i` could otherwise be linearized before `q`'s. The induction hypothesis of the
paper is applied to a configuration which is not initial (with `p_N` pending and the domain
restricted to `V \ {0}`); the unrolled construction makes this step precise. We found no error
in the theorem or in its proof.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory
open RImpl (solo solo_in)

namespace Thm1

/-- The data of the lower-bound construction: `m + 1` distinct processes `p 0, …, p (m-1), q`
and `m + 1` distinct values `w 0 = v₀, …, w m`. -/
structure Gadget (P V : Type) (v₀ : V) where
  m : ℕ
  q : P
  p : ℕ → P
  w : ℕ → V
  hpq : ∀ i < m, p i ≠ q
  hp : ∀ i j, i < m → j < m → p i = p j → i = j
  hw0 : w 0 = v₀
  hw : ∀ i j, i ≤ m → j ≤ m → w i = w j → i = j

/-- Every operation of level `≥ 1` is preceded by an operation of the previous level. -/
def Pre (L : List (ℕ × RCOp V)) : Prop :=
  ∀ X x Y, L = X ++ x :: Y → 1 ≤ x.1 / 2 → ∃ y ∈ X, y.1 / 2 + 1 = x.1 / 2

variable {P V : Type} [DecidableEq V] {v₀ : V} (G : Gadget P V v₀)

namespace Gadget

/-- The operation of level `k`: `cas (w k) (w (k+1))`. -/
def c (k : ℕ) : RCOp V := .cas (G.w k) (G.w (k + 1))

/-- In `X`, the operation instance `a` is the operation of level `a / 2 < m`. -/
def IsChain (X : List (ℕ × RCOp V)) : Prop := ∀ x ∈ X, x.2 = G.c (x.1 / 2) ∧ x.1 / 2 < G.m

lemma delta_snd {ℓ k : ℕ} (hℓ : ℓ ≤ G.m) (hk : k < G.m) :
    ((casRC V v₀).δ (G.w ℓ) (G.c k)).2 = .inr (decide (ℓ = k)) := by
  have : G.w ℓ = G.w k ↔ ℓ = k := ⟨G.hw ℓ k hℓ hk.le, fun h => h ▸ rfl⟩
  by_cases h : ℓ = k
  · subst h; simp [c]
  · simp [c, h, this]

lemma delta_fst {ℓ k : ℕ} (hℓ : ℓ ≤ G.m) (hk : k < G.m) :
    ((casRC V v₀).δ (G.w ℓ) (G.c k)).1 = if ℓ = k then G.w (k + 1) else G.w ℓ := by
  have : G.w ℓ = G.w k ↔ ℓ = k := ⟨G.hw ℓ k hℓ hk.le, fun h => h ▸ rfl⟩
  by_cases h : ℓ = k
  · subst h; simp [c]
  · simp [c, h, this]

lemma isChain_sub {L X : List (ℕ × RCOp V)} (hL : G.IsChain L) (h : ∀ x ∈ X, x ∈ L) :
    G.IsChain X := fun x hx => hL x (h x hx)

/-- The state only moves up along a chain. -/
lemma run_mono (X : List (ℕ × RCOp V)) (hX : G.IsChain X) : ∀ ℓ, ℓ ≤ G.m →
    ∃ ℓ', ℓ ≤ ℓ' ∧ ℓ' ≤ G.m ∧ (casRC V v₀).runOps (G.w ℓ) (X.map Prod.snd) = G.w ℓ' := by
  induction X with
  | nil => intro ℓ hℓ; exact ⟨ℓ, le_rfl, hℓ, rfl⟩
  | cons x X ih =>
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := hX x (by simp)
    have hX' : G.IsChain X := fun y hy => hX y (by simp [hy])
    rw [List.map_cons, ObjSpec.runOps_cons, h1, G.delta_fst hℓ h2]
    split_ifs with h
    · obtain ⟨ℓ', h3, h4, h5⟩ := ih hX' (x.1 / 2 + 1) (by omega)
      exact ⟨ℓ', by omega, h4, h5⟩
    · exact ih hX' ℓ hℓ

/-- Without operations of level `j`, the state cannot pass `j`. -/
lemma run_up (X : List (ℕ × RCOp V)) (hX : G.IsChain X) {j : ℕ} (hj : j ≤ G.m)
    (hXj : ∀ x ∈ X, x.1 / 2 ≠ j) : ∀ ℓ, ℓ ≤ j →
    ∃ ℓ', ℓ' ≤ j ∧ (casRC V v₀).runOps (G.w ℓ) (X.map Prod.snd) = G.w ℓ' := by
  induction X with
  | nil => intro ℓ hℓ; exact ⟨ℓ, hℓ, rfl⟩
  | cons x X ih =>
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := hX x (by simp)
    have hX' : G.IsChain X := fun y hy => hX y (by simp [hy])
    have hxj := hXj x (by simp)
    rw [List.map_cons, ObjSpec.runOps_cons, h1, G.delta_fst (hℓ.trans hj) h2]
    split_ifs with h
    · exact ih hX' (fun y hy => hXj y (by simp [hy])) (x.1 / 2 + 1) (by omega)
    · exact ih hX' (fun y hy => hXj y (by simp [hy])) ℓ hℓ

/-- Before an operation of level `k`, the state is at least `w k`. -/
lemma run_ge {L : List (ℕ × RCOp V)} (hL : G.IsChain L) (hpre : Pre L) :
    ∀ X x Y, L = X ++ x :: Y → ∃ ℓ, x.1 / 2 ≤ ℓ ∧ ℓ ≤ G.m ∧
      (casRC V v₀).runOps (G.w 0) (X.map Prod.snd) = G.w ℓ := by
  suffices H : ∀ n X x Y, X.length = n → L = X ++ x :: Y → ∃ ℓ, x.1 / 2 ≤ ℓ ∧ ℓ ≤ G.m ∧
      (casRC V v₀).runOps (G.w 0) (X.map Prod.snd) = G.w ℓ by
    intro X x Y h; exact H _ X x Y rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X x Y hn hLX
    have hXc : G.IsChain X := G.isChain_sub hL (fun y hy => by rw [hLX]; simp [hy])
    by_cases h0 : x.1 / 2 = 0
    · obtain ⟨ℓ, -, h2, h3⟩ := G.run_mono X hXc 0 (Nat.zero_le _)
      exact ⟨ℓ, by omega, h2, h3⟩
    · obtain ⟨y, hy, hyx⟩ := hpre X x Y hLX (by omega)
      obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hy
      obtain ⟨ℓ1, h1, h2, h3⟩ := ih X1.length (by simp at hn; omega) X1 y (X2 ++ x :: Y) rfl
        (by rw [hLX]; simp)
      obtain ⟨hy1, hy2⟩ := hXc y (by simp)
      have hX2 : G.IsChain X2 := G.isChain_sub hXc (fun z hz => by simp [hz])
      rw [List.map_append, List.map_cons, ObjSpec.runOps_append, h3,
        ObjSpec.runOps_cons, hy1, G.delta_fst h2 hy2]
      split_ifs with h
      · obtain ⟨ℓ', h4, h5, h6⟩ := G.run_mono X2 hX2 (y.1 / 2 + 1) (by omega)
        exact ⟨ℓ', by omega, h5, h6⟩
      · obtain ⟨ℓ', h4, h5, h6⟩ := G.run_mono X2 hX2 ℓ1 h2
        exact ⟨ℓ', by omega, h5, h6⟩

/-- After an operation of level `k`, the state is at least `w (k+1)`. -/
lemma run_after {L : List (ℕ × RCOp V)} (hL : G.IsChain L) (hpre : Pre L)
    {X Y : List (ℕ × RCOp V)} (hLX : L = X ++ Y) {y : ℕ × RCOp V} (hy : y ∈ X) :
    ∃ ℓ, y.1 / 2 + 1 ≤ ℓ ∧ ℓ ≤ G.m ∧
      (casRC V v₀).runOps (G.w 0) (X.map Prod.snd) = G.w ℓ := by
  obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hy
  obtain ⟨ℓ1, h1, h2, h3⟩ := G.run_ge hL hpre X1 y (X2 ++ Y) (by rw [hLX]; simp)
  have hXc : G.IsChain (X1 ++ y :: X2) := G.isChain_sub hL (fun z hz => by
    rw [hLX]; exact List.mem_append_left _ hz)
  obtain ⟨hy1, hy2⟩ := hXc y (by simp)
  have hX2 : G.IsChain X2 := G.isChain_sub hXc (fun z hz => by simp [hz])
  rw [List.map_append, List.map_cons, ObjSpec.runOps_append, h3,
    ObjSpec.runOps_cons, hy1, G.delta_fst h2 hy2]
  split_ifs with h
  · obtain ⟨ℓ', h4, h5, h6⟩ := G.run_mono X2 hX2 (y.1 / 2 + 1) (by omega)
    exact ⟨ℓ', by omega, h5, h6⟩
  · obtain ⟨ℓ', h4, h5, h6⟩ := G.run_mono X2 hX2 ℓ1 h2
    exact ⟨ℓ', by omega, h5, h6⟩


end Gadget

/-! ### Generic facts about linearizations -/

section Generic

variable {O : ObjSpec} {Q : Type} {h : List (HEv Q O.Op O.Resp)}

/-- An operation that real-time precedes `x` is ordered before `x`. -/
lemma rt_before {L X Y : List (ℕ × O.Op)} {x y : ℕ × O.Op}
    (hrt : L.Pairwise (fun x y => ¬ Prec h y.1 x.1)) (hLX : L = X ++ x :: Y) (hy : y ∈ L)
    (hne : y ≠ x) (hp : Prec h y.1 x.1) : y ∈ X := by
  subst hLX
  rcases List.mem_append.1 hy with hy | hy
  · exact hy
  · rcases List.mem_cons.1 hy with hy | hy
    · exact absurd hy hne
    · exfalso
      have h1 := (List.pairwise_append.1 hrt).2.1
      exact (List.pairwise_cons.1 h1).1 y hy hp

lemma nodup_ne {L X Y : List (ℕ × O.Op)} (hnd : (L.map Prod.fst).Nodup) (hLX : L = X ++ Y)
    {u v : ℕ × O.Op} (hu : u ∈ X) (hv : v ∈ Y) : u.1 ≠ v.1 := by
  subst hLX
  rw [List.map_append] at hnd
  intro heq
  exact List.disjoint_of_nodup_append hnd (List.mem_map_of_mem hu)
    (heq ▸ List.mem_map_of_mem hv)

/-- The sequential response of an element of a legal order. -/
lemma legal_at {σ : O.State} {L X Y : List (ℕ × O.Op)} {x : ℕ × O.Op}
    (hl : Legal O h σ L) (hLX : L = X ++ x :: Y) {r : O.Resp} {c : Bool}
    (hr : HEv.res x.1 (some r) c ∈ h) :
    r = (O.δ (O.runOps σ (X.map Prod.snd)) x.2).2 := by
  subst hLX
  have := Legal.append hl
  obtain ⟨a, o⟩ := x
  exact this.1 r c hr

end Generic

variable [DecidableEq P]

namespace Gadget

/-! ### The histories of the construction -/

/-- History of level `k`: `p k` invokes `c k` (identifier `2k`) and takes some steps, then `q`
runs `c k` (identifier `2k+1`) solo to completion; it returns `true` iff `b k = false`. -/
def blk (b : ℕ → Bool) (k : ℕ) : List (HEv P (RCOp V) (V ⊕ Bool)) :=
  [.inv (2 * k) (G.p k) (G.c k), .inv (2 * k + 1) G.q (G.c k),
    .res (2 * k + 1) (some (.inr (!b k))) false]

/-- History of the first `i` levels. -/
def H (b : ℕ → Bool) : ℕ → List (HEv P (RCOp V) (V ⊕ Bool))
  | 0 => []
  | i + 1 => H b i ++ G.blk b i

lemma mem_H_inv {b : ℕ → Bool} {i a : ℕ} {z : P} {o : RCOp V}
    (h : HEv.inv a z o ∈ G.H b i) : a < 2 * i ∧ o = G.c (a / 2) := by
  induction i with
  | zero => simp [H] at h
  | succ i ih =>
    simp only [H, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨by omega, h2⟩
    · simp only [blk, List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff,
        or_false] at h
      rcases h with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
      · exact ⟨by omega, by congr 1; omega⟩
      · exact ⟨by omega, by congr 1; omega⟩

lemma res_mem_H (b : ℕ → Bool) {k i : ℕ} (hk : k < i) :
    HEv.res (2 * k + 1) (some (.inr (!b k))) false ∈ G.H b i := by
  induction i with
  | zero => omega
  | succ i ih =>
    simp only [H, List.mem_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact .inl (ih hk)
    · exact .inr (by simp [blk])

lemma H_split (b : ℕ → Bool) {k i : ℕ} (h : k ≤ i) : ∃ D, G.H b i = G.H b k ++ D := by
  induction i with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact ⟨[], by simp⟩
  | succ i ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
    · obtain ⟨D, hD⟩ := ih (by omega)
      exact ⟨D ++ G.blk b i, by simp [H, hD]⟩
    · exact ⟨[], by simp⟩

lemma prec_H {b : ℕ → Bool} {k i a : ℕ} {T : List (HEv P (RCOp V) (V ⊕ Bool))} {z : P}
    {o : RCOp V} (hk : k < i) (ha : 2 * k + 2 ≤ a) (h : HEv.inv a z o ∈ G.H b i ++ T) :
    Prec (G.H b i ++ T) (2 * k + 1) a := by
  obtain ⟨D, hD⟩ := G.H_split b (show k + 1 ≤ i by omega)
  rw [hD, List.append_assoc] at h ⊢
  refine ⟨G.H b (k + 1), D ++ T, rfl, ⟨_, false, G.res_mem_H b (Nat.lt_succ_self k)⟩, z, o, ?_⟩
  rcases List.mem_append.1 h with h | h
  · have := (G.mem_H_inv h).1; omega
  · exact h

/-- Linearizations of the histories of the construction are chains in which every operation
is preceded by one of the previous level. -/
lemma lin_chain {b : ℕ → Bool} {i : ℕ} {T : List (HEv P (RCOp V) (V ⊕ Bool))} (hi : i ≤ G.m)
    (hT : ∀ a z o, HEv.inv a z o ∈ T → a / 2 = i ∧ i < G.m ∧ o = G.c i)
    {L : List (ℕ × RCOp V)} (hL : DLin (casRC V v₀) (G.H b i ++ T) v₀ L) :
    G.IsChain L ∧ Pre L := by
  -- levels of invoked operations
  have hlev : ∀ x ∈ L, x.2 = G.c (x.1 / 2) ∧ x.1 / 2 < G.m ∧ x.1 / 2 ≤ i := by
    intro x hx
    obtain ⟨z, hz⟩ := hL.inv_of_mem x hx
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨h1, h2⟩ := G.mem_H_inv hz
      exact ⟨h2, by omega, by omega⟩
    · obtain ⟨h1, h2, h3⟩ := hT _ _ _ hz
      exact ⟨by rw [h3, h1], by omega, by omega⟩
  refine ⟨fun x hx => ⟨(hlev x hx).1, (hlev x hx).2.1⟩, ?_⟩
  intro X x Y hLX h1
  have hx : x ∈ L := by rw [hLX]; simp
  obtain ⟨-, -, hxi⟩ := hlev x hx
  set k := x.1 / 2 with hk
  have hres := G.res_mem_H b (k := k - 1) (i := i) (by omega)
  obtain ⟨y, hy, hyk⟩ := List.mem_map.1
    (hL.mem_of_res _ _ _ (List.mem_append_left T hres))
  refine ⟨y, rt_before hL.rt hLX hy ?_ ?_, by rw [hyk]; omega⟩
  · rintro rfl; omega
  · rw [hyk]
    obtain ⟨z, hz⟩ := hL.inv_of_mem x hx
    exact G.prec_H (by omega) (by omega) hz

/-! ### Consequences of linearizability for the construction -/

/-- (E1) Alone at level `i` (only one operation of level `i` invoked), a `c i` returns `true`. -/
lemma lin_first {b : ℕ → Bool} {i : ℕ} (hi : i < G.m) {z : P} {r : V ⊕ Bool}
    {L : List (ℕ × RCOp V)}
    (hL : DLin (casRC V v₀)
      (G.H b i ++ [.inv (2 * i) z (G.c i), .res (2 * i) (some r) false]) v₀ L) :
    r = .inr true := by
  obtain ⟨hc, hpre⟩ := G.lin_chain hi.le (by
    intro a z' o h
    simp only [List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff, or_false] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨by omega, hi, rfl⟩) hL
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hL.mem_of_res (2 * i) r false (by simp))
  obtain ⟨X, Y, hLX⟩ := List.append_of_mem hx
  have hr := legal_at hL.legal hLX (r := r) (c := false) (by rw [hx1]; simp)
  obtain ⟨hx2, -⟩ := hc x hx
  have hxl : x.1 / 2 = i := by omega
  rw [hx2, hxl] at hr
  obtain ⟨ℓ, h1, h2, h3⟩ := G.run_ge hc hpre X x Y hLX
  rw [G.hw0] at h3
  have hXc : G.IsChain X := G.isChain_sub hc (fun y hy => by rw [hLX]; simp [hy])
  obtain ⟨ℓ', h4, h5⟩ := G.run_up X hXc hi.le (by
    intro y hy
    have hyL : y ∈ L := by rw [hLX]; simp [hy]
    have hne := nodup_ne hL.nodup hLX hy (List.mem_cons_self)
    obtain ⟨z', hz'⟩ := hL.inv_of_mem y hyL
    rcases List.mem_append.1 hz' with hz' | hz'
    · have := (G.mem_H_inv hz').1; omega
    · simp only [List.mem_cons, HEv.inv.injEq, reduceCtorEq, List.mem_nil_iff,
        or_false] at hz'
      omega) 0 (Nat.zero_le _)
  rw [G.hw0] at h5
  have : ℓ = ℓ' := G.hw ℓ ℓ' h2 (by omega) (h3.symm.trans h5)
  rw [h3, G.delta_snd h2 hi] at hr
  rw [hr]; simp; omega

/-- (E2) After an operation of level `i` completed, a `c i` returns `false`. -/
lemma lin_second {b : ℕ → Bool} {i : ℕ} (hi : i < G.m) {z z' : P} {r₀ r : V ⊕ Bool}
    {L : List (ℕ × RCOp V)}
    (hL : DLin (casRC V v₀)
      (G.H b i ++ [.inv (2 * i) z (G.c i), .res (2 * i) (some r₀) false,
        .inv (2 * i + 1) z' (G.c i), .res (2 * i + 1) (some r) false]) v₀ L) :
    r = .inr false := by
  obtain ⟨hc, hpre⟩ := G.lin_chain hi.le (by
    intro a z'' o h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h | h | h <;> cases h <;> exact ⟨by omega, hi, rfl⟩) hL
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hL.mem_of_res (2 * i + 1) r false (by simp))
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 (hL.mem_of_res (2 * i) r₀ false (by simp))
  obtain ⟨X, Y, hLX⟩ := List.append_of_mem hx
  have hyX : y ∈ X := by
    refine rt_before hL.rt hLX hy (by rintro rfl; omega) ?_
    rw [hx1, hy1]
    refine ⟨G.H b i ++ [.inv (2 * i) z (G.c i), .res (2 * i) (some r₀) false],
      [.inv (2 * i + 1) z' (G.c i), .res (2 * i + 1) (some r) false], by simp,
      ⟨some r₀, false, by simp⟩, z', G.c i, by simp⟩
  obtain ⟨ℓ, h1, h2, h3⟩ := G.run_after hc hpre (X := X) (Y := x :: Y) hLX hyX
  rw [G.hw0] at h3
  have hr := legal_at hL.legal hLX (r := r) (c := false) (by rw [hx1]; simp)
  obtain ⟨hx2, -⟩ := hc x hx
  have hxl : x.1 / 2 = i := by omega
  rw [hx2, hxl, h3, G.delta_snd h2 hi] at hr
  rw [hr]; simp; omega

/-- (F-ns) If `q`'s operation of level `j` returned `true`, the operation of `p j` cannot be
linearized with response `true`. -/
lemma lin_final_ns {b : ℕ → Bool} {j : ℕ} (hj : j < G.m) (hbj : b j = false)
    {L : List (ℕ × RCOp V)}
    (hL : DLin (casRC V v₀)
      (G.H b G.m ++ [.crash, .res (2 * j) (some (.inr true)) true]) v₀ L) : False := by
  obtain ⟨hc, hpre⟩ := G.lin_chain le_rfl (by intro a z o h; simp at h) hL
  have hq := G.res_mem_H b hj
  rw [hbj] at hq
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1
    (hL.mem_of_res (2 * j + 1) _ false (List.mem_append_left _ hq))
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 (hL.mem_of_res (2 * j) (.inr true) true (by simp))
  obtain ⟨X, Y, hLX⟩ := List.append_of_mem hx
  obtain ⟨hx2, -⟩ := hc x hx
  obtain ⟨hy2, -⟩ := hc y hy
  have hxl : x.1 / 2 = j := by omega
  have hyl : y.1 / 2 = j := by omega
  have hyx : y ≠ x := by rintro rfl; omega
  rw [hLX] at hy
  rcases List.mem_append.1 hy with hyX | hyY
  · obtain ⟨ℓ, h1, h2, h3⟩ := G.run_after hc hpre (X := X) (Y := x :: Y) hLX hyX
    rw [G.hw0] at h3
    have hr := legal_at hL.legal hLX (r := .inr true) (c := false)
      (by rw [hx1]; exact List.mem_append_left _ hq)
    rw [hx2, hxl, h3, G.delta_snd h2 hj] at hr
    simp at hr; omega
  · rcases List.mem_cons.1 hyY with h | hyY
    · exact hyx h
    obtain ⟨Y1, Y2, rfl⟩ := List.append_of_mem hyY
    have hLX' : L = (X ++ x :: Y1) ++ y :: Y2 := by rw [hLX]; simp
    obtain ⟨ℓ, h1, h2, h3⟩ := G.run_after hc hpre (X := X ++ x :: Y1) (Y := y :: Y2) hLX'
      (y := x) (by simp)
    rw [G.hw0] at h3
    have hr := legal_at hL.legal hLX' (r := .inr true) (c := true) (by rw [hy1]; simp)
    rw [hy2, hyl, h3, G.delta_snd h2 hj] at hr
    simp at hr; omega

/-- (F-s) If `q`'s operation of level `j` returned `false`, the operation of `p j` must be
linearized before it, with response `true`; hence its recovery returns `true`. -/
lemma lin_final_s {b : ℕ → Bool} {j : ℕ} (hj : j < G.m) (hbj : b j = true)
    {x : Option (V ⊕ Bool)} {L : List (ℕ × RCOp V)}
    (hL : DLin (casRC V v₀) (G.H b G.m ++ [.crash, .res (2 * j) x true]) v₀ L) :
    x = some (.inr true) := by
  obtain ⟨hc, hpre⟩ := G.lin_chain le_rfl (by intro a z o h; simp at h) hL
  have hq := G.res_mem_H b hj
  rw [hbj] at hq
  obtain ⟨z, hz, hz1⟩ := List.mem_map.1
    (hL.mem_of_res (2 * j + 1) _ false (List.mem_append_left _ hq))
  obtain ⟨X, Y, hLX⟩ := List.append_of_mem hz
  obtain ⟨hz2, -⟩ := hc z hz
  have hzl : z.1 / 2 = j := by omega
  have hr := legal_at hL.legal hLX (r := .inr false) (c := false)
    (by rw [hz1]; exact List.mem_append_left _ hq)
  obtain ⟨ℓ, h1, h2, h3⟩ := G.run_ge hc hpre X z Y hLX
  rw [G.hw0] at h3
  rw [hz2, hzl, h3, G.delta_snd h2 hj] at hr
  have hℓ : ℓ ≠ j := by intro h; simp [h] at hr
  have hXc : G.IsChain X := G.isChain_sub hc (fun y hy => by rw [hLX]; simp [hy])
  -- the operation `2j` of `p j` precedes `q`'s operation in the linearization
  have hyX : ∃ y ∈ X, y.1 = 2 * j := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    obtain ⟨ℓ', h4, h5⟩ := G.run_up X hXc hj.le (by
      intro y hy
      have := nodup_ne hL.nodup hLX hy (List.mem_cons_self)
      have := hne y hy
      omega) 0 (Nat.zero_le _)
    rw [G.hw0] at h5
    have : ℓ = ℓ' := G.hw ℓ ℓ' h2 (by omega) (h3.symm.trans h5)
    omega
  obtain ⟨y, hy, hy1⟩ := hyX
  have hyL : y ∈ L := by rw [hLX]; simp [hy]
  obtain ⟨X1, X2, rfl⟩ := List.append_of_mem hy
  have hLX' : L = X1 ++ y :: (X2 ++ z :: Y) := by rw [hLX]; simp
  cases x with
  | none =>
    exact absurd (List.mem_map.2 ⟨y, hyL, hy1⟩) (hL.not_mem_of_fail (2 * j) true (by simp))
  | some r =>
    have hr' := legal_at hL.legal hLX' (r := r) (c := true) (by rw [hy1]; simp)
    obtain ⟨hy2, -⟩ := hc y hyL
    have hyl : y.1 / 2 = j := by omega
    obtain ⟨ℓ1, h6, h7, h8⟩ := G.run_ge hc hpre X1 y _ hLX'
    rw [G.hw0] at h8
    have hX1c : G.IsChain X1 := G.isChain_sub hc (fun u hu => by rw [hLX']; simp [hu])
    obtain ⟨ℓ', h4, h5⟩ := G.run_up X1 hX1c hj.le (by
      intro u hu
      have e1 := nodup_ne hL.nodup hLX' hu (List.mem_cons_self)
      have e2 := nodup_ne hL.nodup (X := X1) (Y := y :: (X2 ++ z :: Y)) hLX' hu
        (v := z) (by simp)
      omega) 0 (Nat.zero_le _)
    rw [G.hw0] at h5
    have : ℓ1 = ℓ' := G.hw ℓ1 ℓ' h7 (by omega) (h8.symm.trans h5)
    rw [hy2, hyl, h8, G.delta_snd h7 hj] at hr'
    rw [hr']; simp; omega


end Gadget

/-! ### Generic facts about executions -/

section GenericExec

variable {O : ObjSpec} {Q : Type} [DecidableEq Q] (A : RImpl O Q)

/-- The least `k` with `Pr k` (`0` if there is none). -/
noncomputable def kOf (Pr : ℕ → Prop) : ℕ := by
  classical exact if h : ∃ k, Pr k then Nat.find h else 0

lemma kOf_spec {Pr : ℕ → Prop} (h : ∃ k, Pr k) : Pr (kOf Pr) := by
  classical
  unfold kOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Nat.find_spec h

lemma kOf_min {Pr : ℕ → Prop} (h : ∃ k, Pr k) {k : ℕ} (hk : k < kOf Pr) : ¬ Pr k := by
  classical
  unfold kOf at hk
  rw [dite_eq_left_of_eq_true (eq_true h)] at hk
  exact Nat.find_min h hk

/-- Number of solo steps after which `p` is idle (exists by obstruction-freedom). -/
noncomputable def kIdle (p : Q) (D : A.Cfg) : ℕ :=
  kOf (fun k => (A.exec D (solo p k)).1.ps p = .idle)

lemma kIdle_spec (hof : A.ObstructionFree) {D : A.Cfg} (hD : A.Reachable D) (p : Q) :
    (A.exec D (solo p (kIdle A p D))).1.ps p = .idle :=
  kOf_spec (hof D hD p)

lemma erase_eq_none {Op L : Type} {s : PSt Op L} : s.erase = none ↔ s = .idle := by
  cases s <;> simp [PSt.erase]

variable {A} in
lemma kIdle_agree {p : Q} {D D' : A.Cfg} (h : A.Agree {p} D D') :
    kIdle A p D = kIdle A p D' := by
  have : (fun k => (A.exec D (solo p k)).1.ps p = .idle) =
      (fun k => (A.exec D' (solo p k)).1.ps p = .idle) := by
    funext k
    have := (h.exec (solo p k) (solo_in {p} rfl k)).1.ps p rfl
    apply propext
    rw [← erase_eq_none, ← erase_eq_none, this]
  unfold kIdle; rw [this]

/-- The response of a one-event history, up to identifiers. -/
def respOf {Op R : Type} (h : List (HEv Q Op R)) : Option R :=
  match h.map HEv.erase with
  | [.res _ r _] => r
  | _ => none

@[simp] lemma respOf_single {Op R : Type} (a : ℕ) (r : Option R) (b : Bool) :
    respOf [(HEv.res a r b : HEv Q Op R)] = r := by
  simp [respOf, HEv.erase]

variable {A} in
lemma respOf_agree {p : Q} {D D' : A.Cfg} (h : A.Agree {p} D D') :
    respOf (A.exec D (solo p (kIdle A p D))).2 = respOf (A.exec D' (solo p (kIdle A p D'))).2 := by
  rw [kIdle_agree h]
  unfold respOf
  rw [(h.exec _ (solo_in {p} rfl _)).2]

/-- A solo run either leaves the process running (no events) or completes its operation. -/
lemma solo_cases (p : Q) (k : ℕ) : ∀ (C : A.Cfg) a o b l, C.ps p = .run a o b l →
    (∃ l', (A.exec C (solo p k)).1.ps p = .run a o b l' ∧ (A.exec C (solo p k)).2 = []) ∨
    ((A.exec C (solo p k)).1.ps p = .idle ∧ ∃ r, (A.exec C (solo p k)).2 = [.res a r b]) := by
  induction k with
  | zero => intro C a o b l h1; exact .inl ⟨l, by simpa using h1, rfl⟩
  | succ k ih =>
    intro C a o b l h1
    rw [RImpl.solo_succ, RImpl.exec_cons]
    simp only [RImpl.step1, h1]
    cases hact : A.act p l with
    | sh f =>
      rcases ih ⟨(f C.sh).2, C.pv, Function.update C.ps p (.run a o b (f C.sh).1), C.cnt⟩
        a o b (f C.sh).1 (by simp) with ⟨l', h2, h3⟩ | ⟨h2, r, h3⟩
      · exact .inl ⟨l', h2, by simp [h3]⟩
      · exact .inr ⟨h2, r, by simp [h3]⟩
    | pv f =>
      rcases ih ⟨C.sh, Function.update C.pv p (f (C.pv p)).2,
        Function.update C.ps p (.run a o b (f (C.pv p)).1), C.cnt⟩ a o b (f (C.pv p)).1 (by simp) with ⟨l', h2, h3⟩ | ⟨h2, r, h3⟩
      · exact .inl ⟨l', h2, by simp [h3]⟩
      · exact .inr ⟨h2, r, by simp [h3]⟩
    | ret r =>
      have h2 := A.exec_solo_idle ⟨C.sh, C.pv, Function.update C.ps p .idle, C.cnt⟩ p (by simp) k
      rw [h2]
      exact .inr ⟨by simp, r, by simp⟩

/-- A step that changes the shared memory is a shared-memory step: the process keeps running
and its private memory is unchanged. -/
lemma step_sh {C : A.Cfg} {p : Q} {a : ℕ} {o : O.Op} {b : Bool} {l : A.L}
    (hp : C.ps p = .run a o b l) (hsh : (A.step1 C (.step p)).1.sh ≠ C.sh) :
    ∃ l', (A.step1 C (.step p)).1.ps p = .run a o b l' ∧
      (A.step1 C (.step p)).1.pv p = C.pv p ∧ (A.step1 C (.step p)).2 = [] := by
  simp only [RImpl.step1, hp] at hsh ⊢
  cases hact : A.act p l with
  | sh f => simp
  | pv f => simp [hact] at hsh
  | ret r => simp [hact] at hsh

/-- A system-wide crash followed by a solo run of the recovery function of `p`: if `p` runs the
same operation with the same private memory in two configurations with the same shared memory,
the recovery function returns the same value in both. -/
lemma crash_recover (hof : A.ObstructionFree) {F F' : A.Cfg} (hF : A.Reachable F) {p : Q}
    {a a' : ℕ} {o : O.Op} {l l' : A.L} (hp : F.ps p = .run a o false l)
    (hp' : F'.ps p = .run a' o false l') (hsh : F.sh = F'.sh) (hpv : F.pv p = F'.pv p) :
    ∃ K x, (A.exec F (.crash :: solo p K)).2 = [.crash, .res a x true] ∧
      (A.exec F' (.crash :: solo p K)).2 = [.crash, .res a' x true] := by
  have hG : (A.step1 F .crash).1.ps p = .run a o true (A.recov p o) := by
    simp [RImpl.step1, hp, RImpl.crashPS]
  have hG' : (A.step1 F' .crash).1.ps p = .run a' o true (A.recov p o) := by
    simp [RImpl.step1, hp', RImpl.crashPS]
  have hag : A.Agree {p} (A.step1 F .crash).1 (A.step1 F' .crash).1 :=
    ⟨by simp [RImpl.step1, hsh],
      fun x hx => by rw [Set.mem_singleton_iff.1 hx]; simp [RImpl.step1, hpv],
      fun x hx => by rw [Set.mem_singleton_iff.1 hx, hG, hG']; rfl⟩
  have hreach : A.Reachable (A.step1 F .crash).1 := by
    have := A.reachable_exec hF [.crash]; rwa [RImpl.exec_singleton] at this
  have hidle := kIdle_spec A hof hreach p
  obtain ⟨x, hx⟩ := A.solo_hist p _ _ _ _ _ _ hG hidle
  obtain ⟨hag2, hhist⟩ := hag.exec (solo p (kIdle A p (A.step1 F .crash).1)) (solo_in {p} rfl _)
  have hidle' : (A.exec (A.step1 F' .crash).1
      (solo p (kIdle A p (A.step1 F .crash).1))).1.ps p = .idle := by
    rw [← erase_eq_none, ← hag2.ps p rfl, erase_eq_none]; exact hidle
  obtain ⟨x', hx'⟩ := A.solo_hist p _ _ _ _ _ _ hG' hidle'
  have hxx : x = x' := by
    rw [hx, hx'] at hhist; simpa [HEv.erase] using hhist
  refine ⟨kIdle A p (A.step1 F .crash).1, x, ?_, ?_⟩
  · rw [RImpl.exec_cons, hx]; rfl
  · rw [RImpl.exec_cons, hx', ← hxx]; rfl

end GenericExec

namespace Gadget

/-! ### The executions of the construction -/

variable (A : RImpl (casRC V v₀) P)

/-- `p i` invokes `c i` and takes `k` solo steps. -/
def pPart (i k : ℕ) : List (Ev P (casRC V v₀).Op) :=
  [.inv (G.p i) (G.c i)] ++ solo (O := casRC V v₀) (G.p i) k

/-- Execution of `pPart i k` from `C`. -/
def Ek (C : A.Cfg) (i k : ℕ) := A.exec C (G.pPart i k)

/-- Configuration after `pPart i k` and the invocation of `c i` by `q`. -/
def Dk (C : A.Cfg) (i k : ℕ) : A.Cfg := (A.exec C (G.pPart i k ++ [.inv G.q (G.c i)])).1

/-- History of `q` running solo from `D` until it is idle. -/
noncomputable def qhist (D : A.Cfg) := (A.exec D (solo G.q (kIdle A G.q D))).2

/-- Response of `q`'s `c i` after `p i` took `k` steps of its `c i`. -/
noncomputable def qr (C : A.Cfg) (i k : ℕ) : Option (V ⊕ Bool) := respOf (G.qhist A (G.Dk A C i k))

/-- The first `k` after which `q`'s `c i` returns `false`: the `k`-th step of `p i` is its
*modifying step* `s`. -/
noncomputable def mstar (C : A.Cfg) (i : ℕ) : ℕ := kOf (fun k => G.qr A C i k = some (.inr false))

/-- Number of steps of `p i` in the branch `bit` (`false`: before `s`; `true`: including `s`). -/
noncomputable def kk (C : A.Cfg) (i : ℕ) (bit : Bool) : ℕ :=
  if bit then G.mstar A C i else G.mstar A C i - 1

/-- `pPart i k`, then `q` runs `c i` solo to completion. -/
noncomputable def lvlK (C : A.Cfg) (i k : ℕ) : List (Ev P (casRC V v₀).Op) :=
  G.pPart i k ++ [.inv G.q (G.c i)] ++ solo G.q (kIdle A G.q (G.Dk A C i k))

/-- Schedule of level `i` in branch `bit`. -/
noncomputable def lvl (C : A.Cfg) (i : ℕ) (bit : Bool) : List (Ev P (casRC V v₀).Op) :=
  G.lvlK A C i (G.kk A C i bit)

/-- Schedule of the first `i` levels in the branches given by `b`. -/
noncomputable def sched (b : ℕ → Bool) : ℕ → List (Ev P (casRC V v₀).Op)
  | 0 => []
  | i + 1 => sched b i ++ G.lvl A (A.exec A.init (sched b i)).1 i (b i)

/-- The configuration `C` reached by `es` at the beginning of level `i`. -/
structure Base (b : ℕ → Bool) (i : ℕ) (es : List (Ev P (casRC V v₀).Op)) (C : A.Cfg) : Prop where
  exec : A.exec A.init es = (C, G.H b i)
  cnt : C.cnt = 2 * i
  q_idle : C.ps G.q = .idle
  p_idle : C.ps (G.p i) = .idle

variable {G A}

lemma Base.reach {b i es C} (hB : G.Base A b i es C) : A.Reachable C := ⟨es, by rw [hB.exec]⟩

lemma Base.hist {b i es C} (hB : G.Base A b i es C) (X : List (Ev P (casRC V v₀).Op)) :
    (A.exec A.init (es ++ X)).2 = G.H b i ++ (A.exec C X).2 := by
  rw [RImpl.exec_snd_append, hB.exec]

lemma Base.cfg {b i es C} (hB : G.Base A b i es C) (X : List (Ev P (casRC V v₀).Op)) :
    (A.exec A.init (es ++ X)).1 = (A.exec C X).1 := by
  rw [RImpl.exec_fst_append, hB.exec]

lemma pPart_exec {b i es C} (hB : G.Base A b i es C) (k : ℕ) :
    (G.Ek A C i k).1.cnt = 2 * i + 1 ∧
    (∀ x, x ≠ G.p i → (G.Ek A C i k).1.ps x = C.ps x ∧ (G.Ek A C i k).1.pv x = C.pv x) ∧
    ((∃ l, (G.Ek A C i k).1.ps (G.p i) = .run (2 * i) (G.c i) false l ∧
        (G.Ek A C i k).2 = [.inv (2 * i) (G.p i) (G.c i)]) ∨
      ((G.Ek A C i k).1.ps (G.p i) = .idle ∧
        ∃ r, (G.Ek A C i k).2 = [.inv (2 * i) (G.p i) (G.c i), .res (2 * i) r false])) := by
  have hstep := A.step1_inv_idle C (G.p i) (G.c i) hB.p_idle
  have h1 : (A.step1 C (.inv (G.p i) (G.c i))).1.ps (G.p i) =
      .run (2 * i) (G.c i) false (A.start (G.p i) (G.c i)) := by
    rw [hstep, hB.cnt]; simp
  have h2 : (A.step1 C (.inv (G.p i) (G.c i))).2 = [.inv (2 * i) (G.p i) (G.c i)] := by
    rw [hstep, hB.cnt]
  have h3 : (A.step1 C (.inv (G.p i) (G.c i))).1.cnt = 2 * i + 1 := by
    rw [hstep, hB.cnt]
  have h4 : ∀ x, x ≠ G.p i → (A.step1 C (.inv (G.p i) (G.c i))).1.ps x = C.ps x ∧
      (A.step1 C (.inv (G.p i) (G.c i))).1.pv x = C.pv x := by
    intro x hx; rw [hstep]; simp [Function.update_of_ne hx]
  have hE : G.Ek A C i k = ((A.exec (A.step1 C (.inv (G.p i) (G.c i))).1 (solo (G.p i) k)).1,
      (A.step1 C (.inv (G.p i) (G.c i))).2 ++
        (A.exec (A.step1 C (.inv (G.p i) (G.c i))).1 (solo (G.p i) k)).2) := by
    unfold Ek pPart; rw [RImpl.exec_append, RImpl.exec_singleton]
  rw [hE]
  refine ⟨by rw [A.exec_solo_cnt, h3], ?_, ?_⟩
  · intro x hx
    obtain ⟨h5, h6⟩ := A.exec_solo_other (A.step1 C (.inv (G.p i) (G.c i))).1 hx k
    exact ⟨h5.trans (h4 x hx).1, h6.trans (h4 x hx).2⟩
  · rcases solo_cases A (G.p i) k _ _ _ _ _ h1 with ⟨l', h5, h6⟩ | ⟨h5, r, h6⟩
    · exact .inl ⟨l', h5, by rw [h2, h6]; rfl⟩
    · exact .inr ⟨h5, r, by rw [h2, h6]; rfl⟩

lemma Ek_zero_sh {b i es C} (hB : G.Base A b i es C) : (G.Ek A C i 0).1.sh = C.sh := by
  unfold Ek pPart
  rw [RImpl.exec_append, RImpl.exec_singleton, A.step1_inv_idle C (G.p i) (G.c i) hB.p_idle]
  rfl

lemma Ek_succ (C : A.Cfg) (i k : ℕ) :
    G.Ek A C i (k + 1) = ((A.step1 (G.Ek A C i k).1 (.step (G.p i))).1,
      (G.Ek A C i k).2 ++ (A.step1 (G.Ek A C i k).1 (.step (G.p i))).2) := by
  unfold Ek pPart
  rw [RImpl.solo_succ', ← List.append_assoc, RImpl.exec_snoc]

lemma Dk_eq (C : A.Cfg) (i k : ℕ) :
    G.Dk A C i k = (A.step1 (G.Ek A C i k).1 (.inv G.q (G.c i))).1 := by
  unfold Dk Ek; rw [RImpl.exec_fst_append, RImpl.exec_singleton]


lemma delta_cas_inr (s a a' : V) : ∃ v, ((casRC V v₀).δ s (.cas a a')).2 = .inr v := by
  by_cases h : s = a <;> simp [h]

/-- Every value returned in the histories of the construction is a Boolean. -/
lemma inr_of_lin {b : ℕ → Bool} {i : ℕ} {T : List (HEv P (RCOp V) (V ⊕ Bool))} (hi : i ≤ G.m)
    (hT : ∀ a z o, HEv.inv a z o ∈ T → a / 2 = i ∧ i < G.m ∧ o = G.c i)
    {L : List (ℕ × RCOp V)} (hL : DLin (casRC V v₀) (G.H b i ++ T) v₀ L)
    {a : ℕ} {r : V ⊕ Bool} {c : Bool} (hres : HEv.res a (some r) c ∈ G.H b i ++ T) :
    ∃ v, r = .inr v := by
  obtain ⟨hc, -⟩ := G.lin_chain hi hT hL
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hL.mem_of_res a r c hres)
  obtain ⟨X, Y, hLX⟩ := List.append_of_mem hx
  have hr := legal_at hL.legal hLX (r := r) (c := c) (by rw [hx1]; exact hres)
  rw [(hc x hx).1] at hr
  obtain ⟨v, hv⟩ := delta_cas_inr (v₀ := v₀) ((casRC V v₀).runOps v₀ (X.map Prod.snd))
    (G.w (x.1 / 2)) (G.w (x.1 / 2 + 1))
  exact ⟨v, hr.trans hv⟩

lemma ev_in_q (i : ℕ) : ∀ e ∈ [(Ev.inv G.q (G.c i) : Ev P (casRC V v₀).Op)], e.In {G.q} := by
  intro e he
  rw [List.mem_singleton.1 he]
  exact Set.mem_singleton _

lemma q_stage (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) (k : ℕ) :
    ∃ r, G.qhist A (G.Dk A C i k) = [.res (2 * i + 1) (some r) false] ∧
      G.qr A C i k = some r ∧
      (A.exec C (G.lvlK A C i k)).2 =
        (G.Ek A C i k).2 ++ [.inv (2 * i + 1) G.q (G.c i), .res (2 * i + 1) (some r) false] ∧
      (A.exec C (G.lvlK A C i k)).1.cnt = 2 * i + 2 ∧
      (A.exec C (G.lvlK A C i k)).1.ps G.q = .idle ∧
      (∀ x, x ≠ G.q → (A.exec C (G.lvlK A C i k)).1.ps x = (G.Ek A C i k).1.ps x ∧
        (A.exec C (G.lvlK A C i k)).1.pv x = (G.Ek A C i k).1.pv x) := by
  obtain ⟨hcnt, hoth, -⟩ := pPart_exec hB k
  have hqp : G.q ≠ G.p i := (G.hpq i hi).symm
  have hqi : (G.Ek A C i k).1.ps G.q = .idle := (hoth G.q hqp).1.trans hB.q_idle
  have hstep := A.step1_inv_idle (G.Ek A C i k).1 G.q (G.c i) hqi
  have hDps : (G.Dk A C i k).ps G.q = .run (2 * i + 1) (G.c i) false (A.start G.q (G.c i)) := by
    rw [Dk_eq, hstep, hcnt]; simp
  have hDcnt : (G.Dk A C i k).cnt = 2 * i + 2 := by rw [Dk_eq, hstep, hcnt]
  have hDoth : ∀ x, x ≠ G.q → (G.Dk A C i k).ps x = (G.Ek A C i k).1.ps x ∧
      (G.Dk A C i k).pv x = (G.Ek A C i k).1.pv x := by
    intro x hx; rw [Dk_eq, hstep]; simp [Function.update_of_ne hx]
  have hreach : A.Reachable (G.Dk A C i k) :=
    ⟨es ++ (G.pPart i k ++ [.inv G.q (G.c i)]), by rw [hB.cfg]; rfl⟩
  have hidle := kIdle_spec A hof hreach G.q
  obtain ⟨r, hr⟩ := A.solo_hist G.q _ _ _ _ _ _ hDps hidle
  have e1 : A.exec C (G.pPart i k) = G.Ek A C i k := rfl
  have hfst : (A.exec C (G.lvlK A C i k)).1 =
      (A.exec (G.Dk A C i k) (solo G.q (kIdle A G.q (G.Dk A C i k)))).1 := by
    unfold lvlK; rw [RImpl.exec_fst_append]; rfl
  have hsnd : (A.exec C (G.lvlK A C i k)).2 =
      (G.Ek A C i k).2 ++ [.inv (2 * i + 1) G.q (G.c i), .res (2 * i + 1) r false] := by
    unfold lvlK
    have : (A.exec C (G.pPart i k ++ [.inv G.q (G.c i)])).1 = G.Dk A C i k := rfl
    rw [RImpl.exec_snd_append, this, hr, RImpl.exec_snoc, e1, hstep, hcnt]; simp
  -- `q`'s operation does not fail
  have hsome : ∃ r', r = some r' := by
    cases r with
    | some r' => exact ⟨r', rfl⟩
    | none =>
      exfalso
      apply (hcor (es ++ G.lvlK A C i k)).2 (2 * i + 1)
      rw [hB.hist, hsnd]; simp
  obtain ⟨r', rfl⟩ := hsome
  refine ⟨r', hr, by unfold qr qhist; rw [hr]; simp, hsnd, ?_, ?_, ?_⟩
  · rw [hfst, A.exec_solo_cnt, hDcnt]
  · rw [hfst]; exact hidle
  · intro x hx
    rw [hfst]
    obtain ⟨h1, h2⟩ := A.exec_solo_other (G.Dk A C i k) hx (kIdle A G.q (G.Dk A C i k))
    exact ⟨h1.trans (hDoth x hx).1, h2.trans (hDoth x hx).2⟩

lemma q_inr (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) (k : ℕ) : ∃ v, G.qr A C i k = some (.inr v) := by
  obtain ⟨r, -, hqr, hsnd, -⟩ := q_stage hof hcor hi hB k
  obtain ⟨-, -, hcase⟩ := pPart_exec hB k
  obtain ⟨L, hL⟩ := (hcor (es ++ G.lvlK A C i k)).1
  rw [hB.hist, hsnd] at hL
  have hT : ∀ a z o, HEv.inv a z o ∈ (G.Ek A C i k).2 ++
      [.inv (2 * i + 1) G.q (G.c i), .res (2 * i + 1) (some r) false] →
      a / 2 = i ∧ i < G.m ∧ o = G.c i := by
    intro a z o h
    rcases hcase with ⟨l, -, he⟩ | ⟨-, r0, he⟩ <;> rw [he] at h <;>
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
        or_false] at h
    · rcases h with h | h | h <;> cases h <;> exact ⟨by omega, hi, rfl⟩
    · rcases h with h | h | h | h | h <;> cases h <;> exact ⟨by omega, hi, rfl⟩
  obtain ⟨v, hv⟩ := G.inr_of_lin hi.le hT hL (a := 2 * i + 1) (r := r) (c := false) (by simp)
  exact ⟨v, by rw [hqr, hv]⟩

lemma qr_idle (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) (k : ℕ) (hidle : (G.Ek A C i k).1.ps (G.p i) = .idle) :
    G.qr A C i k = some (.inr false) := by
  obtain ⟨r, -, hqr, hsnd, -⟩ := q_stage hof hcor hi hB k
  obtain ⟨-, -, hcase⟩ := pPart_exec hB k
  rcases hcase with ⟨l, hl, -⟩ | ⟨-, r0, he⟩
  · rw [hidle] at hl; cases hl
  rw [he] at hsnd
  have hsome : ∃ r', r0 = some r' := by
    cases r0 with
    | some r' => exact ⟨r', rfl⟩
    | none =>
      exfalso
      apply (hcor (es ++ G.lvlK A C i k)).2 (2 * i)
      rw [hB.hist, hsnd]; simp
  obtain ⟨r', rfl⟩ := hsome
  obtain ⟨L, hL⟩ := (hcor (es ++ G.lvlK A C i k)).1
  rw [hB.hist, hsnd] at hL
  simp only [List.cons_append, List.nil_append] at hL
  rw [hqr, G.lin_second hi hL]

lemma qr_zero (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) : G.qr A C i 0 = some (.inr true) := by
  have hqp : G.q ≠ G.p i := (G.hpq i hi).symm
  obtain ⟨-, hoth, -⟩ := pPart_exec hB 0
  have hag0 : A.Agree {G.q} C (G.Ek A C i 0).1 :=
    ⟨(Ek_zero_sh hB).symm, fun x hx => by rw [Set.mem_singleton_iff.1 hx, (hoth G.q hqp).2],
      fun x hx => by rw [Set.mem_singleton_iff.1 hx, (hoth G.q hqp).1]⟩
  have hag := (hag0.exec _ (G.ev_in_q i)).1
  rw [RImpl.exec_singleton, RImpl.exec_singleton, ← Dk_eq] at hag
  have hresp := respOf_agree hag
  set D' := (A.step1 C (.inv G.q (G.c i))).1 with hD'
  have hstepq := A.step1_inv_idle C G.q (G.c i) hB.q_idle
  have hreach : A.Reachable D' := ⟨es ++ [.inv G.q (G.c i)], by rw [hB.cfg, RImpl.exec_singleton]⟩
  have hDps : D'.ps G.q = .run (2 * i) (G.c i) false (A.start G.q (G.c i)) := by
    rw [hD', hstepq, hB.cnt]; simp
  have hidle := kIdle_spec A hof hreach G.q
  obtain ⟨r, hr⟩ := A.solo_hist G.q _ _ _ _ _ _ hDps hidle
  have hsnd : (A.exec A.init (es ++ ([.inv G.q (G.c i)] ++ solo G.q (kIdle A G.q D')))).2 =
      G.H b i ++ [.inv (2 * i) G.q (G.c i), .res (2 * i) r false] := by
    rw [hB.hist, RImpl.exec_snd_append, RImpl.exec_singleton, ← hD', hr]
    rw [hstepq, hB.cnt]; simp
  have hsome : ∃ r', r = some r' := by
    cases r with
    | some r' => exact ⟨r', rfl⟩
    | none =>
      exfalso
      apply (hcor (es ++ ([.inv G.q (G.c i)] ++ solo G.q (kIdle A G.q D')))).2 (2 * i)
      rw [hsnd]; simp
  obtain ⟨r', rfl⟩ := hsome
  obtain ⟨L, hL⟩ := (hcor (es ++ ([.inv G.q (G.c i)] ++ solo G.q (kIdle A G.q D')))).1
  rw [hsnd] at hL
  have h1 := G.lin_first hi hL
  unfold qr qhist
  rw [← hresp, hr, h1]; simp

lemma qr_eq_of_sh {b i es C} (hi : i < G.m) (hB : G.Base A b i es C) {k k' : ℕ}
    (h : (G.Ek A C i k).1.sh = (G.Ek A C i k').1.sh) : G.qr A C i k = G.qr A C i k' := by
  have hqp : G.q ≠ G.p i := (G.hpq i hi).symm
  obtain ⟨-, hoth, -⟩ := pPart_exec hB k
  obtain ⟨-, hoth', -⟩ := pPart_exec hB k'
  have hag0 : A.Agree {G.q} (G.Ek A C i k).1 (G.Ek A C i k').1 :=
    ⟨h, fun x hx => by rw [Set.mem_singleton_iff.1 hx, (hoth G.q hqp).2, (hoth' G.q hqp).2],
      fun x hx => by rw [Set.mem_singleton_iff.1 hx, (hoth G.q hqp).1, (hoth' G.q hqp).1]⟩
  have hag := (hag0.exec _ (G.ev_in_q i)).1
  rw [RImpl.exec_singleton, RImpl.exec_singleton, ← Dk_eq, ← Dk_eq] at hag
  unfold qr qhist
  exact respOf_agree hag

lemma mstar_spec (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) :
    0 < G.mstar A C i ∧ G.qr A C i (G.mstar A C i) = some (.inr false) ∧
      ∀ k < G.mstar A C i, G.qr A C i k = some (.inr true) := by
  have hex : ∃ k, G.qr A C i k = some (.inr false) := by
    have hreach : A.Reachable (A.exec C [.inv (G.p i) (G.c i)]).1 :=
      ⟨es ++ [.inv (G.p i) (G.c i)], by rw [hB.cfg]⟩
    obtain ⟨K, hK⟩ := hof _ hreach (G.p i)
    refine ⟨K, qr_idle hof hcor hi hB K ?_⟩
    unfold Ek pPart; rw [RImpl.exec_fst_append]; exact hK
  have hspec : G.qr A C i (G.mstar A C i) = some (.inr false) := kOf_spec hex
  have hmin : ∀ k < G.mstar A C i, G.qr A C i k = some (.inr true) := by
    intro k hk
    have h1 := kOf_min hex hk
    obtain ⟨v, hv⟩ := q_inr hof hcor hi hB k
    cases v
    · exact absurd hv h1
    · exact hv
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, hspec, hmin⟩
  have h2 := qr_zero hof hcor hi hB
  rw [← h0, hspec] at h2
  simp at h2

lemma run_of_lt (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) {k : ℕ} (hk : k < G.mstar A C i) :
    ∃ l, (G.Ek A C i k).1.ps (G.p i) = .run (2 * i) (G.c i) false l ∧
      (G.Ek A C i k).2 = [.inv (2 * i) (G.p i) (G.c i)] := by
  obtain ⟨-, -, hcase⟩ := pPart_exec hB k
  rcases hcase with h | ⟨hidle, -⟩
  · exact h
  · have h1 := qr_idle hof hcor hi hB k hidle
    rw [(mstar_spec hof hcor hi hB).2.2 k hk] at h1
    simp at h1

/-- The modifying step `s` of `p i` is a shared-memory step: it does not change the private
memory of `p i`, and `p i` is still running after it. -/
lemma s_step (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) :
    (G.Ek A C i (G.mstar A C i)).1.pv (G.p i) = (G.Ek A C i (G.mstar A C i - 1)).1.pv (G.p i) ∧
    ∃ l, (G.Ek A C i (G.mstar A C i)).1.ps (G.p i) = .run (2 * i) (G.c i) false l ∧
      (G.Ek A C i (G.mstar A C i)).2 = [.inv (2 * i) (G.p i) (G.c i)] := by
  obtain ⟨hpos, hs, hlt⟩ := mstar_spec hof hcor hi hB
  set k := G.mstar A C i - 1 with hk
  have hk1 : G.mstar A C i = k + 1 := by omega
  obtain ⟨l, hl, he⟩ := run_of_lt hof hcor hi hB (k := k) (by omega)
  have hsucc := Ek_succ (G := G) (A := A) C i k
  rw [hk1, hsucc]
  have hsh : (A.step1 (G.Ek A C i k).1 (.step (G.p i))).1.sh ≠ (G.Ek A C i k).1.sh := by
    intro heq
    have h1 := qr_eq_of_sh hi hB (k := k + 1) (k' := k) (by rw [hsucc]; exact heq)
    rw [← hk1, hs, hlt k (by omega)] at h1
    simp at h1
  obtain ⟨l', h1, h2, h3⟩ := step_sh A hl hsh
  exact ⟨h2, l', h1, by rw [he, h3]; rfl⟩

/-- One level of the construction. -/
lemma level_step (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) (bit : Bool) :
    (A.exec C (G.lvl A C i bit)).2 = [.inv (2 * i) (G.p i) (G.c i), .inv (2 * i + 1) G.q (G.c i),
      .res (2 * i + 1) (some (.inr (!bit))) false] ∧
    (A.exec C (G.lvl A C i bit)).1.cnt = 2 * i + 2 ∧
    (A.exec C (G.lvl A C i bit)).1.ps G.q = .idle ∧
    (∃ l, (A.exec C (G.lvl A C i bit)).1.ps (G.p i) = .run (2 * i) (G.c i) false l) ∧
    (∀ x, x ≠ G.q → x ≠ G.p i → (A.exec C (G.lvl A C i bit)).1.ps x = C.ps x ∧
      (A.exec C (G.lvl A C i bit)).1.pv x = C.pv x) ∧
    (A.exec C (G.lvl A C i bit)).1.pv (G.p i) = (G.Ek A C i (G.kk A C i bit)).1.pv (G.p i) := by
  have hqp : G.q ≠ G.p i := (G.hpq i hi).symm
  -- facts about `kk bit`
  have hkk : (∃ l, (G.Ek A C i (G.kk A C i bit)).1.ps (G.p i) = .run (2 * i) (G.c i) false l ∧
      (G.Ek A C i (G.kk A C i bit)).2 = [.inv (2 * i) (G.p i) (G.c i)]) ∧
      G.qr A C i (G.kk A C i bit) = some (.inr (!bit)) := by
    obtain ⟨hpos, hs, hlt⟩ := mstar_spec hof hcor hi hB
    cases bit
    · simp only [kk, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      exact ⟨run_of_lt hof hcor hi hB (by omega), hlt _ (by omega)⟩
    · simp only [kk, ↓reduceIte, Bool.not_true]
      exact ⟨(s_step hof hcor hi hB).2, hs⟩
  obtain ⟨⟨l, hl, he⟩, hqr⟩ := hkk
  obtain ⟨r, -, hqr', hsnd, hcnt, hq, hoth⟩ := q_stage hof hcor hi hB (G.kk A C i bit)
  obtain ⟨-, hothE, -⟩ := pPart_exec hB (G.kk A C i bit)
  rw [hqr'] at hqr
  cases hqr
  have hlvl : G.lvl A C i bit = G.lvlK A C i (G.kk A C i bit) := rfl
  rw [hlvl]
  refine ⟨?_, hcnt, hq, ⟨l, by rw [(hoth _ hqp.symm).1, hl]⟩, ?_, (hoth _ hqp.symm).2⟩
  · rw [hsnd, he]; rfl
  · intro x hxq hxp
    exact ⟨(hoth x hxq).1.trans (hothE x hxp).1, (hoth x hxq).2.trans (hothE x hxp).2⟩

/-- **The key step**: the private memory of `p i` is the same in both branches. -/
lemma level_pv (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b i es C} (hi : i < G.m)
    (hB : G.Base A b i es C) :
    (A.exec C (G.lvl A C i true)).1.pv (G.p i) = (A.exec C (G.lvl A C i false)).1.pv (G.p i) := by
  rw [(level_step hof hcor hi hB true).2.2.2.2.2, (level_step hof hcor hi hB false).2.2.2.2.2]
  simp only [kk, ↓reduceIte, Bool.false_eq_true]
  exact (s_step hof hcor hi hB).1


/-! ### All levels -/

lemma sched_succ (b : ℕ → Bool) (i : ℕ) :
    G.sched A b (i + 1) = G.sched A b i ++ G.lvl A (A.exec A.init (G.sched A b i)).1 i (b i) :=
  rfl

/-- Invariant of the construction after `i` levels. -/
lemma sched_inv (hof : A.ObstructionFree) (hcor : A.DurLinDet) (b : ℕ → Bool) (i : ℕ)
    (hi : i ≤ G.m) :
    (A.exec A.init (G.sched A b i)).2 = G.H b i ∧
    (A.exec A.init (G.sched A b i)).1.cnt = 2 * i ∧
    (A.exec A.init (G.sched A b i)).1.ps G.q = .idle ∧
    (∀ k, i ≤ k → k < G.m → (A.exec A.init (G.sched A b i)).1.ps (G.p k) = .idle) ∧
    (∀ k < i, ∃ l, (A.exec A.init (G.sched A b i)).1.ps (G.p k) = .run (2 * k) (G.c k) false l) := by
  induction i with
  | zero =>
    refine ⟨rfl, rfl, rfl, fun k _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (by omega)
    have hB : G.Base A b i (G.sched A b i) (A.exec A.init (G.sched A b i)).1 :=
      ⟨Prod.ext rfl h1, h2, h3, h4 i le_rfl (by omega)⟩
    obtain ⟨l1, l2, l3, ⟨l, l4⟩, l5, -⟩ := level_step hof hcor (show i < G.m by omega) hB (b i)
    rw [sched_succ, hB.hist, hB.cfg]
    refine ⟨by rw [l1]; rfl, by rw [l2]; omega, l3, ?_, ?_⟩
    · intro k hk1 hk2
      have hpk : G.p k ≠ G.p i := fun h => by have := G.hp k i hk2 (by omega) h; omega
      rw [(l5 (G.p k) (G.hpq k hk2) hpk).1]; exact h4 k (by omega) hk2
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · have hpk : G.p k ≠ G.p i := fun h => by have := G.hp k i (by omega) (by omega) h; omega
        rw [(l5 (G.p k) (G.hpq k (by omega)) hpk).1]; exact h5 k hk
      · exact ⟨l, l4⟩

lemma base_of_sched (hof : A.ObstructionFree) (hcor : A.DurLinDet) (b : ℕ → Bool) {i : ℕ}
    (hi : i < G.m) : G.Base A b i (G.sched A b i) (A.exec A.init (G.sched A b i)).1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := sched_inv hof hcor b i hi.le
  exact ⟨Prod.ext rfl h1, h2, h3, h4 i le_rfl hi⟩

/-- Later levels do not touch the private memory of `p j`. -/
lemma sched_pv (hof : A.ObstructionFree) (hcor : A.DurLinDet) (b : ℕ → Bool) (j : ℕ) (d : ℕ)
    (hd : j + 1 + d ≤ G.m) :
    (A.exec A.init (G.sched A b (j + 1 + d))).1.pv (G.p j) =
      (A.exec A.init (G.sched A b (j + 1))).1.pv (G.p j) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hi : j + 1 + d < G.m := by omega
    have hB := base_of_sched hof hcor b hi
    obtain ⟨-, -, -, -, l5, -⟩ := level_step hof hcor hi hB (b (j + 1 + d))
    have hpj : G.p j ≠ G.p (j + 1 + d) := fun h => by
      have := G.hp j (j + 1 + d) (by omega) hi h; omega
    rw [show j + 1 + (d + 1) = (j + 1 + d) + 1 by omega, sched_succ, hB.cfg,
      (l5 (G.p j) (G.hpq j (by omega)) hpj).2, ← ih (by omega)]

lemma sched_congr {b b' : ℕ → Bool} {i : ℕ} (h : ∀ k < i, b k = b' k) :
    G.sched A b i = G.sched A b' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [sched_succ, sched_succ, ih (fun k hk => h k (by omega)), h i (by omega)]

lemma H_congr {b b' : ℕ → Bool} {i : ℕ} (h : ∀ k < i, b k = b' k) : G.H b i = G.H b' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [H, blk, ih (fun k hk => h k (by omega)), h i (by omega)]

/-- **Distinctness**: two branches that first differ at level `j` end in configurations with
different shared memory. -/
lemma distinct_aux (hof : A.ObstructionFree) (hcor : A.DurLinDet) {b b' : ℕ → Bool} {j : ℕ}
    (hj : j < G.m) (heq : ∀ k < j, b k = b' k) (hb : b j = false) (hb' : b' j = true) :
    (A.exec A.init (G.sched A b G.m)).1.sh ≠ (A.exec A.init (G.sched A b' G.m)).1.sh := by
  intro hsh
  -- the private memory of `p j` is the same in both final configurations
  have hpv : (A.exec A.init (G.sched A b G.m)).1.pv (G.p j) =
      (A.exec A.init (G.sched A b' G.m)).1.pv (G.p j) := by
    have e1 := sched_pv (G := G) (A := A) hof hcor b j (G.m - (j + 1)) (by omega)
    have e2 := sched_pv (G := G) (A := A) hof hcor b' j (G.m - (j + 1)) (by omega)
    rw [show j + 1 + (G.m - (j + 1)) = G.m by omega] at e1 e2
    rw [e1, e2, sched_succ, sched_succ, sched_congr heq]
    have hB := base_of_sched hof hcor b' hj
    rw [hB.cfg, hB.cfg, hb, hb']
    exact (level_pv hof hcor hj hB).symm
  obtain ⟨h1, -, -, -, h5⟩ := sched_inv hof hcor b G.m le_rfl
  obtain ⟨h1', -, -, -, h5'⟩ := sched_inv hof hcor b' G.m le_rfl
  obtain ⟨l, hl⟩ := h5 j hj
  obtain ⟨l', hl'⟩ := h5' j hj
  obtain ⟨K, x, hx, hx'⟩ := crash_recover A hof ⟨_, rfl⟩ hl hl' hsh hpv
  obtain ⟨L, hL⟩ := (hcor (G.sched A b G.m ++ (.crash :: solo (G.p j) K))).1
  obtain ⟨L', hL'⟩ := (hcor (G.sched A b' G.m ++ (.crash :: solo (G.p j) K))).1
  rw [RImpl.exec_snd_append, h1, hx] at hL
  rw [RImpl.exec_snd_append, h1', hx'] at hL'
  have hs := G.lin_final_s hj hb' hL'
  subst hs
  exact G.lin_final_ns hj hb hL

/-- **Theorem 1** for a gadget: at least `2 ^ m` reachable configurations with pairwise
different shared memory. -/
theorem lower_bound (hof : A.ObstructionFree) (hcor : A.DurLinDet) :
    (2 : ℕ∞) ^ G.m ≤ Set.encard {s : A.Sh | ∃ C, A.Reachable C ∧ C.sh = s} := by
  classical
  let ext : (Fin G.m → Bool) → ℕ → Bool := fun g k => if h : k < G.m then g ⟨k, h⟩ else false
  let Φ : (Fin G.m → Bool) → A.Sh := fun g => (A.exec A.init (G.sched A (ext g) G.m)).1.sh
  have hinj : Function.Injective Φ := by
    intro g g' hgg
    by_contra hne
    have hex : ∃ j, j < G.m ∧ ext g j ≠ ext g' j := by
      obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
      exact ⟨t.1, t.2, by simpa [ext, t.2] using ht⟩
    have hj : Nat.find hex < G.m ∧ ext g (Nat.find hex) ≠ ext g' (Nat.find hex) :=
      Nat.find_spec hex
    have heq : ∀ k < Nat.find hex, ext g k = ext g' k := by
      intro k hk
      by_contra h
      exact Nat.find_min hex hk ⟨by omega, h⟩
    cases hb : ext g (Nat.find hex) <;> cases hb' : ext g' (Nat.find hex)
    · rw [hb, hb'] at hj; exact hj.2 rfl
    · exact distinct_aux hof hcor hj.1 heq hb hb' hgg
    · exact distinct_aux hof hcor hj.1 (fun k hk => (heq k hk).symm) hb' hb hgg.symm
    · rw [hb, hb'] at hj; exact hj.2 rfl
  calc (2 : ℕ∞) ^ G.m = Set.encard (Set.univ : Set (Fin G.m → Bool)) := by
        simp [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    _ ≤ _ := Set.encard_le_encard_of_injOn
        (fun g _ => show Φ g ∈ {s : A.Sh | ∃ C, A.Reachable C ∧ C.sh = s} from
          ⟨_, ⟨_, rfl⟩, rfl⟩) hinj.injOn

end Gadget

end Thm1

open Thm1

/-- **Theorem 1** of [Ben-Baruch, Hendler, Rusanovsky, PODC 2020]: an obstruction-free,
durably linearizable and detectable implementation of a CAS object for `N` processes, over a
domain of at least `N` values, has at least `2 ^ (N - 1)` reachable configurations with pairwise
different shared memory. -/
theorem theorem1 {P : Type} [Fintype P] [DecidableEq P] {V : Type} [DecidableEq V] (v₀ : V)
    (A : RImpl (casRC V v₀) P) (hof : A.ObstructionFree) (hcor : A.DurLinDet)
    (hV : Nonempty (Fin (Fintype.card P) ↪ V)) :
    (2 : ℕ∞) ^ (Fintype.card P - 1) ≤ Set.encard {s : A.Sh | ∃ C, A.Reachable C ∧ C.sh = s} := by
  by_cases hn : Fintype.card P ≤ 1
  · rw [show Fintype.card P - 1 = 0 by omega, pow_zero]
    exact Set.one_le_encard_iff_nonempty.2 ⟨A.sh₀, A.init, A.reachable_init, rfl⟩
  obtain ⟨emb⟩ := hV
  set n := Fintype.card P with hn_def
  have h0 : 0 < n := by omega
  have hm : n - 1 < n := by omega
  let e := Fintype.equivFin P
  let q : P := e.symm ⟨n - 1, hm⟩
  let p : ℕ → P := fun i => if h : i < n then e.symm ⟨i, h⟩ else q
  let σ := Equiv.swap (emb ⟨0, h0⟩) v₀
  let w : ℕ → V := fun i => if h : i < n then σ (emb ⟨i, h⟩) else v₀
  let G : Gadget P V v₀ :=
    { m := n - 1, q := q, p := p, w := w
      hpq := by
        intro i hi h
        simp only [p, show i < n by omega, dite_true, q] at h
        have := congrArg Fin.val (e.symm.injective h)
        simp at this; omega
      hp := by
        intro i j hi hj h
        simp only [p, show i < n by omega, show j < n by omega, dite_true] at h
        have := congrArg Fin.val (e.symm.injective h)
        simpa using this
      hw0 := by simp [w, h0, σ]
      hw := by
        intro i j hi hj h
        simp only [w, show i < n by omega, show j < n by omega, dite_true] at h
        have := congrArg Fin.val (emb.injective (σ.injective h))
        simpa using this }
  exact Gadget.lower_bound (G := G) (A := A) hof hcor

/-- Corollary of Theorem 1: the shared memory needs at least `N - 1` bits (even if only the
reachable shared-memory states have to be encoded injectively). -/
theorem theorem1_bits {P : Type} [Fintype P] [DecidableEq P] {V : Type} [DecidableEq V] (v₀ : V)
    (A : RImpl (casRC V v₀) P) (hof : A.ObstructionFree) (hcor : A.DurLinDet)
    (hV : Nonempty (Fin (Fintype.card P) ↪ V)) (b : ℕ) (enc : A.Sh → (Fin b → Bool))
    (henc : Set.InjOn enc {s : A.Sh | ∃ C, A.Reachable C ∧ C.sh = s}) :
    Fintype.card P - 1 ≤ b := by
  have h1 := theorem1 v₀ A hof hcor hV
  rw [← henc.encard_image] at h1
  have h2 : (enc '' {s : A.Sh | ∃ C, A.Reachable C ∧ C.sh = s}).encard ≤ (2 : ℕ∞) ^ b := by
    refine Set.encard_le_card.trans ?_
    simp [ENat.card_eq_coe_fintype_card]
  have h3 : 2 ^ (Fintype.card P - 1) ≤ 2 ^ b := by exact_mod_cast h1.trans h2
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 h3

end Papers.PODC2020.DetectableSpace
