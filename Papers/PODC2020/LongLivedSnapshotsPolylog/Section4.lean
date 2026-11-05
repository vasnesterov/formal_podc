import Papers.PODC2020.LongLivedSnapshotsPolylog.Section4Log
import Papers.PODC2012.LimitedUseSnapshots.SnapshotLemma41
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Section 4.1: bounded increments in Algorithm 2 (Lemmas 4.1 and 4.2)

Algorithm 2 of the paper is Algorithm 3 of Aspnes–Attiya–Censor-Hillel–Ellen with unbounded max
arrays and max registers; with atomic base objects it is `Snapshot.alg3 T v₀`
(`Papers/PODC2012/LimitedUseSnapshots/SnapshotDefs.lean`), for an arbitrary binary tree `T`
whose leaves are the processes (`T.WF`). The max registers of interest are the two components of
the max array `u.MA` of every internal node `u` (key `some (p, b)`: side `b` of the node at
address `p`, written by `MaxUpdate` of Line 8) and `root.MR` (key `none`, Line 14).

## Proof

We do not follow the paper's history-based argument (claims (1), (2) and Claim 5); instead we
strengthen the invariant of Theorem 4.2 of [AACE] (`Snapshot.Inv`, whose ghost `SeqR` gives the
vector `seq` of leaf pointers represented by each index) by `RepInv`: for the current value `x`
of side `b` of `p.MA` (child `c`) and every process `j` below `c`,
`count_j ≤ seq[x]_j + owe`, where `owe ∈ {0, 1}` is `1` iff the current `Update` of `j` has not
yet performed its `MaxUpdate` of side `b` on `p.MA` (and similarly for `root.MR`). This is
inductive because `seq` is monotone in the index. Then a `MaxUpdate(ptr)` satisfies
`ptr = Σ_{j ∈ c} seq[ptr]_j ≤ Σ_{j ∈ c} count_j ≤ Σ_{j ∈ c} (seq[x]_j + 1) = x + |leaves c|`.
-/

namespace Podc.LongLivedSnapshotsPolylog.Section4

open Cslib.SharedMemory Podc.LimitedUseSnapshots
open Podc.LimitedUseSnapshots.Snapshot (BTree Cfg Mem Inv PInv GInv SeqR cntOf alg3 swSnap)

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-- The `WriteMax` (on a component of a max array, or on `root.MR`) that a process of
Algorithm 2 in local state `l` is about to perform: key `some (p, b)` is side `b` of the max
array of the node at address `p`, key `none` is `root.MR`. -/
def wm3 (_i : P) (l : Snapshot.Loc P V) : Option (Option (List Bool × Bool) × ℕ) :=
  match l.pc with
  | .up (b :: p) ptr => some (some (p, b), ptr)
  | .up [] ptr => some (none, ptr)
  | .wm d => some (none, d)
  | _ => none

/-- Side `b` of a pair (`false` = left). -/
def side : Bool → ℕ × ℕ → ℕ
  | false, x => x.1
  | true, x => x.2

/-- The state of the max register with key `k`. -/
def mval (M : Mem v₀) : Option (List Bool × Bool) → ℕ
  | none => M .mr
  | some (p, b) => side b (M (.ma p))

omit [DecidableEq P] in
lemma wm3_eq_some_some {i : P} {l : Snapshot.Loc P V} {p : List Bool} {b : Bool} {v : ℕ}
    (h : wm3 i l = some (some (p, b), v)) : l.pc = .up (b :: p) v := by
  unfold wm3 at h; split at h <;> simp_all

omit [DecidableEq P] in
lemma wm3_eq_some_none {i : P} {l : Snapshot.Loc P V} {v : ℕ}
    (h : wm3 i l = some (none, v)) : l.pc = .up [] v ∨ l.pc = .wm v := by
  unfold wm3 at h; split at h <;> simp_all

/-! ### The memory is the maximum of the writes -/

/-- One step of Algorithm 2 updates each max register by the value written (if any). -/
lemma mval_step {C C' : Cfg v₀} {ℓ : Label P (swSnap P V v₀)}
    (h : (alg3 T v₀).step C ℓ = some C') (k : Option (List Bool × Bool)) :
    mval C'.mem k = max (mval C.mem k) (lmax ((stepLog wm3 C ℓ).filterMap (selK k))) := by
  cases ℓ with
  | inv p o => rw [(Impl.step_inv h).2.2.2.2]; simp [stepLog]
  | ret p r => rw [(Impl.step_ret h).2.2.1]; simp [stepLog]
  | tau p =>
    obtain ⟨-, -, i, o, kk, hact, hmem, -⟩ := Impl.step_tau h
    rw [hmem]
    rcases hl : C.loc p with ⟨n, pc⟩
    rw [hl] at hact
    cases pc with
    | idle | ackU | retS _ => simp [Snapshot.act] at hact
    | lw v =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q, b⟩ <;> simp [mval, stepLog, hl, wm3]
    | up a ptr =>
      rcases a with _ | ⟨b, q⟩
      · simp only [Snapshot.act] at hact; cases hact
        rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3, selK]
      · simp only [Snapshot.act] at hact; cases hact
        rcases k with _ | ⟨q', b'⟩
        · simp [mval, stepLog, hl, wm3, selK]
        · by_cases hq : q' = q
          · subst hq
            by_cases hb : b' = b
            · subst hb; cases b' <;> simp [mval, stepLog, hl, wm3, selK, side]
            · cases b' <;> cases b <;> simp_all [mval, stepLog, wm3, selK, side]
          · have hq' : (some (q, b) : Option (List Bool × Bool)) ≠ some (q', b') := by simp [Ne.symm hq]
            simp [mval, stepLog, hl, wm3, selK, hq, hq']
    | sc q =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]
    | rl q x y =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]
    | rr q x y lv =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]
    | wv q k' val =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]
    | wm d =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3, selK]
    | s0 =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]
    | s1 c =>
      simp only [Snapshot.act] at hact; cases hact
      rcases k with _ | ⟨q', b'⟩ <;> simp [mval, stepLog, hl, wm3]

/-! ### Pending obligations of a process -/

/-- `owe a l = 1` iff the current `Update` of a process in local state `l` has passed its leaf
write but has not yet reported the node `a ≠ []` to its parent (`MaxUpdate` on the parent's max
array, Line 8). -/
def owe (a : List Bool) (l : Snapshot.Loc P V) : ℕ :=
  match l.pc with
  | .up a' _ => if a <:+ a' then 1 else 0
  | .sc p | .rl p _ _ | .rr p _ _ _ | .wv p _ _ => if a <:+ p then 1 else 0
  | _ => 0

/-- `oweR l = 1` iff the current `Update` of a process in local state `l` has passed its leaf
write but has not yet performed its `WriteMax(root.MR, ·)` (Line 14). -/
def oweR (l : Snapshot.Loc P V) : ℕ :=
  match l.pc with
  | .up _ _ | .sc _ | .rl _ _ _ | .rr _ _ _ _ | .wv _ _ _ | .wm _ => 1
  | _ => 0

omit [DecidableEq P] in
lemma owe_le_one (a : List Bool) (l : Snapshot.Loc P V) : owe a l ≤ 1 := by
  unfold owe; split <;> (try split) <;> omega

omit [DecidableEq P] in
lemma oweR_le_one (l : Snapshot.Loc P V) : oweR l ≤ 1 := by
  unfold oweR; split <;> omega

omit [DecidableEq P] in
lemma owe_cont (a : List Bool) (ha : a ≠ []) (n : ℕ) (q : List Bool) (k : ℕ) :
    owe a (⟨n, Snapshot.cont q k⟩ : Snapshot.Loc P V) = if a <:+ q then 1 else 0 := by
  unfold Snapshot.cont
  split_ifs with h1 h2 h2
  · subst h1; exact absurd (List.eq_nil_of_suffix_nil h2) ha
  · rfl
  · simp [owe, h2]
  · simp [owe, h2]

omit [DecidableEq P] in
lemma oweR_cont (n : ℕ) (q : List Bool) (k : ℕ) :
    oweR (⟨n, Snapshot.cont q k⟩ : Snapshot.Loc P V) = 1 := by
  unfold Snapshot.cont; split_ifs <;> rfl

/-- How the obligations of a process evolve in a step: the counter plus the obligations never
grow, except at the `MaxUpdate` that discharges the obligation for `a` (which keeps the
counter). -/
lemma owe_step {C C' : Cfg v₀} {ℓ : Label P (swSnap P V v₀)}
    (h : (alg3 T v₀).step C ℓ = some C') {j : P} (hidle : C.pend j = none → (C.loc j).pc = .idle)
    {a : List Bool} (ha : a ≠ []) (hsuf : a <:+ T.path j) :
    (C'.loc j).cnt + owe a (C.loc j) ≤ (C.loc j).cnt + owe a (C'.loc j) ∨
      (ℓ = .tau j ∧ (C'.loc j).cnt = (C.loc j).cnt ∧ ∃ ptr, (C.loc j).pc = .up a ptr) := by
  by_cases hq : ℓ.proc = j
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨hpend, -, -, hloc, -⟩ := Impl.step_inv h
      left
      rw [hloc, Function.update_self]
      have := hidle hpend
      cases o <;> simp [owe, this]
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret h
      left
      rw [hloc, Function.update_self]
      rcases hl : C.loc q with ⟨n, pc⟩
      rw [hl] at hact
      cases pc with
      | up a ptr => cases a <;> simp [Snapshot.act] at hact
      | idle | ackU | retS _ => simp only [Snapshot.act] at hact; cases hact; simp [owe]
      | _ => simp [Snapshot.act] at hact
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, i, o, kk, hact, -, hloc⟩ := Impl.step_tau h
      rw [hloc, Function.update_self]
      rcases hl : C.loc q with ⟨n, pc⟩
      rw [hl] at hact
      cases pc with
      | idle | ackU | retS _ => simp [Snapshot.act] at hact
      | lw v =>
        simp only [Snapshot.act] at hact; cases hact
        left; dsimp only; rw [owe_cont a ha]; simp [hsuf, owe]
      | up a' ptr =>
        rcases a' with _ | ⟨b, p⟩
        · simp only [Snapshot.act] at hact; cases hact
          left; simp [owe, ha]
        · simp only [Snapshot.act] at hact; cases hact
          by_cases hab : a = b :: p
          · right; exact ⟨rfl, rfl, ptr, by rw [hab]⟩
          · left
            simp only [owe, List.suffix_cons_iff, hab, false_or]
            omega
      | sc p => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
      | rl p x y => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
      | rr p x y lv => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
      | wv p k val =>
        simp only [Snapshot.act] at hact; cases hact
        left; dsimp only; rw [owe_cont a ha]; simp [owe]
      | wm d => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
      | s0 => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
      | s1 c => simp only [Snapshot.act] at hact; cases hact; left; simp [owe]
  · left; rw [(Impl.step_other h hq).1]

/-- The same for the obligation towards `root.MR`. -/
lemma oweR_step {C C' : Cfg v₀} {ℓ : Label P (swSnap P V v₀)}
    (h : (alg3 T v₀).step C ℓ = some C') {j : P} (hidle : C.pend j = none → (C.loc j).pc = .idle) :
    (C'.loc j).cnt + oweR (C.loc j) ≤ (C.loc j).cnt + oweR (C'.loc j) ∨
      (ℓ = .tau j ∧ (C'.loc j).cnt = (C.loc j).cnt ∧
        ∃ d, (C.loc j).pc = .up [] d ∨ (C.loc j).pc = .wm d) := by
  by_cases hq : ℓ.proc = j
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨hpend, -, -, hloc, -⟩ := Impl.step_inv h
      left
      rw [hloc, Function.update_self]
      have := hidle hpend
      cases o <;> simp [oweR, this]
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret h
      left
      rw [hloc, Function.update_self]
      rcases hl : C.loc q with ⟨n, pc⟩
      rw [hl] at hact
      cases pc with
      | up a ptr => cases a <;> simp [Snapshot.act] at hact
      | idle | ackU | retS _ => simp only [Snapshot.act] at hact; cases hact; simp [oweR]
      | _ => simp [Snapshot.act] at hact
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, i, o, kk, hact, -, hloc⟩ := Impl.step_tau h
      rw [hloc, Function.update_self]
      rcases hl : C.loc q with ⟨n, pc⟩
      rw [hl] at hact
      cases pc with
      | idle | ackU | retS _ => simp [Snapshot.act] at hact
      | lw v =>
        simp only [Snapshot.act] at hact; cases hact
        left; dsimp only; rw [oweR_cont]; simp [oweR]
      | up a' ptr =>
        rcases a' with _ | ⟨b, p⟩
        · simp only [Snapshot.act] at hact; cases hact
          right; exact ⟨rfl, rfl, ptr, Or.inl rfl⟩
        · simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
      | sc p => simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
      | rl p x y => simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
      | rr p x y lv => simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
      | wv p k val =>
        simp only [Snapshot.act] at hact; cases hact
        left; dsimp only; rw [oweR_cont]; simp [oweR]
      | wm d =>
        simp only [Snapshot.act] at hact; cases hact
        right; exact ⟨rfl, rfl, d, Or.inr rfl⟩
      | s0 => simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
      | s1 c => simp only [Snapshot.act] at hact; cases hact; left; simp [oweR]
  · left; rw [(Impl.step_other h hq).1]

/-! ### The invariant -/

omit [DecidableEq P] in
lemma sub_parent {b : Bool} {p : List Bool} {c : BTree P} (hc : T.sub (b :: p) = some c) :
    ∃ l r, T.sub p = some (.node l r) ∧ c = (if b then r else l) := by
  simp only [BTree.sub_cons] at hc
  cases hp : T.sub p with
  | none => simp [hp] at hc
  | some u =>
    simp only [hp, Option.bind_some] at hc
    cases u with
    | leaf q => simp [BTree.child] at hc
    | node l r =>
      refine ⟨l, r, rfl, ?_⟩
      cases b <;> simp [BTree.child] at hc <;> simp [hc]

lemma seq_side {M : Mem v₀} {c : P → ℕ} {R : List Bool → Set (ℕ × ℕ)} {L : Snapshot.Lin v₀}
    {s₀ : P → ℕ} (hG : GInv T M c R L s₀) {b : Bool} {p : List Bool} {t : BTree P}
    (hc : T.sub (b :: p) = some t) : ∃ s, SeqR R c t (b :: p) (side b (M (.ma p))) s := by
  obtain ⟨l, r, hsubp, rfl⟩ := sub_parent hc
  obtain ⟨⟨s₁, h₁, -⟩, ⟨s₂, h₂, -⟩⟩ := hG.reach p l r hsubp _ _ (hG.cur p)
  cases b
  · exact ⟨s₁, h₁⟩
  · exact ⟨s₂, h₂⟩

/-- **The reporting invariant.** For the current value `x` of side `b` of the max array of the
node `p` (child `c`) and every process `j` below `c`, the vector `seq[x]` of leaf pointers covers
all `Update`s of `j` except possibly the current one, and also the current one once `j` has
reported `c` to `p`. Similarly for `root.MR`. -/
structure RepInv (T : BTree P) (C : Cfg v₀) (R : List Bool → Set (ℕ × ℕ)) : Prop where
  ma : ∀ p b c, T.sub (b :: p) = some c → ∀ s,
    SeqR R (cntOf C) c (b :: p) (side b (C.mem (.ma p))) s →
    ∀ j ∈ c.leaves, (C.loc j).cnt ≤ s j + owe (b :: p) (C.loc j)
  mr : ∀ s, SeqR R (cntOf C) T [] (C.mem .mr) s →
    ∀ j ∈ T.leaves, (C.loc j).cnt ≤ s j + oweR (C.loc j)

lemma repInv_init (R : List Bool → Set (ℕ × ℕ)) : RepInv T (alg3 T v₀).initCfg R :=
  ⟨fun _ _ _ _ _ _ _ _ => Nat.zero_le _, fun _ _ _ _ => Nat.zero_le _⟩

lemma repInv_step (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀}
    {R R' : List Bool → Set (ℕ × ℕ)} {L L' : Snapshot.Lin v₀} {s₀ s₀' : P → ℕ}
    {ℓ : Label P (swSnap P V v₀)} (hI : Inv T α C R L s₀) (hR : RepInv T C R)
    (h : (alg3 T v₀).step C ℓ = some C') (hI' : Inv T (α ++ [ℓ]) C' R' L' s₀')
    (hRR : ∀ a, R a ⊆ R' a) : RepInv T C' R' := by
  have hcnt := Snapshot.step_cnt_mono h
  have hch := hI'.g.chain
  have hidle : ∀ j, C.pend j = none → (C.loc j).pc = .idle := fun j hj =>
    (hj ▸ hI.proc j).pc_idle
  constructor
  · intro p b c hc s' hs' j hj
    obtain ⟨s, hs⟩ := seq_side hI.g hc
    have hmv := mval_step h (some (p, b))
    simp only [mval] at hmv
    have hmono : side b (C.mem (.ma p)) ≤ side b (C'.mem (.ma p)) := by
      rw [hmv]; exact le_max_left _ _
    have hle : s ≤ s' := SeqR.le hch (SeqR.mono hRR hcnt hs) hs' hmono
    have hold := hR.ma p b c hc s hs j hj
    have hsuf := BTree.suffix_path_of_sub hT.nodup hc hj
    rcases owe_step h (hidle j) (List.cons_ne_nil b p) hsuf with h1 | ⟨rfl, hc', ptr, hpc⟩
    · have : s j ≤ s' j := hle j; omega
    · have hP := hI.proc j
      unfold PInv at hP; rw [hpc] at hP
      obtain ⟨-, -, -, t, hsubt, sp, hsp, hspj, -⟩ := hP
      obtain rfl : t = c := by rw [hc] at hsubt; exact (Option.some.inj hsubt).symm
      have hptr : ptr ≤ side b (C'.mem (.ma p)) := by
        rw [hmv]; simp [stepLog, wm3, hpc, selK]
      have : sp j ≤ s' j := SeqR.le hch (SeqR.mono hRR hcnt hsp) hs' hptr j
      rw [hc']; omega
  · intro s' hs' j hj
    have hs := hI.g.root.1
    have hmv := mval_step h none
    simp only [mval] at hmv
    have hmono : C.mem .mr ≤ C'.mem .mr := by rw [hmv]; exact le_max_left _ _
    have hle := SeqR.le hch (SeqR.mono hRR hcnt hs) hs' hmono
    have hold := hR.mr _ hs j hj
    rcases oweR_step h (hidle j) with h1 | ⟨rfl, hc', d, hpc | hpc⟩
    · have : s₀ j ≤ s' j := hle j; omega
    · have hP := hI.proc j
      unfold PInv at hP; rw [hpc] at hP
      exact absurd rfl hP.2.1
    · have hP := hI.proc j
      unfold PInv at hP; rw [hpc] at hP
      obtain ⟨-, sp, hsp, hspj, -⟩ := hP
      have hptr : d ≤ C'.mem .mr := by
        rw [hmv]; simp [stepLog, wm3, hpc, selK]
      have : sp j ≤ s' j := SeqR.le hch (SeqR.mono hRR hcnt hsp) hs' hptr j
      rw [hc']; omega

/-- The invariant of Theorem 4.2 of [AACE] together with the reporting invariant holds in every
reachable configuration. -/
theorem exists_repInv (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) : ∃ R L s₀, Inv T α C R L s₀ ∧ RepInv T C R :=
  Impl.run_induction (Q := fun α C => ∃ R L s₀, Inv T α C R L s₀ ∧ RepInv T C R)
    ⟨Snapshot.R₀, [], 0, Snapshot.inv_init, repInv_init _⟩
    (fun _ _ _ _ hα ⟨_, _, _, hI, hR⟩ hs =>
      let ⟨R', L', s₀', hI', hRR⟩ := Snapshot.inv_step hT hα hI hs
      ⟨R', L', s₀', hI', repInv_step hT hI hR hs hI' hRR⟩) h

/-! ### Every write is at most the current value plus the number of leaves -/

/-- The paper's claims (1) and (2) combined: a `MaxUpdate(ptr)` on side `b` of the max array of
the node `p`, whose child `c` on that side has `|leaves c|` leaves, satisfies
`ptr ≤ x + |leaves c|` where `x` is the current value of that side. -/
theorem maxUpdate_le (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) {i : P} {p : List Bool} {b : Bool} {c : BTree P}
    {ptr : ℕ} (hc : T.sub (b :: p) = some c) (hpc : (C.loc i).pc = .up (b :: p) ptr) :
    ptr ≤ side b (C.mem (.ma p)) + c.leaves.length := by
  obtain ⟨R, L, s₀, hI, hR⟩ := exists_repInv hT h
  have hP := hI.proc i
  unfold PInv at hP; rw [hpc] at hP
  obtain ⟨-, -, -, t, hsubt, sp, hsp, -, -⟩ := hP
  obtain rfl : t = c := by rw [hc] at hsubt; exact (Option.some.inj hsubt).symm
  obtain ⟨s, hs⟩ := seq_side hI.g hc
  have hnd := BTree.nodup_of_sub hc hT.nodup
  rw [← SeqR.sum hnd hsp, ← SeqR.sum hnd hs]
  have h1 : ∀ j ∈ t.leaves, sp j ≤ s j + 1 := fun j hj =>
    (Snapshot.seq_le_cnt hT hc hsp j).trans ((hR.ma p b t hc s hs j hj).trans
      (by have := owe_le_one (b :: p) (C.loc j); omega))
  calc (t.leaves.map sp).sum ≤ (t.leaves.map (fun j => s j + 1)).sum :=
        List.sum_le_sum (fun j hj => h1 j hj)
    _ = (t.leaves.map s).sum + t.leaves.length := by simp [List.sum_map_add]

/-- The same for `WriteMax(root.MR, d)`: `d ≤ x + n` where `x` is the current value of
`root.MR` and `n` the number of processes. -/
theorem writeMax_le (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) {i : P} {d : ℕ}
    (hpc : (C.loc i).pc = .up [] d ∨ (C.loc i).pc = .wm d) :
    d ≤ C.mem .mr + T.leaves.length := by
  obtain ⟨R, L, s₀, hI, hR⟩ := exists_repInv hT h
  have hP := hI.proc i
  rcases hpc with hpc | hpc
  · unfold PInv at hP; rw [hpc] at hP; exact absurd rfl hP.2.1
  unfold PInv at hP; rw [hpc] at hP
  obtain ⟨-, sp, hsp, -, -⟩ := hP
  have hs := hI.g.root.1
  rw [← SeqR.sum hT.nodup hsp, ← SeqR.sum hT.nodup hs]
  have h1 : ∀ j ∈ T.leaves, sp j ≤ s₀ j + 1 := fun j hj =>
    (Snapshot.seq_le_cnt_root hT hsp j).trans ((hR.mr s₀ hs j hj).trans
      (by have := oweR_le_one (C.loc j); omega))
  calc (T.leaves.map sp).sum ≤ (T.leaves.map (fun j => s₀ j + 1)).sum :=
        List.sum_le_sum (fun j hj => h1 j hj)
    _ = (T.leaves.map s₀).sum + T.leaves.length := by simp [List.sum_map_add]

/-! ### Lemmas 4.1 and 4.2 -/

/-- **Lemma 4.1 of [BHMT20]**, first part: only the processes whose leaf is below the node at
address `p` access its max array `p.MA`. -/
theorem lemma_4_1_access (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) {i : P} {p : List Bool}
    {o : (Snapshot.objSpec P V v₀ (.ma p)).Op}
    {k : (Snapshot.objSpec P V v₀ (.ma p)).Resp → Snapshot.Loc P V}
    (hact : Snapshot.act T v₀ i (C.loc i) = .access (.ma p) o k) : i ∈ T.leavesAt p := by
  obtain ⟨R, L, s₀, hI⟩ := Snapshot.exists_inv hT h
  have hP := hI.proc i
  have hsuf : p <:+ T.path i := by
    rcases hl : C.loc i with ⟨n, pc⟩
    rw [hl] at hact hP
    unfold PInv at hP
    cases pc with
    | up a ptr =>
      rcases a with _ | ⟨b, q⟩
      · simp [Snapshot.act] at hact
      · simp only [Snapshot.act] at hact
        cases hact
        exact (List.suffix_cons _ _).trans hP.2.2.1
    | sc q =>
      simp only [Snapshot.act] at hact
      cases hact
      exact hP.2.1
    | _ => simp [Snapshot.act] at hact
  obtain ⟨u, hu, hiu⟩ := BTree.sub_of_suffix_path (hT.mem i) hsuf
  rw [BTree.leavesAt_of_sub hu]; exact hiu

/-- **Lemma 4.1 of [BHMT20]** (for an arbitrary tree; second part): in every execution of
Algorithm 2, the values written by `MaxUpdate` to side `b` of the max array of the node at
address `p` are `|leaves c|`-bounded-increment (Definition 2.1), where `c` is the child of that
node on side `b`. For the balanced tree and a node of height `h`, `|leaves c| = 2^{h-1}`. -/
theorem lemma_4_1 (hT : T.WF) {p : List Bool} {b : Bool} {c : BTree P}
    (hc : T.sub (b :: p) = some c) (α : List (Label P (swSnap P V v₀))) :
    BoundedIncr c.leaves.length (writesTo (alg3 T v₀) wm3 α (some (p, b))) :=
  boundedIncr_of_stepBounded <| writesTo_stepBounded (alg3 T v₀) wm3 (some (p, b))
    (fun C => mval C.mem (some (p, b))) _ (by cases b <;> rfl)
    (fun _ _ _ _ _ hs => mval_step hs _)
    (fun _ _ _ _ _ hα _ hw => maxUpdate_le hT hα hc (wm3_eq_some_some hw)) α

/-- **Lemma 4.2 of [BHMT20]** (for an arbitrary tree): in every execution of Algorithm 2, the
values written to `root.MR` are `n`-bounded-increment (Definition 2.1), `n` the number of
processes. -/
theorem lemma_4_2 (hT : T.WF) (α : List (Label P (swSnap P V v₀))) :
    BoundedIncr T.leaves.length (writesTo (alg3 T v₀) wm3 α none) :=
  boundedIncr_of_stepBounded <| writesTo_stepBounded (alg3 T v₀) wm3 none
    (fun C => mval C.mem none) _ rfl
    (fun _ _ _ _ _ hs => mval_step hs _)
    (fun _ _ _ _ _ hα _ hw => writeMax_le hT hα (wm3_eq_some_none hw)) α

end Podc.LongLivedSnapshotsPolylog.Section4
