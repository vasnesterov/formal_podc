import Papers.PODC2011.RobustAtomicStorage.Label
import Papers.PODC2011.RobustAtomicStorage.Blocks

/-!
# Lemma 1: the write lower bound (§4), block form

The objects are partitioned into the blocks `B₀, …, B_{k+1}`, `C₁, …, C_k` (`Blocks.lean`); the
hypothesis `Fits k t blk` bounds every set of objects that is malicious in a run, or skipped by a
terminated round, by `t`. Writes take `k ≥ 1` rounds, reads three rounds; read `l` (`1 ≤ l ≤ k`) is
performed by reader `rd l` (instance `ri l`, one read per reader, `instN`).

Read `l`: rounds 1, 2 skip `M_{l-2} ∪ P_{l+1}` (`H12 l` is the set they hear); round 1 reaches
`P_l` already in `prinit` (`pinit`, `rdInit`) and the rest `R1 l` later; round 3 skips
`M_{l-2} ∪ 𝒞_{l+1}` (`l < k`) or `M_{k-2} ∪ P_{k+1}` (`l = k`) and is delivered in two batches,
`Q3a l` (objects that processed rounds 1, 2) and `Q3b l = P_{l+1}` (three pending messages). The
phases are `inc2` (round 1 terminated, round 2 reaches `𝒞_j`), `inc3` (rounds 1, 2 terminated,
round 3 reaches `Q3a`), `full` (complete read); before round 1 of read `j` the malicious objects
of `B_{j-1}`, `C_{j-1}` forge `σ^r_{j-1}` (`hook`). The partial write `wr^{k-i}` (`wrP i`) reaches
`B₀` and the `B_j` with `j ≢ i (mod 2)` in its last round (`wc i X` write rounds at block `X`).

Correspondence with the runs of the paper (all are label runs, checked canonical by `cexec`):
* `prC_one` = `pr_1^C`: `prinit` with read 1 replaced by the forging of `P_1`, the complete
  write, then read 1, where `P_1` forges its `prinit` state, receives round 1 and forges `σ*`
  (`rdStart`); malicious set `P_1`. Read 1 succeeds the write, so it returns `v₁`.
* `prC_succ l` = `pr_l^C` (`2 ≤ l ≤ k`): `prinit` with read `l` replaced by forging, `wr^{k-l+1}`,
  reads `1..l-3` incomplete (`inc2`), read `l-2` incomplete (`inc3`), read `l-1` complete, read `l`
  complete (started by `rdStart`); malicious set `M_{l-3} ∪ P_l` (`FC l`). Read `l` succeeds read
  `l-1`, so it returns `v₁` if read `l-1` does.
* `dpr` = `Δpr_k`: `prinit`, no write, reads `1..k-1` incomplete (`inc2`), read `k` complete;
  malicious set `M_{k-1}`. There is no write, so read `k` returns `⊥`.

The paper's `pr_l` and `Δpr_l` for `l < k` are not needed: every read `l` sees the canonical
transcript `T (ri l, ·)` in each run where it occurs, so it returns the same value `cv l` in all
of them (`Sim.lean`). `refLog L X` is the state of block `X` (of index `≥ L`) at the end of the
paper's `Δpr_L`, i.e. `σ^r_L` (and `σ*_{k-L-1}` for the blocks of `P_{L+1}`); `pre`, `cr` are the
labels of `prinit` and of the incomplete reads. The closed forms of the logs are `sJ` (after the
incomplete reads `1..J`), `refLog_next` (after a read with three rounds) and `refLog_zero`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RobustAtomicStorage.WriteLB

open Classical Blk

variable {Obj Rd V : Type} [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]

section Defs

variable (k : ℕ) (os : List Obj) (blk : Obj → Blk) (rd : ℕ → Rd)

/-- The client performing read `l`. -/
def rc (l : ℕ) : Cl Rd := .r (rd l)

/-- The instance of read `l`. -/
def ri (l : ℕ) : Inst Rd := (rc rd l, l)

/-- The writer's instance. -/
def wi : Inst Rd := (.w, 0)

/-- Label of round `q` of read `m` in a log (absent for `m = 0`). -/
def rl (m q : ℕ) : List (Cl Rd × Lab (Inst Rd)) :=
  if 1 ≤ m then [(rc rd m, (ri rd m, q))] else []

/-- Log of an object after the first `m` write rounds. -/
def W (m : ℕ) : List (Cl Rd × Lab (Inst Rd)) :=
  (List.range m).map fun p => (.w, (wi, p + 1))

/-- Labels of the first rounds of reads `1..n` that reach the block `X` in `prinit`
(read `m` reaches `P_m`). -/
def pre (n : ℕ) (X : Blk) : List (Cl Rd × Lab (Inst Rd)) :=
  (List.range n).flatMap fun m => if P k (m + 1) X then rl rd (m + 1) 1 else []

/-- Labels of the first two rounds of the reads `1..L`. -/
def cr (L : ℕ) : List (Cl Rd × Lab (Inst Rd)) :=
  (List.range L).flatMap fun j => rl rd (j + 1) 1 ++ rl rd (j + 1) 2

/-- `B` blocks (the blocks written to). -/
def isB : Blk → Prop
  | B _ => True
  | C _ => False

instance (X : Blk) : Decidable (isB X) := by cases X <;> unfold isB <;> infer_instance

/-- Blocks reached by round `k - i + 1` of the partial write `wr^{k-i}`: `B₀` and the `B_j`
with `j ≢ i (mod 2)`. -/
def wl (i : ℕ) : Blk → Prop
  | B j => j = 0 ∨ j % 2 ≠ i % 2
  | C _ => False

instance (i : ℕ) (X : Blk) : Decidable (wl i X) := by cases X <;> unfold wl <;> infer_instance

/-- Number of write rounds received by block `X` in `wr^{k-i}`. -/
def wc (i : ℕ) : Blk → ℕ
  | B j => if j = 0 then k - i + 1 else if j % 2 = i % 2 then k - i else k - i + 1
  | C _ => 0

/-- Log of the objects of block `X` (of index `≥ L`) at the end of the paper's `Δpr_L`, i.e.
when read `L + 1` starts (`σ*`, `σ^r_L` of the paper). -/
def refLog (L : ℕ) : Blk → List (Cl Rd × Lab (Inst Rd))
  | B m => pre k rd k (B m) ++ W (wc k (L + 1) (B m)) ++
      (if m % 2 = L % 2 then rl rd L 2 ++ rl rd L 3 else [])
  | C m => cr rd L ++ (if m = L then rl rd L 3 else [])

/-- Log of block `X` after round 1 of read `l`. -/
def aft1 (l : ℕ) (X : Blk) : List (Cl Rd × Lab (Inst Rd)) :=
  refLog k rd (l - 1) X ++ (if P k l X then [] else rl rd l 1)

/-- Blocks heard by rounds 1 and 2 of read `l` (it skips `M_{l-2} ∪ P_{l+1}`). -/
def H12 (l : ℕ) (X : Blk) : Prop := ¬ (Mlt (l - 1) X ∨ P k (l + 1) X)

/-- Blocks reached by round 1 of read `l` outside of `prinit`. -/
def R1 (l : ℕ) (X : Blk) : Prop := H12 k l X ∧ ¬ P k l X

/-- Blocks reached by round 3 of read `l` that already processed rounds 1 and 2. -/
def Q3a (l : ℕ) (X : Blk) : Prop := ¬ Mlt (l - 1) X ∧ ¬ CC k (l + 1) X ∧ ¬ P k (l + 1) X

/-- Blocks reached by round 3 of read `l < k` with three pending messages (`P_{l+1}`). -/
def Q3b (l : ℕ) (X : Blk) : Prop := ¬ Mlt (l - 1) X ∧ P k (l + 1) X ∧ l < k

/-- Blocks `B_m`, `C_m`. -/
def Idx (m : ℕ) (X : Blk) : Prop := X = B m ∨ X = C m

instance (l : ℕ) (X : Blk) : Decidable (H12 k l X) := by unfold H12; infer_instance
instance (l : ℕ) (X : Blk) : Decidable (R1 k l X) := by unfold R1; infer_instance
instance (l : ℕ) (X : Blk) : Decidable (Q3a k l X) := by unfold Q3a; infer_instance
instance (l : ℕ) (X : Blk) : Decidable (Q3b k l X) := by unfold Q3b; infer_instance
instance (m : ℕ) (X : Blk) : Decidable (Idx m X) := by unfold Idx; infer_instance

/-- Objects of the blocks satisfying `p`, in the order of `os`. -/
def objs (p : Blk → Prop) [DecidablePred p] : List Obj := os.filter fun s => p (blk s)

/-- Replies of an object of `P_{l+1}` to round 3 of read `l` (three pending messages). -/
def ents3 (l : ℕ) (s : Obj) : View Obj (LRep Rd (Inst Rd)) :=
  [(s, ((ri rd l, 1), refLog k rd (l - 1) (blk s))),
   (s, ((ri rd l, 2), refLog k rd (l - 1) (blk s) ++ rl rd l 1)),
   (s, ((ri rd l, 3), refLog k rd (l - 1) (blk s) ++ rl rd l 1 ++ rl rd l 2))]

/-- The canonical transcripts. -/
def T : Lab (Inst Rd) → View Obj (LRep Rd (Inst Rd))
  | ((.w, 0), q) => (objs os blk isB).map fun s => (s, ((wi, q), pre k rd k (blk s) ++ W (q - 1)))
  | ((.r _, l), 1) =>
    if 1 ≤ l then
      (objs os blk (P k l)).map (fun s => (s, ((ri rd l, 1), pre k rd (l - 1) (blk s)))) ++
      (objs os blk (R1 k l)).map (fun s => (s, ((ri rd l, 1), refLog k rd (l - 1) (blk s))))
    else []
  | ((.r _, l), 2) =>
    if 1 ≤ l then (objs os blk (H12 k l)).map fun s => (s, ((ri rd l, 2), aft1 k rd l (blk s)))
    else []
  | ((.r _, l), 3) =>
    if 1 ≤ l then
      (objs os blk (Q3a k l)).map (fun s => (s, ((ri rd l, 3), aft1 k rd l (blk s) ++ rl rd l 2))) ++
      (objs os blk (Q3b k l)).flatMap (ents3 k blk rd l)
    else []
  | _ => []

/-- Rank of labels: first rounds `0`; the writer's rounds before all reads; reads in
increasing order. -/
def rank (lab : Lab (Inst Rd)) : ℕ := if lab.2 ≤ 1 then 0 else lab.1.2 * (k + 4) + lab.2

end Defs

section Rank

variable (k : ℕ) (os : List Obj) (blk : Obj → Blk) (rd : ℕ → Rd)

lemma rank_W {m : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (W m).map Prod.snd) : rank k l ≤ m := by
  simp only [W, List.map_map, List.mem_map, List.mem_range, Function.comp] at h
  obtain ⟨p, hp, rfl⟩ := h
  simp only [rank, wi]; (try split_ifs) <;> omega

lemma rank_rl {m q : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (rl rd m q).map Prod.snd) :
    rank k l ≤ m * (k + 4) + q := by
  simp only [rl] at h
  split_ifs at h
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    subst h; simp only [rank, ri]; split_ifs <;> omega
  · simp at h

lemma rank_rl1 {m : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (rl rd m 1).map Prod.snd) : rank k l = 0 := by
  simp only [rl] at h
  split_ifs at h
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    subst h; simp [rank]
  · simp at h

lemma rank_pre {n : ℕ} {X : Blk} {l : Lab (Inst Rd)} (h : l ∈ (pre k rd n X).map Prod.snd) :
    rank k l = 0 := by
  simp only [pre, List.map_flatMap, List.mem_flatMap, List.mem_range] at h
  obtain ⟨m, -, h⟩ := h
  split_ifs at h
  · exact rank_rl1 k rd h
  · simp at h

lemma rank_cr {L : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (cr rd L).map Prod.snd) :
    rank k l ≤ L * (k + 4) + 2 := by
  simp only [cr, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_append,
    List.mem_append] at h
  obtain ⟨j, hj, h | h⟩ := h
  · rw [rank_rl1 k rd h]; omega
  · have := rank_rl k rd h
    have : (j + 1) * (k + 4) ≤ L * (k + 4) := Nat.mul_le_mul_right _ (by omega)
    omega

lemma wc_le (i : ℕ) (X : Blk) : wc k i X ≤ k + 1 := by
  cases X <;> simp only [wc] <;> (try split_ifs) <;> omega

lemma rank_refLog {L : ℕ} (X : Blk) {l : Lab (Inst Rd)} (h : l ∈ (refLog k rd L X).map Prod.snd) :
    rank k l ≤ L * (k + 4) + k + 4 := by
  cases X with
  | B m =>
    simp only [refLog, List.map_append, List.mem_append] at h
    rcases h with (h | h) | h
    · rw [rank_pre k rd h]; omega
    · have := rank_W k h; have := wc_le k (L + 1) (B m); omega
    · split_ifs at h
      · simp only [List.map_append, List.mem_append] at h
        rcases h with h | h <;> (have := rank_rl k rd h; omega)
      · simp at h
  | C m =>
    simp only [refLog, List.map_append, List.mem_append] at h
    rcases h with h | h
    · have := rank_cr k rd h; omega
    · split_ifs at h
      · have := rank_rl k rd h; omega
      · simp at h

lemma rank_refLog' {l' : ℕ} (hl : 1 ≤ l') (X : Blk) {l : Lab (Inst Rd)}
    (h : l ∈ (refLog k rd (l' - 1) X).map Prod.snd) : rank k l ≤ l' * (k + 4) := by
  have := rank_refLog k rd X h
  have : (l' - 1) * (k + 4) + k + 4 = l' * (k + 4) := by
    obtain ⟨n, rfl⟩ : ∃ n, l' = n + 1 := ⟨l' - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  omega

lemma labs_T (i : Inst Rd) (p : ℕ) (l : Lab (Inst Rd)) (hl : l ∈ labsV (T k os blk rd (i, p))) :
    rank k l ≤ i.2 * (k + 4) + p := by
  obtain ⟨c, n⟩ := i
  simp only [labsV, List.mem_flatMap] at hl
  obtain ⟨e, he, hl⟩ := hl
  rcases c with _ | x
  · rcases n with _ | n
    · simp only [T, List.mem_map] at he
      obtain ⟨s, -, rfl⟩ := he
      simp only [List.mem_cons, List.map_append, List.mem_append] at hl
      rcases hl with rfl | hl | hl
      · simp only [rank, wi]; split_ifs <;> omega
      · rw [rank_pre k rd hl]; omega
      · have := rank_W k hl; simp only at this ⊢; omega
    · simp [T] at he
  · rcases p with _ | _ | _ | _ | p
    · simp [T] at he
    · simp only [T] at he
      split_ifs at he with hn
      · simp only [List.mem_append, List.mem_map] at he
        rcases he with ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ <;> simp only [List.mem_cons] at hl <;>
          rcases hl with rfl | hl
        · simp [rank]
        · rw [rank_pre k rd hl]; omega
        · simp [rank]
        · have := rank_refLog' k rd hn _ hl; simp only at this ⊢; omega
      · simp at he
    · simp only [T] at he
      split_ifs at he with hn
      · simp only [List.mem_map] at he
        obtain ⟨s, -, rfl⟩ := he
        simp only [List.mem_cons, aft1, List.map_append, List.mem_append] at hl
        rcases hl with rfl | hl | hl
        · simp [rank, ri]
        · have := rank_refLog' k rd hn _ hl; simp only at this ⊢; omega
        · split_ifs at hl
          · simp at hl
          · rw [rank_rl1 k rd hl]; omega
      · simp at he
    · simp only [T] at he
      split_ifs at he with hn
      · have hR : ∀ l, l ∈ (refLog k rd (n - 1) (blk e.1)).map Prod.snd →
            rank k l ≤ n * (k + 4) + 3 := fun l hl => (rank_refLog' k rd hn _ hl).trans (by omega)
        have h1 : ∀ l, l ∈ (rl rd n 1).map Prod.snd → rank k l ≤ n * (k + 4) + 3 :=
          fun l hl => by rw [rank_rl1 k rd hl]; omega
        have h2 : ∀ l, l ∈ (rl rd n 2).map Prod.snd → rank k l ≤ n * (k + 4) + 3 :=
          fun l hl => (rank_rl k rd hl).trans (by omega)
        simp only [List.mem_append, List.mem_map, List.mem_flatMap] at he
        rcases he with ⟨s, -, rfl⟩ | ⟨s, -, he⟩
        · simp only [List.mem_cons, aft1, List.map_append, List.mem_append] at hl
          rcases hl with rfl | ((hl | hl) | hl)
          · simp [rank, ri]
          · exact hR _ hl
          · split_ifs at hl
            · simp at hl
            · exact h1 _ hl
          · exact h2 _ hl
        · simp only [ents3, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl <;>
          simp only [List.mem_cons, List.map_append, List.mem_append] at hl <;>
          rcases hl with rfl | hl
          · simp [rank]
          · exact hR _ hl
          · simp [rank, ri]
          · rcases hl with hl | hl
            · exact hR _ hl
            · exact h1 _ hl
          · simp [rank, ri]
          · rcases hl with (hl | hl) | hl
            · exact hR _ hl
            · exact h1 _ hl
            · exact h2 _ hl
      · simp at he
    · simp [T] at he

theorem rank_ok (i : Inst Rd) (q p : ℕ) (hpq : p + 1 < q) (l : Lab (Inst Rd))
    (hl : l ∈ labsV (T k os blk rd (i, p + 1))) : rank k l < rank k (i, q) := by
  have := labs_T k os blk rd i (p + 1) l hl
  have h2 : rank k (i, q) = i.2 * (k + 4) + q := by simp only [rank]; split_ifs <;> omega
  omega

end Rank

section Runs

variable (k : ℕ) (os : List Obj) (blk : Obj → Blk) (rd : ℕ → Rd) (v₁ bot : V) (t : ℕ)
  (F : Finset Obj) (inst : Cl Rd → Inst Rd)

omit [Fintype Obj] [DecidableEq V] in
lemma mem_objs (hall : ∀ s, s ∈ os) (p : Blk → Prop) [DecidablePred p] (s : Obj) :
    s ∈ objs os blk p ↔ p (blk s) := by
  simp [objs, hall s]

omit [Fintype Obj] [DecidableEq V] in
lemma nodup_objs (hos : os.Nodup) (p : Blk → Prop) [DecidablePred p] : (objs os blk p).Nodup :=
  hos.filter _

lemma W_succ (m : ℕ) : (W m : List (Cl Rd × Lab (Inst Rd))) ++ [(.w, (wi, m + 1))] = W (m + 1) := by
  simp [W, List.range_succ]

lemma rl_pos {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    (rl rd m q : List (Cl Rd × Lab (Inst Rd))) = [(rc rd m, (ri rd m, q))] := by
  simp [rl, hm]

lemma rl_zero (q : ℕ) : (rl rd 0 q : List (Cl Rd × Lab (Inst Rd))) = [] := by simp [rl]

lemma pre_succ (n : ℕ) (X : Blk) :
    pre k rd (n + 1) X = pre k rd n X ++ (if P k (n + 1) X then rl rd (n + 1) 1 else []) := by
  simp [pre, List.range_succ]

lemma pre_C (n m : ℕ) : pre k rd n (C m) = [] := by simp [pre, P]

lemma cr_succ (L : ℕ) : cr rd (L + 1) = cr rd L ++ rl rd (L + 1) 1 ++ rl rd (L + 1) 2 := by
  simp [cr, List.range_succ]

/-- Enough responders, via a block predicate. -/
lemma card_le (p : Obj → Prop) [DecidablePred p] (q : Blk → Prop) [DecidablePred q]
    (h : ∀ s, p s → q (blk s)) (hq : nBlk blk q ≤ t) : (Finset.univ.filter p).card ≤ t := by
  unfold nBlk at hq
  refine le_trans (Finset.card_le_card fun s hs => ?_) hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact h s hs

/-- The checked execution used throughout this file (`K = k` write rounds, `N = 3` read
rounds). -/
noncomputable abbrev cx := cexec k 3 (T k os blk rd) v₁ bot inst t F

/-! ### Local states of clients -/

/-- The local state of client `c`. -/
def cst (C : LCfg Obj Rd V (Inst Rd)) (c : Cl Rd) :
    ℕ × List (View Obj (LRep Rd (Inst Rd))) × View Obj (LRep Rd (Inst Rd)) × Bool × (Obj → ℕ) :=
  (C.rnd c, C.past c, C.cur c, C.done c, fun s => C.prc s c)

lemma cst_dlvRes {C : LCfg Obj Rd V (Inst Rd)} {c c' : Cl Rd} (h : c' ≠ c) (xs : List Obj)
    (d : Obj → ℕ) : cst (dlvRes inst C c xs d) c' = cst C c' := by
  simp [cst, dlvRes, h]

lemma cst_nxtRes {C : LCfg Obj Rd V (Inst Rd)} {c c' : Cl Rd} (h : c' ≠ c) (r : ℕ) :
    cst (nxtRes C c r) c' = cst C c' := by
  unfold nxtRes; split_ifs <;> simp [cst, h]

lemma cst_invR {C : LCfg Obj Rd V (Inst Rd)} {c : Cl Rd} {j : Rd} (h : c ≠ .r j) :
    cst { C with rnd := Function.update C.rnd (.r j) 1 } c = cst C c := by
  simp [cst, h]

lemma cst_invW {C : LCfg Obj Rd V (Inst Rd)} {c : Cl Rd} (h : c ≠ .w) (v : V) :
    cst { C with rnd := Function.update C.rnd .w 1, wv := v } c = cst C c := by
  simp [cst, h]

lemma cst_eq {C C' : LCfg Obj Rd V (Inst Rd)} {c : Cl Rd} (h : cst C' c = cst C c) :
    C'.rnd c = C.rnd c ∧ C'.past c = C.past c ∧ C'.cur c = C.cur c ∧ C'.done c = C.done c ∧
      ∀ s, C'.prc s c = C.prc s c := by
  simp only [cst, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun s => congrFun h.2.2.2.2 s⟩

lemma fresh_of_cst {C C' : LCfg Obj Rd V (Inst Rd)} {c : Cl Rd} (h : cst C' c = cst C c)
    (hf : Fresh C c) : Fresh C' c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cst_eq h
  obtain ⟨f1, f2, f3, f4, f5⟩ := hf
  exact ⟨h1.trans f1, h2.trans f2, h3.trans f3, h4.trans f4, fun s => (h5 s).trans (f5 s)⟩

/-- Read `l` has been invoked and its first round reached exactly `P_l` (as in `prinit`). -/
def Started (C : LCfg Obj Rd V (Inst Rd)) (l : ℕ) : Prop :=
  C.rnd (rc rd l) = 1 ∧ C.past (rc rd l) = [] ∧
    C.cur (rc rd l) = (objs os blk (P k l)).map
      (fun s => (s, ((ri rd l, 1), pre k rd (l - 1) (blk s)))) ∧
    C.done (rc rd l) = false ∧ ∀ s, C.prc s (rc rd l) = if P k l (blk s) then 1 else 0

lemma started_of_cst {C C' : LCfg Obj Rd V (Inst Rd)} {l : ℕ}
    (h : cst C' (rc rd l) = cst C (rc rd l)) (hs : Started k os blk rd C l) :
    Started k os blk rd C' l := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cst_eq h
  obtain ⟨f1, f2, f3, f4, f5⟩ := hs
  exact ⟨h1.trans f1, h2.trans f2, h3.trans f3, h4.trans f4, fun s => (h5 s).trans (f5 s)⟩

/-! ### `prinit`: the first rounds of all reads -/

/-- Invocation of read `l` and delivery of its first round to `P_l`. -/
def rdInit (l : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invR (rd l)] ++ dlvs (rc rd l) (objs os blk (P k l)) (fun _ => 1)

theorem rdInit_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (l : ℕ) (hl : 1 ≤ l)
    (hinst : inst (rc rd l) = ri rd l) (C : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C (rc rd l))
    (hlog : ∀ s, P k l (blk s) → C.log s = pre k rd (l - 1) (blk s)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (rdInit k os blk rd l) = some (C', [.invR (rd l)]) ∧
      (∀ s, C'.log s = if P k l (blk s) then C.log s ++ rl rd l 1 else C.log s) ∧
      Started k os blk rd C' l ∧ (∀ c, c ≠ rc rd l → cst C' c = cst C c) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfr
  have hinst' : inst (rc rd l) = (rc rd l, l) := hinst
  have e1 := cexec_invR k 3 (T k os blk rd) v₁ bot inst t F C (rd l) f1
  set C1 := { C with rnd := Function.update C.rnd (Cl.r (rd l)) 1 } with hC1
  have g1 : C1.rnd (rc rd l) = 1 := by simp [hC1, rc]
  have e2 := cexec_dlvs k 3 (T k os blk rd) v₁ bot inst t F C1 (rc rd l) (objs os blk (P k l))
    (nodup_objs os blk hos _) (fun _ => 1) (fun s _ => by rw [g1]; simp [hC1, f5])
    (by rw [g1]; simp [hC1, f2])
  refine ⟨_, by dsimp only [cx]; rw [rdInit]; exact cexec_append_some k 3 _ v₁ bot inst t F e1 e2,
    ?_, ?_, ?_⟩
  · intro s
    by_cases h : P k l (blk s)
    · simp [dlvRes, mem_objs os blk hall, h, hC1, newLabs, f5, hinst', rl_pos rd hl, ri]
    · simp [dlvRes, mem_objs os blk hall, h, hC1]
  · refine ⟨by simp [dlvRes, hC1, rc], by simp [dlvRes, hC1]; exact f2, ?_, by simp [dlvRes, hC1, f4],
      fun s => ?_⟩
    · have : ∀ s ∈ objs os blk (P k l), ents inst C1 (rc rd l) s 1 =
          [(s, ((ri rd l, 1), pre k rd (l - 1) (blk s)))] := by
        intro s hs
        simp [ents, newLabs, hC1, f5, hinst', ri, hlog s ((mem_objs os blk hall _ s).1 hs)]
      simp only [dlvRes, Function.update_self, hC1]
      rw [show C.cur (rc rd l) = [] from f3, List.nil_append, List.flatMap_congr this,
        ← List.map_eq_flatMap]
    · by_cases h : P k l (blk s) <;> simp [dlvRes, mem_objs os blk hall, h, hC1, f5]
  · intro c hc
    rw [cst_dlvRes inst hc]
    exact cst_invR (by simpa [rc] using hc)

/-- Step `l` of `prinit`: read `l` is invoked and reaches `P_l`; if `l = l₀`, the read does
not occur and `P_l` forges the same state instead. -/
def pstep (l₀ l : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  if l = l₀ then forges (objs os blk (P k l)) (fun s => pre k rd l (blk s)) else rdInit k os blk rd l

/-- `prinit` (first `n` steps). -/
def pinit (l₀ n : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  (List.range n).flatMap fun m => pstep k os blk rd l₀ (m + 1)

/-- History of `prinit`. -/
def piH (l₀ n : ℕ) : List (HEv Rd V) :=
  (List.range n).flatMap fun m => if m + 1 = l₀ then [] else [.invR (rd (m + 1))]

/-- `rd` is injective on the readers `1..k`. -/
def RdInj : Prop := ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → rd i = rd j → i = j

lemma rc_ne (hrd : RdInj k rd) {i j : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (h : i ≠ j) : rc rd i ≠ rc rd j := by
  intro h'
  simp only [rc, Cl.r.injEq] at h'
  exact h (hrd i j hi hik hj hjk h')

theorem pinit_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hrd : RdInj k rd)
    (hinst : ∀ l, 1 ≤ l → l ≤ k → inst (rc rd l) = ri rd l) (l₀ : ℕ)
    (hF : 1 ≤ l₀ → ∀ s, P k l₀ (blk s) → s ∈ F) (n : ℕ) (hn : n ≤ k) :
    ∃ C, cx k os blk rd v₁ bot t F inst (Cfg.init bot) (pinit k os blk rd l₀ n) =
        some (C, piH rd l₀ n) ∧
      (∀ s, C.log s = pre k rd n (blk s)) ∧
      (∀ l, 1 ≤ l → l ≤ n → l ≠ l₀ → Started k os blk rd C l) ∧
      (∀ c, (∀ l, 1 ≤ l → l ≤ n → l ≠ l₀ → c ≠ rc rd l) → Fresh C c) := by
  induction n with
  | zero =>
    refine ⟨Cfg.init bot, by simp [pinit, piH, cexec_nil], fun s => by simp [pre, Cfg.init],
      fun l h1 h2 => by omega, fun c _ => fresh_init bot c⟩
  | succ n ih =>
    obtain ⟨C, e, hlog, hst, hfr⟩ := ih (by omega)
    have hpi : pinit (V := V) k os blk rd l₀ (n + 1) =
        pinit k os blk rd l₀ n ++ pstep k os blk rd l₀ (n + 1) := by
      simp [pinit, List.range_succ]
    have hpH : piH (V := V) rd l₀ (n + 1) = piH rd l₀ n ++ (if n + 1 = l₀ then [] else [.invR (rd (n + 1))]) := by
      simp [piH, List.range_succ]
    by_cases h0 : n + 1 = l₀
    · have e2 := cexec_forges k 3 (T k os blk rd) v₁ bot inst t F C (objs os blk (P k (n + 1)))
        (fun s => pre k rd (n + 1) (blk s))
        (fun s hs => hF (by omega) s (by rw [← h0]; exact (mem_objs os blk hall _ s).1 hs))
      refine ⟨{ C with log := fun s =>
          (if s ∈ objs os blk (P k (n + 1)) then pre k rd (n + 1) (blk s) else C.log s) }, ?_, fun s => ?_, fun l h1 h2 h3 => ?_, fun c hc => ?_⟩
      · rw [hpi, hpH, ite_cond_eq_true _ _ (eq_true h0)]
        refine cexec_append_some k 3 _ v₁ bot inst t F e ?_
        simpa [pstep, h0] using e2
      · by_cases h : P k (n + 1) (blk s)
        · simp [mem_objs os blk hall, h]
        · simp [mem_objs os blk hall, h, hlog, pre_succ]
      · exact hst l h1 (by omega) h3
      · exact hfr c fun l h1 h2 h3 => hc l h1 (by omega) h3
    · obtain ⟨C', e2, hlog', hst', hfr'⟩ := rdInit_spec k os blk rd v₁ bot t F inst hos hall (n + 1)
        (by omega) (hinst _ (by omega) hn) C
        (hfr _ fun l h1 h2 _ => rc_ne k rd hrd (by omega) hn h1 (by omega) (by omega))
        (fun s _ => by rw [hlog]; rfl)
      refine ⟨C', ?_, fun s => ?_, fun l h1 h2 h3 => ?_, fun c hc => ?_⟩
      · simp only [hpi, hpH, h0, pstep, ↓reduceIte]
        exact cexec_append_some k 3 _ v₁ bot inst t F e e2
      · rw [hlog', hlog, pre_succ]; split_ifs <;> simp
      · by_cases hl : l = n + 1
        · subst hl; exact hst'
        · exact started_of_cst k os blk rd (hfr' _ (rc_ne k rd hrd h1 (by omega) (by omega) hn hl))
            (hst l h1 (by omega) h3)
      · exact fresh_of_cst (hfr' c (hc _ (by omega) le_rfl h0))
          (hfr c fun l h1 h2 h3 => hc l h1 (by omega) h3)

/-! ### The write -/

/-- One terminated write round (it reaches all `B` blocks). -/
def wround : List (LEv Obj Rd V (Inst Rd)) :=
  dlvs .w (objs os blk isB) (fun _ => 1) ++ [.nxt .w]

/-- `write(v₁)` with `r` terminated rounds. -/
def wpre (r : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invW v₁] ++ (List.replicate r (wround os blk)).flatten

lemma not_isB_CC {X : Blk} (hv : Valid k X) (h : ¬ isB X) : Mlt (0 - 1) X ∨ CC k (0 + 1) X := by
  cases X with
  | B x => exact absurd trivial h
  | C x => right; simp only [Valid] at hv; simp only [CC]; omega

theorem wpre_spec (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hb : v₁ ≠ bot) (hiw : inst .w = wi) (C0 : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C0 .w)
    (h0 : ∀ s, C0.log s = pre k rd k (blk s)) (r : ℕ) (hr : r ≤ k) :
    ∃ C, cx k os blk rd v₁ bot t F inst C0 (wpre os blk v₁ r) =
        some (C, [.invW v₁] ++ (if r = k then [.retW] else [])) ∧
      (∀ s, C.log s = pre k rd k (blk s) ++ (if isB (blk s) then W r else [])) ∧
      (∀ s, C.prc s .w = if isB (blk s) then r else 0) ∧
      (r < k → C.rnd .w = r + 1 ∧ C.done .w = false ∧ (C.past .w).length = r ∧ C.cur .w = []) ∧
      (∀ c, c ≠ .w → cst C c = cst C0 c) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfr
  induction r with
  | zero =>
    refine ⟨{ C0 with rnd := Function.update C0.rnd .w 1, wv := v₁ }, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [wpre, List.replicate_zero, List.flatten_nil, List.append_nil]
      dsimp only [cx]
      rw [cexec_invW _ _ _ _ _ _ _ _ _ f1 hb]
      simp; omega
    · intro s; simp [h0, W]
    · intro s; simp [f5]
    · intro _; simp [f2, f3, f4]
    · intro c hc; exact cst_invW hc v₁
  | succ r ih =>
    obtain ⟨C, hC, hlog, hprc, hst, hfr⟩ := ih (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hst (by omega)
    have hround := cexec_round k 3 (T k os blk rd) v₁ bot inst t F C .w (objs os blk isB)
      (nodup_objs os blk hos _) (fun _ => 1)
      (fun s hs => by rw [hprc, if_pos ((mem_objs os blk hall _ s).1 hs), h1])
      (by omega) h2 (fun s => isB (blk s)) (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
      (card_le blk t _ _ (fun s hs => not_isB_CC k (hfit.valid s) hs) (hfit.c 0 hk)) (by
        rw [h4, h1, List.nil_append, hiw]
        have : ∀ s ∈ objs os blk isB, ents inst C .w s 1 =
            [(s, ((wi, r + 1), pre k rd k (blk s) ++ W r))] := by
          intro s hs
          have hs' := (mem_objs os blk hall _ s).1 hs
          simp [ents, newLabs, hiw, hprc, hlog, hs']
        rw [List.flatMap_congr this, ← List.map_eq_flatMap]
        simp [T, wi])
    have hrounds : (LPr (Obj := Obj) k 3 bot inst).rounds .w = k := rfl
    rw [hrounds] at hround
    have hnk : r ≠ k := by omega
    simp only [hnk, ite_false, List.append_nil] at hC
    have hall' := cexec_append_some k 3 (T k os blk rd) v₁ bot inst t F hC hround
    set D := dlvRes inst C .w (objs os blk isB) fun _ => 1 with hD
    have hDr : D.rnd .w = r + 1 := by simp [hD, dlvRes, h1]
    refine ⟨nxtRes D .w k, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show wpre os blk v₁ (r + 1) = wpre os blk v₁ r ++ wround os blk by
        simp [wpre, List.replicate_succ', List.flatten_append]]
      dsimp only [cx]
      rw [wround, hall']
      congr 2
      simp only [nxtHist, hDr]
    · intro s; rw [nxtRes_log]
      by_cases hs : isB (blk s)
      · simp [hD, dlvRes, mem_objs os blk hall, hs, hlog, newLabs, hprc, hiw, ← W_succ]
      · simp [hD, dlvRes, mem_objs os blk hall, hs, hlog]
    · intro s; rw [nxtRes_prc]
      by_cases hs : isB (blk s) <;> simp [hD, dlvRes, mem_objs os blk hall, hs, hprc]
    · intro hlt
      have : D.rnd .w ≠ k := by omega
      simp only [nxtRes, this, ite_false]
      simp [hD, dlvRes, h1, h2, h3]
    · intro c hc
      rw [cst_nxtRes hc, cst_dlvRes inst hc]; exact hfr c hc

/-- The partial write `wr^{k-i}` (`1 ≤ i ≤ k`): `k - i` terminated rounds, round `k - i + 1`
reaches `B₀` and the `B_j` with `j ≢ i`. -/
def wrP (i : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  wpre os blk v₁ (k - i) ++ dlvs .w (objs os blk (wl i)) (fun _ => 1)

theorem wrP_spec (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hb : v₁ ≠ bot) (hiw : inst .w = wi) (C0 : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C0 .w)
    (h0 : ∀ s, C0.log s = pre k rd k (blk s)) (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
    ∃ C, cx k os blk rd v₁ bot t F inst C0 (wrP k os blk v₁ i) = some (C, [.invW v₁]) ∧
      (∀ s, C.log s = pre k rd k (blk s) ++ W (wc k i (blk s))) ∧
      (∀ c, c ≠ .w → cst C c = cst C0 c) := by
  obtain ⟨C, hC, hlog, hprc, hst, hfr⟩ :=
    wpre_spec k os blk rd v₁ bot t F inst hk hos hall hfit hb hiw C0 hfr h0 (k - i) (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := hst (by omega)
  have hnk : k - i ≠ k := by omega
  simp only [hnk, ite_false, List.append_nil] at hC
  have hd := cexec_dlvs k 3 (T k os blk rd) v₁ bot inst t F C .w
    (objs os blk (wl i)) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      have hB : isB (blk s) := by revert this; cases blk s <;> simp [wl, isB]
      rw [hprc, if_pos hB, h1]) (by omega)
  refine ⟨_, by dsimp only [cx]; rw [wrP]; exact cexec_append_some k 3 _ v₁ bot inst t F hC hd,
    fun s => ?_, fun c hc => by rw [cst_dlvRes inst hc]; exact hfr c hc⟩
  rcases hX : blk s with x | x
  · by_cases hw : wl i (B x)
    · have hB : isB (blk s) := by rw [hX]; trivial
      have hm : s ∈ objs os blk (wl i) := (mem_objs os blk hall _ s).2 (hX ▸ hw)
      have hwc : wc k i (B x) = k - i + 1 := by
        simp only [wl] at hw; simp only [wc]; split_ifs <;> omega
      simp only [dlvRes, hm, ite_true, hlog, newLabs, hprc, hiw, List.range_one, List.map_cons,
        List.map_nil, hX, hwc, List.append_assoc]
      rw [← W_succ]; simp [isB]
    · have hm : s ∉ objs os blk (wl i) := fun h => hw (hX ▸ (mem_objs os blk hall _ s).1 h)
      have hwc : wc k i (B x) = k - i := by
        simp only [wl, not_or] at hw; simp only [wc]; split_ifs <;> omega
      simp [dlvRes, hm, hlog, hX, hwc, isB]
  · have hm : s ∉ objs os blk (wl i) := fun h => by
      have := (mem_objs os blk hall _ s).1 h; rw [hX] at this; exact this
    simp [dlvRes, hm, hlog, hX, wc, isB, W]

/-! ### Block arithmetic -/

lemma P_H12 {l : ℕ} {X : Blk} (h : P k l X) : H12 k l X := by
  cases X <;> simp_all [H12, P, Mlt]; omega

lemma H12_cases {l : ℕ} {X : Blk} (h : H12 k l X) : R1 k l X ∨ P k l X := by
  by_cases hp : P k l X
  · exact Or.inr hp
  · exact Or.inl ⟨h, hp⟩

lemma R1_H12 {l : ℕ} {X : Blk} (h : R1 k l X) : H12 k l X := h.1

lemma R1_not_P {l : ℕ} {X : Blk} (h : R1 k l X) : ¬ P k l X := h.2

lemma not_H12 {l : ℕ} {X : Blk} (h : ¬ H12 k l X) : Mlt (l + 1 - 2) X ∨ P k (l + 1) X := by
  simp only [H12, not_not] at h
  rwa [show l + 1 - 2 = l - 1 by omega]

lemma CC_R1 {l : ℕ} {X : Blk} (h : CC k l X) : R1 k l X := by
  cases X <;> simp_all [R1, H12, P, Mlt, CC]; omega

lemma Q3a_H12 {l : ℕ} {X : Blk} (h : Q3a k l X) : H12 k l X := by
  simp only [Q3a] at h; simp only [H12]; tauto

lemma Q3b_not_H12 {l : ℕ} {X : Blk} (h : Q3b k l X) : ¬ H12 k l X := by
  simp only [Q3b] at h; simp only [H12, not_not]; exact Or.inr h.2.1

lemma Q3b_not_Q3a {l : ℕ} {X : Blk} (h : Q3b k l X) : ¬ Q3a k l X := by
  simp only [Q3b] at h; simp only [Q3a]; tauto

lemma not_Q3_lt {l : ℕ} (hl : l < k) {X : Blk} (h : ¬ (Q3a k l X ∨ Q3b k l X)) :
    Mlt (l - 1) X ∨ CC k (l + 1) X := by
  simp only [Q3a, Q3b] at h; tauto

lemma not_Q3_eq {X : Blk} (h : ¬ (Q3a k k X ∨ Q3b k k X)) : Mlt (k + 1 - 2) X ∨ P k (k + 1) X := by
  rw [show k + 1 - 2 = k - 1 by omega]
  have : ¬ CC k (k + 1) X := by cases X <;> simp [CC]
  simp only [Q3a, Q3b] at h; tauto

/-! ### Read phases -/

/-- Forging before round 1 of read `l`: the objects of the blocks `fg` forge `refLog (l - 1)`. -/
def fgs (l : ℕ) (fg : Blk → Prop) [DecidablePred fg] : List (LEv Obj Rd V (Inst Rd)) :=
  forges (objs os blk fg) (fun s => refLog k rd (l - 1) (blk s))

/-- Forging, then the rest of round 1 of read `l` (to `R1 l`), terminated. -/
def ph1 (l : ℕ) (fg : Blk → Prop) [DecidablePred fg] : List (LEv Obj Rd V (Inst Rd)) :=
  fgs k os blk rd l fg ++ (dlvs (rc rd l) (objs os blk (R1 k l)) (fun _ => 1) ++ [.nxt (rc rd l)])

theorem ph1_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk) (l : ℕ) (hl : 1 ≤ l)
    (hlk : l ≤ k) (hinst : inst (rc rd l) = ri rd l) (fg : Blk → Prop) [DecidablePred fg]
    (hF : ∀ s, fg (blk s) → s ∈ F) (C : LCfg Obj Rd V (Inst Rd)) (hst : Started k os blk rd C l)
    (hlog : ∀ s, R1 k l (blk s) → ¬ fg (blk s) → C.log s = refLog k rd (l - 1) (blk s)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (ph1 k os blk rd l fg) = some (C', []) ∧
      (∀ s, C'.log s = (if fg (blk s) then refLog k rd (l - 1) (blk s) else C.log s) ++
        (if R1 k l (blk s) then rl rd l 1 else [])) ∧
      C'.rnd (rc rd l) = 2 ∧ (C'.past (rc rd l)).length = 1 ∧ C'.cur (rc rd l) = [] ∧
      C'.done (rc rd l) = false ∧ (∀ s, C'.prc s (rc rd l) = if H12 k l (blk s) then 1 else 0) ∧
      (∀ c, c ≠ rc rd l → cst C' c = cst C c) := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := hst
  have hinst' : inst (rc rd l) = (rc rd l, l) := hinst
  have hri : ri rd l = (rc rd l, l) := rfl
  have e1 := cexec_forges k 3 (T k os blk rd) v₁ bot inst t F C (objs os blk fg)
    (fun s => refLog k rd (l - 1) (blk s)) (fun s hs => hF s ((mem_objs os blk hall _ s).1 hs))
  set C2 : LCfg Obj Rd V (Inst Rd) := { C with log := fun s =>
    (if s ∈ objs os blk fg then refLog k rd (l - 1) (blk s) else C.log s) } with hC2
  have hC2log : ∀ s, C2.log s = if fg (blk s) then refLog k rd (l - 1) (blk s) else C.log s := by
    intro s; simp [hC2, mem_objs os blk hall]
  have e2 := cexec_round k 3 (T k os blk rd) v₁ bot inst t F C2 (rc rd l)
    (objs os blk (R1 k l)) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      show C.prc s (rc rd l) + 1 = C.rnd (rc rd l)
      rw [g5, if_neg (R1_not_P k this), g1])
    (by show (C.past (rc rd l)).length + 1 = C.rnd (rc rd l); rw [g2, g1]; rfl) g4
    (fun s => H12 k l (blk s))
    (fun s hs => by
      rcases H12_cases k hs with h | h
      · exact Or.inl ((mem_objs os blk hall _ s).2 h)
      · right; show C.prc s (rc rd l) = C.rnd (rc rd l); rw [g5, if_pos h, g1])
    (card_le blk t _ _ (fun s hs => not_H12 k hs) (hfit.b (l + 1) (by omega) (by omega))) (by
      show C.cur (rc rd l) ++ _ = T k os blk rd (inst (rc rd l), C.rnd (rc rd l))
      rw [g3, hinst, g1]
      have : ∀ s ∈ objs os blk (R1 k l), ents inst C2 (rc rd l) s 1 =
          [(s, ((ri rd l, 1), refLog k rd (l - 1) (blk s)))] := by
        intro s hs
        have h1 := (mem_objs os blk hall _ s).1 hs
        have h2 : C2.prc s (rc rd l) = 0 := by
          show C.prc s (rc rd l) = 0; rw [g5, if_neg (R1_not_P k h1)]
        have h3 : C2.log s = refLog k rd (l - 1) (blk s) := by
          rw [hC2log]; split_ifs with h
          · rfl
          · exact hlog s h1 h
        simp [ents, newLabs, h2, h3, hinst', hri]
      rw [List.flatMap_congr this, ← List.map_eq_flatMap]
      simp [T, ri, rc, hl])
  have hrounds : (LPr (Obj := Obj) k 3 bot inst).rounds (rc rd l) = 3 := by
    simp [rc, Proto.rounds, LP]
  rw [hrounds] at e2
  set D1 := dlvRes inst C2 (rc rd l) (objs os blk (R1 k l)) fun _ => 1 with hD1
  have hD1r : D1.rnd (rc rd l) = 1 := by simp [hD1, dlvRes, hC2, g1]
  have hH1 : nxtHist bot D1 (rc rd l) 3 = [] := by simp [nxtHist, hD1r]
  rw [hH1] at e2
  have hC3' : nxtRes D1 (rc rd l) 3 = { D1 with
      past := Function.update D1.past (rc rd l) (D1.past (rc rd l) ++ [D1.cur (rc rd l)])
      cur := Function.update D1.cur (rc rd l) []
      rnd := Function.update D1.rnd (rc rd l) (D1.rnd (rc rd l) + 1) } :=
    nxtRes_adv D1 (rc rd l) 3 (by omega)
  refine ⟨nxtRes D1 (rc rd l) 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [cx]
    have := cexec_append_some k 3 _ v₁ bot inst t F e1 e2
    simpa [ph1, fgs] using this
  · intro s
    rw [nxtRes_log]
    by_cases h : R1 k l (blk s)
    · simp [hD1, dlvRes, mem_objs os blk hall, h, hC2log, newLabs, hinst', rl_pos rd hl, hri,
        show C2.prc s (rc rd l) = 0 by show C.prc s (rc rd l) = 0; rw [g5, if_neg (R1_not_P k h)]]
    · simp [hD1, dlvRes, mem_objs os blk hall, h, hC2log]
  · rw [hC3']; simp [hD1r]
  · rw [hC3']; simp [hD1, dlvRes, hC2, g2]
  · rw [hC3']; simp
  · rw [hC3']; simp [hD1, dlvRes, hC2, g4]
  · intro s
    rw [nxtRes_prc]
    by_cases h : R1 k l (blk s)
    · simp [hD1, dlvRes, mem_objs os blk hall, h, R1_H12 k h, hC2, g5, R1_not_P k h]
    · have : H12 k l (blk s) ↔ P k l (blk s) :=
        ⟨fun h' => (H12_cases k h').resolve_left h, P_H12 k⟩
      simp only [hD1, dlvRes, mem_objs os blk hall, h, false_and, ite_false, this]
      exact g5 s
  · intro c hc
    rw [cst_nxtRes hc, cst_dlvRes inst hc]; rfl

/-- An incomplete read (`inc2`): round 1 terminated, round 2 reaches `𝒞_j` only. -/
def inc2 (j : ℕ) (fg : Blk → Prop) [DecidablePred fg] : List (LEv Obj Rd V (Inst Rd)) :=
  ph1 k os blk rd j fg ++ dlvs (rc rd j) (objs os blk (CC k j)) (fun _ => 1)

theorem inc2_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk) (j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (hinst : inst (rc rd j) = ri rd j) (fg : Blk → Prop) [DecidablePred fg]
    (hF : ∀ s, fg (blk s) → s ∈ F) (C : LCfg Obj Rd V (Inst Rd)) (hst : Started k os blk rd C j)
    (hlog : ∀ s, R1 k j (blk s) → ¬ fg (blk s) → C.log s = refLog k rd (j - 1) (blk s)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (inc2 k os blk rd j fg) = some (C', []) ∧
      (∀ s, C'.log s = (if fg (blk s) then refLog k rd (j - 1) (blk s) else C.log s) ++
        (if R1 k j (blk s) then rl rd j 1 else []) ++ (if CC k j (blk s) then rl rd j 2 else [])) ∧
      (∀ c, c ≠ rc rd j → cst C' c = cst C c) := by
  have hinst' : inst (rc rd j) = (rc rd j, j) := hinst
  have hri : ri rd j = (rc rd j, j) := rfl
  obtain ⟨C1, e1, hlog1, r1, p1, -, -, prc1, fr1⟩ :=
    ph1_spec k os blk rd v₁ bot t F inst hos hall hfit j hj hjk hinst fg hF C hst hlog
  have e2 := cexec_dlvs k 3 (T k os blk rd) v₁ bot inst t F C1 (rc rd j) (objs os blk (CC k j))
    (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      rw [prc1, if_pos (R1_H12 k (CC_R1 k this)), r1]) (by rw [r1, p1])
  refine ⟨_, by dsimp only [cx]; rw [inc2]; exact cexec_append_some k 3 _ v₁ bot inst t F e1 e2,
    fun s => ?_, fun c hc => by rw [cst_dlvRes inst hc]; exact fr1 c hc⟩
  by_cases h : CC k j (blk s)
  · simp [dlvRes, mem_objs os blk hall, h, hlog1, newLabs, prc1, R1_H12 k (CC_R1 k h), hinst',
      rl_pos rd hj, hri]
  · simp [dlvRes, mem_objs os blk hall, h, hlog1]

/-- An incomplete read (`inc3`): rounds 1, 2 terminated, round 3 reaches `Q3a l` only. -/
def inc3 (l : ℕ) (fg : Blk → Prop) [DecidablePred fg] : List (LEv Obj Rd V (Inst Rd)) :=
  ph1 k os blk rd l fg ++ (dlvs (rc rd l) (objs os blk (H12 k l)) (fun _ => 1) ++ [.nxt (rc rd l)]) ++
    dlvs (rc rd l) (objs os blk (Q3a k l)) (fun _ => 1)

theorem inc3_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk) (l : ℕ) (hl : 1 ≤ l)
    (hlk : l ≤ k) (hinst : inst (rc rd l) = ri rd l) (fg : Blk → Prop) [DecidablePred fg]
    (hF : ∀ s, fg (blk s) → s ∈ F) (C : LCfg Obj Rd V (Inst Rd)) (hst : Started k os blk rd C l)
    (hlog : ∀ s, H12 k l (blk s) → ¬ fg (blk s) → C.log s = refLog k rd (l - 1) (blk s)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (inc3 k os blk rd l fg) = some (C', []) ∧
      (∀ s, C'.log s = (if fg (blk s) then refLog k rd (l - 1) (blk s) else C.log s) ++
        (if R1 k l (blk s) then rl rd l 1 else []) ++ (if H12 k l (blk s) then rl rd l 2 else []) ++
        (if Q3a k l (blk s) then rl rd l 3 else [])) ∧
      C'.rnd (rc rd l) = 3 ∧ (C'.past (rc rd l)).length = 2 ∧
      C'.cur (rc rd l) = (objs os blk (Q3a k l)).map
        (fun s => (s, ((ri rd l, 3), aft1 k rd l (blk s) ++ rl rd l 2))) ∧
      C'.done (rc rd l) = false ∧
      (∀ s, C'.prc s (rc rd l) = if Q3a k l (blk s) then 3 else if H12 k l (blk s) then 2 else 0) ∧
      (∀ c, c ≠ rc rd l → cst C' c = cst C c) := by
  have hinst' : inst (rc rd l) = (rc rd l, l) := hinst
  have hri : ri rd l = (rc rd l, l) := rfl
  obtain ⟨C1, e1, hlog1, r1, p1, c1, d1, prc1, fr1⟩ :=
    ph1_spec k os blk rd v₁ bot t F inst hos hall hfit l hl hlk hinst fg hF C hst
      (fun s h1 h2 => hlog s (R1_H12 k h1) h2)
  have hlog1' : ∀ s, H12 k l (blk s) → C1.log s = aft1 k rd l (blk s) := by
    intro s hs
    rw [hlog1, aft1]
    have : (if fg (blk s) then refLog k rd (l - 1) (blk s) else C.log s) =
        refLog k rd (l - 1) (blk s) := by
      split_ifs with h
      · rfl
      · exact hlog s hs h
    rw [this]
    by_cases hp : P k l (blk s)
    · simp [hp, R1]
    · simp [hp, R1, hs]
  -- round 2
  have e2 := cexec_round k 3 (T k os blk rd) v₁ bot inst t F C1 (rc rd l)
    (objs os blk (H12 k l)) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by rw [prc1, if_pos ((mem_objs os blk hall _ s).1 hs), r1])
    (by rw [p1, r1]) d1 (fun s => H12 k l (blk s))
    (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
    (card_le blk t _ _ (fun s hs => not_H12 k hs) (hfit.b (l + 1) (by omega) (by omega))) (by
      rw [c1, List.nil_append, hinst, r1]
      have : ∀ s ∈ objs os blk (H12 k l), ents inst C1 (rc rd l) s 1 =
          [(s, ((ri rd l, 2), aft1 k rd l (blk s)))] := by
        intro s hs
        have h1 := (mem_objs os blk hall _ s).1 hs
        simp [ents, newLabs, prc1, h1, hlog1' s h1, hinst', hri]
      rw [List.flatMap_congr this, ← List.map_eq_flatMap]
      simp [T, ri, rc, hl])
  have hrounds : (LPr (Obj := Obj) k 3 bot inst).rounds (rc rd l) = 3 := by
    simp [rc, Proto.rounds, LP]
  rw [hrounds] at e2
  set D2 := dlvRes inst C1 (rc rd l) (objs os blk (H12 k l)) fun _ => 1 with hD2
  have hD2r : D2.rnd (rc rd l) = 2 := by simp [hD2, dlvRes, r1]
  have hH2 : nxtHist bot D2 (rc rd l) 3 = [] := by simp [nxtHist, hD2r]
  rw [hH2] at e2
  set C3 := nxtRes D2 (rc rd l) 3 with hC3
  have hC3' : C3 = { D2 with
      past := Function.update D2.past (rc rd l) (D2.past (rc rd l) ++ [D2.cur (rc rd l)])
      cur := Function.update D2.cur (rc rd l) []
      rnd := Function.update D2.rnd (rc rd l) (D2.rnd (rc rd l) + 1) } :=
    nxtRes_adv D2 (rc rd l) 3 (by omega)
  have h3r : C3.rnd (rc rd l) = 3 := by simp [hC3', hD2r]
  have h3p : (C3.past (rc rd l)).length = 2 := by simp [hC3', hD2, dlvRes, p1]
  have h3c : C3.cur (rc rd l) = [] := by simp [hC3']
  have h3d : C3.done (rc rd l) = false := by simp [hC3', hD2, dlvRes, d1]
  have h3prc : ∀ s, C3.prc s (rc rd l) = if H12 k l (blk s) then 2 else 0 := by
    intro s; by_cases h : H12 k l (blk s) <;> simp [hC3', hD2, dlvRes, mem_objs os blk hall, h, prc1]
  have h3log : ∀ s, C3.log s = C1.log s ++ (if H12 k l (blk s) then rl rd l 2 else []) := by
    intro s
    by_cases h : H12 k l (blk s)
    · simp [hC3', hD2, dlvRes, mem_objs os blk hall, h, newLabs, prc1, hinst', rl_pos rd hl, hri]
    · simp [hC3', hD2, dlvRes, mem_objs os blk hall, h]
  -- round 3 (partial)
  have e3 := cexec_dlvs k 3 (T k os blk rd) v₁ bot inst t F C3 (rc rd l) (objs os blk (Q3a k l))
    (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      rw [h3prc, if_pos (Q3a_H12 k this), h3r]) (by rw [h3r, h3p])
  refine ⟨dlvRes inst C3 (rc rd l) (objs os blk (Q3a k l)) (fun _ => 1), ?_, fun s => ?_, ?_, ?_, ?_,
    ?_, fun s => ?_, fun c hc => ?_⟩
  · dsimp only [cx]
    have := cexec_append_some k 3 _ v₁ bot inst t F (cexec_append_some k 3 _ v₁ bot inst t F e1 e2) e3
    simpa [inc3, List.append_assoc] using this
  · by_cases h : Q3a k l (blk s)
    · simp [dlvRes, mem_objs os blk hall, h, h3log, Q3a_H12 k h, h3prc, newLabs, hinst',
        rl_pos rd hl, hri, hlog1]
    · simp [dlvRes, mem_objs os blk hall, h, h3log, hlog1]
  · simp [dlvRes, h3r]
  · simp [dlvRes, h3p]
  · simp only [dlvRes, Function.update_self, h3c, List.nil_append]
    rw [List.map_eq_flatMap]
    apply List.flatMap_congr
    intro s hs
    have h1 := (mem_objs os blk hall _ s).1 hs
    simp [ents, newLabs, h3prc, Q3a_H12 k h1, h3log, hlog1' s (Q3a_H12 k h1), hinst', hri,
      rl_pos rd hl]
  · simp [dlvRes, h3d]
  · by_cases h : Q3a k l (blk s)
    · simp [dlvRes, mem_objs os blk hall, h, h3prc, Q3a_H12 k h]
    · simp [dlvRes, mem_objs os blk hall, h, h3prc]
  · rw [cst_dlvRes inst hc, hC3, cst_nxtRes hc, cst_dlvRes inst hc]; exact fr1 c hc

/-- A complete read: `inc3`, then round 3 reaches `Q3b l` (three pending messages each) and
terminates. -/
def full (l : ℕ) (fg : Blk → Prop) [DecidablePred fg] : List (LEv Obj Rd V (Inst Rd)) :=
  inc3 k os blk rd l fg ++ (dlvs (rc rd l) (objs os blk (Q3b k l)) (fun _ => 3) ++ [.nxt (rc rd l)])

theorem full_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk) (l : ℕ) (hl : 1 ≤ l)
    (hlk : l ≤ k) (hinst : inst (rc rd l) = ri rd l) (fg : Blk → Prop) [DecidablePred fg]
    (hF : ∀ s, fg (blk s) → s ∈ F) (C : LCfg Obj Rd V (Inst Rd)) (hst : Started k os blk rd C l)
    (hlog : ∀ s, (H12 k l (blk s) ∨ Q3b k l (blk s)) → ¬ fg (blk s) →
      C.log s = refLog k rd (l - 1) (blk s)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (full k os blk rd l fg) =
        some (C', [.retR (rd l) bot]) ∧
      (∀ s, C'.log s = (if fg (blk s) then refLog k rd (l - 1) (blk s) else C.log s) ++
        (if R1 k l (blk s) then rl rd l 1 else []) ++ (if H12 k l (blk s) then rl rd l 2 else []) ++
        (if Q3a k l (blk s) then rl rd l 3 else []) ++
        (if Q3b k l (blk s) then rl rd l 1 ++ rl rd l 2 ++ rl rd l 3 else [])) ∧
      (∀ c, c ≠ rc rd l → cst C' c = cst C c) := by
  have hinst' : inst (rc rd l) = (rc rd l, l) := hinst
  have hri : ri rd l = (rc rd l, l) := rfl
  obtain ⟨C1, e1, hlog1, r1, p1, c1, d1, prc1, fr1⟩ :=
    inc3_spec k os blk rd v₁ bot t F inst hos hall hfit l hl hlk hinst fg hF C hst
      (fun s h1 h2 => hlog s (Or.inl h1) h2)
  have hQ : ∀ s, Q3b k l (blk s) → C1.log s = refLog k rd (l - 1) (blk s) := by
    intro s h
    rw [hlog1]
    have h1 := Q3b_not_H12 k h
    have h2 := Q3b_not_Q3a k h
    have h3 : ¬ R1 k l (blk s) := fun h' => h1 (R1_H12 k h')
    simp only [h1, h2, h3, ite_false, List.append_nil]
    split_ifs with h4
    · rfl
    · exact hlog s (Or.inr h) h4
  have e2 := cexec_round k 3 (T k os blk rd) v₁ bot inst t F C1 (rc rd l)
    (objs os blk (Q3b k l)) (nodup_objs os blk hos _) (fun _ => 3)
    (fun s hs => by
      have h := (mem_objs os blk hall _ s).1 hs
      rw [prc1, if_neg (Q3b_not_Q3a k h), if_neg (Q3b_not_H12 k h), r1])
    (by rw [p1, r1]) d1 (fun s => Q3a k l (blk s) ∨ Q3b k l (blk s))
    (fun s hs => by
      rcases hs with h | h
      · right; rw [prc1, if_pos h, r1]
      · exact Or.inl ((mem_objs os blk hall _ s).2 h))
    (by
      rcases Nat.lt_or_ge l k with hlt | hge
      · exact card_le blk t _ _ (fun s hs => not_Q3_lt k hlt hs) (hfit.c l (by omega))
      · have hlk' : l = k := by omega
        subst hlk'
        exact card_le blk t _ _ (fun s hs => not_Q3_eq l hs) (hfit.b (l + 1) (by omega) le_rfl)) (by
      rw [c1, hinst, r1]
      have : ∀ s ∈ objs os blk (Q3b k l), ents inst C1 (rc rd l) s 3 = ents3 k blk rd l s := by
        intro s hs
        have h := (mem_objs os blk hall _ s).1 hs
        simp [ents, ents3, newLabs, prc1, Q3b_not_Q3a k h, Q3b_not_H12 k h, hQ s h, hinst', hri,
          rl_pos rd hl, List.range_succ]
      rw [List.flatMap_congr this]
      simp [T, ri, rc, hl])
  have hrounds : (LPr (Obj := Obj) k 3 bot inst).rounds (rc rd l) = 3 := by
    simp [rc, Proto.rounds, LP]
  rw [hrounds] at e2
  set D := dlvRes inst C1 (rc rd l) (objs os blk (Q3b k l)) fun _ => 3 with hD
  have hDr : D.rnd (rc rd l) = 3 := by simp [hD, dlvRes, r1]
  have hH : nxtHist bot D (rc rd l) 3 = [.retR (rd l) bot] := by
    unfold nxtHist; rw [if_pos hDr]; rfl
  rw [hH] at e2
  refine ⟨nxtRes D (rc rd l) 3, ?_, fun s => ?_, fun c hc => ?_⟩
  · dsimp only [cx]
    have := cexec_append_some k 3 _ v₁ bot inst t F e1 e2
    simpa [full, List.append_assoc] using this
  · rw [nxtRes_log]
    by_cases h : Q3b k l (blk s)
    · rw [← hlog1]
      simp [hD, dlvRes, mem_objs os blk hall, h, newLabs, prc1, Q3b_not_Q3a k h, Q3b_not_H12 k h,
        hinst', rl_pos rd hl, hri, List.range_succ]
    · simp [hD, dlvRes, mem_objs os blk hall, h, hlog1]
  · rw [cst_nxtRes hc, cst_dlvRes inst hc]; exact fr1 c hc

/-- Start of read `l` in the run `pr_l^C`: the objects of `P_l` forge their state from `prinit`
(where read `l` was replaced by forging), round 1 reaches `P_l`, and `P_l` forges `σ*`
(`refLog (l - 1)`). -/
def rdStart (l : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  forges (objs os blk (P k l)) (fun s => pre k rd (l - 1) (blk s)) ++ rdInit k os blk rd l ++
    forges (objs os blk (P k l)) (fun s => refLog k rd (l - 1) (blk s))

theorem rdStart_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (l : ℕ) (hl : 1 ≤ l)
    (hinst : inst (rc rd l) = ri rd l) (hF : ∀ s, P k l (blk s) → s ∈ F)
    (C : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C (rc rd l)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (rdStart k os blk rd l) = some (C', [.invR (rd l)]) ∧
      (∀ s, C'.log s = if P k l (blk s) then refLog k rd (l - 1) (blk s) else C.log s) ∧
      Started k os blk rd C' l ∧ (∀ c, c ≠ rc rd l → cst C' c = cst C c) := by
  have e1 := cexec_forges k 3 (T k os blk rd) v₁ bot inst t F C (objs os blk (P k l))
    (fun s => pre k rd (l - 1) (blk s)) (fun s hs => hF s ((mem_objs os blk hall _ s).1 hs))
  set C1 : LCfg Obj Rd V (Inst Rd) := { C with log := fun s =>
    (if s ∈ objs os blk (P k l) then pre k rd (l - 1) (blk s) else C.log s) } with hC1
  obtain ⟨C2, e2, hlog2, hst2, hfr2⟩ := rdInit_spec k os blk rd v₁ bot t F inst hos hall l hl hinst C1
    hfr (fun s hs => by simp [hC1, mem_objs os blk hall, hs])
  have e3 := cexec_forges k 3 (T k os blk rd) v₁ bot inst t F C2 (objs os blk (P k l))
    (fun s => refLog k rd (l - 1) (blk s)) (fun s hs => hF s ((mem_objs os blk hall _ s).1 hs))
  refine ⟨{ C2 with log := fun s =>
      (if s ∈ objs os blk (P k l) then refLog k rd (l - 1) (blk s) else C2.log s) }, ?_, fun s => ?_,
    started_of_cst k os blk rd rfl hst2, fun c hc => by rw [← show cst C1 c = cst C c from rfl, ← hfr2 c hc]; rfl⟩
  · dsimp only [cx]
    have := cexec_append_some k 3 _ v₁ bot inst t F (cexec_append_some k 3 _ v₁ bot inst t F e1 e2) e3
    simpa [rdStart, List.append_assoc] using this
  · by_cases h : P k l (blk s)
    · simp [mem_objs os blk hall, h]
    · simp [mem_objs os blk hall, h, hlog2, hC1]

/-! ### The incomplete reads `1..J` -/

/-- Forging before read `j`: the malicious objects of `B_{j-1}`, `C_{j-1}` forge `σ^r_{j-1}`. -/
def hook (mal : Blk → Prop) (j : ℕ) (X : Blk) : Prop := Idx (j - 1) X ∧ mal X

/-- Logs after `prinit`, the write (`w X` rounds at block `X`) and the incomplete reads `1..J`. -/
def sJ (w : Blk → ℕ) (J : ℕ) : Blk → List (Cl Rd × Lab (Inst Rd))
  | B m => if m < J then refLog k rd m (B m) ++ rl rd (m + 1) 1 else pre k rd k (B m) ++ W (w (B m))
  | C m => if m < J then refLog k rd m (C m) ++ rl rd (m + 1) 1 else cr rd J

/-- The incomplete reads `1..J` (`inc2`). -/
noncomputable def loop (mal : Blk → Prop) [DecidablePred mal] (J : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  (List.range J).flatMap fun m => inc2 k os blk rd (m + 1) (hook mal (m + 1))

lemma sJ_pre (w : Blk → ℕ) (j : ℕ) (hj : 1 ≤ j) (mal : Blk → Prop) (X : Blk) (hv : Valid k X)
    (hm : Idx (j - 1) X → mal X) (h : R1 k j X) (hh : ¬ hook mal j X) :
    sJ k rd w (j - 1) X = refLog k rd (j - 1) X := by
  have hI : ¬ Idx (j - 1) X := fun hI => hh ⟨hI, hm hI⟩
  cases X with
  | B m =>
    exfalso; apply hI; left
    simp only [R1, H12, Mlt, P, not_or, not_and] at h
    simp only [Valid] at hv
    congr 1
    by_contra hne
    rcases Nat.lt_or_ge m (j - 1) with h1 | h1
    · exact h.1.1 h1
    · rcases Nat.mod_two_eq_zero_or_one m with h2 | h2 <;>
      rcases Nat.mod_two_eq_zero_or_one j with h3 | h3
      all_goals exact h.2 (by omega) (by omega) (by omega)
  | C m =>
    have : m ≠ j - 1 := fun h' => hI (Or.inr (by rw [h']))
    simp only [R1, H12, Mlt] at h
    simp only [Valid] at hv
    simp only [sJ, refLog, this, ite_false, List.append_nil]
    rw [if_neg (fun h' => h.1 (Or.inl ⟨hv.1, h'⟩))]

lemma sJ_next (w : Blk → ℕ) (j : ℕ) (hj : 1 ≤ j) (mal : Blk → Prop) [DecidablePred mal] (X : Blk)
    (hv : Valid k X) (hm : Idx (j - 1) X → mal X) :
    (if hook mal j X then refLog k rd (j - 1) X else sJ k rd w (j - 1) X) ++
      (if R1 k j X then rl rd j 1 else []) ++ (if CC k j X then rl rd j 2 else []) =
    sJ k rd w j X := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hm ⊢
  cases X with
  | B m =>
    simp only [Valid] at hv
    rcases lt_trichotomy m j with h | rfl | h
    · have h1 : ¬ hook mal (j + 1) (B m) := by simp [hook, Idx]; omega
      have h2 : ¬ R1 k (j + 1) (B m) := by simp [R1, H12, Mlt]; omega
      simp [h1, h2, CC, sJ, h, show m < j + 1 by omega]
    · have h1 : hook mal (m + 1) (B m) := ⟨by simp [Idx], hm (by simp [Idx])⟩
      have h2 : R1 k (m + 1) (B m) := by simp [R1, H12, Mlt, P]
      simp [h1, h2, CC, sJ]
    · have h1 : ¬ hook mal (j + 1) (B m) := by simp [hook, Idx]; omega
      have h2 : ¬ R1 k (j + 1) (B m) := by
        simp only [R1, H12, Mlt, P, not_or, not_and]; omega
      simp [h1, h2, CC, sJ, show ¬ m < j by omega, show ¬ m < j + 1 by omega]
  | C m =>
    simp only [Valid] at hv
    rcases lt_trichotomy m j with h | rfl | h
    · have h1 : ¬ hook mal (j + 1) (C m) := by simp [hook, Idx]; omega
      have h2 : ¬ R1 k (j + 1) (C m) := by simp [R1, H12, Mlt]; omega
      simp [h1, h2, CC, sJ, h, show m < j + 1 by omega]; omega
    · have h1 : hook mal (m + 1) (C m) := ⟨by simp [Idx], hm (by simp [Idx])⟩
      have h2 : R1 k (m + 1) (C m) := by simp [R1, H12, Mlt, P]
      simp [h1, h2, CC, sJ]
    · have h1 : ¬ hook mal (j + 1) (C m) := by simp [hook, Idx]; omega
      have h2 : R1 k (j + 1) (C m) := by simp [R1, H12, Mlt, P]; omega
      have h3 : CC k (j + 1) (C m) := by simp [CC]; omega
      simp [h1, h2, h3, sJ, show ¬ m < j by omega, show ¬ m < j + 1 by omega, cr_succ]

theorem loop_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk) (hrd : RdInj k rd)
    (hinst : ∀ l, 1 ≤ l → l ≤ k → inst (rc rd l) = ri rd l) (mal : Blk → Prop) [DecidablePred mal]
    (hF : ∀ s, mal (blk s) → s ∈ F) (w : Blk → ℕ) (C0 : LCfg Obj Rd V (Inst Rd))
    (h0 : ∀ s, C0.log s = sJ k rd w 0 (blk s)) (J : ℕ) (hJ : J ≤ k)
    (hmal : ∀ j, 1 ≤ j → j ≤ J → ∀ X, Valid k X → Idx (j - 1) X → mal X)
    (hst : ∀ j, 1 ≤ j → j ≤ J → Started k os blk rd C0 j) :
    ∃ C, cx k os blk rd v₁ bot t F inst C0 (loop k os blk rd mal J) = some (C, []) ∧
      (∀ s, C.log s = sJ k rd w J (blk s)) ∧
      (∀ c, (∀ j, 1 ≤ j → j ≤ J → c ≠ rc rd j) → cst C c = cst C0 c) := by
  induction J with
  | zero => exact ⟨C0, by simp [loop, cexec_nil], h0, fun _ _ => rfl⟩
  | succ J ih =>
    obtain ⟨C, e, hlog, hfr⟩ := ih (by omega) (fun j h1 h2 => hmal j h1 (by omega))
      (fun j h1 h2 => hst j h1 (by omega))
    have hstJ : Started k os blk rd C (J + 1) :=
      started_of_cst k os blk rd (hfr _ fun j h1 h2 => rc_ne k rd hrd (by omega) hJ h1 (by omega)
        (by omega)) (hst (J + 1) (by omega) le_rfl)
    obtain ⟨C', e', hlog', hfr'⟩ := inc2_spec k os blk rd v₁ bot t F inst hos hall hfit (J + 1)
      (by omega) hJ (hinst _ (by omega) hJ) (hook mal (J + 1)) (fun s h => hF s h.2) C hstJ
      (fun s h1 h2 => by
        rw [hlog s]
        have := sJ_pre k rd w (J + 1) (by omega) mal (blk s) (hfit.valid s)
          (hmal (J + 1) (by omega) le_rfl _ (hfit.valid s)) h1 h2
        simpa using this)
    refine ⟨C', ?_, fun s => ?_, fun c hc => ?_⟩
    · have := cexec_append_some k 3 _ v₁ bot inst t F e e'
      simpa [loop, List.range_succ] using this
    · rw [hlog', hlog s]
      have := sJ_next k rd w (J + 1) (by omega) mal (blk s) (hfit.valid s)
        (hmal (J + 1) (by omega) le_rfl _ (hfit.valid s))
      simpa using this
    · rw [hfr' c (hc _ (by omega) le_rfl), hfr c fun j h1 h2 => hc j h1 (by omega)]

/-! ### Consistency of the logs `refLog` -/

lemma wc_succ (L m : ℕ) (hm : m ≠ 0) (hpar : m % 2 = L % 2) (hLk : L + 1 ≤ k) :
    wc k (L + 1) (B m) = wc k L (B m) := by
  simp only [wc, hm, ite_false]; split_ifs <;> omega

lemma refLog_zero (X : Blk) : refLog k rd 0 X = pre k rd k X ++ W (wc k 1 X) := by
  cases X with
  | B m => simp [refLog, rl_zero]
  | C m => simp [refLog, rl_zero, cr, pre_C, wc, W]

lemma refLog_P (L m : ℕ) (h : m % 2 ≠ L % 2) :
    refLog k rd L (B m) = pre k rd k (B m) ++ W (wc k (L + 1) (B m)) := by
  simp [refLog, h]

/-- After round 3 of read `L` (`L < k`), the blocks of index `≥ L` outside `P_{L+1}` are in
the state `σ^r_L`. -/
lemma refLog_next (L : ℕ) (hL : 1 ≤ L) (hLk : L + 1 ≤ k) (X : Blk) (hv : Valid k X)
    (h1 : ¬ Mlt L X) (h2 : ¬ P k (L + 1) X) :
    refLog k rd (L - 1) X ++ (if R1 k L X then rl rd L 1 else []) ++
      (if H12 k L X then rl rd L 2 else []) ++ (if Q3a k L X then rl rd L 3 else []) =
    refLog k rd L X := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  cases X with
  | B m =>
    simp only [Valid] at hv
    simp only [Mlt, not_lt] at h1
    simp only [P, not_and] at h2
    have hpar : m % 2 = (L + 1) % 2 := by
      rcases Nat.lt_or_ge m (L + 2) with h | h
      · omega
      · have := h2 h hv; omega
    have hP : P k (L + 1) (B m) := ⟨h1, hv, hpar⟩
    have hR : ¬ R1 k (L + 1) (B m) := fun h => h.2 hP
    have hH : H12 k (L + 1) (B m) := P_H12 k hP
    have hQ : Q3a k (L + 1) (B m) := by
      refine ⟨?_, by simp [CC], fun h => ?_⟩
      · simp only [Mlt]; omega
      · simp only [P] at h; omega
    have hw := wc_succ k (L + 1) m (by omega) hpar hLk
    simp only [refLog, hR, hH, hQ, ite_true, ite_false, List.append_nil, hw]
    rw [if_neg (by omega), if_pos hpar]
    simp
  | C m =>
    simp only [Valid] at hv
    simp only [Mlt, not_and, not_lt] at h1
    have hm : L + 1 ≤ m := h1 hv.1
    have hR : R1 k (L + 1) (C m) := by simp [R1, H12, Mlt, P]; omega
    have hH : H12 k (L + 1) (C m) := hR.1
    rcases Nat.lt_or_ge (L + 1) m with h | h
    · have hQ : ¬ Q3a k (L + 1) (C m) := by simp [Q3a, CC]; omega
      simp [refLog, hR, hH, hQ, cr_succ, show m ≠ L by omega, show m ≠ L + 1 by omega]
    · have hm' : m = L + 1 := by omega
      subst hm'
      have hQ : Q3a k (L + 1) (C (L + 1)) := by simp [Q3a, CC, Mlt, P]
      simp [refLog, hR, hH, hQ, cr_succ]

lemma sJ_zero (w : Blk → ℕ) (hw : ∀ m, w (C m) = 0) (X : Blk) :
    sJ k rd w 0 X = pre k rd k X ++ W (w X) := by
  cases X with
  | B m => simp [sJ]
  | C m => simp [sJ, cr, pre_C, hw, W]

/-- Before read `L` of `pr_{L+2}^C`: blocks heard by rounds 1, 2 of read `L`. -/
lemma sJ_H12 (L : ℕ) (hL : 1 ≤ L) (hLk : L + 1 ≤ k) (X : Blk) (hv : Valid k X) (h : H12 k L X)
    (hI : ¬ Idx (L - 1) X) : sJ k rd (wc k (L + 1)) (L - 1) X = refLog k rd (L - 1) X := by
  cases X with
  | B m =>
    simp only [Valid] at hv
    simp only [H12, Mlt, P, not_or, not_and] at h
    have hm : m ≠ L - 1 := fun h' => hI (Or.inl (by rw [h']))
    have hpar : m % 2 = L % 2 := by
      rcases Nat.lt_or_ge m (L + 1) with h' | h'
      · omega
      · have := h.2 h' hv; omega
    have hw := wc_succ k L m (by omega) hpar hLk
    have hL1 : L - 1 + 1 = L := by omega
    simp only [sJ, refLog, show ¬ m < L - 1 by omega, ite_false, hw, hL1]
    rw [if_neg (by omega)]; simp
  | C m =>
    simp only [Valid] at hv
    simp only [H12, Mlt, P, not_or, not_and] at h
    have hm : m ≠ L - 1 := fun h' => hI (Or.inr (by rw [h']))
    simp [sJ, refLog, hm, show ¬ m < L - 1 by have := h.1 hv.1; omega]

/-- Read `k` of `Δpr_k`: the blocks it hears. -/
lemma sJ_last (hk : 1 ≤ k) (X : Blk) (hv : Valid k X) (h : H12 k k X) (hI : ¬ Idx (k - 1) X) :
    sJ k rd (fun _ => 0) (k - 1) X = refLog k rd (k - 1) X := by
  cases X with
  | B m =>
    simp only [Valid] at hv
    simp only [H12, Mlt, P, not_or, not_and] at h
    have hm : m ≠ k - 1 := fun h' => hI (Or.inl (by rw [h']))
    have hmk : m = k := by
      rcases Nat.lt_or_ge m (k + 1) with h' | h'
      · omega
      · have := h.2 h' hv; omega
    subst hmk
    have hk1 : m - 1 + 1 = m := by omega
    simp only [sJ, refLog, show ¬ m < m - 1 by omega, ite_false, wc, show m ≠ 0 by omega, hk1]
    simp [show ¬ (m % 2 = (m - 1) % 2) by omega]
  | C m =>
    simp only [Valid] at hv
    simp only [H12, Mlt, P, not_or, not_and] at h
    have hm : m ≠ k - 1 := fun h' => hI (Or.inr (by rw [h']))
    simp [sJ, refLog, hm, show ¬ m < k - 1 by have := h.1 hv.1; omega]

lemma not_hook {mal : Blk → Prop} {L : ℕ} {X : Blk} (hL : 1 ≤ L) (hv : Valid k X) (h : ¬ Mlt L X) :
    ¬ hook mal L X := by
  rintro ⟨hI | hI, -⟩ <;> subst hI <;> simp only [Valid] at hv <;> simp only [Mlt] at h <;> omega

/-! ### The runs -/

/-- The instance assignment of all runs: reader `rd l` performs read `l`. -/
noncomputable def instN : Cl Rd → Inst Rd
  | .w => wi
  | .r x => (.r x, if h : ∃ l, 1 ≤ l ∧ l ≤ k ∧ rd l = x then Classical.choose h else 0)

lemma instN_fst (c : Cl Rd) : (instN k rd c).1 = c := by cases c <;> rfl

lemma instN_rc (hrd : RdInj k rd) (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ k) :
    instN k rd (rc rd l) = ri rd l := by
  have hex : ∃ l', 1 ≤ l' ∧ l' ≤ k ∧ rd l' = rd l := ⟨l, h1, h2, rfl⟩
  have hc := Classical.choose_spec hex
  have : Classical.choose hex = l := hrd _ _ hc.1 hc.2.1 h1 h2 hc.2.2
  simp only [instN, rc, ri, dif_pos hex, this]

/-- The malicious objects of `pr_l^C`: `M_{l-3} ∪ P_l`. -/
def FC (l : ℕ) : Finset Obj := Finset.univ.filter fun s => Mlt (l - 2) (blk s) ∨ P k l (blk s)

lemma rc_ne_w (l : ℕ) : (Cl.w : Cl Rd) ≠ rc rd l := by simp [rc]

/-- The prefix of `pr_l^C` (`l ≥ 2`) up to the complete read `l - 1`: `prinit` (read `l` replaced
by forging), `wr^{k-l+1}`, the incomplete reads `1..l-3` (`inc2`) and `l - 2` (`inc3`). -/
theorem pre_full (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hrd : RdInj k rd) (hb : v₁ ≠ bot) (l : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) :
    ∃ σ C h, cx k os blk rd v₁ bot t (FC k blk l) (instN k rd) (Cfg.init bot) σ = some (C, h) ∧
      HEv.invW v₁ ∈ h ∧ (∀ s, ¬ Mlt (l - 2) (blk s) → C.log s = refLog k rd (l - 2) (blk s)) ∧
      Started k os blk rd C (l - 1) ∧ Fresh C (rc rd l) := by
  set F := FC k blk l
  set inst := instN k rd
  have hinst : ∀ l', 1 ≤ l' → l' ≤ k → inst (rc rd l') = ri rd l' := instN_rc k rd hrd
  have hF : ∀ s, (Mlt (l - 2) (blk s) ∨ P k l (blk s)) → s ∈ F := fun s h => by simp [F, FC, h]
  obtain ⟨C1, e1, hlog1, hst1, hfr1⟩ := pinit_spec k os blk rd v₁ bot t F inst hos hall hrd hinst l
    (fun _ s h => hF s (Or.inr h)) k le_rfl
  obtain ⟨C2, e2, hlog2, hfr2⟩ := wrP_spec k os blk rd v₁ bot t F inst hk hos hall hfit hb rfl C1
    (hfr1 _ fun l' _ _ _ => rc_ne_w rd l') hlog1 (l - 1) (by omega) (by omega)
  have e12 := cexec_append_some k 3 _ v₁ bot inst t F e1 e2
  have hfrl : Fresh C2 (rc rd l) := fresh_of_cst (hfr2 _ (rc_ne_w rd l).symm)
    (hfr1 _ fun l' h1 h2 h3 => rc_ne k rd hrd (by omega) hlk h1 h2 (Ne.symm h3))
  have hstC2 : ∀ j, 1 ≤ j → j < l → Started k os blk rd C2 j := fun j h1 h2 =>
    started_of_cst k os blk rd (hfr2 _ (rc_ne_w rd j).symm) (hst1 j h1 (by omega) (by omega))
  rcases Nat.lt_or_ge l 3 with hl3 | hl3
  · -- `l = 2`
    have hl2 : l = 2 := by omega
    subst hl2
    refine ⟨_, C2, _, e12, by simp, fun s _ => ?_, hstC2 1 le_rfl (by omega), hfrl⟩
    rw [hlog2, refLog_zero]
  · -- `l ≥ 3`
    set mal := fun X => Mlt (l - 2) X ∨ P k l X with hmal
    obtain ⟨C3, e3, hlog3, hfr3⟩ := loop_spec k os blk rd v₁ bot t F inst hos hall hfit hrd hinst mal
      hF (wc k (l - 1)) C2 (fun s => by rw [hlog2, sJ_zero k rd _ (fun m => rfl)]) (l - 3) (by omega)
      (fun j h1 h2 X hv hI => by
        left
        rcases hI with rfl | rfl <;> simp only [Valid] at hv <;> simp only [Mlt] <;> omega)
      (fun j h1 h2 => hstC2 j h1 (by omega))
    have hst3 : Started k os blk rd C3 (l - 2) := started_of_cst k os blk rd
      (hfr3 _ fun j h1 h2 => rc_ne k rd hrd (by omega) (by omega) h1 (by omega) (by omega))
      (hstC2 _ (by omega) (by omega))
    obtain ⟨C4, e4, hlog4, -, -, -, -, -, hfr4⟩ := inc3_spec k os blk rd v₁ bot t F inst hos hall hfit
      (l - 2) (by omega) (by omega) (hinst _ (by omega) (by omega)) (hook mal (l - 2))
      (fun s h => hF s h.2) C3 hst3
      (fun s h1 h2 => by
        rw [hlog3, show l - 3 = l - 2 - 1 by omega, show l - 1 = l - 2 + 1 by omega]
        exact sJ_H12 k rd (l - 2) (by omega) (by omega) _ (hfit.valid s) h1
          (fun hI => h2 ⟨hI, by
            left; rcases hI with h | h <;> rw [h] <;> have := hfit.valid s <;> rw [h] at this <;>
              simp only [Valid] at this <;> simp only [Mlt] <;> omega⟩))
    have e1234 := cexec_append_some k 3 _ v₁ bot inst t F
      (cexec_append_some k 3 _ v₁ bot inst t F e12 e3) e4
    have hne : ∀ c, c = rc rd (l - 1) ∨ c = rc rd l →
        (∀ j, 1 ≤ j → j ≤ l - 3 → c ≠ rc rd j) ∧ c ≠ rc rd (l - 2) := by
      rintro c (rfl | rfl)
      · exact ⟨fun j h1 h2 => rc_ne k rd hrd (by omega) (by omega) h1 (by omega) (by omega),
          rc_ne k rd hrd (by omega) (by omega) (by omega) (by omega) (by omega)⟩
      · exact ⟨fun j h1 h2 => rc_ne k rd hrd (by omega) hlk h1 (by omega) (by omega),
          rc_ne k rd hrd (by omega) hlk (by omega) (by omega) (by omega)⟩
    refine ⟨_, C4, _, e1234, by simp, fun s hs => ?_, ?_, ?_⟩
    · have hv := hfit.valid s
      rw [hlog4, if_neg (not_hook k (by omega) hv hs), hlog3]
      by_cases hP : P k (l - 2 + 1) (blk s)
      · have h1 : ¬ H12 k (l - 2) (blk s) := fun h => h (Or.inr hP)
        have h2 : ¬ R1 k (l - 2) (blk s) := fun h => h1 h.1
        have h3 : ¬ Q3a k (l - 2) (blk s) := fun h => h1 (Q3a_H12 k h)
        simp only [h1, h2, h3, ite_false, List.append_nil]
        rcases hX : blk s with m | m
        · rw [hX] at hP hs
          simp only [P] at hP
          simp only [Mlt] at hs
          rw [refLog_P k rd (l - 2) m (by omega)]
          simp [sJ, show ¬ m < l - 3 by omega, show l - 2 + 1 = l - 1 by omega]
        · rw [hX] at hP; simp [P] at hP
      · rw [show l - 3 = l - 2 - 1 by omega, show l - 1 = l - 2 + 1 by omega,
          sJ_H12 k rd (l - 2) (by omega) (by omega) _ hv
          (fun h => h.elim (fun h' => hs (by
            revert h'; rcases blk s with m | m <;> simp [Mlt] <;> omega)) hP)
          (fun hI => (not_hook k (mal := fun _ => True) (by omega) hv hs) ⟨hI, trivial⟩)]
        exact refLog_next k rd (l - 2) (by omega) (by omega) _ hv hs hP
    · exact started_of_cst k os blk rd
        (by rw [hfr4 _ (hne _ (Or.inl rfl)).2, hfr3 _ (hne _ (Or.inl rfl)).1]) (hstC2 _ (by omega) (by omega))
    · exact fresh_of_cst (by rw [hfr4 _ (hne _ (Or.inr rfl)).2, hfr3 _ (hne _ (Or.inr rfl)).1]) hfrl

/-- `pr_l^C` (`2 ≤ l ≤ k`): the prefix, the complete read `l - 1`, then the complete read `l`
(started by the forging of `P_l`). -/
theorem prC_succ (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hrd : RdInj k rd) (hb : v₁ ≠ bot) (l : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) :
    ∃ σ C h, cx k os blk rd v₁ bot t (FC k blk l) (instN k rd) (Cfg.init bot) σ =
        some (C, h ++ [.retR (rd (l - 1)) bot, .invR (rd l), .retR (rd l) bot]) ∧
      HEv.invW v₁ ∈ h := by
  set F := FC k blk l
  set inst := instN k rd
  have hinst : ∀ l', 1 ≤ l' → l' ≤ k → inst (rc rd l') = ri rd l' := instN_rc k rd hrd
  have hF : ∀ s, (Mlt (l - 2) (blk s) ∨ P k l (blk s)) → s ∈ F := fun s h => by simp [F, FC, h]
  set mal := fun X => Mlt (l - 2) X ∨ P k l X with hmal
  obtain ⟨σ, C, h, e, hw, hlog, hst, hfr⟩ := pre_full k os blk rd v₁ bot t hk hos hall hfit hrd hb l hl hlk
  -- the complete read `l - 1`
  obtain ⟨C5, e5, hlog5, hfr5⟩ := full_spec k os blk rd v₁ bot t F inst hos hall hfit (l - 1)
    (by omega) (by omega) (hinst _ (by omega) (by omega)) (hook mal (l - 1)) (fun s h => hF s h.2)
    C hst (fun s hs _ => by
      rw [show l - 1 - 1 = l - 2 by omega]
      refine hlog s fun hM => ?_
      rcases hs with hs | hs
      · exact hs (Or.inl (by rwa [show l - 1 - 1 = l - 2 by omega]))
      · exact hs.1 (by rwa [show l - 1 - 1 = l - 2 by omega]))
  have hlog5' : ∀ s, ¬ Mlt (l - 1) (blk s) → ¬ P k l (blk s) →
      C5.log s = refLog k rd (l - 1) (blk s) := by
    intro s h1 h2
    have hv := hfit.valid s
    have h1' : ¬ Mlt (l - 2) (blk s) := fun h => h1 (by
      revert h; rcases blk s with m | m <;> simp [Mlt] <;> omega)
    have hQ : ¬ Q3b k (l - 1) (blk s) := fun h => h2 (by
      have := h.2.1; rwa [show l - 1 + 1 = l by omega] at this)
    rw [hlog5, if_neg (not_hook k (by omega) hv h1),
      hlog s h1', if_neg hQ, List.append_nil, show l - 2 = l - 1 - 1 by omega]
    exact refLog_next k rd (l - 1) (by omega) (by omega) _ hv h1
      (by rwa [show l - 1 + 1 = l by omega])
  -- the start of read `l`
  obtain ⟨C6, e6, hlog6, hst6, hfr6⟩ := rdStart_spec k os blk rd v₁ bot t F inst hos hall l (by omega)
    (hinst l (by omega) hlk) (fun s h => hF s (Or.inr h)) C5
    (fresh_of_cst (hfr5 _ (rc_ne k rd hrd (by omega) hlk (by omega) (by omega) (by omega))) hfr)
  -- the complete read `l`
  obtain ⟨C7, e7, -, -⟩ := full_spec k os blk rd v₁ bot t F inst hos hall hfit l (by omega) hlk
    (hinst l (by omega) hlk) (hook mal l) (fun s h => hF s h.2) C6 hst6 (fun s hs _ => by
      rw [hlog6]
      split_ifs with hP
      · rfl
      · refine hlog5' s (fun hM => ?_) hP
        rcases hs with hs | hs
        · exact hs (Or.inl hM)
        · exact hs.1 hM)
  have := cexec_append_some k 3 _ v₁ bot inst t F
    (cexec_append_some k 3 _ v₁ bot inst t F (cexec_append_some k 3 _ v₁ bot inst t F e e5) e6) e7
  exact ⟨_, C7, h, this.trans (by simp), hw⟩

/-- `pr_1^C`: `prinit` (read `1` replaced by the forging of `P_1`), the complete write, then the
complete read `1` (started by the forging of `P_1`). -/
theorem prC_one (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hrd : RdInj k rd) (hb : v₁ ≠ bot) :
    ∃ σ C h, cx k os blk rd v₁ bot t (FC k blk 1) (instN k rd) (Cfg.init bot) σ =
        some (C, h ++ [.retW, .invR (rd 1), .retR (rd 1) bot]) ∧ HEv.invW v₁ ∈ h := by
  set F := FC k blk 1
  set inst := instN k rd
  have hinst : ∀ l', 1 ≤ l' → l' ≤ k → inst (rc rd l') = ri rd l' := instN_rc k rd hrd
  have hF : ∀ s, (Mlt (1 - 2) (blk s) ∨ P k 1 (blk s)) → s ∈ F := fun s h => by simp [F, FC, h]
  obtain ⟨C1, e1, hlog1, -, hfr1⟩ := pinit_spec k os blk rd v₁ bot t F inst hos hall hrd hinst 1
    (fun _ s h => hF s (Or.inr h)) k le_rfl
  obtain ⟨C2, e2, hlog2, -, -, hfr2⟩ := wpre_spec k os blk rd v₁ bot t F inst hk hos hall hfit hb rfl
    C1 (hfr1 _ fun l' _ _ _ => rc_ne_w rd l') hlog1 k le_rfl
  obtain ⟨C3, e3, hlog3, hst3, -⟩ := rdStart_spec k os blk rd v₁ bot t F inst hos hall 1 le_rfl
    (hinst 1 le_rfl hk) (fun s h => hF s (Or.inr h)) C2
    (fresh_of_cst (hfr2 _ (rc_ne_w rd 1).symm) (hfr1 _ fun l' h1 h2 h3 =>
      rc_ne k rd hrd le_rfl hk h1 h2 (by omega)))
  obtain ⟨C4, e4, -, -⟩ := full_spec k os blk rd v₁ bot t F inst hos hall hfit 1 le_rfl hk
    (hinst 1 le_rfl hk) (hook (fun X => Mlt (1 - 2) X ∨ P k 1 X) 1) (fun s h => hF s h.2) C3 hst3
    (fun s _ _ => by
      rw [hlog3]
      split_ifs with hP
      · rfl
      · rw [hlog2, refLog_zero]
        congr 1
        have hv := hfit.valid s
        revert hP hv
        rcases blk s with m | m
        · intro hP hv
          simp only [Valid] at hv
          simp only [P, not_and] at hP
          simp only [isB, ite_true, wc]
          congr 1
          split_ifs <;> omega
        · intro _ _; simp [isB, wc, W])
  have := cexec_append_some k 3 _ v₁ bot inst t F
    (cexec_append_some k 3 _ v₁ bot inst t F (cexec_append_some k 3 _ v₁ bot inst t F e1 e2) e3) e4
  exact ⟨_, C4, piH rd 1 k ++ [.invW v₁], this.trans (by simp), by simp⟩

/-- `Δpr_k`: `prinit`, **no write**, the incomplete reads `1..k-1` (`inc2`) and the complete read
`k`; the malicious set is `M_{k-1}`. -/
theorem dpr (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hfit : Fits k t blk)
    (hrd : RdInj k rd) :
    ∃ σ C h, cx k os blk rd v₁ bot t (Finset.univ.filter fun s => Mlt k (blk s)) (instN k rd)
        (Cfg.init bot) σ = some (C, h ++ [.retR (rd k) bot]) ∧ ∀ v, HEv.invW v ∉ h := by
  set F := Finset.univ.filter fun s => Mlt k (blk s)
  set inst := instN k rd
  have hinst : ∀ l', 1 ≤ l' → l' ≤ k → inst (rc rd l') = ri rd l' := instN_rc k rd hrd
  have hF : ∀ s, Mlt k (blk s) → s ∈ F := fun s h => by simp [F, h]
  have hmal : ∀ X, Valid k X → Idx (k - 1) X → Mlt k X := by
    intro X hv hI; rcases hI with rfl | rfl <;> simp only [Valid] at hv <;> simp only [Mlt] <;> omega
  obtain ⟨C1, e1, hlog1, hst1, -⟩ := pinit_spec k os blk rd v₁ bot t F inst hos hall hrd hinst 0
    (fun h => absurd h (by omega)) k le_rfl
  obtain ⟨C2, e2, hlog2, hfr2⟩ := loop_spec k os blk rd v₁ bot t F inst hos hall hfit hrd hinst
    (Mlt k) hF (fun _ => 0) C1 (fun s => by rw [hlog1, sJ_zero k rd _ (fun _ => rfl)]; simp [W])
    (k - 1) (by omega)
    (fun j h1 h2 X hv hI => by
      rcases hI with rfl | rfl <;> simp only [Valid] at hv <;> simp only [Mlt] <;> omega)
    (fun j h1 h2 => hst1 j h1 (by omega) (by omega))
  obtain ⟨C3, e3, -, -⟩ := full_spec k os blk rd v₁ bot t F inst hos hall hfit k hk le_rfl
    (hinst k hk le_rfl) (hook (Mlt k) k) (fun s h => hF s h.2) C2
    (started_of_cst k os blk rd (hfr2 _ fun j h1 h2 => rc_ne k rd hrd hk le_rfl h1 (by omega)
      (by omega)) (hst1 k hk le_rfl (by omega)))
    (fun s hs hh => by
      have hv := hfit.valid s
      rcases hs with hs | hs
      · rw [hlog2]
        exact sJ_last k rd hk _ hv hs (fun hI => hh ⟨hI, hmal _ hv hI⟩)
      · exact absurd hs.2.2 (lt_irrefl k))
  have := cexec_append_some k 3 _ v₁ bot inst t F (cexec_append_some k 3 _ v₁ bot inst t F e1 e2) e3
  exact ⟨_, C3, piH rd 0 k, this.trans (by simp), fun v hv => by simp [piH] at hv⟩

end Runs

omit [DecidableEq Obj] [Fintype Obj] [DecidableEq V] in
lemma before_app {l l' : List (HEv Rd V)} {a c : HEv Rd V} : Before (l ++ a :: c :: l') a c :=
  ⟨l.length, l.length + 1, by omega, by simp, by simp⟩

/-- **Lemma 1 (write lower bound), block form.** Let the objects be partitioned into the blocks
`B₀, …, B_{k+1}`, `C₁, …, C_k` so that every set of objects that is malicious in one of the runs
of the proof, or skipped by one of its terminated rounds, has at most `t` objects (`Fits`; e.g.
the paper's block sizes with `t = t_k`, `S = 3 t_k + 1`). Then, with `k` distinct readers, no
protocol whose writes take `k ≥ 1` rounds and whose reads take three rounds implements an atomic
SWMR register tolerating `t` malicious objects. -/
theorem write_lb {Msg Rep : Type} (P : Proto Obj Rd V Msg Rep) (k : ℕ) (hk : 1 ≤ k)
    (hK : P.K = k) (hN : P.N = 3) (t : ℕ) (os : List Obj) (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (blk : Obj → Blk) (hfit : Fits k t blk)
    (rd : ℕ → Rd) (hrd : ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → rd i = rd j → i = j)
    (v₁ bot : V) (hb : v₁ ≠ bot) : ¬ P.Atomic t bot := by
  intro hP
  subst hK
  set k := P.K with hk'
  obtain ⟨M, hM⟩ := exists_isCanon P (T k os blk rd) Prod.fst v₁ (rank k) (rank_ok k os blk rd)
  set inst := instN k rd
  let cv : ℕ → V := fun l => cret P M (T k os blk rd) inst (rd l)
  have hFC : ∀ l, 1 ≤ l → l ≤ k → (FC k blk l).card ≤ t := fun l h1 h2 => by
    have := hfit.b l h1 (by omega); unfold nBlk at this; exact this
  -- `pr_1^C`: read 1 succeeds the complete write
  have step1 : cv 1 = v₁ := by
    obtain ⟨σ, C, h, e, hw⟩ := prC_one k os blk rd v₁ bot t hk hos hall hfit hrd hb
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot inst t hP _ (hFC 1 le_rfl hk) hM
      (instN_fst k rd) σ C _ (by rw [hN]; exact e)
    exact cret_of_after_write hA (List.mem_append_left _ hw) (x := bot) (by simp) before_app
  -- `pr_l^C`: read `l` succeeds read `l - 1`
  have stepS : ∀ l, 2 ≤ l → l ≤ k → cv (l - 1) = v₁ → cv l = v₁ := by
    intro l hl hlk ih
    obtain ⟨σ, C, h, e, hw⟩ := prC_succ k os blk rd v₁ bot t hk hos hall hfit hrd hb l hl hlk
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot inst t hP _ (hFC l (by omega) hlk) hM
      (instN_fst k rd) σ C _ (by rw [hN]; exact e)
    exact cret_of_after_read hA hb (List.mem_append_left _ hw) (x' := bot) (by simp) ih (x := bot)
      (by simp) before_app
  -- `Δpr_k`: no write, so read `k` returns `⊥`
  have final : cv k = bot := by
    obtain ⟨σ, C, h, e, hw⟩ := dpr k os blk rd v₁ bot t hk hos hall hfit hrd
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot inst t hP _
      (by have := hfit.a; unfold nBlk at this; exact this) hM (instN_fst k rd) σ C _
      (by rw [hN]; exact e)
    exact cret_of_no_write hA (fun v hv => by simp [hw v] at hv) (x := bot) (by simp)
  have all : ∀ l, 1 ≤ l → l ≤ k → cv l = v₁ := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => intro _; exact step1
    | succ l hl ih => intro h; exact stepS (l + 1) (by omega) h (by simpa using ih (by omega))
  exact hb ((all k hk le_rfl).symm.trans final)

end Podc.RobustAtomicStorage.WriteLB
