import Papers.PODC2011.RobustAtomicStorage.Label

/-!
# Proposition 1: the read lower bound (§3)

Objects are split into four blocks `B₀, …, B₃` (the paper's `B₁, …, B₄`, here `Fin 4`) of at most
`t` objects each; four readers `rd 0, …, rd 3`; the write takes `k ≥ 1` rounds and skips `B₃`.

Read instance `n ≥ 1` (the paper's `rd_j` in iteration `i`, `n = 4i + j`) is performed by reader
`rd (b n)`, `b n = (n - 1) mod 4`; its round 1 skips block `b n + 1`, its round 2 skips block `b n`.
The runs of the paper (`pr_n`, `Δpr_n`) are label runs here:
* `Δpr_n` = write prefix `wr^{k - n/4}` whose last round reaches the blocks `≥ n mod 4`, then the
  incomplete read `n - 2` (round 1 reaches block `b (n-2)`), the incomplete read `n - 1` (block
  `b n + 1` is malicious and forges its state `σ^r_{n-2}`; round 1 terminated, round 2 reaches
  blocks `b n + 2`, `b n + 1`), and the complete read `n`;
* `pr_{n+1}` = `Δpr_n` followed by the complete read `n + 1`, where block `b (n+1)` is malicious and
  forges the state `σ_{k-i-1}` (`W (A (n+1) (b (n+1)))`).

All rounds of instance `n` see the same transcript in `pr_n` and `Δpr_n`; `L n β` is the log of
block `β` when read `n` starts in `pr_n`. Block `β` has received `A n β = k - ⌊(n+3-β)/4⌋` write
rounds (`0` for `β = 3`).
-/

set_option linter.unusedSectionVars false

namespace Podc.RobustAtomicStorage.ReadLB

open Classical

variable {Obj Rd V : Type} [DecidableEq Obj] [DecidableEq Rd] [Fintype Obj] [DecidableEq V]

section Defs

variable (k : ℕ) (os : List Obj) (blk : Obj → Fin 4) (rd : Fin 4 → Rd)

/-- Block skipped... the block index of read instance `n`: `(n - 1) mod 4`. -/
def b (n : ℕ) : Fin 4 := ⟨(n + 3) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The client performing read instance `n`. -/
def rc (n : ℕ) : Cl Rd := .r (rd (b n))

/-- The instance (client, index) of read `n`. -/
def ri (n : ℕ) : Inst Rd := (rc rd n, n)

/-- The writer's instance. -/
def wi : Inst Rd := (.w, 0)

/-- Label of round `q` of read instance `m` in a log (absent for `m = 0`). -/
def rl (m q : ℕ) : List (Cl Rd × Lab (Inst Rd)) :=
  if 1 ≤ m then [(rc rd m, (ri rd m, q))] else []

/-- Log of an object after the first `m` write rounds. -/
def W (m : ℕ) : List (Cl Rd × Lab (Inst Rd)) :=
  (List.range m).map fun p => (.w, (wi, p + 1))

/-- Number of write rounds received by block `β` in `Δpr_n` (and in `pr_{n+1}`, except at
`b (n+1)`). -/
def A (n : ℕ) (β : Fin 4) : ℕ := if β = 3 then 0 else k - (n + 3 - β) / 4

/-- Position of block `β` relative to read instance `n`. -/
def off (n : ℕ) (β : Fin 4) : ℕ := ((β : ℕ) + 4 - b n) % 4

/-- Log of block `β` when read instance `n` starts (in `pr_n`, before forging). -/
def L (n : ℕ) (β : Fin 4) : List (Cl Rd × Lab (Inst Rd)) :=
  W (A k n β) ++
    if off n β = 0 then []
    else if off n β = 1 then
      rl rd (n - 3) 1 ++ rl rd (n - 2) 1 ++ rl rd (n - 2) 2 ++ rl rd (n - 1) 1 ++ rl rd (n - 1) 2
    else if off n β = 2 then rl rd (n - 2) 1 ++ rl rd (n - 1) 1 ++ rl rd (n - 1) 2
    else rl rd (n - 1) 1

/-- Replies of an object of block `blk s` in round 2 of read `n`. -/
def ents2 (n : ℕ) (s : Obj) : View Obj (LRep Rd (Inst Rd)) :=
  if off n (blk s) = 1 then
    [(s, ((ri rd n, 1), L k rd n (blk s))), (s, ((ri rd n, 2), L k rd n (blk s) ++ rl rd n 1))]
  else [(s, ((ri rd n, 2), L k rd n (blk s) ++ rl rd n 1))]

/-- Objects of the blocks satisfying `p`, in the order of `os`. -/
def objs (p : Fin 4 → Prop) [DecidablePred p] : List Obj := os.filter fun s => p (blk s)

/-- The canonical transcripts. -/
def T : Lab (Inst Rd) → View Obj (LRep Rd (Inst Rd))
  | ((.w, 0), q) => (objs os blk (· ≠ 3)).map fun s => (s, ((wi, q), W (q - 1)))
  | ((.r _, n), 1) =>
    if 1 ≤ n then (objs os blk fun β => off n β ≠ 1).map fun s => (s, ((ri rd n, 1), L k rd n (blk s)))
    else []
  | ((.r _, n), 2) =>
    if 1 ≤ n then (objs os blk fun β => off n β ≠ 0).flatMap (ents2 k blk rd n) else []
  | _ => []

/-- Rank of labels: blind first rounds `0`; the writer's rounds before all reads; read instances
in increasing order. -/
def rank (lab : Lab (Inst Rd)) : ℕ := if lab.2 ≤ 1 then 0 else lab.1.2 * (k + 3) + lab.2

end Defs

section Rank

variable (k : ℕ) (os : List Obj) (blk : Obj → Fin 4) (rd : Fin 4 → Rd)

lemma rank_W {m : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (W m).map Prod.snd) : rank k l ≤ m := by
  simp only [W, List.map_map, List.mem_map, List.mem_range, Function.comp] at h
  obtain ⟨p, hp, rfl⟩ := h
  simp only [rank, wi]; (try split_ifs) <;> omega

lemma rank_rl {m q : ℕ} {l : Lab (Inst Rd)} (h : l ∈ (rl rd m q).map Prod.snd) :
    rank k l ≤ m * (k + 3) + q := by
  simp only [rl] at h
  split_ifs at h
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    subst h; simp only [rank, ri]; split_ifs <;> omega
  · simp at h

lemma rank_L {n : ℕ} (hn : 1 ≤ n) (β : Fin 4) {l : Lab (Inst Rd)} (h : l ∈ (L k rd n β).map Prod.snd) :
    rank k l ≤ n * (k + 3) := by
  have hk : k ≤ n * (k + 3) := by nlinarith
  have h1 : (n - 1) * (k + 3) + 2 ≤ n * (k + 3) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, add_mul, one_mul]; omega
  have h2 : (n - 2) * (k + 3) + 2 ≤ n * (k + 3) :=
    le_trans (by gcongr <;> omega) h1
  have h3 : (n - 3) * (k + 3) + 1 ≤ n * (k + 3) :=
    le_trans (by gcongr <;> omega) h1
  simp only [L, List.map_append, List.mem_append] at h
  rcases h with h | h
  · exact (rank_W k h).trans (by unfold A; split_ifs <;> omega)
  · split_ifs at h <;>
    (try simp only [List.map_append, List.mem_append, List.map_nil, List.not_mem_nil] at h) <;>
    (repeat' rcases h with h | h) <;>
    first
    | exact False.elim h
    | exact (rank_rl k rd h).trans (by omega)

lemma labs_T (i : Inst Rd) (p : ℕ) (l : Lab (Inst Rd)) (hl : l ∈ labsV (T k os blk rd (i, p))) :
    rank k l ≤ i.2 * (k + 3) + p := by
  obtain ⟨c, n⟩ := i
  simp only [labsV, List.mem_flatMap] at hl
  obtain ⟨e, he, hl⟩ := hl
  rcases c with _ | x
  · rcases n with _ | n
    · simp only [T, List.mem_map] at he
      obtain ⟨s, -, rfl⟩ := he
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp only [rank, wi]; split_ifs <;> omega
      · have := rank_W k hl; simp only at this ⊢; omega
    · simp [T] at he
  · rcases p with _ | _ | _ | p
    · simp [T] at he
    · simp only [T] at he
      split_ifs at he with hn
      · simp only [List.mem_map] at he
        obtain ⟨s, -, rfl⟩ := he
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · simp [rank]
        · have := rank_L k rd hn _ hl; simp only at this ⊢; omega
      · simp at he
    · simp only [T] at he
      split_ifs at he with hn
      · simp only [List.mem_flatMap] at he
        obtain ⟨s, -, he⟩ := he
        have hL : ∀ l ∈ (L k rd n (blk s)).map Prod.snd, rank k l ≤ n * (k + 3) + 2 :=
          fun l hl => (rank_L k rd hn _ hl).trans (by omega)
        have hL1 : ∀ l ∈ (L k rd n (blk s) ++ rl rd n 1).map Prod.snd, rank k l ≤ n * (k + 3) + 2 := by
          intro l hl
          simp only [List.map_append, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hL l hl
          · exact (rank_rl k rd hl).trans (by omega)
        simp only [ents2] at he
        split_ifs at he <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he <;>
        (repeat' rcases he with rfl | he) <;>
        simp only [List.mem_cons] at hl <;>
        rcases hl with rfl | hl <;>
        first
        | (simp [rank, ri]; done)
        | exact hL l hl
        | exact hL1 l hl
        | (simp [rank, ri]; omega)
      · simp at he
    · simp [T] at he

theorem rank_ok (i : Inst Rd) (q p : ℕ) (hpq : p + 1 < q) (l : Lab (Inst Rd))
    (hl : l ∈ labsV (T k os blk rd (i, p + 1))) : rank k l < rank k (i, q) := by
  have := labs_T k os blk rd i (p + 1) l hl
  have h2 : rank k (i, q) = i.2 * (k + 3) + q := by simp only [rank]; split_ifs <;> omega
  omega

end Rank

section Runs

variable (k : ℕ) (os : List Obj) (blk : Obj → Fin 4) (rd : Fin 4 → Rd) (v₁ bot : V) (t : ℕ)
  (F : Finset Obj) (inst : Cl Rd → Inst Rd)

omit [Fintype Obj] [DecidableEq V] in
lemma mem_objs (hall : ∀ s, s ∈ os) (p : Fin 4 → Prop) [DecidablePred p] (s : Obj) :
    s ∈ objs os blk p ↔ p (blk s) := by
  simp [objs, hall s]

omit [Fintype Obj] [DecidableEq V] in
lemma nodup_objs (hos : os.Nodup) (p : Fin 4 → Prop) [DecidablePred p] : (objs os blk p).Nodup :=
  hos.filter _

lemma W_succ (m : ℕ) : (W m : List (Cl Rd × Lab (Inst Rd))) ++ [(.w, (wi, m + 1))] = W (m + 1) := by
  simp [W, List.range_succ]

/-- One terminated write round. -/
def wround : List (LEv Obj Rd V (Inst Rd)) :=
  dlvs .w (objs os blk (· ≠ 3)) (fun _ => 1) ++ [.nxt .w]

/-- `write(v₁)` with `r` terminated rounds. -/
def wpre (r : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invW v₁] ++ (List.replicate r (wround os blk)).flatten

/-- The checked execution used throughout this file. -/
noncomputable abbrev cx := cexec k 2 (T k os blk rd) v₁ bot inst t F

theorem wpre_spec (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (hb : v₁ ≠ bot)
    (hiw : inst .w = wi) (r : ℕ) (hr : r ≤ k) :
    ∃ C, cx k os blk rd v₁ bot t F inst (Cfg.init bot) (wpre os blk v₁ r) =
        some (C, [.invW v₁] ++ (if r = k then [.retW] else [])) ∧
      (∀ s, C.log s = if blk s = 3 then [] else W r) ∧
      (∀ s, C.prc s .w = if blk s = 3 then 0 else r) ∧
      (r < k → C.rnd .w = r + 1 ∧ C.done .w = false ∧ (C.past .w).length = r ∧ C.cur .w = []) ∧
      (∀ c, c ≠ .w → Fresh C c) := by
  induction r with
  | zero =>
    refine ⟨{ (Cfg.init bot : LCfg Obj Rd V (Inst Rd)) with
      rnd := Function.update (Cfg.init bot : LCfg Obj Rd V (Inst Rd)).rnd .w 1, wv := v₁ },
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [wpre, List.replicate_zero, List.flatten_nil, List.append_nil]
      dsimp only [cx]
      rw [cexec_invW _ _ _ _ _ _ _ _ _ (by rfl) hb]
      simp; omega
    · intro s; split_ifs <;> rfl
    · intro s; split_ifs <;> rfl
    · intro _; simp [Cfg.init]
    · intro c hc; exact fresh_invW (fresh_init bot c) hc v₁
  | succ r ih =>
    obtain ⟨C, hC, hlog, hprc, hst, hfr⟩ := ih (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hst (by omega)
    have hround := cexec_round k 2 (T k os blk rd) v₁ bot inst t F C .w (objs os blk (· ≠ 3))
      (nodup_objs os blk hos _) (fun _ => 1)
      (fun s hs => by rw [hprc, if_neg ((mem_objs os blk hall _ s).1 hs), h1])
      (by omega) h2 (fun s => blk s ≠ 3) (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
      (by simpa using hblk 3) (by
        rw [h4, h1, List.nil_append, hiw]
        have : ∀ s ∈ objs os blk (· ≠ 3), ents inst C .w s 1 = [(s, ((wi, r + 1), W r))] := by
          intro s hs
          have hs' := (mem_objs os blk hall _ s).1 hs
          simp [ents, newLabs, hiw, hprc, hlog, hs']
        rw [List.flatMap_congr this, ← List.map_eq_flatMap]
        simp [T, wi])
    have hrounds : (LPr (Obj := Obj) k 2 bot inst).rounds .w = k := rfl
    rw [hrounds] at hround
    have hnk : r ≠ k := by omega
    simp only [hnk, if_false, List.append_nil] at hC
    have hall' := cexec_append_some k 2 (T k os blk rd) v₁ bot inst t F hC hround
    set D := dlvRes inst C .w (objs os blk (· ≠ 3)) fun _ => 1 with hD
    have hDr : D.rnd .w = r + 1 := by simp [hD, dlvRes, h1]
    have hDlog : ∀ s, D.log s = if blk s = 3 then [] else W (r + 1) := by
      intro s
      by_cases hs : blk s = 3
      · simp [hD, dlvRes, mem_objs os blk hall, hs, hlog]
      · simp [hD, dlvRes, mem_objs os blk hall, hs, hlog, newLabs, hprc, hiw, ← W_succ]
    have hDprc : ∀ s, D.prc s .w = if blk s = 3 then 0 else r + 1 := by
      intro s
      by_cases hs : blk s = 3 <;> simp [hD, dlvRes, mem_objs os blk hall, hs, hprc]
    refine ⟨nxtRes D .w k, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show wpre os blk v₁ (r + 1) = wpre os blk v₁ r ++ wround os blk by
        simp [wpre, List.replicate_succ', List.flatten_append]]
      dsimp only [cx]
      rw [wround, hall']
      congr 2
      simp only [nxtHist, hDr]
    · intro s; rw [nxtRes_log]; exact hDlog s
    · intro s; rw [nxtRes_prc]; exact hDprc s
    · intro hlt
      have : D.rnd .w ≠ k := by omega
      simp only [nxtRes, this, if_false]
      simp [hD, dlvRes, h1, h2, h3]
    · intro c hc
      exact fresh_nxtRes (fresh_dlvRes inst (hfr c hc) hc _ _) hc _

/-- The write prefix of `Δpr_n`: `m - 1` terminated rounds, round `m` reaches blocks `f ≤ β < 3`. -/
def wrE (m f : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  wpre os blk v₁ (m - 1) ++ dlvs .w (objs os blk fun β => f ≤ β.val ∧ β ≠ 3) (fun _ => 1)

theorem wrE_spec (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (hb : v₁ ≠ bot)
    (hiw : inst .w = wi) (m f : ℕ) (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    ∃ C, cx k os blk rd v₁ bot t F inst (Cfg.init bot) (wrE os blk v₁ m f) = some (C, [.invW v₁]) ∧
      (∀ s, C.log s = if blk s = 3 then [] else if f ≤ (blk s).val then W m else W (m - 1)) ∧
      (∀ c, c ≠ .w → Fresh C c) := by
  obtain ⟨C, hC, hlog, hprc, hst, hfr⟩ :=
    wpre_spec k os blk rd v₁ bot t F inst hk hos hall hblk hb hiw (m - 1) (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := hst (by omega)
  have hnk : m - 1 ≠ k := by omega
  simp only [hnk, if_false, List.append_nil] at hC
  have hd := cexec_dlvs k 2 (T k os blk rd) v₁ bot inst t F C .w
    (objs os blk fun β => f ≤ β.val ∧ β ≠ 3) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      rw [hprc, if_neg this.2, h1]) (by omega)
  refine ⟨_, by dsimp only [cx]; rw [wrE]; exact cexec_append_some k 2 _ v₁ bot inst t F hC hd, ?_, ?_⟩
  · intro s
    by_cases h3' : blk s = 3
    · simp [dlvRes, mem_objs os blk hall, h3', hlog]
    · by_cases hf : f ≤ (blk s).val
      · simp only [dlvRes, mem_objs os blk hall, h3', hf, ne_eq, not_false_eq_true, and_self,
          if_true, if_false, hlog, newLabs, hprc, hiw, List.range_one, List.map_cons, List.map_nil]
        rw [show m = m - 1 + 1 by omega, ← W_succ]; simp
      · simp [dlvRes, mem_objs os blk hall, h3', hf, hlog]
  · intro c hc; exact fresh_dlvRes inst (hfr c hc) hc _ _

/-- The complete write. -/
theorem wfull_spec (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (hb : v₁ ≠ bot)
    (hiw : inst .w = wi) :
    ∃ C, cx k os blk rd v₁ bot t F inst (Cfg.init bot) (wpre os blk v₁ k) =
        some (C, [.invW v₁, .retW]) ∧
      (∀ s, C.log s = if blk s = 3 then [] else W k) ∧ (∀ c, c ≠ .w → Fresh C c) := by
  obtain ⟨C, hC, hlog, -, -, hfr⟩ :=
    wpre_spec k os blk rd v₁ bot t F inst hk hos hall hblk hb hiw k le_rfl
  exact ⟨C, by simpa using hC, hlog, hfr⟩

/-! ### Arithmetic of blocks and offsets -/

lemma b_val (n : ℕ) : (b n).val = (n + 3) % 4 := rfl

lemma off_eq_iff (n : ℕ) (β : Fin 4) (j : ℕ) (hj : j < 4) :
    off n β = j ↔ β.val = ((n + 3) % 4 + j) % 4 := by
  unfold off; rw [b_val]; have := β.isLt; omega

lemma card_off (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (n j : ℕ) (hj : j < 4) :
    (Finset.univ.filter fun s => off n (blk s) = j).card ≤ t := by
  have := hblk ⟨((n + 3) % 4 + j) % 4, Nat.mod_lt _ (by norm_num)⟩
  convert this using 3
  rw [off_eq_iff n _ j hj, Fin.ext_iff]

lemma off_lt (n : ℕ) (β : Fin 4) : off n β < 4 := Nat.mod_lt _ (by norm_num)

lemma A_eq (n : ℕ) (β : Fin 4) (hβ : β ≠ 3) (hn : n + 1 ≤ 4 * k) :
    A k n β = if n % 4 ≤ β.val then k - n / 4 else k - n / 4 - 1 := by
  have h3 : β.val ≠ 3 := fun h => hβ (Fin.ext h)
  have := β.isLt
  unfold A; rw [if_neg hβ]; split_ifs <;> omega

lemma rl_pos {m : ℕ} (hm : 1 ≤ m) (q : ℕ) :
    (rl rd m q : List (Cl Rd × Lab (Inst Rd))) = [(rc rd m, (ri rd m, q))] := by
  simp [rl, hm]

/-! ### Read phases -/

/-- The complete read of instance `n`; if `fg`, block `b n` first forges `L n (b n)`. -/
def rdC (n : ℕ) (fg : Bool) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invR (rd (b n))] ++
    (if fg then forges (objs os blk fun β => off n β = 0) (fun s => L k rd n (blk s)) else []) ++
    (dlvs (rc rd n) (objs os blk fun β => off n β ≠ 1) (fun _ => 1) ++ [.nxt (rc rd n)]) ++
    (dlvs (rc rd n) (objs os blk fun β => off n β ≠ 0)
      (fun s => if off n (blk s) = 1 then 2 else 1) ++ [.nxt (rc rd n)])

theorem rdC_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t)
    (n : ℕ) (hn : 1 ≤ n) (fg : Bool) (hinst : inst (rc rd n) = ri rd n)
    (C : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C (rc rd n))
    (hlog : ∀ s, (off n (blk s) ≠ 0 ∨ fg = false) → C.log s = L k rd n (blk s))
    (hF : fg = true → ∀ s, off n (blk s) = 0 → s ∈ F) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (rdC k os blk rd n fg) =
        some (C', [.invR (rd (b n)), .retR (rd (b n)) bot]) ∧
      (∀ s, C'.log s = L k rd n (blk s) ++ rl rd n 1 ++
        (if off n (blk s) ≠ 0 then rl rd n 2 else [])) ∧
      (∀ c', c' ≠ rc rd n → Fresh C c' → Fresh C' c') := by
  have hinst' : inst (rc rd n) = (rc rd n, n) := hinst
  have hri : ri rd n = (rc rd n, n) := rfl
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfr
  -- invocation
  have e1 := cexec_invR k 2 (T k os blk rd) v₁ bot inst t F C (rd (b n)) f1
  set C1 := { C with rnd := Function.update C.rnd (Cl.r (rd (b n))) 1 } with hC1
  -- forging
  set C2 : LCfg Obj Rd V (Inst Rd) :=
    if fg then { C1 with log := fun s =>
      (if s ∈ objs os blk (fun β => off n β = 0) then L k rd n (blk s) else C1.log s) }
    else C1 with hC2
  have e2 : cx k os blk rd v₁ bot t F inst C1
      (if fg then forges (objs os blk fun β => off n β = 0) (fun s => L k rd n (blk s)) else []) =
      some (C2, []) := by
    cases fg
    · simp [hC2, cexec_nil]
    · simp only [if_true, hC2]
      exact cexec_forges k 2 _ v₁ bot inst t F C1 _ _
        (fun s hs => hF rfl s ((mem_objs os blk hall _ s).1 hs))
  have hC2log : ∀ s, C2.log s = L k rd n (blk s) := by
    intro s
    cases fg
    · simpa [hC2, hC1] using hlog s (Or.inr rfl)
    · by_cases h0 : off n (blk s) = 0
      · simp [hC2, mem_objs os blk hall, h0]
      · simpa [hC2, hC1, mem_objs os blk hall, h0] using hlog s (Or.inl h0)
  have hC2c : C2.rnd (rc rd n) = 1 ∧ C2.past (rc rd n) = [] ∧ C2.cur (rc rd n) = [] ∧ C2.done (rc rd n) = false ∧
      ∀ s, C2.prc s (rc rd n) = 0 := by
    refine ⟨by cases fg <;> simp [hC2, hC1, rc], ?_⟩
    cases fg <;> simp [hC2, hC1, f2, f3, f4, f5]
  obtain ⟨g1, g2, g3, g4, g5⟩ := hC2c
  -- round 1
  have e3 := cexec_round k 2 (T k os blk rd) v₁ bot inst t F C2 (rc rd n)
    (objs os blk fun β => off n β ≠ 1) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s _ => by rw [g5, g1]) (by simp [g2, g1]) g4 (fun s => off n (blk s) ≠ 1)
    (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
    (by simpa using card_off blk t hblk n 1 (by norm_num)) (by
      rw [g3, List.nil_append, hinst, g1]
      have : ∀ s ∈ objs os blk (fun β => off n β ≠ 1), ents inst C2 (rc rd n) s 1 =
          [(s, ((ri rd n, 1), L k rd n (blk s)))] := by
        intro s _; simp [ents, newLabs, g5, hC2log, hinst', hri]
      rw [List.flatMap_congr this, ← List.map_eq_flatMap]
      simp [T, ri, rc, hn])
  have hrounds : (LPr (Obj := Obj) k 2 bot inst).rounds (rc rd n) = 2 := by simp [rc, Proto.rounds, LP]
  rw [hrounds] at e3
  set xs1 := objs os blk fun β => off n β ≠ 1 with hxs1
  set D1 := dlvRes inst C2 (rc rd n) xs1 fun _ => 1 with hD1
  have hD1r : D1.rnd (rc rd n) = 1 := by simp [hD1, dlvRes, g1]
  have hH1 : nxtHist bot D1 (rc rd n) 2 = [] := by simp [nxtHist, hD1r]
  rw [hH1] at e3
  set C3 := nxtRes D1 (rc rd n) 2 with hC3
  have hC3' : C3 = { D1 with
      past := Function.update D1.past (rc rd n) (D1.past (rc rd n) ++ [D1.cur (rc rd n)])
      cur := Function.update D1.cur (rc rd n) []
      rnd := Function.update D1.rnd (rc rd n) (D1.rnd (rc rd n) + 1) } := nxtRes_adv D1 (rc rd n) 2 (by omega)
  have h3r : C3.rnd (rc rd n) = 2 := by simp [hC3', hD1r]
  have h3p : (C3.past (rc rd n)).length = 1 := by simp [hC3', hD1, dlvRes, g2]
  have h3c : C3.cur (rc rd n) = [] := by simp [hC3']
  have h3d : C3.done (rc rd n) = false := by simp [hC3', hD1, dlvRes, g4]
  have h3prc : ∀ s, C3.prc s (rc rd n) = if off n (blk s) ≠ 1 then 1 else 0 := by
    intro s; by_cases h : off n (blk s) = 1 <;> simp [hC3', hD1, dlvRes, hxs1, mem_objs os blk hall, h, g5]
  have h3log : ∀ s, C3.log s = if off n (blk s) ≠ 1 then L k rd n (blk s) ++ rl rd n 1
      else L k rd n (blk s) := by
    intro s
    by_cases h : off n (blk s) = 1
    · simp [hC3', hD1, dlvRes, hxs1, mem_objs os blk hall, h, hC2log]
    · simp [hC3', hD1, dlvRes, hxs1, mem_objs os blk hall, h, hC2log, newLabs, g5, hinst,
        rl_pos rd hn, ri]
  -- round 2
  set d2 : Obj → ℕ := fun s => if off n (blk s) = 1 then 2 else 1 with hd2
  have e4 := cexec_round k 2 (T k os blk rd) v₁ bot inst t F C3 (rc rd n)
    (objs os blk fun β => off n β ≠ 0) (nodup_objs os blk hos _) d2
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      rw [h3prc, h3r]; by_cases h : off n (blk s) = 1 <;> simp [hd2, h])
    (by omega) h3d (fun s => off n (blk s) ≠ 0)
    (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
    (by simpa using card_off blk t hblk n 0 (by norm_num)) (by
      rw [h3c, List.nil_append, hinst, h3r]
      have : ∀ s ∈ objs os blk (fun β => off n β ≠ 0), ents inst C3 (rc rd n) s (d2 s) = ents2 k blk rd n s := by
        intro s hs
        have h0 := (mem_objs os blk hall _ s).1 hs
        by_cases h : off n (blk s) = 1
        · simp [ents, ents2, newLabs, hd2, h, h3prc, h3log, hinst', hri, rl_pos rd hn,
            List.range_succ]
        · simp [ents, ents2, newLabs, hd2, h, h3prc, h3log, hinst', hri]
      rw [List.flatMap_congr this]
      simp [T, ri, rc, hn])
  rw [hrounds] at e4
  set D2 := dlvRes inst C3 (rc rd n) (objs os blk fun β => off n β ≠ 0) d2 with hD2
  have hD2r : D2.rnd (rc rd n) = 2 := by simp [hD2, dlvRes, h3r]
  have hH2 : nxtHist bot D2 (rc rd n) 2 = [.retR (rd (b n)) bot] := by
    unfold nxtHist; rw [if_pos hD2r]; rfl
  rw [hH2] at e4
  refine ⟨nxtRes D2 (rc rd n) 2, ?_, ?_, ?_⟩
  · dsimp only [cx]
    have := cexec_append_some k 2 _ v₁ bot inst t F
      (cexec_append_some k 2 _ v₁ bot inst t F (cexec_append_some k 2 _ v₁ bot inst t F e1 e2) e3) e4
    simpa [rdC, List.append_assoc] using this
  · intro s
    rw [nxtRes_log]
    by_cases h0 : off n (blk s) = 0
    · have h1' : off n (blk s) ≠ 1 := by omega
      simp [hD2, dlvRes, mem_objs os blk hall, h0, h3log, h1']
    · by_cases h : off n (blk s) = 1
      · simp [hD2, dlvRes, mem_objs os blk hall, h0, h, h3log, newLabs, hd2, h3prc, hinst',
          rl_pos rd hn, ri, List.range_succ]
      · simp [hD2, dlvRes, mem_objs os blk hall, h0, h, h3log, newLabs, hd2, h3prc, hinst',
          rl_pos rd hn, ri]
  · intro c' hne hfr'
    have a1 : Fresh C1 c' := fresh_invR hfr' (by simpa [rc] using hne)
    have a2 : Fresh C2 c' := by cases fg <;> simp only [hC2, if_true, if_false] <;>
      first | exact a1 | exact fresh_log a1 _
    exact fresh_nxtRes (fresh_dlvRes inst (fresh_nxtRes (fresh_dlvRes inst a2 hne _ _) hne _) hne _ _) hne _

/-- The incomplete read of instance `m` that only reaches block `b m` in round 1. -/
def rdA (m : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invR (rd (b m))] ++ dlvs (rc rd m) (objs os blk (· = b m)) (fun _ => 1)

theorem rdA_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (m : ℕ) (hm : 1 ≤ m)
    (hinst : inst (rc rd m) = ri rd m) (C : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C (rc rd m)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (rdA os blk rd m) = some (C', [.invR (rd (b m))]) ∧
      (∀ s, C'.log s = if blk s = b m then C.log s ++ rl rd m 1 else C.log s) ∧
      (∀ c', c' ≠ rc rd m → Fresh C c' → Fresh C' c') := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfr
  have hinst' : inst (rc rd m) = (rc rd m, m) := hinst
  have e1 := cexec_invR k 2 (T k os blk rd) v₁ bot inst t F C (rd (b m)) f1
  set C1 := { C with rnd := Function.update C.rnd (Cl.r (rd (b m))) 1 } with hC1
  have g1 : C1.rnd (rc rd m) = 1 := by simp [hC1, rc]
  have e2 := cexec_dlvs k 2 (T k os blk rd) v₁ bot inst t F C1 (rc rd m) (objs os blk (· = b m))
    (nodup_objs os blk hos _) (fun _ => 1) (fun s _ => by rw [g1]; simp [hC1, f5])
    (by rw [g1]; simp [hC1, f2])
  refine ⟨_, by dsimp only [cx]; rw [rdA]; exact cexec_append_some k 2 _ v₁ bot inst t F e1 e2, ?_, ?_⟩
  · intro s
    by_cases h : blk s = b m
    · simp [dlvRes, mem_objs os blk hall, h, hC1, newLabs, f5, hinst', rl_pos rd hm, ri]
    · simp [dlvRes, mem_objs os blk hall, h, hC1]
  · intro c' hne hfr'
    exact fresh_dlvRes inst (fresh_invR hfr' (by simpa [rc] using hne)) hne _ _

/-- The incomplete read of instance `m`: block `b m + 2` forges `L m`, round 1 terminates,
round 2 reaches the blocks `b m + 2` and `b m + 3`. -/
def rdB (m : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  [.invR (rd (b m))] ++ forges (objs os blk fun β => off m β = 2) (fun s => L k rd m (blk s)) ++
    (dlvs (rc rd m) (objs os blk fun β => off m β ≠ 1) (fun _ => 1) ++ [.nxt (rc rd m)]) ++
    dlvs (rc rd m) (objs os blk fun β => off m β = 2 ∨ off m β = 3) (fun _ => 1)

theorem rdB_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t)
    (m : ℕ) (hm : 1 ≤ m) (hinst : inst (rc rd m) = ri rd m)
    (C : LCfg Obj Rd V (Inst Rd)) (hfr : Fresh C (rc rd m))
    (hlog : ∀ s, (off m (blk s) = 0 ∨ off m (blk s) = 3) → C.log s = L k rd m (blk s))
    (hF : ∀ s, off m (blk s) = 2 → s ∈ F) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (rdB k os blk rd m) = some (C', [.invR (rd (b m))]) ∧
      (∀ s, C'.log s = if off m (blk s) = 1 then C.log s
        else if off m (blk s) = 0 then L k rd m (blk s) ++ rl rd m 1
        else L k rd m (blk s) ++ rl rd m 1 ++ rl rd m 2) ∧
      (∀ c', c' ≠ rc rd m → Fresh C c' → Fresh C' c') := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfr
  have hinst' : inst (rc rd m) = (rc rd m, m) := hinst
  have hri : ri rd m = (rc rd m, m) := rfl
  have e1 := cexec_invR k 2 (T k os blk rd) v₁ bot inst t F C (rd (b m)) f1
  set C1 := { C with rnd := Function.update C.rnd (Cl.r (rd (b m))) 1 } with hC1
  have e2 := cexec_forges k 2 (T k os blk rd) v₁ bot inst t F C1
    (objs os blk fun β => off m β = 2) (fun s => L k rd m (blk s))
    (fun s hs => hF s ((mem_objs os blk hall _ s).1 hs))
  set C2 := { C1 with log := fun s =>
    (if s ∈ objs os blk (fun β => off m β = 2) then L k rd m (blk s) else C1.log s) } with hC2
  have hC2log : ∀ s, off m (blk s) ≠ 1 → C2.log s = L k rd m (blk s) := by
    intro s h1
    by_cases h2 : off m (blk s) = 2
    · simp [hC2, mem_objs os blk hall, h2]
    · have := off_lt m (blk s)
      simpa [hC2, hC1, mem_objs os blk hall, h2] using hlog s (by omega)
  have g1 : C2.rnd (rc rd m) = 1 := by simp [hC2, hC1, rc]
  have g2 : C2.past (rc rd m) = [] := by simp [hC2, hC1, f2]
  have g3 : C2.cur (rc rd m) = [] := by simp [hC2, hC1, f3]
  have g4 : C2.done (rc rd m) = false := by simp [hC2, hC1, f4]
  have g5 : ∀ s, C2.prc s (rc rd m) = 0 := by simp [hC2, hC1, f5]
  have e3 := cexec_round k 2 (T k os blk rd) v₁ bot inst t F C2 (rc rd m)
    (objs os blk fun β => off m β ≠ 1) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s _ => by rw [g5, g1]) (by simp [g2, g1]) g4 (fun s => off m (blk s) ≠ 1)
    (fun s hs => Or.inl ((mem_objs os blk hall _ s).2 hs))
    (by simpa using card_off blk t hblk m 1 (by norm_num)) (by
      rw [g3, List.nil_append, hinst, g1]
      have : ∀ s ∈ objs os blk (fun β => off m β ≠ 1), ents inst C2 (rc rd m) s 1 =
          [(s, ((ri rd m, 1), L k rd m (blk s)))] := by
        intro s hs
        simp [ents, newLabs, g5, hC2log s ((mem_objs os blk hall _ s).1 hs), hinst', hri]
      rw [List.flatMap_congr this, ← List.map_eq_flatMap]
      simp [T, ri, rc, hm])
  have hrounds : (LPr (Obj := Obj) k 2 bot inst).rounds (rc rd m) = 2 := by
    simp [rc, Proto.rounds, LP]
  rw [hrounds] at e3
  set D1 := dlvRes inst C2 (rc rd m) (objs os blk fun β => off m β ≠ 1) fun _ => 1 with hD1
  have hD1r : D1.rnd (rc rd m) = 1 := by simp [hD1, dlvRes, g1]
  have hH1 : nxtHist bot D1 (rc rd m) 2 = [] := by simp [nxtHist, hD1r]
  rw [hH1] at e3
  set C3 := nxtRes D1 (rc rd m) 2 with hC3
  have hC3' : C3 = { D1 with
      past := Function.update D1.past (rc rd m) (D1.past (rc rd m) ++ [D1.cur (rc rd m)])
      cur := Function.update D1.cur (rc rd m) []
      rnd := Function.update D1.rnd (rc rd m) (D1.rnd (rc rd m) + 1) } :=
    nxtRes_adv D1 (rc rd m) 2 (by omega)
  have h3r : C3.rnd (rc rd m) = 2 := by simp [hC3', hD1r]
  have h3p : (C3.past (rc rd m)).length = 1 := by simp [hC3', hD1, dlvRes, g2]
  have h3prc : ∀ s, C3.prc s (rc rd m) = if off m (blk s) ≠ 1 then 1 else 0 := by
    intro s; by_cases h : off m (blk s) = 1 <;> simp [hC3', hD1, dlvRes, mem_objs os blk hall, h, g5]
  have h3log : ∀ s, C3.log s = if off m (blk s) ≠ 1 then L k rd m (blk s) ++ rl rd m 1
      else C.log s := by
    intro s
    by_cases h : off m (blk s) = 1
    · have h2 : off m (blk s) ≠ 2 := by omega
      simp [hC3', hD1, dlvRes, mem_objs os blk hall, h, hC2, hC1, h2]
    · simp [hC3', hD1, dlvRes, mem_objs os blk hall, h, hC2log s h, newLabs, g5, hinst',
        rl_pos rd hm, hri]
  have e4 := cexec_dlvs k 2 (T k os blk rd) v₁ bot inst t F C3 (rc rd m)
    (objs os blk fun β => off m β = 2 ∨ off m β = 3) (nodup_objs os blk hos _) (fun _ => 1)
    (fun s hs => by
      have := (mem_objs os blk hall _ s).1 hs
      rw [h3prc, h3r, if_pos (by omega)]) (by omega)
  refine ⟨dlvRes inst C3 (rc rd m) (objs os blk fun β => off m β = 2 ∨ off m β = 3) (fun _ => 1),
    ?_, ?_, ?_⟩
  · dsimp only [cx]
    have := cexec_append_some k 2 _ v₁ bot inst t F
      (cexec_append_some k 2 _ v₁ bot inst t F (cexec_append_some k 2 _ v₁ bot inst t F e1 e2) e3) e4
    simpa [rdB, List.append_assoc] using this
  · intro s
    have hlt := off_lt m (blk s)
    by_cases h1 : off m (blk s) = 1
    · have : ¬ (off m (blk s) = 2 ∨ off m (blk s) = 3) := by omega
      simp [dlvRes, mem_objs os blk hall, this, h3log, h1]
    · by_cases h0 : off m (blk s) = 0
      · have : ¬ (off m (blk s) = 2 ∨ off m (blk s) = 3) := by omega
        simp [dlvRes, mem_objs os blk hall, this, h3log, h1, h0]
      · have : off m (blk s) = 2 ∨ off m (blk s) = 3 := by omega
        simp [dlvRes, mem_objs os blk hall, this, h3log, h1, h0, newLabs, h3prc, hinst',
          rl_pos rd hm, hri]
  · intro c' hne hfr'
    have a1 : Fresh C1 c' := fresh_invR hfr' (by simpa [rc] using hne)
    exact fresh_dlvRes inst (fresh_nxtRes (fresh_dlvRes inst (fresh_log a1 _) hne _ _) hne _) hne _ _

/-! ### Consistency of the logs `L` between consecutive instances -/

lemma off_zero_iff (n : ℕ) (β : Fin 4) : off n β = 0 ↔ β = b n := by
  rw [off_eq_iff n β 0 (by norm_num), Fin.ext_iff, b_val]; omega

lemma off_succ (n : ℕ) (β : Fin 4) : off (n + 1) β = (off n β + 3) % 4 := by
  unfold off; rw [b_val, b_val]; have := β.isLt; omega

lemma A_succ (n : ℕ) (β : Fin 4) (hβ : off (n + 1) β ≠ 0) : A k (n + 1) β = A k n β := by
  rw [Ne, off_zero_iff, Fin.ext_iff, b_val] at hβ
  unfold A; split_ifs with h
  · rfl
  · have : β.val ≠ 3 := fun h' => h (Fin.ext h')
    have := β.isLt
    omega

lemma L_off0 (n : ℕ) (β : Fin 4) (h : off n β = 0) : L k rd n β = W (A k n β) := by
  simp [L, h]

lemma L_one (β : Fin 4) : L k rd 1 β = W (A k 1 β) := by
  simp [L, rl]

/-- The log of block `β ≠ b (n+1)` at the end of `Δpr_n` is its log when read `n + 1` starts. -/
lemma L_succ (n : ℕ) (β : Fin 4) (hβ : off (n + 1) β ≠ 0) :
    L k rd (n + 1) β = L k rd n β ++ rl rd n 1 ++ (if off n β ≠ 0 then rl rd n 2 else []) := by
  have hA := A_succ k n β hβ
  have hs := off_succ n β
  have hlt := off_lt n β
  rw [hs] at hβ
  have hn3 : n + 1 - 3 = n - 2 := by omega
  have hn2 : n + 1 - 2 = n - 1 := by omega
  have hn1 : n + 1 - 1 = n := by omega
  unfold L
  rw [hA, hs, hn3, hn2, hn1]
  rcases (by omega : off n β = 0 ∨ off n β = 2 ∨ off n β = 3) with h | h | h <;>
    simp [h]

/-! ### Instance assignment of the runs around read `n` -/

/-- Instances in the runs `Δpr_n`, `pr_{n+1}`: reader `rd β` performs the read instance in
`[n - 3, n]` (or `[n-2, n+1]`) with block index `β`. -/
noncomputable def instN (n : ℕ) : Cl Rd → Inst Rd
  | .w => wi
  | .r x => (.r x, if h : ∃ β, rd β = x then n - (n + 3 - (Classical.choose h).val) % 4 else 0)

lemma instN_fst (n : ℕ) (c : Cl Rd) : (instN rd n c).1 = c := by cases c <;> rfl

lemma instN_rc (hrd : Function.Injective rd) (n m : ℕ) (hm : m ≤ n) (hm3 : n ≤ m + 3) :
    instN rd n (rc rd m) = ri rd m := by
  have hex : ∃ β, rd β = rd (b m) := ⟨_, rfl⟩
  have hc : Classical.choose hex = b m := hrd (Classical.choose_spec hex)
  simp only [instN, rc, ri, dif_pos hex, hc, b_val]
  congr 1
  omega

lemma rc_ne (hrd : Function.Injective rd) {m m' : ℕ} (h : b m ≠ b m') : rc rd m ≠ rc rd m' := by
  intro h'
  simp only [rc, Cl.r.injEq] at h'
  exact h (hrd h')

lemma b_ne {m m' : ℕ} (h1 : m < m') (h2 : m' ≤ m + 3) : b m ≠ b m' := by
  intro h; rw [Fin.ext_iff, b_val, b_val] at h; omega

lemma off_three_iff (m : ℕ) (hm : 1 ≤ m) (β : Fin 4) : off m β = 3 ↔ β = b (m - 1) := by
  rw [off_eq_iff m β 3 (by norm_num), Fin.ext_iff, b_val]; omega

/-! ### The reads of `Δpr_n` -/

/-- The reads of `Δpr_n` (after the write prefix): instances `n - 2` (if `n ≥ 3`), `n - 1`
(if `n ≥ 2`), and `n`. -/
def abEv (n : ℕ) : List (LEv Obj Rd V (Inst Rd)) :=
  (if 3 ≤ n then rdA os blk rd (n - 2) else []) ++ (if 2 ≤ n then rdB k os blk rd (n - 1) else []) ++
    rdC k os blk rd n false

/-- Their history. -/
def abHist (n : ℕ) : List (HEv Rd V) :=
  (if 3 ≤ n then [.invR (rd (b (n - 2)))] else []) ++ (if 2 ≤ n then [.invR (rd (b (n - 1)))] else []) ++
    [.invR (rd (b n)), .retR (rd (b n)) bot]

theorem abEv_spec (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hrd : Function.Injective rd)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t)
    (n : ℕ) (hn : 1 ≤ n)
    (hinst : ∀ m, 1 ≤ m → m ≤ n → n ≤ m + 2 → inst (rc rd m) = ri rd m)
    (hF : 2 ≤ n → ∀ s, blk s = b (n + 1) → s ∈ F)
    (C : LCfg Obj Rd V (Inst Rd)) (hlog : ∀ s, C.log s = W (A k n (blk s)))
    (hfr : ∀ m, m ≤ n + 1 → n ≤ m + 2 → Fresh C (rc rd m)) :
    ∃ C', cx k os blk rd v₁ bot t F inst C (abEv k os blk rd n) = some (C', abHist rd bot n) ∧
      (∀ s, C'.log s = L k rd n (blk s) ++ rl rd n 1 ++
        (if off n (blk s) ≠ 0 then rl rd n 2 else [])) ∧
      Fresh C' (rc rd (n + 1)) := by
  -- after the first read
  obtain ⟨CA, eA, hlogA, hfrA⟩ : ∃ CA, cx k os blk rd v₁ bot t F inst C
      (if 3 ≤ n then rdA os blk rd (n - 2) else []) =
        some (CA, if 3 ≤ n then [.invR (rd (b (n - 2)))] else []) ∧
      (∀ s, CA.log s = W (A k n (blk s)) ++ (if blk s = b (n - 2) then rl rd (n - 2) 1 else [])) ∧
      (∀ m, n - 1 ≤ m → m ≤ n + 1 → Fresh CA (rc rd m)) := by
    by_cases h3 : 3 ≤ n
    · obtain ⟨CA, e, hl, hf⟩ := rdA_spec k os blk rd v₁ bot t F inst hos hall (n - 2) (by omega)
        (hinst _ (by omega) (by omega) (by omega)) C (hfr _ (by omega) (by omega))
      refine ⟨CA, by simpa [h3] using e, fun s => ?_, fun m h1 h2 =>
        hf _ (rc_ne rd hrd (b_ne (by omega) (by omega)).symm) (hfr m h2 (by omega))⟩
      rw [hl s, hlog s]; split_ifs <;> simp
    · refine ⟨C, by simp [h3, cexec_nil], fun s => ?_, fun m h1 h2 => hfr m h2 (by omega)⟩
      have : rl rd (n - 2) 1 = ([] : List (Cl Rd × Lab (Inst Rd))) := by simp [rl]; omega
      rw [hlog s, this]; simp
  -- after the second read: all logs are `L n`
  obtain ⟨CB, eB, hlogB, hfrB⟩ : ∃ CB, cx k os blk rd v₁ bot t F inst CA
      (if 2 ≤ n then rdB k os blk rd (n - 1) else []) =
        some (CB, if 2 ≤ n then [.invR (rd (b (n - 1)))] else []) ∧
      (∀ s, CB.log s = L k rd n (blk s)) ∧ (∀ m, n ≤ m → m ≤ n + 1 → Fresh CB (rc rd m)) := by
    by_cases h2 : 2 ≤ n
    · obtain ⟨CB, e, hl, hf⟩ := rdB_spec k os blk rd v₁ bot t F inst hos hall hblk (n - 1) (by omega)
        (hinst _ (by omega) (by omega) (by omega)) CA (hfrA _ (by omega) (by omega))
        (fun s hs => by
          rcases hs with hs | hs
          · rw [hlogA s, L_off0 k rd _ _ hs]
            have hb : blk s = b (n - 1) := (off_zero_iff _ _).1 hs
            have hne : blk s ≠ b (n - 2) := by rw [hb]; exact b_ne (by omega) (by omega) |>.symm
            have hA := A_succ k (n - 1) (blk s) (by
              rw [show n - 1 + 1 = n by omega, Ne, off_zero_iff, hb]; exact b_ne (by omega) (by omega))
            rw [show n - 1 + 1 = n by omega] at hA
            simp [hne, hA]
          · rw [hlogA s]
            have hb : blk s = b (n - 2) := by
              rw [(off_three_iff _ (by omega) _).1 hs]; congr 1
            have hA := A_succ k (n - 1) (blk s) (by
              rw [show n - 1 + 1 = n by omega, Ne, off_zero_iff, hb]; exact b_ne (by omega) (by omega))
            rw [show n - 1 + 1 = n by omega] at hA
            have hL : L k rd (n - 1) (blk s) = W (A k (n - 1) (blk s)) ++ rl rd (n - 2) 1 := by
              simp [L, hs, show n - 1 - 1 = n - 2 by omega]
            rw [hL, hA, if_pos hb])
        (fun s hs => hF h2 s (by
          have := (off_eq_iff (n - 1) (blk s) 2 (by norm_num)).1 hs
          rw [Fin.ext_iff, b_val]; omega))
      refine ⟨CB, by simpa [h2] using e, fun s => ?_, fun m h1 h2' =>
        hf _ (rc_ne rd hrd (b_ne (by omega) (by omega)).symm) (hfrA m (by omega) h2')⟩
      rw [hl s]
      have hlt := off_lt (n - 1) (blk s)
      have hsucc := L_succ k rd (n - 1) (blk s)
      rw [show n - 1 + 1 = n by omega] at hsucc
      by_cases h1 : off (n - 1) (blk s) = 1
      · have hb : off n (blk s) = 0 := by
          have := off_succ (n - 1) (blk s); rw [show n - 1 + 1 = n by omega] at this; omega
        have hne : blk s ≠ b (n - 2) := by
          rw [(off_zero_iff _ _).1 hb]; exact b_ne (by omega) (by omega) |>.symm
        rw [if_pos h1, hlogA s, L_off0 k rd _ _ hb]; simp [hne]
      · have hb : off n (blk s) ≠ 0 := by
          have := off_succ (n - 1) (blk s); rw [show n - 1 + 1 = n by omega] at this; omega
        rw [if_neg h1, hsucc hb]
        by_cases h0 : off (n - 1) (blk s) = 0 <;> simp [h0]
    · have hn1 : n = 1 := by omega
      subst hn1
      refine ⟨CA, by simp [cexec_nil], fun s => ?_, fun m h1 h2' => hfrA m (by omega) h2'⟩
      rw [hlogA s, L_one]
      simp [rl]
  -- the complete read
  obtain ⟨CC, eC, hlogC, hfrC⟩ := rdC_spec k os blk rd v₁ bot t F inst hos hall hblk n hn false
    (hinst n hn le_rfl (by omega)) CB (hfrB n le_rfl (by omega)) (fun s _ => hlogB s)
    (fun h => by simp at h)
  refine ⟨CC, ?_, hlogC, hfrC _ (rc_ne rd hrd (b_ne (by omega) (by omega))).symm (hfrB _ (by omega) le_rfl)⟩
  dsimp only [cx] at eA eB eC ⊢
  have := cexec_append_some k 2 _ v₁ bot inst t F (cexec_append_some k 2 _ v₁ bot inst t F eA eB) eC
  simpa [abEv, abHist, List.append_assoc] using this

/-! ### The runs `pr_n` and the final run -/

/-- `pr_1`: the complete write, then read 1 (block `b 1 = B₀` forges `σ_{k-1}`). -/
theorem pr_one (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hrd : Function.Injective rd)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (hb : v₁ ≠ bot) :
    ∃ C, cx k os blk rd v₁ bot t (Finset.univ.filter fun s => blk s = b 1) (instN rd 1)
      (Cfg.init bot) (wpre os blk v₁ k ++ rdC k os blk rd 1 true) =
      some (C, [.invW v₁, .retW] ++ [.invR (rd (b 1)), .retR (rd (b 1)) bot]) := by
  obtain ⟨C, e1, hlog, hfr⟩ := wfull_spec k os blk rd v₁ bot t
    (Finset.univ.filter fun s => blk s = b 1) (instN rd 1) hk hos hall hblk hb rfl
  obtain ⟨C', e2, -, -⟩ := rdC_spec k os blk rd v₁ bot t
    (Finset.univ.filter fun s => blk s = b 1) (instN rd 1) hos hall hblk 1 le_rfl true
    (instN_rc rd hrd 1 1 le_rfl (by omega)) C (hfr _ (by simp [rc]))
    (fun s hs => by
      rcases hs with hs | hs
      · rw [hlog s, L_one]
        by_cases h3 : blk s = 3
        · simp [h3, A, W]
        · rw [if_neg h3]
          rw [Ne, off_zero_iff, Fin.ext_iff, b_val] at hs
          have : (blk s).val ≠ 3 := fun h => h3 (Fin.ext h)
          have := (blk s).isLt
          unfold A; rw [if_neg h3]; congr 1; omega
      · simp at hs)
    (fun _ s hs => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (off_zero_iff _ _).1 hs)
  exact ⟨C', by dsimp only [cx] at e1 e2 ⊢; exact cexec_append_some k 2 _ v₁ bot _ t _ e1 e2⟩

/-- `pr_{n+1} = Δpr_n` followed by read `n + 1` (block `b (n+1)` forges `σ`). -/
theorem pr_succ (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hrd : Function.Injective rd)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) (hb : v₁ ≠ bot)
    (n : ℕ) (hn : 1 ≤ n) (hnk : n + 2 ≤ 4 * k) :
    ∃ C, cx k os blk rd v₁ bot t (Finset.univ.filter fun s => blk s = b (n + 1)) (instN rd (n + 1))
      (Cfg.init bot) (wrE os blk v₁ (k - n / 4) (n % 4) ++ abEv k os blk rd n ++
        rdC k os blk rd (n + 1) true) =
      some (C, [.invW v₁] ++ abHist rd bot n ++ [.invR (rd (b (n + 1))), .retR (rd (b (n + 1))) bot]) := by
  set F := Finset.univ.filter fun s => blk s = b (n + 1)
  obtain ⟨C, e1, hlog, hfr⟩ := wrE_spec k os blk rd v₁ bot t F (instN rd (n + 1)) hk hos hall hblk hb
    rfl (k - n / 4) (n % 4) (by omega) (by omega)
  obtain ⟨C', e2, hlog', hfr'⟩ := abEv_spec k os blk rd v₁ bot t F (instN rd (n + 1)) hos hall hrd hblk
    n hn (fun m h1 h2 h3 => instN_rc rd hrd _ _ (by omega) (by omega))
    (fun _ s hs => by simp [F, hs]) C
    (fun s => by
      rw [hlog s]
      by_cases h3 : blk s = 3
      · simp [h3, A, W]
      · rw [if_neg h3, A_eq k n (blk s) h3 (by omega)]
        split_ifs <;> first | rfl | (congr 1; omega))
    (fun m _ _ => hfr _ (by simp [rc]))
  obtain ⟨C'', e3, -, -⟩ := rdC_spec k os blk rd v₁ bot t F (instN rd (n + 1)) hos hall hblk (n + 1)
    (by omega) true (instN_rc rd hrd _ _ le_rfl (by omega)) C' hfr'
    (fun s hs => by
      rcases hs with hs | hs
      · rw [hlog' s, L_succ k rd n (blk s) hs]
      · simp at hs)
    (fun _ s hs => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; exact (off_zero_iff _ _).1 hs)
  refine ⟨C'', ?_⟩
  dsimp only [cx] at e1 e2 e3 ⊢
  have := cexec_append_some k 2 _ v₁ bot _ t _ (cexec_append_some k 2 _ v₁ bot _ t _ e1 e2) e3
  simpa [List.append_assoc] using this

/-- The final run: `Δpr_{4k-1}` without the write (`wr^1_4` is indistinguishable from no write). -/
theorem pr_final (hk : 1 ≤ k) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (hrd : Function.Injective rd)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t) :
    ∃ C, cx k os blk rd v₁ bot t (Finset.univ.filter fun s => blk s = b (4 * k))
      (instN rd (4 * k - 1)) (Cfg.init bot) (abEv k os blk rd (4 * k - 1)) =
      some (C, abHist rd bot (4 * k - 1)) := by
  obtain ⟨C, e, -, -⟩ := abEv_spec k os blk rd v₁ bot t
    (Finset.univ.filter fun s => blk s = b (4 * k)) (instN rd (4 * k - 1)) hos hall hrd hblk
    (4 * k - 1) (by omega) (fun m h1 h2 h3 => instN_rc rd hrd _ _ (by omega) (by omega))
    (fun _ s hs => by simp [hs, show 4 * k - 1 + 1 = 4 * k by omega])
    (Cfg.init bot) (fun s => by
      unfold A
      have := (blk s).isLt
      split_ifs with h
      · rfl
      · have : (blk s).val ≠ 3 := fun h' => h (Fin.ext h')
        rw [show k - (4 * k - 1 + 3 - (blk s).val) / 4 = 0 by omega]; rfl)
    (fun m _ _ => fresh_init bot _)
  exact ⟨C, e⟩

end Runs

omit [DecidableEq Obj] [Fintype Obj] [DecidableEq V] in
lemma before_app {l l' : List (HEv Rd V)} {a c : HEv Rd V} : Before (l ++ a :: c :: l') a c :=
  ⟨l.length, l.length + 1, by omega, by simp, by simp⟩

/-- **Proposition 1 (read lower bound), block form.** With four blocks of at most `t` objects each
and four distinct readers, no protocol whose writes take `K ≥ 1` rounds and whose reads take two
rounds implements an atomic SWMR register tolerating `t` malicious objects. -/
theorem read_lb {Msg Rep : Type} (P : Proto Obj Rd V Msg Rep) (hK : 1 ≤ P.K) (hN : P.N = 2)
    (t : ℕ) (os : List Obj) (hos : os.Nodup) (hall : ∀ s, s ∈ os) (blk : Obj → Fin 4)
    (hblk : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t)
    (rd : Fin 4 → Rd) (hrd : Function.Injective rd) (v₁ bot : V) (hb : v₁ ≠ bot) :
    ¬ P.Atomic t bot := by
  intro hP
  set k := P.K with hk
  obtain ⟨M, hM⟩ := exists_isCanon P (T k os blk rd) Prod.fst v₁ (rank k) (rank_ok k os blk rd)
  let cv : ℕ → V := fun m => P.rRet (rd (b m))
    ((List.range P.N).map fun p => iview P M (.r (rd (b m))) (T k os blk rd (ri rd m, p + 1)))
  have hcret : ∀ n m, m ≤ n → n ≤ m + 3 →
      cret P M (T k os blk rd) (instN rd n) (rd (b m)) = cv m := by
    intro n m h1 h2
    have := instN_rc rd hrd n m h1 h2
    simp only [rc] at this
    simp only [cret, this, cv]
  have hFc : ∀ β, (Finset.univ.filter fun s => blk s = β).card ≤ t := hblk
  -- `pr_1`
  have step1 : cv 1 = v₁ := by
    obtain ⟨C, e⟩ := pr_one k os blk rd v₁ bot t hK hos hall hrd hblk hb
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot (instN rd 1) t hP _ (hFc _) hM
      (instN_fst rd 1) _ C _ (by rw [hN]; exact e)
    rw [← hcret 1 1 le_rfl (by omega)]
    exact cret_of_after_write hA (v := v₁) (by simp) (x := bot) (by simp)
      (by simpa using (before_app (l := [HEv.invW v₁]) (l' := [HEv.retR (rd (b 1)) bot])))
  -- `pr_{n+1}`
  have stepS : ∀ n, 1 ≤ n → n + 2 ≤ 4 * k → cv n = v₁ → cv (n + 1) = v₁ := by
    intro n hn hnk ih
    obtain ⟨C, e⟩ := pr_succ k os blk rd v₁ bot t hK hos hall hrd hblk hb n hn hnk
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot (instN rd (n + 1)) t hP _ (hFc _) hM
      (instN_fst rd (n + 1)) _ C _ (by rw [hN]; exact e)
    rw [← hcret (n + 1) (n + 1) le_rfl (by omega)]
    have hj' : cret P M (T k os blk rd) (instN rd (n + 1)) (rd (b n)) = v₁ := by
      rw [hcret (n + 1) n (by omega) (by omega)]; exact ih
    refine cret_of_after_read hA hb (by simp) (x' := bot) (by simp [abHist]) hj' (x := bot)
      (by simp) ?_
    have : [HEv.invW v₁] ++ abHist rd bot n ++ [HEv.invR (rd (b (n + 1))), HEv.retR (rd (b (n + 1))) bot] =
        ([HEv.invW v₁] ++ (if 3 ≤ n then [HEv.invR (rd (b (n - 2)))] else []) ++
          (if 2 ≤ n then [HEv.invR (rd (b (n - 1)))] else []) ++ [HEv.invR (rd (b n))]) ++
        HEv.retR (rd (b n)) bot :: HEv.invR (rd (b (n + 1))) :: [HEv.retR (rd (b (n + 1))) bot] := by
      simp [abHist]
    rw [this]; exact before_app
  -- the final run
  have final : cv (4 * k - 1) = bot := by
    obtain ⟨C, e⟩ := pr_final k os blk rd v₁ bot t hK hos hall hrd hblk
    have hA := atomic_of_cexec P (T k os blk rd) M v₁ bot (instN rd (4 * k - 1)) t hP _ (hFc _) hM
      (instN_fst rd _) _ C _ (by rw [hN]; exact e)
    rw [← hcret (4 * k - 1) (4 * k - 1) le_rfl (by omega)]
    refine cret_of_no_write hA (fun v hv => ?_) (x := bot) (by simp [abHist])
    simp only [abHist, List.mem_append, List.mem_cons, List.not_mem_nil] at hv
    split_ifs at hv <;> simp_all
  have all : ∀ m, 1 ≤ m → m + 1 ≤ 4 * k → cv m = v₁ := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; exact step1
    | succ m hm ih => intro h; exact stepS m hm (by omega) (ih (by omega))
  exact hb ((all (4 * k - 1) (by omega) (by omega)).symm.trans final)

end Podc.RobustAtomicStorage.ReadLB
