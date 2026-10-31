import Papers.PODC2011.LocallyCheckableProofs.Gluing

/-!
# Section 5.3: the core of the `Ω(log n)` lower bound

Identifiers `{1, …, n²}` are split into `2n` blocks: `a_i = blkA n i` (`⌊n/2⌋` identifiers) and
`b_i = blkB n i` (`⌈n/2⌉` identifiers), `i < n`. The yes-instances are the `n`-cycles
`C(a,b) = cycN n a b`.

`lowerBound_core`: for a (weak) proof labelling scheme with horizon `r` and node labels from a finite
type `L`, if every `C(a,b)` has a correct labelling in `F` and `K (K+1)² < n` for
`K = (|L| 2^(s(n)+2))^(4r+4)`, then there are correct labellings of all `C(a,b)` and `a₁ ≠ a₂`,
`b₁ ≠ b₂` such that the glued `2n`-cycle with the inherited labelling is a yes-instance as soon as
it belongs to `F`.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

variable {L : Type*}

/-! ### Cycles as instances -/

/-- The underlying graph of a cycle. -/
def cycGraph (l : List ℕ) : SimpleGraph ℕ := SimpleGraph.fromRel (Succ l)

@[simp] lemma cyc_G (l : List ℕ) (lab : ℕ → L) (mk : ℕ → Bool) :
    (cyc l lab mk).G = cycGraph l := rfl

/-- The successor of `x` in the cyclic order of `l`. -/
def nxt (l : List ℕ) (x : ℕ) : ℕ := l.getD ((l.idxOf x + 1) % l.length) 0

lemma succ_iff_nxt {l : List ℕ} (hl : l.Nodup) {x y : ℕ} : Succ l x y ↔ x ∈ l ∧ y = nxt l x := by
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    refine ⟨List.getElem_mem hi, ?_⟩
    rw [nxt, hl.idxOf_getElem, List.getD_eq_getElem]
  · rintro ⟨hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨i, hi, rfl, ?_⟩
    rw [nxt, hl.idxOf_getElem, List.getD_eq_getElem]

/-- The mark of the edge from `x` to its successor in `l`, read off an instance. -/
noncomputable def markOf (J : Inst L) (l : List ℕ) (x : ℕ) : Bool := by
  classical exact decide (J.S.Adj x (nxt l x))

lemma markOf_eq_true {J : Inst L} {l : List ℕ} {x : ℕ} :
    markOf J l x = true ↔ J.S.Adj x (nxt l x) := by
  simp [markOf]

/-- An instance whose graph is the cycle on `l` is a labelled cycle. -/
lemma eq_cyc {l : List ℕ} (hl : l.Nodup) (J : Inst L) (hV : J.V = l.toFinset)
    (hG : J.G = cycGraph l) :
    J = cyc l J.lab (markOf J l) := by
  ext x y
  · simp [hV]
  · simp [hG]
  · rw [cyc_sadj]
    constructor
    · intro h
      have hG' := J.S_le h
      rw [hG, cycGraph, fromRel_adj] at hG'
      refine ⟨hG'.1, hG'.2.imp (fun hs => ⟨hs, ?_⟩) (fun hs => ⟨hs, ?_⟩)⟩
      · obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs; exact markOf_eq_true.2 h
      · obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs; exact markOf_eq_true.2 h.symm
    · rintro ⟨-, ⟨hs, hm⟩ | ⟨hs, hm⟩⟩
      · obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs; exact markOf_eq_true.1 hm
      · obtain ⟨-, rfl⟩ := (succ_iff_nxt hl).1 hs; exact (markOf_eq_true.1 hm).symm
  · rfl

lemma cyc_n {l : List ℕ} (hl : l.Nodup) (lab : ℕ → L) (mk : ℕ → Bool) :
    (cyc l lab mk).n = l.length := by
  simp [Inst.n, List.toFinset_card_of_nodup hl]

/-! ### Identifier blocks -/

/-- The block `a_i`: identifiers `1 + i n + j`, `j < ⌊n/2⌋`. -/
def blkA (n : ℕ) (i : Fin n) : List ℕ := (List.range (n / 2)).map fun j => 1 + i * n + j

/-- The block `b_i`: identifiers `1 + i n + ⌊n/2⌋ + j`, `j < ⌈n/2⌉`. -/
def blkB (n : ℕ) (i : Fin n) : List ℕ := (List.range (n - n / 2)).map fun j => 1 + i * n + n / 2 + j

/-- The node list of the `n`-cycle `C(a,b)`. -/
abbrev lstN (n : ℕ) (a b : Fin n) : List ℕ := lst (blkA n) (blkB n) a b

lemma blk_inj {n i i' j j' : ℕ} (hj : j < n) (hj' : j' < n) (h : i * n + j = i' * n + j') :
    i = i' ∧ j = j' := by
  have hn : 0 < n := by omega
  have h1 : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (i' * n + j') / n = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj', zero_add]
  have hi : i = i' := by rw [← h1, ← h2, h]
  subst hi
  exact ⟨rfl, by omega⟩

lemma goodLists_blk (n : ℕ) : GoodLists (blkA n) (blkB n) (n / 2) (n - n / 2) := by
  refine ⟨fun a => by simp [blkA], fun b => by simp [blkB], fun a => ?_, fun b => ?_,
    fun a a' haa x hx hx' => ?_, fun b b' hbb x hx hx' => ?_, fun a b x hx hx' => ?_⟩
  · exact (List.nodup_range).map (fun x y h => by simpa using h)
  · exact (List.nodup_range).map (fun x y h => by simpa using h)
  · simp only [blkA, List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', hj', he⟩ := hx'
    exact haa (Fin.ext (blk_inj (n := n) (i := a.1) (i' := a'.1) (j := j) (j' := j') (by omega)
      (by omega) (by omega)).1)
  · simp only [blkB, List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', hj', he⟩ := hx'
    exact hbb (Fin.ext (blk_inj (n := n) (i := b'.1) (i' := b.1) (j := n / 2 + j')
      (j' := n / 2 + j) (by omega) (by omega) (by omega)).1.symm)
  · simp only [blkA, blkB, List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, hj, rfl⟩ := hx
    obtain ⟨j', hj', he⟩ := hx'
    have := (blk_inj (n := n) (i := b.1) (i' := a.1) (j := n / 2 + j') (j' := j) (by omega)
      (by omega) (by omega)).2
    omega

lemma mem_lstN_bound {n : ℕ} {a b : Fin n} {x : ℕ} (hx : x ∈ lstN n a b) : 1 ≤ x ∧ x ≤ n ^ 2 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [lstN, lst, blkA, blkB, List.mem_append, List.mem_reverse, List.mem_map,
    List.mem_range] at hx
  rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · constructor
    · omega
    · have : (a : ℕ) * n ≤ (n - 1) * n := Nat.mul_le_mul_right _ (by omega)
      have h2 : (n - 1) * n + n = n ^ 2 := by
        cases n with
        | zero => omega
        | succ m => simp [pow_two]; ring
      omega
  · constructor
    · omega
    · have : (b : ℕ) * n ≤ (n - 1) * n := Nat.mul_le_mul_right _ (by omega)
      have h2 : (n - 1) * n + n = n ^ 2 := by
        cases n with
        | zero => omega
        | succ m => simp [pow_two]; ring
      omega

lemma lstN_length (n : ℕ) (a b : Fin n) : (lstN n a b).length = n := by
  simp [lstN, lst, blkA, blkB]; omega

/-! ### The core statement -/

/-- **Core of Theorem 5.1 (Section 5.3).** Let `(f, A)` be a weak proof labelling scheme of horizon
`r` for `P` on `F`, with node labels from a finite type `L`. For every `n ≥ 4r+4` such that every
`n`-cycle `C(a,b)` has a correct labelling in `F`, and `K (K+1)² < n` where
`K = (|L| 2^(s(n)+2))^(4r+4)`: there are correct labellings of all `C(a,b)` (in `F ∩ P`) and
`a₁ ≠ a₂`, `b₁ ≠ b₂` such that the glued `2n`-cycle with inherited labels is in `P` whenever it is
in `F`. -/
theorem lowerBound_core [Fintype L] [DecidableEq L] {F P : Set (Inst L)} {s : ℕ → ℕ}
    (hW : AdmitsWeakLCP F P s) :
    ∃ r : ℕ, ∀ n : ℕ, 4 * r + 4 ≤ n →
      (Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) *
        ((Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) + 1) ^ 2 < n →
      (∀ a b : Fin n, ∃ J ∈ F, J ∈ P ∧ J.V = (lstN n a b).toFinset ∧ J.G = cycGraph (lstN n a b)) →
      ∃ (lab : Fin n → Fin n → ℕ → L) (mk : Fin n → Fin n → ℕ → Bool),
        (∀ a b, cyc (lstN n a b) (lab a b) (mk a b) ∈ F ∧ cyc (lstN n a b) (lab a b) (mk a b) ∈ P) ∧
        ∃ a₁ a₂ b₁ b₂, a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
          (glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂ ∈ F →
            glued (blkA n) (blkB n) lab mk a₁ b₁ a₂ b₂ ∈ P) := by
  classical
  obtain ⟨r, A, hA, hc, hs⟩ := hW
  refine ⟨r, fun n hn hK hyes => ?_⟩
  have hG := goodLists_blk n
  have hnd : ∀ a b : Fin n, (lstN n a b).Nodup := fun a b => hG.nodup_lst a b
  -- the scheme's correct solutions and proofs
  have hsol : ∀ a b : Fin n, ∃ J ∈ F, J ∈ P ∧ J.V = (lstN n a b).toFinset ∧
      J.G = cycGraph (lstN n a b) ∧ ∃ Pf : Proof, SizeLE J Pf (s J.n) ∧ AllAccept A J Pf := by
    intro a b
    obtain ⟨J, hJF, hJP, hJV, hJG⟩ := hyes a b
    obtain ⟨J', hJ'F, hJ'P, ⟨hV, hG'⟩, Pf, hPf, hacc⟩ := hc J hJF ⟨J, hJF, hJP, rfl, rfl⟩
    exact ⟨J', hJ'F, hJ'P, hV ▸ hJV, hG' ▸ hJG, Pf, hPf, hacc⟩
  choose J hJF hJP hJV hJG Pf hPf hacc using hsol
  have hJeq : ∀ a b, J a b = cyc (lstN n a b) (J a b).lab (markOf (J a b) (lstN n a b)) :=
    fun a b => eq_cyc (hnd a b) _ (hJV a b) (hJG a b)
  let lab : Fin n → Fin n → ℕ → L := fun a b => (J a b).lab
  let mk : Fin n → Fin n → ℕ → Bool := fun a b => markOf (J a b) (lstN n a b)
  have hJn : ∀ a b, (J a b).n = n := fun a b => by
    rw [hJeq a b, cyc_n (hnd a b), lstN_length]
  refine ⟨lab, mk, fun a b => ⟨?_, ?_⟩, ?_⟩
  · rw [← hJeq a b]; exact hJF a b
  · rw [← hJeq a b]; exact hJP a b
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, hall⟩ := glue_accept (A := A) (r := r) (lab := lab) (mk := mk)
    (P := Pf) hA hG (by omega) (by omega) (s n)
    (fun a b => by have := hacc a b; rwa [hJeq a b] at this)
    (fun a b => by have := hPf a b; rw [hJn a b, hJeq a b] at this; exact this)
    (by simpa using hK) (by
      have : (Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) ≤
          (Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) *
            ((Fintype.card L * 2 ^ (s n + 2)) ^ (4 * r + 4) + 1) ^ 2 :=
        Nat.le_mul_of_pos_right _ (by positivity)
      simp only [Fintype.card_fin]; omega)
  refine ⟨a₁, a₂, b₁, b₂, ha, hb, fun hF => ?_⟩
  by_contra hP
  obtain ⟨v, hv, hrej⟩ := hs _ hF hP (gluedProof (blkA n) (blkB n) Pf a₁ b₁ a₂ b₂)
  rw [hall v hv] at hrej
  exact Bool.noConfusion hrej

end Podc.LocallyCheckableProofs
