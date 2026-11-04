import Podc.Computability.Distributed.SharedMemory.Awareness

/-!
# Write blocks of essential processes

For the max-register lower bound (Section 4 of Hendler–Khait, PODC'14) we track, for every base
object, the *block* of its history: the maximal top segment of value-setting entries written by
*essential* processes (a set `E`). The invariant `BlockOK E h` says that the block of the history
`h` was written by a single process (its *owner*). Then erasing any set of essential processes
either leaves the top entry of `h` in place or uncovers the first entry written by a
non-essential process — this is what the paper's proof of Lemma 4 implicitly assumes
("o's familiarity set may only be extended by …") and what fails without the invariant (erasing
the last writer of an object *resurrects* older writes).
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {P V : Type} [DecidableEq P]

/-- The block of `h` w.r.t. `E`: the maximal top segment of entries written by `E`. -/
def block (E : Finset P) (h : List (Entry P V)) : List (Entry P V) :=
  h.takeWhile (fun e => decide (e.proc ∈ E))

/-- All entries of the block of `h` w.r.t. `E` are written by one process. -/
def BlockOK (E : Finset P) (h : List (Entry P V)) : Prop :=
  ∀ x ∈ block E h, ∀ y ∈ block E h, x.proc = y.proc

@[simp] lemma block_nil (E : Finset P) : block E ([] : List (Entry P V)) = [] := rfl

lemma block_cons_of_mem {E : Finset P} {y : Entry P V} {h : List (Entry P V)} (hy : y.proc ∈ E) :
    block E (y :: h) = y :: block E h := by
  simp [block, List.takeWhile_cons, hy]

lemma block_cons_of_not_mem {E : Finset P} {y : Entry P V} {h : List (Entry P V)}
    (hy : y.proc ∉ E) : block E (y :: h) = [] := by
  simp [block, List.takeWhile_cons, hy]

lemma mem_block {E : Finset P} {h : List (Entry P V)} {x : Entry P V} (hx : x ∈ block E h) :
    x ∈ h ∧ x.proc ∈ E := by
  induction h with
  | nil => simp at hx
  | cons y h ih =>
    by_cases hy : y.proc ∈ E
    · rw [block_cons_of_mem hy] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨List.mem_cons_self, hy⟩
      · exact ⟨List.mem_cons_of_mem _ (ih hx).1, (ih hx).2⟩
    · rw [block_cons_of_not_mem hy] at hx; simp at hx

lemma blockOK_nil (E : Finset P) : BlockOK E ([] : List (Entry P V)) := by
  intro x hx; simp at hx

lemma blockOK_cons_of_not_mem {E : Finset P} {y : Entry P V} {h : List (Entry P V)}
    (hy : y.proc ∉ E) : BlockOK E (y :: h) := by
  intro x hx; rw [block_cons_of_not_mem hy] at hx; simp at hx

lemma BlockOK.tail {E : Finset P} {y : Entry P V} {h : List (Entry P V)} (hb : BlockOK E (y :: h))
    (hy : y.proc ∈ E) : BlockOK E h := by
  intro x hx z hz
  unfold BlockOK at hb
  rw [block_cons_of_mem hy] at hb
  exact hb x (List.mem_cons_of_mem _ hx) z (List.mem_cons_of_mem _ hz)

/-- Pushing an entry of process `q` on a history whose block (if any) belongs to `q`. -/
lemma blockOK_cons_self {E : Finset P} {y : Entry P V} {h : List (Entry P V)}
    (hb : BlockOK E h) (hq : ∀ x ∈ block E h, x.proc = y.proc) : BlockOK E (y :: h) := by
  by_cases hy : y.proc ∈ E
  · rw [BlockOK, block_cons_of_mem hy]
    intro x hx z hz
    rcases List.mem_cons.1 hx with hx | hx <;> rcases List.mem_cons.1 hz with hz | hz
    · rw [hx, hz]
    · rw [hx]; exact (hq z hz).symm
    · rw [hz]; exact hq x hx
    · exact hb x hx z hz
  · exact blockOK_cons_of_not_mem hy

lemma block_sublist_of_subset {E E' : Finset P} (hE : E' ⊆ E) (h : List (Entry P V)) :
    ∀ x ∈ block E' h, x ∈ block E h := by
  induction h with
  | nil => simp
  | cons y h ih =>
    intro x hx
    by_cases hy' : y.proc ∈ E'
    · rw [block_cons_of_mem hy'] at hx
      rw [block_cons_of_mem (hE hy')]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih x hx)
    · rw [block_cons_of_not_mem hy'] at hx; simp at hx

lemma BlockOK.mono {E E' : Finset P} {h : List (Entry P V)} (hb : BlockOK E h) (hE : E' ⊆ E) :
    BlockOK E' h := fun x hx y hy =>
  hb x (block_sublist_of_subset hE h x hx) y (block_sublist_of_subset hE h y hy)

/-- Entries of the block of a filtered history come from the block of the history. -/
lemma block_filter_sub {E X : Finset P} (hX : X ⊆ E) (h : List (Entry P V)) :
    ∀ x ∈ block (E \ X) (h.filter (fun e => decide (e.proc ∉ X))), x ∈ block E h := by
  induction h with
  | nil => simp
  | cons y h ih =>
    intro x hx
    by_cases hyX : y.proc ∈ X
    · have : (y :: h).filter (fun e => decide (e.proc ∉ X)) =
          h.filter (fun e => decide (e.proc ∉ X)) := by
        simp [List.filter_cons, hyX]
      rw [this] at hx
      rw [block_cons_of_mem (hX hyX)]; exact List.mem_cons_of_mem _ (ih x hx)
    · have : (y :: h).filter (fun e => decide (e.proc ∉ X)) =
          y :: h.filter (fun e => decide (e.proc ∉ X)) := by
        simp [List.filter_cons, hyX]
      rw [this] at hx
      by_cases hyE : y.proc ∈ E
      · have hyEX : y.proc ∈ E \ X := Finset.mem_sdiff.2 ⟨hyE, hyX⟩
        rw [block_cons_of_mem hyEX] at hx
        rw [block_cons_of_mem hyE]
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih x hx)
      · have hyEX : y.proc ∉ E \ X := fun h' => hyE (Finset.mem_sdiff.1 h').1
        rw [block_cons_of_not_mem hyEX] at hx; simp at hx

/-- Erasing a subset of the essential processes preserves `BlockOK` (for the remaining ones). -/
lemma BlockOK.filter {E X : Finset P} {h : List (Entry P V)} (hb : BlockOK E h) (hX : X ⊆ E) :
    BlockOK (E \ X) (h.filter (fun e => decide (e.proc ∉ X))) := fun x hx y hy =>
  hb x (block_filter_sub hX h x hx) y (block_filter_sub hX h y hy)

/-- If the top entry of a filtered history is written by an essential process, it belongs to
the block of the history. -/
lemma head_filter_mem_block {E X : Finset P} (hX : X ⊆ E) {h : List (Entry P V)} {y : Entry P V}
    (hy : (h.filter (fun e => decide (e.proc ∉ X))).head? = some y) (hyE : y.proc ∈ E) :
    y ∈ block E h := by
  apply block_filter_sub hX h y
  obtain ⟨t, ht⟩ : ∃ t, h.filter (fun e => decide (e.proc ∉ X)) = y :: t := by
    cases hf : h.filter (fun e => decide (e.proc ∉ X)) with
    | nil => rw [hf] at hy; simp at hy
    | cons z t => rw [hf] at hy; simp only [List.head?_cons, Option.some.injEq] at hy; exact ⟨t, hy ▸ rfl⟩
  have hyX : y.proc ∉ X := by
    have : y ∈ h.filter (fun e => decide (e.proc ∉ X)) := by rw [ht]; exact List.mem_cons_self
    simpa using (List.mem_filter.1 this).2
  rw [ht, block_cons_of_mem (Finset.mem_sdiff.2 ⟨hyE, hyX⟩)]
  exact List.mem_cons_self

/-- Two filters agree on their top entry when the coarser one's top entry is outside the finer
erased set. -/
lemma head_filter_eq {X Y : Finset P} (hXY : X ⊆ Y) (h : List (Entry P V))
    (hh : ∀ y ∈ (h.filter (fun e => decide (e.proc ∉ X))).head?, y.proc ∉ Y) :
    (h.filter (fun e => decide (e.proc ∉ X))).head? =
      (h.filter (fun e => decide (e.proc ∉ Y))).head? := by
  induction h with
  | nil => rfl
  | cons z t ih =>
    by_cases hzX : z.proc ∈ X
    · have h1 : (z :: t).filter (fun e => decide (e.proc ∉ X)) =
          t.filter (fun e => decide (e.proc ∉ X)) := by simp [List.filter_cons, hzX]
      have h2 : (z :: t).filter (fun e => decide (e.proc ∉ Y)) =
          t.filter (fun e => decide (e.proc ∉ Y)) := by simp [List.filter_cons, hXY hzX]
      rw [h1, h2]; rw [h1] at hh; exact ih hh
    · have h1 : (z :: t).filter (fun e => decide (e.proc ∉ X)) =
          z :: t.filter (fun e => decide (e.proc ∉ X)) := by simp [List.filter_cons, hzX]
      rw [h1] at hh ⊢
      have hzY : z.proc ∉ Y := hh z (by simp)
      simp [List.filter_cons, hzY]

/-- The top value of a history. -/
lemma topVal_eq_of_head? {h h' : List (Entry P V)} (e : h.head? = h'.head?) (d : V) :
    topVal d h = topVal d h' := by
  cases h <;> cases h' <;> simp_all

lemma topAw_eq_of_head? {h h' : List (Entry P V)} (e : h.head? = h'.head?) :
    topAw h = topAw h' := by
  cases h <;> cases h' <;> simp_all

end Podc.ReadUpdateTradeoffs
