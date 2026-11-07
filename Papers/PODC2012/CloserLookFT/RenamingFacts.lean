import Papers.PODC2012.CloserLookFT.ElectionLiveness

/-!
# Per-object facts behind Theorem 4.1 (perfect renaming from election objects)

Theorem 4.1 builds partially-wait-free perfect renaming from `n - 1` election objects: a process
tries objects `1, 2, …` in order and takes the name of the first object that elects it (or `n`).
Its proof uses two facts about one election object `i`:

1. "at most `n - i + 1` processes participate in object `i`", so object `i` may be implemented
   with `⌈log (n - i + 1)⌉` levels. The paper derives this from the *abstract* election
   specification ("in the absence of faults exactly one process is elected"); read literally this
   is not enough (a fault elsewhere in the run would allow an object to elect nobody while all its
   participants move on). What the argument really needs, and what the algorithm of Section 2
   guarantees, is the per-object fact `card_outFalse_lt`: in every state of one object, the
   processes that returned `0` are strictly fewer than those that started — the last process to
   write `turn` never returns `0` unless somebody has been elected (and then the elected process
   does not return `0`).
2. safety of object `i` when only `n - i + 1 ≤ 2^L` processes ever participate, although more
   processes exist: `Inv.elected_unique_of_started` (two elected processes need more than `2^L`
   *started* processes).

The composition of the `n - 1` objects into one implementation is not formalized.
-/

namespace Podc.CloserLookFT

open Finset

variable {P : Type} [DecidableEq P]

/-- A process that returned `0` saw `done = 1` or is not the last process to have written
`turn`. -/
def OutFalseInv (s : ESys P) : Prop :=
  ∀ x a w c, s.loc x = .out false a w c → s.m.done = true ∨ s.m.turn ≠ some x

lemma outFalseInv_step {L : ℕ} {s : ESys P} (hs : SInv s) (h : OutFalseInv s) (p : P) :
    OutFalseInv (s.step L p) := by
  intro x a w c hx
  have hdone : s.m.done = true → (s.step L p).m.done = true := fun hd => estep_done_mono hd
  by_cases hxp : x = p
  · subst hxp
    have hx' : (estep L x s.m (s.loc x)).2 = .out false a w c := by simpa [ESys.step] using hx
    have hturn : (estep L x s.m (s.loc x)).1.turn = s.m.turn := by
      by_cases hst : s.loc x = .start
      · rw [hst] at hx'; simp only [estep] at hx'; split_ifs at hx' <;> simp at hx'
      · exact estep_turn_eq hst
    simp only [ESys.step, hturn]
    by_cases ht : s.m.turn = some x
    · rcases estep_outFalse_turn hx' ht with h1 | h1 | ⟨k, b, j, h1⟩
      · exact Or.inl (estep_done_mono h1)
      · rcases h x a w c h1 with h2 | h2
        · exact Or.inl (estep_done_mono h2)
        · exact absurd ht h2
      · exact absurd ht (hs.clrTurn x k b j h1)
    · exact Or.inr ht
  · have hx' : s.loc x = .out false a w c := by simpa [ESys.step, hxp] using hx
    rcases h x a w c hx' with h1 | h1
    · exact Or.inl (hdone h1)
    · right; intro h2
      rcases estep_turn h2 with h3 | ⟨h3, h4⟩
      · exact h1 h3
      · exact hxp h4

lemma outFalseInv_invoke {s : ESys P} (h : OutFalseInv s) (p : P) :
    OutFalseInv (s.invoke p) := by
  intro x a w c hx
  unfold ESys.invoke at hx ⊢
  split_ifs at hx ⊢ with hp
  · by_cases hxp : x = p
    · subst hxp; simp at hx
    · exact h x a w c (by simpa [hxp] using hx)
  · exact h x a w c hx

theorem EReach.outFalseInv {L : ℕ} {s : ESys P} (hs : EReach L s) : OutFalseInv s := by
  induction hs with
  | init => intro x a w c hx; simp [ESys.init] at hx
  | step p hr ih => exact outFalseInv_step hr.sInv ih p
  | invoke p _ ih => exact outFalseInv_invoke ih p

variable [Fintype P]

instance (l : ELoc) : Decidable l.Started := by unfold ELoc.Started; infer_instance

/-- The process has returned `0`. -/
def ELoc.RetZero : ELoc → Prop
  | .out false _ _ _ => True
  | _ => False

instance (l : ELoc) : Decidable l.RetZero := by
  rcases l with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _, _, _, _⟩ <;>
    simp only [ELoc.RetZero] <;> infer_instance

omit [DecidableEq P] [Fintype P] in
lemma ELoc.retZero_iff {l : ELoc} : l.RetZero ↔ ∃ a w c, l = .out false a w c := by
  cases l with
  | out r a w c => cases r <;> simp [ELoc.RetZero]
  | _ => simp [ELoc.RetZero]

/-- **Per-object counting fact for Theorem 4.1**: in every reachable state of one election
object in which some process has started, fewer processes have returned `0` than have started.
Hence at most `m - 1` of the `m` participants of an object move on to the next object. -/
theorem card_outFalse_lt {L : ℕ} {s : ESys P} (hs : EReach L s) (hst : ∃ z, (s.loc z).Started) :
    (univ.filter fun x => (s.loc x).RetZero).card <
      (univ.filter fun x => (s.loc x).Started).card := by
  classical
  obtain ⟨g, hg⟩ := hs.inv
  have hsub : (univ.filter fun x => (s.loc x).RetZero) ⊆
      univ.filter fun x => (s.loc x).Started := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    obtain ⟨a, w, c, h⟩ := ELoc.retZero_iff.1 hx; rw [h]; simp [ELoc.Started]
  -- a started process that has not returned `0`
  have hex : ∃ y, (s.loc y).Started ∧ ¬ ∃ a w c, s.loc y = .out false a w c := by
    by_cases hd : s.m.done = true
    · obtain ⟨y, a, w, c, hy⟩ := hs.sInv.doneOut hd
      exact ⟨y, by rw [hy]; simp [ELoc.Started], fun ⟨a', w', c', h'⟩ => by rw [hy] at h'; cases h'⟩
    · obtain ⟨z, hz⟩ := hst
      have hturn : s.m.turn ≠ none := fun h0 => ((hg.age0 z).1 (hg.turnNone h0 z)) hz
      obtain ⟨Y, hY⟩ := Option.ne_none_iff_exists'.1 hturn
      refine ⟨Y, ?_, fun ⟨a, w, c, h'⟩ => ?_⟩
      · by_contra h'; exact (hg.turnSome Y hY).1 ((hg.age0 Y).2 h')
      · rcases hs.outFalseInv Y a w c h' with h1 | h1
        · exact hd h1
        · exact h1 hY
  obtain ⟨y, hy1, hy2⟩ := hex
  refine card_lt_card ⟨hsub, fun h => ?_⟩
  have := h (show y ∈ univ.filter fun x => (s.loc x).Started by simpa using hy1)
  simp only [mem_filter, mem_univ, true_and] at this
  exact hy2 (ELoc.retZero_iff.1 this)

/-- **Safety of one object with few participants**: two distinct elected processes need more than
`2^L` started processes. So an object with `L` levels is safe whenever at most `2^L` processes
ever participate in it, whatever the total number of processes. -/
theorem Inv.elected_unique_of_started {L : ℕ} {s : ESys P} {g : Ghost P} (h : Inv L s g)
    (hn : (univ.filter fun x => (s.loc x).Started).card ≤ 2 ^ L) {x y : P}
    (hx : (s.loc x).Elected) (hy : (s.loc y).Elected) : x = y := by
  classical
  by_contra hxy
  have hel : ∀ z, (s.loc z).Elected → (s.loc z).Started := fun z hz => by
    constructor <;> intro h' <;> rw [h'] at hz <;> simp [ELoc.Elected] at hz
  set S := univ.filter fun x => (s.loc x).Started
  have h1 : (2 : ℤ) ^ L ≤ g.cr x := (req_elected hx).symm.le.trans (h.reqLe x)
  have h2 : (2 : ℤ) ^ L ≤ g.cr y := (req_elected hy).symm.le.trans (h.reqLe y)
  have hnn : ∀ z, 0 ≤ g.cr z := fun z => (req_nonneg s g z).trans (h.reqLe z)
  have hxS : x ∈ S := by simpa [S] using hel x hx
  have hyS : y ∈ S := by simpa [S] using hel y hy
  have hsumS : g.cr x + g.cr y ≤ ∑ z ∈ S, g.cr z := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := g.cr)
      (show ({x, y} : Finset P) ⊆ S by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
      (fun z _ _ => hnn z)
    rwa [Finset.sum_pair hxy] at this
  have hsplit : ∑ z, g.cr z = ∑ z ∈ S, g.cr z + ∑ z ∈ univ.filter (fun x => ¬ (s.loc x).Started),
      g.cr z := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hunst : ∑ z ∈ univ.filter (fun x => ¬ (s.loc x).Started), g.cr z =
      (univ.filter fun x => ¬ (s.loc x).Started).card := by
    rw [Finset.sum_congr rfl fun z hz => h.unst z (by simpa using hz)]; simp
  have hcard : (S.card : ℤ) + (univ.filter fun x => ¬ (s.loc x).Started).card =
      Fintype.card P := by
    exact_mod_cast Finset.card_filter_add_card_filter_not _
  have hfree : 0 ≤ free L s.m := sum_ite_nonneg fun j => by positivity
  have hc := h.cons
  have hn' : (S.card : ℤ) ≤ 2 ^ L := by exact_mod_cast hn
  linarith

end Podc.CloserLookFT
