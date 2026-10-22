import Podc.Computability.Distributed.SharedMemory.Byzantine.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Byzantine/Restrict.lean

/-!
# Restricting histories to the correct processes

`h.filter (fun ℓ => ℓ.proc ∉ Bz)` is the history `h|correct` of Definition 6 of Hu–Toueg. The
operations, responses and real-time order of correct processes are the same in `h` and in
`h|correct` (`opsOf_filter_correct`, `respsOf_filter_correct`, `precedes_filter_correct_iff`);
hence they agree between two histories with the same restriction (`opsOf_eq_of_filter_eq`, …).
This is how properties of a Byzantine linearization `h'` transfer back to `h`.
-/

namespace Cslib.SharedMemory.Byzantine

open Cslib.SharedMemory

variable {A : ObjSpec} {P : Type} [DecidableEq P]

lemma opsOf_filter_correct (Bz : Finset P) (h : List (Label P A)) {p : P} (hp : p ∉ Bz) :
    opsOf (h.filter (fun ℓ => ℓ.proc ∉ Bz)) p = opsOf h p := by
  induction h with
  | nil => rfl
  | cons ℓ h ih =>
    rw [List.filter_cons]
    split_ifs with hℓ
    · rw [opsOf_cons, opsOf_cons, ih]
    · have hne : ℓ.proc ≠ p := fun h' => hp (by rw [← h']; simpa using hℓ)
      rw [opsOf_cons, ih, Label.invOf_eq_none_of_proc_ne hne]; rfl

lemma respsOf_filter_correct (Bz : Finset P) (h : List (Label P A)) {p : P} (hp : p ∉ Bz) :
    respsOf (h.filter (fun ℓ => ℓ.proc ∉ Bz)) p = respsOf h p := by
  induction h with
  | nil => rfl
  | cons ℓ h ih =>
    rw [List.filter_cons]
    split_ifs with hℓ
    · rw [respsOf_cons, respsOf_cons, ih]
    · have hne : ℓ.proc ≠ p := fun h' => hp (by rw [← h']; simpa using hℓ)
      rw [respsOf_cons, ih, Label.retOf_eq_none_of_proc_ne hne]; rfl

lemma precedes_filter_correct_iff (Bz : Finset P) (h : List (Label P A)) {a b : OpId P}
    (ha : a.1 ∉ Bz) (hb : b.1 ∉ Bz) :
    Precedes (h.filter (fun ℓ => ℓ.proc ∉ Bz)) a b ↔ Precedes h a b := by
  constructor
  · rintro ⟨β', γ', he, hc, hi⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := List.filter_eq_append_iff.1 he
    refine ⟨β, γ, rfl, ?_, ?_⟩
    · rw [Completed, respsOf_filter_correct Bz β ha] at hc; exact hc
    · rw [Invoked, opsOf_filter_correct Bz β hb] at hi; exact hi
  · rintro ⟨β, γ, rfl, hc, hi⟩
    refine ⟨β.filter (fun ℓ => ℓ.proc ∉ Bz), γ.filter (fun ℓ => ℓ.proc ∉ Bz),
      List.filter_append .., ?_, ?_⟩
    · rw [Completed, respsOf_filter_correct Bz β ha]; exact hc
    · rw [Invoked, opsOf_filter_correct Bz β hb]; exact hi

variable {Bz : Finset P} {h h' : List (Label P A)}

lemma opsOf_eq_of_filter_eq (e : h'.filter (fun ℓ => ℓ.proc ∉ Bz) =
    h.filter (fun ℓ => ℓ.proc ∉ Bz)) {p : P} (hp : p ∉ Bz) : opsOf h' p = opsOf h p := by
  rw [← opsOf_filter_correct Bz h' hp, e, opsOf_filter_correct Bz h hp]

lemma respsOf_eq_of_filter_eq (e : h'.filter (fun ℓ => ℓ.proc ∉ Bz) =
    h.filter (fun ℓ => ℓ.proc ∉ Bz)) {p : P} (hp : p ∉ Bz) : respsOf h' p = respsOf h p := by
  rw [← respsOf_filter_correct Bz h' hp, e, respsOf_filter_correct Bz h hp]

lemma opOf_eq_of_filter_eq (e : h'.filter (fun ℓ => ℓ.proc ∉ Bz) =
    h.filter (fun ℓ => ℓ.proc ∉ Bz)) {x : OpId P} (hx : x.1 ∉ Bz) : opOf h' x = opOf h x := by
  simp [opOf, opsOf_eq_of_filter_eq e hx]

lemma respOf_eq_of_filter_eq (e : h'.filter (fun ℓ => ℓ.proc ∉ Bz) =
    h.filter (fun ℓ => ℓ.proc ∉ Bz)) {x : OpId P} (hx : x.1 ∉ Bz) :
    respOf h' x = respOf h x := by
  simp [respOf, respsOf_eq_of_filter_eq e hx]

lemma precedes_iff_of_filter_eq (e : h'.filter (fun ℓ => ℓ.proc ∉ Bz) =
    h.filter (fun ℓ => ℓ.proc ∉ Bz)) {a b : OpId P} (ha : a.1 ∉ Bz) (hb : b.1 ∉ Bz) :
    Precedes h' a b ↔ Precedes h a b := by
  rw [← precedes_filter_correct_iff Bz h' ha hb, e, precedes_filter_correct_iff Bz h ha hb]

end Cslib.SharedMemory.Byzantine
