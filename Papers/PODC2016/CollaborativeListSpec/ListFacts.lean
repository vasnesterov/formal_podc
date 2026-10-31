import Mathlib

/-!
# Lists ordered consistently with a relation

Facts used to read off list responses from the list order `lo` of the weak specification: two
lists that are both ordered by `lo`, where `lo` is irreflexive and transitive on the larger one,
are in sublist relation; a list obtained from another by one insertion at position `min k n` is
the corresponding `insertIdx`.
-/

namespace Podc.CollaborativeListSpec

variable {U : Type} [DecidableEq U]

theorem nodup_of_pairwise {lo : U → U → Prop} {l : List U} (h : l.Pairwise lo)
    (hirr : ∀ a, ¬ lo a a) : l.Nodup :=
  h.imp fun {a b} hab (heq : a = b) => hirr _ (heq ▸ hab)

/-- Two `lo`-ordered lists, `lo` irreflexive and transitive on the larger one: the smaller is a
subsequence. -/
theorem sublist_of_pairwise {lo : U → U → Prop} {l₁ l₂ : List U} (h₁ : l₁.Pairwise lo)
    (h₂ : l₂.Pairwise lo) (hirr : ∀ a, ¬ lo a a)
    (htr : ∀ a ∈ l₂, ∀ b ∈ l₂, ∀ c ∈ l₂, lo a b → lo b c → lo a c)
    (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.Sublist l₂ := by
  have hn₁ := nodup_of_pairwise h₁ hirr
  have hn₂ := nodup_of_pairwise h₂ hirr
  set f := l₂.filter (· ∈ l₁) with hf
  have hfs : f.Sublist l₂ := List.filter_sublist
  have hperm : f.Perm l₁ := by
    rw [List.perm_ext_iff_of_nodup (hn₂.sublist hfs) hn₁]
    intro x; simp only [hf, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub x h, h⟩⟩
  have : f = l₁ := by
    refine hperm.eq_of_pairwise (le := lo) ?_ (h₂.sublist hfs) h₁
    intro a b ha hb hab hba
    exact absurd (htr a (hfs.subset ha) b (hsub b hb) a (hfs.subset ha) hab hba) (hirr a)
  exact this ▸ hfs

/-- Two `lo`-ordered lists with the same members, `lo` irreflexive and transitive on one of them,
are equal. -/
theorem eq_of_pairwise {lo : U → U → Prop} {l₁ l₂ : List U} (h₁ : l₁.Pairwise lo)
    (h₂ : l₂.Pairwise lo) (hirr : ∀ a, ¬ lo a a)
    (htr : ∀ a ∈ l₂, ∀ b ∈ l₂, ∀ c ∈ l₂, lo a b → lo b c → lo a c)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  have hs := sublist_of_pairwise h₁ h₂ hirr htr (fun x hx => (hmem x).1 hx)
  have hn₁ := nodup_of_pairwise h₁ hirr
  have hn₂ := nodup_of_pairwise h₂ hirr
  apply hs.eq_of_length
  have := (List.perm_ext_iff_of_nodup hn₁ hn₂).2 hmem
  exact this.length_eq

/-- A list `l'` with the members of `l` plus a fresh `a`, keeping the order of `l`, with `a` at
position `min k (|l'| - 1)`, is `l.insertIdx (min k |l|) a`. -/
theorem eq_insertIdx {l l' : List U} {a : U} {k : ℕ} (hn' : l'.Nodup) (hs : l.Sublist l')
    (ha : a ∉ l) (hmem : ∀ x, x ∈ l' ↔ x ∈ l ∨ x = a)
    (hk : l'[min k (l'.length - 1)]? = some a) : l' = l.insertIdx (min k l.length) a := by
  have hn : l.Nodup := hn'.sublist hs
  have hperm : l'.Perm (a :: l) := by
    rw [List.perm_ext_iff_of_nodup hn' (List.nodup_cons.2 ⟨ha, hn⟩)]
    intro x; rw [hmem x]; simp [or_comm]
  have hlen : l'.length = l.length + 1 := by simpa using hperm.length_eq
  rw [hlen, Nat.add_sub_cancel] at hk
  set j := min k l.length with hj
  have hjl : j < l'.length := by omega
  have hget : l'[j] = a := by
    rw [List.getElem?_eq_getElem hjl] at hk; exact Option.some.inj hk
  have herase : l'.eraseIdx j = l := by
    have h1 : l.Sublist (l'.erase a) := by
      have := hs.erase a
      rwa [List.erase_of_not_mem ha] at this
    have h2 : (l'.erase a).length = l.length := by
      rw [List.length_erase_of_mem (hmem a |>.2 (Or.inr rfl)), hlen]; rfl
    have h3 : l'.erase a = l'.eraseIdx j := by
      apply List.erase_eq_eraseIdx_of_idxOf
      rw [← hget]; exact List.Nodup.idxOf_getElem hn' j hjl
    rw [← h3]; exact (h1.eq_of_length h2.symm).symm
  conv_lhs => rw [← List.insertIdx_eraseIdx_getElem hjl]
  rw [herase, hget]

end Podc.CollaborativeListSpec
