import Papers.PODC2022.AnonymousMACConsensus.Invariant

/-!
# MAC-SC: regularity from the history invariant

`HInv.regular`: every history satisfying the history part `HInv` of the invariant (together with
the facts `PastOK` recorded by collects) satisfies regularity. This is the purely history-level part
of the proof of Theorem 1.
-/

namespace Podc.AnonymousMACConsensus

variable {ι V : Type*} {cnt : ι → ℕ} {op : ι → Option (Op V)} {h : History ι V}

/-- Property I. -/
lemma HInv.regularI (H : HInv cnt op h) : RegularI h := by
  intro i n W hret j
  obtain ⟨q₀, hq₀, hA, -⟩ := H.done i n W hret
  constructor
  · intro hW m v hst ⟨r, o, p, q, hpq, hp, hq⟩
    obtain ⟨p₁, hp₁⟩ := mem_iff_getElem?.1 hst
    have hqq : q = q₀ := H.inv_unique _ _ _ _ _ _ hq hq₀
    obtain ⟨p'', o'', hp''lt, hp''⟩ := H.inv_before_ret _ _ _ _ hp
    have : p'' = p₁ := H.inv_unique _ _ _ _ _ _ hp'' hp₁
    subst this
    have := hA p p'' j m r v hp''lt (hqq ▸ hpq) hp₁ hp
    simp [hW, key] at this
  · intro m v hW
    refine ⟨?_, ?_⟩
    · obtain ⟨q₁, hq₁⟩ := mem_iff_getElem?.1 hret
      obtain ⟨p, hpq, hp⟩ := H.done_inv q₁ i n W hq₁ j m v hW
      exact ⟨p, q₁, hpq, hp, hq₁⟩
    · rintro ⟨m', v', r, r', hne, hst, ⟨a, b, hab, ha, hb⟩, ⟨b', q, hbq, hb', hq⟩⟩
      have hqq : q = q₀ := H.inv_unique _ _ _ _ _ _ hq hq₀
      obtain ⟨p₁, hp₁⟩ := mem_iff_getElem?.1 hst
      obtain ⟨p'', o'', hp''lt, hp''⟩ := H.inv_before_ret _ _ _ _ hb'
      have : p'' = p₁ := H.inv_unique _ _ _ _ _ _ hp'' hp₁
      subst this
      have h1 := hA b' p'' j m' r' v' hp''lt (hqq ▸ hbq) hp₁ hb'
      have h2 := H.ret_mono a b j m m' r r' hab ha hb
      rw [hW] at h1
      simp [key] at h1
      omega

/-- Property II. -/
lemma HInv.regularII (H : HInv cnt op h) : RegularII h := by
  intro i₁ n₁ W₁ i₂ n₂ W₂ hr₁ hr₂ ⟨r, o, p, q, hpq, hp, hq⟩
  obtain ⟨q₀, hq₀, -, hB⟩ := H.done i₂ n₂ W₂ hr₂
  have hqq : q = q₀ := H.inv_unique _ _ _ _ _ _ hq hq₀
  obtain ⟨p₁, hp₁⟩ := mem_iff_getElem?.1 hr₁
  have hpp : p = p₁ := by
    rcases lt_trichotomy p p₁ with h' | h' | h'
    · exact absurd (H.ret_mono _ _ _ _ _ _ _ h' hp hp₁) (lt_irrefl _)
    · exact h'
    · exact absurd (H.ret_mono _ _ _ _ _ _ _ h' hp₁ hp) (lt_irrefl _)
  subst hpp
  have hle := hB p i₁ n₁ W₁ (hqq ▸ hpq) hp₁
  intro j m₁ v₁ hW₁
  have hk := hle j
  rw [hW₁] at hk
  have hk1 : key (some (m₁, v₁)) = m₁ + 1 := rfl
  obtain ⟨m₂, v₂, hW₂, hkey⟩ := exists_of_key_pos (x := W₂ j) (by omega)
  refine ⟨m₂, v₂, hW₂, ?_⟩
  rcases eq_or_lt_of_le (show m₁ ≤ m₂ by omega) with hm | hm
  · subst hm
    left
    have i₁mem := H.valid_ret _ _ _ hr₁ j m₁ v₁ hW₁
    have i₂mem := H.valid_ret _ _ _ hr₂ j m₁ v₂ hW₂
    obtain ⟨a, ha⟩ := mem_iff_getElem?.1 i₁mem
    obtain ⟨b, hb⟩ := mem_iff_getElem?.1 i₂mem
    have := H.inv_unique _ _ _ _ _ _ ha hb
    subst this
    rw [ha] at hb
    simp at hb
    rw [hb]
  · right
    obtain ⟨b, hb⟩ := mem_iff_getElem?.1 (H.valid_ret _ _ _ hr₂ j m₂ v₂ hW₂)
    obtain ⟨a, r', hab, ha⟩ := H.ret_before_inv b j m₁ m₂ _ hb hm
    exact ⟨r', a, b, hab, ha, hb⟩

lemma HInv.regular (H : HInv cnt op h) : Regular h := ⟨H.regularI, H.regularII⟩

end Podc.AnonymousMACConsensus
