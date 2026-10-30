import Papers.PODC2022.AnonymousMACConsensus.Invariant

/-!
# MAC-SC: preservation of the invariant

`Inv` holds initially and is preserved by every step of MAC-SC with handler priority.
-/

namespace Podc.AnonymousMACConsensus

variable {ι V : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma Valid.append {h : History ι V} {W : View ι V} (hv : Valid h W) (t : History ι V) :
    Valid (h ++ t) W := fun j m v hj => List.mem_append_left _ (hv j m v hj)

omit [DecidableEq ι] in
lemma Knows.of_view_queue {c c' : Config ι V} {k j : ι} {s : ℕ}
    (hv : c'.view k = c.view k) (hq : c'.queue k = c.queue k) (hk : Knows c k j s) :
    Knows c' k j s := by
  unfold Knows at *; rw [hv, hq]; exact hk

/-! ## Initial configuration -/

omit [DecidableEq ι] in
lemma inv_init : Inv (Config.init : Config ι V) [] := by
  have hsys : ∀ W, SysView (Config.init : Config ι V) W → W = View.empty := by
    rintro W ⟨k, hW | hW | hW⟩
    · exact hW
    · simp [Config.init] at hW
    · simp [Config.init, Phase.cv?] at hW
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Config.init, Phase.op?, Phase.cv?]
  · intro W hW j m v hj
    rw [hsys W hW] at hj; simp [View.empty] at hj
  · intro i W hW
    rw [hsys W hW]; simp [View.empty, key]

/-! ## Invocation -/

lemma Inv.invoke {c : Config ι V} {h : History ι V} (I : Inv c h) (i : ι) (o : Op V)
    (hidle : c.phase i = .idle) :
    Inv { c with phase := Function.update c.phase i (.invoked o) }
      (h ++ [Label.inv i (c.cnt i) o]) := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set c' : Config ι V := { c with phase := Function.update c.phase i (.invoked o) } with hc'
  have hop : ∀ j, (c'.phase j).op? = if j = i then some o else (c.phase j).op? := by
    intro j; by_cases hj : j = i <;> simp [c', hj, Phase.op?]
  have hcv : ∀ j, (c'.phase j).cv? = (c.phase j).cv? := by
    intro j; by_cases hj : j = i <;> simp [c', hj, Phase.cv?, hidle]
  have hsys : ∀ W, SysView c' W ↔ SysView c W := by
    intro W; simp only [SysView, hcv]; rfl
  have hopi : (c.phase i).op? = none := by simp [hidle, Phase.op?]
  have hcvi : (c.phase i).cv? = none := by simp [hidle, Phase.cv?]
  have hkn : ∀ k j s, Knows c' k j s ↔ Knows c k j s := fun _ _ _ => Iff.rfl
  set e : Label ι V := Label.inv i (c.cnt i) o
  have hlen := @lt_length_of_getElem?_eq_some
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- inv_idx
  · intro p j m o' hp
    rw [getElem?_append_singleton] at hp
    rcases hp with hp | ⟨-, hp⟩
    · rcases H.inv_idx p j m o' hp with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · by_cases hj : j = i
        · subst hj; rw [hopi] at h2; simp at h2
        · right; exact ⟨h1, by rw [hop]; simp [hj, h2]⟩
    · simp only [e, Label.inv.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      right; exact ⟨rfl, by rw [hop]; simp⟩
  -- ret_idx
  · intro p j m r hp
    rw [getElem?_append_singleton] at hp
    rcases hp with hp | ⟨-, hp⟩
    · exact H.ret_idx p j m r hp
    · simp [e] at hp
  -- cur_inv
  · intro j o' hj
    rw [hop] at hj
    by_cases hji : j = i
    · subst hji; simp at hj; subst hj; simp [e, c']
    · simp [hji] at hj
      exact List.mem_append_left _ (H.cur_inv j o' hj)
  -- done_ret
  · intro j m hm
    obtain ⟨r, hr⟩ := H.done_ret j m hm
    exact ⟨r, List.mem_append_left _ hr⟩
  -- ret_before_inv
  · intro q j m m' o' hq hmm
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨hql, hq⟩
    · obtain ⟨p, r, hpq, hp⟩ := H.ret_before_inv q j m m' o' hq hmm
      exact ⟨p, r, hpq, getElem?_append_of_eq_some hp⟩
    · simp only [e, Label.inv.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨r, hr⟩ := H.done_ret j m hmm
      obtain ⟨p, hp⟩ := mem_iff_getElem?.1 hr
      exact ⟨p, r, hql ▸ hlen hp, getElem?_append_of_eq_some hp⟩
  -- inv_before_ret
  · intro q j m r hq
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨-, hq⟩
    · obtain ⟨p, o', hpq, hp⟩ := H.inv_before_ret q j m r hq
      exact ⟨p, o', hpq, getElem?_append_of_eq_some hp⟩
    · simp [e] at hq
  -- inv_unique
  · intro p q j m o₁ o₂ hp hq
    rw [getElem?_append_singleton] at hp hq
    have key : ∀ (p : ℕ) (o₁ : Op V), h[p]? = some (Label.inv i (c.cnt i) o₁) → False := by
      intro p o₁ hp
      rcases H.inv_idx p i (c.cnt i) o₁ hp with h1 | ⟨-, h2⟩
      · exact lt_irrefl _ h1
      · rw [hopi] at h2; simp at h2
    rcases hp with hp | ⟨hpl, hp⟩ <;> rcases hq with hq | ⟨hql, hq⟩
    · exact H.inv_unique p q j m o₁ o₂ hp hq
    · simp only [e, Label.inv.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      exact (key p o₁ hp).elim
    · simp only [e, Label.inv.injEq] at hp
      obtain ⟨rfl, rfl, rfl⟩ := hp
      exact (key q o₂ hq).elim
    · rw [hpl, hql]
  -- ret_mono
  · intro p q j a b r r' hpq hp hq
    rw [getElem?_append_singleton] at hp hq
    rcases hp with hp | ⟨-, hp⟩
    · rcases hq with hq | ⟨-, hq⟩
      · exact H.ret_mono p q j a b r r' hpq hp hq
      · simp [e] at hq
    · simp [e] at hp
  -- valid_ret
  · intro j n W hW
    rcases List.mem_append.1 hW with hW | hW
    · exact (H.valid_ret j n W hW).append _
    · simp [e] at hW
  -- done_inv
  · intro q j n W hq j' m v hW
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨-, hq⟩
    · obtain ⟨p, hpq, hp⟩ := H.done_inv q j n W hq j' m v hW
      exact ⟨p, hpq, getElem?_append_of_eq_some hp⟩
    · simp [e] at hq
  -- done
  · intro j n W hW
    rcases List.mem_append.1 hW with hW | hW
    · exact (H.done j n W hW).append _
    · simp [e] at hW
  -- valid_sys
  · intro W hW
    exact (hvs W ((hsys W).1 hW)).append _
  -- key_le
  · intro j hj W hW
    rw [hcv] at hj
    exact hkl j hj W ((hsys W).1 hW)
  -- store_cv
  · intro j v cv hj hcvj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · subst hji; rw [hcvi] at hcvj; simp at hcvj
    · rw [hop] at hj; simp [hji] at hj
      exact hsc j v cv hj hcvj
  -- knows_bcast
  · intro j o' cv got hj k hk hkc j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hkb j o' cv got hj k hk hkc j'
  -- knows_acked
  · intro j o' cv hj k hkc j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hka j o' cv hj k hkc j'
  -- knows_store
  · intro p p' j m r v hp' hp k hkc
    rw [getElem?_append_singleton] at hp hp'
    rcases hp with hp | ⟨-, hp⟩
    · rcases hp' with hp' | ⟨-, hp'⟩
      · exact hks p p' j m r v hp' hp k hkc
      · simp only [e, Label.inv.injEq] at hp'
        obtain ⟨rfl, rfl, -⟩ := hp'
        exact absurd (H.ret_idx p _ _ r hp) (lt_irrefl _)
    · simp [e] at hp
  -- knows_collect
  · intro j n W hW k hk' j'
    rcases List.mem_append.1 hW with hW | hW
    · exact hkc j n W hW k hk' j'
    · simp [e] at hW
  -- pend
  · intro j cv hj hcvj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · subst hji; rw [hcvi] at hcvj; simp at hcvj
    · rw [hop] at hj; simp [hji] at hj
      exact (hpd j cv hj hcvj).append _

/-! ## Return -/

lemma Inv.ret {c : Config ι V} {h : History ι V} (I : Inv c h) (i : ι) (o : Op V) (cv : View ι V)
    (hph : c.phase i = .acked o cv) :
    Inv { c with phase := Function.update c.phase i .idle,
                 cnt := Function.update c.cnt i (c.cnt i + 1) }
      (h ++ [Label.ret i (c.cnt i) (resp o cv)]) := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set c' : Config ι V := { c with phase := Function.update c.phase i .idle, cnt := Function.update c.cnt i (c.cnt i + 1) } with hc'
  have hop : ∀ j, (c'.phase j).op? = if j = i then none else (c.phase j).op? := by
    intro j; by_cases hj : j = i <;> simp [c', hj, Phase.op?]
  have hcv : ∀ j, (c'.phase j).cv? = if j = i then none else (c.phase j).cv? := by
    intro j; by_cases hj : j = i <;> simp [c', hj, Phase.cv?]
  have hcnt : ∀ j, c'.cnt j = if j = i then c.cnt i + 1 else c.cnt j := by
    intro j; by_cases hj : j = i <;> simp [c', hj]
  have hsys : ∀ W, SysView c' W → SysView c W := by
    rintro W ⟨k, hW | hW | hW⟩
    · exact ⟨k, Or.inl hW⟩
    · exact ⟨k, Or.inr (Or.inl hW)⟩
    · rw [hcv] at hW
      by_cases hk : k = i
      · simp [hk] at hW
      · simp [hk] at hW; exact ⟨k, Or.inr (Or.inr hW)⟩
  have hopi : (c.phase i).op? = some o := by simp [hph, Phase.op?]
  have hcvi : (c.phase i).cv? = some cv := by simp [hph, Phase.cv?]
  have hkn : ∀ k j s, Knows c' k j s ↔ Knows c k j s := fun _ _ _ => Iff.rfl
  set e : Label ι V := Label.ret i (c.cnt i) (resp o cv)
  have hlen := @lt_length_of_getElem?_eq_some
  have hcvvalid : Valid h cv := hvs cv ⟨i, Or.inr (Or.inr hcvi)⟩
  have hresp : ∀ W, resp o cv = Resp.view W → o = .collect ∧ W = cv := by
    intro W hW; cases o <;> simp [resp] at hW ⊢; exact hW.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- inv_idx
  · intro p j m o' hp
    rw [getElem?_append_singleton] at hp
    rcases hp with hp | ⟨-, hp⟩
    · rw [hcnt, hop]
      rcases H.inv_idx p j m o' hp with h1 | ⟨h1, h2⟩
      · left; split_ifs with hj
        · subst hj; omega
        · exact h1
      · by_cases hj : j = i
        · subst hj; left; simp; omega
        · right; simp [hj, h1, h2]
    · simp [e] at hp
  -- ret_idx
  · intro p j m r hp
    rw [getElem?_append_singleton] at hp
    rw [hcnt]
    rcases hp with hp | ⟨-, hp⟩
    · have := H.ret_idx p j m r hp
      split_ifs with hj
      · subst hj; omega
      · exact this
    · simp only [e, Label.ret.injEq] at hp
      obtain ⟨rfl, rfl, -⟩ := hp
      simp
  -- cur_inv
  · intro j o' hj
    rw [hop] at hj
    by_cases hji : j = i
    · simp [hji] at hj
    · simp [hji] at hj
      rw [hcnt]; simp only [hji, ite_false]
      exact List.mem_append_left _ (H.cur_inv j o' hj)
  -- done_ret
  · intro j m hm
    rw [hcnt] at hm
    by_cases hji : j = i
    · subst hji
      simp at hm
      rcases lt_or_eq_of_le hm with hm | rfl
      · obtain ⟨r, hr⟩ := H.done_ret j m hm
        exact ⟨r, List.mem_append_left _ hr⟩
      · exact ⟨resp o cv, by simp [e]⟩
    · simp [hji] at hm
      obtain ⟨r, hr⟩ := H.done_ret j m hm
      exact ⟨r, List.mem_append_left _ hr⟩
  -- ret_before_inv
  · intro q j m m' o' hq hmm
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨-, hq⟩
    · obtain ⟨p, r, hpq, hp⟩ := H.ret_before_inv q j m m' o' hq hmm
      exact ⟨p, r, hpq, getElem?_append_of_eq_some hp⟩
    · simp [e] at hq
  -- inv_before_ret
  · intro q j m r hq
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨hql, hq⟩
    · obtain ⟨p, o', hpq, hp⟩ := H.inv_before_ret q j m r hq
      exact ⟨p, o', hpq, getElem?_append_of_eq_some hp⟩
    · simp only [e, Label.ret.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      obtain ⟨p, hp⟩ := mem_iff_getElem?.1 (H.cur_inv j o hopi)
      exact ⟨p, o, hql ▸ hlen hp, getElem?_append_of_eq_some hp⟩
  -- inv_unique
  · intro p q j m o₁ o₂ hp hq
    rw [getElem?_append_singleton] at hp hq
    rcases hp with hp | ⟨-, hp⟩
    · rcases hq with hq | ⟨-, hq⟩
      · exact H.inv_unique p q j m o₁ o₂ hp hq
      · simp [e] at hq
    · simp [e] at hp
  -- ret_mono
  · intro p q j a b r r' hpq hp hq
    rw [getElem?_append_singleton] at hp hq
    rcases hp with hp | ⟨hpl, hp⟩ <;> rcases hq with hq | ⟨hql, hq⟩
    · exact H.ret_mono p q j a b r r' hpq hp hq
    · simp only [e, Label.ret.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      exact H.ret_idx p j a r hp
    · have := hlen hq; omega
    · omega
  -- valid_ret
  · intro j n W hW
    rcases List.mem_append.1 hW with hW | hW
    · exact (H.valid_ret j n W hW).append _
    · simp only [e, List.mem_singleton, Label.ret.injEq] at hW
      obtain ⟨rfl, rfl, hWr⟩ := hW
      obtain ⟨-, rfl⟩ := hresp W hWr.symm
      exact hcvvalid.append _
  -- done_inv
  · intro q j n W hq j' m v hW
    rw [getElem?_append_singleton] at hq
    rcases hq with hq | ⟨hql, hq⟩
    · obtain ⟨p, hpq, hp⟩ := H.done_inv q j n W hq j' m v hW
      exact ⟨p, hpq, getElem?_append_of_eq_some hp⟩
    · simp only [e, Label.ret.injEq] at hq
      obtain ⟨rfl, rfl, hq⟩ := hq
      obtain ⟨-, rfl⟩ := hresp W hq.symm
      obtain ⟨p, hp⟩ := mem_iff_getElem?.1 (hcvvalid j' m v hW)
      exact ⟨p, hql ▸ hlen hp, getElem?_append_of_eq_some hp⟩
  -- done
  · intro j n W hW
    rcases List.mem_append.1 hW with hW | hW
    · exact (H.done j n W hW).append _
    · simp only [e, List.mem_singleton, Label.ret.injEq] at hW
      obtain ⟨rfl, rfl, hWr⟩ := hW
      obtain ⟨rfl, rfl⟩ := hresp W hWr.symm
      exact (hpd j W hopi hcvi).append _
  -- valid_sys
  · intro W hW
    exact (hvs W (hsys W hW)).append _
  -- key_le
  · intro j hj W hW
    have hW' := hsys W hW
    rw [hcnt]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true]
      rcases hWj : W j with _ | ⟨m, v⟩
      · simp [key]
      · obtain ⟨p, hp⟩ := mem_iff_getElem?.1 (hvs W hW' j m v hWj)
        have := H.inv_idx p j m _ hp
        simp only [key]; omega
    · rw [hcv] at hj; simp only [hji, ite_false] at hj ⊢
      exact hkl j hj W hW'
  -- store_cv
  · intro j v cv' hj hcvj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · simp [hji] at hcvj
    · rw [hop] at hj; simp only [hji, ite_false] at hj hcvj
      rw [hcnt]; simp only [hji, ite_false]
      exact hsc j v cv' hj hcvj
  -- knows_bcast
  · intro j o' cv' got hj k hk hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hkb j o' cv' got hj k hk hkc' j'
  -- knows_acked
  · intro j o' cv' hj k hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hka j o' cv' hj k hkc' j'
  -- knows_store
  · intro p p' j m r v hp' hp k hkc'
    rw [getElem?_append_singleton] at hp hp'
    rcases hp' with hp' | ⟨-, hp'⟩
    · rcases hp with hp | ⟨-, hp⟩
      · exact hks p p' j m r v hp' hp k hkc'
      · simp only [e, Label.ret.injEq] at hp
        obtain ⟨rfl, rfl, -⟩ := hp
        rcases H.inv_idx p' j _ _ hp' with h1 | ⟨-, h2⟩
        · exact absurd h1 (lt_irrefl _)
        · rw [hopi] at h2
          simp only [Option.some.injEq] at h2
          subst h2
          have := hka j _ cv hph k hkc' j
          rw [hsc j v cv hopi hcvi] at this
          exact this
    · simp [e] at hp'
  -- knows_collect
  · intro j n W hW k hk' j'
    rcases List.mem_append.1 hW with hW | hW
    · exact hkc j n W hW k hk' j'
    · simp only [e, List.mem_singleton, Label.ret.injEq] at hW
      obtain ⟨rfl, rfl, hWr⟩ := hW
      obtain ⟨rfl, rfl⟩ := hresp W hWr.symm
      exact hka j _ W hph k hk' j'
  -- pend
  · intro j cv' hj hcvj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · simp [hji] at hcvj
    · rw [hop] at hj; simp only [hji, ite_false] at hj hcvj
      rw [hcnt]; simp only [hji, ite_false]
      exact (hpd j cv' hj hcvj).append _

/-! ## Line 1 / line 4 and the start of `mac-broadcast` -/

lemma lineView_apply_ne {c : Config ι V} {i j : ι} (hj : j ≠ i) (o : Op V) :
    lineView c i o j = c.view i j := by
  cases o <;> simp [lineView, View.merge, View.single, hj, newer_none_right]

lemma lineView_store_self {c : Config ι V} {i : ι} {v : V} (hk : key (c.view i i) ≤ c.cnt i) :
    lineView c i (.store v) i = some (c.cnt i, v) := by
  simp only [lineView, View.merge, View.single, ite_true, newer]
  split_ifs with h'
  · rfl
  · exact absurd (Nat.lt_succ_of_le hk) h'

lemma Inv.exec {c : Config ι V} {h : History ι V} (I : Inv c h) (i : ι) (o : Op V)
    (halive : i ∉ c.crashed) (hph : c.phase i = .invoked o) (hq : c.queue i = []) :
    Inv { c with phase := Function.update c.phase i (.bcast o (lineView c i o) ∅) } h := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set cv := lineView c i o with hcvdef
  set c' : Config ι V := { c with phase := Function.update c.phase i (.bcast o cv ∅) } with hc'
  have hop : (fun j => (c'.phase j).op?) = (fun j => (c.phase j).op?) := by
    funext j; by_cases hj : j = i
    · subst hj; simp [c', hph, Phase.op?]
    · simp [c', hj]
  have hop' : ∀ j, (c'.phase j).op? = (c.phase j).op? := fun j => congrFun hop j
  have hcv : ∀ j, (c'.phase j).cv? = if j = i then some cv else (c.phase j).cv? := by
    intro j; by_cases hj : j = i <;> simp [c', hj, Phase.cv?]
  have hsys : ∀ W, SysView c' W → SysView c W ∨ W = cv := by
    rintro W ⟨k, hW | hW | hW⟩
    · exact Or.inl ⟨k, Or.inl hW⟩
    · exact Or.inl ⟨k, Or.inr (Or.inl hW)⟩
    · rw [hcv] at hW
      by_cases hk : k = i
      · simp [hk] at hW; exact Or.inr hW.symm
      · simp [hk] at hW; exact Or.inl ⟨k, Or.inr (Or.inr hW)⟩
  have hopi : (c.phase i).op? = some o := by simp [hph, Phase.op?]
  have hcvi : (c.phase i).cv? = none := by simp [hph, Phase.cv?]
  have hview : SysView c (c.view i) := ⟨i, Or.inl rfl⟩
  have hcvvalid : Valid h cv := by
    intro j m v hj
    by_cases hji : j = i
    · subst hji
      cases o with
      | collect => exact hvs _ hview j m v hj
      | store v₀ =>
        rw [hcvdef, lineView_store_self (hkl j hcvi _ hview)] at hj
        simp only [Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact H.cur_inv j _ hopi
    · rw [hcvdef, lineView_apply_ne hji] at hj
      exact hvs _ hview j m v hj
  refine ⟨hop ▸ H, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- valid_sys
  · intro W hW
    rcases hsys W hW with hW | rfl
    · exact hvs W hW
    · exact hcvvalid
  -- key_le
  · intro j hj W hW
    have hji : j ≠ i := by rintro rfl; rw [hcv] at hj; simp at hj
    rw [hcv] at hj; simp only [hji, ite_false] at hj
    rcases hsys W hW with hW | rfl
    · exact hkl j hj W hW
    · rw [hcvdef, lineView_apply_ne hji]; exact hkl j hj _ hview
  -- store_cv
  · intro j v cv' hj hcvj
    rw [hop'] at hj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · subst hji
      simp only [ite_true, Option.some.injEq] at hcvj
      subst hcvj
      rw [hopi] at hj; simp only [Option.some.injEq] at hj; subst hj
      exact lineView_store_self (hkl j hcvi _ hview)
    · simp only [hji, ite_false] at hcvj
      exact hsc j v cv' hj hcvj
  -- knows_bcast
  · intro j o' cv' got hj k hk hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj; rw [← hj.2.2] at hk; simp at hk
    · simp [c', hji] at hj
      exact hkb j o' cv' got hj k hk hkc' j'
  -- knows_acked
  · intro j o' cv' hj k hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hka j o' cv' hj k hkc' j'
  -- knows_store
  · exact hks
  -- knows_collect
  · exact hkc
  -- pend
  · intro j cv' hj hcvj
    rw [hop'] at hj
    rw [hcv] at hcvj
    by_cases hji : j = i
    · subst hji
      simp only [ite_true, Option.some.injEq] at hcvj
      subst hcvj
      rw [hopi] at hj; simp only [Option.some.injEq] at hj; subst hj
      obtain ⟨q₀, hq₀⟩ := mem_iff_getElem?.1 (H.cur_inv j _ hopi)
      have hkn : ∀ j' s, Knows c j j' s → s ≤ key (c.view j j') := by
        intro j' s hs
        rcases hs with hs | ⟨W, hW, -⟩
        · exact hs
        · rw [hq] at hW; simp at hW
      refine ⟨q₀, hq₀, ?_, ?_⟩
      · intro p p' j' m r v _ _ hp' hp
        exact hkn _ _ (hks p p' j' m r v hp' hp j halive)
      · intro p i' n' W' _ hp j'
        exact hkn _ _ (hkc i' n' W' (mem_iff_getElem?.2 ⟨p, hp⟩) j halive j')
    · simp only [hji, ite_false] at hcvj
      exact hpd j cv' hj hcvj

/-! ## Delivery by the MAC layer -/

lemma Inv.deliver {c : Config ι V} {h : History ι V} (I : Inv c h) (i k : ι) (o : Op V)
    (cv : View ι V) (got : Set ι) (hph : c.phase i = .bcast o cv got) :
    Inv { c with phase := Function.update c.phase i (.bcast o cv (insert k got)),
                 queue := Function.update c.queue k (c.queue k ++ [cv]) } h := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set c' : Config ι V := { c with phase := Function.update c.phase i (.bcast o cv (insert k got)), queue := Function.update c.queue k (c.queue k ++ [cv]) } with hc'
  have hop' : ∀ j, (c'.phase j).op? = (c.phase j).op? := by
    intro j; by_cases hj : j = i
    · subst hj; simp [c', hph, Phase.op?]
    · simp [c', hj]
  have hop : (fun j => (c'.phase j).op?) = (fun j => (c.phase j).op?) := funext hop'
  have hcv : ∀ j, (c'.phase j).cv? = (c.phase j).cv? := by
    intro j; by_cases hj : j = i
    · subst hj; simp [c', hph, Phase.cv?]
    · simp [c', hj]
  have hcvi : (c.phase i).cv? = some cv := by simp [hph, Phase.cv?]
  have hsys : ∀ W, SysView c' W → SysView c W := by
    rintro W ⟨k', hW | hW | hW⟩
    · exact ⟨k', Or.inl hW⟩
    · by_cases hk : k' = k
      · subst hk
        simp only [c', Function.update_self, List.mem_append, List.mem_singleton] at hW
        rcases hW with hW | rfl
        · exact ⟨k', Or.inr (Or.inl hW)⟩
        · exact ⟨i, Or.inr (Or.inr hcvi)⟩
      · simp only [c', Function.update_of_ne hk] at hW
        exact ⟨k', Or.inr (Or.inl hW)⟩
    · rw [hcv] at hW; exact ⟨k', Or.inr (Or.inr hW)⟩
  have hkn : ∀ k' j s, Knows c k' j s → Knows c' k' j s := by
    intro k' j s hs
    rcases hs with hs | ⟨W, hW, hs⟩
    · exact Or.inl hs
    · right; refine ⟨W, ?_, hs⟩
      by_cases hk : k' = k
      · subst hk; simp [c', hW]
      · simp [c', hk, hW]
  refine ⟨hop ▸ H, fun W hW => hvs W (hsys W hW), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj W hW
    rw [hcv] at hj; exact hkl j hj W (hsys W hW)
  · intro j v cv' hj hcvj
    rw [hop'] at hj; rw [hcv] at hcvj; exact hsc j v cv' hj hcvj
  · intro j o' cv' got' hj k' hk' hkc' j'
    by_cases hji : j = i
    · subst hji
      simp [c'] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      subst h1 h2 h3
      rcases hk' with rfl | hk'
      · right; exact ⟨cv, by simp [c'], le_rfl⟩
      · exact hkn _ _ _ (hkb j o cv got hph k' hk' hkc' j')
    · simp [c', hji] at hj
      exact hkn _ _ _ (hkb j o' cv' got' hj k' hk' hkc' j')
  · intro j o' cv' hj k' hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hkn _ _ _ (hka j o' cv' hj k' hkc' j')
  · intro p p' j m r v hp' hp k' hkc'
    exact hkn _ _ _ (hks p p' j m r v hp' hp k' hkc')
  · intro j n W hW k' hkc' j'
    exact hkn _ _ _ (hkc j n W hW k' hkc' j')
  · intro j cv' hj hcvj
    rw [hop'] at hj; rw [hcv] at hcvj; exact hpd j cv' hj hcvj

/-! ## The message handler (lines 7–8) -/

lemma Inv.handle {c : Config ι V} {h : History ι V} (I : Inv c h) (k : ι) (W : View ι V)
    (q : List (View ι V)) (hq : c.queue k = W :: q) :
    Inv { c with view := Function.update c.view k ((c.view k).merge W),
                 queue := Function.update c.queue k q } h := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set c' : Config ι V := { c with view := Function.update c.view k ((c.view k).merge W), queue := Function.update c.queue k q } with hc'
  have hWsys : SysView c W := ⟨k, Or.inr (Or.inl (by rw [hq]; simp))⟩
  have hvk : SysView c (c.view k) := ⟨k, Or.inl rfl⟩
  have hsys : ∀ W', SysView c' W' → ∀ j, ∃ W₀, SysView c W₀ ∧ W' j = W₀ j := by
    rintro W' ⟨k', hW' | hW' | hW'⟩ j
    · by_cases hk : k' = k
      · subst hk
        simp only [c', Function.update_self] at hW'
        subst hW'
        rcases newer_cases (c.view k' j) (W j) with h1 | h1
        · exact ⟨_, hvk, h1⟩
        · exact ⟨_, hWsys, h1⟩
      · simp only [c', Function.update_of_ne hk] at hW'
        exact ⟨W', ⟨k', Or.inl hW'⟩, rfl⟩
    · by_cases hk : k' = k
      · subst hk
        simp only [c', Function.update_self] at hW'
        exact ⟨W', ⟨k', Or.inr (Or.inl (by rw [hq]; simp [hW']))⟩, rfl⟩
      · simp only [c', Function.update_of_ne hk] at hW'
        exact ⟨W', ⟨k', Or.inr (Or.inl hW')⟩, rfl⟩
    · exact ⟨W', ⟨k', Or.inr (Or.inr hW')⟩, rfl⟩
  have hkn : ∀ k' j s, Knows c k' j s → Knows c' k' j s := by
    intro k' j s hs
    by_cases hk : k' = k
    · subst hk
      have hv : c'.view k' j = newer (c.view k' j) (W j) := by simp [c', View.merge]
      have hq' : c'.queue k' = q := by simp [c']
      unfold Knows; rw [hv, hq', key_newer]
      rcases hs with hs | ⟨W', hW', hs⟩
      · left; omega
      · rw [hq] at hW'
        rcases List.mem_cons.1 hW' with rfl | hW'
        · left; omega
        · right; exact ⟨W', hW', hs⟩
    · exact Knows.of_view_queue (by simp [c', hk]) (by simp [c', hk]) hs
  refine ⟨H, ?_, ?_, hsc, ?_, ?_, ?_, ?_, hpd⟩
  · intro W' hW' j m v hj
    obtain ⟨W₀, hW₀, he⟩ := hsys W' hW' j
    exact hvs W₀ hW₀ j m v (he ▸ hj)
  · intro j hj W' hW'
    obtain ⟨W₀, hW₀, he⟩ := hsys W' hW' j
    rw [he]; exact hkl j hj W₀ hW₀
  · intro j o' cv' got' hj k' hk' hkc' j'
    exact hkn _ _ _ (hkb j o' cv' got' hj k' hk' hkc' j')
  · intro j o' cv' hj k' hkc' j'
    exact hkn _ _ _ (hka j o' cv' hj k' hkc' j')
  · intro p p' j m r v hp' hp k' hkc'
    exact hkn _ _ _ (hks p p' j m r v hp' hp k' hkc')
  · intro j n W' hW' k' hkc' j'
    exact hkn _ _ _ (hkc j n W' hW' k' hkc' j')

/-! ## The acknowledgment -/

lemma Inv.ack {c : Config ι V} {h : History ι V} (I : Inv c h) (i : ι) (o : Op V)
    (cv : View ι V) (got : Set ι) (hph : c.phase i = .bcast o cv got)
    (hall : ∀ k, k ∉ c.crashed → k ∈ got) :
    Inv { c with phase := Function.update c.phase i (.acked o cv) } h := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  set c' : Config ι V := { c with phase := Function.update c.phase i (.acked o cv) } with hc'
  have hop' : ∀ j, (c'.phase j).op? = (c.phase j).op? := by
    intro j; by_cases hj : j = i
    · subst hj; simp [c', hph, Phase.op?]
    · simp [c', hj]
  have hop : (fun j => (c'.phase j).op?) = (fun j => (c.phase j).op?) := funext hop'
  have hcv : ∀ j, (c'.phase j).cv? = (c.phase j).cv? := by
    intro j; by_cases hj : j = i
    · subst hj; simp [c', hph, Phase.cv?]
    · simp [c', hj]
  have hsys : ∀ W, SysView c' W → SysView c W := by
    rintro W ⟨k', hW | hW | hW⟩
    · exact ⟨k', Or.inl hW⟩
    · exact ⟨k', Or.inr (Or.inl hW)⟩
    · rw [hcv] at hW; exact ⟨k', Or.inr (Or.inr hW)⟩
  refine ⟨hop ▸ H, fun W hW => hvs W (hsys W hW), ?_, ?_, ?_, ?_, hks, hkc, ?_⟩
  · intro j hj W hW
    rw [hcv] at hj; exact hkl j hj W (hsys W hW)
  · intro j v cv' hj hcvj
    rw [hop'] at hj; rw [hcv] at hcvj; exact hsc j v cv' hj hcvj
  · intro j o' cv' got' hj k' hk' hkc' j'
    by_cases hji : j = i
    · subst hji; simp [c'] at hj
    · simp [c', hji] at hj
      exact hkb j o' cv' got' hj k' hk' hkc' j'
  · intro j o' cv' hj k' hkc' j'
    by_cases hji : j = i
    · subst hji
      simp [c'] at hj
      obtain ⟨h1, h2⟩ := hj
      subst h1 h2
      exact hkb j o cv got hph k' (hall k' hkc') hkc' j'
    · simp [c', hji] at hj
      exact hka j o' cv' hj k' hkc' j'
  · intro j cv' hj hcvj
    rw [hop'] at hj; rw [hcv] at hcvj; exact hpd j cv' hj hcvj

/-! ## Crashes -/

omit [DecidableEq ι] in
lemma Inv.crash {c : Config ι V} {h : History ι V} (I : Inv c h) (i : ι) :
    Inv { c with crashed := insert i c.crashed } h := by
  obtain ⟨H, hvs, hkl, hsc, hkb, hka, hks, hkc, hpd⟩ := I
  refine ⟨H, hvs, hkl, hsc, ?_, ?_, ?_, ?_, hpd⟩
  · intro j o cv got hj k hk hkc' j'
    exact hkb j o cv got hj k hk (fun h' => hkc' (Set.mem_insert_of_mem _ h')) j'
  · intro j o cv hj k hkc' j'
    exact hka j o cv hj k (fun h' => hkc' (Set.mem_insert_of_mem _ h')) j'
  · intro p p' j m r v hp' hp k hkc'
    exact hks p p' j m r v hp' hp k (fun h' => hkc' (Set.mem_insert_of_mem _ h'))
  · intro j n W hW k hkc' j'
    exact hkc j n W hW k (fun h' => hkc' (Set.mem_insert_of_mem _ h')) j'

/-! ## All steps -/

lemma Inv.step {c c' : Config ι V} {h : History ι V} {l : Option (Label ι V)} (I : Inv c h)
    (hs : Step true c l c') : Inv c' (h ++ l.toList) := by
  cases hs with
  | invoke i o halive hidle => exact I.invoke i o hidle
  | exec i o halive hph hq => simpa using I.exec i o halive hph (hq rfl)
  | deliver i k o cv got hph hk => simpa using I.deliver i k o cv got hph
  | handle k W q halive hq => simpa using I.handle k W q hq
  | ack i o cv got halive hph hall => simpa using I.ack i o cv got hph hall
  | ret i o cv halive hph => exact I.ret i o cv hph
  | crash i => simpa using I.crash i

/-- The invariant holds in every reachable configuration of MAC-SC with handler priority. -/
lemma Reach.inv {c : Config ι V} {h : History ι V} (hr : Reach true c h) : Inv c h := by
  induction hr with
  | init => exact inv_init
  | step _ hs ih => exact ih.step hs

end Podc.AnonymousMACConsensus
