import Papers.PODC2019.RDMAAgreement.RB.Effect

/-!
# Algorithm 2 — monotonicity of the ghost variables

The ghost variables `signed`, `bc`, `echo`, `echoT`, `l1`, `dlv` only grow (write-once entries
for correct processes), by the local invariants `InvA`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- `b` is the (unique, see `canon_unique`) signed pair that may appear in correct `j`'s slot
`Value[j,k,q]`: `j`'s own broadcast (if `q = j`) or the pair `j` echoed. -/
def canon (s : St P M) (j q : P) (k : ℕ) (b : Base P M) : Prop :=
  b.sender = q ∧ b.key = k ∧ ((q = j ∧ s.bc j k = some b.msg) ∨ s.echo j q k = some b)

/-- Growth of the ghost variables over one step. -/
structure Grows (F : Finset P) (s s' : St P M) : Prop where
  signed : s.signed ⊆ s'.signed
  bc : ∀ j ∉ F, ∀ k m, s.bc j k = some m → s'.bc j k = some m
  echo : ∀ j ∉ F, ∀ q k b, s.echo j q k = some b → s'.echo j q k = some b
  echoT : ∀ j ∉ F, ∀ q k e, s.echoT j q k = some e → s'.echoT j q k = some e
  l1 : ∀ j ∉ F, ∀ q k x, s.l1 j q k = some x → s'.l1 j q k = some x
  dlv : ∀ j ∉ F, ∀ q k m, s.dlv j q k = some m → s'.dlv j q k = some m
  now : s'.now = s.now + 1

lemma Grows.canon {s s' : St P M} (G : Grows F s s') {j q : P} {k : ℕ} {b : Base P M}
    (hj : j ∉ F) (h : canon s j q k b) : canon s' j q k b := by
  obtain ⟨h1, h2, h3 | h3⟩ := h
  · exact ⟨h1, h2, Or.inl ⟨h3.1, G.bc j hj _ _ h3.2⟩⟩
  · exact ⟨h1, h2, Or.inr (G.echo j hj _ _ _ h3)⟩

lemma Step.grows {s s' : St P M} {ℓ : Label P M} (I : InvA F s) (h : Step F f s ℓ s') :
    Grows F s s' := by
  cases h with
  | sndOk hp hpc hv hc hs hk =>
    rename_i p q v c
    have T := I.thr p hp q
    have hph : s.phase p q = .wfs := T.ph .wfs (by simp [St.loc, hpc, PC.ph])
    have hnone : s.echo p q (s.key p q) = none := by
      rcases (T.wfs hph).2.2 with h | ⟨b, h⟩
      · exact h
      · simp [St.loc, hpc] at h
    refine ⟨fun x hx => by simp [St.tick, St.sign]; exact Or.inr hx, fun _ _ _ _ h => by
      simpa [St.tick, St.sign] using h, ?_, fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h, by simp [St.tick, St.sign]⟩
    intro j _ q' k b hb
    simp only [St.tick, St.sign, go_echo, upd3_apply2, upd2_apply]
    split_ifs with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      rw [Function.update_of_ne]; exact hb
      intro h; subst h; simp_all [St.key]
    · exact hb
  | valOk hp hpc hv hcard hb =>
    rename_i p q i acc v b
    have T := I.thr p hp q
    have hph : s.phase p q = .wfl1 := T.ph .wfl1 (by simp [St.loc, hpc, PC.ph])
    have hnone : s.l1 p q (s.key p q) = none := by
      rcases T.wfl1 hph with h | ⟨π, h⟩
      · exact h
      · simp [St.loc, hpc] at h
    refine ⟨fun x hx => by simp [St.tick, St.sign]; exact Or.inr hx, fun _ _ _ _ h => by
      simpa [St.tick, St.sign] using h, fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h, ?_,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h, by simp [St.tick, St.sign]⟩
    intro j _ q' k x hx
    simp only [St.tick, St.sign, go_l1, upd3_apply2, upd2_apply]
    split_ifs with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      rw [Function.update_of_ne]; exact hx
      intro h; subst h; simp_all [St.key]
    · exact hx
  | echoDone hp hpc =>
    rename_i p q j b
    have T := I.thr p hp q
    have hph : s.phase p q = .wfs := T.ph .wfs (by simp [St.loc, hpc, PC.ph])
    have hnone : s.echoT p q (s.key p q) = none := (T.wfs hph).1
    refine ⟨fun x hx => by simpa [St.tick, St.write, St.setPhase] using hx, fun _ _ _ _ h => by
      simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h, ?_,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      by simp [St.tick, St.write, St.setPhase]⟩
    intro j' _ q' k e he
    simp only [St.tick, St.write, St.setPhase, go_echoT, upd3_apply2, upd2_apply]
    split_ifs with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      rw [Function.update_of_ne]; exact he
      intro h; subst h; simp_all [St.key]
    · exact he
  | copyDone hp hpc =>
    rename_i p q j ρ m
    have T := I.thr p hp q
    have hnone : s.dlv p q (s.key p q) = none := T.dlvCur
    refine ⟨fun x hx => by simpa [St.tick, St.write, St.deliver] using hx, fun _ _ _ _ h => by
      simpa [St.tick, St.write, St.deliver] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.deliver] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.deliver] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.deliver] using h, ?_,
      by simp [St.tick, St.write, St.deliver]⟩
    intro j' _ q' k m' hm
    simp only [St.tick, St.write, St.deliver, go_dlv, upd3_apply2, upd2_apply]
    split_ifs with hjq
    · obtain ⟨rfl, rfl⟩ := hjq
      rw [Function.update_of_ne]; exact hm
      intro h; subst h; simp_all [St.key]
    · exact hm
  | bcast hp hidle =>
    rename_i p m
    have B := I.bcast p hp
    refine ⟨fun x hx => by simp [St.tick, St.doBcast]; exact Or.inr (Or.inr hx), ?_,
      fun _ _ _ _ _ h => by simpa [St.tick, St.doBcast] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.doBcast] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.doBcast] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.doBcast] using h, by simp [St.tick, St.doBcast]⟩
    intro j _ k m' hm
    simp only [St.tick, St.doBcast]
    by_cases hjp : j = p
    · subst hjp; simp only [Function.update_self]
      rw [Function.update_of_ne]; exact hm
      rintro rfl; simp [B.bcNone (s.bnext j + 1) (by omega)] at hm
    · rw [Function.update_of_ne hjp]; exact hm
  | l1Ok =>
    exact ⟨fun x hx => by simp [St.tick, St.sign]; exact Or.inr hx,
      fun _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.sign] using h, by simp [St.tick, St.sign]⟩
  | _ =>
    exact ⟨fun x hx => by simpa [St.tick, St.write, St.setPhase] using hx,
      fun _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      fun _ _ _ _ _ h => by simpa [St.tick, St.write, St.setPhase] using h,
      by simp [St.tick, St.write, St.setPhase]⟩

end Podc.RDMAAgreement.RB
