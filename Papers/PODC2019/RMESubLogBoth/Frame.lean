import Papers.PODC2019.RMESubLogBoth.Model

/-!
# A step of one process does not change another process's program counter
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

lemma Step.pc_other {c c' : Cfg k} {q : Fin k} (h : Step c q c') {p : Fin k} (hp : p ≠ q) :
    c'.pc p = c.pc p := by
  cases h <;> simp [Cfg.setPc, Function.update, hp]

lemma Step.node_other {c c' : Cfg k} {q : Fin k} (h : Step c q c') {p : Fin k} (hp : p ≠ q) :
    c'.node p = c.node p := by
  cases h <;> simp [Cfg.setPc, Function.update, hp]

lemma Next.pc_other {c c' : Cfg k} {e : Ev k} (h : Next c e c') {p : Fin k}
    (hp : e ≠ .step p) (hc : e ≠ .crash p) : c'.pc p = c.pc p := by
  cases e with
  | step q =>
    have : p ≠ q := fun h' => hp (h' ▸ rfl)
    exact Step.pc_other h this
  | crash q =>
    have : p ≠ q := fun h' => hc (h' ▸ rfl)
    change c' = c.crash q at h
    subst h; simp [Cfg.crash, Cfg.setPc, this]

lemma Next.node_other {c c' : Cfg k} {e : Ev k} (h : Next c e c') {p : Fin k}
    (hp : e ≠ .step p) : c'.node p = c.node p := by
  cases e with
  | step q =>
    have : p ≠ q := fun h' => hp (h' ▸ rfl)
    exact Step.node_other h this
  | crash q =>
    change c' = c.crash q at h
    subst h; rfl

end Podc.RMESubLogBoth
