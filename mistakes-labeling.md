# Labeling mistakes

Each mistake gets a label saying how hard it is to fix.

**A fix saves the author's intent.** First state what the author was trying to convey, in the paper's own words: what
it claims to achieve ("first", "optimal", "for any `f < n/3`"). Only then ask what it takes to make the paper convey
that correctly. An easy correction that gives up the intent is not a fix; a heavy repair that saves it is.

The label does not depend on how important the result is. A fix counts only if we proved it in Lean, except for ✏️
slips, which need no Lean proof. Typos that leave every claim correct are not labeled.

Always give a verdict to the best of your knowledge; never ask for manual review, and don't redo proofs yourself. An
unformalized gap counts as a mistake only if we investigated it deeply enough: we tried to understand and check the
proof, and it is really broken, or so messy and suspicious that it can't be trusted. If we did not look that deep, the
part is unchecked, not a mistake. Only as a last resort, a really unclear case is resolved in the paper's favor.

- ✏️ **Slip:** a typo that makes a claim wrong (the intended version is in the paper and its proof works for it), a degenerate case (`n ≤ 1`,
  empty sets, unused trivial corners; `K₂`, `P₃`, `n = 4`, `f = 1` are not degenerate), or an implied assumption
  (holds throughout the paper, which claims no more generality).
- 🔧 **Easy fix:** the intent is saved by a local change: a few lines, one constant, one condition.
- 🛠️ **Hard fix:** the intent is saved, but it takes a new argument or a redesign.
- ⚠️ **Weakened:** part of the intent is saved: the result holds only in a weaker form, for example with new genuine
  assumptions.
- ❌ **Intent lost:** the claim fails, or a specific proof step is wrong or missing, and the intent is not saved by
  anything we proved, even if a corrected statement is true.

## Examples

1. The author claims the best result, an `O(n)` algorithm, but it runs in `O(n log n)` and doesn't beat the previous
   one. Correcting the statement is easy, but the intent is lost: ❌.
2. The proof of the headline theorem is wrong, but we proved the theorem differently. The fix is heavy, but the intent
   is saved: 🛠️.
3. A secondary theorem is false without new genuine assumptions, and its proof is otherwise mostly correct: ⚠️. If the
   author clearly meant to claim it without those assumptions: ❌.
4. The pseudocode is wrong but easily fixed: 🔧, even if the headline theorem is completely false for the printed
   pseudocode.
