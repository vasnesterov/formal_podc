# Labeling a paper

A reviewer who did not label the mistakes reads the paper and its labeled mistakes, then gives the paper one label and
one sentence saying why.

The label says how hard it is to save what the paper set out to convey, judged as a whole. Weigh each mistake by how
much the paper depends on it. Never average, and never count correct parts against a mistake. The label covers only
what was checked; if the paper's main point was not checked, the sentence must say so.

- ✅ **Correct:** no labeled mistakes.
- ✏️ **Slip:** only slips: the paper is right apart from typos, degenerate cases and implied assumptions.
- 🔧 **Easy fix:** the paper's point is saved by local changes, and anything lost is minor.
- 🛠️ **Hard fix:** the paper's point is saved, but it takes a new argument or a redesign.
- ⚠️ **Weakened:** the paper keeps real value, but part of what it set out to convey is lost or holds only in a weaker
  form.
- ❌ **Intent lost:** the paper's main point does not survive, even if other parts of it are correct.

## Examples

1. The paper's protocol is broken as printed, and a one-line fix saves it: 🔧.
2. All main results hold, and a by-product that nothing depends on is false: 🔧.
3. The main theorem's proof is wrong, and we proved the theorem differently: 🛠️.
4. The paper has two equal halves, and one of them is lost: ⚠️.
5. The algorithm named in the title is refuted, and two other algorithms are fully correct: ❌.
