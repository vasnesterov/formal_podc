# Paper formalizations

One folder per paper: `Papers/PODC<Year>/<ShortName>/`, containing
- `README.md`, written for a reader who knows the paper: the verdict, the mistakes found in the paper explained in
  plain language, and a compact summary of the formalization (model, main theorems ↔ Lean names, what is not
  formalized);
- `differencies.md`: every difference between the formalization and the paper, including modelling choices and
  minor imprecisions;
- the Lean files (modules `Papers.PODC<Year>.<ShortName>.*`, all imported by `Papers.lean`).
