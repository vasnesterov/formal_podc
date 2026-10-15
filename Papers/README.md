# Paper formalizations

One folder per paper: `Papers/PODC<Year>/<ShortName>/`, containing
- the Lean files (module names `Papers.PODC<Year>.<ShortName>.*`; import from `Papers.lean`),
- `README.md`: citation (title, authors, DOI, arXiv), model assumptions, main results ↔ Lean names, status
  (open `sorry`s), token spend,
- `differencies.md`: every difference between the formalization and the paper .
