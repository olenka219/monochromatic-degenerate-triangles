# Every two-colouring of the plane contains a monochromatic T(1,3,4)

Paper, certificates, verifiers and interactive walkthroughs.

## Layout
- `paper/` — `T134.tex`, `T134.pdf`, generated tables (`tables_*.tex`, `table_*.tex`) and `figures/`.
- `certificates/`
  - `ruleA_four_cases.json` — Rule A: four symmetry cases, one split each (49 points).
  - `ruleA_two_splits.json` — Rule A, alternative proof: two splits, the first at q (81 points).
  - `ruleB_cases.json` — Rule B: five common deductions in Λ, then one short chain per long direction of qΛ.
- `code/`
  - `verify_ruleA.py`, `verify_ruleB.py` — standard-library verifiers.
  - `make_paper_assets.py` — regenerates the paper's tables and figures from the certificates (needs matplotlib).
- `walkthroughs/` — self-contained HTML pages stepping through Rule A (both proofs) and Rule B. Open in a browser.

## Conventions
ω = e^{iπ/3}, Λ = Z[ω], π = 2+ω, and q = π/π̄ = (3+5ω)/7, a unit with π = q·π̄, so Λ and qΛ share
the index-7 sublattice πΛ. Certificates use numerator coordinates: `[a,b]` means (a + bω)/7.
Only four triangle types are ever used: T(1), T(3), T(4) and the collinear T(1,3,4); by the
eight-point bridge lemma none of them can be monochromatic in a T(1,3,4)-free colouring.

## Verify
```
cd code
python3 verify_ruleA.py
python3 verify_ruleB.py
```
Regenerate tables and figures, then rebuild the paper:
```
cd code && python3 make_paper_assets.py
cd ../paper && pdflatex T134.tex && pdflatex T134.tex
```

## Structure of the proof
1. Rule A — no maximal monochromatic run of exactly three in a unit triangular lattice (Theorem 3.13 of the
   thesis, two reflections, four cases with one split each).
2. Bands of width four with steps 4 or 5 (from Rule A and Theorem 3.13).
3. Rule B — the steps never turn; equivalently, open pairs above and below a row always have different
   colours. Proved by forcing alone, with the four-apart rule in qΛ.
4. Any two points at distance 8 share a colour; two radius-8 circles then give a monochromatic unit triangle.
