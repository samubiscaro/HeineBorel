# Heine–Borel theorem in Lean

This project formalizes the Heine–Borel theorem for metric spaces in Lean 4.

The development is carried out under the constraint that we may freely use Mathlib
*except* for `Mathlib.Topology`. All topological notions are therefore developed
from scratch in the setting of metric spaces.

The project is based on and extends the course repository
[MAT740 Topology in Lean HS25](https://github.com/MariusFurter/MAT740-Topology-in-Lean-HS25).

---

## Repository structure

- `MAT740TopologyInLeanHS25/`
  - `Definitions/`: core definitions and basic theory developed during the course
  - `Project/`: files specific to this project
    - `CompleteSpaces.lean`: completeness results for metric spaces
    - `BoundedSpaces.lean`: total boundedness results for metric spaces
    - `HeineBorel.lean`: formalization of the Heine–Borel theorem

- `Report/`
  - `main.typ`: Typst source of the written report
  - `Heine Borel.pdf`: compiled report (submitted)
  - `setup/`: Typst style and macro files
  - `work.bib`: bibliography

- `lean-toolchain`
- `lakefile.toml`, `lake-manifest.json`
- `README.md`

The main entry point of the formalization is
`MAT740TopologyInLeanHS25/Project/HeineBorel.lean`.