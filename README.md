## Practicum "Logik II"
Exercise implementations for the practicum to ["Logik II" at LMU, SoSo2017](http://www.mathematik.uni-muenchen.de/~schwicht/lectures/logic/ss17/). The aim of the practicum is to implement a simplified version of the logical machinery underlying the Minlog proof assistant (the theory of which is covered in the lecture). 


#### Planned Files:

- `1-scheme-exercises.scm`
- `2-untyped-lambda-calculus.scm`
  - Scheme representation for lambda terms
  - Normalization/evaluation of LC
  - Example: Church numerals
- `3-minimal-implicational-logic.scm`
  - Scheme representation for `->`-formulas
  - Derivations represented as typed lambda terms
  - Basic proof checking & search
- `4-propositional-logic.scm`
  - `3-..scm` extended with scheme for inductively defined connectives
- `5-minimal-predicate-logic.scm`
  - TODO: `3-..scm` extended by treatment of all-quantifier.
- `6-inductive-algebras.scm`
  - TODO: `5-..scm` + scheme to inductively specify domains of quantification.
- `7-defined-function-constants.scm`
  - TODO
- `8-inductive-predicates.scm`
  - TODO
- `A1-interactive-derivation-building.scm`
  - helper functions for interactively constructing (propositional) derivation trees/terms from bottom to top.
- `A2-propositional-minlog-derivations.scm`
  - Implementation of (propositional) interactive proof construction in Minlog
- `B1-helper-functions.scm`
  - auxiliary functions, loaded by above files
