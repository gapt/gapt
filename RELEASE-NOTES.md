# Release notes for GAPT

## Version 2.1 (unreleased)

* Escargot, a simple built-in superposition prover
* New expansion tree implementation, now with cuts!
* Type classes for types that are closed under substitution
* gaptic, LK proof input using tactics
  * Most of the included proofs are converted to gaptic
* Faster delta-table algorithm
* Complete input/output format Babel with string interpolators
* Context class that stores data types, constants, definitions, etc.
* SPASS interface supporting splitting inferences
* Skolem symbol validation
* Many-sorted to first-order reduction
* DRUP proof import from SAT solvers (Sat4j, PicoSAT, and Glucose)

## Version 2.0 (released on 2016-01-18)

* Refactoring of (most) calculi (LK, resolution mainly)
* Replay-based proof import for TPTP proofs, including a Vampire and E interface
* New cut-intro code that doesn't need interpolation
* sbt console
* Cleaned up prooftool now supports multiple open windows at once
* Brand new CERES implementation
* Tons of bug fixes

