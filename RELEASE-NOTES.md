# Release notes for GAPT

## Version 2.15.1 (released on 2020-04-08)

* Updates to the 2.15 release notes

## Version 2.15 (released on 2020-03-30)

* DLS algorithm for formula equations
* Spin: saturation-based induction prover
* Update to Scala 2.13
* Refactoring of TIP tools, HOL to FOL translation and iProver interface

## Version 2.14 (released on 2019-03-04)

* Bug fixes
* Slakje: performance improvements

## Version 2.13 (released on 2018-12-03)

* Escargot: discrimination trees and feature vector indices.
* New term-based expansion tree implementation.
* Support for E 2.2.
* Slakje: automated theorem prover for first-order intuitionistic logic.
* JSON export and import for proofs and expressions
* Kolmogorov and Friedman translations

## Version 2.12 (released on 2018-08-17)

* SMTInterpol interface
* Support for Vampire 4.2.2
* JSON Serialization for expressions, LK Proofs, ND Proofs
* Improvements to the TIP Parser
* TPTP/TSTP Statistics
* New proof schemata

## Version 2.11 (released on 2018-04-30)

* Deskolemization of proofs with equational reasoning
* Root package was renamed from `at.logic.gapt` to just `gapt`
* Modified realizability
* New reductive cut-elimination implementation for LK

## Version 2.10 (released on 2018-03-19)

* Emoji support in formulas
* Implication is now → (instead of ⊃)
* LKt: proof terms for high performance cut normalization
* IEscargot prototype: an effective prover for first-order intuitionist logic
* User-defined operators in Babel (the formula parser)
* Simplifier tactic
* Formalization of the Fundamental Theorem of Arithmetic
* Hierarchical logging levels
* Many bugfixes for parametric polymorphism

## Version 2.9 (released on 2018-01-30)

* Support for the current (yet unreleased) TIP format
* Rewrite of the tree grammar-based induction prover
* Atomic expansion for expansion proofs
* Restructured user manual
* The Scala operator for function types is now `->:` instead of `->`
* Logback logging library was removed, use `verbose{...}` or `tactic.verbose` to enable logging
* Schematic structs and characteristic formulas for CERES
* Support for iProver 2.7
* Induction support for ExpansionProofToLK, LKToExpansionProof
* Constants now have an explicit list of type parameters

## Version 2.8 (released on 2017-10-09)

* Support for EProver 2.0
* Support for Vampire 4.2
* Experimental support for iProver (requires current development version)
* MutableContext now keeps track of automatically generated Skolem functions
* Cut-elimination no longer regularizes
* deskolemizeET now supports inner Skolemization

## Version 2.7 (released on 2017-07-05)

* Conversion from LK to natural deduction
* Induction elimination
* Grammar generation for Π₂-cut introduction

## Version 2.6 (released on 2017-04-03)

* Natural deduction
* Free monad for the SMT solver interface
* Portfolio mode in new viper command-line interface
* Skolemization with free variables support in ResolutionProver.getLKProof
* Primitive recursive definitions
* Proof schemata
* ACNF support in reductive cut-elimination

## Version 2.5 (released on 2017-02-22)

* Support veriT stable2016
* CERES version that directly produces expansion proofs
* Deskolemization
* First prototype of Pi2 cut-introduction
* Better error messages in Babel, the formula parser

## Version 2.4 (released on 2017-01-13)

* Update to Scala 2.12
* LKsk and Ral are replaced by the standard calculi, CERESω is now just CERES.
* Analytic induction prover
* Tons of proofs for problems from TIP
* Refactored Context data structure to enable future support for recursors

## Version 2.3 (release on 2016-10-10)

* The minimum required Java version is now Java 8
* String interpolators for sequents
* `:-` operator to construct sequents
* `loadExpansionProof` provides convenient access to TSTP proof import
* Refactored prooftool supports n-ary inferences now
* Conversion of unit-equational resolution proofs to unary LK proofs
* Special class for polarities instead of Booleans
* Support for Vampire 4.1
* Support for SPASS 3.9
* Context now support polymorphic declarations (for equality, ...)
* Many-sorted grammars
* Sound definition rules for LK

## Version 2.2 (released on 2016-07-09)

* New resolution calculus with Avatar splitting
* Vampire proof import with splitting
* More reliable leanCoP interface
* Metis interface
* TPTP problem parser
* Removal of obsolete or unmaintained code:
  * Schemata
  * Old LK implementation
  * Old LKsk implementation
  * Old LLK parser
  * Old Delta-Table implemenetation
  * XML parser
* Skolem inferences for LK
* Sequent is now a case class
* Subproofs can be hidden in prooftool now

## Version 2.1 (released on 2016-04-18)

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

