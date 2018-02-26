<!---
vim:spell spelllang=en:
-->
## GAPT: General Architecture for Proof Theory

[![Join the chat at https://gitter.im/gapt/gapt](https://badges.gitter.im/gapt/gapt.svg)](https://gitter.im/gapt/gapt?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![Build Status](https://travis-ci.org/gapt/gapt.svg?branch=master)](https://travis-ci.org/gapt/gapt) [![codecov.io](https://codecov.io/github/gapt/gapt/coverage.svg?branch=master)](https://codecov.io/github/gapt/gapt?branch=master)

GAPT is a proof theory framework developed primarily at the Vienna University
of Technology. GAPT contains data structures, algorithms, parsers and other
components common in proof theory and automated deduction. In contrast to
automated and interactive theorem provers whose focus is the construction of
proofs, GAPT concentrates on the transformation and further processing of
proofs.

Website: https://logic.at/gapt

Contact: [mailing list](https://groups.google.com/forum/#!forum/gapt-group)

### Example

One of the many features GAPT supports is an implementation of [Herbrand's
theorem](https://en.wikipedia.org/wiki/Herbrand%27s_theorem).  Here is how you can
automatically generate a Herbrand disjunction in GAPT:
```scala
Escargot.getExpansionProof(fof"P(c) ∨ P(d) → ∃x P(x)").map(_.deep)
```
which returns the following Herbrand disjunction (the quantifier on the right
has been expanded):
```
Some( ⊢ P(c) ∨ P(d) → P(c) ∨ P(d))
```

You can also use `Prover9`, `Vampire`, `EProver`, and lots of other provers
instead of the built-in `Escargot` prover, if you have them installed.
There are many more examples in the [user
manual](http://logic.at/gapt/downloads/gapt-user-manual.pdf), and you can look
into the [API documentation](http://logic.at/gapt/api/) for reference as well.

### Installation

There are [binary distributions](https://logic.at/gapt) available, you only
need to have Java installed to run them:
```
wget https://logic.at/gapt/downloads/gapt-2.9.tar.gz
tar xf gapt-2.9.tar.gz
cd gapt-2.9
./gapt.sh
```
This will drop you into a scala REPL with GAPT pre-loaded.

If you want to use GAPT in your project, all you have to do is add two lines to
your SBT build file:
```scala
resolvers += Resolver.jcenterRepo
libraryDependencies += "at.logic.gapt" %% "gapt" % "2.9"
```

If you want to use the unstable git version of GAPT, you can use `sbt
console`--this will drop you into the same environment as `./gapt.sh` in the
binary distribution.

See [the wiki](https://github.com/gapt/gapt/wiki/Compiling-and-running-from-source)
for more details.

### System requirements

* Java 8 (or later)
* optional: [external tools](https://github.com/gapt/gapt/wiki/External-software)
* for development: [sbt](http://www.scala-sbt.org/)

### License

GAPT is free software licensed under the GNU General Public License Version 3.
See the file COPYING for details.
