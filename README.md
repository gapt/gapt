<!---
vim:spell spelllang=en:
-->
## GAPT: General Architecture for Proof Theory
[![Build Status](https://travis-ci.org/gapt/gapt.svg?branch=master)](https://travis-ci.org/gapt/gapt) [![Coverage Status](https://coveralls.io/repos/gapt/gapt/badge.svg?branch=master)](https://coveralls.io/r/gapt/gapt?branch=master)

GAPT is a proof theory framework developed primarily at the Vienna University
of Technology. GAPT contains data structures, algorithms, parsers and other
components common in proof theory and automated deduction. In contrast to
automated and interactive theorem provers whose focus is the construction of
proofs, GAPT concentrates on the transformation and further processing of
proofs.

Website: https://logic.at/gapt

Contact: gapt@logic.at

### Example

One of the many features GAPT supports is an implementation of [Herbrand's
theorem](https://en.wikipedia.org/wiki/Herbrand%27s_theorem).  Here is how can
automatically generate a Herbrand sequent in GAPT:
```scala
val firstOrderSequent = existsclosure("p(c) | p(d)" +: Sequent() :+ "p(x)" map parseFormula)
Prover9 getExpansionSequent firstOrderSequent map { extractInstances(_) }
```
which returns the following Herbrand sequent:
```
Some((p(c)∨p(d)) :- p(c), p(d))
```

There are many more examples in the [user
manual](http://logic.at/gapt/downloads/gapt-user-manual.pdf), and you can look
into the [API documentation](http://logic.at/gapt/api/) for reference as well.

### Installation

There are [binary distributions](https://logic.at/gapt) available, you only
need to have Java installed to run them:
```
wget https://logic.at/gapt/downloads/gapt-1.10.tar.gz
tar xf gapt-1.10.tar.gz
cd gapt-1.10
./gapt.sh
```
This will drop you into a scala REPL with GAPT pre-loaded.

If you want to use GAPT in your project, all you have to do is add one line to
your SBT build file:
```scala
libraryDependencies += "at.logic.gapt" %% "gapt" % "1.10"
```

If you want to use the unstable git version of GAPT, you can use `sbt
console`--this will drop you into the same environment as `./gapt.sh` in the
binary distribution.

See [the wiki](https://github.com/gapt/gapt/wiki/Compiling-and-running-from-source)
for more details.

### System requirements

* Java 7 (or later)
* optional: [external tools](https://github.com/gapt/gapt/wiki/External-software)
* for development: [sbt](http://www.scala-sbt.org/)

### License

GAPT is free software licensed under the GNU General Public License Version 3.
See the file COPYING for details.
