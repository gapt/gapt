# GAPT Check

Uses [GAPT](https://www.logic.at/gapt/) to check TSTP derivations.

## Usage

```bash
./gapt-check <PROOF>
```

where `<PROOF>` is a path to a TSTP derivation. The corresponding problem file is resolved
relative to the directory of the given input file.
For example, using the provided proofs in the `samples` directory we get

```bash
./gapt-check samples/COR000+1.s
% SZS status VerifiedGood
```

```bash
./gapt-check samples/EVL000+1.s
% SZS status VerifiedBad : inference step with name s1 is incorrect
```

```bash
./gapt-check samples/TMO000+1.s
% SZS status Timeout
```

## Requirements

GAPT Check requires a Java runtime version 21 to run.
We tested it with OpenJDK Runtime Environment Zulu21.44+17-CA

## Solutions

The `samples` directory contains a `Solutions` subdirectory which contains the expected outputs for the corresponding solution files, e.g., `samples/Solutions/EVL000+1.out` contains the expected output when running `./gapt-check samples/EVL000+1.s` from the directory where `gapt-check` resides.
