# GAPT Check

Uses [GAPT](https://www.logic.at/gapt/) to check TSTP derivations.

## Usage

```bash
./gapt-check <PROOF>
```

where `<PROOF>` is a path to a TSTP derivation. For example, using the provided
proofs in the `samples` directory we get

```bash
./gapt-check samples/correct_proof.p
%SZS status VerifiedGood
```

```bash
./gapt-check samples/evil_proof.p
%SZS status VerifiedBad : ...
```

```bash
./gapt-check samples/timeout_proof.p
%SZS status Timeout
```
