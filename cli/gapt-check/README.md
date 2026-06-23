# GAPT Check

Uses [GAPT](https://www.logic.at/gapt/) to check TSTP derivations.

## Usage

```bash
./gapt-check <PROOF>
```

where `<PROOF>` is a path to a TSTP derivation. For example, using the provided
proofs in the `examples` directory we get

```bash
./gapt-check examples/correct_example1_c_proof.p
%SZS status Verified
```

```bash
./gapt-check examples/incorrect_example1_e_proof.p
%SZS status FailedVerified : ...
```
