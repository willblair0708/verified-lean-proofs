# verified-lean-proofs

A small, self-checking index of formal Lean 4 proofs of solved research problems,
hosted as stable `formal_proof` targets for
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

Every push runs the same gate the proofs are claimed to pass: the whole library
builds against a pinned Mathlib, and a `#print axioms` audit fails the build if
any headline theorem uses `sorry` or any axiom outside the kernel set
`[propext, Classical.choice, Quot.sound]`. A green badge here is a standing,
re-checkable guarantee, not a one-time assertion.

## Layout

```
ErdosProblems/          one Lean file per problem
Audit.lean              #print axioms for every headline theorem
proofs.yaml             machine-readable index (consumed by erdos-fc-sync)
scripts/check_axioms.sh the verification gate
scripts/check_manifest.sh keeps proofs.yaml in sync with the audit
```

## Verify locally

```bash
lake exe cache get
lake build
bash scripts/check_axioms.sh
```

## Index

| Problem | Theorem | Statement | FC |
|--------:|---------|-----------|----|
| [154](https://www.erdosproblems.com/154) | `Erdos154.erdos_154_sumset` | For a Sidon set `A` with `\|A\| ~ √N`, the sumset `A+A` is equidistributed over residue classes mod `m`. | [#4340](https://github.com/google-deepmind/formal-conjectures/pull/4340) |

## Relationship to the rest of the ecosystem

- **erdos-fc-sync** reads `proofs.yaml` as a proof source. When a problem has a
  clean proof here that Formal Conjectures does not yet link, the sync surfaces
  it as a contribution target.
- Proofs that build on existing formalizations carry that lineage in their
  headers and in `proofs.yaml`. The 154 sumset proof builds on the Lindström
  residue-distribution theorem for `A` (formal authors Aristotle and Wouter van
  Doorn, hosted via `plby/lean-proofs`) and transfers it to `A+A` using the
  Sidon property.

## Adding a proof

1. Add `ErdosProblems/Erdos<n>.lean`, building cleanly against the pinned Mathlib.
2. Add its module import and a `#print axioms` line to `Audit.lean`.
3. Add an entry to `proofs.yaml`.
4. `bash scripts/check_axioms.sh && bash scripts/check_manifest.sh` must pass.

## License

Original contributions in this repository are MIT licensed (see `LICENSE`).
Third-party formalizations included as build dependencies retain their original
licenses, noted in their file headers; Mathlib is Apache-2.0.
