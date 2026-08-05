# rsBTC Stage-3 Harness Contract

Status: Phase-1 review candidate

This document fixes the evidence vocabulary and binding rules used to exchange
the I-3/Base and C-2/Base pilot matrices. It is derived from lifecycle rev3
SHA-256
`4e5dd69daf7b09c5e2bc5eecff35f4eca18f9981f9edd2af81cd2bb78f74767a`
and evidence head
`0d0da9936706198a011df2b9036c6ac99fb03407`.

It does not define a deployment manifest, final contract bytes, node admission,
or production readiness.

## Outcome Vocabulary

Every expected result has the structured shape
`{stage, channel, category, target_rule}`. Accepting parents use
`target_rule = ALL_ACTIVE`; a negative or mutant names its exact first
discriminating Rule ID. The closed Phase-1 vocabulary is:

| Stage | Channel | Categories | Current evidence |
| --- | --- | --- | --- |
| `MANIFEST_LOAD` | `JSON_MANIFEST_LOADER` | `LOAD_ACCEPT`, `SCHEMA_REJECT`, `BINDING_REJECT`, `ISOLATION_REJECT` | Required of the Stage-3 loader; not yet produced by the Scala specs. |
| `FIXTURE_CONSTRUCTION` | `SCALA_FIXTURE_BUILDER` | `BUILD_ACCEPT`, `CONSTRUCTION_FAILURE` | A construction exception is currently a test failure, not an expected contract rejection. The harness must capture it explicitly before this channel can close a row. |
| `SIGMA_REDUCTION` | `ERGO_LIKE_TEST_INTERPRETER_V6` | `CONTRACT_TRUE`, `CONTRACT_FALSE`, `EVALUATION_FAILURE`, `PROOF_FAILURE` | Implemented by the current Scala harness. `PROOF_FAILURE` is a controlled subtype of interpreter failure and requires a proof-bearing fixture plus an accepting proof control. |
| `TARGET_NODE_VALIDATION` | `ERGO_REFERENCE_NODE` | `NODE_ACCEPT`, `NODE_REJECT` | Not observed in Phase 1. A row requiring this stage remains evidence-gated. |

`REJECTED` is not a canonical category because it collapses contract-false,
evaluation, proof, construction, and node failures. Transaction serialization
and monetary conservation are fixture-reachability preconditions in the
current harness, not independently observed rejection stages. They must pass
before a row can claim a later first discriminator. A Sigma result must not be
relabeled as target-node evidence.

## Executor-Bounty Decision For I-3

`Fe` is a branch-specific compiled family constant. It is not a per-deal field
and is not inherited from a predecessor box. A C-2 fixture with `Fe = 0`
therefore does not imply an I-3 fixture with `Fe = 0`.

The selected minimal Base/PLAIN Phase-1 profile fixes I-3 to `Fe = 0`:

- the executor output is absent;
- `Ye = 0`;
- the buyer-authorized I-3 transaction may still use one token-free external
  input for miner-fee uplift, Claim top-up, and clean change;
- a dedicated accepting I-3/Base parent is required for the executor-absence
  negative.

This is a profile decision, not a lifecycle-wide ban on bounties. A future
bountied I-3 profile would be a distinct compiled family with its own output
schema, value equations, positives, negatives, costs, and proposition hash.

## Family-Binding Authority

The machine-readable pilot candidate table is
`2026-08-05-rsbtc-base-family-bindings-candidate.json`. Its detached SHA-256
is
`01b97e371b0aff99d6b12308bea41b493d8bdd777bfe11041c68b2147e212472`.

The table distinguishes three authority classes:

1. `compiled_constant`: a typed literal consumed by the ErgoScript predicate;
2. `compiled_semantics`: a relation fixed by the branch code, such as output
   positions and optional-output rules;
3. `build_manifest_integrity`: an off-chain identifier for reviewed build
   material.

An output-schema digest belongs to class 3. It can bind a canonical descriptor
inside the build manifest, but the lifecycle does not read that digest on
chain. The on-chain authority is the compiled output-schema predicate. No
negative may claim contract enforcement by a manifest-only digest.

The current table is a pilot projection, not a deployment manifest. Only an
implemented binding for the row's exact branch may close a
`family:<symbol>` negative. A pending, selected-but-unimplemented, or undefined
binding may be generated as binding-gated, but it cannot count as executable
evidence until the compiled value and every materialization site are pinned.

## Derived-Update Closure

For every negative or mutant, the manifest declares one semantic fault and a
closed list of dependent updates. The harness must:

1. load the accepting parent;
2. apply only the declared fault coordinate;
3. regenerate every declared dependent value rather than trusting supplied
   bytes;
4. byte-compare regenerated txids, proofs, headers, balances, boxes, and other
   derived artifacts with the candidate fixture;
5. reject a missing update, an undeclared difference, or a changed value
   outside the declared closure;
6. run prechecks showing that the fixture reaches the declared stage; and
7. assert the declared first discriminating Rule ID.

One semantic fault does not mean one changed byte. Deterministic cryptographic
or accounting closure may change many bytes, but it must not alter a second
independent protocol fact.

## Coordinate Classes

The manifest uses exactly three authoritative fault-coordinate classes:

- `fixture:<json-pointer>`: validate the parent and child byte-for-byte, then
  permit only the fault plus its declared derived-update closure;
- `family:<symbol>`: resolve type, encoding, value, equality relation, and all
  materialization sites through the family-binding table; reject unresolved or
  mismatched bindings;
- `impl:<locator>`: bind the exact baseline source blob, unique source or IR
  locus, expected occurrence count, replacement, baseline compiled-tree hash,
  and mutant compiled-tree hash.

A pinned build alone is insufficient for `impl` coordinates because it does
not prove that the intended occurrence was the one changed. Derived values are
never authoritative fault coordinates.
