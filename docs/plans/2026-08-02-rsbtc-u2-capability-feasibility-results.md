# rsBTC U-2 Capability Feasibility Results

## Status

Local, non-normative Phase-1 evidence. These results select a candidate for the
next review step; they do not freeze the lifecycle ABI or establish production
readiness.

Lifecycle input: `rsbtc-insurance-vault-lifecycle-plan-rev3.md`, SHA-256
`4e5dd69daf7b09c5e2bc5eecff35f4eca18f9981f9edd2af81cd2bb78f74767a`.

## Experiment

Both candidates authorize a capability bound to the originating
`UnactivatedVault` id under the byte domain:

```text
"ERG-RSBTC" || version=1 || ergoNetwork=mainnet || bitcoinNetwork=mainnet || purpose=U2_ACTIVATE
```

The isolated probes use context var 7 for one bounded `Coll[Byte]`. They do not
modify the lifecycle contracts, field map, or successor equations.

The signed messages deliberately differ and are not interchangeable:

- Candidate A signs the raw `domain || originBoxId` bytes.
- Candidate B signs `SHA-256(domain || originBoxId)` because BIP340 requires a
  32-byte message in this probe.

The BIP340 primitive and vector are pinned against the
[Bitcoin BIPs specification](https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki)
and its
[official test vectors](https://github.com/bitcoin/bips/blob/master/bip-0340/test-vectors.csv).

| Property | Sigma message proof | BIP340 |
| --- | ---: | ---: |
| Envelope | 56 bytes (`challenge[24] || z[32]`) | 64 bytes (`rX[32] || s[32]`) |
| Isolated ErgoTree size | 211 bytes | 354 bytes |
| Full-path success cost | 406 | 396 |
| Full-path bad-signature cost | 406 | 396 |
| Signed message | Raw `domain || originBoxId` | `SHA-256(domain || originBoxId)` |
| External check | SigmaState `verifySignature` | Official BIP340 vector 0 |
| Key identity | Full compressed group element | X-only; `P` and `-P` are equivalent |
| Malformed commitment point | Not present in envelope | Invalid x-only point is an evaluation failure |

Costs are interpreter-reported values for the isolated verifier probes, not a
full U-2 transaction budget.

## Candidate A Findings

The existing Sigma simple-DLog message proof can be verified under Sigma V6.
The probe reconstructs the current strong Fiat-Shamir leaf exactly, enforces
the exact 56-byte envelope, requires `z < q`, rejects the identity key, and
binds the complete domain and `SELF.id`.

This candidate preserves the lifecycle's current key semantics: the committed
seller authorization key is the same full `GroupElement` used by transaction
authorization. The deterministic artifact is wire-compatible with the current
Sigma simple-DLog message-proof verifier. Separately, the core
`ProverInterpreter.signMessage` path is exercised with the same fixed key and
message; both a captured golden proof and a fresh proof from that path are
accepted by the off-chain and on-chain verifiers. This establishes core
signer/verifier compatibility, not compatibility with the intended seller
wallet or its signing policy.

The wire contract must nevertheless be explicit. The generic off-chain
`verifySignature` accepts trailing proof bytes in an explicit regression, while
the U-2 probe rejects the same proof. The Fiat-Shamir leaf framing, exact proof
length, holder encoding, origin id, raw message, deterministic proof, and
isolated compiled-tree SHA-256 are therefore pinned explicitly rather than
inferred from the permissive verifier.

## Candidate B Findings

The BIP340 verifier is technically feasible under Sigma V6 and agrees with the
official positive vector. It is slightly cheaper in the isolated cost model,
but its script is larger and it introduces a semantic mismatch with the
current lifecycle field map.

BIP340 identifies a public key by its x coordinate and normalizes it to even Y.
The verifier therefore normalizes `P` and `-P` to the same x-only key. A direct
same-message regression accepts one proof under both full points, and a
separate on-chain regression demonstrates authorization under an
opposite-parity committed key. Full-point identity is not preserved, so
Candidate B is not a drop-in verifier for the current seller authorization
field.

A BIP340 profile would need one of these explicit ABI choices:

1. require the seller authorization key to use canonical even-Y encoding at
   formation and define its identity as x-only everywhere; or
2. commit a distinct BIP340 activation-capability key.

The second choice keeps transaction-authorization semantics intact and avoids
cross-protocol key reuse. Invalid x-only commitment bytes also reject through
an interpreter evaluation failure rather than a normal contract-false result;
the spend remains invalid, but the failure channel must stay documented.

## Recommendation

Advance Candidate A as the canonical v1 U-2 feasibility target. It is the only
candidate tested here that preserves the jointly reviewed lifecycle field map,
full-key identity, and existing Sigma signer model without adding a new key or
changing formation rules. The ten-unit isolated cost difference in Candidate
B's favor is not material enough to outweigh those semantic changes.

Keep Candidate B as exploratory comparison evidence only. It is not a supported
optional profile and does not justify the additional negative-vector and
formation-policy surface unless the design deliberately reopens it.

Before the Candidate A ABI is frozen:

1. review the pinned transcript ABI byte-for-byte, including leaf framing,
   encodings, challenge truncation, envelope, domain, golden vector, and
   isolated compiled-tree hash;
2. prove that the intended seller-side tooling can produce the exact 56-byte
   artifact without exporting the secret key, constructs the domain internally,
   derives or confirms the origin id from structured input, and refuses
   arbitrary caller-selected messages under the seller role key; and
3. compose Candidate A into U-2 and pin the complete branch cost and compiled
   tree hash. The cost 406 remains an isolated-probe measurement.

If the intended wallet/tooling path cannot satisfy that policy, do not
substitute an ad hoc signer under the transaction-authorization key; add a
distinct activation-capability key or reopen the activation mechanism.

## Closeout Matrix

| Invariant | Producer / enforcement | Downstream consumer | Failure if relaxed | Isolated evidence |
| --- | --- | --- | --- | --- |
| Exact capability length | Seller tooling; outer U-2 verifier guard | Candidate-specific parser and group operations | Trailing-byte malleability or malformed parsing | Short, long, trailing, and guard-dominance cases |
| Domain and origin id | Seller tooling signs fixed domain plus originating box id | U-2 replay boundary | Cross-purpose, cross-network, or cross-deal activation | One mutation per domain component and alternate origin |
| Candidate A transcript | Sigma `signMessage`; exact strong Fiat-Shamir bytes | U-2 Sigma verifier | Signer/verifier disagreement or weaker statement binding | Serializer equality, pinned ABI tuple, core `signMessage`, and off-chain verification |
| Candidate A response encoding | U-2 verifier, `z < q` | Group equation | Non-canonical response aliases | Order and above-order mutations; a zero mutation is in range and fails by the equation |
| Candidate A full-key identity | Formation commits non-identity `GroupElement` | U-1/I-2/C-3 authorization and U-2 capability | Detached authorization no longer names the same role key | Wrong-key and identity-key negatives |
| Candidate A ABI types | U-2 contract reads R4 and var 7 | Holder and capability decoding | Missing or wrong-typed fields could be mislabeled or evaluated unexpectedly | Missing and wrong-typed R4/var-7 evaluation-failure regressions |
| Candidate B `r`/`s` ranges | U-2 verifier, `r < p` and `s < n` | Point lift and group equation | Non-canonical or invalid BIP340 values | Order, above-order, and field-prime mutations; zero response is in range and fails by the equation |
| Candidate B x-only identity | Formation policy, if Candidate B is selected | Every consumer of the seller role key | `P` and `-P` silently become one authorization identity | Opposite-parity acceptance regression |
| Invalid BIP340 x coordinate | Point decoder | U-2 verification failure channel | Evaluation failure could be mislabeled as contract false | Official malformed-point vector |
| Sigma version | Compiler and activated-version context | Both candidate verifiers | Unsupported primitives or divergent decoding | Pre-V6 parser rejection and V6 positive paths |

## Evidence Vector

| Dimension | Status |
| --- | --- |
| Implementation | `matrix_covered` for the isolated probes |
| Independent review | `completed` for `19a935907`; repairs in the current revision require re-review |
| CI | `not_run` |
| Target runtime | `verified` in the Sigma V6 JVM test interpreter |
| Readiness claim | `local_only` |

## Evidence Boundary

The focused specification now runs 21 tests and pins positive vectors, both
message transformations, the Candidate A ABI tuple and core signer path, all
domain components, origin id, wrong and identity keys, exact lengths and types,
scalar upper bounds versus equation failures, evaluation-order guards, BIP340
parity behavior, malformed x-only failure, V6 gating, script size, and
full-path isolated cost. The repaired revision still requires independent
review before this result can become normative or be composed into
value-releasing ErgoScript.
