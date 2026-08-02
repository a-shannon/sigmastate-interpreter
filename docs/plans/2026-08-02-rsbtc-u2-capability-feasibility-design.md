# rsBTC U-2 Detached Capability Feasibility Design

## Status

Local, non-normative feasibility work. This design does not select a production
signature scheme, change the lifecycle contracts, or establish production
readiness.

## Objective

Determine whether the U-2 activation authorization can be carried as one
bounded `Coll[Byte]` context value and verified under Sigma V6 at acceptable
cost without freezing an ad hoc cryptographic construction. The result must
also decide whether reusing the seller transaction-authorization key is a
defensible default or whether the lifecycle needs a distinct activation key.

## Constraints

- The signed semantic message is the originating `UnactivatedVault` box id
  under explicit protocol, network, purpose, and version domain separation.
- The capability does not authorize caller-selected terms. U-2 successor
  equations remain the authority for every immutable term.
- The experiment does not modify the existing lifecycle harness, register map,
  state scripts, or context-variable assignments.
- Every parser and verifier rejects malformed, non-canonical, out-of-range, or
  trailing data before expensive group operations where possible.
- Test signing uses fixed keys and deterministic fixtures. No wallet, live key,
  node, or network operation is involved.

## Candidate A: Sigma Message-Proof Compatibility

Use the existing Sigma interpreter's simple DLog `signMessage` output as the
wire artifact. A simple proof is exactly 56 bytes: a 24-byte challenge followed
by a 32-byte response. The on-chain probe reconstructs the DLog commitment,
serializes the simple Fiat-Shamir leaf exactly, hashes that transcript together
with the domain-separated message, and compares the first 24 hash bytes to the
provided challenge.

Advantages:

- reuses the Ergo Sigma prover, key type, and existing message-signing vectors;
- avoids inventing a new signer or nonce algorithm;
- uses the ecosystem's strong Fiat-Shamir statement/commitment binding.

Risks to test:

- faithfully reproducing the exact Fiat-Shamir leaf bytes in ErgoScript;
- enforcing the exact 56-byte proof length because the off-chain verifier
  currently tolerates appended bytes;
- cost of two exponentiations, point inversion/multiplication, serialization,
  and hashing;
- dependence on the existing prover's random-nonce boundary.

## Candidate B: BIP340-Compatible Capability

Use a fixed 64-byte BIP340 signature over a 32-byte, domain-separated digest of
the origin box id. The probe normalizes the committed secp256k1 public key to
the BIP340 even-Y form, lifts the signature's x-only commitment, performs the
tagged challenge hash, and verifies the BIP340 equation.

Advantages:

- established external specification and public test vectors;
- fixed canonical envelope and standardized deterministic-nonce construction;
- independent oracle implementations are readily available.

Risks to test:

- public-key even-Y normalization from the committed Ergo group element;
- implementation and cost of the exact BIP340 tagged hash and equation;
- availability of compatible signing support in reference Ergo tooling;
- cross-protocol use of the seller key even when both protocols are sound.

## Rejected Default: Custom Full-Point Schnorr

A locally defined `R || z` construction is useful only as a primitive smoke
test. It is not a candidate default because the transcript, nonce derivation,
encoding, malleability rules, and cross-protocol security would all become new
protocol surface owned by this project.

## Key-Separation Decision

The comparison records two outcomes independently:

1. whether a candidate is technically verifiable under the target Sigma
   version and cost envelope;
2. whether using the existing seller authorization key is justified by a
   standard signer and domain-separated transcript.

If neither candidate gives a reviewed, interoperable same-key construction,
the lifecycle must commit a distinct activation-capability key before its field
map is frozen. The experiment must not conceal that consequence by selecting a
convenient test key.

## Experimental Architecture

One standalone Scala specification owns:

- fixed domain and origin-id fixtures;
- fixed external or interpreter-generated signature vectors;
- minimal candidate-specific ErgoScript strings;
- no-secret reduction helpers;
- malformed-envelope, wrong-message, wrong-key, and boundary fixtures;
- measured reduction cost and serialized script size;
- a comparison record containing supported, rejected, and unresolved claims.

Candidate probes are independent. Failure of one does not weaken or alter the
other. Neither is imported by the lifecycle specification.

## Required Evidence

For each candidate:

- V6 compilation succeeds and pre-V6 compilation or reduction fails where a
  V6-only primitive is required;
- the canonical vector verifies;
- wrong origin id, domain, network, purpose, version, and public key reject;
- short, long, trailing-byte, malformed-point, zero, order, and above-order
  scalar cases reject through the intended first predicate;
- malformed envelopes return contract false rather than being accepted through
  exception collapse;
- the size guard dominates all decoding and group work;
- measured worst-case cost and script size are recorded without converting the
  experiment into a production-readiness claim;
- off-chain reference verification agrees with the ErgoScript verdict.

## Decision Rule

Prefer Sigma message-proof compatibility if its exact transcript can be
reproduced compactly and canonically and its signer boundary is suitable.
Otherwise prefer BIP340 only if its standard vectors, key normalization,
tooling path, and cost all close. If both fail or same-key use remains
unjustified, require a distinct activation key or reopen activation mechanism B
before lifecycle freeze.
