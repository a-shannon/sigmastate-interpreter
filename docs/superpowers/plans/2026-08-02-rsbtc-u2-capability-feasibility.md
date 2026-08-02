# rsBTC U-2 Capability Feasibility Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compare two bounded detached-signature verifiers for U-2 activation under Sigma V6 and produce evidence for the key-separation decision without changing the lifecycle contracts.

**Architecture:** Add one standalone test specification containing deterministic fixtures, minimal ErgoScript verifier probes, direct reduction helpers, adversarial cases, and measured cost/script-size evidence. Candidate A reproduces the existing Sigma simple-DLog `signMessage` transcript. Candidate B verifies official BIP340 vectors and a vault-id-bound fixture. The lifecycle harness, register map, and context-variable ABI remain untouched.

**Tech Stack:** Scala, ScalaTest/ScalaCheck property specifications, Sigma V6 compiler and interpreter, secp256k1 group operations, existing Sigma prover primitives.

---

## Task 1: Establish The Standalone Test Surface

**Files:**
- Create: `sc/shared/src/test/scala/sigmastate/utxo/examples/BitcoinRsBtcActivationCapabilityFeasibilitySpecification.scala`

- [ ] Add fixed protocol/network/purpose/version domain bytes and deterministic origin-box fixtures.
- [ ] Add a V6 compile helper and a direct verifier returning both the contract verdict and reduction cost without collapsing evaluation failures into `false`.
- [ ] Add a deliberately rejecting canonical-fixture test and run it to observe the expected red result before implementing either candidate.

Run:

```text
sbt "scJVM/testOnly sigmastate.utxo.examples.BitcoinRsBtcActivationCapabilityFeasibilitySpecification"
```

Expected: the canonical Candidate A property fails because the initial probe rejects.

## Task 2: Implement Candidate A, Sigma Message-Proof Compatibility

**Files:**
- Modify: `sc/shared/src/test/scala/sigmastate/utxo/examples/BitcoinRsBtcActivationCapabilityFeasibilitySpecification.scala`

- [ ] Generate a deterministic simple-DLog proof fixture using the production Sigma transcript and prover equations.
- [ ] Cross-check the fixture with the existing off-chain `verifySignature` implementation.
- [ ] Implement the V6 ErgoScript probe for the exact 56-byte `challenge || z` envelope.
- [ ] Enforce canonical scalar range and reconstruct the strong Fiat-Shamir leaf byte-for-byte.
- [ ] Make the canonical property green before adding adversarial cases.
- [ ] Add isolated negatives for wrong box id, every domain component, wrong key, short/long/trailing envelopes, and zero/order/above-order response boundaries.
- [ ] Add an evaluation-path regression proving that the length guard dominates parsing and group operations.

Expected: canonical proof verifies; every malformed or mismatched fixture either returns contract false at the declared predicate or preserves a separately asserted evaluation-failure channel.

## Task 3: Implement Candidate B, BIP340 Compatibility

**Files:**
- Modify: `sc/shared/src/test/scala/sigmastate/utxo/examples/BitcoinRsBtcActivationCapabilityFeasibilitySpecification.scala`

- [ ] Pin at least one official BIP340 vector as an independent primitive oracle.
- [ ] Add a deterministic domain-and-origin-bound BIP340 fixture with even-Y public-key normalization.
- [ ] Implement the exact 64-byte `rX || s` V6 verifier, tagged challenge hash, scalar bounds, point lift, and verification equation.
- [ ] Observe a red canonical property before wiring the verifier, then make it green.
- [ ] Add isolated negatives for wrong origin/domain/key, short/long/trailing envelopes, invalid x-only points, and zero/order/above-order scalar boundaries.
- [ ] Preserve and assert any unavoidable decode failure as a distinct channel; never relabel an exception as contract rejection.
- [ ] Add an evaluation-path regression proving that the 64-byte guard dominates point decoding and group work.

Expected: official and vault-bound canonical vectors agree with independent off-chain verification; all adversarial cases have explicit outcomes.

## Task 4: Compare The Candidates

**Files:**
- Modify: `sc/shared/src/test/scala/sigmastate/utxo/examples/BitcoinRsBtcActivationCapabilityFeasibilitySpecification.scala`

- [ ] Record serialized script size and successful/worst-case reduction cost for each probe.
- [ ] Pin exact envelope lengths, domain bytes, public-key normalization, and failure-channel behavior in tests.
- [ ] Test pre-V6 behavior for each V6-only primitive and record whether failure occurs at compilation or reduction.
- [ ] State only experimentally established interoperability claims; keep wallet/API availability and production nonce discipline separate.
- [ ] Decide whether the evidence supports same-key use or requires a distinct activation-capability key before field-map freeze.

## Task 5: Validate And Record The Pre-Freeze Recommendation

**Files:**
- Modify: `.agent/handoffs/2026-08-02_rsbtc-insurance-vault-live.md` in the workspace root, only after results are stable.

- [ ] Run the focused specification.
- [ ] Run `git diff --check` on the task-owned path set.
- [ ] Run the strict checkpoint cadence plan for the new specification.
- [ ] Perform the signing-boundary closeout: producer/consumer map, exact-check justification, branch/field negatives, and an independent-review requirement before any production claim.
- [ ] Record exact commit, test command, test count, costs, supported claims, rejected claims, and remaining gate in the active handoff.
- [ ] Run the publication guard on the exact staged diff before any local commit.
- [ ] Commit locally without pushing or modifying any public repository state.

**Completion rule:** The spike is complete only when both candidates have independently checked positive vectors, explicit malformed-input behavior, measured costs, and a defensible key-separation recommendation. A green experiment is not a production-readiness claim.
