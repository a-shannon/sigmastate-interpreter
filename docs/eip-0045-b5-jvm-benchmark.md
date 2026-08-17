# EIP-0045 JVM verifier timing and resource evidence

`Eip0045VerifierBenchmark` is an opt-in evidence tool for calibrating the
fixed consensus charge of the stock-profile verifier. It is a JVM test-source
`runMain`, not a test suite, so ordinary builds do not execute it.

The harness loads the checked-in B1, B2, and B3 resources through the
production profile-package loader and hard-binds the candidate profile ID. It
then measures four preconstructed paths:

- a valid real RISC0 raw seal;
- a claim mismatch reached after all proof queries;
- a mutation in the final proof word reached through the cryptographic path;
- a wrong first transport-chunk length rejected before cryptographic work.

Each path is validated before timing. Warmup and sampling use a deterministic
rotating round-robin order so no path permanently occupies one position. One
sample is one complete `Risc0RawSealVerifier.verify` call. Profile loading,
fixture construction, JSON serialization, and summary calculation are outside
the timed samples. Version 3 records the current benchmark thread's
allocated-byte delta around each invocation and process-wide garbage-collector
count/time deltas across the complete sampling phase. It refuses to emit V3
evidence when either JVM counter is unavailable or moves backwards.

V3 can also bind a run to exact campaign-manifest bytes and a public run ID.
It hashes the ordered JVM input-argument strings reported by `RuntimeMXBean`
with explicit count and byte-length framing. The envelope retains only that
digest and argument count, not the raw arguments or the local manifest path.

## Recommended invocation

Use a fresh forked JVM, an otherwise idle host, and the final release JDK and
node JVM settings intended for the reference measurement. For example:

```text
sbt -batch "project coreJVM" "set Test / fork := true" "Test / runMain sigma.stark.profile.benchmark.Eip0045VerifierBenchmark --warmup-rounds 15 --sample-rounds 100 --implementation-revision REVISION_OR_TREE_DIGEST --cpu-model CPU_MODEL --campaign-manifest CAMPAIGN_MANIFEST --campaign-run-id RUN_ID --output target/eip0045-b5-evidence.json"
```

The output path must not already exist. Omitting `--output` emits the JSON to
standard output. `--help` lists all options. Shorter sample counts are useful
for smoke testing, but they are not substitutes for the agreed B5 campaign.
Replace the uppercase placeholders with public, shell-safe values. The
manifest must be nonempty and at most 1,048,576 bytes. Its path is used only to
read the bytes and is not written to the evidence.
An accepted campaign run must replace the default `unrecorded` implementation
revision with the exact public commit or a reviewed source-tree digest; this
field is intentionally declarative because the harness does not shell out to
Git or depend on a particular checkout layout.

The harness content-binds the manifest bytes and run ID but does not parse the
manifest or prove that the run ID belongs to it. A companion campaign validator
must check its schema, run membership, expected JVM-argument digest and matrix
policy. Omitting both campaign options remains useful for local diagnostics,
but the output says it is not acceptable campaign evidence. Supplying only one
option, or using `unrecorded` in campaign mode, fails before output.

## Evidence format and integrity

The output is canonical, single-line UTF-8 JSON containing:

- exact lengths and SHA-256 digests of every consumed package/proof resource;
- the profile ID, implementation revision, and timed verifier entry point;
- optional campaign-manifest byte length/digest and public run ID;
- JVM, operating-system, CPU, core-count, heap, JIT, and GC metadata;
- the ordered JVM input-argument count and domain-separated digest, without the
  raw argument strings;
- every raw nanosecond sample plus nearest-rank p50, p95, p99, and maximum;
- every current-thread allocated-byte sample plus the same percentile summary;
- process-wide collection-count and collection-time deltas for every reported
  garbage collector during the sampling phase;
- the benchmark method and explicit scope limitations.

The V3 `evidenceDigest` is:

```text
SHA-256(ASCII("Ergo.EIP0045.B5.Evidence.v3") || 0x00 || UTF8(payload))
```

Here `payload` is the exact compact JSON object stored in the top-level
`payload` field. The top-level `canonicalization` value identifies the fixed
field-order, no-whitespace encoding used by this version. Raw samples are kept
so reviewers can independently recompute every percentile. This digest binds
the exact payload bytes under the fixed V3 domain. Consumers must independently
require the exact top-level `schema`, `digestAlgorithm`, `digestDomain`, and
`canonicalization` values. Whole-file identity requires a separate full-file
hash. The evidence digest is not an operator signature or proof that a claimed
run actually occurred.

For JVM input arguments, V3 hashes the ASCII domain
`Ergo.EIP0045.B5.JvmInputArguments.v1`, a zero byte, the unsigned 32-bit
big-endian argument count, then each strict UTF-8 argument prefixed by its
unsigned 32-bit big-endian byte length. Reordering arguments or moving bytes
across argument boundaries changes the identity. The reviewed campaign
manifest binds only the expected argument count and this domain-separated
digest, plus an optional public-safe JVM policy identifier. Neither the
evidence nor a public campaign manifest should contain the complete raw JVM
argument strings. The companion validator compares the observed count/digest
with those expected identities.

## What one run proves

A successful run is digest-bound evidence for one verifier build, JVM process
and host under the recorded conditions. In campaign mode it also identifies
the exact manifest bytes, run ID and ordered JVM-input-argument digest observed
for that process. It can expose the gap between an early transport rejection
and the valid/late-rejection floor, and it can contribute to cost calibration.
Its allocation samples are JVM-reported approximations of Java-heap allocation
charged to the benchmark thread for each path, while its GC deltas show whether
the complete sampling phase coincided with collector work.

It does not close B5 by itself, choose a `fixedJit`, measure node admission or
ErgoTree preflight, control host scheduling or thermals, or replace the
multi-host/repeated-operator campaign required before activation.

Manifest hashing does not validate manifest semantics, attest the operator or
prove that the observed JVM arguments satisfy campaign policy. Those checks
remain obligations of the companion validator and reviewed evidence archive.

It does not measure native or other-thread allocations, peak live memory, a
scenario-specific GC pause, or the complete GC/resource envelope. Those remain
separate B5 obligations. The current-thread counter and process-wide GC deltas
are observations, not memory-safety or concurrency bounds.

## Retained local diagnostic

The repository retains one explicitly non-closing V1 timing-only local run in
`eip-0045-b5-local-diagnostic-v1.json`. It used the source-map identity
`15049a63cbf7c7fa43e1dc66a669b98a57988cc22c0cc0d6f53b0983a98ff64b`,
Microsoft OpenJDK 17.0.18, one 16-logical-processor Intel host, 15 rotating
warmup rounds, and 100 samples per scenario.

| Scenario | Query checkpoints | p50 | p95 | p99 | maximum |
|---|---:|---:|---:|---:|---:|
| valid proof | 50 | 25.572 ms | 33.564 ms | 37.359 ms | 39.621 ms |
| late claim mismatch | 50 | 25.723 ms | 32.895 ms | 34.290 ms | 37.271 ms |
| late cryptographic mutation | 50 | 25.646 ms | 34.589 ms | 37.942 ms | 38.503 ms |
| early transport rejection | 0 | 0.004 ms | 0.008 ms | 0.026 ms | 0.032 ms |

The evidence digest is
`60db4b9b71b66f076db2c46079f60f649301c1302f38ee52911f782cea46ba63`;
the complete JSON file SHA-256 is
`338410d5dbc423c5564da19abed3d49c8573321c05241ce403b97898f862a888`.
An independent recomputation from the exact embedded payload produced the
same evidence digest. This run is useful for falsifying microsecond-scale or
uniform-rejection assumptions, but its single host and unmeasured memory/GC
envelope prevent it from selecting the consensus charge.
