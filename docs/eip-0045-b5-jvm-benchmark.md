# EIP-0045 JVM verifier benchmark evidence

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
the timed samples.

## Recommended invocation

Use a fresh forked JVM, an otherwise idle host, and the final release JDK and
node JVM settings intended for the reference measurement. For example:

```text
sbt -batch "set coreJVM / Test / fork := true" "coreJVM / Test / runMain sigma.stark.profile.benchmark.Eip0045VerifierBenchmark --warmup-rounds 15 --sample-rounds 100 --implementation-revision REVISION_OR_TREE_DIGEST --cpu-model CPU_MODEL --output target/eip0045-b5-evidence.json"
```

The output path must not already exist. Omitting `--output` emits the JSON to
standard output. `--help` lists all options. Shorter sample counts are useful
for smoke testing, but they are not substitutes for the agreed B5 campaign.
Replace both uppercase placeholders with public, shell-safe labels for the
measured build and processor.
An accepted campaign run must replace the default `unrecorded` implementation
revision with the exact public commit or a reviewed source-tree digest; this
field is intentionally declarative because the harness does not shell out to
Git or depend on a particular checkout layout.

## Evidence format and integrity

The output is canonical, single-line UTF-8 JSON containing:

- exact lengths and SHA-256 digests of every consumed package/proof resource;
- the profile ID, implementation revision, and timed verifier entry point;
- JVM, operating-system, CPU, core-count, heap, JIT, and GC metadata;
- every raw nanosecond sample plus nearest-rank p50, p95, p99, and maximum;
- the benchmark method and explicit scope limitations.

`evidenceDigest` is:

```text
SHA-256(ASCII("Ergo.EIP0045.B5.Evidence.v1") || 0x00 || UTF8(payload))
```

Here `payload` is the exact compact JSON object stored in the top-level
`payload` field. The top-level `canonicalization` value identifies the fixed
field-order, no-whitespace encoding used by this version. Raw samples are kept
so reviewers can independently recompute every percentile. This digest binds
the file contents; it is not an operator signature or proof that a claimed run
actually occurred.

## What one run proves

A successful run is digest-bound evidence for one verifier build, JVM process,
and host under the recorded conditions. It can expose the gap between an early
transport rejection and the valid/late-rejection floor, and it can contribute
to cost calibration.

It does not close B5 by itself, choose a `fixedJit`, measure node admission or
ErgoTree preflight, control host scheduling or thermals, or replace the
multi-host/repeated-operator campaign required before activation.

It also does not measure peak live memory, allocation volume or allocation
rate, or the GC pause/resource envelope. Those remain separate B5 obligations;
recording the JVM's maximum heap and collector names is environment metadata,
not memory-safety or allocation evidence.

## Retained local diagnostic

The repository retains one explicitly non-closing local run in
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
