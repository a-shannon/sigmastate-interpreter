# EIP-0045 JVM verifier timing and resource evidence

`Eip0045VerifierBenchmark` is a JVM test-source `runMain` for collecting
evidence used to calibrate the stock-profile verifier's fixed consensus charge.
Full campaigns are opt-in. The runner is not itself a ScalaTest suite, while
focused support tests exercise bounded zero-warmup, one-sample smoke runs.

The benchmark loads the checked-in B1, B2, and B3 resources through the
production profile-package loader and hard-binds the candidate profile ID. It
also loads a checked-in po2-16 interoperability KAT from a separate source,
derives its claim from the image ID and journal, and compares that result with
the retained claim digest. It then measures six preconstructed scenarios:

- a valid real RISC0 raw seal;
- a wrong first transport-chunk length rejected before cryptographic work;
- a canonical raw-seal mutation rejected by the terminal control allowlist;
- a mutation in the final proof word rejected in FRI after reaching all 50 proof-query checkpoints;
- a claim mismatch reached after all proof queries;
- the independently sourced real raw seal accepted as a normal po2-16 lift.

Each scenario is validated before timing. Warmup and sampling use a deterministic
rotating round-robin order so no path permanently occupies one position. One
sample is one complete `Risc0RawSealVerifier.verify` call. Profile loading,
fixture construction, claim derivation, validation probes, JSON serialization,
and summary calculation are outside the timed samples. Validation invokes every
scenario before warmup, so a zero-warmup smoke is not a cold-start measurement.
Version 5 records the current benchmark thread's
allocated-byte delta around each invocation and process-wide garbage-collector
count/time deltas across the complete sampling phase. It also records a
per-pool `MemoryPoolMXBean` phase envelope. After validation and warmup, the
runner checks the ordered pool topology, resets each retained pool handle's
peak tracker, reads `afterResetPeakUsage`, runs the GC-bracketed sample loop,
then reads `endUsage`, `finalPeakUsage` and the final topology. It refuses to
emit V5 evidence when a required counter, pool, reset or snapshot is
unavailable or invalid. The canonical `memoryPoolScope` names the sequential
per-pool `MemoryPoolMXBean.resetPeakUsage()`, `getPeakUsage()` and `getUsage()`
boundary calls. Runner and JVM-management overhead inside those boundaries is
part of the phase envelope, even though it is outside each timed verifier call.

V5 can also run under a declared campaign policy. The producer takes one
defensive copy of the manifest bytes, parses that copy and computes its length
and SHA-256. It then resolves run to cell to environment/JVM policy. Revision,
warmup rounds, sample rounds, environment fields, ordered collector names,
ordered memory-pool identities and the JVM argument count/digest must all match
before the profile fixture is loaded or the verifier is called. The envelope
retains the manifest identity and public run ID, never the local manifest path
or raw JVM arguments.

## Recommended invocation

Use a fresh forked JVM, an otherwise idle host, and the final release JDK and
node JVM settings intended for the reference measurement. No other benchmark,
monitoring agent or JMX client may call `resetPeakUsage()` during the run. For
example:

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
field is intentionally declarative because the runner does not shell out to
Git or depend on a particular checkout layout.

Campaign mode is fail-closed. The runner parses the canonical manifest,
requires the run ID to be declared, selects that run's cell and checks the
observed process against its policy before verifier setup. There is no fallback
from a rejected campaign run to diagnostic mode. Omitting both campaign options
still runs a local diagnostic, and the output labels it as non-campaign evidence.
Supplying only one option, or using `unrecorded` in campaign mode, fails before
output.

## Evidence format and integrity

The output is canonical, single-line UTF-8 JSON containing:

- exact lengths and SHA-256 digests of every consumed package/proof resource;
- the profile ID, implementation revision, and timed verifier entry point;
- optional campaign-manifest byte length/digest and public run ID;
- JVM, operating-system, CPU, core-count, heap, JIT, and GC metadata;
- the sorted `(name, memoryType)` identity of every observed JVM memory pool;
- the ordered JVM input-argument count and domain-separated digest, without the
  raw argument strings;
- every raw nanosecond sample plus nearest-rank p50, p95, p99, and maximum;
- every current-thread allocated-byte sample plus the same percentile summary;
- the validation-only boundary and last verifier checkpoint for each scenario;
- process-wide collection-count and collection-time deltas for every reported
  garbage collector during the sampling phase;
- each pool's after-reset peak, end usage and final peak snapshots, with raw
  `usedBytes`, `committedBytes` and `maxBytes` values;
- the benchmark method and explicit scope limitations.

The V5 `evidenceDigest` is:

```text
SHA-256(ASCII("Ergo.EIP0045.B5.Evidence.v5") || 0x00 || UTF8(payload))
```

Here `payload` is the exact compact JSON object stored in the top-level
`payload` field. The top-level `canonicalization` value identifies the fixed
field-order, no-whitespace encoding used by this version. Raw samples are kept
so reviewers can independently recompute every percentile. This digest binds
the exact payload bytes under the fixed V5 domain. Consumers must independently
require the exact top-level `schema`, `digestAlgorithm`, `digestDomain`, and
`canonicalization` values. Whole-file identity requires a separate full-file
hash. The evidence digest is not an operator signature or proof that a claimed
run actually occurred.

For JVM input arguments, V5 retains the separate ASCII domain
`Ergo.EIP0045.B5.JvmInputArguments.v1`, a zero byte, the unsigned 32-bit
big-endian argument count, then each strict UTF-8 argument prefixed by its
unsigned 32-bit big-endian byte length. Reordering arguments or moving bytes
across argument boundaries changes the identity. The reviewed campaign
manifest binds only the expected argument count and this domain-separated
digest, plus an optional public-safe JVM policy identifier. Neither the
evidence nor a public campaign manifest should contain the complete raw JVM
argument strings. The companion validator compares the observed count/digest
with those expected identities.

This digest is a stable fingerprint, not an anonymizer. Reusing the same JVM
argument vector produces the same value and can link records across runs or
archives. It can also support guessing when the plausible argument set is
small. Do not treat the digest as confidential, anonymous or proof that the
arguments were safe; its only job here is exact policy matching without
publishing the raw vector.

## Campaign manifest and archive validation

`Eip0045CampaignValidator` consumes a canonical `CampaignManifestV3` and the
V5 evidence files named by that campaign. The manifest fixes the candidate
profile, implementation revision, verifier entry point, twelve resource
identities, six scenarios, warmup and sample rounds, and every V5 format
constant used by the producer. Revision identities use either
`commit:` followed by 40 lowercase hexadecimal digits or `tree-sha256:`
followed by a 64-digit lowercase digest.

The manifest V3 and archive-index V1 canonicalization identifiers say exactly
what the encoders write: fixed field order, no whitespace between JSON tokens,
and one terminal LF byte. The LF is part of the file identity.

The matrix is explicit. A public environment policy records the JVM, OS, CPU,
heap, JIT, collector names, ordered memory-pool identities and
allocation-counter implementation expected for one host class. A separate
JVM-argument policy records only the ordered
argument count and domain-separated digest. Cells pair those two policies and
declare a bounded replicate count; runs assign one public run ID to each
replicate. Policy IDs, cell IDs, run IDs and replicate slots must be sorted,
unique and fully referenced. Environment policy values, JVM count/digest
identities and cell policy pairs must also be unique, so a run cannot resolve
through two labels for the same policy.

Resource identities describe the inputs loaded for the complete run. The
association between one scenario and its fixture is fixed by the exact
benchmark source; it is not encoded as a separate manifest field. The po2-16
case replays checked-in KAT bytes from an independent source. This does not
reproduce or attest the upstream receipt-generation process.

For example, the first archive pass is:

```text
sbt -batch "project coreJVM" "Test / runMain sigma.stark.profile.benchmark.Eip0045CampaignValidator --manifest CAMPAIGN_MANIFEST --evidence RUN_1_JSON --evidence RUN_2_JSON --output ARCHIVE_INDEX"
```

The validator reads only bounded regular files. It requires exactly one V5
evidence file for every declared run, recomputes the payload digest and sample
summaries, checks collector metadata, and compares all campaign-bound fields
with the selected cell. Producer and validator call the same pure run-policy
resolver; the validator reuses the exact parsed-manifest identity when it checks
each claimed length and SHA-256. The file command validates one evidence file
at a time and retains only its fixed-size index entry before opening the next
file; it does not collect the campaign's evidence bytes in memory. The first
invalid file stops the scan, so later paths are not opened.

All manifest, evidence and expected-index paths, including their ancestor
directories, must remain trusted, quiescent, non-shared and controlled by the
operator for the entire validation. The regular-file and size checks, followed
by the open, are pathname prechecks; they do not pin an inode or defend against
concurrent local substitution. Stage every input in a private custody directory
before running the validator.

Output uses create-new semantics and is written only after every input has
passed. The writer chooses a bounded random adjacent name and opens it once
with `CREATE_NEW`; name collisions alone are retried, and a colliding entry is
never treated as owned or removed. After 16 consecutive collisions, publication
fails with the final name absent and every colliding entry untouched. The same
open handle fills the temporary file, flushes it, forces it to storage and
closes it. The writer then creates the final name atomically as a hard link,
which fails if that name already exists. A filesystem without hard-link support
fails closed. An interrupted write leaves the final name absent; retrying is
safe after the owned temporary file is removed. Cleanup never deletes a final
link that has already been published. If removal of the redundant temporary
link fails after publication, the operation still reports success because the
final file is complete; that temporary name may remain for later housekeeping.

The output parent must be a real directory with no symbolic-link component. It
is also a precondition that this parent is trusted, non-shared and controlled
by the operator. Java's standard hard-link API publishes by pathname, so this
tool does not claim protection against another principal concurrently changing
directory entries.

The resulting index is deterministic and contains no local paths. Entries are
sorted by run ID and bind each complete evidence file by byte length and
SHA-256, alongside its V5 payload digest. Preserve that index as a reviewed
campaign artifact. A later replay can supply it with `--expected-index`; this
detects changes even when someone has coordinated new raw samples, summaries,
collector deltas, memory-pool snapshots and a matching V5 payload digest.

Canonical JSON and full-file hashes provide content identity. They do not
authenticate an operator, prove host isolation, establish that a measurement
occurred, or decide whether a campaign is sufficient for B5. The public
manifest should contain policy identities and public machine descriptions,
never raw JVM arguments, credentials, local paths or private host metadata.

## Dynamic primitive census

Before warmup, the runner checks each scenario with an integer-ID operation
observer. The observer receives no proof data. It counts seven direct-verifier
primitives, and an observer exception leaves the verifier rather than becoming
a proof rejection. No observer is stored in the verifier, transcript RNG,
`ReadIop`, Merkle verifier or FRI round state.

| Validation path | Top pair hashes | Query pair hashes | Content hash calls | Content permutations | RNG commits | RNG element draws | RNG permutations | Total Poseidon2 permutations |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Valid proof, both late paths, independent receipt | 217 | 4,050 | 353 | 1,384 | 12 | 244 | 32 | 5,683 |
| Early transport rejection | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Canonical byte-132 mutation | 31 | 0 | 1 | 3 | 4 | 0 | 4 | 38 |

The total is `top pair hashes + query pair hashes + content permutations + RNG
permutations`. Hash-call, commit and draw counts describe control flow; adding
them again would double-count work already represented by the permutation
columns. The two valid receipts have different guests and terminal control
parameters but the same verifier profile shape, so their vectors match.

This check is validation-only. Warmup and sample collection call the production
`NoProbe` path, and the seven counts are not written into V5 evidence. The
evidence, campaign-manifest and archive-index schemas are unchanged. The census
agrees with the existing static model for these paths. It does not count field
arithmetic, JVM instructions, allocation sites, native work, node admission or
the full Sigma transaction path, and it cannot select `fixedJit` or close B5.

## What one run proves

A successful run is digest-bound evidence for one verifier build, JVM process
and host under the recorded conditions. In campaign mode it also identifies
the exact canonical manifest bytes, one declared run and the selected
environment/JVM policy observed for that process. It can expose the gap between
transport parsing, an early canonical cryptographic rejection, FRI rejection
and the final claim comparison. It can contribute to cost calibration.
Its allocation samples are JVM-reported approximations of Java-heap allocation
charged to the benchmark thread for each path, while its GC deltas show whether
the complete sampling phase coincided with collector work. The memory-pool
records show each MXBean's reported high-water `usedBytes` value after the runner
reset and its usage at the end of that same phase.

The runner validates each memory snapshot on its own. `usedBytes` and
`committedBytes` must be non-negative, `usedBytes` cannot exceed
`committedBytes`, and a declared `maxBytes` cannot be below `committedBytes`;
`maxBytes = -1` remains valid. Across phases, only the reported final peak's
`usedBytes` value must cover both the after-reset peak and end usage.
`committedBytes` and `maxBytes` may change. Pool values are kept separate and
are never summed.

It does not close B5 by itself, choose a `fixedJit`, measure node admission or
ErgoTree preflight, control host scheduling or thermals, or replace the
multi-host/repeated-operator campaign required before activation.

The benchmark measures two real direct-verifier positives, po2-15 and po2-16.
The po2-16 KAT uses a different guest and journal, so it is not one of the 11
positive profile cases required by the conformance corpus. These two cases do
not provide a complete operation or allocation census. The validation-only
counts cover seven named primitives in the direct verifier; they do not exercise
the full Sigma/transaction path, measure dispatch or attest the source build
that produced the verifier bytes.

Run-policy resolution does not attest the operator, prove host isolation or
show that a particular JVM invocation occurred. The archive validator checks
the resulting files; it does not turn their content bindings into execution
attestation.

It does not measure native or other-thread allocations, object liveness, a
scenario-specific GC pause or the complete GC/resource envelope. A pool peak
cannot be attributed to one scenario, and these records do not bound a node
process. The current-thread counter, GC deltas and pool snapshots are
observations, not memory-safety or concurrency bounds.

Topology is checked at three boundaries: before campaign policy resolution,
immediately before the reset and after the final peak read. The runner does not
watch topology continuously. A private lock serializes runs through this loaded
runner instance, but it cannot stop an external JMX client, Java agent or
unrelated code from resetting peaks. Campaign evidence therefore requires an
isolated fork with no concurrent peak resetter. A transient topology change or
an external reset that leaves the final `usedBytes` inequalities intact can go
undetected.

The V5 boundary and checkpoint fields come from the untimed validation call.
They record where that call stopped under the typed verifier result and probe
labels. V5 does not serialize the operation counters, and none of those fields
is a cost bound or measurement of a timed call.

## Retained local diagnostic

The repository retains one explicitly non-closing V1 timing-only local run in
`eip-0045-b5-local-diagnostic-v1.json`. It used the source-map identity
`15049a63cbf7c7fa43e1dc66a669b98a57988cc22c0cc0d6f53b0983a98ff64b`,
Microsoft OpenJDK 17.0.18, one 16-logical-processor Intel host, 15 rotating
warmup rounds, and 100 samples per scenario.

This older diagnostic predates the current V5 six-scenario boundary contract.
It has four scenarios and cannot be promoted to V5 campaign evidence.

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
