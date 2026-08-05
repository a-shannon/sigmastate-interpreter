# rsBTC Base I-3 Claim Opening: Phase-1 Design

Status: local Phase-1 implementation target

Design authority:

- lifecycle SHA-256:
  `4e5dd69daf7b09c5e2bc5eecff35f4eca18f9981f9edd2af81cd2bb78f74767a`;
- implementation base:
  `0d0da9936706198a011df2b9036c6ac99fb03407`;
- Sigma target: V6;
- profile: Base/PLAIN.

## Claim

This slice implements the buyer-authorized I-3 transition from `InsuredDeal`
to `Claim` with the selected Base/PLAIN executor policy `Fe.I3 = 0`.

It uses a provisional Claim proposition solely to measure and falsify the I-3
predicate. It does not publish or propagate a final Claim hash. C-1 composition
remains the gate for the final Claim proposition and every upstream successor
pin.

## State And Transaction Shape

`InsuredDeal` is input 0. Its token vector is exactly:

1. `(originNftId, 1)`;
2. `(rsBtcTokenId, collateralAmount)`, with `collateralAmount > 0`.

Its registers are:

| Register | Type | Meaning |
| --- | --- | --- |
| R4 | `(Coll[Byte], Coll[Byte])` | 36-byte Bitcoin outpoint and 32-byte destination-script hash |
| R5 | `Long` | Minimum satoshis |
| R6 | `(GroupElement, GroupElement)` | Buyer and seller payout keys |
| R7 | `(GroupElement, GroupElement)` | Buyer and seller authorization keys |
| R8 | `Coll[Int]` | D1, `responseMin`, `responseMax` |
| R9 | `Coll[Byte]` | Family-fixed Claim proposition hash |

Context var 0 is the closed branch tag: `0 = I-1`, `1 = I-2`, `2 = I-3`.
This slice enables only I-3. It does not read Bitcoin vars 1-6 and permits no
data input.

The canonical I-3 output order is:

1. Claim successor;
2. recognized miner-fee output;
3. optional token-free change when one token-free external input is present.

There is no executor output. `Fe.I3 = 0` and `Ye = 0`. One optional external
input may fund only miner-fee uplift, Claim top-up, and clean change through the
ordered nonnegative equation.

## I-3 Predicate

The branch requires:

- exact InsuredDeal state schema, token vector, role-key separation, and
  compiled Claim hash;
- state input 0, at most one token-free external input, zero data inputs, and
  the exact output schema;
- buyer authorization over the complete transaction;
- `HEIGHT >= D1`;
- widened D2 bounds at actual inclusion height H:
  `H + responseMin + 1 <= D2 <= H + responseMax + 1`;
- exact Claim proposition, R4-R7 continuity, R8 set to D2, unchanged origin NFT
  and collateral, bounded-fresh creation height, and no current-box-id issuance;
- fixed fee proposition and state contribution;
- `successor.value >= SELF.value - Fs.I3` and
  `successor.value >= Rnext.I3`;
- exact external-value closure for fee uplift, successor top-up, and change.

## Evidence Strategy

The first red/green cycle proves that the canonical path is gated by the I-3
branch. A second red batch runs the full negative matrix against an intentionally
permissive branch before the complete predicate is added.

The matrix isolates:

- D1 and both D2 endpoints;
- missing or wrong buyer authorization;
- input position, extra input, data input, appended output, and executor-output
  presence;
- each future-trusted register and Claim successor field;
- origin NFT and collateral continuity;
- fee proposition, fee contribution, reserve floor, and external-value closure;
- successor creation-height freshness;
- closed branch tags and non-evaluation of vars 1-6.

Source mutants pin the D2 lower bound, Claim proposition binding,
external-value equality, and buyer authorization after the fixture matrix is
green.

## Closeout Matrix

| Invariant | Producer / enforcement | Downstream consumer | Failure if relaxed | Evidence |
| --- | --- | --- | --- | --- |
| Dense InsuredDeal R4-R9 schema and role separation | U-2 produces; I-3 revalidates | Claim construction and later C branches | Malformed or cross-role terms become successor authority | Missing/type/field and role-collision negatives |
| Exact origin NFT and rsBTC collateral vector | U-2 produces; I-3 preserves | Claim identity and C-1/C-2/C-3 value release | Deal substitution, collateral drift, or extra-token carriage | Input and successor token-field negatives |
| State at input 0, one optional token-free external input, zero data inputs | I-3 | Transaction accounting and branch-local witness interpretation | State ambiguity, undeclared funding authority, or hidden authenticated input | Topology negatives |
| `Fe.I3 = 0` and exact output positions | I-3 | Claim, fee, and optional-change consumers | Undeclared executor value or output-index confusion | Extra-output and change-without-input negatives |
| `HEIGHT >= D1`, widened inclusive D2 bounds, and explicit strictly-later-height counts | I-3 | Claim C-1/C-2 deadline semantics | Premature Claim or invalid response horizon | Count equalities, boundary pair, and D2-lower-bound mutant |
| Exact Claim proposition, R4-R8 continuity, and no R9 | I-3 | C-1/C-2/C-3 | Successor script or deal terms can be replaced | One field/type negative per successor coordinate and proposition mutant |
| Bounded-fresh Claim creation height | I-3 | Downstream deadline/rent assumptions | A stale or future-labelled successor can enter the state chain | Lower and upper creation-height negatives |
| Fixed fee proposition, `Fs.I3`, `Fe.I3 = 0`, `Fs + Fe <= totalStateDeductionMax`, and `Rnext.I3` | Family build and I-3 | Miner-fee output and Claim liveness reserve | Excessive family deduction, fee diversion, or underfunded Claim state | Build-time cap negative plus fee, reserve, and top-up negatives |
| Ordered external-value equality and token-free fee/change paths | I-3 | Transaction conservation and token identity | Unaccounted value or protocol-token escape | Balanced positive, one-nanoERG drift, token negatives, and value mutant |
| Buyer authorization and closed non-I-3 tags | I-3 | State transition authority | Unauthorized Claim opening or accidental branch activation | Missing/wrong proof and closed-tag negatives; authorization mutant |
| Vars 1-6 are outside the I-3 ABI | I-3 | Future C-1 Bitcoin witness composition | Hidden coupling to irrelevant witness material | Wrong-typed vars 1-6 accepting control |

## Phase-1 Evidence Snapshot

The current candidate source is
`BitcoinRsBtcI3ClaimOpeningSpecification.scala`, SHA-256
`73730da2146fefc3e7bb94801dea28e892baa53f332b687a2e530da638d01875`.
Its focused suite contains 13 properties and passes `13/13` on
Scala `2.11.12`, `2.12.21`, and `2.13.18`. The semantic negatives assert
`CONTRACT_FALSE` through direct Sigma reduction, malformed typed access asserts
`EVALUATION_FAILURE` with its exact root-cause class, and missing or wrong buyer
secrets assert the prover's witness-deficiency failure rather than a generic
failed `Try`.

The four source mutants each require one unique occurrence within the emitted
ErgoScript and turn their selected isolated control into an accepting
transaction. They cover the D2 lower bound, Claim proposition binding, exact
external-value closure, and buyer authorization. The remaining negative matrix
is not claimed to have been rerun under each mutant.

The provisional compiled measurements are:

- tree size: `1196` bytes;
- tree Blake2b-256:
  `0168e8ca61fde3560f2c456b919f9826ad1471ac98cd6a56a328f7b7ddf3d285`;
- canonical I-3 reduction cost: `1218`;
- external fee/top-up/change reduction cost: `1237`.

These measurements are regression pins for this Phase-1 slice only. They are
not final lifecycle ABI values.

## Evidence Ceiling

A green suite establishes only SigmaState V6 compile/reduction evidence for
the I-3/Base slice and its exact fixtures. The provisional Claim target means
the resulting InsuredDeal tree, hash, size, reserve, and costs are not final ABI
pins. The slice does not establish C-1, a literal I-3-to-C-2 chain, wallet
signing support, target-node admission, or production readiness.
