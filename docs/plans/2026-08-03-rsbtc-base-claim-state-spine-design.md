# rsBTC Base Claim State Spine: Phase-2 Design

Status: Phase-1 C-2/C-3 state-spine evidence

Design authority:

- lifecycle SHA-256:
  `4e5dd69daf7b09c5e2bc5eecff35f4eca18f9981f9edd2af81cd2bb78f74767a`;
- implementation base:
  `bcef084d89f795998b14078a6d377f0732d0c2ca`;
- Sigma target: V6;
- profile: Base/PLAIN.

## Claim

This slice fixes the Base/PLAIN `Claim` state packing and implements the two
non-Bitcoin terminal branches from frozen rev3:

- C-2, the permissionless buyer payout from D2; and
- C-3, the buyer-and-seller-authorized mutual split at any height.

C-1 remains an explicit false branch until the complete outpoint, parser,
Merkle, relay-binding, and relay-freshness predicate is composed. Consequently,
this slice produces no successor-consumable Claim hash and no final ABI pin.

## State ABI

`Claim` is input 0. Its token vector is exactly:

1. `(originNftId, 1)`;
2. `(rsBtcTokenId, collateralAmount)`, with `collateralAmount > 0`.

Its dense registers are:

| Register | Type | Meaning |
| --- | --- | --- |
| R4 | `(Coll[Byte], Coll[Byte])` | 36-byte committed Bitcoin outpoint and 32-byte destination script hash |
| R5 | `Long` | Minimum satoshis, `0 < value <= 2100000000000000` |
| R6 | `(GroupElement, GroupElement)` | Buyer and seller payout keys |
| R7 | `(GroupElement, GroupElement)` | Buyer and seller authorization keys |
| R8 | `Int` | Absolute D2 |

The proposition fixes the profile, rsBTC token id, fee proposition, fee
contribution, output minima, and creation-height lag. Claim carries no D1,
formation boundary, response policy, successor hash, or mutable profile field.

Payout identity is checked against `proveDlog(committedKey).propBytes`. The
independent output fixtures use the canonical zero-header P2PK ErgoTree. A V6
header on the same key has different proposition bytes and is pinned as a
negative fixture; the enclosing Claim contract itself remains V6.

## Common Transaction Shape

- context var 0 is a closed `Byte`: `0 = C-1`, `1 = C-2`, `2 = C-3`;
- the Claim state is `INPUTS(0)`;
- one optional token-free external fee/top-up input may be `INPUTS(1)`;
- C-2 and C-3 require zero data inputs and never read vars 1-6;
- every terminal output omits the origin NFT and every token with id `SELF.id`;
- the recognized fee output is token-free and uses the family fee proposition;
- an optional change output is positive-value and token-free;
- fee and change register metadata is non-authoritative and unrestricted.

Terminal origin-identity burn is structural across the closed output topology:
the payout shapes exclude the origin NFT, while fee and change are token-free.
The evidence suite therefore routes the origin NFT into each auxiliary output
and uses source mutants to show that relaxing either token-free check permits
that exact escape.

The feasibility profile uses no executor bounty (`Fe = 0`). It therefore has
no executor output. This is a profile choice, not a lifecycle-wide claim.

## C-2 Output Schema

Outputs are fixed as:

1. buyer payout;
2. miner fee;
3. optional external-input change.

The buyer payout proposition equals `buyerPayoutKey.propBytes`, carries exactly
the rsBTC collateral token, and satisfies the bounded-fresh creation-height
rule. C-2 requires `HEIGHT >= D2` and no signature.

Let `V = SELF.value`, `Fs` be the fixed state contribution, `Fm` the fee-output
value, `X` the optional external-input value, `Yp` the buyer-output top-up, and
`Vc` optional change. The branch enforces ordered nonnegative arithmetic:

```text
buyer.value >= V - Fs
Yp = buyer.value - (V - Fs)
X >= Fm - Fs
X - (Fm - Fs) >= Yp
X - (Fm - Fs) - Yp == Vc
```

## C-3 Output Schema

Outputs are fixed as:

1. buyer payout;
2. seller payout;
3. miner fee;
4. optional external-input change.

Both payout propositions are derived from their committed payout keys. Each
payout token vector is either empty or exactly one positive amount of rsBTC,
and the two amounts sum exactly to the Claim collateral. Zero/full and
positive/positive partitions are valid; a zero-valued token entry is not.

C-3 is valid at any height only with both committed authorization proofs over
the complete transaction. With `Yp` equal to the sum of both payout values
above `V - Fs`, the same ordered external-value equation applies.

## Schema And Evaluation Invariants

| Invariant | Enforcement | Failure if relaxed | Required regression |
| --- | --- | --- | --- |
| Closed branch selection | Typed var 0 and complete branch-local conjunctions | Partial or unknown branch enters a payout path | Missing, wrong-typed, and unknown tag |
| State is input 0 | `SELF.id == INPUTS(0).id` | Two state boxes may share one terminal output | State moved to input 1 and two-Claim shared-payout case |
| Exact Claim token vector | Two fixed-position entries and exact amounts | Identity/collateral loss, injection, or drift | Missing, duplicated, reordered, wrong-id, and wrong-amount cases |
| Terminal burn | No output carries origin NFT or current `SELF.id` | A terminal path leaves a live or forged deal identity | Origin preserved, split, or current-id minted |
| Payout identity | Exact committed P2PK `propBytes` | Builder redirects collateral | Wrong buyer/seller proposition |
| C-2 deadline | `HEIGHT >= D2` | Buyer withdraws before the insured boundary | D2-1 rejects; D2 and D2+1 accept |
| C-3 authorization | Both distinct role proofs | One party controls a mutual cancellation | Missing each proof, wrong proof, equal cross-party keys |
| Token partition | Exact per-output shape and sum | Collateral is burned, duplicated, or diverted | Zero/full and split positives; sum and shape mutations |
| State-value conservation | Fixed `Fs` plus exact external equation | Caller burns state value or attributes external value to it | One-nanoERG drift in both directions |
| Fresh payouts | Bounded creation-height floor | Backdated outputs shorten the rent horizon | Lag boundary accepts; one older rejects |
| Branch-local evaluation | C-2/C-3 do not read vars 1-6 or relay data | Non-proof exit inherits proof failures or cost | Absent and wrong-typed vars remain irrelevant; any data input rejects |

State-field negative fixtures must keep every unrelated field and the selected
branch transaction coherent so the named predicate is the first discriminant.

## State-Spine Evidence

The exact C-2/C-3 scaffold currently pins:

| Artifact or branch | Measurement |
| --- | --- |
| Compiled V6 tree size | 1,517 bytes |
| Compiled tree Blake2b-256 | `24ed963ae59eec23d4add20517f804a9d0393fc75bea1173affa4fc5b17c84a5` |
| C-2, state-funded | 629 |
| C-2, external fee/payout top-up and change | 648 |
| C-3, positive/positive collateral split | 1,527 |
| C-3, zero/full collateral split | 1,517 |
| C-3, external fee/payout top-up and change | 1,547 |

The suite contains 26 properties covering canonical paths, boundaries,
transaction topology, dense mandatory-register failure, role separation,
terminal identity burn, token partitions, value conservation, branch-local
evaluation, two-party authorization, and source mutants. These measurements
are reproduced as 26/26 on scJVM with Scala 2.11.12, 2.12.21, and 2.13.18.
They are reproducibility pins for this scaffold only. C-1 composition changes
the tree bytes, hash, and costs. The three-input source mutant isolates the
`inputCountOk` guard at Sigma reduction; it is not target-node monetary-balance
evidence. Independent review accepted commit `4a989b7e`; the evidence-only
follow-up after that commit remains to be re-reviewed.

## C-1 Promotion Gate

The Claim hash remains non-authoritative until C-1 adds, in one guarded
predicate:

- a `61..1640` byte transaction envelope and one canonical parser walk;
- an exactly-once committed-outpoint scan without caller-supplied offsets;
- same-output script-hash and minimum-amount binding;
- txid derivation from the same var-1 bytes;
- authenticated equal-depth payment and coinbase Merkle proofs;
- exact 88-byte header-row and header-id binding;
- active-chain membership under the pinned relay proposition and exact relay
  state ABI;
- the family relay-age bound; and
- C-1's strict `HEIGHT < D2` and terminal seller payout equation.

Until those inputs are pinned, this scaffold's compiled bytes, hash, and costs
are state-spine measurements only and must not be embedded in `InsuredDeal`.

## Evidence Ceiling

A green Sigma V6 suite for this slice establishes only C-2/C-3 compile,
reduction, authorization, topology, and accounting evidence for its exact
fixtures. It does not establish C-1, the final Claim ABI, target-node
acceptance, released-wallet signing, operational liveness, or production
readiness.
