# rsBTC U-2 Composed Activation: Phase-1 Design

Status: local Phase-1 implementation target

Design authority:

- lifecycle SHA-256:
  `4e5dd69daf7b09c5e2bc5eecff35f4eca18f9981f9edd2af81cd2bb78f74767a`;
- implementation base: `d256e445ae2cf144b6370ea574365591c0f9b8fa`;
- Sigma target: V6.

## Claim

This slice composes the accepted Candidate-A detached Sigma message proof into
the complete U-2 activation predicate. It measures the resulting branch and
pins its compiled tree for one explicit feasibility profile.

It does not freeze the final lifecycle ABI. The final `InsuredDeal` proposition
hash, fee constants, reserve floor, wallet signing policy, and full lifecycle
cost envelope remain separate promotion gates.

## State And Transaction Shape

`UnactivatedVault` is input 0 and contains exactly one positive amount of the
family rsBTC token. Its registers are:

| Register | Type | Meaning |
| --- | --- | --- |
| R4 | `(Coll[Byte], Coll[Byte])` | 36-byte Bitcoin outpoint and 32-byte script hash |
| R5 | `Long` | Minimum satoshis |
| R6 | `(GroupElement, GroupElement)` | Buyer and seller payout keys |
| R7 | `(GroupElement, GroupElement)` | Buyer and seller authorization keys |
| R8 | `Coll[Int]` | `activationCutoff`, `recoveryHeight`, D1, `responseMin`, `responseMax` |
| R9 | `Coll[Byte]` | Family-fixed `InsuredDeal` proposition hash |

U-2 reads only context vars 0 and 7:

- var 0: branch byte `1`;
- var 7: exact 56-byte Candidate-A proof over
  `ERG-RSBTC || version || Ergo network || Bitcoin network || purpose || SELF.id`.

Vars 1-6 are not read. No data input is allowed.

The canonical output shape is:

1. `InsuredDeal` successor;
2. recognized miner-fee output;
3. optional token-free change output when one token-free external input is
   present.

U-2 has no executor bounty in this feasibility profile. The state contributes
exactly the family fee constant. Any fee uplift, successor top-up, or change is
funded only by the optional external input and is checked with ordered,
nonnegative subtraction. Fee and change outputs are token-free. Their optional
register metadata is not an authority for value, identity, or successor state
and is therefore not restricted by this slice.

## Closeout Matrix

| Invariant | Producer / enforcement | Downstream consumer | Failure if relaxed | Positive | Isolated negative |
| --- | --- | --- | --- | --- | --- |
| State is input 0 | U predicate checks `SELF.id == INPUTS(0).id`; token-bearing SELF plus a token-free external input independently imply the same placement in this profile | Mint id and all later deal identity | Another input can become the mint/deal anchor if the external-input profile later changes | Canonical U-2 | Move state to input 1; this is a topology negative, not an isolated mutant under the current token rules |
| Closed U-2 tag | Var 0 is typed `Byte` and equals 1 | Branch-local evaluation | Unknown or malformed branch can enter a partial predicate | Tag 1 | Unknown, missing, wrong type |
| Capability envelope | Exact length 56 before decoding | Candidate-A verifier | Trailing bytes, malformed scalar, or unbounded nested work | Canonical proof | 55/57 bytes and scalar boundaries |
| Capability subject | Domain plus `SELF.id`, seller key from R7 | Seller authorization policy | Cross-deal replay or wrong-key activation | Proof for this U box | Other U id, wrong key, identity key |
| Formation schema | R4-R9 and token vector checked in U | Every I/Claim branch | Malformed or attacker-selected future terms | Canonical U box | One field changed with capability regenerated for that box |
| Effective activation interval | `D1 - maxWindow <= HEIGHT <= activationCutoff` | Seller payment window before D1 | Empty or shortened insured payment window | Both endpoints | One height outside each endpoint |
| Successor script | Blake2b-256 of output proposition equals family constant | Every later state spend | Attacker creates a lookalike or unspendable successor | Pinned successor | Alternative proposition |
| Successor fields | R4-R7 copied; R8 reduced to I fields; R9 fixed to Claim hash | I and Claim predicates | Future branch consumes forged or stale terms | Exact successor | One mutation per register |
| Origin NFT | Exactly `(SELF.id, 1)` at token position 0 | I, Claim, Hardened marker | Lost, duplicated, split, or substituted deal identity | Exact two-token vector | Zero/two/wrong id/order/extra token |
| Collateral continuity | Exact rsBTC id and amount at position 1 | Terminal payout equations | Collateral loss, inflation, or token substitution | Exact amount | Wrong amount/id/order |
| Value continuity | State funds only fixed fee; successor preserves remainder | Every later value release | Activation drains reserve or burns arbitrary state ERG | Exact fee | One nanoERG drain and coordinated top-up mutations |
| External funding | At most one token-free input and optional token-free change | Fee/top-up accounting | External value is mistaken for state value or protocol tokens escape | Fee uplift/top-up/change, with irrelevant fee/change metadata accepted | Tokenized input/change and broken subtraction equation |
| Successor freshness | Output creation height bounded below by current height | Storage-rent support horizon | Backdated successor shortens support lifetime | Current and lag boundary | One below the lag floor |
| Branch locality | U-2 never reads vars 1-6 or data inputs | Composition ABI | Activation accidentally depends on Bitcoin proof material | No vars 1-6 | Wrong-typed vars 1-6 remain irrelevant; any data input rejects |

Each state-input mutation changes the box id. Its negative fixture must therefore
regenerate a valid detached capability for the mutated box before asserting the
target rejection. Otherwise the capability check would hide the intended
failure.

The direct input-0 check is intentionally retained because it states the
lifecycle rule at its point of use. In this exact profile it is defense in
depth, not an independently mutation-sensitive guard: SELF carries rsBTC while
the only permitted external input is token-free, so moving SELF to input 1 also
violates the external-input rule.

## Phase-1 Pins

For the exact source in this slice, with provisional compiled targets for
`InsuredDeal` and `Claim`:

| Artifact | Pin |
| --- | --- |
| U ErgoTree serialized size | 1,494 bytes |
| U ErgoTree Blake2b-256 | `e6ba0c08b1026cf73220b6265daaa967e04e6e80b8f8a6055d33fc3ab06ea508` |
| Canonical U-2 full-path reduction cost | 1,149 |
| U-2 with external fee uplift, successor top-up, and change | 1,168 |

These pins measure the complete U-2 predicate, including Candidate A. They are
not final lifecycle ABI pins: replacing either downstream target proposition,
or changing a family constant, intentionally changes the U tree hash and may
change its size or cost.

## Validation Sequence

1. Establish canonical U-2 and lower/upper-bound positives.
2. Add one red test per matrix row before implementing that row.
3. Keep contract-false and evaluation-failure outcomes distinct.
4. Use single-source mutants only for guards whose negative can be isolated.
5. Pin compiled bytes, Blake2b-256 hash, and full canonical reduction cost only
   after the matrix is green.
6. Re-run the focused spec on every supported `scJVM` Scala line.

## Evidence Ceiling

A green suite establishes SigmaState V6 compile/reduction evidence for the
exact fixtures. It does not establish released-wallet support, secret-key
custody, target-node acceptance, mempool inclusion, lifecycle completion, or
production readiness.
