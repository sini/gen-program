# gen-program — agent sheet

> **Library class: reference-grade.** Deletion requires a domain argument — wrong abstraction, subsumption by another construct, or theory-unsoundness; a usage count is inadmissible as a deletion ground (P7, 2026-08-17).

The consumer that turns a framework's declarations into a **logic program**, drives gen-scope's
well-founded engine over it, and carries the third value out under its own name.

This library implements **no semantics**. The semantics is gen-scope's and it is already ruled
(ADR-0020, ADR-0022). What lives here is the translation, the pass-boundary construction, the
coherence adjudication, and the call.

## The published surface

The library is a function of its injected substrate: `import ./lib { prelude, scope, algebra, identity }`, where `scope` is `gen-scope.lib`, `algebra` is `gen-algebra.lib` and `identity` is
`gen-identity.lib`. Its flake inputs are declared, never applied (the root is published
unapplied) — only plain data crosses a gen↔gen boundary, and a library that applied the evaluator
would pin it on its consumer's behalf.

Root `default.nix`'s `wire ? { deps, resolve, lock }: import ./lib deps` formal is the seam that hands
this exact substrate attrset to `./lib` as `deps`, and it is also the only channel by which the shim
publishes anything outward — a formal is an INPUT channel and cannot carry a value out, so the
lock-parameterised `follows` resolver rides out on the same record. Overriding `wire` is how a cell
reads the shim's own formal-to-path map AND its own resolver, instead of restating either by hand;
the `follows` rule is therefore declared once in this repository, in `default.nix`.

```json
[
  "adjudicate",
  "adjudicationOutcomes",
  "admit",
  "body",
  "codomainBreaches",
  "ctorNames",
  "declaration",
  "deriveCodomain",
  "emit",
  "escape",
  "fireEscape",
  "flagNames",
  "flags",
  "forEach",
  "groundInstances",
  "mkModel",
  "model",
  "program",
  "rule",
  "ruleEdges",
  "stableModelBudget",
  "stableModelCriterion",
  "unresolvedRelata"
]
```

`ci/tests/surface.nix` asserts that block against the library's own `attrNames` and against this
document's prose in one cell, so neither side can drift onto the other.

### The translation

- **`declaration`** — `declaration { pos?; neg?; label?; promote?; when?; } relata head` → one normalised
  declaration. A door (den-hoag-7gp66 P2): the defaulted fields are one closed options set, first,
  published as `__contract`; `relata` and `head` are positional and carry no default. `pos` and
  `neg` default to empty because a declaration with neither body is a FACT (ADR-0020's own base
  case). An unknown option is refused by name at the options application. A declaration AS DATA —
  an entry of `program`'s list, or `rule`'s argument — is the record `{ head; relata; pos?; neg?; label?; promote?; when?; }`, normalised by the same door's record core: an unknown field and a missing
  `head` or `relata` are refused by name, catchably. An optional
  `label` (a string, or `null`, the default) names the edge the head denotes when included; a
  declaration is labelled exactly when `label != null`, and a non-string label is refused by name.
  An optional **`promote`** (a relation kind, or `null`) makes the included head a NODE instead: its
  `relata` are then a labelled tuple, an attrset label → identifier, and a list, an empty tuple, a
  relatum labelled `identifier` (the mint's reserved key), a non-string kind and `label` beside
  `promote` are each refused by name.
  An optional **`when`** is the **literal tier** (fuci G1): a condition term lowered to `pos`/`neg`
  — `has a` ↦ `a ∈ pos`, `not (has a)` ↦ `a ∈ neg`, `all` conjoins, `always` is the empty body. `any`,
  `eq`, `not` over a compound and a function are refused by name (a rule body is a conjunction of
  literals, and nothing here mints an atom), and `when` beside `pos`/`neg` is refused: they are two
  writings of one body. Its atoms are program atoms solved by the well-founded engine, never context
  coordinates.
- **`rule`** — one declaration's rule, through gen-scope's `mkRule`. The relata do not appear:
  they are IDENTIFIERS resolved against the frozen set, and a rule's atoms are MEMBERSHIP FACTS.
  Two universes; collapsing them would make an identifier derivable.
- **`program`** — `program frozen declarations` → gen-scope's own program value, **unchanged and
  unwrapped**. It refuses one thing by name: a relatum no strictly-earlier pass settled.
- **`unresolvedRelata`** — `unresolvedRelata frozen declarations`: the refusal's CONTENT, as data. `tryEval` discards message text, so a
  suite that could only assert THAT something refused would be equally satisfied by a construction
  with one refusal in it. This is what the throw renders.

### The call

- **`model`** — `{ program, interpretation, complete, prior }` → the result record: one keyed
  record, open (R5), because its four fields have no natural order (den-hoag-7gp66 P2, the
  keyed-record ruling); a missing field is refused by name at the application. It drives
  `engine.solve` over THIS pass's program and interpretation, from scratch: no verdict of a prior
  pass is carried (den-hoag-ea3j4, owner-ruled arm (ii)). **`prior`** is the previous pass's result
  record, and it is the **omission guard** only: the entry **refuses by name, catchably,** when any
  rule of `prior.rules` is missing from this pass's program. `prior` carries **no default**: a first
  or single pass states `prior = null`, and a defaulted `null` would silently skip the guard for a
  stepping caller who forgot it. `interpretation` is the general **assertion** channel — a LIST of
  `{ atom, verdict }` a caller states of atoms at THIS pass, restated at a later pass if it is to
  hold there — and it carries **no default**. `complete` carries none either: a defaulted `true`
  would silently claim the pass sequence had closed.
- **`ruleEdges`** — `ruleEdges model declarations` → `{ candidates, reached, promotions, promoted }`, plain lists of
  `{ from, to, label }` edge records, one per labelled head (`from`/`to` are the declaration's two
  relata). `candidates` is every labelled edge whatever it resolves to and never forces `model`;
  `reached` is the candidates whose head the model includes. Declarations of one head that agree
  collapse to one edge and ones that conflict refuse, as does a labelled declaration not relating
  exactly two. `reached` refuses by name, naming every offending head, on an undefined (`U`)
  head, on a relation still growing (`complete = false`), and on a labelled declaration that is not
  a rule of `model`. `promotions` is one promotion record per promoted head,
  `{ identifier = head; kind; relata; content = { }; site; }` (gen-scope's emitter without `pass`),
  model-free and keyed by head like the edges (a head both labelled and promoted refuses);
  `promoted` is the records whose head the model includes, off the same verdict map, so it and
  `reached` refuse together, and a promoted head is named as a node. A promotion record carries no
  identity and is not a node: the caller mints it with `mintStrata` beside its relata's emitters at
  a later pass. `candidates` also holds each promotion's incident edges; `reached` does not.
  Linear in the labelled and promoted declarations.
- **`mkModel`** — the result record's constructor, published so a consumer (and a cell) can READ
  which fields are required rather than discovering it from a crash: a door whose `__contract`
  (read by `prelude.functionArgs`) marks every field required, `adjudication` in particular.

★ **Every MISSING-FIELD refusal is CATCHABLE** (den-hoag-7gp66 P2). `model`, `mkModel`, `adjudicate` and
`body` are doors over one open keyed record: a call without `prior`, or a `mkModel` call without
`program` — the two the ea3j4 landing gate named, once the evaluator's own uncatchable "called
without required argument" — is refused by the door's name, and `ci/tests-error.nix` pins each to
the byte. The formal-set cells (`relation.nix`, `adjudication.nix`, `surface.nix`) read the
published contract through `prelude.functionArgs`. The omission refusal, the non-record `prior`
refusal and the withholding refusal are ordinary throws, and `tryEval` catches them.
★ **Every operand a door READS is checked at its application** (den-hoag-l3cwb). A wrong shape is a
catchable refusal by name that states the operand and the form expected, never the evaluator's own
"attribute missing": `ruleEdges`' `model` is a gen-program result record (`rules`, `resolve`,
`complete`) and is checked WHERE IT IS READ, so a call with nothing labelled reads no model and
answers `[ ]`; `adjudicate`'s `model` and `mkModel`'s `solved` are gen-scope solved records (their
atom lists lists of strings); `program`, `interpretation`, `complete` and `adjudication` are checked
on `model`, `mkModel` and `adjudicate`; `codomainBreaches`' `contract` is `{ emits; binds; suppresses; }`; `groundInstances` returns the tagged refusals `policy-body/context-malformed` (the
context is not a map) and `policy-body/option-malformed` (`sources` not a map, `door` neither a
function nor null). The checks read each field at WHNF and each atom list's elements, and the cores
`model` calls on records it built stay unchecked. **Two stated exceptions** (ADR-0025 item 1). What
a closure ANSWERS cannot be checked, so a `verdict`/`resolve` handed over in `solved` or `model`
that aborts on an atom (`resolve 5` aborts "expected a string") aborts uncatchably when read; the
caller owns those closures. And `groundInstances`' context keys are an open world, so an option
misplaced in the context map is dropped without a message (the `groundInstances` entry below; cell
`test-exception-a-misplaced-sources-option-in-the-context-is-dropped`).

The record carries `trueAtoms` / `withheldAtoms` / `undefinedAtoms` / `falseAtoms`, which partition
**gen-scope's extended base, `program.atoms ∪ dom(interpretation)`**, in its order: on a growing
relation a derived atom whose support rests on negation, or on an assertion, moves from `trueAtoms`
to `withheldAtoms`, and on a closed one `withheldAtoms` is empty and the other three are gen-scope's
own. It carries `verdict` — total on a closed relation, refusing a withheld atom by name on a
growing one — and `resolve`, `adjudication`, `complete`, `converged`, and gen-scope's `provenance`
and `condensationDepth` unchanged. `mkModel` takes `program` because whether a derived atom's support
is negation-free is a fact about the rules, which `solved` does not carry.

The record also carries `rules` — the rules it was solved over, as plain data, in an attrset keyed
by the `builtins.toJSON` of each CANONICAL rule (`pos` and `neg` sorted and deduplicated, since a
body is a set of literals) — which is the index a next pass's `prior` check looks each rule up in. A
resubmission that reorders a body or repeats a literal is the same rule, and is admitted. A list scanned per rule would be quadratic at thousands of rules; evaluator counters cannot see
the difference, so `withhold.nix` asserts the index's structure.

The passes are the caller's to drive (see "What this library does NOT do"). What a stepping caller
owes — resubmitting every earlier declaration — is enforced at the entry through `prior`. What stays
the caller's is restating any assertion it wants to hold at a later pass, and `complete = true`, set
only on its own knowledge that nothing further can arrive.

### The resolved relation

- **`resolve`** (on the record) — total on every string, and every answer carries its flag. There
  is no shape of this record from which a consumer can take a bare boolean.
- **`flagNames`** / **`flags`** — van Antwerpen et al. 2016 §4.1–4.2's `T` / `P` / `U`, kept as
  his own letters with the gloss carried as data.

| flag | when                                                                                                                                            | `included`                                                                                                               |
| ---- | ----------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| `T`  | the relation is closed and the atom has a two-valued verdict                                                                                    | answers both ways                                                                                                        |
| `P`  | the relation is still growing and the atom IS derived, with negation-free support                                                               | answers `true` — the positive fragment is monotone, so no later pass retracts it                                         |
| `P`  | the relation is still growing and the atom IS derived, but its support rests on `not` at any depth, or on an atom only `interpretation` asserts | **refuses by name** — a later pass may derive what the `not` reads; an assertion is not a rule (den-hoag-ea3j4, arm (a)) |
| `P`  | the relation is still growing and the atom is NOT derived                                                                                       | **refuses by name** — a later pass may derive it (vA2018 §4.3 delays such a query)                                       |
| `U`  | the atom has no two-valued verdict                                                                                                              | **refuses by name** — ADR-0020's third value                                                                             |

The three withheld answers are **fields that throw**, never absent fields and never `null`. Every
`if r.included` in the world reads `null` as false, which is the silent collapse the ruling ended.
"Negation-free" is transitive: it is gen-scope's `leastModel` over the program's rules with every
`neg`-bearing rule dropped, so `a :- y` is withheld when `y :- root, not z` is. `ci/tests/withhold.nix`
carries the oracle, quantified over every served answer at every pass.

### The coherence criterion

- **`adjudicate`** — `{ program, model, interpretation }` → the adjudication record (one open
  keyed record, a door: a missing field is refused by name).
- **`stableModelCriterion`** / **`adjudicationOutcomes`** — the criterion's name, and the closed
  outcome vocabulary `admitted` · `refused` · `not-evaluated`.
- **`stableModelBudget`** — the derived figure with its `derivation`, `fixtures`, `environment`
  and `reDerivationOwedOn`. Never a bare number.

The normal path is **polynomial**; the bounded search is the coherence gate only:

- a **TOTAL** well-founded model short-circuits — it IS the unique stable model, so existence is
  certified by the value path (VGRS 1991 Corollary 5.6);
- a **PARTIAL** model searches, over the candidate space Corollary 5.7 bounds (`trueAtoms ∪ S` for
  `S ⊆ undefinedAtoms`), which makes the walk EXHAUSTIVE and licenses the `refused` outcome;
- past the budget the field carries **`not-evaluated`** — a named outcome stating an ABSENCE of
  adjudication, never an admission.

### The policy-body algebra, on terms

The normal form a policy body is authored in, from `lib/policy-body.nix` (spec of record:
den-ag-design `specs/2026-08-26-gen-policy-body-algebra-spec.md`, made terms-only by
`specs/2026-10-02-gen-program-terms-only-spec.md`, den-hoag-lwbb1 unit 3). Every free slot — `when`,
payload values, `over`, edge/realize targets — is a **term** of gen-algebra's one algebra, applied
to gen-identity's `hashIdentity`; a function there is refused `policy-body/term-function`. A body's
three codomain facts — `emits`, `binds`, `suppresses` — are READ off its structure at registration,
never recovered by firing.

- **`body`** — `{ name, clauses, declared }` → the admitted normal form, or a tagged refusal
  `{ refused = true; code; blamed = "author"; witness; message; }`. Refusals are VALUES, never
  throws. `declared` is the framework's declared coordinate set, **required**: `null` is written for
  the open world. Every clause passes gen-algebra's `checkClause` under it — a body reads a
  coordinate only where a positive atom of its condition covers it — and a core refusal keeps its
  name as `policy-body/<code>`.
- **`emit`** / **`forEach`** — the two structural formers (a single emission skeleton; an
  iteration `{ over, emit }` whose items join the scope as `item`). Each runs the structural walk at
  call time: constructor in the closed enum, field presence exactly per the constructor row, payload
  keys forced at construction, suppress target literal. An out-of-row field is refused, never
  ignored. `over` has no guard field: its condition is `has` over its safety reads (`readCtx`,
  `default`), so a `has` test inside it stays a test.
- A **door clause** `{ when?, body = ref r, emits, binds, suppresses }` is the third clause form:
  `r` is a door-registration identifier (gen-algebra's `refId`), and the contract is declared at
  registration — `binds`/`suppresses` are a name list or `null`, the over-approximation. A
  door-registration `ref` anywhere else is refused `policy-body/ref-position`.
- **`ctorNames`** — the closed constructor enum as data: `member` · `deliver` · `edge` ·
  `suppress` · `realize` (the ruled mechanism column's names; extended by owner ruling only).
- **`deriveCodomain`** — body → `{ emits; binds; suppresses }`. Its signature takes **no
  context**, which is its own by-construction proof that no derived fact depends on the firing
  context. On a door clause it reads the declared contract, so every policy has a codomain at
  registration (ADR-0008 §3's precondition); a `null` stays `null`. A value that is not the normal
  form handed to it is refused `policy-body/skeleton-malformed`.
- **`groundInstances`** — `groundInstances { door ? null; sources ? { }; } context body` → the list of fired
  declarations, data only, or a refusal. It resolves an admitted body at `context` under the body's
  own `declared`, and a door clause's `ref r` through `door { id; context; sources; captured; }`,
  which answers `{ output; scope; }`; a nested door clause in the output passes the same walk and
  fires under the extended scope. Each admitted rule carries `__mint`, its rule identity; each
  fired declaration carries its firing identity over the rule and the `sources` of its reads (an
  absent declared coordinate enters as a fixed absence tag). Context keys are an open world:
  `groundInstances` does not inspect them, so an option placed in the context map
  (`{ thimble = "x"; sources = { … }; }`) is read as a coordinate named `sources`, never as the
  option, which is ignored, by design. Options go in the first argument:
  `groundInstances { sources = { … }; } context body`.
- **`escape`** — RETIRED (den-hoag-lwbb1 unit 3, U3r): an alias of its original arity that refuses
  any argument as the value `policy-body/escape-retired`, naming the gen-rules door. A closure crosses
  that door (`defunctionalize`, `mkApply`) and reaches gen-program as a door clause.
- **`fireEscape`** — RETIRED with `escape`: refuses `policy-body/escape-retired`, naming the door and
  `codomainBreaches`, the per-firing check it ran.
- **`codomainBreaches`** — the per-firing codomain check: `contract` (`{ emits; binds; suppresses; }`)
  → `declarations` → the list of breaches `{ field; delta; }` (`field` is `emits`, `binds`, `suppresses`
  or `shape`), `[ ]` when the contract holds. It is published so the gen-rules door, which applies it
  at every firing, reads this one row table rather than a copy.
- **`admit`** — the registration door: re-runs the walk on hand-rolled records, refuses a record
  that is not the normal form `{ name; clauses; declared; }` `policy-body/skeleton-malformed`, and
  refuses a bare lambda with the signpost to the gen-rules door.

**`__` keys crossing the boundary** (R12 stated contracts; the census that reads these lines takes the
first line of each):

### The boundary, and what retired with it

A prior pass's verdicts cross as an **interpretation**, handed to `solve` beside the program. They
used to be compiled into **rules** — two per contested atom, over one minted atom — and that made a
carried atom freely supported in every candidate containing it, so a program with no stable model
acquired one at the boundary.

Retired, and each is a **deletion**: `carriedRules` · `partnerOf` and reserved.nix itself · the
built record's `reserved` field and the wrapper around the program · the `onlyAuthored` subtraction
· `mkModel`'s `authored` formal · and the published `reservedPrefix` / `isReserved` /
`reservedCollisions`.

★ **The vanishing surface is not fixed; it has no expression.** The subtraction that hid the minted
atoms again was itself a place content could vanish; with no minted atoms there is nothing to
subtract. And `den-hoag-h2yp` law 2's discharge is stronger than the prefix ever made it: not "the
library's own names are fenced off" but **the library has none**.

## The names, and the per-primary check each one owes

ADR-0011's theory-terminology rider asks whether a term resolves at the primary the construct
CITES — not whether it exists somewhere in the corpus. For this library's family those come apart
completely.

★ **The predicate is part of the measurement, so it is named with it.** `grep -aoE "\b<term>\b"`,
**case-sensitive**, over the paper transcription only (both archived files open with an archivist
note explicitly marked NOT PART OF THE SOURCE TEXT, so a whole-file sweep mixes typed commentary
with extracted text), counting **occurrences** rather than lines, with a live in-file control and
a negative control at 0 in the same runs. A figure whose predicate is unstated is not a
measurement — a reader cannot tell what it counted.

⇒ **The spec's own R§0.4 figures are the case-INSENSITIVE reading of the same corpus**, and they
differ from these wherever a term opens a sentence: `program` reads **101 / 154** there against
100 / 152 here, and `rule` **12 / 78** against 11 / 78. Both reproduce. **The conclusion is
identical under either predicate** — the disjointness below is 20/0 and 0/20 with or without `-i`,
and the negative control is 0 under both — so the difference is one of instrument labelling, not
of finding.

| term                     | Apt, Blair & Walker 1988 | Van Gelder, Ross & Schlipf 1991 | verdict                                   |
| ------------------------ | ------------------------ | ------------------------------- | ----------------------------------------- |
| `program`                | **100**                  | **152**                         | resolves at BOTH — the library's own name |
| `rule`                   | **11**                   | **78**                          | resolves at BOTH                          |
| `stratum`                | **20**                   | **0**                           | ABW only — **not published here**         |
| `well-founded model`     | **0**                    | **20**                          | VGRS only — **not published here**        |
| NEGATIVE CONTROL (nonce) | 0                        | 0                               | the instrument reached both files         |

**The library is named `gen-program` because `program` is the term that resolves at BOTH primaries
it cites**, so no citation site can be a transplant. `stratum` belongs to the stratification
driver and `well-founded model` to the semantics; both live in gen-scope, and naming a construct
here for either would assert of this object a claim true of a neighbouring one.

★ **Ligature damage is per-term, not per-file, so both spellings are swept on both files.** VGRS's
transcription carries no surviving `fi` in any measured term (`strati ed` 36 / `stratified` 0);
ABW's is mixed (`stratified` 81 / `strati ed` 0, but `xpoint` 2 / `fixpoint` 0). A single per-file
policy is wrong in both directions.

★ **`policy` appears in no published identifier**, and that is measured rather than preferred. The
word is four-way overloaded: van Antwerpen's own term for the (E, \<) carrier pair — under the 2018
arrangement attached **per query**, which is this library's own granularity — a merge strategy
shipping as six identifiers across four substrate libraries, Manchanda & Warren's view-update
translation policy, and den's own rule surface. It stays on the DECLARATION at the framework
surface. `ci/tests/surface.nix` asserts the absence with a positive control beside it.

★ **No identifier names the ACT.** Turning declarations into ground rules has no term in either
corpus (`grounding` ⇒ 0 across both), while `ground atom` and `ground instance` do resolve. So the
library names the RESULT (`program`) and the INPUTS (`rule`, `declaration`) and gives the act no
name — the cheapest discharge available, and also asserted with a control.

## What this library does NOT do

<!-- gen-citations:begin -->

- **It owns no driver.** `stratify` is the ABW completeness driver and it is already instantiated;
  `engine.solve` is the meaning of one pass's rules. This library owns the program handed to the
  second, once per pass. A library that built its own stratum schedule would be a second copy of a
  discipline that agrees with the first only while someone keeps them in step.
- **It mints no identity.** Identity is substrate vocabulary with exactly one authority
  (ADR-0016 rulings 4–5); a second copy is a second authority.
- **It publishes no query surface, no ordering door and no materialisation.** The last is
  gen-view's by ADR-0012, which governs views OF the graph. `ruleEdges` is not one: it is a SOURCE of
  the graph's edges, plain data the caller appends to its declared edges before any graph exists.
- **It re-exports nothing of gen-scope.** The program VALUE crosses as a field of a construction
  result, which is plain data by its own module's statement; no gen-scope construct is republished
  under a name here, and `ci/tests/surface.nix` asserts the disjointness with a control.
- **It reproduces no shape it retires.** No keyset-equality convergence test, no
  union-accumulation without retraction, no in-flight membership predicate handed to a caller's
  guard. The program is closed before it is solved; the model is a function of the rules.

<!-- gen-citations:end -->

## What it rests on and does not control

- **ADR-0019's input-type discipline.** A consumed query cannot observe a conditional edge, so the
  `includes → ¬holds → includes` cycle cannot be written. If that discipline is ever relaxed — if
  a query result can decide an edge's existence — the cycle becomes writable and **the failure is
  silent**. That is a change to this library's premise, and it announces itself nowhere.
- **ADR-0008 §3's `bounded well-defined`.** It takes two of Vogt's three conjuncts, so an
  arbitrary user-supplied function inside a declaration is what makes the translation's TOTALITY a
  question. This library states the precondition and supplies no missing conjunct; the debt is
  `den-hoag-xin3`'s.
- ★★★ **The contract on `carried` — STATED, NOT ENFORCED.** `carried` is meant to be the atoms
  whose verdict at the previous pass was `undefined`, and nothing checks it — nor can it be checked
  here, since the previous pass's model is not an argument to the construction. **A caller who
  carries a SETTLED atom injects undefinedness silently, and it propagates to that atom's
  readers.** Measured on `s.` + `r :- f` with `f` headed by no rule: `carried = [ ]` gives
  `f = "false"`, `r = "false"`, contested 0; `carried = [ "f" ]` gives `f = "undefined"`,
  `r = "undefined"`, contested 3. It is a precondition on the caller and the one shape of
  vanishing content this design does not close by construction. No enforcement is built,
  deliberately — the construct retires under the input-interpretation ruling (`den-hoag-1tu3`),
  where the hazard **dissolves**: an interpretation carries each atom's verdict with it, so
  undefinedness cannot be asserted of an atom that did not have it.
- **The "composes rather than pins" claim is direction-asymmetric.** It composes with a positive
  derivation and OVERRIDES a negative one — a carried atom the next pass leaves underived comes
  back `undefined` rather than `false`. That is what re-injecting the third value is for, and only
  the direction named is claimed. Dissolves at `den-hoag-1tu3` for the same reason.
- **The compositional result is NOT established.** ABW's theorem is about a stratified program and
  a pass here carries negative cycles by premise, so the pass sequence is not an instance of their
  iteration. What replaces it is a CONSTRUCTION — ADR-0016 ruling 7's frozen set with ADR-0033
  clause 1 — which makes each pass's input closed. No archived primary states that a sequence of
  well-founded models over successively frozen inputs inherits the properties a single one has.
  **This library claims the construction and not the theorem.**
- **An acquisition gap.** VGRS 1991 is archived; Van Gelder 1993, which gives the alternating
  fixpoint construction gen-scope actually iterates, is cited-not-held. A claim that this library
  composes two HELD published results would be false.
- **The pass-boundary construction is not stable-model-equivalent** to the program it stands in
  for: one partner per contested atom makes anti-correlated atoms independent, admitting
  combinations the original excluded. The well-founded verdicts agree ATOM BY ATOM, which is all
  it claims.
- ★★★ **The refusal direction is NOT preserved across that re-encoding, and this is measured
  rather than reasoned.** The argument that partners "only ADD stable models, so a program with
  none does not acquire one" has a true premise and an invalid inference — adding to zero gives
  more than zero. On VGRS Example 5.3's `P2 = p :- not p` ("Hence P2 has no stable model"),
  `carried = [ ]` adjudicates **refused** and `carried = [ "p" ]` adjudicates **admitted**,
  because `p :- not p′` supplies a derivation `p :- not p` alone never had. ⇒ the adjudication is
  a statement about the program AS CONSTRUCTED; `admitted` must not be read as a statement about
  the same declarations without the carry. `ci/tests/carry.nix` pins both readings.

## Running the suites

```bash
cd ci && nix flake lock          # after changing an input
nix develop ./ci --command ci                # the suites, guarded
nix develop ./ci --command ci --tests-error  # cells whose subject is an error MESSAGE, guarded
nix-unit --flake ./ci#tests                  # the suites, unguarded
nix-unit --flake ./ci#testsError             # the error cells, unguarded
cd ci && nix fmt -- --ci         # format (run from the MAIN checkout, never a linked worktree)
```

`ci` refuses when anything under a declared read root is unknown to git — any extension or name,
`_`-prefixed included — and the remedy is `git add` or a move. The bare `nix-unit` and
`nix flake check` forms are unguarded: they read a git-filtered copy of the tree, so an untracked
cell is silently absent and the run stays green.

Count ❌ **and** ☢️ in the output; a run with zero of the first and some of the second has not
passed.

A value cell sits under a suite, `flake.tests.<suite>.<cell>`: the batch gate behind `checks.default`
maps over suites, so a cell placed directly under `flake.tests` passes `nix-unit` and then crashes
`nix flake check` with "expected a set but found a list". The error plane (`flake.testsError`) is
flat by its own convention.

## Formatting

`nix fmt -- --ci` REWRITES the tree, so a second run is green regardless of what the first found.
`git add` new files **before** formatting — untracked files are invisible to treefmt and a
`0 changed` report does not cover them — and `git add` again **after**.

## Drift check

`nix eval --json .#lib --apply builtins.attrNames` — the form 23 sibling sheets publish —
**aborts here**. The library is a function of its injected substrate, so the flake's `lib` output is
a lambda and the apply reads *"expected a set but found a function"*. The check goes through
`ci/repl.nix`, which resolves the acceptance run's own substrate — this repository's
`ci/flake.lock` pin of `gen-scope` and the prelude beneath it — rather than a second,
differently-pinned one. That is what `--impure` costs. From the repository root:

```sh
nix eval --json --impure --file ci/repl.nix --apply 'r: builtins.attrNames r.genProgram'
```

Current output (verbatim):

```json
["adjudicate","adjudicationOutcomes","admit","body","codomainBreaches","ctorNames","declaration","deriveCodomain","emit","escape","fireEscape","flagNames","flags","forEach","groundInstances","mkModel","model","program","rule","ruleEdges","stableModelBudget","stableModelCriterion","unresolvedRelata"]
```
