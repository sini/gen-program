# gen-program — agent sheet

The consumer that turns a framework's declarations into a **logic program**, drives gen-scope's
well-founded engine over it, and carries the third value out under its own name.

This library implements **no semantics**. The semantics is gen-scope's and it is already ruled
(ADR-0020, ADR-0022). What lives here is the translation, the pass-boundary construction, the
coherence adjudication, and the call.

## The published surface

The library is a function of its injected substrate: `import ./lib { prelude, scope }`, where
`scope` is `gen-scope.lib`. It declares no flake inputs — only plain data crosses a gen↔gen
boundary, and a library that re-declared the evaluator would pin it on its consumer's behalf.

```json
[
  "adjudicate",
  "adjudicationOutcomes",
  "declaration",
  "flagNames",
  "flags",
  "isReserved",
  "mkModel",
  "model",
  "program",
  "reservedCollisions",
  "reservedPrefix",
  "rule",
  "stableModelBudget",
  "stableModelCriterion",
  "unresolvedRelata"
]
```

`ci/tests/surface.nix` asserts that block against the library's own `attrNames` and against this
document's prose in one cell, so neither side can drift onto the other.

### The translation

- **`declaration`** — normalises one declaration. A **strict pattern**: `head` and `relata` carry
  no default, `pos` and `neg` default to empty because a declaration with neither body is a FACT
  (ADR-0020's own base case). An unknown field is refused by name at application.
- **`rule`** — one declaration's rule, through gen-scope's `mkRule`. The relata do not appear:
  they are IDENTIFIERS resolved against the frozen set, and a rule's atoms are MEMBERSHIP FACTS.
  Two universes; collapsing them would make an identifier derivable.
- **`program`** — `{ declarations, frozen, carried }` → `{ program, authored, reserved }`. The
  `program` field is gen-scope's own value, **unchanged**. It refuses two things by name: an
  authored atom trespassing on the reserved namespace, and a relatum no strictly-earlier pass
  settled.
- **`unresolvedRelata`** / **`reservedCollisions`** — each refusal's CONTENT, as data. `tryEval`
  discards message text, so a suite that could only assert THAT something refused would be equally
  satisfied by a construction with one refusal in it. These are what the throws render.

### The call

- **`model`** — `{ built, complete }` → the result record. It drives `engine.solve`. `complete`
  carries **no default**: a defaulted `true` would silently claim the pass sequence had closed.
- **`mkModel`** — the result record's constructor, published so a consumer (and a cell) can READ
  which fields are required rather than discovering it from a crash. Every formal is required;
  `adjudication` in particular.

The record carries `trueAtoms` / `undefinedAtoms` / `falseAtoms` (this library's own atoms
subtracted), the total `verdict`, `resolve`, `adjudication`, `complete`, `converged`, and
gen-scope's `provenance` and `condensationDepth` unchanged.

### The resolved relation

- **`resolve`** (on the record) — total on every string, and every answer carries its flag. There
  is no shape of this record from which a consumer can take a bare boolean.
- **`flagNames`** / **`flags`** — van Antwerpen et al. 2016 §4.1–4.2's `T` / `P` / `U`, kept as
  his own letters with the gloss carried as data.

| flag | when                                                         | `included`                                                                         |
| ---- | ------------------------------------------------------------ | ---------------------------------------------------------------------------------- |
| `T`  | the relation is closed and the atom has a two-valued verdict | answers both ways                                                                  |
| `P`  | the relation is still growing and the atom IS derived        | answers `true` — growth is monotone in the positive direction                      |
| `P`  | the relation is still growing and the atom is NOT derived    | **refuses by name** — a later pass may derive it (vA2018 §4.3 delays such a query) |
| `U`  | the atom has no two-valued verdict                           | **refuses by name** — ADR-0020's third value                                       |

The two withheld answers are **fields that throw**, never absent fields and never `null`. Every
`if r.included` in the world reads `null` as false, which is the silent collapse the ruling ended.

### The coherence criterion

- **`adjudicate`** — `{ program, model }` → the adjudication record.
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

### The reserved namespace

- **`reservedPrefix`** / **`isReserved`** — the namespace this library owns inside the Herbrand
  base. An authored atom carrying the prefix is **refused**, so collision is impossible rather
  than improbable, and the same string makes an introduced atom recognisable for subtraction.

## The names, and the per-primary check each one owes

ADR-0011's theory-terminology rider asks whether a term resolves at the primary the construct
CITES — not whether it exists somewhere in the corpus. For this library's family those come apart
completely. Measured on the archived transcriptions (paper text only; both files open with an
archivist note explicitly marked NOT PART OF THE SOURCE TEXT, so a whole-file sweep mixes typed
commentary with extracted text), word-bounded, occurrences, with a live in-file control and a
negative control at 0 in the same runs:

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

- **It owns no driver.** `stratify` is the ABW completeness driver and it is already instantiated;
  `engine.solve` is the meaning of one pass's rules. This library owns the program handed to the
  second, once per pass. A library that built its own stratum schedule would be a second copy of a
  discipline that agrees with the first only while someone keeps them in step.
- **It mints no identity.** Identity is substrate vocabulary with exactly one authority
  (ADR-0016 rulings 4–5); a second copy is a second authority.
- **It publishes no query surface, no ordering door and no materialisation.** The last is
  gen-view's by ADR-0012.
- **It re-exports nothing of gen-scope.** The program VALUE crosses as a field of a construction
  result, which is plain data by its own module's statement; no gen-scope construct is republished
  under a name here, and `ci/tests/surface.nix` asserts the disjointness with a control.
- **It reproduces no shape it retires.** No keyset-equality convergence test, no
  union-accumulation without retraction, no in-flight membership predicate handed to a caller's
  guard. The program is closed before it is solved; the model is a function of the rules.

## What it rests on and does not control

- **ADR-0019's input-type discipline.** A consumed query cannot observe a conditional edge, so the
  `includes → ¬holds → includes` cycle cannot be written. If that discipline is ever relaxed — if
  a query result can decide an edge's existence — the cycle becomes writable and **the failure is
  silent**. That is a change to this library's premise, and it announces itself nowhere.
- **ADR-0008 §3's `bounded well-defined`.** It takes two of Vogt's three conjuncts, so an
  arbitrary user-supplied function inside a declaration is what makes the translation's TOTALITY a
  question. This library states the precondition and supplies no missing conjunct; the debt is
  `den-hoag-xin3`'s.
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
  it claims. The direction of the error is the safe one — partners only ADD stable models, so a
  program with none does not acquire one, and the criterion still refuses what it would have
  refused.

## Running the suites

```bash
cd ci && nix flake lock          # after changing an input
nix-unit --flake ./ci#tests      # the suites
nix-unit --flake ./ci#testsError # cells whose subject is an error MESSAGE
cd ci && nix fmt -- --ci         # format (run from the MAIN checkout, never a linked worktree)
```

Count ❌ **and** ☢️ in the output; a run with zero of the first and some of the second has not
passed.

## Formatting

`nix fmt -- --ci` REWRITES the tree, so a second run is green regardless of what the first found.
`git add` new files **before** formatting — untracked files are invisible to treefmt and a
`0 changed` report does not cover them — and `git add` again **after**.
