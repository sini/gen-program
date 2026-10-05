# gen-program

The consumer that turns a framework's declarations into a **logic program**, drives gen-scope's
well-founded engine over it, and carries the third value out under its own name.

gen-scope ships the semantics — `program`, `least-model`, `well-founded`, `engine`, `stratify` —
all exported, all tested, and, measured before this library existed, **called by nothing**. This
library is that consumer. It implements no semantics of its own.

```nix
genProgram = import gen-program/lib {
  prelude = gen-prelude.lib;
  scope = gen-scope.lib;
  algebra = gen-algebra.lib;
  identity = gen-identity.lib;
};

# `program frozen declarations`: the frozen set (what strictly earlier passes settled), then the
# declarations it is read against.
program = genProgram.program [ ] [
  { head = "guard:B"; relata = [ ]; }
  { head = "member:X"; pos = [ "guard:B" ]; relata = [ ]; }
  { head = "guard:A"; pos = [ "member:X" ]; neg = [ "excluded:X" ]; relata = [ ]; }
];

model = genProgram.model {
  inherit program;
  interpretation = [ ];   # verdicts the caller asserts; required, so an empty one is said
  prior = null;           # the previous pass's record; required, so the first pass says so
  complete = true;
};

model.resolve "member:X"    # => { flag = "T"; included = true; }
model.adjudication.outcome  # => "admitted"
```

## Why it exists

**A ruled, built, tested semantics was called by nothing.** The substrate settles the meaning of a
policy stratum — well-founded semantics (Van Gelder, Ross & Schlipf 1991) under a confluence
commitment; gen-scope computes it; nothing turned a declaration into a program. That gap
had a second cost beyond the obvious one: **the confluence commitment's recorded exit is armed by
benchmark acceptance failure**, and with nothing reaching the solve the benchmark never ran, so
the exit could never fire. A consumer makes the confluence commitment testable rather than merely stated.

**One construction, not one per framework.** With each framework building its own
declarations→program step, the confluence guarantee would hold only for the programs each framework
happened to construct correctly.

**The workload is measured, not anticipated.** den v1 at `ecaefcb` composes a negation over the
**in-flight** include set and runs two named fixpoint loops, capping at `maxPolicyIterations = 10`
and failing at the bound. The report states the standard in v1's own terms: it *"does not
establish convergence statically — it **bounds** it and fails at the bound."* A budget standing in
for a convergence condition is the defect. Well-founded semantics gives that shape a meaning; this
library computes it.

## What it does

### The translation

`head` is the fact a declaration asserts; `pos` is its enabling membership plus the positive
literals of its guard; `neg` is its negated literals. A declaration with neither body is a **fact**
— gen-scope's `mkRule`'s own base case.

An **atom is one fact** — one ⟨scope, member⟩ membership, one promotion — never a relation symbol.
That granularity is deliberate, and it is what lets one contested pair be contested while
its neighbours in the same relation settle. A translation that atomised per relation would contest
a whole relation on one contested pair.

**Atom names are the caller's.** A library may not encode topology or kind relationships into the
names it mints, and a topology-free program datatype removes only one channel for that: an atom
scheme keyed `host:…→user:…` encodes the forbidden relationship just as effectively, and the
datatype cannot tell. So this library mints no atom name from a scheme of its own. The only names
it introduces are the reserved partners below, which name no kind and no relationship.

### The pass boundary

`engine.solve interpretation program` takes the program last, and verdicts reach it as the
**interpretation** — a list of `{ atom, verdict }`, travelling as themselves. In `model` that list
is the caller's own and nothing else: the general **assertion** channel, an input of the pass that
states it. It carries no default (a defaulted empty list is the silent collapse it exists to
prevent, so a caller asserting nothing supplies `[ ]` and says so), and **an assertion does not
persist**: a later pass holds it only if it restates it. No verdict of a prior pass is ever carried
into this list (below).

The three values are three different kinds of thing, and gen-scope's engine is where that is
stated. **TRUE** is an external fact and seeds both of the engine's operators. **FALSE** is inert —
`verdict` is already total, so a FALSE carry asks for the answer the model gives anyway, and the
only way to make it operative would be to let it suppress a derivation this pass justifies, which
is pinning. **UNDEFINED** is a *suspension of falsity*: a carried-undefined atom is one whose
support lies outside this program, and it enters by being exempt from the greatest unfounded set.

```nix
model = genProgram.model {
  prior = null;
  program = genProgram.program frozen declarations;
  interpretation = [ { atom = "member:X"; verdict = "undefined"; } ];
  complete = false;
};
```

#### What this replaced, and why the deletion is the point

The boundary used to be a **two-rule gadget** per contested atom — `x :- not x′` and `x′ :- not x`,
a negative cycle whose well-founded verdict is UNDEFINED. It reproduced the third value per atom,
and it was measured **wrong in the direction that matters**: the partner rule makes a carried atom
freely supported in every candidate containing it, so a program with **no stable model acquired
one** at the boundary. On a recurring declaration set the coherence adjudication flipped
REFUSED → ADMITTED at the first pass and never returned.

Three constructions died with it, and each was a place content could vanish:

- the **fresh atoms**, which entered the Herbrand base and every verdict list;
- the **subtraction** that hid them again — itself a place content could vanish, which is why it
  needed a leak control rather than trust;
- the **reserved namespace** that made the collision impossible rather than improbable.

⇒ **The vanishing surface is not fixed; it has no expression.** By construction, not repair.

★ **And the unenforced contract died with it.** `carried` was documented as *the atoms whose
verdict was UNDEFINED* and nothing checked it — carrying a settled atom injected undefinedness
silently. It could not be checked, because the prior pass's model was not an argument to the
construction. Under the parameter **it is the argument**: an interpretation carries each atom's
verdict with it, so asserting undefinedness of an atom that did not have it has no expression
either. No check was added, because there is nothing left to check.

★★ **The agnosticism discharge is stronger than the prefix ever made it.** The whole exposure was a
library minting atom names of its own. With the minter gone, every atom in an
authored position is a string the caller wrote — not "the library's own names are fenced off" but
**the library has none**.

#### The claim, and its oracle

The design is stated in two vocabularies — the unfounded-set account and the alternating-fixpoint
account — and VG93's **Theorem 7.8** makes their un-interpreted forms an *identity*, with no slack.
But with a non-empty undefined carry the engine's two seeded operators belong to two **different**
augmented programs, while the alternating transformation composes one program's operator with
itself. **So the construction is `A_Q` for no `Q`, Theorem 7.8 does not reach it, and the
interpreted analogue is claimed and not proved.**

`ci/tests/identity.nix` is what stands in for the proof: a test-only reference implementation of
the unfounded-set account, run beside the shipped construction and asserted **identical atom by
atom**. Its control is a measured disagreement — removing the exemption makes a positive reader of
a carried atom read FALSE where the shipped construction says UNDEFINED, which is the exact defect
that rejected the spec's first revision. **If that suite ever fails, the claim is refuted; that is
a finding, not a bug.**

### The coherence criterion

**Stable-model existence** (Gelfond & Lifschitz 1988) is the refusal oracle. gen-scope states in
its own README that the oracle *"is NOT built here"*. It is built here, and it runs under a derived budget.

**The normal path is polynomial.** The well-founded computation is the sole value path and runs on
every program. The search below decides admissibility only.

| the model                  | what happens                                                                                                                        |
| -------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| **total**                  | short-circuits — it **is** the unique stable model (VGRS 1991, **Corollary 5.6**), so existence is certified free by the value path |
| **partial**, within budget | searches the candidate space **Corollary 5.7** bounds, exhaustively                                                                 |
| **partial**, past budget   | `not-evaluated` — a named outcome stating an *absence* of adjudication, never an admission                                          |

The search space is not a heuristic. Corollary 5.7 — *"The well-founded partial model of P is a
subset of every stable model of P"* — with Definition 2.4's partial interpretation being *"a
consistent **set of literals**"* constrains **both signs**: every stable model contains every
well-founded true atom and excludes every well-founded false one. So the candidates are exactly
`trueAtoms ∪ S` for `S ⊆ undefinedAtoms`, which is **2^u in the contested count** and exhaustive
over stable models — and that exhaustiveness is what licenses the `refused` outcome. It is a
decision, not a sample.

Stability is tested with gen-scope's own `reduct` and `leastModel`. Nothing here re-implements a
reduct or a fixpoint.

### The resolved relation

The semantics gives the atom a named third value; den's include surface has two. The fork over what
an undefined gate means there was **settled**: the relation acquires a third value every consumer
handles, in van Antwerpen et al. 2016 §4.1–4.2's published `T` / `P` / `U` shape with vA2018
§4.3's delayed queries.

There is no shape of the result record from which a consumer can take a bare boolean:

| flag | when                                                                                                                                            | `included`                                                                                     |
| ---- | ----------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- |
| `T`  | the relation is closed, the atom has a two-valued verdict                                                                                       | answers both ways                                                                              |
| `P`  | the relation is still growing, the atom **is** derived and its whole support is negation-free                                                   | answers `true` — the positive fragment is monotone, so no later pass retracts it               |
| `P`  | the relation is still growing, the atom **is** derived but its support rests on `not` at any depth, or on an atom only `interpretation` asserts | **refuses by name** — a later pass may derive what the `not` reads; an assertion is not a rule |
| `P`  | the relation is still growing, the atom is **not** derived                                                                                      | **refuses by name** — a later pass may derive it                                               |
| `U`  | the atom has no two-valued verdict                                                                                                              | **refuses by name** — the semantics' third value                                               |

The three withheld answers are **fields that throw**, never absent fields and never `null`. Every
`if r.included` in the world reads `null` as false, which is the silent collapse the ruling ended.
On a growing relation `verdict` refuses a withheld atom by the same name, and the atom is enumerated
in `withheldAtoms` rather than `trueAtoms`, so no reader of the record serves it.

**At `complete = false`, an asserted atom withholds too.** "Negation-free" is gen-scope's least
model over the program's negation-free RULES, and an assertion is not a rule: with `x` asserted
`true` and `y :- x`, both `x` and `y` read `P` and refuse while the relation grows, and both answer
`T`, in, once it closes. That is conservative — latency, never an unsound answer — and
`ci/tests/withhold.nix` pins it.

**The passes are the caller's to drive** — this library owns no driver — **and each pass takes
the previous one's record as `prior`:**

```nix
pass1 = genProgram.model { program = p1; interpretation = [ ]; complete = false; prior = null; };
pass2 = genProgram.model { program = p2; interpretation = [ ]; complete = true; prior = pass1; };
```

**No verdict crosses a pass.** Each pass solves its own cumulative program from scratch, at its own
`complete`, under its own `interpretation`, so the final pass's answers are the final graph's
answers whatever the pass boundaries were: the semantics never mentions arrival. A carried `undefined` used to pin an atom a
later rule settled — a negation cycle broken by a later fact stayed `U` — and the protocol no longer
derives any carry. A caller can still rebuild that pin by hand, by forwarding a prior pass's
verdicts as its own `interpretation`: that is this pass's assertion, answered as asserted, and it is
not the protocol. `prior` is the **omission guard** and nothing else:
`p2` must contain **every** rule of `pass1.rules` — a prior pass's verdicts are not rules, so a
delta-only program re-derives nothing earlier passes settled — or `model` refuses by name,
catchably. A body is a set of literals, so a resubmission may reorder a body or repeat a literal.
`pass1.rules` is an index keyed by each rule's canonical JSON rendering (bodies sorted and
deduplicated), so the check is a lookup per rule rather than a scan. `prior` is required: a first or single pass states `prior = null`.
What remains the caller's is `complete = true`, set only once it knows, by its own external
knowledge, that no further declarations can arrive; an unchanged answer set between two passes is
consistent with that and does not entail it.

★ **The letters are kept rather than spelled, and that is a transplant guard.** This library cites
two primaries that both use *total* and *partial* for **different things**: VGRS Definition 2.6
makes a *model* total when it is two-valued over the Herbrand base, while van Antwerpen's `T` is
about whether an answer **set** is complete. A field named `total` would read as one and mean the
other.

### The solved model's edges

A declaration may carry a **`label`**. It then asserts that its head, when included, **is** the
edge `{ from = relata[0]; to = relata[1]; label; }` — the label is the rule's own, never parsed out
of the atom, and the endpoints are relata that already passed the frozen-set check.
`ruleEdges model declarations` returns two plain edge lists (and two promotion lists, below):

- **`candidates`** — every labelled edge, whatever it resolves to. A function of the declarations
  alone: it never forces `model`, so a gate over the declared edges reads it at registration.
- **`reached`** — the candidates whose head the model includes. An edge that resolves off is
  absent. The caller appends it to its declared edges: one edge list, one graph.

An edge is a property of the membership, so the set is keyed by head: agreeing declarations of one
head collapse and conflicting ones refuse. An edge list has no third value and no flag, so
`reached` refuses by name on a `U` head, on a relation still growing (`complete = false`: its
absences are the negatives that relation withholds), and on a model solved from other
declarations. One membership's answer stays readable through `resolve`.

A declaration may instead carry **`promote`**, a relation kind. Its head, when included, then
denotes a **node**: a reified relation over its relata, so its `relata` are a labelled
tuple, an attrset label → identifier. Edge or node is declared on the rule, never read off the
relata count, and a declaration carrying both `label` and `promote` is refused. Two more fields:

- **`promotions`** — one **promotion record** per promoted head, model-free:
  `{ identifier = head; kind; relata; content = { }; site; }`, gen-scope's emitter without `pass`.
- **`promoted`** — the promotion records whose head the model includes. It reads the same verdicts
  as `reached` under the same refusals, so the two refuse together, and a refusal names a promoted
  head as a node.

★ **A promotion record is not a node.** It carries no identity, because the identity is a hash over
the relata's minted identities and only the mint holds those. Only the mint makes the node: the
caller hands `promoted` to gen-scope's `mintStrata` beside its relata's emitters, at a pass strictly
later than theirs —
`mintStrata kinds (relataEmitters ++ map (p: p // { pass = N; }) r.promoted)`. `candidates` carries
each promotion's incident edges (head → relatum, labelled by role); `reached` does not, because the
mint publishes the node and its edges together.

### The policy-body algebra

The authoring surface for policy bodies, and the interpreter that resolves one. A normal-form
policy body is a list of clauses: a single skeleton (`emit`), an iteration over a computed list
(`forEach { over, emit }`, the item joining the scope), or a **door clause** whose body is a
reference to a closure the framework registered. Four slots are registration data — the
constructor (closed enum `member` · `deliver` · `edge` · `suppress` · `realize`, published as
`ctorNames`), the emitted kind, the payload attrset's **spine**, and the suppress target — and the
firing context is **unreachable from them by construction**. Every other slot — guards, `over`,
payload values, free targets — is a **term** of gen-algebra's first-order term algebra: data the
walk can read, never a function. A body names the coordinates it may read (`declared`), and each
clause is checked at construction: a body reads a coordinate only where its condition guarantees it
is present.

`deriveCodomain` reads `{ emits; binds; suppresses }` off the structure with no context parameter,
so the recovered-empty-head failure class (fire a value-conditional body at a sentinel, read back
the empty codomain) has no expression: **a term is read, not fired**. A malformed body is refused
at construction as a **tagged value** naming the violated slot, the author as the blamed party,
and the remedy. `groundInstances` resolves an admitted body at a context and returns the fired
declarations as data; a door clause resolves through the door the framework passes in, which is
the only place a closure is applied. Context keys are an open world: `groundInstances` does not
inspect them, so an option placed in the context map (`{ thimble = "x"; sources = { … }; }`) is
read as a coordinate named `sources`, never as the option, which is ignored, by design. Options go
in the first argument: `groundInstances { sources = { … }; } context body`. Each rule and each
firing carries an identity minted through gen-identity,
the firing's over the sources of what it read, never the values.

The per-firing codomain check is published as `codomainBreaches contract declarations`, so the
gen-rules door validates a closure's output against the same row table at **every firing**; a
breach is named by field and delta. `admit` is the registration door: hand-rolled records fail the
same walk the formers run, and a bare lambda is refused with the signpost to the gen-rules door.
The declared escape is retired: `escape` and `fireEscape` stay as aliases that refuse
`policy-body/escape-retired`, naming the door, and `admit` refuses an escape record the same way.

A declaration can also write its body as a condition term: `declaration { when = all [ (has "a") (not (has "b")) ]; } relata head` is `pos = [ "a" ]; neg = [ "b" ];`, solved by the same
well-founded engine.

## The budget, and the curve it is derived from

The figure is never a bare number. It is derived from this library's own measured cost curve and
recorded with its derivation, and `reDerivationOwedOn` names the constructions whose editing owes a
re-derivation. **This work changed two of the four it named** — the stability test is now seeded
with `Pos(I)`, and gen-scope's least-model door now takes a starting set — so a re-derivation was
owed by the budget's own trigger, not as a follow-up.

```bash
nix eval --impure --json -f ci/bench/coherence-cost.nix at --apply 'f: f "unstable" 16'
```

**The worst-case arm** — `unstable`, `u` independent `p :- not p`, no stable model anywhere, so the
walk is exhaustive and nothing short-circuits:

| u      | candidates | wall clock                                                     |
| ------ | ---------- | -------------------------------------------------------------- |
| 14     | 16,384     | 0.33 – 0.73 s                                                  |
| 15     | 32,768     | 1.34 – 1.45 s                                                  |
| 16     | 65,536     | 1.28 – 1.31 s (five readings)                                  |
| **17** | 131,072    | **2.57 – 5.12 s** ← exceeds the criterion on its worst of five |
| 18     | 262,144    | 6.64 – 9.27 s                                                  |

⇒ **`contested = 16`, re-derived and unmoved.** That is a result rather than a non-event: the
seeded fixpoint adds a *constant* per candidate, not an exponent, so the curve shifts without
changing where it crosses the criterion. A re-derivation that reproduces its predecessor is still a
re-derivation — what would have been dishonest is not running it. Read against the **worst**
reading, per this file's own correction.

### Where the parameter actually pays: the carried recovery

Under the retired boundary each carried atom brought a **partner** into the Herbrand base, so a
pass carrying `n` contested atoms arrived at the next with roughly twice the contested count —
measured `2n+1` — and the budget was effectively **halved** in carried terms: about 7 atoms could
cross one boundary. The partners are gone.

★★ **What replaces the `2n` is not a constant.** The contested count at the next pass is the carried
set **closed under reachability over both signs** — carried undefinedness propagates through a
positive body exactly as it does through negation. Measured on the three-axis `carriedAt n p q`:

| n   | positive readers | negative readers | contested                                                           |
| --- | ---------------- | ---------------- | ------------------------------------------------------------------- |
| 4   | 0                | 0                | **4** — the partners are gone: `n` carried costs `n`                |
| 4   | 4                | 0                | 8                                                                   |
| 4   | 0                | 4                | 8 — a family holding this axis fixed could not see half the closure |
| 4   | 2                | 2                | 8                                                                   |
| 2   | 1                | 1                | 4                                                                   |

⇒ **The budget is no longer halved in carried terms**: about 16 atoms may cross one boundary where
before about 7 could, less whatever this pass reads from them. ★★ And it is an **upper bound**, not
an identity — a reader whose body cannot be satisfied does not become contested — so the real count
is generally smaller. Safe in direction, and called a bound.

★★ **Measuring refuted an assumption that looked safe, and the arm stays with its reason
corrected.** `anticorrelated` was written up as the *cheap* corner because a program with stable
models short-circuits. It does — but where the first stable model sits in the enumeration is a
property of the program, and for that family it sits **exactly one third of the way through at
every rung** (86/256, 1366/4096, 21846/65536). Having stable models buys a factor of three, never
an exponent.

A third reading, which checks the design rather than the figure: **`mixed`** — four contested atoms
beside a settled bulk of 10, 100 and 400 cost 6 candidates and 0.04 s at all three sizes. That is
Corollary 5.7's restriction working: the budget prices the contested corner, not the program.

## What it does not do, and does not claim

- **It owns no driver.** `stratify` is the ABW completeness driver and is already instantiated;
  `engine.solve` is the meaning of one pass's rules. This library owns the program handed to the
  second, once per pass.
- **It mints no identity**, publishes **no query surface**, **no ordering door** and **no
  materialisation** of a view of the graph (`ruleEdges` is a source of the graph's edges, not a view
  of it), and **re-exports nothing of gen-scope**.
- **It reproduces no shape it retires**: no keyset-equality convergence test, no
  union-accumulation without retraction, no in-flight membership predicate handed to a caller's
  guard. The program is closed before it is solved; the model is a function of the rules.
- **It claims the construction and not the theorem.** ABW's theorem is about a *stratified*
  program, and a pass here carries negative cycles by premise, so the pass sequence is not an
  instance of their iteration. What replaces it is a frozen set per pass, which makes
  each pass's input closed. **No archived primary states that a sequence of
  well-founded models over successively frozen inputs inherits what a single one has.**
- **An acquisition gap is recorded as one.** VGRS 1991 is archived; Van Gelder 1993, which gives
  the alternating-fixpoint construction gen-scope actually iterates, is cited-not-held.

### Two standing conditions it rests on and does not control

- **The input-type discipline.** A consumed query cannot observe a conditional edge, so the
  `includes → ¬holds → includes` cycle cannot be written. If that is ever relaxed the cycle becomes
  writable and **the failure is silent**.
- **`bounded well-defined`**, which takes two of Vogt's three conjuncts. An
  arbitrary user-supplied function inside a declaration is what makes the translation's totality a
  question, and that debt is open.

## Running it

```bash
nix develop ./ci --command ci                # the suites, guarded
nix develop ./ci --command ci --tests-error  # cells whose subject is an error MESSAGE, guarded
nix-unit --flake ./ci#tests                  # the suites, unguarded
nix-unit --flake ./ci#testsError             # the error cells, unguarded
# `ci` refuses when anything under a declared read root is unknown to git (any extension or
# name, `_`-prefixed included); `git add` it or move it. The unguarded forms read a git-filtered
# copy of the tree, so an untracked cell is silently absent and the run stays green.

# The constructor's refusal of an omitted `adjudication`, exhibited as an exit status.
# Read it UNPIPED — under zsh a pipeline's per-stage status is `$pipestatus`, lowercase.
nix eval --impure -f ci/bench/requiredness-probe.nix dropped    # MUST fail, naming the field
nix eval --impure -f ci/bench/requiredness-probe.nix attached   # MUST succeed — the control

cd ci && nix fmt -- --ci          # from the MAIN checkout, never a linked worktree
```

Count ❌ **and** ☢️; a run with none of the first and some of the second has not passed.

## Naming

`program` is the term that resolves at **both** archived primaries this library cites — measured
on the paper transcriptions, word-bounded, with a live in-file control and a negative control at
zero in the same runs: **ABW 100 · VGRS 152**. `stratum` resolves at ABW only (20 / 0) and
`well-founded model` at VGRS only (0 / 20), so neither names a construct here — they belong to the
driver and the semantics, both of which live in gen-scope.

**`policy` appears in no published identifier**, and that is measured rather than preferred: the
word is four-way overloaded, including as van Antwerpen's own term for the `(E, <)` carrier pair —
which under the 2018 arrangement is attached **per query**, this library's own granularity. And no
identifier names the **act**: `grounding` measures 0 occurrences across both corpora, so the
library names the *result* and the *inputs* and gives the act no name. Both absences are asserted
in `ci/tests/surface.nix` with positive controls beside them.

Full per-primary table and the ligature-damage measurement: `AGENTS.md`.
