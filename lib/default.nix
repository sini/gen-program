# gen-program — THE CONSUMER THAT TURNS DECLARATIONS INTO A PROGRAM AND SOLVES THEM.
#
# gen-scope ships the semantics: `program`, `least-model`, `well-founded`, `engine` and
# `stratify`, all exported, all tested, and — measured before this library existed — called by
# nothing. This library is that consumer. It implements NO semantics; the semantics is one library
# over and it is already ruled (ADR-0020, ADR-0022). What this one owns is the translation from a
# framework's declarations to a program, the pass-boundary construction that keeps the third value
# from vanishing, the coherence adjudication that keeps silence from reading as admission, and the
# call.
#
# ── WHY IT IS SHARED RATHER THAN PER-FRAMEWORK, WHICH IS THE RULING'S OWN GROUND ──
# With each framework building its own declarations→program step, ADR-0022's confluence commitment
# would hold only for the programs each framework happened to construct correctly. ONE
# construction, ONE input path, both frameworks consuming it — which is what makes a
# substrate-level semantic commitment mean anything at the surface.
#
# ── WHY IT IS ADJACENT TO THE ASSEMBLY LAYER RATHER THAN INSIDE IT ──
# gen-assemble publishes, under §Design Principles, that "**The toolkit never evaluates.** It
# composes the argument to the evaluator's call. Evaluation belongs to the sole evaluator, and
# limb 3 of the membership criterion is exactly this line." This library's ruled purpose is to
# REACH `engine.solve`, so folding it in would make that toolkit transitively evaluate and would
# change a published contract other work may already rest on. Adjacency changes no published
# property. (Owner-ruled; spec R§2.11, R§4.3, O8.)
#
# ── THE NAMES, AND EACH ONE OWES A PER-PRIMARY CHECK RATHER THAN A CORPUS TOTAL ──
# ADR-0011's theory-terminology rider asks whether a term resolves at the primary the construct
# CITES, not whether it exists somewhere in the corpus, and for this library's family those come
# apart completely.
#
# ★ THE PREDICATE IS PART OF THE MEASUREMENT AND IS NAMED WITH IT: `grep -aoE "\b<term>\b"`,
# CASE-SENSITIVE, over the paper transcription only (both archived files open with an archivist
# note explicitly marked NOT PART OF THE SOURCE TEXT, so a whole-file sweep mixes typed commentary
# with extracted text), counting OCCURRENCES rather than lines. A figure whose predicate is not
# stated is not a measurement — a reader cannot tell what it counted.
# ⇒ The spec's own R§0.4 figures are the CASE-INSENSITIVE reading of the same corpus and differ
# where a term opens a sentence: `program` reads 101 / 154 there against 100 / 152 here, `rule`
# 12 / 78 against 11 / 78. Both reproduce; **the conclusion is identical under either predicate**,
# because the disjointness below is 20/0 and 0/20 with or without `-i`, and the negative control
# is 0 under both.
#
#   program              ABW 100 · VGRS 152   → resolves at BOTH; the library's own name
#   rule                 ABW  11 · VGRS  78   → resolves at BOTH
#   stratum              ABW  20 · VGRS   0   → ABW ONLY; not a name published here
#   well-founded model   ABW   0 · VGRS  20   → VGRS ONLY; not a name published here
#
# ⇒ `program` is the term that resolves at both primaries this library cites, which is why the
# library is named for it and why no construct here is named `stratum` or for the well-founded
# model — those belong to the driver and the semantics respectively, and both live in gen-scope.
#
# ★ `policy` APPEARS IN NO IDENTIFIER PUBLISHED HERE, and that is a measured decision rather than
# a preference. The word is FOUR-WAY OVERLOADED: it is van Antwerpen's own term for the (E, <)
# carrier pair — "the scope graph and resolution calculus are parameterized with … a regular
# expression E that defines the scope **reachability policy**, and an order < … that defines the
# scope **visibility policy**" — and under the 2018 arrangement that parameter is attached PER
# QUERY, which is this library's own granularity; it is a merge strategy shipping as six
# identifiers across four substrate libraries; it is Manchanda & Warren's view-update translation
# policy; and it is den's own rule surface. It stays where the approved vocabulary mapping puts
# it: on the DECLARATION, at the framework surface. The mechanism is substrate-side and takes the
# theory's terms.
#
# ★ AND NO IDENTIFIER IS PUBLISHED FOR THE ACT. Turning declarations into ground rules has no term
# in either corpus — `grounding` measures 0 occurrences across both, while the adjectival
# collocations `ground atom` and `ground instance` do resolve — so this library names the RESULT
# (`program`) and the INPUTS (`rule`, `declaration`) and gives the act no name of its own.
#
# ── THE SUBSTRATE ARRIVES INJECTED, WHICH IS THE BOUNDARY RULE AND NOT A CONVENIENCE ──
# Only plain data crosses a gen↔gen boundary. This library takes `prelude` and `scope` as VALUES
# and constructs inside the consumer's own evaluation; it re-exports neither, and in particular it
# does not republish gen-scope's constructors under names of its own. What it does carry through
# is gen-scope's PROGRAM value, unchanged, in a field — that value is plain data by its own
# module's statement, so carrying it re-exports no build.
{ prelude, scope }:
let
  rules = import ./rules.nix { inherit prelude scope; };
  # The ONE recorded budget, wired here. The coherence module takes it as a parameter so a
  # derivation run can reach the construction past the figure — but this is the only wiring the
  # published surface has, so a consumer can read the budget and cannot select one.
  stableModel = import ./stable-model.nix {
    inherit prelude scope;
    budget = import ./budget.nix;
  };
  modelling = import ./model.nix { inherit prelude scope stableModel; };
in
{
  # ── THE TRANSLATION ──
  inherit (rules)
    rule
    program
    declaration
    ;

  # The refusals' CONTENT, published as data. Each refusal in `program` throws, and `tryEval`
  # discards a message — so a suite that could only assert THAT something refused would be equally
  # satisfied by a construction with one refusal in it. These are what the throws render, and a
  # consumer can read which declarations are unresolvable without provoking one.
  inherit (rules)
    unresolvedRelata
    reservedCollisions
    ;

  # ── THE CALL ──
  inherit (modelling)
    model
    mkModel
    ;

  # ── THE RESOLVED RELATION'S VOCABULARY ──
  inherit (modelling)
    flagNames
    flags
    ;

  # ── THE NAMESPACE THIS LIBRARY OWNS INSIDE THE HERBRAND BASE ──
  inherit (modelling)
    reservedPrefix
    isReserved
    ;

  # ── THE COHERENCE CRITERION ──
  inherit (stableModel)
    adjudicate
    stableModelBudget
    stableModelCriterion
    adjudicationOutcomes
    ;
}
