# THE TRANSLATION: one declaration becomes one rule, and a pass's declarations become one program.
#
# THEORY, AND THE TWO PRIMARIES DO NOT OVERLAP. A `rule` is `head :- p₁ … pₙ, not q₁ … not qₘ` and
# a `program` is a set of them — Van Gelder, Ross & Schlipf 1991, Definition 2.1 (a general logic
# program is a finite set of general rules), and Apt, Blair & Walker 1988 for the stratified
# fragment those rules fall into when no cycle carries a negative edge. Both terms resolve at BOTH
# archived primaries with live in-file controls, which is why they are the names published here;
# `stratum` resolves at ABW ONLY and `well-founded model` at VGRS ONLY, so neither is a name this
# file may use for a construct of its own (ADR-0011's per-primary rider).
#
# ★ NOTHING HERE IS A SEMANTICS. The rules are handed to gen-scope, which owns the model, the
# reduct, the least fixpoint and the alternating fixpoint. This file builds the argument.
#
# ── WHAT ONE DECLARATION BECOMES ──
# `head` is the fact the declaration asserts. `pos` is its enabling membership together with the
# positive literals of its guard. `neg` is its negated literals. A declaration with neither body
# is a FACT — that is `mkRule`'s own base case, not an omission — and the Herbrand base is closed
# by construction over the rules, so an atom no rule can derive comes back FALSE from the model
# rather than absent from it.
#
# ★ ATOM GRANULARITY IS RULED, NOT CHOSEN (ADR-0020): an atom is ONE fact — one ⟨scope, member⟩
# membership, one promotion — and never a relation symbol. Nothing here groups facts into a
# relation, because a translation that atomised per relation would contest a whole relation on one
# contested pair and would not be ADR-0020's semantics under ADR-0020's name.
#
# ★★★ THIS FILE MINTS NO ATOM AT ALL, AND THAT IS NOW TRUE WITHOUT A GUARD.
# `den-hoag-h2yp` law 2 forbids encoding topology or kind relationships, and a topology-free
# program datatype removes only ONE channel for that: an atom scheme keyed `host:…→user:…` encodes
# the forbidden relationship just as effectively, and the datatype cannot tell.
# ⇒ **EVERY ATOM IN AN AUTHORED POSITION IS A STRING THE CALLER WROTE.** There is no exception to
# hedge, because there is no minter. What used to buy that property — a reserved namespace, a
# prefix refusal, a recognition predicate — is RETIRED, and the discharge is stronger than the
# prefix ever made it: not "the library's own names are fenced off" but "the library has none."
#
# ── WHAT USED TO BE HERE, AND WHY ITS DELETION IS THE POINT ──
# A prior pass's contested atoms used to arrive as `carried` and be COMPILED INTO RULES: two rules
# over one fresh atom, `x :- not x′` and `x′ :- not x`, a negative cycle whose well-founded verdict
# is UNDEFINED. It reproduced the third value per atom, and it was measured WRONG in the direction
# that matters — the partner rule makes a carried atom freely supported in every candidate
# containing it, so a program with NO stable model acquired one at the boundary.
#
# ⇒ **A PRIOR PASS'S VERDICTS ARE NOT RULES, AND THE ENGINE NOW HAS A CHANNEL THAT SAYS SO.** They
# travel as an INTERPRETATION, handed to `solve` beside the program (see `model.nix`). Three
# constructions died with the gadget and each was a place content could vanish:
#   · the fresh atoms, which entered the Herbrand base and every verdict list;
#   · the SUBTRACTION that hid them again — itself a place content could vanish, which is why it
#     needed a leak control rather than trust;
#   · the reserved namespace that made the collision impossible rather than improbable.
# **The vanishing surface is not fixed; it has no expression.** That is by-construction rather than
# repair, and it is the strongest single argument for the arm the owner ruled.
#
# ★ AND THE UNENFORCED CONTRACT DIED WITH IT. `carried` was documented as *the atoms whose verdict
# was UNDEFINED* and nothing checked it — carrying a SETTLED atom injected undefinedness silently
# and it propagated to that atom's readers. It could not be checked here, because the prior pass's
# model was not an argument to this construction. Under the parameter **it is the argument**: an
# interpretation carries each atom's verdict WITH it, so asserting undefinedness of an atom that
# did not have it has no expression either. No check was added, because there is nothing to check.
#
# ── THE FROZEN SET, AND WHY THE REFUSAL NAMES AN IDENTIFIER RATHER THAN A CYCLE ──
# ADR-0016 ruling 7 with ADR-0033 clause 1: a pass resolves relata against what STRICTLY EARLIER
# passes settled, so a later pass's program is built over closed input and no pass reads its own
# in-flight output. ★ That is a CONSTRUCTION, not a theorem — ABW's theorem is about a stratified
# program and a pass here carries negative cycles by premise, so the pass sequence is not an
# instance of their iteration and this file claims none. **The interpretation changes the
# boundary's REPRESENTATION, not the pass schedule**, so that question is inherited exactly as it
# stood.
#
# ★★ THE REFUSAL THAT FIRES IS THE UNRESOLVED-RELATUM ONE, AND NOT A CYCLE DETECTOR. ADR-0033:
# "a same-pass reference CANNOT BE NAMED … there is no cycle check to run, because a stratum's
# in-flight output is not nameable from inside it." A refusal naming a cycle would be a detector
# for something inexpressible. What IS named is the identifier: resolution is identifier→identity
# against the frozen set, a same-pass identifier is simply not in that set, and a ROOT relatum
# refuses by the identical path because nothing earlier minted it either. ★ It is about RELATA —
# identifiers — and never about ATOMS; collapsing the two universes would make an identifier
# derivable.
{ prelude, scope }:
let
  quoteAll = names: prelude.concatMapStringsSep ", " (n: "'${n}'") names;

  # ── THE REFUSAL'S CONTENT, PUBLISHED AS DATA ──
  # The refusal below throws, and `tryEval` discards a message. A suite that could only assert THAT
  # something refused would be equally satisfied by a construction with one refusal in it, so the
  # CONTENT is computed by a function a caller can call and a cell can assert. The throw renders
  # what this returns; it does not re-derive it.
  unresolvedRelata =
    { declarations, frozen }:
    let
      settled = prelude.genAttrs frozen (_: true);
    in
    prelude.unique (
      prelude.filter (id: !(settled ? ${id})) (
        prelude.concatMap (d: d.relata) (map declaration declarations)
      )
    );

  # ── THE DECLARATION ──
  # A STRICT PATTERN, so a field this library does not know is refused BY NAME at application by
  # the evaluator itself and a missing one is refused the same way. `pos` and `neg` default because
  # ADR-0020's own base case says a declaration with neither body is a fact; `relata` does NOT,
  # because a defaulted empty relatum list is a decision nobody made and nobody can see — it would
  # silently assert "this declaration relates nothing" and skip the frozen-set check for exactly
  # the declarations that forgot to state it.
  declaration =
    {
      head,
      pos ? [ ],
      neg ? [ ],
      relata,
    }:
    {
      inherit
        head
        pos
        neg
        relata
        ;
    };

  # One declaration's rule. The relata do not appear: they are IDENTIFIERS resolved against the
  # frozen set, and the rule's atoms are MEMBERSHIP FACTS.
  rule =
    d:
    let
      normalized = declaration d;
    in
    scope.mkRule {
      inherit (normalized) head pos neg;
    };

  # ── THE PROGRAM ──
  # It returns gen-scope's own value, UNCHANGED and UNWRAPPED. Under the gadget this had to be a
  # record — the minted atoms travelled beside the program so the reporting filter could subtract
  # them — and with no minted atoms there is nothing to carry, so the wrapper goes too. A program
  # is plain data by its own module's statement, so handing it back as itself re-exports no build
  # (ADR-0014) and puts no second shape in front of a consumer.
  program =
    { declarations, frozen }:
    let
      unresolved = unresolvedRelata { inherit declarations frozen; };
    in
    if unresolved != [ ] then
      throw "gen-program: ${quoteAll unresolved} is not in the frozen set of relata that strictly earlier passes settled (ADR-0016 ruling 7), so it does not resolve — a same-pass reference and a root relatum both reach this refusal by that one path, and neither is named as a cycle because a stratum's in-flight output is not nameable from inside it (ADR-0033)"
    else
      scope.mkProgram { rules = map rule declarations; };
in
{
  inherit
    rule
    program
    declaration
    unresolvedRelata
    ;
}
