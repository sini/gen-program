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
{
  prelude,
  scope,
  isRefusal,
}:
let
  quoteAll = names: prelude.concatMapStringsSep ", " (n: "'${n}'") names;

  # ── THE NAMES ARE STRINGS, AND A DOOR SAYS SO BY ITS OWN NAME (den-hoag-bkdkg) ──
  # Heads and body atoms become attribute names in the program's index and relata are looked up in
  # the frozen set by name, so nothing but a string survives either. A record handed in their place
  # — the node VALUE where its identifier goes — used to be admitted here and abort past `tryEval`
  # one layer down, naming nothing the caller wrote. The refusal names the TYPE and never the value,
  # because rendering a value that is not a string is the very abort it replaces. Each is forced
  # whole at the door, so a caller reading one field still meets it.
  identifier =
    who: what: v:
    builtins.isString v
    || throw "gen-program.${who}: ${what} is a ${builtins.typeOf v}, expected a node identifier (a string)${
      if builtins.isFunction v then
        "; a guard is written as a `when` term (has, not, all, always), and a closure crosses the gen-rules door"
      else
        ""
    }";

  # ── THE LITERAL TIER (fuci G1): a `when` term lowered to `pos`/`neg` ──
  # A rule body is a conjunction of literals, so the tier admits exactly the literals and their
  # conjunction: `has a` is the positive literal `a`, `not (has a)` the negative one, `all` conjoins,
  # `always` is the empty body. The atom is the string the caller wrote: nothing here mints one, so
  # `eq` (a value test with no atom) and `not` over a compound (Lloyd–Topor needs a fresh atom) refuse,
  # and so does `any`: a disjunction is one declaration per disjunct over the one head.
  lowerWhen =
    t:
    let
      f = t.__bodyTerm or null;
      none = {
        pos = [ ];
        neg = [ ];
      };
      why =
        if builtins.isFunction t then
          "a function `when` stays unlowerable (fuci G1); a closure crosses the gen-rules door"
        # A refusal is recognised only by gen-algebra's own predicate, exact to `refuse`'s string code
        # (den-hoag-s1ua7); any other `left`-shaped value is not a literal, and says so below.
        else if isRefusal t then
          "the term algebra refused it (${t.left.code})"
        else if f == "Any" then
          "`any` is a disjunction, and a rule body is a conjunction: write one declaration per disjunct over the one head"
        else if f == "Eq" then
          "`eq` tests a value and lowers to no atom; write the tested fact as an atom the caller names"
        else if f == "Not" then
          "`not` lowers only over `has a`; negating a compound needs an atom nothing here mints"
        else
          "${if f == null then builtins.typeOf t else f} is not a literal, a conjunction or `always`";
    in
    if f == "Has" then
      none // { pos = [ t.name ]; }
    else if f == "Not" && (t.operand.__bodyTerm or null) == "Has" then
      none // { neg = [ t.operand.name ]; }
    else if f == "Always" then
      none
    else if f == "All" then
      builtins.foldl' (
        acc: x:
        let
          l = lowerWhen x;
        in
        {
          pos = acc.pos ++ l.pos;
          neg = acc.neg ++ l.neg;
        }
      ) none t.items
    else
      throw "gen-program.declaration: `when` is not in the literal tier: ${why}";
  identifiers =
    who: what: vs:
    if builtins.isList vs then
      builtins.all (identifier who "an entry of ${what}") vs
    else
      throw "gen-program.${who}: ${what} is a ${builtins.typeOf vs}, expected a list of node identifiers (strings)";

  # ── THE REFUSAL'S CONTENT, PUBLISHED AS DATA ──
  # The refusal below throws, and `tryEval` discards a message. A suite that could only assert THAT
  # something refused would be equally satisfied by a construction with one refusal in it, so the
  # CONTENT is computed by a function a caller can call and a cell can assert. The throw renders
  # what this returns; it does not re-derive it.
  # POSITIONAL (den-hoag-7gp66 P2, rule 4): `unresolvedRelata frozen declarations`. The
  # declarations are what is read, so they are the subject and go last; the frozen set is what
  # they are read against, which is configuration. Positional arity is structural, so the P1
  # `checkRequired` retires.
  unresolvedRelata =
    frozen: declarations:
    let
      settled = builtins.seq (identifiers "unresolvedRelata" "the frozen set" frozen) (
        prelude.genAttrs frozen (_: true)
      );
    in
    prelude.unique (
      prelude.filter (id: !(settled ? ${id})) (
        prelude.concatMap (d: if d.promote == null then d.relata else builtins.attrValues d.relata) (
          map declarationRecord declarations
        )
      )
    );

  # ── THE DECLARATION ──
  # A declaration AS DATA is a record, `{ head; relata; pos ? [ ]; neg ? [ ]; label ? null; promote ?
  # null; when ? null; }`, and that is the shape `program`'s list, `rule` and `ruleEdges` take. `declarationRecord`
  # is its normaliser: an unknown field and a missing `head` or `relata` are both refused by name and
  # catchably (`checkOptions` over `checkRequired`), where the native formal of P1 aborted
  # uncatchably on a missing one.
  # `pos` and `neg` default because ADR-0020's own base case says a declaration with neither body is
  # a fact; `relata` does NOT, because a defaulted empty relatum list is a decision nobody made and
  # nobody can see — it would silently assert "this declaration relates nothing" and skip the
  # frozen-set check for exactly the declarations that forgot to state it.
  #
  # `label` names the edge the head denotes when it is included: `{ from = relata[0]; to =
  # relata[1]; label; }`, read by `ruleEdges`. It is the rule's OWN, on its own declaration, and never
  # parsed out of the atom — an atom is a string the caller wrote. A declaration is labelled exactly
  # when `label != null`, so an explicit `null` is the omission and never a null-labelled edge. The
  # rule ignores it: `rule` builds from `head`, `pos` and `neg` alone.
  #
  # `promote` names the relation KIND the head denotes when it is included, and it is the other half
  # of that choice: an included head is an edge or a node, never both, so a declaration carrying both
  # is refused. A promoted head is a reified relation (ADR-0016 rulings 2-4), so its `relata` are the
  # LABELLED TUPLE, an attrset label -> identifier, which is gen-scope's emitter shape: a
  # label/relatum mismatch has no expression. Edge or node is DECLARED and never inferred from the
  # relata count, because a two-relatum binding is a node exactly when its rule says so. Two tuples
  # are refused here rather than at the mint: the empty one, because a relation with no relata is
  # not a relation and the mint would mint it; and one labelling a relatum `identifier`, the key the
  # mint reserves for the node's own identifier, whose refusal there would name neither the head nor
  # this door. The rule ignores `promote` too.
  declarationOptions = [
    "pos"
    "neg"
    "label"
    "promote"
    "when"
  ];
  declarationRecord =
    args:
    let
      a = prelude.checkOptions "gen-program.declaration" (
        [
          "head"
          "relata"
        ]
        ++ declarationOptions
      ) (prelude.checkRequired "gen-program.declaration" [ "head" "relata" ] args);
      inherit (a) head relata;
      pos = a.pos or [ ];
      neg = a.neg or [ ];
      label = a.label or null;
      promote = a.promote or null;
      when = a.when or null;
      lowered =
        if when == null then
          { inherit pos neg; }
        else if a ? pos || a ? neg then
          throw "gen-program.declaration: `when` and `pos`/`neg` are two writings of one body; write one"
        else
          lowerWhen when;
    in
    builtins.seq a (
      builtins.seq
        (
          identifier "declaration" "the head" head
          && identifiers "declaration" "pos" lowered.pos
          && identifiers "declaration" "neg" lowered.neg
          && (
            label == null
            || builtins.isString label
            || throw "gen-program.declaration: the label is a ${builtins.typeOf label}, expected an edge label (a string) or null"
          )
          && (
            promote == null
            || builtins.isString promote
            || throw "gen-program.declaration: promote is a ${builtins.typeOf promote}, expected a relation kind (a string) or null"
          )
          && (
            promote == null
            || label == null
            || throw "gen-program.declaration: '${head}' carries both a label and promote; an included head is an edge or a node, not both"
          )
          && (
            if promote == null then
              identifiers "declaration" "relata" relata
            else if !builtins.isAttrs relata then
              throw "gen-program.declaration: '${head}' is promoted, so its relata are a labelled tuple (an attrset label -> identifier), not a ${builtins.typeOf relata}"
            else if relata == { } then
              throw "gen-program.declaration: '${head}' is promoted with no relata; a relation with no relata is not a relation (ADR-0016)"
            else if relata ? identifier then
              throw "gen-program.declaration: '${head}' is promoted with a relatum labelled 'identifier', the label the mint reserves for the node's own identifier; label the relatum otherwise"
            else
              builtins.all (identifier "declaration" "a relatum of a promoted head") (builtins.attrValues relata)
          )
        )
        {
          inherit (lowered) pos neg;
          inherit
            head
            relata
            label
            promote
            ;
        }
    );

  # The published door (den-hoag-7gp66 P2, rules 1, 2 and 4; OQ14 (β)): `declaration { pos?; neg?;
  # label?; promote?; when?; } relata head`. The defaulted fields are one closed options set, first, and its
  # contract is published as data (`__contract`, read by `prelude.functionArgs`). `head` is the
  # subject — the fact the declaration asserts, as `scope.mkRule { … } head` takes its own — and
  # `relata`, the identifiers it is resolved against, is configuration before it.
  declaration =
    prelude.door
      {
        name = "gen-program.declaration";
        optional = declarationOptions;
      }
      (
        o: relata: head:
        declarationRecord (o // { inherit head relata; })
      );

  # One declaration's rule, from the declaration as data. The relata do not appear: they are
  # IDENTIFIERS resolved against the frozen set, and the rule's atoms are MEMBERSHIP FACTS.
  rule =
    d:
    let
      normalized = declarationRecord d;
    in
    scope.mkRule {
      inherit (normalized) pos neg;
    } normalized.head;

  # ── THE PROGRAM ──
  # It returns gen-scope's own value, UNCHANGED and UNWRAPPED. Under the gadget this had to be a
  # record — the minted atoms travelled beside the program so the reporting filter could subtract
  # them — and with no minted atoms there is nothing to carry, so the wrapper goes too. A program
  # is plain data by its own module's statement, so handing it back as itself re-exports no build
  # (ADR-0014) and puts no second shape in front of a consumer.
  # POSITIONAL (den-hoag-7gp66 P2, rule 4): `program frozen declarations`, as `unresolvedRelata`.
  program =
    frozen: declarations:
    let
      unresolved = unresolvedRelata frozen declarations;
    in
    if unresolved != [ ] then
      throw "gen-program: ${quoteAll unresolved} is not in the frozen set of relata that strictly earlier passes settled, so it does not resolve — a same-pass reference and a root relatum both reach this refusal by that one path, and neither is named as a cycle because a stratum's in-flight output is not nameable from inside it"
    else
      scope.mkProgram (map rule declarations);
in
{
  inherit
    rule
    program
    declaration
    declarationRecord
    unresolvedRelata
    ;
}
