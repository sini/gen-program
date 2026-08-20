# THE TRANSLATION: one declaration becomes one rule, and a pass's declarations become one program.
#
# THEORY, AND THE TWO PRIMARIES DO NOT OVERLAP. A `rule` is `head :- p₁ … pₙ, not q₁ … not qₘ` and
# a `program` is a set of them — Van Gelder, Ross & Schlipf 1991, Definition 2.1 (a general logic
# program is a finite set of general rules), and Apt, Blair & Walker 1988 for the stratified
# fragment those rules fall into when no cycle carries a negative edge. Both terms resolve at BOTH
# archived primaries with live in-file controls, which is why they are the names published here;
# `stratum` resolves at ABW ONLY and `well-founded model` at VGRS ONLY, so neither is a name this
# file may use for a construct of its own (spec R§0.4, ADR-0011's per-primary rider).
#
# ★ NOTHING HERE IS A SEMANTICS. The rules are handed to gen-scope, which owns the model, the
# reduct, the least fixpoint and the alternating fixpoint. This file builds the argument.
#
# ── WHAT ONE DECLARATION BECOMES (spec R§2.4) ──
# `head` is the fact the declaration asserts. `pos` is its enabling membership together with the
# positive literals of its guard. `neg` is its negated literals. A declaration with neither body
# is a FACT — that is `mkRule`'s own base case, not an omission — and the Herbrand base is closed
# by construction, so an atom no rule can derive comes back FALSE from the model rather than
# absent from it.
#
# ★ ATOM GRANULARITY IS RULED, NOT CHOSEN (ADR-0020, spec R§2.3): an atom is ONE fact — one
# ⟨scope, member⟩ membership, one promotion — and never a relation symbol. Nothing here groups
# facts into a relation, because a translation that atomised per relation would contest a whole
# relation on one contested pair and would not be ADR-0020's semantics under ADR-0020's name.
#
# ★★ ATOM NAMES ARE THE CALLER'S, AND THAT IS THIS FILE'S HALF OF THE AGNOSTICISM LAW.
# `den-hoag-h2yp` law 2 forbids encoding topology or kind relationships. A program of strings and
# lists of strings removes ONE channel for that — no field carries a kind — and leaves the other
# wide open, because an atom scheme keyed `host:…→user:…` encodes the forbidden relationship just
# as effectively and the datatype cannot tell (spec R§1.7, which strikes round 1's claim that the
# representation discharged the law). So this file mints NO atom name from a scheme of its own:
# every atom in an authored position is a string the caller wrote, and the only names this library
# introduces are the reserved partners below, which name no kind and no relationship.
#
# ── THE PASS BOUNDARY, AND WHY IT NEEDS A CONSTRUCTION AT ALL ──
# `solve` takes ONE argument, a program, and a program is rules over atoms. So the only channel by
# which a prior pass's result enters the next pass's program is AS RULES: a fact encodes true and
# omission encodes false. UNDEFINED has no encoding, so a prior pass's contested atom would
# silently collapse to one of the two values the channel can carry — the vanishing defect at the
# one boundary this design adds (spec R§2.8d).
#
# THE CONSTRUCTION, over the current surface: for each atom `x` contested at the previous pass,
# two rules over one fresh atom — `x :- not x′` and `x′ :- not x`. That is a cycle through a
# negative edge over `{x, x′}`, which is precisely the shape ABW's stratified semantics leaves
# without a meaning (their Lemma 1: a program is stratified iff its dependency graph has no cycle
# containing a negative edge) and which the well-founded model gives UNDEFINED. So `x` comes back
# undefined, under its own name, on the far side of the boundary.
#
# ★ IT COMPOSES RATHER THAN PINS, and the difference is the whole point. Where the new pass
# independently derives `x` through a positive rule whose body holds, `x` becomes TRUE and the
# construction does not prevent it: it supplies undefinedness only in the ABSENCE of other
# information, which is what re-injecting a third value has to mean. A construction that pinned
# would be a fourth value wearing the third one's name.
#
# ★★ AND THAT SENTENCE IS DIRECTION-ASYMMETRIC, WHICH IS STATED HERE BECAUSE A READER WILL
# OTHERWISE TAKE IT FOR BOTH DIRECTIONS. It composes with a POSITIVE derivation and OVERRIDES a
# NEGATIVE one. An atom the next pass leaves underived would read FALSE from the total verdict
# function; carried, it reads UNDEFINED — the two rules give it a derivation it did not otherwise
# have. That is exactly what re-injecting the third value is FOR, so it is not a defect; but
# "composes rather than pins" is true only of the direction it names, and this file claims no
# more. ⇒ The asymmetry dissolves when the input-interpretation parameter replaces this
# construction (`den-hoag-1tu3`): a prior verdict arriving as an INTERPRETATION overrides nothing,
# because it is not a rule.
#
# ★★★ THE CONTRACT ON `carried` IS STATED AND NOT ENFORCED, AND SAYING SO IS THE POINT.
# `carried` is meant to be the atoms whose verdict at the previous pass was UNDEFINED. Nothing
# below checks that, and it cannot be checked here: the previous pass's model is not an argument
# to this construction. **A caller who carries an atom that was settled injects undefinedness
# SILENTLY, and it propagates to that atom's readers.** Measured on this library — `s.` and
# `r :- f`, where `f` is headed by no rule and so is settled FALSE:
#
#     carried = [ ]      ⇒  f = "false",     r = "false",     contested = 0
#     carried = [ "f" ]  ⇒  f = "undefined", r = "undefined", contested = 3
#
# ⇒ It is a PRECONDITION on the caller, and it is the one shape of vanishing-content this design
# does not close by construction. No enforcement is built, deliberately: the construct retires
# under the input-interpretation ruling (`den-hoag-1tu3`), where the hazard dissolves rather than
# being guarded — an interpretation carries each atom's verdict WITH it, so there is no way to
# assert undefinedness of an atom that did not have it.
#
# ★★ AND ITS LIMIT IS SEMANTIC, NOT COSMETIC, SO IT IS STATED HERE RATHER THAN LEFT TO BE
# DISCOVERED (spec R§4.10). Two atoms left undefined at the previous pass BECAUSE THEY WERE
# ANTI-CORRELATED — the `a :- not b` / `b :- not a` shape, whose two stable models are `{a}` and
# `{b}` and never both or neither — become INDEPENDENT under one partner each, so the re-encoded
# program admits combinations the original excluded. **The re-encoded program is NOT
# stable-model-equivalent to the one it stands in for.** What is preserved is the well-founded
# verdict ATOM BY ATOM, which is all this construction claims.
#
# ★★★ AND THE SAFETY ARGUMENT THAT MADE THIS ARM LOOK CHEAP DOES NOT HOLD. IT IS STATED HERE
# BECAUSE SHIPPING THE REFUTED VERSION WOULD BE THE DEFECT.
# The argument ran: partners only ADD stable models, SO a program with none does not acquire one,
# SO the coherence criterion still refuses what it would have refused. **The premise is true and
# the inference is not** — adding stable models to a program that had ZERO gives it more than
# zero. Measured on this library, over Van Gelder, Ross & Schlipf 1991's Example 5.3
# `P2 = p :- not p`, of which that paper says in as many words "Hence P2 has no stable model":
#
#     carried = [ ]      ⇒  adjudication.outcome = "refused"
#     carried = [ "p" ]  ⇒  adjudication.outcome = "admitted"
#
# because `p :- not p′` supplies a derivation for `p` that `p :- not p` alone never had, and `{p}`
# is then stable in the re-encoded program. `ci/tests/carry.nix` pins both readings side by side.
#
# ⇒ **WHAT THE ADJUDICATION IS A STATEMENT ABOUT: the program AS CONSTRUCTED, these rules
# included.** That is coherent — it is the program whose model is computed and whose verdicts are
# reported, and no other program is in play at this pass. What a reader must NOT do is read
# `admitted` as a statement about the same declarations WITHOUT the carry. **The refusal direction
# is not preserved across the re-encoding, and this file no longer claims it is.**
#
# ⇒ It is a measured argument for the alternative: `solve` growing a three-valued
# input-interpretation parameter, so a prior pass's verdicts enter as an INTERPRETATION rather than
# as rules and no re-encoding happens at all. That is a new requirement on gen-scope, and it is
# promoted rather than taken here.
#
# ── THE FROZEN SET, AND WHY THE REFUSAL NAMES AN IDENTIFIER RATHER THAN A CYCLE ──
# ADR-0016 ruling 7 with ADR-0033 clause 1: a pass resolves relata against what STRICTLY EARLIER
# passes settled, so a later pass's program is built over closed input and no pass reads its own
# in-flight output. ★ That is a CONSTRUCTION, not a theorem — ABW's theorem is about a stratified
# program and a pass here carries negative cycles by premise, so the pass sequence is not an
# instance of their iteration and this file claims none (spec R§2.8b, R§4.9).
#
# ★★ THE REFUSAL THAT FIRES IS THE UNRESOLVED-RELATUM ONE, AND NOT A CYCLE DETECTOR. ADR-0033:
# "a same-pass reference CANNOT BE NAMED … there is no cycle check to run, because a stratum's
# in-flight output is not nameable from inside it." A refusal naming a cycle would be a detector
# for something inexpressible. What IS named is the identifier: resolution is identifier→identity
# against the frozen set, a same-pass identifier is simply not in that set, and a ROOT relatum
# refuses by the identical path because nothing earlier minted it either.
{ prelude, scope }:
let
  reserved = import ./reserved.nix { inherit prelude; };
  inherit (reserved) isReserved partnerOf reservedPrefix;

  quoteAll = names: prelude.concatMapStringsSep ", " (n: "'${n}'") names;

  # ── THE REFUSALS' CONTENT, PUBLISHED AS DATA ──
  # Each refusal below throws, and `tryEval` discards a message. A suite that could only assert
  # THAT something refused would be equally satisfied by a construction with one refusal in it, so
  # the CONTENT of each refusal is computed by a function a caller can call and a cell can assert.
  # The throw renders what these return; it does not re-derive it.

  # Every atom in an AUTHORED position that trespasses on the reserved namespace, in first
  # occurrence order. Authored positions are the three rule fields and the carried set — a carried
  # atom was authored at the pass that produced it.
  reservedCollisions =
    { declarations, carried }:
    prelude.unique (
      prelude.filter isReserved (
        prelude.concatMap (d: [ d.head ] ++ d.pos ++ d.neg) (map declaration declarations) ++ carried
      )
    );

  # Every relatum no strictly-earlier pass settled, in first-occurrence order. This is the
  # same-pass reference's path and the root relatum's path, and they are one path rather than two
  # — which is what makes the refusal the frozen-set mechanism rather than a special case.
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
  # the evaluator itself and a missing one is refused the same way. `pos` and `neg` default
  # because ADR-0020's own base case says a declaration with neither body is a fact; `relata` does
  # NOT, because a defaulted empty relatum list is a decision nobody made and nobody can see — it
  # would silently assert "this declaration relates nothing" and skip the frozen-set check for
  # exactly the declarations that forgot to state it.
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
  # frozen set, and the rule's atoms are MEMBERSHIP FACTS. Two universes, and collapsing them
  # would make an identifier derivable.
  rule =
    d:
    let
      normalized = declaration d;
    in
    scope.mkRule {
      inherit (normalized) head pos neg;
    };

  # The two rules that carry one contested atom across the boundary.
  carriedRules = atom: [
    (scope.mkRule {
      head = atom;
      neg = [ (partnerOf atom) ];
    })
    (scope.mkRule {
      head = partnerOf atom;
      neg = [ atom ];
    })
  ];

  program =
    {
      declarations,
      frozen,
      carried,
    }:
    let
      normalized = map declaration declarations;

      trespassers = reservedCollisions { inherit declarations carried; };
      unresolved = unresolvedRelata { inherit declarations frozen; };

      # Authored atoms: everything the declarations mention, plus the carried set, in
      # first-occurrence order. The carried atoms were authored at the pass that contested them.
      authored = prelude.unique (
        map (r: r.head) normalized ++ prelude.concatMap (r: r.pos ++ r.neg) normalized ++ carried
      );
      # The partners, one per carried atom. Disjoint from `authored` because the prefix is refused
      # there, and injective because `partnerOf` is a prefix of a distinct string.
      partners = map partnerOf carried;

      # Declaration order first, then the boundary construction: an authored atom's position in
      # the Herbrand base is where it was written, which is the order the ordered fold over
      # contributions is defined against.
      built = scope.mkProgram {
        rules = map rule declarations ++ prelude.concatMap carriedRules carried;
      };
    in
    if trespassers != [ ] then
      throw "gen-program: ${quoteAll trespassers} occupies the namespace this library reserves for the atoms it introduces at a pass boundary ('${reservedPrefix}…'), and an authored atom carrying it is refused rather than allowed to collide with one"
    else if unresolved != [ ] then
      throw "gen-program: ${quoteAll unresolved} is not in the frozen set of relata that strictly earlier passes settled (ADR-0016 ruling 7), so it does not resolve — a same-pass reference and a root relatum both reach this refusal by that one path, and neither is named as a cycle because a stratum's in-flight output is not nameable from inside it (ADR-0033)"
    else
      {
        # gen-scope's own value, UNCHANGED and carried as a field. It is plain data — strings and
        # lists of strings — so it crosses an evaluation boundary as itself, and re-shaping it here
        # would put a second program shape in front of a consumer for no gain (ADR-0014, spec
        # R§2.2).
        program = built;
        inherit authored;
        # The atoms THIS LIBRARY introduced, carried beside the program rather than re-derived by
        # whoever needs them: a second derivation is a second place the decision lives, and two of
        # them agree only for as long as someone keeps them in step.
        reserved = partners;
      };
in
{
  inherit
    rule
    program
    declaration
    unresolvedRelata
    reservedCollisions
    ;
}
