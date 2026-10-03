# THE CALL, AND THE RESULT RECORD THAT CANNOT BE BUILT WITHOUT SAYING WHAT IT WAS ADJUDICATED BY.
#
# This file drives `engine.solve` and assembles what comes back into the record a consumer reads.
# It computes no semantics: the model is gen-scope's, the partition behind the provenance stamp is
# gen-graph's through gen-scope's door, and the coherence criterion is the module next door.
#
# ★ IT DRIVES RATHER THAN MERELY CONSTRUCTS, AND THAT IS THE RULED ACCEPTANCE. ADR-0022's recorded
# exit is armed by benchmark acceptance failure; with nothing turning a policy into a program and
# reaching the solve, the benchmark never runs and that exit can never fire. A pure constructor
# with no caller would rebuild the wiring gap one layer up — which is the finding this whole
# commission exists to close.
#
# ── EACH PASS IS SOLVED FROM SCRATCH; NO VERDICT CROSSES A PASS BOUNDARY (den-hoag-ea3j4, arm (ii)) ──
# `solve` takes `{ program, interpretation }`. The interpretation is a LIST of `{ atom, verdict }`
# the caller ASSERTS at this pass — an input of this pass alone, restated at a later pass if it is
# to hold there. It carries NO default here for the same reason it carries none there: a defaulted
# empty list is the silent collapse the parameter exists to prevent, so a caller asserting nothing
# supplies `[ ]` and says so. A prior pass's verdicts are never carried: every pass solves its whole
# cumulative program, so a carried verdict is either redundant or — for an atom a later rule
# settles — a pin that makes the answer depend on where the pass boundary fell (ADR-0022).
#
# ★★ WHAT THIS REPLACED, BECAUSE THE DELETION IS THE HEADLINE. The boundary used to be a two-rule
# gadget per contested atom, and the gadget's fresh atoms had to be SUBTRACTED from every verdict
# list this record reports. That subtraction was *itself a place content could vanish*, which is
# why it was armed with a leak control rather than trusted. **With no library-introduced atoms
# there is nothing to subtract**, the filter is deleted rather than fixed, and the leak control
# loses its subject rather than passing. By construction, not repair.
#
# ★ AND THE ENUMERATIONS COME BACK FROM THE ENGINE UNTOUCHED. gen-scope reports over
# `program.atoms ∪ dom(interpretation)` — program atoms first in declaration order, then carried
# atoms not already present. This file does not re-order, re-filter or re-derive them; a second
# derivation is a second place the decision lives.
{
  prelude,
  scope,
  stableModel,
}:
let
  sortUnique = xs: builtins.sort (a: b: a < b) (prelude.unique xs);

  # ── THE CANONICAL RULE, AND ITS KEY ──
  # A body is a conjunction, a SET of literals under the well-founded semantics, so each body is
  # sorted and deduplicated: `a :- y, x` and `a :- x, x, y` are the rule `a :- x, y`. The key is the
  # JSON rendering of the canonical rule. It reads `head`, `pos` and `neg` only, so a rule and the
  # declaration it came from key alike — which is what lets `ruleEdges` ask whether a declaration is a
  # rule of a given model by the same index the `prior` omission guard reads, and not by a second
  # derivation of it.
  canonicalRule = r: {
    inherit (r) head;
    pos = sortUnique r.pos;
    neg = sortUnique r.neg;
  };
  ruleKey = r: builtins.toJSON (canonicalRule r);

  # ── THE FLAGS, AND THEY ARE VAN ANTWERPEN'S, CITED AT THEIR OWN PRIMARY ──
  # van Antwerpen et al. 2016 §4.1 puts a flag on a resolution result and gives it three values,
  # verbatim from the archived transcription: "a result flag, **T (total)** if all declarations
  # visible from S can be computed or **P (partial)** if there are still possible additional
  # resolutions (some scope variables are accessible)" (file lines 1723, 1728), and the resolution
  # function "returns either a set of declarations or **U (unknown)** if the reference cannot be
  # resolved in the current graph" (lines 1716–1717).
  #
  # ★★ THE LETTERS ARE KEPT RATHER THAN SPELLED, AND THAT IS A TRANSPLANT GUARD AND NOT A STYLE
  # CHOICE. This library cites TWO primaries that both use the words `total` and `partial`, for
  # DIFFERENT things: Van Gelder, Ross & Schlipf 1991 Definition 2.6 makes a model total when it
  # is two-valued over the whole Herbrand base, while van Antwerpen's T is about whether an answer
  # SET is complete. A field named `total` here would read as one and mean the other — which is
  # exactly the substitution this design keeps refusing. So van Antwerpen's flags travel as his
  # own letters with the gloss carried as data beside them, and the model's own totality is never
  # called anything but what VGRS calls it.
  flagNames = [
    "T"
    "P"
    "U"
  ];

  flags = {
    T = {
      gloss = "total — the answer is final: the atom's verdict is two-valued and the relation this reading is taken from is closed";
      source = "van Antwerpen et al. 2016, §4.1";
    };
    P = {
      gloss = "partial — the RELATION is still growing: later passes may add memberships this reading does not carry. A positive answer is given only for an atom whose whole support is negation-free, which no later pass can retract; every other two-valued answer is withheld until the relation is closed";
      source = "van Antwerpen et al. 2016, §4.1–4.2";
    };
    U = {
      gloss = "unknown — the atom has no two-valued verdict: ADR-0020's third value, reaching the surface under its own name";
      source = "van Antwerpen et al. 2016, §4.1; ADR-0020";
    };
  };

  # ── THE RESULT RECORD'S CONSTRUCTOR ──
  # `adjudication` STILL CARRIES NO DEFAULT. A construction that does not attach the field does not
  # construct: the door refuses the application by name, so there is no path on which a result
  # exists without the statement. That is O6's stated requirement. The refusal is a `throw`, so
  # `tryEval` contains it (ADR-0025 item 1); no result exists on either reading.
  #
  # ★ THE REQUIREDNESS IS READABLE IN-LANGUAGE, WHICH IS WHY THIS CONSTRUCTOR IS PUBLISHED.
  # The door publishes its contract as data (den-hoag-7gp66 P2, rule 1, OQ14 (β)): `__contract`,
  # and the map `prelude.functionArgs mkModel` reads, which marks each field required (`false`), so
  # a consumer — and a cell — can assert that `adjudication` is required rather than discovering it
  # from a crash (`ci/tests/adjudication.nix`). The four fields are configuration with no natural
  # order among them, so they stay ONE keyed record (rule 5; the keyed-record ruling, 2026-09-28),
  # OPEN under R5: a missing field is refused by name and CATCHABLY, at the application, and an
  # extra one is admitted. The native formal it replaces refused a missing one uncatchably.
  #
  # ★★ `authored` IS GONE, AND IT DIED WITH THE FILTER RATHER THAN BEING TIDIED AWAY. Its only
  # consumer was the subtraction of the gadget's own atoms; with no minted atoms there is nothing
  # to distinguish an authored atom from any other, so the formal has no question left to answer.
  #
  # ★ `program` IS A FORMAL BECAUSE THE POSITIVE ANSWER'S SOUNDNESS IS A FACT ABOUT THE RULES, not
  # about the model: whether a derived atom's support is negation-free is read off the program, and
  # `solved` does not carry it.
  # The unchecked core, which `model` calls with a record it built itself.
  mkModelCore =
    {
      solved,
      program,
      adjudication,
      complete,
      ...
    }:
    (
      let
        # ── WHICH DERIVED ATOMS A GROWING RELATION MAY SERVE ──
        # The atoms derivable with no negative literal ANYWHERE in their support: gen-scope's own
        # least fixpoint over the negation-free rules alone. Both of its arms read only `pos`, so
        # dropping every rule with a `neg` leaves exactly the positive fragment, and an atom whose
        # support passes through such a rule at ANY depth is unreachable in it — transitively, not
        # by inspecting the atom's own rule body. The positive fragment is monotone, so no later
        # pass retracts what it derives; that, and not the frozen set (ADR-0016 ruling 7 freezes
        # IDENTIFIERS, never verdicts), is what makes a positive answer sound before the relation
        # closes. Nothing is seeded from the interpretation: a carried verdict's own support is not
        # visible to this pass, so it cannot license a positive serve.
        #
        # Demand-driven: forced only under `complete = false`, and only for a derived atom.
        negationFree =
          (scope.leastModel { } (scope.mkProgram (builtins.filter (r: r.neg == [ ]) program.rules))).derived;

        withheld = atom: !complete && solved.verdict atom == "true" && !(negationFree ? ${atom});

        withholding =
          atom:
          "gen-program: the membership '${atom}' is derived at this pass, but its support rests on negation and the relation is still growing (complete = false), so a later pass may still falsify it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";

        # ── THE RESOLVED RELATION, WITH THE THIRD VALUE EVERY CONSUMER HANDLES ──
        # Total on every string, and every answer carries its flag. There is no shape of this record
        # from which a consumer can take a bare boolean.
        #
        # ★ UNDER `P` ONLY A NEGATION-FREE POSITIVE ANSWER IS GIVEN, AND THAT IS van Antwerpen 2018
        # §4.3's DISCIPLINE RATHER THAN CAUTION. vA2018's own statement of the problem: "Invoking the
        # resolution algorithm on an intermediate, incomplete graph may yield a different result
        # than invoking it on the final graph. This is potentially unsound" (archived
        # transcription, file lines 1861–1863); its answer is that "resolution is aborted, and the
        # query constraint delayed" (lines 1925–1926 — the quote is split across the two). Two
        # answers are unsound before the relation closes, and both are delayed by NAME:
        # `included = false` for an atom no pass has yet derived (a later pass may derive it), and
        # `included = true` for a derived atom whose support rests on `not q` at any depth (a later
        # pass may derive `q`). van Antwerpen et al. 2016's Lemma 2 is what licenses serving the
        # remaining one — a derived atom with negation-free support — while the graph still grows.
        #
        # ★ THE WITHHELD ANSWERS ARE FIELDS THAT REFUSE, NOT FIELDS THAT ARE ABSENT. An absent
        # field is a missing-attribute error naming nothing a consumer can act on, and `null` would
        # be worse — every `if r.included` in the world reads `null` as false, which is the silent
        # collapse this fork was ruled to end.
        resolve =
          atom:
          let
            v = solved.verdict atom;
          in
          if v == "undefined" then
            {
              flag = "U";
              included = throw "gen-program: the membership '${atom}' is UNDEFINED — the well-founded model's third truth value, neither true nor false, which this relation carries rather than collapsing. Read `flag` and handle 'U'; `included` has no answer to give here";
            }
          else if withheld atom then
            {
              flag = "P";
              included = throw (withholding atom);
            }
          else if v == "true" then
            {
              flag = if complete then "T" else "P";
              included = true;
            }
          else if complete then
            {
              flag = "T";
              included = false;
            }
          else
            {
              flag = "P";
              included = throw "gen-program: the membership '${atom}' is not derived at this pass, but the relation is still growing (complete = false), so a NEGATIVE answer is not yet sound — a later pass may derive it. van Antwerpen et al. 2018 §4.3 delays such a query rather than answering it; read `flag` and handle 'P'";
            };
      in
      {
        inherit resolve complete;

        # The rules this record was solved over, as plain data KEYED by the canonical rule's key
        # (`ruleKey` above) — an index, so a NEXT pass handed this record as its `prior` checks it
        # resubmitted every one by attribute lookup rather than a list scan per rule (quadratic at
        # thousands of rules). The same index is this record's side of that check. A resubmission
        # that writes `a :- y, x` for `a :- x, y`, or repeats a literal, is the same rule and is not
        # an omission. The value is the canonical rule too, so every key is the rendering of its
        # own value. gen-scope's program value itself is not carried: it holds more than the rules,
        # and not all of it crosses an evaluation boundary.
        rules = builtins.listToAttrs (
          map (r: {
            name = ruleKey r;
            value = canonicalRule r;
          }) program.rules
        );

        # gen-scope's own enumerations, over its own extended base, in its order. Nothing is
        # removed: a WITHHELD atom moves from `trueAtoms` to `withheldAtoms`, so the four lists
        # still partition the base and a withheld answer cannot be read back out of `trueAtoms`.
        # On a closed relation `withheldAtoms` is empty and `trueAtoms` is gen-scope's own.
        inherit (solved) undefinedAtoms falseAtoms;
        trueAtoms = builtins.filter (atom: !(withheld atom)) solved.trueAtoms;
        withheldAtoms = builtins.filter withheld solved.trueAtoms;

        # THE REQUIRED FIELD. It names ADR-0020's criterion, records the criterion's outcome on this
        # program, and names what decided it. It is plain data and crosses an evaluation boundary as
        # itself — never a `builtins.trace`, never a warn emission, because a channel a consumer can
        # drop is a channel on which silence reads as admission.
        inherit adjudication;

        # gen-scope's own, cited apart. `verdict` is TOTAL on a closed relation. On a growing one it
        # refuses a WITHHELD atom by the same name `resolve` does, and answers every other atom as
        # gen-scope does: a consumer reading `verdict` instead of `resolve` — and carrying that
        # forward — would otherwise route the served `P:in` around the withholding. The raw model
        # stays the adjudication's input, inside this library, and is not republished.
        verdict = atom: if withheld atom then throw (withholding atom) else solved.verdict atom;
        inherit (solved) converged;

        # The engine's stamp, carried as the engine emits it: empty inside the benchmark-verified
        # condensation depth and populated past it, which is what makes a stamped result say
        # something about the input that produced it. ★ Carried atoms contribute no edges, so the
        # stamp reads the same quantity it read before the parameter existed.
        inherit (solved) provenance condensationDepth;
      }
    );
  mkModel = prelude.door {
    name = "gen-program.mkModel";
    required = [
      "solved"
      "program"
      "adjudication"
      "complete"
    ];
    open = true;
  } mkModelCore;

  # ── THE ENTRY ──
  # `complete` carries NO DEFAULT. A defaulted `true` would silently claim the pass sequence had
  # closed, which is the one claim this record cannot make on its caller's behalf — and a defaulted
  # `false` would withhold every negative answer forever. `interpretation` carries none either, for
  # the reason gen-scope states at its own parameter. Absence is a decision, so the caller makes it.
  #
  # ── `prior` IS THE OMISSION GUARD, AND NOTHING ELSE (den-hoag-ea3j4, owner-ruled arms (B), (ii)) ──
  # A stepping caller hands this pass the previous pass's RECORD. No verdict of it is read: this
  # pass is solved from scratch over its own cumulative program, at its own `complete`, under its
  # own `interpretation`. What `prior` guards is the cumulation itself. A prior pass's verdicts are
  # not rules, so a program that drops an earlier pass's declaration re-derives nothing that
  # declaration settled, and reads the dropped atoms `false` by the closed-world default —
  # silently, and sometimes to the right answer for the wrong reason. Every rule of `prior.rules`
  # must be a rule of this program, or the entry refuses by name, catchably. Rules and not
  # declarations are compared: a declaration's relata are identifiers resolved against the frozen
  # set, and they are not part of the atom's meaning.
  #
  # ★ `prior` CARRIES NO DEFAULT. A defaulted `null` would silently skip the omission refusal for
  # every stepping caller who forgot it, which is the fallback this parameter exists to remove. A
  # first or single pass states `prior = null`, and that is the base case: nothing to have
  # resubmitted.
  #
  # ONE KEYED RECORD, OPEN (den-hoag-7gp66 P2, rule 5 and the keyed-record ruling, as `mkModel`
  # above): `program` is the subject, but `interpretation`, `complete` and `prior` are three
  # configuration operands with no natural order, so the four stay one record whose fields are
  # named at the call site. A missing field — `prior` above all, which has no default — is refused
  # by name and CATCHABLY at the application; the native formal it replaces aborted uncatchably
  # (den-hoag-ea3j4 landing gate Q4). An extra field is admitted (R5).
  model =
    prelude.door
      {
        name = "gen-program.model";
        required = [
          "program"
          "interpretation"
          "complete"
          "prior"
        ];
        open = true;
      }
      (
        {
          program,
          interpretation,
          complete,
          prior,
          ...
        }:
        (
          let
            priorKeys =
              if prior == null then
                [ ]
              else if builtins.isAttrs prior && builtins.isAttrs (prior.rules or null) then
                builtins.attrNames prior.rules
              else
                throw "gen-program.model: `prior` is not a gen-program result record — pass the previous pass's `model` result, or `prior = null` on the first pass";
            solved = scope.solve interpretation program;
            result = mkModelCore {
              inherit solved program complete;
              adjudication = stableModel.adjudicateCore {
                inherit program interpretation;
                model = solved;
              };
            };
            omitted = builtins.filter (k: !(result.rules ? ${k})) priorKeys;
          in
          if omitted != [ ] then
            throw "gen-program.model: this pass's program drops ${toString (builtins.length omitted)} rule(s) of the prior pass, headed ${
              builtins.concatStringsSep ", " (map (k: "'${prior.rules.${k}.head}'") omitted)
            } — every pass resubmits every earlier pass's declarations, because a prior pass's verdicts are not rules and a dropped declaration re-derives nothing it settled"
          else
            result
        )
      );
in
{
  inherit
    model
    mkModel
    flagNames
    flags
    ruleKey
    ;
}
