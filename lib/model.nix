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
# ── THE PRIOR PASS ARRIVES AS AN INTERPRETATION, AND THAT IS THE WHOLE BOUNDARY NOW ──
# `solve` takes `{ program, interpretation }`. The interpretation is a LIST of `{ atom, verdict }`
# — a prior pass's verdicts, travelling as themselves. It carries NO default here for the same
# reason it carries none there: a defaulted empty carry is the silent collapse the parameter
# exists to prevent, and the first pass supplies `[ ]` and says so.
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
      gloss = "partial — the atom's verdict is two-valued and will not change, but the RELATION is still growing: later passes may add memberships this reading does not carry";
      source = "van Antwerpen et al. 2016, §4.1–4.2";
    };
    U = {
      gloss = "unknown — the atom has no two-valued verdict: ADR-0020's third value, reaching the surface under its own name";
      source = "van Antwerpen et al. 2016, §4.1; ADR-0020";
    };
  };

  # ── THE RESULT RECORD'S CONSTRUCTOR ──
  # A STRICT PATTERN WITH `adjudication` CARRYING NO DEFAULT. A construction that does not attach
  # the field does not construct: the evaluator refuses the application by name, and that refusal
  # is UNCATCHABLE — `tryEval` does not contain it — so there is no path on which a result exists
  # without the statement.
  #
  # ★ THE REQUIREDNESS IS READABLE IN-LANGUAGE, WHICH IS WHY THIS CONSTRUCTOR IS PUBLISHED.
  # `builtins.functionArgs mkModel` reports each formal against whether it has a default, so a
  # consumer — and a cell — can assert that `adjudication` is required rather than discovering it
  # from a crash.
  #
  # ★★ `authored` IS GONE, AND IT DIED WITH THE FILTER RATHER THAN BEING TIDIED AWAY. Its only
  # consumer was the subtraction of the gadget's own atoms; with no minted atoms there is nothing
  # to distinguish an authored atom from any other, so the formal has no question left to answer.
  mkModel =
    {
      solved,
      adjudication,
      complete,
    }:
    let
      # ── THE RESOLVED RELATION, WITH THE THIRD VALUE EVERY CONSUMER HANDLES ──
      # Total on every string, and every answer carries its flag. There is no shape of this record
      # from which a consumer can take a bare boolean.
      #
      # ★ THE NEGATIVE ANSWER IS WITHHELD UNDER `P`, AND THAT IS van Antwerpen 2018 §4.3's
      # DISCIPLINE RATHER THAN CAUTION. Growth across the pass sequence is monotone in the
      # positive direction — the frozen-set construction means no pass retracts an earlier pass's
      # derivation — so `included = true` is sound at any pass. `included = false` is NOT: an
      # atom no pass has yet derived reads false from a total verdict function, and a later pass
      # may derive it. vA2018's own statement of the problem: "Invoking the resolution algorithm
      # on an intermediate, incomplete graph may yield a different result than invoking it on the
      # final graph. This is potentially unsound" (archived transcription, file lines 1861–1863);
      # its answer is that "resolution is aborted, and the query constraint delayed" (lines
      # 1925–1926 — the quote is split across the two). So under `P` this record delays the
      # negative answer by NAME rather than serving one that a later pass can falsify.
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
            included = throw "gen-program: the membership '${atom}' is UNDEFINED — ADR-0020's third value, which this relation carries rather than collapsing. Read `flag` and handle 'U'; `included` has no answer to give here";
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

      # gen-scope's own enumerations, over its own extended base, unchanged. Nothing is filtered
      # here because nothing in them was put there by this library.
      inherit (solved) trueAtoms undefinedAtoms falseAtoms;

      # THE REQUIRED FIELD. It names ADR-0020's criterion, records the criterion's outcome on this
      # program, and names what decided it. It is plain data and crosses an evaluation boundary as
      # itself — never a `builtins.trace`, never a warn emission, because a channel a consumer can
      # drop is a channel on which silence reads as admission.
      inherit adjudication;

      # gen-scope's own, cited apart. `verdict` is TOTAL and stays total.
      inherit (solved) verdict converged;

      # The engine's stamp, carried as the engine emits it: empty inside the benchmark-verified
      # condensation depth and populated past it, which is what makes a stamped result say
      # something about the input that produced it. ★ Carried atoms contribute no edges, so the
      # stamp reads the same quantity it read before the parameter existed.
      inherit (solved) provenance condensationDepth;
    };

  # ── THE ENTRY ──
  # `complete` carries NO DEFAULT. A defaulted `true` would silently claim the pass sequence had
  # closed, which is the one claim this record cannot make on its caller's behalf — and a defaulted
  # `false` would withhold every negative answer forever. `interpretation` carries none either, for
  # the reason gen-scope states at its own parameter. Absence is a decision, so the caller makes it.
  model =
    {
      program,
      interpretation,
      complete,
    }:
    let
      solved = scope.solve { inherit program interpretation; };
    in
    mkModel {
      inherit solved complete;
      adjudication = stableModel.adjudicate {
        inherit program interpretation;
        model = solved;
      };
    };
in
{
  inherit
    model
    mkModel
    flagNames
    flags
    ;
}
