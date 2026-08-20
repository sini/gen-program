# THE CALL, AND THE RESULT RECORD THAT CANNOT BE BUILT WITHOUT SAYING WHAT IT WAS ADJUDICATED BY.
#
# This file drives `engine.solve` and assembles what comes back into the record a consumer reads.
# It computes no semantics: the model is gen-scope's, the partition behind the provenance stamp is
# gen-graph's through gen-scope's door, and the coherence criterion is the module next door.
#
# ★ IT DRIVES RATHER THAN MERELY CONSTRUCTS, AND THAT IS THE RULED ACCEPTANCE (spec R§4.7, R§1.6).
# ADR-0022's recorded exit is armed by benchmark acceptance failure; with nothing turning a policy
# into a program and reaching the solve, the benchmark never runs and that exit can never fire. A
# pure constructor with no caller would rebuild the wiring gap one layer up — which is the finding
# this whole commission exists to close.
#
# ── THE THIRD VALUE IS CARRIED OUT, NEVER COLLAPSED ──
# ADR-0020 rules contested atoms UNDEFINED — a named third value, never silence. `verdict` is
# gen-scope's own total function and it returns `"undefined"` under its own name; `undefinedAtoms`
# is the enumeration. Both reach this record. What the include surface then does with an undefined
# gate was the open fork, and it is RULED: arm (a), the resolved relation acquires a third value
# every consumer handles. `relation` below is that construction.
#
# ── WHAT IS SUBTRACTED FROM THE REPORTED LISTS, AND WHAT IS NOT ──
# The pass-boundary construction introduces reserved atoms (see `rules.nix`). They are REAL atoms:
# they enter the Herbrand base and would otherwise appear in every verdict list this record
# carries. So they are subtracted from the ENUMERATIONS.
#
# ★★ AND THE LIMIT OF THAT SUBTRACTION IS STATED HERE RATHER THAN LEFT TO BE ASSUMED, BECAUSE IT
# IS EASY TO OVERCLAIM (spec R§2.4). `verdict` is a TOTAL FUNCTION on every string. Filtering the
# reserved atoms out of the lists makes them UNREPORTED, never UNOBSERVABLE: a caller who invokes
# `verdict` on a reserved atom's name still receives an answer, and receives `"undefined"` rather
# than the `"false"` an unmentioned string would get. The subtraction hides them from ENUMERATION
# and that is the whole of the claim. What makes the collision impossible is the reserved
# namespace's REFUSAL, not this filter.
#
# ★ THE SUBTRACTION IS ITSELF A PLACE CONTENT CAN VANISH, which is why the suite arms it with a
# control that compares the reported lists against the AUTHORED atom set and shows a deliberately
# broken filter failing, rather than trusting the filter because it was written.
{
  prelude,
  scope,
  stableModel,
}:
let
  reserved = import ./reserved.nix { inherit prelude; };

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
  # A STRICT PATTERN WITH `adjudication` CARRYING NO DEFAULT, and that is the armed form of
  # R§2.14 rather than a sentence about what results should look like. A construction that does
  # not attach the field does not construct: the evaluator refuses the application by name, and
  # that refusal is UNCATCHABLE — `tryEval` does not contain it — so there is no path on which a
  # result exists without the statement.
  #
  # ★ THE REQUIREDNESS IS READABLE IN-LANGUAGE, WHICH IS WHY THIS CONSTRUCTOR IS PUBLISHED.
  # `builtins.functionArgs mkModel` reports each formal against whether it has a default, so a
  # consumer — and a cell — can assert that `adjudication` is required rather than discovering it
  # from a crash. The same reason gen-assemble publishes its substrate preconditions: a property a
  # consumer depends on should be readable, not inferable from a throw.
  #
  # ★ AND THE FIELD IS PRESENT ON EVERY RESULT, DELIBERATELY. It is a property of the LIBRARY, not
  # of the program, so gen-scope's rule about `provenance` — that a field always populated says
  # nothing about the input that produced it — does NOT transfer here. Two fields, two
  # disciplines: `provenance` means something BY being conditional; this one means something by
  # being unconditional, because what it reports is whether the ruled criterion was applied at all.
  # Reading the first's rule onto the second is the transplant defect at its smallest scale.
  mkModel =
    {
      solved,
      authored,
      adjudication,
      complete,
    }:
    let
      authoredSet = prelude.genAttrs authored (_: true);
      # The enumerations, with this library's own atoms subtracted. Order is preserved: the lists
      # arrive in the program's declaration order and a filter does not disturb it.
      onlyAuthored = prelude.filter (atom: authoredSet ? ${atom});

      trueAtoms = onlyAuthored solved.trueAtoms;
      undefinedAtoms = onlyAuthored solved.undefinedAtoms;
      falseAtoms = onlyAuthored solved.falseAtoms;

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
      # its answer is that "resolution is aborted, and the query constraint delayed" (line 1900).
      # So under `P` this record delays the negative answer by NAME rather than serving one that
      # a later pass can falsify.
      #
      # ★ THE WITHHELD ANSWERS ARE FIELDS THAT REFUSE, NOT FIELDS THAT ARE ABSENT. An absent
      # field is a missing-attribute error naming nothing a consumer can act on, and `null` would
      # be worse — every `if r.included` in the world reads `null` as false, which is the silent
      # collapse this fork was ruled to end. A field whose forcing is a named refusal is loud in
      # exactly the place a consumer would otherwise have decided the question without seeing it.
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
      inherit
        trueAtoms
        undefinedAtoms
        falseAtoms
        resolve
        complete
        ;

      # THE REQUIRED FIELD. It names ADR-0020's criterion, records the criterion's outcome on this
      # program, and names what decided it. It is plain data and crosses an evaluation boundary as
      # itself — never a `builtins.trace`, never a warn emission, because a channel a consumer can
      # drop is a channel on which silence reads as admission.
      inherit adjudication;

      # gen-scope's own, unchanged and cited apart. `verdict` is TOTAL and stays total: it answers
      # on a reserved atom too, which the enumerations above do not report. The two surfaces are
      # different and the difference is real.
      inherit (solved) verdict converged;

      # The engine's stamp, carried as the engine emits it: empty inside the benchmark-verified
      # condensation depth and populated past it, which is what makes a stamped result say
      # something about the input that produced it.
      inherit (solved) provenance condensationDepth;
    };

  # ── THE ENTRY ──
  # `complete` carries NO DEFAULT. A defaulted `true` would silently claim the pass sequence had
  # closed, which is the one claim this record cannot make on its caller's behalf — and a
  # defaulted `false` would withhold every negative answer forever. Absence is a decision, so the
  # caller makes it.
  model =
    { built, complete }:
    let
      solved = scope.solve built.program;
    in
    mkModel {
      inherit solved complete;
      inherit (built) authored;
      adjudication = stableModel.adjudicate {
        inherit (built) program;
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

  inherit (reserved) reservedPrefix isReserved;
}
