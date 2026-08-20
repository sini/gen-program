# THE SURFACE, held to an EXACT list, and bound to the document that publishes it.
#
# The list is exact rather than a count, so a new export lands as a failing cell with the author
# obliged to state it here, in `AGENTS.md` and in the README in the same change.
#
# ★ AND THE OBLIGATION TOWARDS `AGENTS.md` IS DISCHARGED BY CONSTRUCTION RATHER THAN BY DILIGENCE.
# A tripwire that holds the library to a list, while the document describing that list is bound to
# nothing, catches the library drifting from the list and never the document drifting from the
# library — so the sheet can go on publishing a surface the library stopped having, silently,
# which is the failure class this whole repository is built against. The sheet's drift-check block
# is JSON for that reason: it is ONE artefact, read by a reader and asserted here.
#
# ★ `policy` APPEARS IN NO NAME BELOW, AND THAT IS ASSERTED RATHER THAN LEFT TO REVIEW. The word
# is four-way overloaded — van Antwerpen's (E, <) carrier pair, a merge strategy shipping as six
# identifiers across four substrate libraries, Manchanda & Warren's view-update translation
# policy, and den's own rule surface — so a construct named for any of them is ambiguous at the
# point of use. The cell that checks it carries its own positive control, because an absence over
# a predicate that cannot match is not an absence.
{
  genProgram,
  prelude,
  scope,
  lib,
  ...
}:
let
  publishedSurface = [
    "adjudicate"
    "adjudicationOutcomes"
    "declaration"
    "flagNames"
    "flags"
    "isReserved"
    "mkModel"
    "model"
    "program"
    "reservedCollisions"
    "reservedPrefix"
    "rule"
    "stableModelBudget"
    "stableModelCriterion"
    "unresolvedRelata"
  ];

  agentsSheet = builtins.readFile ../../AGENTS.md;

  # The sheet's drift-check block: the output it publishes as the library's surface, taken FROM the
  # document rather than described from it.
  documentedSurface = builtins.fromJSON (
    lib.head (lib.splitString "```" (lib.elemAt (lib.splitString "```json" agentsSheet) 1))
  );

  mentions = name: lib.hasInfix "`${name}`" agentsSheet;

  lowered = s: lib.toLower s;
in
{
  flake.tests.surface = {
    test-lib-exports-exactly-the-published-surface = {
      expr = builtins.attrNames genProgram;
      expected = publishedSurface;
    };

    # ── THE SHEET AND THE LIBRARY, BOUND TOGETHER ──
    # Both halves are asserted against the same literal in one cell, so neither can drift onto the
    # other and neither side can pass by being empty.
    test-agents-md-publishes-the-exported-surface = {
      expr = {
        documented = documentedSurface;
        exported = builtins.attrNames genProgram;
      };
      expected = {
        documented = publishedSurface;
        exported = publishedSurface;
      };
    };

    test-agents-md-names-every-export-in-its-prose = {
      expr = prelude.filter (n: !(mentions n)) publishedSurface;
      expected = [ ];
    };

    test-control-the-mention-predicate-can-read-false = {
      expr = mentions "notAnExportOfThisLibrary";
      expected = false;
    };

    # ── THE NAMING RULING, MADE CHECKABLE ──
    test-no-published-identifier-carries-the-word-policy = {
      expr = prelude.filter (n: lib.hasInfix "polic" (lowered n)) publishedSurface;
      expected = [ ];
    };

    # CONTROL: the same predicate over the same shape of input, on a name that DOES carry it. An
    # absence over a predicate that cannot match is not an absence — and the substrate ships six
    # such identifiers, so this is the live shape and not an invented one.
    test-control-the-policy-predicate-matches-a-name-that-carries-it = {
      expr = prelude.filter (n: lib.hasInfix "polic" (lowered n)) [
        "mergePolicyNames"
        "rule"
      ];
      expected = [ "mergePolicyNames" ];
    };

    # ★ AND THE COLLISION IS A VOCABULARY FACT, NOT A DEPENDENCE ONE — measured live on the
    # substrate surface this library actually consumes, rather than quoted from a document.
    # gen-scope's only occurrences of the word are COMMENT PROSE describing a *consumer's*
    # attribute; it defines no construct under that name. (The merge-sense identifiers — six of
    # them — live in gen-bind and other substrate members, which this library neither pins nor
    # depends on, so asserting them HERE would be a claim about a neighbouring object.)
    test-the-consumed-substrate-surface-defines-no-policy-named-construct = {
      expr = prelude.filter (n: lib.hasInfix "polic" (lowered n)) (builtins.attrNames scope);
      expected = [ ];
    };

    # THE ARMING, over the SAME domain in the SAME run: one seeded name is enough to show the
    # sweep reaches the substrate's surface at all. An absence over a predicate that could not
    # match is not an absence.
    test-control-the-same-sweep-over-that-surface-finds-a-seeded-name = {
      expr = prelude.filter (n: lib.hasInfix "polic" (lowered n)) (
        builtins.attrNames scope ++ [ "mergePolicyNames" ]
      );
      expected = [ "mergePolicyNames" ];
    };

    # ── NO IDENTIFIER FOR THE ACT ──
    # `grounding` measures 0 occurrences across both paper corpora; the act of turning declarations
    # into ground rules has no term, so this library publishes none for it and names the RESULT
    # instead.
    test-no-published-identifier-names-the-act-of-translation = {
      expr = prelude.filter (
        n:
        prelude.any (verb: lib.hasInfix verb (lowered n)) [
          "ground"
          "translat"
          "compil"
          "encod"
          "convert"
        ]
      ) publishedSurface;
      expected = [ ];
    };

    test-control-the-act-predicate-matches-a-name-that-names-an-act = {
      expr =
        prelude.filter
          (
            n:
            prelude.any (verb: lib.hasInfix verb (lowered n)) [
              "ground"
              "translat"
              "compil"
              "encod"
              "convert"
            ]
          )
          [
            "groundProgram"
            "rule"
          ];
      expected = [ "groundProgram" ];
    };

    # ── THE TWO ENTRIES ARE ONE SURFACE ──
    # ★ The assertion is over the APPLIED surfaces, not over the entries themselves: both are
    # functions of the injected substrate, and two Nix lambdas are never equal — so `entry ==
    # entry` would read false on a correct library and could not distinguish drift from the
    # language. The applied form is also the stronger claim: it is the surface a consumer actually
    # receives.
    test-standalone-entry-matches-lib = {
      expr = builtins.attrNames (import ../.. { inherit prelude scope; });
      expected = publishedSurface;
    };

    # ── THIS LIBRARY RE-EXPORTS NONE OF THE SUBSTRATE ──
    # Re-exporting another library's value re-exports its build (ADR-0014). The program VALUE
    # crosses as a field of a construction result, which is plain data by its own module's
    # statement; no gen-scope construct is republished under a name here.
    test-no-export-is-a-gen-scope-export-under-another-name = {
      expr = prelude.filter (n: scope ? ${n}) publishedSurface;
      expected = [ ];
    };

    test-control-the-overlap-predicate-can-match = {
      expr = prelude.filter (n: scope ? ${n}) [
        "solve"
        "model"
      ];
      expected = [ "solve" ];
    };
  };
}
