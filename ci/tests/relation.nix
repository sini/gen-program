# THE RESOLVED RELATION CARRIES A THIRD VALUE EVERY CONSUMER HANDLES — the ruled arm.
#
# ADR-0020 gives the atom a named third value; den's include surface has TWO. The fork over what
# an undefined gate means on that surface was ruled: arm (a), the resolved relation ACQUIRES a
# third value every consumer handles, in the published shape of van Antwerpen et al. 2016 §4.1–4.2
# (the `T` / `P` / `U` flags) with van Antwerpen et al. 2018 §4.3 (delayed queries). The incumbent
# — v1's silent tombstone — is knowingly not taken.
#
# ★★ THE CONSTRUCTION'S CLAIM IS THAT A CONSUMER CANNOT GET A BARE BOOLEAN, and these cells are
# what make that a measurement rather than a description. There are exactly two states in which a
# yes/no answer is unsound, and in both of them the field REFUSES BY NAME instead of answering:
#
#   `U` — the atom has no two-valued verdict at all. Answering either way would be this library
#         deciding ADR-0020's third value on a consumer's behalf, silently.
#   `P` — the atom is not derived AND the relation is still growing. Growth across the pass
#         sequence is monotone in the positive direction, so `true` stays true; `false` does not
#         stay false, because a later pass may derive it. vA2018 §4.3 delays such a query rather
#         than answering it, and so does this.
#
# ★ THE REFUSAL IS A FIELD THAT THROWS, NOT AN ABSENT FIELD AND NOT A `null`. An absent field is a
# missing-attribute error naming nothing a consumer can act on; `null` is worse, because every
# `if r.included` in the world reads it as false — which is the silent collapse this fork was
# ruled to end.
{
  genProgram,
  prelude,
  ...
}:
let
  modelOf =
    complete:
    genProgram.model {
      program = genProgram.program {
        declarations = [
          {
            head = "settled:in";
            relata = [ ];
          }
          {
            head = "contested:x";
            neg = [ "contested:y" ];
            relata = [ ];
          }
          {
            head = "contested:y";
            neg = [ "contested:x" ];
            relata = [ ];
          }
          {
            head = "reader";
            pos = [ "settled:out" ];
            relata = [ ];
          }
        ];
        frozen = [ ];
      };
      interpretation = [ ];
      inherit complete;
    };

  closed = modelOf true;
  growing = modelOf false;

  answers = m: atom: (builtins.tryEval (m.resolve atom).included);
in
{
  flake.tests.relation = {
    # ── THE CLOSED RELATION: both answers are sound and both are given ──
    test-a-derived-membership-on-a-closed-relation-is-total-and-included = {
      expr = closed.resolve "settled:in";
      expected = {
        flag = "T";
        included = true;
      };
    };

    test-an-underived-membership-on-a-closed-relation-is-total-and-excluded = {
      expr = closed.resolve "settled:out";
      expected = {
        flag = "T";
        included = false;
      };
    };

    # ── THE THIRD VALUE ──
    test-a-contested-membership-carries-the-unknown-flag = {
      expr = (closed.resolve "contested:x").flag;
      expected = "U";
    };

    test-a-contested-membership-refuses-to-answer-included-either-way = {
      expr = (answers closed "contested:x").success;
      expected = false;
    };

    # THE CONTROL BESIDE IT: the same field, on the same record, ANSWERS for a settled atom.
    # Without this the cell above would pass against a record whose `included` never answers.
    test-control-the-same-field-answers-on-a-settled-atom-in-the-same-record = {
      expr = answers closed "settled:in";
      expected = {
        success = true;
        value = true;
      };
    };

    test-control-and-answers-negatively-on-an-underived-atom-in-the-same-record = {
      expr = answers closed "settled:out";
      expected = {
        success = true;
        value = false;
      };
    };

    # ── THE GROWING RELATION: the positive answer stands, the negative one is delayed ──
    test-a-derived-membership-on-a-growing-relation-is-partial-and-still-included = {
      expr = growing.resolve "settled:in";
      expected = {
        flag = "P";
        included = true;
      };
    };

    test-an-underived-membership-on-a-growing-relation-is-partial-and-delays = {
      expr = {
        flag = (growing.resolve "settled:out").flag;
        answered = (answers growing "settled:out").success;
      };
      expected = {
        flag = "P";
        answered = false;
      };
    };

    # ★ THE ARMING FOR THE WHOLE `P` HALF: the SAME atom on the SAME program answers when the
    # relation is closed and delays when it is growing. Without this pairing the delay cell would
    # be indistinguishable from a field that never answers.
    test-control-the-identical-atom-answers-when-the-relation-is-closed = {
      expr = {
        growing = (answers growing "settled:out").success;
        closed = (answers closed "settled:out").success;
      };
      expected = {
        growing = false;
        closed = true;
      };
    };

    # Undefined outranks incompleteness: a contested atom is `U` on a growing relation too, and
    # not `P`. The two are different questions and the flag says which one is being answered.
    test-a-contested-membership-is-unknown-rather-than-partial-on-a-growing-relation = {
      expr = (growing.resolve "contested:x").flag;
      expected = "U";
    };

    # ── THE VOCABULARY IS CLOSED, AND ITS GLOSSES CITE WHERE THE LETTERS COME FROM ──
    test-the-flag-vocabulary-is-the-published-three = {
      expr = genProgram.flagNames;
      expected = [
        "T"
        "P"
        "U"
      ];
    };

    test-every-flag-a-resolution-can-carry-is-a-member-of-that-vocabulary = {
      expr = prelude.all (a: prelude.elem (closed.resolve a).flag genProgram.flagNames) (
        closed.trueAtoms ++ closed.falseAtoms ++ closed.undefinedAtoms
      );
      expected = true;
    };

    test-each-flag-carries-a-gloss-and-the-primary-it-is-taken-from = {
      expr = prelude.all (
        n: genProgram.flags.${n} ? gloss && genProgram.flags.${n} ? source
      ) genProgram.flagNames;
      expected = true;
    };

    test-the-vocabulary-and-the-glosses-are-one-set = {
      expr = prelude.sort (a: b: a < b) (prelude.attrNames genProgram.flags);
      expected = prelude.sort (a: b: a < b) genProgram.flagNames;
    };

    # ── `complete` IS THE CALLER'S DECISION AND CANNOT BE DEFAULTED INTO ──
    # A defaulted `true` would silently claim the pass sequence had closed — the one claim this
    # record cannot make on its caller's behalf — and a defaulted `false` would withhold every
    # negative answer forever.
    test-completeness-is-a-required-argument-of-the-entry = {
      expr = builtins.functionArgs genProgram.model;
      expected = {
        complete = false;
        interpretation = false;
        program = false;
      };
    };

    # And it reaches the record, so a consumer can read which reading they are holding rather than
    # inferring it from a flag.
    test-the-record-says-which-reading-it-is = {
      expr = {
        inherit (closed) complete;
        growing = growing.complete;
      };
      expected = {
        complete = true;
        growing = false;
      };
    };
  };
}
