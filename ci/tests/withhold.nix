# A `P` ANSWER THAT RESTS ON NEGATION IS WITHHELD UNTIL THE RELATION IS CLOSED — the ruled arm (a).
#
# The multi-pass protocol used to serve `included = true` under `P` for any derived atom. That is
# sound for an atom whose support is negation-free: the positive fragment is monotone, so a later
# pass cannot retract it. It is NOT sound for an atom resting on `not q` for some `q` no pass has
# derived YET — a later pass derives `q`, and the served `P:in` becomes a falsified prior claim.
# Owner-ruled (den-hoag-ea3j4, arm (a)): a `P` verdict answers `included = true` only when the
# atom's WHOLE support chain is negation-free, transitively; anything else refuses by name until
# `complete = true`. van Antwerpen et al. 2016 Lemma 2 licenses the positive serve; vA2018 §4.3's
# prevention — delay the query until the graph is total — is the withholding, applied per atom.
#
# ★★ THE ORACLE QUANTIFIES OVER EVERY SERVED ANSWER AT EVERY PASS, not over the final one. Under
# the carry-undefined-only protocol the FINAL pass is correct even in the defective library, so a
# "final answer matches from-scratch" oracle passes at the RED state and discriminates nothing.
# RED = an intermediate pass SERVES `included = true` for an atom the final graph, evaluated from
# scratch, answers `false`.
#
# ★ THE PASSES FOLLOW THE STEPPING CONSUMER'S CONTRACT: every later pass resubmits EVERY earlier
# pass's declarations plus its own, and carries forward only the previous pass's `undefined` atoms.
# For N1/N2 that carry is EMPTY (an atom no rule heads is `false`, not `undefined`), so the final
# pass's correctness comes from the cumulative resubmission, not from the carry.
{
  genProgram,
  prelude,
  ...
}:
let
  d = r: r // { relata = [ ]; };

  modelOf =
    declarations: interpretation: complete:
    genProgram.model {
      program = genProgram.program {
        inherit declarations;
        frozen = [ ];
      };
      inherit interpretation complete;
    };

  undef = map (atom: {
    inherit atom;
    verdict = "undefined";
  });

  # One stepping consumer's two passes over a pass-1 declaration set and the declarations pass 2
  # adds, plus the from-scratch evaluation of the final graph that every served answer answers to.
  twoPass =
    first: added:
    let
      pass1 = modelOf first [ ] false;
      final = first ++ added;
    in
    {
      inherit pass1;
      pass2 = modelOf final (undef pass1.undefinedAtoms) true;
      scratch = modelOf final [ ] true;
    };

  # The corrected oracle's predicate: the atoms a pass SERVED `included = true` for, that the
  # from-scratch final graph answers `false`. A withheld answer is not a served one.
  contradictions =
    served: final:
    builtins.filter (
      atom:
      let
        s = builtins.tryEval (served.resolve atom).included;
        f = final.resolve atom;
      in
      s.success && s.value && f.flag == "T" && !f.included
    ) (final.trueAtoms ++ final.falseAtoms ++ final.undefinedAtoms);

  answered = m: atom: (builtins.tryEval (m.resolve atom).included).success;

  root = d { head = "member:root"; };

  # N1 — DIRECT negative support: `a :- root, not b`; pass 2 adds `b`.
  n1 =
    twoPass
      [
        root
        (d {
          head = "member:a";
          pos = [ "member:root" ];
          neg = [ "member:b" ];
        })
      ]
      [ (d { head = "member:b"; }) ];

  # N2 — TRANSITIVE negative support: `a :- y` carries no `not` of its own; `y :- root, not z` does.
  # A check reading only the atom's own rule body admits `a` here, and is wrong.
  n2 =
    twoPass
      [
        root
        (d {
          head = "member:y";
          pos = [ "member:root" ];
          neg = [ "member:z" ];
        })
        (d {
          head = "member:a";
          pos = [ "member:y" ];
        })
      ]
      [ (d { head = "member:z"; }) ];

  # PC — the POSITIVE control: `a :- root, c`, every link negation-free. Pass 2 adds an unrelated
  # fact, so the relation genuinely grows and `a` stays in.
  pc =
    twoPass
      [
        root
        (d { head = "member:c"; })
        (d {
          head = "member:a";
          pos = [
            "member:root"
            "member:c"
          ];
        })
      ]
      [ (d { head = "member:b"; }) ];

  # The negation cycle: ADR-0020's third value, which no amount of further graph settles.
  cycleAt =
    modelOf
      [
        (d {
          head = "member:p";
          neg = [ "member:q" ];
        })
        (d {
          head = "member:q";
          neg = [ "member:p" ];
        })
      ]
      [ ];

  sort = prelude.sort (a: b: a < b);
in
{
  flake.tests.withhold = {
    # ══ THE GATING ORACLE: NO SERVED ANSWER, AT ANY PASS, IS CONTRADICTED BY THE FINAL GRAPH ══
    test-n1-no-pass-1-answer-is-contradicted-by-the-final-graph = {
      expr = contradictions n1.pass1 n1.scratch;
      expected = [ ];
    };

    test-n2-no-pass-1-answer-is-contradicted-by-the-final-graph = {
      expr = contradictions n2.pass1 n2.scratch;
      expected = [ ];
    };

    test-pc-no-pass-1-answer-is-contradicted-by-the-final-graph = {
      expr = contradictions pc.pass1 pc.scratch;
      expected = [ ];
    };

    # ★ THE ORACLE'S SUBJECT IS REAL: the final graph answers `a` OUT on N1/N2, both carried and
    # from scratch. Without this the three cells above would pass against a fixture where `a` stays in.
    test-control-the-final-graph-answers-a-out-on-n1-and-n2-both-ways = {
      expr =
        map
          (c: {
            carried = c.pass2.resolve "member:a";
            scratch = c.scratch.resolve "member:a";
          })
          [
            n1
            n2
          ];
      expected =
        let
          out = {
            flag = "T";
            included = false;
          };
        in
        [
          {
            carried = out;
            scratch = out;
          }
          {
            carried = out;
            scratch = out;
          }
        ];
    };

    # ★ AND THE PREDICATE FIRES when a served answer IS contradicted: pass 1 of N1 read at
    # `complete = true` serves `a` in, and the same final graph answers it out.
    test-control-the-contradiction-predicate-fires-on-a-served-falsified-answer = {
      expr = contradictions (modelOf
        [
          root
          (d {
            head = "member:a";
            pos = [ "member:root" ];
            neg = [ "member:b" ];
          })
        ]
        [ ]
        true
      ) n1.scratch;
      expected = [ "member:a" ];
    };

    # ══ THE WITHHOLDING, CELL BY CELL ══
    test-n1-a-directly-negatively-supported-atom-is-withheld-at-pass-1 = {
      expr = {
        inherit ((n1.pass1.resolve "member:a")) flag;
        answered = answered n1.pass1 "member:a";
      };
      expected = {
        flag = "P";
        answered = false;
      };
    };

    test-n2-a-transitively-negatively-supported-atom-is-withheld-at-pass-1 = {
      expr = {
        inherit ((n2.pass1.resolve "member:a")) flag;
        answered = answered n2.pass1 "member:a";
      };
      expected = {
        flag = "P";
        answered = false;
      };
    };

    # The positive control, on the same record shape: a negation-free chain is served at pass 1.
    test-pc-a-negation-free-atom-is-served-in-at-pass-1-and-stays-in = {
      expr = {
        pass1 = pc.pass1.resolve "member:a";
        pass2 = pc.pass2.resolve "member:a";
      };
      expected = {
        pass1 = {
          flag = "P";
          included = true;
        };
        pass2 = {
          flag = "T";
          included = true;
        };
      };
    };

    # ★ AND ON THE N1/N2 RECORDS THEMSELVES the negation-free atom is still served: the withholding
    # is per atom, never per pass.
    test-control-the-negation-free-root-is-served-on-the-same-withholding-records = {
      expr = map (c: c.pass1.resolve "member:root") [
        n1
        n2
      ];
      expected = [
        {
          flag = "P";
          included = true;
        }
        {
          flag = "P";
          included = true;
        }
      ];
    };

    # ══ THE NEGATION CYCLE IS `U` AT EVERY COMPLETENESS, AND IS NOT THE WITHHELD `P` ══
    # Withheld pending totality (`P`) and undecidable regardless of totality (`U`) are different
    # answers; this cell keeps a change to the derived branch from collapsing them.
    test-a-negation-cycle-is-unknown-and-refuses-at-both-completeness-states = {
      expr =
        map
          (complete: {
            flag = ((cycleAt complete).resolve "member:p").flag;
            answered = answered (cycleAt complete) "member:p";
          })
          [
            false
            true
          ];
      expected = [
        {
          flag = "U";
          answered = false;
        }
        {
          flag = "U";
          answered = false;
        }
      ];
    };

    # ══ NO PUBLISHED READER LAUNDERS THE WITHHELD ANSWER ══
    # `verdict` and the enumerations are readers too. A consumer reading `verdict` instead of
    # `resolve` — and carrying THAT forward — would route the served `P:in` around the withholding.
    test-verdict-refuses-the-withheld-atom-rather-than-answering-true = {
      expr = map (c: (builtins.tryEval (c.pass1.verdict "member:a")).success) [
        n1
        n2
      ];
      expected = [
        false
        false
      ];
    };

    test-control-verdict-answers-a-negation-free-atom-on-a-growing-relation = {
      expr = pc.pass1.verdict "member:a";
      expected = "true";
    };

    test-the-withheld-atom-is-enumerated-as-withheld-and-not-as-true = {
      expr = map (c: { inherit (c.pass1) trueAtoms withheldAtoms; }) [
        n1
        n2
      ];
      expected = [
        {
          trueAtoms = [ "member:root" ];
          withheldAtoms = [ "member:a" ];
        }
        {
          trueAtoms = [ "member:root" ];
          withheldAtoms = [
            "member:y"
            "member:a"
          ];
        }
      ];
    };

    # ★ NOTHING VANISHES: the four enumerations partition the extended base on every record.
    test-the-four-enumerations-partition-the-base = {
      expr = map (m: sort (m.trueAtoms ++ m.withheldAtoms ++ m.undefinedAtoms ++ m.falseAtoms)) [
        n1.pass1
        n2.pass1
        pc.pass1
        n1.scratch
      ];
      expected = [
        (sort [
          "member:root"
          "member:a"
          "member:b"
        ])
        (sort [
          "member:root"
          "member:y"
          "member:a"
          "member:z"
        ])
        (sort [
          "member:root"
          "member:c"
          "member:a"
        ])
        (sort [
          "member:root"
          "member:a"
          "member:b"
        ])
      ];
    };

    # And a closed relation withholds nothing: `complete = true` is the totality the delay waits for.
    test-control-a-closed-relation-withholds-nothing = {
      expr = map (m: m.withheldAtoms) [
        n1.pass2
        n2.pass2
        n1.scratch
      ];
      expected = [
        [ ]
        [ ]
        [ ]
      ];
    };
  };
}
