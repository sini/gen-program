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
# ★★ THE ORACLE QUANTIFIES OVER EVERY SERVED ANSWER AT EVERY PASS, not over the final one. The
# FINAL pass of N1/N2 is correct even in the defective library, so a "final answer matches
# from-scratch" oracle passes at that RED state and discriminates nothing.
# RED = an intermediate pass SERVES `included = true` for an atom the final graph, evaluated from
# scratch, answers `false`.
#
# ★ THE PASSES FOLLOW THE STEPPING CONSUMER'S CONTRACT (owner-ruled arms (B), (ii)): every later
# pass resubmits EVERY earlier pass's declarations plus its own and is handed the previous record as
# `prior`, which only guards that resubmission. No verdict crosses a pass boundary, so each pass is
# its cumulative program solved from scratch — and the FINAL pass must equal that from-scratch
# evaluation on every shape, including the ones a carried `undefined` used to pin (the second half
# of this suite, ported from reports/den-hoag-ea3j4-carry-arms-v0.md).
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
      prior = null;
      program = genProgram.program {
        inherit declarations;
        frozen = [ ];
      };
      inherit interpretation complete;
    };

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
      pass2 = withPrior final pass1 true;
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

  # ── THE PASS PROTOCOL: `prior` guards the cumulation; nothing is carried ──
  withPrior =
    declarations: prior: complete:
    genProgram.model {
      program = genProgram.program {
        inherit declarations;
        frozen = [ ];
      };
      interpretation = [ ];
      inherit prior complete;
    };

  bodyPass1 = withPrior [
    (d {
      head = "a";
      pos = [
        "x"
        "y"
      ];
      neg = [ "z" ];
    })
  ] null false;

  n1Final = [
    root
    (d {
      head = "member:a";
      pos = [ "member:root" ];
      neg = [ "member:b" ];
    })
    (d { head = "member:b"; })
  ];

  # One case's passes, stepped with `prior`, against the from-scratch evaluation of the final
  # cumulative program at the final pass's own `complete` and `interpretation`. A pass is
  # `{ add; complete; interp ? [ ]; }`; `serve` renders an answer as `flag:in|out|refused`.
  serve =
    m: atom:
    let
      r = m.resolve atom;
      t = builtins.tryEval r.included;
    in
    r.flag
    + ":"
    + (
      if !t.success then
        "refused"
      else if t.value then
        "in"
      else
        "out"
    );
  stepped =
    c:
    let
      progAt =
        k:
        genProgram.program {
          declarations = builtins.concatLists (prelude.genList (i: (builtins.elemAt c.passes i).add) (k + 1));
          frozen = [ ];
        };
      go =
        k: prior:
        let
          p = builtins.elemAt c.passes k;
          m = genProgram.model {
            program = progAt k;
            interpretation = p.interp or [ ];
            inherit (p) complete;
            inherit prior;
          };
        in
        if k + 1 == builtins.length c.passes then m else go (k + 1) m;
      last = builtins.length c.passes - 1;
      lastPass = builtins.elemAt c.passes last;
      final = go 0 null;
      scratch = genProgram.model {
        program = progAt last;
        interpretation = lastPass.interp or [ ];
        inherit (lastPass) complete;
        prior = null;
      };
      at = m: prelude.genAttrs c.watch (serve m);
    in
    {
      final = at final;
      agrees = at final == at scratch && view final == view scratch;
    };

  cyc = [
    (d {
      head = "p";
      neg = [ "q" ];
    })
    (d {
      head = "q";
      neg = [ "p" ];
    })
  ];
  U = atom: {
    inherit atom;
    verdict = "undefined";
  };
  # gen-inspect's fleet fixture (`examples/fleet/default.nix`), relata dropped: they are
  # identifiers resolved against the frozen set and no part of an atom's meaning.
  fleet = map d [
    {
      head = "enrolled:hemony:chiming";
    }
    {
      head = "absorbs:full-circle:chiming";
    }
    {
      head = "admits:bourdon:full-circle";
    }
    {
      head = "enrolled:hemony:full-circle";
      pos = [
        "enrolled:hemony:chiming"
        "absorbs:full-circle:chiming"
      ];
    }
    {
      head = "rings:hemony:bourdon";
      pos = [
        "enrolled:hemony:full-circle"
        "admits:bourdon:full-circle"
      ];
      neg = [ "silenced:hemony:bourdon" ];
    }
  ];

  cases = {
    # a negation cycle that a later pass settles
    C1 = {
      watch = [
        "p"
        "q"
      ];
      passes = [
        {
          add = cyc;
          complete = false;
        }
        {
          add = [ (d { head = "q"; }) ];
          complete = true;
        }
      ];
    };
    # three passes: a cycle, a dependant of it, then the settling fact
    CHAIN3 = {
      watch = [
        "p"
        "q"
        "r"
      ];
      passes = [
        {
          add = cyc;
          complete = false;
        }
        {
          add = [
            (d {
              head = "r";
              pos = [ "p" ];
            })
          ];
          complete = false;
        }
        {
          add = [ (d { head = "q"; }) ];
          complete = true;
        }
      ];
    };
    # asserted `undefined` at pass 1, then a later pass DECLARES it with a rule that cannot fire
    ASU_RULE_F = {
      watch = [
        "r"
        "e"
      ];
      passes = [
        {
          add = [
            (d {
              head = "r";
              pos = [ "e" ];
            })
          ];
          complete = false;
          interp = [ (U "e") ];
        }
        {
          add = [
            (d {
              head = "e";
              pos = [ "never" ];
            })
          ];
          complete = true;
        }
      ];
    };
    # a pure asserted-`undefined` atom, asserted at pass 1 only: it does not persist
    EXT = {
      watch = [
        "r"
        "e"
      ];
      passes = [
        {
          add = [
            (d {
              head = "r";
              pos = [ "e" ];
            })
          ];
          complete = false;
          interp = [ (U "e") ];
        }
        {
          add = [ ];
          complete = true;
        }
      ];
    };
    # the same assertion RESTATED at the final pass: that is how an assertion persists
    EXT_RESTATE = {
      watch = [
        "r"
        "e"
      ];
      passes = [
        {
          add = [
            (d {
              head = "r";
              pos = [ "e" ];
            })
          ];
          complete = false;
          interp = [ (U "e") ];
        }
        {
          add = [ ];
          complete = true;
          interp = [ (U "e") ];
        }
      ];
    };
    # three passes, an external `undefined` asserted once at pass 1 and never restated
    CHAIN3_EXT = {
      watch = [
        "r"
        "s"
        "e"
      ];
      passes = [
        {
          add = [
            (d {
              head = "r";
              pos = [ "e" ];
            })
          ];
          complete = false;
          interp = [ (U "e") ];
        }
        {
          add = [
            (d {
              head = "s";
              pos = [ "r" ];
            })
          ];
          complete = false;
        }
        {
          add = [ ];
          complete = true;
        }
      ];
    };
    # gen-inspect's fleet over three passes, the silencing asserted `undefined` at pass 1 only
    FLEET3 = {
      watch = [
        "rings:hemony:bourdon"
        "enrolled:hemony:full-circle"
      ];
      passes = [
        {
          add = prelude.genList (builtins.elemAt fleet) 3;
          complete = false;
          interp = [ (U "silenced:hemony:bourdon") ];
        }
        {
          add = [ (builtins.elemAt fleet 3) ];
          complete = false;
        }
        {
          add = [ (builtins.elemAt fleet 4) ];
          complete = true;
        }
      ];
    };
  };
  run = builtins.mapAttrs (_: stepped) cases;

  # an asserted `true` at a GROWING pass, and a reader of it (the gate's P1)
  asserted =
    complete:
    let
      m =
        modelOf
          [
            (d {
              head = "y";
              pos = [ "x" ];
            })
          ]
          [
            {
              atom = "x";
              verdict = "true";
            }
          ]
          complete;
    in
    {
      x = serve m "x";
      y = serve m "y";
    };

  view = m: {
    inherit (m)
      trueAtoms
      withheldAtoms
      undefinedAtoms
      falseAtoms
      ;
    outcome = m.adjudication.outcome;
  };

  refuses = v: !(builtins.tryEval v).success;
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

    # ══ NO VERDICT CROSSES A PASS: THE FINAL PASS EQUALS THE FINAL GRAPH FROM SCRATCH ══
    # Each case's final pass, stepped with `prior`, against the same cumulative program evaluated
    # with `prior = null` — served answers on the watched atoms and all four enumerations. The
    # literal finals beside `agrees` keep the cell from passing on two identically wrong readings.
    test-c1-a-cycle-a-later-pass-settles-is-settled-at-the-final-pass = {
      expr = run.C1;
      expected = {
        agrees = true;
        final = {
          p = "T:out";
          q = "T:in";
        };
      };
    };

    test-chain3-a-cycle-its-dependant-and-the-settling-fact-over-three-passes = {
      expr = run.CHAIN3;
      expected = {
        agrees = true;
        final = {
          p = "T:out";
          q = "T:in";
          r = "T:out";
        };
      };
    };

    test-asu-rule-f-a-declared-rule-settles-an-atom-asserted-undefined-earlier = {
      expr = run.ASU_RULE_F;
      expected = {
        agrees = true;
        final = {
          e = "T:out";
          r = "T:out";
        };
      };
    };

    # An ASSERTION is an input of the pass that states it: asserted at pass 1 only, it is absent
    # from the final pass, which reads `e` closed-world.
    test-ext-an-assertion-not-restated-does-not-persist = {
      expr = run.EXT;
      expected = {
        agrees = true;
        final = {
          e = "T:out";
          r = "T:out";
        };
      };
    };

    # ★ THE CONTROL: restated at the final pass, the same assertion holds there.
    test-control-ext-restated-the-assertion-holds = {
      expr = run.EXT_RESTATE;
      expected = {
        agrees = true;
        final = {
          e = "U:refused";
          r = "U:refused";
        };
      };
    };

    test-chain3-ext-an-assertion-made-once-does-not-reach-the-third-pass = {
      expr = run.CHAIN3_EXT;
      expected = {
        agrees = true;
        final = {
          e = "T:out";
          r = "T:out";
          s = "T:out";
        };
      };
    };

    test-fleet3-gen-inspects-fleet-over-three-passes = {
      expr = run.FLEET3;
      expected = {
        agrees = true;
        final = {
          "enrolled:hemony:full-circle" = "T:in";
          "rings:hemony:bourdon" = "T:in";
        };
      };
    };

    # ══ AN ASSERTED ATOM AT A GROWING PASS IS WITHHELD, AND SO ARE ITS READERS (the gate's P1) ══
    # An assertion is not a rule, so it never enters the negation-free fragment: at
    # `complete = false` an asserted `true` and every reader of it refuse under `P`; closed, both
    # answer. Conservative — latency, never an unsound answer.
    test-an-asserted-true-and-its-reader-are-withheld-while-growing-and-answer-when-closed = {
      expr = {
        growing = asserted false;
        closed = asserted true;
      };
      expected = {
        growing = {
          x = "P:refused";
          y = "P:refused";
        };
        closed = {
          x = "T:in";
          y = "T:in";
        };
      };
    };

    # ══ THE OMISSION GUARD'S INDEX IS AN ATTRSET KEYED BY RULE, NOT A LIST ══
    # The prior check looks each prior rule up in this index; a list scan per rule is quadratic, and
    # evaluator counters cannot see the difference (`builtins.elem` runs inside the builtin), so the
    # oracle is the index's STRUCTURE.
    test-the-record-rules-index-is-an-attrset-keyed-by-each-rules-json = {
      expr =
        let
          m = n1.scratch;
        in
        {
          isIndex = builtins.isAttrs m.rules;
          keyed = prelude.all (k: builtins.toJSON m.rules.${k} == k) (builtins.attrNames m.rules);
          count = builtins.length (builtins.attrNames m.rules);
        };
      expected = {
        isIndex = true;
        keyed = true;
        count = 3;
      };
    };

    # ══ AN OMITTED PRIOR DECLARATION IS REFUSED BY NAME, CATCHABLY ══
    # N2 delta-only: pass 2 submits only its new `z`, and every earlier rule is missing.
    test-a-delta-only-pass-is-refused = {
      expr = refuses (withPrior [ (d { head = "member:z"; }) ] n2.pass1 true);
      expected = true;
    };

    test-a-pass-dropping-one-prior-declaration-is-refused = {
      expr = refuses (
        withPrior [
          root
          (d { head = "member:b"; })
        ] n1.pass1 true
      );
      expected = true;
    };

    test-control-the-cumulative-pass-is-admitted = {
      expr = refuses (withPrior n1Final n1.pass1 true);
      expected = false;
    };

    # A body is a SET of literals, so the guard compares rules, not how their bodies are written:
    # pass 1 declares `a :- x, y, not z`, and a resubmission that reorders the body or repeats a
    # literal is the same rule and is admitted. The drop-one cell above is the refusing control.
    test-a-resubmitted-rule-with-its-body-reordered-is-admitted = {
      expr = refuses (
        withPrior [
          (d {
            head = "a";
            pos = [
              "y"
              "x"
            ];
            neg = [ "z" ];
          })
        ] bodyPass1 true
      );
      expected = false;
    };

    test-a-resubmitted-rule-with-a-body-literal-repeated-is-admitted = {
      expr = refuses (
        withPrior [
          (d {
            head = "a";
            pos = [
              "x"
              "y"
              "y"
            ];
            neg = [
              "z"
              "z"
            ];
          })
        ] bodyPass1 true
      );
      expected = false;
    };

    test-control-a-resubmitted-rule-with-a-body-literal-changed-is-refused = {
      expr = refuses (
        withPrior [
          (d {
            head = "a";
            pos = [ "x" ];
            neg = [ "z" ];
          })
        ] bodyPass1 true
      );
      expected = true;
    };

    test-a-prior-that-is-not-a-result-record-is-refused = {
      expr = refuses (withPrior n1Final { rules = [ ]; } true);
      expected = true;
    };

    # ★ THE WITHHOLDING REFUSAL IS CATCHABLE: `tryEval` contains it, on `included` and on `verdict`.
    test-the-withholding-refusal-is-caught-by-tryEval = {
      expr = {
        included = builtins.tryEval (n1.pass1.resolve "member:a").included;
        verdict = builtins.tryEval (n1.pass1.verdict "member:a");
      };
      expected = {
        included = {
          success = false;
          value = false;
        };
        verdict = {
          success = false;
          value = false;
        };
      };
    };
  };
}
