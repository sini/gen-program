# ORACLE O7 — UNDEFINED SURVIVES THE PASS BOUNDARY, AND THIS LIBRARY'S OWN ATOMS DO NOT LEAK.
#
# `engine.solve` takes ONE argument, a program, and a program is rules over atoms. So the only
# channel by which a prior pass's result enters the next pass's program is AS RULES: a fact
# encodes true and omission encodes false. UNDEFINED has no encoding at all, so without a
# construction a prior pass's contested atom silently collapses to one of the two values the
# channel can carry — the vanishing defect at the one boundary this design adds.
#
# ★★ THREE ARMS, AND TWO OF THEM GUARD THE TWO WAYS THIS CAN GO WRONG.
#   (i)   THE COLLAPSE CONTROL. With the construction suppressed, the same atom comes back TRUE or
#         FALSE. This is the defect the mechanism exists to prevent, and it must be DEMONSTRATED
#         to occur — otherwise the fixture never had a subject and the main cell passes against a
#         program that was never at risk.
#   (ii)  THE OVER-PINNING CONTROL. Where the next pass carries a positive rule deriving the atom
#         from a settled body, it comes back TRUE. The construction supplies undefinedness only in
#         the ABSENCE of other information; one that pinned would be a fourth value wearing the
#         third one's name.
#   (iii) THE LEAK CONTROL. The reported verdict lists are compared against the AUTHORED atom set,
#         and a deliberately broken filter is shown to fail the same comparison. The subtraction
#         is itself a place content can vanish, so it is armed rather than trusted.
#
# ★ SCOPED, PER THE SPEC, BECAUSE IT IS EASY TO OVERCLAIM: THIS MEASURES ENUMERATION, NOT
# OBSERVABILITY. `verdict` is a TOTAL function, so a reserved atom stays answerable by direct
# query and comes back `"undefined"` rather than the `"false"` an unmentioned string would get.
# The cells below assert exactly that, so the difference between the two surfaces is on the record
# rather than papered over. What makes a collision IMPOSSIBLE is the namespace's refusal, not this
# filter.
{
  genProgram,
  prelude,
  scope,
  ...
}:
let
  buildOf =
    { declarations, carried }:
    genProgram.program {
      inherit declarations carried;
      frozen = [ ];
    };

  modelOf =
    args:
    genProgram.model {
      built = buildOf args;
      complete = true;
    };

  # ── PASS N: the negative cycle leaves `a` and `b` contested ──
  passN = modelOf {
    declarations = [
      {
        head = "a";
        neg = [ "b" ];
        relata = [ ];
      }
      {
        head = "b";
        neg = [ "a" ];
        relata = [ ];
      }
    ];
    carried = [ ];
  };

  # ── PASS N+1: nothing here determines `a`; it is merely read ──
  nextDeclarations = [
    {
      head = "z";
      pos = [ "a" ];
      relata = [ ];
    }
  ];

  carriedForward = modelOf {
    declarations = nextDeclarations;
    carried = [ "a" ];
  };

  # ARM (i): the identical pass with the construction SUPPRESSED.
  suppressed = modelOf {
    declarations = nextDeclarations;
    carried = [ ];
  };

  # ARM (ii): the same carry, beside a positive rule that DOES determine `a`.
  determined = modelOf {
    declarations = nextDeclarations ++ [
      {
        head = "settled";
        relata = [ ];
      }
      {
        head = "a";
        pos = [ "settled" ];
        relata = [ ];
      }
    ];
    carried = [ "a" ];
  };

  # ARM (iii): the same result assembled with a BROKEN filter — the authored set widened to admit
  # this library's own atoms, which is what a filter that failed to subtract them would produce.
  carriedBuilt = buildOf {
    declarations = nextDeclarations;
    carried = [ "a" ];
  };
  brokenFilter = genProgram.mkModel {
    # The engine's own result, which is what the real entry hands the constructor. Everything
    # about this arm is the real path except the authored set.
    solved = scope.solve carriedBuilt.program;
    authored = carriedBuilt.authored ++ carriedBuilt.reserved;
    adjudication = carriedForward.adjudication;
    complete = true;
  };

  reservedPartner = genProgram.reservedPrefix + "a";

  reportedAtoms = m: m.trueAtoms ++ m.undefinedAtoms ++ m.falseAtoms;
in
{
  flake.tests.carry = {
    # ── THE SUBJECT EXISTS: pass N really left `a` contested ──
    test-control-the-prior-pass-leaves-the-atom-contested = {
      expr = passN.undefinedAtoms;
      expected = [
        "a"
        "b"
      ];
    };

    # ── (i) THE THIRD VALUE CROSSES THE BOUNDARY ──
    test-an-atom-undefined-at-the-prior-pass-is-undefined-at-the-next = {
      expr = carriedForward.verdict "a";
      expected = "undefined";
    };

    # And it propagates as a value rather than sitting inert: a rule whose body is undefined is
    # itself undefined, which is what "the third value every consumer handles" has to mean one
    # step downstream.
    test-a-rule-reading-the-carried-atom-is-undefined-too = {
      expr = carriedForward.undefinedAtoms;
      expected = [
        "z"
        "a"
      ];
    };

    # ── (i) THE COLLAPSE CONTROL: the defect, demonstrated ──
    test-control-with-the-construction-suppressed-the-atom-collapses-to-false = {
      expr = suppressed.verdict "a";
      expected = "false";
    };

    test-control-the-suppressed-arm-carries-no-third-value-at-all = {
      expr = suppressed.undefinedAtoms;
      expected = [ ];
    };

    # ── (ii) THE OVER-PINNING CONTROL ──
    test-control-a-positive-derivation-at-the-next-pass-settles-the-carried-atom = {
      expr = determined.verdict "a";
      expected = "true";
    };

    test-control-the-determined-arm-settles-its-reader-too = {
      expr = {
        inherit (determined) trueAtoms undefinedAtoms;
      };
      expected = {
        trueAtoms = [
          "z"
          "settled"
          "a"
        ];
        undefinedAtoms = [ ];
      };
    };

    # ── (iii) THE LEAK CONTROL ──
    test-no-atom-this-library-introduced-appears-in-any-reported-list = {
      expr = prelude.filter genProgram.isReserved (reportedAtoms carriedForward);
      expected = [ ];
    };

    # The subject of that cell exists: the construction DID introduce an atom, so the filter had
    # something to subtract. Without this, the cell above passes against a construction that never
    # ran.
    test-control-the-construction-really-did-introduce-an-atom = {
      expr = carriedBuilt.reserved;
      expected = [ reservedPartner ];
    };

    test-control-and-that-atom-is-in-the-programs-herbrand-base = {
      expr = prelude.elem reservedPartner carriedBuilt.program.atoms;
      expected = true;
    };

    # THE BROKEN FILTER FAILS THE SAME COMPARISON. Without this the leak cell would pass against a
    # comparison that could not detect a leak.
    test-control-a-broken-filter-does-leak-under-the-same-comparison = {
      expr = prelude.filter genProgram.isReserved (reportedAtoms brokenFilter);
      expected = [ reservedPartner ];
    };

    # ── THE SCOPE OF THE CLAIM ──
    # Hidden from ENUMERATION, reachable by QUERY. `verdict` is total and answers on the reserved
    # atom — and answers `"undefined"`, not the `"false"` an unmentioned string gets, which is the
    # real difference between the two surfaces.
    test-the-reserved-atom-is-unreported-but-still-answerable = {
      expr = {
        enumerated = prelude.elem reservedPartner (reportedAtoms carriedForward);
        queried = carriedForward.verdict reservedPartner;
        unmentioned = carriedForward.verdict "a-string-no-rule-mentions";
      };
      expected = {
        enumerated = false;
        queried = "undefined";
        unmentioned = "false";
      };
    };

    # ── COLLISION IS IMPOSSIBLE RATHER THAN UNLIKELY ──
    # An authored atom trespassing on the reserved namespace is refused at construction, so the
    # filter never has to distinguish an authored atom from one of this library's.
    test-an-authored-atom-in-the-reserved-namespace-is-refused = {
      expr =
        let
          trespass = buildOf {
            declarations = [
              {
                head = reservedPartner;
                relata = [ ];
              }
            ];
            carried = [ ];
          };
        in
        !(builtins.tryEval (builtins.deepSeq trespass.program trespass.program)).success;
      expected = true;
    };

    test-the-refusal-names-the-trespassing-atom = {
      expr = genProgram.reservedCollisions {
        declarations = [
          {
            head = reservedPartner;
            pos = [ ];
            neg = [ ];
            relata = [ ];
          }
        ];
        carried = [ ];
      };
      expected = [ reservedPartner ];
    };

    test-control-an-ordinary-atom-is-not-a-trespasser = {
      expr = genProgram.reservedCollisions {
        declarations = [
          {
            head = "a";
            pos = [ ];
            neg = [ ];
            relata = [ ];
          }
        ];
        carried = [ ];
      };
      expected = [ ];
    };
  };
}
