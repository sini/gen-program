# ORACLES O6 AND O7 — the candidate-space argument, checked against an UNRESTRICTED enumerator.
#
# The adjudication walks `trueAtoms ∪ S` for `S ⊆ undefinedAtoms` of the INTERPRETED model, and
# calls that walk exhaustive. Two steps license it, and only the first is a published result:
#
#   1. THE CRITERION'S OBJECT IS `P′ = P ∪ facts(Pos(I))`, an ORDINARY general logic program — a
#      fact has no negative body, so it survives every reduct and `lfp T_{(P′)/M}` is exactly
#      `lfp_{⊇Pos(I)} T_{P/M}`. VGRS **Corollary 5.7** therefore applies to `P′` verbatim.
#   2. THE UNDEFINED EXEMPTION IS DEFLATIONARY. `S^U_T(X) ⊇ S_T(X)` and `S` is antitone, so the
#      interpreted TRUE set shrinks and the interpreted FALSE set shrinks — the interpreted model
#      commits to strictly LESS in BOTH directions. ⇒ the candidate space it induces CONTAINS the
#      one `P′` induces, so the walk is exhaustive over `P′`'s stable models *a fortiori*, at a
#      larger-space cost in the SAFE direction.
#
# **Step 2 is an argument written in the spec, not a theorem cited.** O6 checks the conclusion
# against an enumerator that applies NO restriction at all; O7 checks step 2 itself.
#
# ★★★ THE POPULATION IS THE CONTROL, AND ITS DEAD FORM IS DOCUMENTED FROM THIS INSTRUMENT'S OWN
# HISTORY. An earlier differential in this repository ran 120 randomly generated programs, found
# zero disagreements, and its seeded defect was INVISIBLE: every admitted program had a TOTAL
# well-founded model, so the search path never once ran on a program that HAS a stable model, and
# narrowing a space that contains nothing still contains nothing. **The tell is an identity:
# `admitted` == the count of programs with ZERO contested atoms.** It is asserted below.
#
# ★★ AND A THIRD CONDITION, WITHOUT WHICH THE SEEDING IS UNTESTED: at least one member must carry
# a TRUE atom AND an UNDEFINED atom TOGETHER. With `Pos(I) = ∅` throughout, `P′ = P`, the seeded
# stability predicate and an unseeded one agree on every member, and this whole suite passes
# against a build that never seeds.
#
# ★ THE ENUMERATOR IS TEST-ONLY AND IS BARRED FROM THE PRODUCTION PATH. It is a differential
# instrument; two production copies of a semantics agree only while someone keeps them in step.
{
  genProgram,
  prelude,
  scope,
  ...
}:
let
  d = r: r // { relata = [ ]; };
  carry = verdict: atoms: map (atom: { inherit atom verdict; }) atoms;
  undef = carry "undefined";
  true' = carry "true";

  programOf =
    declarations:
    genProgram.program {
      inherit declarations;
      frozen = [ ];
    };

  modelOf =
    { declarations, interpretation }:
    genProgram.model {
      program = programOf declarations;
      inherit interpretation;
      complete = true;
    };

  # `P′ = P ∪ facts(Pos(I))`, solved with the EMPTY interpretation. This is the ordinary program
  # the criterion is actually evaluated on, and the object O7 compares against.
  primeOf =
    { declarations, interpretation }:
    modelOf {
      declarations = declarations ++ map (a: d { head = a; }) (scope.Pos interpretation);
      interpretation = [ ];
    };

  pow2 = n: prelude.foldl' (a: _: a * 2) 1 (prelude.genList (i: i) n);

  # ── THE UNRESTRICTED ENUMERATOR ──
  # Every total interpretation over `H(P′)` tested for Gelfond–Lifschitz stability with the SEEDED
  # predicate. No Corollary 5.7 restriction, no candidate space — the full powerset.
  existsStable =
    { declarations, interpretation }:
    let
      p = programOf declarations;
      pos = scope.Pos interpretation;
      posSet = prelude.genAttrs pos (_: true);
      base = prelude.unique (p.atoms ++ pos);
      m = prelude.length base;
      powers = prelude.genList pow2 m;
      candidate =
        i:
        prelude.genAttrs (prelude.concatMap (
          j: prelude.optional (builtins.bitAnd i (prelude.elemAt powers j) != 0) (prelude.elemAt base j)
        ) (prelude.genList (j: j) m)) (_: true);
      stable =
        g:
        (scope.leastModel {
          program = scope.reduct p g;
          seed = posSet;
        }).derived == g;
    in
    prelude.any (i: stable (candidate i)) (prelude.genList (i: i) (pow2 m));

  # ── THE POPULATION, BUILT TO EXERCISE THE SEARCH RATHER THAN SAMPLED AND HOPED OVER ──
  # `k` anticorrelated pairs have a PARTIAL well-founded model and 2^k stable models, which is the
  # combination a random generator in this shape almost never produces.
  pairs =
    k:
    prelude.concatMap (i: [
      (d {
        head = "a${toString i}";
        neg = [ "b${toString i}" ];
      })
      (d {
        head = "b${toString i}";
        neg = [ "a${toString i}" ];
      })
    ]) (prelude.genList (i: i) k);
  # `p :- not p` — partial model, NO stable model.
  unstable = [
    (d {
      head = "p";
      neg = [ "p" ];
    })
  ];
  chain = [
    (d { head = "c0"; })
    (d {
      head = "c1";
      pos = [ "c0" ];
    })
  ];
  # A rule made derivable only by an EXTERNALLY TRUE atom — the shape that separates a seeded
  # stability predicate from an unseeded one.
  needsExternal = [
    (d {
      head = "n";
      pos = [ "ext" ];
    })
  ];

  population = [
    {
      declarations = pairs 1;
      interpretation = undef [ "w" ];
    }
    {
      declarations = pairs 2;
      interpretation = undef [ "w" ];
    }
    {
      declarations = pairs 1 ++ chain;
      interpretation = true' [ "c0" ] ++ undef [ "w" ];
    }
    {
      declarations = pairs 1 ++ unstable;
      interpretation = undef [ "w" ];
    }
    {
      declarations = unstable;
      interpretation = undef [ "p" ];
    }
    {
      declarations = unstable ++ pairs 1;
      interpretation = true' [ "p" ];
    }
    {
      declarations = needsExternal ++ pairs 1;
      interpretation = true' [ "ext" ] ++ undef [ "w" ];
    }
    {
      declarations = chain;
      interpretation = true' [ "x" ] ++ undef [ "y" ];
    }
    {
      declarations = pairs 2 ++ chain;
      interpretation =
        true' [ "c0" ]
        ++ undef [
          "w1"
          "w2"
        ];
    }
  ];

  rows = map (
    member:
    let
      m = modelOf member;
      a = m.adjudication;
    in
    {
      inherit member;
      outcome = a.outcome;
      contested = a.contested;
      libSaysExists = a.outcome == "admitted";
      brute = existsStable member;
      # `not-evaluated` is neither an agreement nor a disagreement: the criterion did not run.
      agrees = a.outcome == "not-evaluated" || (a.outcome == "admitted") == existsStable member;
    }
  ) population;

  admittedCount = prelude.length (prelude.filter (r: r.outcome == "admitted") rows);
  zeroContestedCount = prelude.length (prelude.filter (r: r.contested == 0) rows);

  # ── O7's SUBJECT: the deflation, POINTWISE over the common base ──
  # `WF_I(P)` ranges over `program.atoms ∪ dom(I)` and `WF(P′)` over `program.atoms ∪ Pos(I)`, so
  # comparing the two ENUMERATIONS compares lists over different domains and a correct build
  # falsifies it. `verdict` is total on every string, so a pointwise reading is well defined.
  deflationFailures =
    member:
    let
      mi = modelOf member;
      mp = primeOf member;
      base = prelude.unique (
        (programOf member.declarations).atoms ++ map (e: e.atom) member.interpretation
      );
    in
    prelude.filter (
      a:
      (mi.verdict a == "true" && mp.verdict a != "true")
      || (mi.verdict a == "false" && mp.verdict a != "false")
    ) base;

  # ★ O7's SEEDED DEFECT, IN THE FORM THIS REPOSITORY CAN BUILD. The spec's own seed is `U`
  # reaching the underestimate, which is a defect of gen-scope's construction and is armed in
  # `gen-scope/ci/tests/interpretation.nix` — gen-scope arrives here as a locked flake input, so a
  # defective engine is not constructible from this side. What IS constructible is the same defect
  # CLASS at this boundary: an INFLATED interpreted true set. It must break the first implication.
  inflatedFailures =
    member:
    let
      mi = modelOf member;
      mp = primeOf member;
      base = prelude.unique (
        (programOf member.declarations).atoms ++ map (e: e.atom) member.interpretation
      );
      # the inflation: everything the interpreted model left contested is claimed TRUE
      inflated = a: if prelude.elem a mi.undefinedAtoms then "true" else mi.verdict a;
    in
    prelude.filter (a: inflated a == "true" && mp.verdict a != "true") base;
in
{
  flake.tests.differential = {
    # ══ O6 — THE RESTRICTED SEARCH AGREES WITH AN UNRESTRICTED ENUMERATOR ══
    test-the-adjudication-agrees-with-a-full-powerset-enumerator = {
      expr = prelude.filter (r: !r.agrees) rows;
      expected = [ ];
    };

    # ★★ THE POPULATION IS LIVE, AND THIS IS THE CELL THAT SAYS SO. If the admitted count equalled
    # the zero-contested count, every admission would have come from the Corollary 5.6
    # short-circuit and the search path would never have run — which is exactly how an earlier
    # differential in this repository reported a vacuous zero.
    test-control-the-population-is-not-vacuous = {
      expr = {
        admitted = admittedCount;
        zeroContested = zeroContestedCount;
        differ = admittedCount != zeroContestedCount;
      };
      expected = {
        admitted = 7;
        zeroContested = 0;
        differ = true;
      };
    };

    # And the search genuinely ran on members that HAVE stable models — the case a dead population
    # never reaches.
    test-control-the-search-ran-on-members-that-have-stable-models = {
      expr = prelude.length (prelude.filter (r: r.brute && r.contested > 0) rows) >= 3;
      expected = true;
    };

    # ★★ THE THIRD CONDITION: a member carrying a TRUE atom AND an UNDEFINED atom together. With
    # `Pos(I) = ∅` throughout, the seeded predicate and an unseeded one agree on every member and
    # this suite passes against a build that never seeds.
    test-control-a-member-carries-true-and-undefined-together = {
      expr =
        prelude.length (
          prelude.filter (
            m:
            prelude.any (e: e.verdict == "true") m.interpretation
            && prelude.any (e: e.verdict == "undefined") m.interpretation
          ) population
        ) >= 3;
      expected = true;
    };

    # ★ THE SEEDED DEFECT: narrowing the candidate set to `S = ∅` — testing only `trueAtoms` — must
    # be CAUGHT, i.e. must disagree with the unrestricted enumerator somewhere.
    test-control-narrowing-the-candidate-set-to-nothing-is-caught = {
      expr =
        let
          narrowed =
            member:
            let
              p = programOf member.declarations;
              mi = modelOf member;
              posSet = prelude.genAttrs (scope.Pos member.interpretation) (_: true);
              trueSet = prelude.genAttrs mi.trueAtoms (_: true);
            in
            (scope.leastModel {
              program = scope.reduct p trueSet;
              seed = posSet;
            }).derived == trueSet;
          caught = prelude.filter (r: narrowed r.member != r.brute) rows;
        in
        prelude.length caught >= 1;
      expected = true;
    };

    # ══ O7 — THE DEFLATION CLAIM, MEASURED POINTWISE OVER THE COMMON BASE ══
    test-the-interpreted-model-commits-to-no-more-than-P-prime = {
      expr = prelude.concatMap deflationFailures population;
      expected = [ ];
    };

    # ★ THE SEEDED DEFECT: an INFLATED interpreted true set must break the first implication. This
    # is what shows the cell above is checking something rather than reading two identical models.
    test-control-an-inflated-true-set-breaks-the-first-implication = {
      expr = prelude.length (prelude.concatMap inflatedFailures population) >= 1;
      expected = true;
    };

    # ★ AND THE TWO MODELS ARE GENUINELY DIFFERENT OBJECTS ON SOME MEMBER — otherwise the
    # implications hold trivially because `P′ = P` everywhere and nothing was compared.
    test-control-P-prime-differs-from-the-interpreted-model-somewhere = {
      expr =
        prelude.length (
          prelude.filter (
            member:
            let
              mi = modelOf member;
              mp = primeOf member;
              base = prelude.unique (
                (programOf member.declarations).atoms ++ map (e: e.atom) member.interpretation
              );
            in
            prelude.any (a: mi.verdict a != mp.verdict a) base
          ) population
        ) >= 1;
      expected = true;
    };

    # ★ AT LEAST ONE MEMBER CARRIES AN UNDEFINED ATOM THE PROGRAM DOES NOT DERIVE, and at least one
    # carries one it DOES — without both, the implications are vacuous in one direction.
    test-control-the-population-carries-both-derived-and-underived-undefined-atoms = {
      expr =
        let
          hasUnderived = prelude.any (
            m:
            prelude.any (
              e: e.verdict == "undefined" && !(prelude.elem e.atom (programOf m.declarations).atoms)
            ) m.interpretation
          ) population;
          hasDerived = prelude.any (
            m:
            prelude.any (
              e: e.verdict == "undefined" && prelude.elem e.atom (programOf m.declarations).atoms
            ) m.interpretation
          ) population;
        in
        {
          inherit hasUnderived hasDerived;
        };
      expected = {
        hasUnderived = true;
        hasDerived = true;
      };
    };
  };
}
