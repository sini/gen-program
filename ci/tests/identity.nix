# ORACLE O5 — THE INTERPRETED ANALOGUE OF THEOREM 7.8: the two accounts define the SAME object.
#
# The design is stated twice, in two vocabularies, and they have to agree.
#
#   THE UNFOUNDED-SET ACCOUNT (VGRS 1991). A carried-UNDEFINED atom is one whose SUPPORT LIES
#   OUTSIDE THIS PROGRAM, and it enters by being EXEMPT FROM THE GREATEST UNFOUNDED SET. VGRS
#   Definition 3.1 makes `A ⊆ H` unfounded with respect to `I` when every rule with head `p ∈ A`
#   has a witness of unusability; VGRS Definition 3.3 puts the greatest such set into the
#   transformation as its negative half, `W_P(I) = T_P(I) ∪ ¬·U_P(I)`. An atom no rule heads
#   satisfies Definition 3.1 vacuously, so without the exemption it enters `U_P` and becomes FALSE.
#
#   THE ALTERNATING ACCOUNT (VG93, and what gen-scope computes). Two seeded operators, `U` reaching
#   the overestimate's fixpoint only.
#
# ★★★ WHY THIS IS AN OBLIGATION AND NOT A STYLISTIC MITIGATION. VG93 **Theorem 7.8** is an
# IDENTITY — "The alternating fixpoint model is IDENTICAL to the well-founded partial model" — with
# no slack to spend. But it applies to `A_P` for a PROGRAM `P`, and with `U ≠ ∅` the two seeded
# operators belong to two DIFFERENT augmented programs (`P ∪ facts(T ∪ U)` and `P ∪ facts(T)`),
# while the alternating transformation composes ONE program's operator with itself. **So the
# construction is `A_Q` for no `Q`, Theorem 7.8 does not reach it, and the interpreted analogue is
# CLAIMED AND NOT PROVED.** This oracle is what stands in for the proof.
#
# ⇒ **IF THIS SUITE FAILS ON ANY FIXTURE, THE SPEC'S CENTRAL CLAIM IS REFUTED.** That is a finding
# to report, not a bug to patch: the two accounts disagreeing means one of them is the wrong
# account of what the library computes.
#
# ★★ THE REFERENCE IMPLEMENTATION IS TEST-ONLY AND IS BARRED FROM THE PRODUCTION PATH. Two
# production copies of a semantics agree only for as long as someone keeps them in step, which is
# `least-model.nix`'s own stated reason for routing through one door. This one exists to DISAGREE
# when the shipped construction is wrong, which is the opposite job.
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

  shipped =
    declarations: interpretation:
    genProgram.model {
      program = programOf declarations;
      inherit interpretation;
      complete = true;
    };

  # ── THE REFERENCE: VGRS's `W_P`, WITH THE CARRIED-UNDEFINED ATOMS EXEMPT FROM `U_P` ──
  # A partial interpretation is carried as two disjoint sets, which is VGRS Definition 2.4's
  # "consistent set of literals" with the polarity split out so membership is a lookup.
  unfoundedSetModel =
    {
      declarations,
      interpretation,
    }:
    let
      p = programOf declarations;
      parsed =
        prelude.foldl'
          (
            acc: e:
            acc
            // {
              ${e.verdict} = acc.${e.verdict} ++ [ e.atom ];
            }
          )
          {
            "true" = [ ];
            "undefined" = [ ];
            "false" = [ ];
          }
          interpretation;
      exempt = prelude.genAttrs parsed."undefined" (_: true);
      seedTrue = prelude.genAttrs parsed."true" (_: true);

      base = p.atoms ++ prelude.filter (a: !(prelude.elem a p.atoms)) (map (e: e.atom) interpretation);
      rulesFor = atom: prelude.filter (r: r.head == atom) p.rules;

      # `T_P(I)`: the heads of rules whose body is entirely TRUE in `I`.
      immediate =
        I:
        prelude.genAttrs (prelude.concatMap (
          r: prelude.optional (prelude.all (q: I.t ? ${q}) r.pos && prelude.all (q: I.f ? ${q}) r.neg) r.head
        ) p.rules) (_: true);

      # `U_P(I)`: the GREATEST unfounded set, as a decreasing fixpoint. Start from every atom that
      # is not already true and not EXEMPT, and remove any atom that has a rule witnessing none of
      # VGRS Definition 3.1's conditions — no subgoal false in `I`, and no positive subgoal inside
      # the candidate set.
      greatestUnfounded =
        I:
        let
          start = prelude.genAttrs (prelude.filter (a: !(I.t ? ${a}) && !(exempt ? ${a})) base) (_: true);
          witnessed =
            A: atom:
            prelude.all (
              r:
              prelude.any (q: I.f ? ${q}) r.pos
              || prelude.any (q: I.t ? ${q}) r.neg
              || prelude.any (q: A ? ${q}) r.pos
            ) (rulesFor atom);
          shrink =
            acc:
            if acc.done then
              acc
            else
              let
                kept = prelude.genAttrs (prelude.filter (a: witnessed acc.A a) (prelude.attrNames acc.A)) (_: true);
              in
              {
                A = kept;
                done = prelude.length (prelude.attrNames kept) == prelude.length (prelude.attrNames acc.A);
              };
        in
        (prelude.iterateBounded scope.forceFields shrink {
          A = start;
          done = false;
        } (base ++ [ null ])).A;

      # `W_P` iterated from `{ t = Pos(I); f = ∅ }` to its least fixpoint.
      step =
        acc:
        if acc.done then
          acc
        else
          let
            I = {
              inherit (acc) t f;
            };
            t' = acc.t // immediate I;
            f' = acc.f // greatestUnfounded I;
          in
          {
            t = t';
            f = f';
            done = t' == acc.t && f' == acc.f;
          };
      final = prelude.iterateBounded scope.forceFields step {
        t = seedTrue;
        f = { };
        done = false;
      } (base ++ base ++ [ null ]);
    in
    {
      inherit base;
      verdict =
        atom:
        if final.t ? ${atom} then
          "true"
        else if final.f ? ${atom} then
          "false"
        else
          "undefined";
    };

  # The comparison is POINTWISE over the common base and never over the enumerations: the two
  # accounts produce lists that may be ordered differently, and `verdict` is total on every string
  # so a pointwise reading is well defined where a list comparison is not.
  agree =
    { declarations, interpretation }:
    let
      m = shipped declarations interpretation;
      r = unfoundedSetModel { inherit declarations interpretation; };
    in
    prelude.all (a: m.verdict a == r.verdict a) r.base;

  disagreementsOn =
    { declarations, interpretation }:
    let
      m = shipped declarations interpretation;
      r = unfoundedSetModel { inherit declarations interpretation; };
    in
    prelude.filter (a: m.verdict a != r.verdict a) r.base;

  # ── THE FIXTURES: the five hand-derived cases, plus the population shapes ──
  fixtures = [
    {
      declarations = [ ];
      interpretation = undef [ "x" ];
    }
    {
      declarations = [
        (d {
          head = "x";
          pos = [ "f" ];
        })
        (d { head = "f"; })
      ];
      interpretation = undef [ "x" ];
    }
    {
      declarations = [
        (d {
          head = "s";
          pos = [ "x" ];
        })
      ];
      interpretation = undef [ "x" ];
    }
    {
      declarations = [
        (d {
          head = "r";
          neg = [ "y" ];
        })
      ];
      interpretation = carry "false" [ "y" ];
    }
    {
      declarations = [
        (d {
          head = "p";
          neg = [ "p" ];
        })
      ];
      interpretation = undef [ "p" ];
    }
    # A member carrying a TRUE atom and an UNDEFINED atom TOGETHER — without one, `Pos(I) = ∅`
    # throughout and the seeding is never exercised.
    {
      declarations = [
        (d {
          head = "q";
          neg = [ "t" ];
        })
        (d {
          head = "s";
          pos = [ "u" ];
        })
      ];
      interpretation = true' [ "t" ] ++ undef [ "u" ];
    }
    # A negative cycle beside a settled bulk, with both carried kinds present.
    {
      declarations = [
        (d {
          head = "a";
          neg = [ "b" ];
        })
        (d {
          head = "b";
          neg = [ "a" ];
        })
        (d { head = "c"; })
        (d {
          head = "e";
          pos = [ "c" ];
        })
      ];
      interpretation = true' [ "c" ] ++ undef [ "w" ];
    }
    # THE `U = ∅` ARM: with no carried-undefined atom the two operators coincide, the construction
    # IS `A_P` over an ordinary program, and Theorem 7.8 applies exactly. This is the arm that
    # shows the reference implementation is not simply a copy of the shipped one.
    {
      declarations = [
        (d {
          head = "a";
          neg = [ "b" ];
        })
        (d {
          head = "b";
          neg = [ "a" ];
        })
        (d {
          head = "z";
          pos = [ "a" ];
        })
      ];
      interpretation = [ ];
    }
    {
      declarations = [
        (d {
          head = "n1";
          neg = [ "n0" ];
        })
        (d { head = "n0"; })
        (d {
          head = "n2";
          neg = [ "n1" ];
        })
      ];
      interpretation = [ ];
    }
  ];

  # ★ THE CONTROL: revision 1's construction — `U` unioned in AFTER the fixpoint rather than
  # seeding it — is a MEASURED disagreement between the two accounts, which is exactly what the
  # identity forbids. It is modelled here on the reference side by removing the EXEMPTION, which is
  # the unfounded-set account's own name for the same mistake: without the exemption a
  # carried-undefined atom no rule heads satisfies Definition 3.1 vacuously and becomes FALSE,
  # which is precisely the `s :- x` answer that rejected revision 1.
  unexemptedModel =
    { declarations, interpretation }:
    unfoundedSetModel {
      inherit declarations;
      interpretation = prelude.filter (e: e.verdict != "undefined") interpretation;
    };

  positiveReader = {
    declarations = [
      (d {
        head = "s";
        pos = [ "x" ];
      })
    ];
    interpretation = undef [ "x" ];
  };
in
{
  flake.tests.identity = {
    # ══ THE IDENTITY ══
    test-the-two-accounts-agree-on-every-fixture = {
      expr = map agree fixtures;
      expected = map (_: true) fixtures;
    };

    # And when they do not, the cell says WHERE — a boolean list would report a refutation of the
    # spec's central claim as a bare `false`.
    test-there-are-no-disagreeing-atoms-anywhere-in-the-population = {
      expr = prelude.concatMap disagreementsOn fixtures;
      expected = [ ];
    };

    # ★ THE `U = ∅` ARM, ASSERTED APART. Where the carried set has no undefined atom the identity
    # holds BY THEOREM 7.8 ITSELF, so this arm is what shows the reference implementation is a
    # second account rather than a mirror of the shipped one: if it were a copy, it would agree
    # here for the wrong reason and the population arm would be worthless.
    test-the-empty-undefined-arm-agrees-where-the-primary-settles-it = {
      expr = map agree (prelude.filter (f: f.interpretation == [ ]) fixtures);
      expected = [
        true
        true
      ];
    };

    # ══ THE CONTROL: A MEASURED DISAGREEMENT ══
    # The reference account with the EXEMPTION REMOVED is the unfounded-set spelling of revision
    # 1's defect, and it must break the identity ON THE POSITIVE-READER FIXTURE — the exact subject
    # that rejected revision 1. Without this arm, "the two agree" could be reporting that the
    # reference tracks the shipped construction rather than the paper.
    test-control-removing-the-exemption-breaks-the-identity-on-the-positive-reader = {
      expr =
        let
          m = shipped positiveReader.declarations positiveReader.interpretation;
          r = unexemptedModel positiveReader;
        in
        {
          shippedSays = m.verdict "s";
          unexemptedSays = r.verdict "s";
          agrees = m.verdict "s" == r.verdict "s";
        };
      expected = {
        shippedSays = "undefined";
        unexemptedSays = "false";
        agrees = false;
      };
    };

    # And the exemption is what carries the carried atom itself, not only its reader.
    test-control-the-carried-atom-goes-false-without-the-exemption = {
      expr = (unexemptedModel positiveReader).verdict "x";
      expected = "false";
    };

    # ★ THE POPULATION IS NOT DEGENERATE: at least one member carries a TRUE atom and an UNDEFINED
    # atom TOGETHER. With `Pos(I) = ∅` throughout, the seeding is never exercised and the whole
    # comparison passes against a build that never seeds.
    test-control-the-population-carries-true-and-undefined-together = {
      expr =
        prelude.length (
          prelude.filter (
            f:
            prelude.any (e: e.verdict == "true") f.interpretation
            && prelude.any (e: e.verdict == "undefined") f.interpretation
          ) fixtures
        ) >= 1;
      expected = true;
    };

    # And it contains a member whose model is genuinely PARTIAL, so the fixtures are not all
    # settled cases where any two accounts would agree.
    test-control-the-population-contains-a-partial-model = {
      expr = prelude.any (f: (shipped f.declarations f.interpretation).undefinedAtoms != [ ]) fixtures;
      expected = true;
    };
  };
}
