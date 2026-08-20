# ORACLE O4 — a same-pass reference FAILS TO RESOLVE, and the refusal that fires is the
# UNRESOLVED-RELATUM one.
#
# ★★ THE ORACLE IS RECAST FROM THE OBVIOUS ONE, AND THE RECASTING IS THE POINT. Asking for "a
# refusal naming the pass" would be asking for a detector for something ADR-0033 rules
# inexpressible: "a same-pass reference CANNOT BE NAMED … there is no cycle check to run, because
# a stratum's in-flight output is not nameable from inside it." What IS named is ADR-0016
# ruling 7's own path — resolution is identifier→identity against the frozen set of STRICTLY
# EARLIER passes, and a same-pass identifier is simply not in that set.
#
# ★★ THE SECOND WITNESS IS WHAT SHOWS IT IS ONE MECHANISM AND NOT A SPECIAL CASE. A ROOT relatum
# refuses through the identical path, because nothing earlier minted it either. If the two
# refused by different paths they would be two mechanisms, and the same-pass one would be a
# detector after all.
#
# ★ THE OVER-BROAD CONTROL IS THE OTHER HALF. A construction that refused every relatum would pass
# every refusal cell here and would be useless — and worse, it would read as a false red. The
# cross-pass form must construct and resolve in the same run.
{
  genProgram,
  ...
}:
let
  # What strictly earlier passes settled. `earlier:node` is in it; nothing else is.
  frozen = [ "earlier:node" ];

  build =
    relata:
    genProgram.program {
      declarations = [
        {
          head = "promotes:${builtins.head (relata ++ [ "nothing" ])}";
          inherit relata;
        }
      ];
      inherit frozen;
      carried = [ ];
    };

  refused = expr: !(builtins.tryEval (builtins.deepSeq expr expr)).success;

  # The three relata under test, all through the ONE published function whose result the refusal
  # renders. Asserting this rather than the message is what makes the CONTENT of each refusal
  # assertable at all: `tryEval` discards message text, so a suite of booleans alone would be
  # equally satisfied by a construction with one refusal in it.
  unresolvedFor =
    relata:
    genProgram.unresolvedRelata {
      declarations = [
        {
          head = "h";
          inherit relata;
        }
      ];
      inherit frozen;
    };
in
{
  flake.tests.staging = {
    # ── THE SUBJECT: a relatum this pass would mint ──
    test-a-same-pass-relatum-does-not-resolve = {
      expr = refused (build [ "same-pass:node" ]).program;
      expected = true;
    };

    # THE REFUSAL'S CONTENT, as data: the IDENTIFIER, named. Not a cycle, not a pass.
    test-the-refusal-names-the-identifier-that-did-not-resolve = {
      expr = unresolvedFor [ "same-pass:node" ];
      expected = [ "same-pass:node" ];
    };

    # ── THE SECOND WITNESS: the root, through the identical path ──
    test-a-root-relatum-refuses-by-the-same-path = {
      expr = refused (build [ "root" ]).program;
      expected = true;
    };

    test-the-root-is-named-by-the-same-function-that-names-a-same-pass-reference = {
      expr = unresolvedFor [ "root" ];
      expected = [ "root" ];
    };

    # Both reach the refusal through ONE function over ONE frozen set — which is what makes them
    # one mechanism rather than a general rule and a special case. Asserted by running the two
    # together and getting both back from the same call.
    test-both-witnesses-are-named-by-one-call-over-one-frozen-set = {
      expr = unresolvedFor [
        "same-pass:node"
        "root"
      ];
      expected = [
        "same-pass:node"
        "root"
      ];
    };

    # ── THE OVER-BROAD CONTROL ──
    # The identical relation ACROSS passes constructs and resolves. Without this arm every cell
    # above passes against a construction that refuses everything.
    test-control-a-relatum-a-strictly-earlier-pass-settled-does-resolve = {
      expr = refused (build [ "earlier:node" ]).program;
      expected = false;
    };

    test-control-nothing-is-unresolved-in-the-cross-pass-form = {
      expr = unresolvedFor [ "earlier:node" ];
      expected = [ ];
    };

    # And the resolved form really produces a program, rather than merely failing to throw.
    test-control-the-cross-pass-form-yields-a-program-with-its-rule = {
      expr = (build [ "earlier:node" ]).program.rules;
      expected = [
        {
          head = "promotes:earlier:node";
          pos = [ ];
          neg = [ ];
        }
      ];
    };

    # ── THE TWO UNIVERSES STAY APART ──
    # Relata are IDENTIFIERS resolved against the frozen set; a rule's atoms are MEMBERSHIP FACTS.
    # A relatum must not become derivable just by being mentioned, or an identifier would acquire
    # a truth value.
    test-a-relatum-does-not-enter-the-herbrand-base = {
      expr = (build [ "earlier:node" ]).program.atoms;
      expected = [ "promotes:earlier:node" ];
    };

    # A declaration relating nothing must SAY so: `relata` carries no default, so a construction
    # that omits it does not apply. The refusal is the evaluator's and is uncatchable, so what is
    # asserted here is the formal's requiredness, which is readable in-language.
    test-relata-is-a-required-field-of-a-declaration = {
      expr = (builtins.functionArgs genProgram.declaration).relata;
      expected = false;
    };

    test-control-the-body-fields-are-optional-in-the-same-reading = {
      expr = {
        inherit (builtins.functionArgs genProgram.declaration) pos neg head;
      };
      expected = {
        pos = true;
        neg = true;
        head = false;
      };
    };
  };
}
