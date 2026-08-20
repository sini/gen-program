# THE PROBE THAT EXHIBITS WHAT NO CELL CAN OBSERVE — the result record's constructor, applied
# without its adjudication field.
#
# `ci/tests/adjudication.nix` asserts that `adjudication` is a REQUIRED FORMAL, which is readable
# in-language through `builtins.functionArgs` and is what a cell can hold. What a cell CANNOT hold
# is the refusal itself: the evaluator's "called without required argument" is not a thrown value,
# `tryEval` does not contain it, and a cell whose `expr` provokes one crashes the run rather than
# failing. gen-scope's `stratify.nix` records the same property of its own argument record.
#
# So the refusal is exhibited here instead, where a person or a CI step reads an EXIT STATUS rather
# than a cell:
#
#   nix eval --impure -f ci/bench/requiredness-probe.nix dropped   # MUST fail, naming the field
#   nix eval --impure -f ci/bench/requiredness-probe.nix attached  # MUST succeed
#
# ★ THE SECOND INVOCATION IS THE CONTROL AND IT IS NOT OPTIONAL. A probe that only shows a failure
# is equally satisfied by a constructor that refuses everything — by a typo in the path, by a
# broken import, by a library that does not evaluate at all. The two arms differ in ONE field.
#
# ★★ READ THE STATUS UNPIPED. `nix eval … | tee log` reports the PIPELINE's status, not the
# evaluator's, and under zsh the per-stage statuses live in `$pipestatus` (lowercase) rather than
# `$PIPESTATUS`. A probe whose failure arm is read through a pipe can report success while the
# thing it probes is broken.
#
# MEASURED, 2026-08-20, nix 2.34.8:
#   dropped  ⇒ exit 1, "error: function 'anonymous lambda' called without required argument
#              'adjudication'"
#   attached ⇒ exit 0, the record's own attribute names
let
  ci = builtins.getFlake (toString ../.);
  scope = ci.inputs.gen-scope.lib;
  prelude = ci.inputs.gen-scope.inputs.gen-prelude.lib;
  genProgram = import ../../lib { inherit prelude scope; };

  built = genProgram.program {
    declarations = [
      {
        head = "a";
        relata = [ ];
      }
    ];
    frozen = [ ];
    carried = [ ];
  };

  solved = scope.solve built.program;

  # Everything the constructor needs EXCEPT the statement. This is the mutilated construction the
  # oracle asks about, written out rather than described.
  withoutTheStatement = {
    inherit solved;
    inherit (built) authored;
    complete = true;
  };
in
{
  # MUST NOT EVALUATE. The refusal is the evaluator's, it names the field, and nothing in the
  # language can catch it — which is the strongest form the requiredness can take.
  dropped = builtins.attrNames (genProgram.mkModel withoutTheStatement);

  # THE CONTROL: the identical application with the one field restored.
  attached = builtins.attrNames (
    genProgram.mkModel (
      withoutTheStatement
      // {
        adjudication = genProgram.adjudicate {
          inherit (built) program;
          model = solved;
        };
      }
    )
  );
}
