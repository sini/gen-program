# THE PROBE THAT EXHIBITS THE REFUSAL AS AN EXIT STATUS — the result record's constructor, applied
# without its adjudication field.
#
# `ci/tests/adjudication.nix` asserts that `adjudication` is a REQUIRED field of the published
# contract. Since den-hoag-7gp66 P2 the constructor is a door, so the refusal is a thrown value
# that `tryEval` contains and `ci/tests-error.nix` pins to the byte
# (`test-mkModel-missing-adjudication-message`); the native formal before it aborted uncatchably.
# This probe stays as the same refusal read where a person or a CI step reads an EXIT STATUS:
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
# MEASURED, 2026-09-29, nix 2.34.8 (re-derived at den-hoag-ea3j4: the previous fixture passed a
# retired `carried` option and read a retired `authored` field, so its CONTROL arm had died):
#   dropped  ⇒ exit 1, "error: function 'mkModel' called without required argument 'adjudication'"
#   attached ⇒ exit 0, the record's own attribute names
# RE-MEASURED, 2026-10-03 (den-hoag-7gp66 P2 L3): at gen-program 8ee37c2 BOTH arms exited 1 with
# "called without required argument 'algebra'" — the import below predated the library's `algebra`
# and `identity` formals, so the control arm had died again. With them wired:
#   dropped  ⇒ exit 1, "gen-program.mkModel: required field 'adjudication' is missing (…)"
#   attached ⇒ exit 0
let
  ci = builtins.getFlake (toString ../.);
  scope = ci.inputs.gen-scope.lib;
  prelude = ci.inputs.gen-scope.inputs.gen-prelude.lib;
  genProgram = import ../../lib {
    inherit prelude scope;
    algebra = ci.inputs.gen-algebra.lib;
    identity = ci.inputs.gen-identity.lib;
  };

  program =
    genProgram.program
      [ ]
      [
        {
          head = "a";
          relata = [ ];
        }
      ];

  solved = scope.solve [ ] program;

  # Everything the constructor needs EXCEPT the statement. This is the mutilated construction the
  # oracle asks about, written out rather than described.
  withoutTheStatement = {
    inherit solved program;
    complete = true;
  };
in
{
  # MUST NOT EVALUATE. The door refuses by name, naming the field.
  dropped = builtins.attrNames (genProgram.mkModel withoutTheStatement);

  # THE CONTROL: the identical application with the one field restored.
  attached = builtins.attrNames (
    genProgram.mkModel (
      withoutTheStatement
      // {
        adjudication = genProgram.adjudicate {
          inherit program;
          interpretation = [ ];
          model = solved;
        };
      }
    )
  );
}
