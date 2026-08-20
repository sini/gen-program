# gen-program REPL — all exports in scope, plus the lib value itself as `genProgram`.
#
# The library is a FUNCTION of its injected substrate, so this file has to resolve one before
# there is a value to splice. It resolves the acceptance run's own — this flake's `gen-scope` and
# the prelude beneath it — so what the REPL hands back is the surface the suite tests and not a
# second, differently-pinned one. That is also why it needs `--impure`.
let
  ci = builtins.getFlake (toString ./.);
  scope = ci.inputs.gen-scope.lib;
  prelude = ci.inputs.gen-scope.inputs.gen-prelude.lib;

  genProgram = import ../lib { inherit prelude scope; };
in
{
  inherit genProgram scope prelude;
}
// genProgram
