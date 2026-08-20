{
  description = "gen-program — the consumer that turns a framework's declarations into a logic program, drives gen-scope's well-founded engine over it, and carries the third value out under its own name";

  # NO inputs, and that is what the content decided rather than what the scaffold left undone. The
  # library takes its substrate — the utility base and the evaluator that owns the semantics — as
  # INJECTED VALUES constructed inside the consumer's own evaluation, which is the gen↔gen
  # boundary rule's shape: only plain data crosses, and a library that re-declared gen-scope here
  # would pin the evaluator on its consumer's behalf. Two instances of gen-scope in one evaluation
  # are two identity formulas for the same node, so the pin belongs to whoever assembles the run.
  # gen-prelude, gen-algebra and gen-assemble ship this same zero-input shape.
  #
  # A consequence, not an omission: zero inputs means no root lock file. The only lock in this
  # repository is ./ci/flake.lock, and it is what the acceptance run uses.
  #
  # The test runner lives in ./ci, which is a separate flake.
  outputs =
    { ... }:
    {
      lib = import ./lib;
    };
}
