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
  #
  # ★ THE FLAKE OUTPUT IS THE ROOT, PUBLISHED UNAPPLIED. `./.` and `./lib` were two independent
  # constructions of one value and so free to disagree; there is ONE construction site now, and the
  # two entry paths differ only in who supplies the arguments. A flake can only pass `inputs.<dep>`
  # for a dependency it DECLARES, and this one declares none — so publishing the root unapplied is
  # what lets the consumer supply every argument instead of dropping the edge through to this
  # repository's own ci lock on the flake path. The hub applies this output verbatim
  # (`(input "gen-program").lib { prelude; scope; }`), so an APPLIED output here would abort every
  # hub evaluation with `attempt to call something which is not a function but a set`.
  outputs = _: {
    lib = import ./.;
  };
}
