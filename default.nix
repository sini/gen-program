# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# THREE CHANNELS, ONE PRECEDENCE, AND NONE OF THEM IS A PROBE. A named formal per dependency wins;
# the `inputs` bag is next, tested by attrset membership so a supplied-but-throwing value throws as
# ITSELF rather than falling back; the default is resolved from `./ci/flake.lock`, read as local
# data. There is NO `...`: an argument this root does not declare is a loud error, not a silent drop.
#
# THE PIN SOURCE IS `ci/flake.lock`, WHICH IS WHY THIS ENTRY CAN EXIST AT ALL. gen-program declares
# no flake inputs, so it has no root lock to defer to — the one lock in this repository is the ci
# one, and deferring to it is what turns `import ./. { }` from an abort into a value.
#
# AND IT IS STATED OVER PATHS, NOT NAMES. `gen-prelude` is not a root input of that lock; the
# acceptance run reaches it THROUGH gen-scope (`ci/flake.nix`: `gen-scope.inputs.gen-prelude.lib`),
# so the default transcribes the wiring that is already there rather than adding a second pin of it.
# Under a name the resolution would abort `attribute 'gen-prelude' missing`, deferred to first force
# rather than loud at the boundary.
#
# `src` AND `dep` ARE FORMALS, NOT `let` BINDINGS, AND THAT IS THE INJECTABLE RESOLVER SEAM. `src`
# is the only expression here that fetches; everything else reads the lock as data. A caller
# supplying `src = segs: throw "…"` therefore makes fetching IMPOSSIBLE for that application rather
# than merely absent. A `dep` bound in the `let` below would close over the `let`'s `src`, so the
# override would silently do nothing and the shim would fetch anyway, at rc 0.
#
# The `let` is OUTSIDE the lambda because a formal's default is evaluated in the FORMAL scope, which
# does not see a `let` in the body.
let
  lock = builtins.fromJSON (builtins.readFile ./ci/flake.lock);
  inputsOf = node: lock.nodes.${node}.inputs or { };
  # A direct edge IS the node key; a `follows` value is a PATH resolved segment by segment from this
  # lock's own root. Never by indexing `lock.nodes.<label>` — a last-segment shortcut reads a
  # different node.
  following =
    node: inp:
    let
      v = (inputsOf node).${inp};
    in
    if builtins.isString v then v else builtins.foldl' following lock.root v;
  fetch = segs: builtins.foldl' following lock.root segs;
in
{
  inputs ? { },
  src ? segs: "${builtins.fetchTree lock.nodes.${fetch segs}.locked}",
  # Arity dispatch, because a dependency's root is a function at a shim'd library and a bare value
  # at a leaf, and neither `import p` nor `import p { }` is total over both.
  dep ?
    segs:
    let
      v = import (src segs);
    in
    if builtins.isFunction v then v { } else v,
  prelude ?
    inputs.gen-prelude or (dep [
      "gen-scope"
      "gen-prelude"
    ]),
  scope ? inputs.gen-scope or (dep [ "gen-scope" ]),
}:
import ./lib { inherit prelude scope; }
