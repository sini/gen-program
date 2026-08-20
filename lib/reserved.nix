# THE NAMESPACE THIS LIBRARY OWNS INSIDE THE HERBRAND BASE, AND THE REFUSAL THAT MAKES IT ITS OWN.
#
# The pass-boundary construction (see `rules.nix`) introduces FRESH ATOMS that no declaration
# wrote. They are real atoms: they enter the program's `atoms`, hence the Herbrand base, hence
# every verdict list the model reports. So two properties have to hold, and only one of them is
# about reporting.
#
#   1. A fresh atom must never collide with an authored one. If it did, a declaration's own fact
#      would acquire a negative partner it never asked for, and the collision would show up as a
#      verdict rather than as an error.
#   2. A fresh atom must be RECOGNISABLE, because the model that reports verdict lists has to
#      subtract them from what it enumerates.
#
# ★ THE TWO ARE MET BY ONE MECHANISM, AND IT IS A REFUSAL RATHER THAN A HOPE. A prefix alone gives
# recognisability and buys collision-freedom only by being unlikely — "unguessable by accident" is
# a probability, and a probability is what this repository keeps refusing to build on. So the
# prefix is RESERVED: an authored atom carrying it is refused BY NAME at construction. Collision
# is then impossible rather than improbable, and the same string that makes it impossible is what
# makes a fresh atom recognisable.
#
# ★ THE PREFIX CARRIES NO FRAMEWORK VOCABULARY, WHICH IS AN OBLIGATION AND NOT AN AESTHETIC.
# `den-hoag-h2yp` law 2 forbids encoding topology or kind relationships, and an atom-naming scheme
# is exactly where a translation can smuggle one back in after the program datatype has been made
# topology-free (spec R§1.7). This prefix names THIS LIBRARY and nothing else: no kind, no
# relationship, no direction. Every other atom in the base is a string the caller supplied.
#
# ★ AND IT NAMES NO ACT. Spec R§0.4 measures `grounding` at 0 occurrences across both corpora and
# rules that no identifier is published for the act of turning declarations into ground rules. The
# names below are the NAMESPACE and its MEMBERSHIP TEST — an object and a predicate, not a verb.
{ prelude }:
let
  # The reserved prefix. It is a value rather than a pattern: membership is a prefix test, so the
  # namespace has one definition and the recogniser and the refusal read the same one.
  reservedPrefix = "gen-program::";

  # Total on every string, including the empty one, and it answers rather than throwing: a
  # membership test that refused on a malformed input would make the refusal above unreachable for
  # exactly the inputs it exists to catch. The test is the prelude's own — a second prefix test
  # written here would be a second place the namespace is defined.
  isReserved = prelude.hasPrefix reservedPrefix;

  # The partner atom of `atom` in the pass-boundary construction. Injective on authored atoms
  # because it is a prefix of a distinct string, and disjoint from them because the prefix is
  # refused in authored position.
  partnerOf = atom: reservedPrefix + atom;
in
{
  inherit
    reservedPrefix
    isReserved
    partnerOf
    ;
}
