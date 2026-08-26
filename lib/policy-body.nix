# THE POLICY-BODY ALGEBRA: registration-time normal forms whose codomain is READ, never fired for.
#
# Spec of record: den-ag-design specs/2026-08-26-gen-policy-body-algebra-spec.md (carrier
# den-hoag-0o6mh; governing ruling den-hoag-nzu9 arm (c) — terms as the normal form, closures as a
# declared escape carrying the codomain contract). Landed here by the 2026-08-26 HOME amendment:
# this module is gen-program's registration-time authoring/validation surface, and it EVALUATES
# NOTHING — the sole-evaluator charter next door is untouched. What it owns is the normal form a
# policy body is written in, the structural walk that admits or refuses one at construction, the
# three derived codomain facts, and the declared escape with its per-firing contract.
#
# ── THE PROBLEM THIS RETIRES ──
# Three codomain facts about a body are consumed by standing law before the body ever fires:
# `emits` feeds ADR-0008 §3's gate (a declared edge set complete at registration, plus a codomain
# contract preventing bodies from introducing undeclared edges), `binds` and `suppresses` feed
# stratification (ADR-0020/0033 — rule heads known before evaluation begins). Recovery-by-firing
# gets them wrong: a value-conditional body fired at a sentinel context takes the false branch and
# recovers the empty head. Here **a term is read, not fired** — the derivation path contains no
# firing at all, so the recovered-empty-head failure class is unconstructible.
#
# ── THE MANIFESTNESS INVARIANT, AS CONSTRUCTED ──
# The four ★ slots — constructor, kind, the payload attrset's SPINE, the suppress target — are
# registration-time data, and the firing context is UNREACHABLE from them by construction: the
# context enters a body only through slots typed as functions (`when`, `over`, payload values,
# free targets), and the walk's signature takes no context, so context-dependence in a ★ slot is
# not a detected violation but an unconstructible one (ADR-0008's own registration-declaration
# form). The operational predicate is REGISTRATION-FIXED-AND-CONTEXT-UNREACHABLE (the spec's Q3,
# ruled adopt): the slot forces to a definite first-order value at construction, before any
# context exists — a superset of source-literal that preserves derivability exactly.
#
# ── REFUSALS ARE TAGGED VALUES, NEVER THROWS ──
# Every refusal is `{ refused = true; code; blamed = "author"; witness; message; }` — the
# crossing's refusal discipline, with the blamed party the policy AUTHOR, who owns the fix at
# every refusal here. The guarantee covers the throw/assert failure class, which is all
# `builtins.tryEval` can catch: whatever the walk encounters in that class surfaces as the tagged
# value. The owned margin — convertible by no walk, and always LOUD — is divergence (infinite
# recursion, a black hole) PLUS the non-throw/assert evaluation errors tryEval cannot contain (a
# missing attribute, a type error, a missing function argument); that margin is owned here, once,
# as the spec owns it at §2.4 (P-1 re-scope, exec gate 2026-08-26).
#
# ── THE NAMES ARE THE RULED MECHANISM COLUMN'S ──
# The five constructors take substrate names from den-hoag-12xc's owner-approved two-column
# mapping (the mechanism is substrate, the name is framework): `member` (an entity resolved with
# its member bindings), `deliver` (the one delivery constructor — source class, target class,
# attribute path; v1's route/provide are framework sugar over it), `edge` (a stratum-0 edge
# assertion), `suppress` (the exclusion — it feeds the derived set of the same name; no theory
# term resolves at the archived primaries, so the name carries no theory citation and simply names
# its own derived fact), `realize` (realization at the delivery boundary — declared content at a
# declared target). den's v1 verbs (`resolveTo route include exclude instantiate`) stay at the
# framework surface as den's vocabulary-map entries; no identifier here utters them.
{ prelude }:
let
  inherit (builtins)
    all
    attrNames
    concatMap
    elem
    filter
    head
    isAttrs
    isFunction
    isList
    isString
    seq
    sort
    tryEval
    ;

  # Derived sets are canonical: sorted and deduplicated, so equality of codomains is byte
  # equality and order/multiplicity invariance (ADR-0022 alignment, oracle O5) is structural.
  sortUnique = xs: sort (a: b: a < b) (prelude.unique xs);

  # ── THE CLOSED CONSTRUCTOR ENUM ──
  # Closed; extended by owner ruling only (ADR-0012 r3, the same discipline as the crossing's
  # MergePolicyName). Pipe stages are deliberately NOT here — they are the escape lane by the
  # xin3 open-vocabulary ruling.
  ctorNames = [
    "member"
    "deliver"
    "edge"
    "suppress"
    "realize"
  ];

  # ── THE CONSTRUCTOR ROW TABLE ──
  # Consumed by the walk's field-presence check and by BOTH folds. Field presence is a per-ctor
  # TOTAL decision: a skeleton carries exactly `ctor`, optionally `when`, and its row's fields —
  # an out-of-row field is refused, never ignored (silently-ignored is this project's core defect
  # class). The binds column's discriminating principle: `binds` is the set of MEMBER-BINDING
  # payload keys, and a payload key is a member binding iff the ctor resolves an entity that
  # carries the key as a member — true of `member` alone. `deliver`'s keys parameterize a
  # delivery, not member bindings; edge/suppress/realize carry no payload at all.
  #
  # Emitted kinds: `member` emits its literal `kind` argument; `deliver` emits "delivery" and
  # `edge` emits "edge" (both are the corpus's own declared strings); `realize` emits
  # "instantiate" (v1 carries no distinct instantiation kind string — its effect-type string is
  # the closest vocabulary, and the spec's O3 table uses the same word); `suppress` emits nothing
  # into `emits` — it feeds `suppresses`.
  rows = {
    member = {
      fields = [
        "kind"
        "payload"
      ];
      emitted = s: [ s.kind ];
      bindsFrom = s: attrNames s.payload;
      freeTarget = false;
    };
    deliver = {
      fields = [ "payload" ];
      emitted = _: [ "delivery" ];
      bindsFrom = _: [ ];
      freeTarget = false;
    };
    edge = {
      fields = [ "target" ];
      emitted = _: [ "edge" ];
      bindsFrom = _: [ ];
      freeTarget = true;
    };
    suppress = {
      fields = [ "target" ];
      emitted = _: [ ];
      bindsFrom = _: [ ];
      freeTarget = false;
    };
    realize = {
      fields = [ "target" ];
      emitted = _: [ "instantiate" ];
      bindsFrom = _: [ ];
      freeTarget = true;
    };
  };

  # The escape is named in every refusal because the refusal is the SIGNPOST to it — the compat
  # channel is discovered rather than fought.
  escapePointer = "the declared escape (`escape`, with its required total emits/binds/suppresses contract) is the sanctioned alternative";

  refuse = code: witness: message: {
    refused = true;
    blamed = "author";
    inherit code witness message;
  };

  isRefusal = v: isAttrs v && (v.refused or false) == true;

  # ── THE STRUCTURAL WALK ──
  # Runs at construction (each former calls it) and again at registration (`admit`), so a record
  # hand-rolled around the formers fails the same walk — the invariant holds for the record form
  # too, not only for the blessed constructors. The walk's signature takes no context.
  walkSkeleton =
    s:
    if !isAttrs s then
      refuse "policy-body/skeleton-malformed" s
        "a skeleton is an attrset carrying `ctor`, optionally `when`, and its constructor row's fields — this value is not an attrset; ${escapePointer}"
    else if !(s ? ctor) then
      refuse "policy-body/skeleton-malformed" s
        "a skeleton carries a `ctor` slot and this one does not; ${escapePointer}"
    else
      let
        forcedCtor = tryEval (seq s.ctor s.ctor);
      in
      # V1: constructor in a field value. The slot must force to a member of the closed enum at
      # construction — a function, a non-member string, or anything context-shaped refuses.
      if !forcedCtor.success || !isString forcedCtor.value || !elem forcedCtor.value ctorNames then
        refuse "policy-body/constructor-not-manifest" s.ctor
          "the `ctor` slot must force to a member of the closed enum ${toString ctorNames} at construction — it is registration data and the firing context is unreachable from it by construction (V1); a computed or context-dependent constructor cannot be admitted, and ${escapePointer}"
      else
        let
          ctor = forcedCtor.value;
          row = rows.${ctor};
          allowed = [
            "ctor"
            "when"
          ]
          ++ row.fields;
          fields = attrNames s;
          extra = filter (f: !elem f allowed) fields;
          missing = filter (f: !elem f fields) row.fields;
        in
        # F1: field presence is total per the ctor row — out-of-row refused, in-row required.
        if extra != [ ] then
          refuse "policy-body/skeleton-malformed" extra
            "the `${ctor}` row admits exactly the fields ${toString allowed} and this skeleton also carries ${toString extra} — an out-of-row field is refused, never ignored; ${escapePointer}"
        else if missing != [ ] then
          refuse "policy-body/skeleton-malformed" missing
            "the `${ctor}` row requires the fields ${toString row.fields} and this skeleton is missing ${toString missing} — absence is a decision, and here it is a malformation; ${escapePointer}"
        else if (s ? when) && !isFunction s.when then
          refuse "policy-body/skeleton-malformed" s.when
            "`when` is a free guard over the scope and must be a function where present; ${escapePointer}"
        else if ctor == "member" && !(tryEval (seq s.kind (isString s.kind))).value or false then
          # The kind slot is ★ slot (ii): a string, fixed at construction. (Grammar
          # wellformedness — the spec's V-table assigns kind no code of its own, so the
          # structural code carries it.)
          refuse "policy-body/skeleton-malformed" "kind"
            "the `kind` slot must force to a string at construction; ${escapePointer}"
        else if elem "payload" row.fields then
          walkPayload s
        else if ctor == "suppress" then
          walkSuppressTarget s
        else
          # edge/realize targets are FREE (D3 is excludes only — the ruled dial; a
          # context-dependent include target is live in the reference corpus). Free means free:
          # the walk never inspects argument position.
          s;

  walkPayload =
    s:
    let
      spine = tryEval (seq s.payload true);
    in
    # V3: computed payload keys. The spine either forces to a finite definite name set at
    # construction — in which case a merge over registration-fixed data is ADMITTED (the Q3
    # registration-fixed reading) — or it does not force, and refuses.
    if !spine.success then
      refuse "policy-body/payload-keys-unfixed" "payload"
        "the payload spine does not force to a finite definite name set at construction (V3) — the KEYS are ★ registration data even though the values are free; ${escapePointer}"
    # V2: the `{...}@ctx` pass-through. A bare function at the payload slot is the shape that
    # re-emits the whole context; an attrset whose values are functions keeps the keys fixed and
    # the values free.
    else if !isAttrs s.payload then
      refuse "policy-body/payload-not-keyed" s.payload
        "the payload slot must be an attrset with function values — a bare function here is the context pass-through shape (V2), whose keys nothing can read without firing; ${escapePointer}"
    else
      let
        vals = tryEval (all isFunction (map (k: s.payload.${k}) (attrNames s.payload)));
      in
      if !vals.success || !vals.value then
        refuse "policy-body/payload-not-keyed" (attrNames s.payload)
          "every payload value must be a function of the scope (the keys are fixed at construction, the values are free expressions); ${escapePointer}"
      else
        s;

  walkSuppressTarget =
    s:
    let
      t = tryEval (seq s.target s.target);
    in
    # V4: dynamic exclude target. The ruled dial D3: suppress targets are ★ LITERAL — the slot
    # forces to a definite policy name at construction. (Resolution against the registered policy
    # set is the registration surface's, which holds the registry; fixedness is what is
    # enforceable by construction here.)
    if !t.success || !isString t.value then
      refuse "policy-body/exclude-target-unfixed" s.target
        "the `suppress` target must force to a literal policy reference at construction (V4, the ruled D3 dial) — a computed or context-dependent exclusion target cannot be admitted, and ${escapePointer}"
    else
      s;

  # A clause is a skeleton (the Emit case — discriminated by `ctor`) or an iteration
  # `{ over, emit }` (the ForEach case — discriminated by `over`). ForEach carries EXACTLY those
  # two fields: a per-item guard is the skeleton-level `when`, which the scope convention
  # (the item joins the scope) already serves — no ForEach-level guard field exists.
  walkClause =
    c:
    if isFunction c then
      refuse "policy-body/constructor-not-manifest" c
        "a bare lambda is not a clause — a normal-form body is a list of emission skeletons whose constructor the walk can read without firing (V1); ${escapePointer}"
    else if !isAttrs c then
      refuse "policy-body/skeleton-malformed" c
        "a clause is an emission skeleton or `{ over, emit }`; ${escapePointer}"
    else if isRefusal c then
      c
    else if c ? over then
      let
        fields = attrNames c;
        extra = filter (
          f:
          !elem f [
            "over"
            "emit"
          ]
        ) fields;
        emitList = tryEval (seq c.emit (isList c.emit));
      in
      if extra != [ ] then
        refuse "policy-body/skeleton-malformed" extra
          "`forEach` carries exactly `over` and `emit`, and this one also carries ${toString extra} — a per-item guard is the skeleton-level `when` (the item joins the scope); an out-of-row field is refused, never ignored"
      else if !(c ? emit) || !emitList.success || !emitList.value then
        refuse "policy-body/skeleton-malformed" c
          "`forEach` needs `emit`, a list of emission skeletons, each of which fires once per item of `over`"
      else
        let
          walked = map walkSkeleton c.emit;
          bad = filter isRefusal walked;
        in
        if bad != [ ] then head bad else c
    else if c ? ctor then
      walkSkeleton c
    else
      refuse "policy-body/skeleton-malformed" (attrNames c)
        "a clause is discriminated by `ctor` (an emission skeleton) or `over` (an iteration), and this attrset carries neither; ${escapePointer}";

  # ── THE FORMERS ──
  # Two structural formers suffice: the corpus's sixteen expression primitives all sit in guard
  # or argument position, which is FREE — the algebra never interprets them. Each former runs the
  # walk at call time, so a violation refuses at the author's construction site.
  emit = walkSkeleton;
  forEach = walkClause;

  body =
    { name, clauses }:
    let
      lst = tryEval (seq clauses (isList clauses));
    in
    if !lst.success || !lst.value then
      refuse "policy-body/skeleton-malformed" name
        "a body is `{ name; clauses = [ ... ]; }` and `clauses` must force to a list at construction"
    else
      let
        walked = map walkClause clauses;
        bad = filter isRefusal walked;
      in
      if bad != [ ] then
        head bad
      else
        {
          refused = false;
          opaque = false;
          inherit name;
          clauses = walked;
        };

  # ── THE DECLARED ESCAPE — THE v1-LAMBDA COMPAT CHANNEL, PRICED ──
  # A STRICT PATTERN with NO defaults on the three codomain fields: an absent field does not
  # construct (`builtins.functionArgs` makes the requiredness readable in-language — the mkModel
  # precedent), and `[ ]` is written, not defaulted — absence is a decision the author makes
  # visibly. ADR-0013's impossibility burden is discharged by the FORM, once: what a closure will
  # read when forced is sealed inside a value the substrate cannot inspect — not derivable at
  # all, declaring is the only honest option; what would have to change is a rewrite as a
  # normal-form body. The four prices, all by construction: three required total fields against
  # the normal form's zero; the per-firing contract below; `opaque = true` queryable (the escapes
  # are enumerable at any time); and no silent entry — the only path in is writing the marker.
  escape =
    {
      name,
      fn,
      emits,
      binds,
      suppresses,
    }:
    {
      refused = false;
      __isPolicy = true;
      opaque = true;
      inherit
        name
        fn
        emits
        binds
        suppresses
        ;
    };

  # ── THE REGISTRATION DOOR ──
  # The substrate re-runs the walk here when a policy is registered: hand-rolled records pass or
  # fail exactly as former-built ones do, a marked escape is checked for its total contract, and
  # a bare v1 lambda without the marker is refused with the signpost.
  admit =
    v:
    if isFunction v then
      refuse "policy-body/constructor-not-manifest" v
        "a bare lambda is not a policy body — its constructors cannot be read without firing (V1); ${escapePointer}"
    else if !isAttrs v then
      refuse "policy-body/skeleton-malformed" v "a policy body is a record; ${escapePointer}"
    else if isRefusal v then
      v
    else if (v.opaque or false) == true then
      let
        required = [
          "name"
          "fn"
          "emits"
          "binds"
          "suppresses"
        ];
        missing = filter (f: !(v ? ${f})) required;
        extra = filter (
          f:
          !elem f (
            required
            ++ [
              "__isPolicy"
              "opaque"
              "refused"
            ]
          )
        ) (attrNames v);
      in
      if missing != [ ] then
        refuse "policy-body/skeleton-malformed" missing
          "an escape declares its whole codomain at the site — ${toString required} are REQUIRED and total (`[ ]` is written, not defaulted), and this one is missing ${toString missing}"
      else if extra != [ ] then
        refuse "policy-body/skeleton-malformed" extra
          "an escape record carries exactly its declared form and this one also carries ${toString extra} — an out-of-row field is refused, never ignored"
      else
        v // { refused = false; }
    else if v ? clauses then
      let
        extra = filter (
          f:
          !elem f [
            "name"
            "clauses"
            "refused"
            "opaque"
          ]
        ) (attrNames v);
      in
      # The out-of-row principle at record level: a declared-codomain field (`binds`, `emits`,
      # `suppresses`) beside normal-form clauses is the migration half-step whose stale
      # declaration the derivation would silently contradict — refused, never dropped.
      if extra != [ ] then
        refuse "policy-body/skeleton-malformed" extra
          "a normal-form body carries exactly `name` and `clauses`, and this record also carries ${toString extra} — the codomain is DERIVED from the clauses here, so a declared field beside them is refused rather than silently dropped"
      else
        body {
          name = v.name or "(unnamed)";
          inherit (v) clauses;
        }
    else
      refuse "policy-body/skeleton-malformed" (attrNames v)
        "a policy body is `{ name; clauses; }` in the normal form or an `opaque = true` escape; ${escapePointer}";

  # ── THE DERIVATIONS ──
  # Three syntactic folds over the clause list, with NO evaluation over any context — the
  # signature has no context parameter, so the checker is its own by-construction proof that no
  # derived fact depends on the firing context (ADR-0013's derive-not-declare made checkable).
  # ForEach contributes its skeletons exactly as Emit does: the folds are invariant under
  # multiplicity — `over` is never read — which is why `over` may be fully free (ADR-0022).
  # On an escape it does not compute — it READS the declared contract — so the result type is
  # total over both forms and every policy has a codomain at registration, which is what
  # ADR-0008 §3's precondition consumes.
  deriveCodomain =
    b:
    if isRefusal b then
      b
    else if b.opaque then
      {
        emits = sortUnique b.emits;
        binds = sortUnique b.binds;
        suppresses = sortUnique b.suppresses;
      }
    else
      let
        skeletons = concatMap (c: if c ? over then c.emit else [ c ]) b.clauses;
      in
      {
        emits = sortUnique (concatMap (s: rows.${s.ctor}.emitted s) skeletons);
        binds = sortUnique (concatMap (s: rows.${s.ctor}.bindsFrom s) skeletons);
        suppresses = sortUnique (
          concatMap (s: if s.ctor == "suppress" then [ s.target ] else [ ]) skeletons
        );
      };

  # ── THE ESCAPE'S PER-FIRING CONTRACT ──
  # Contracted at EVERY FIRING (ADR-0008: the licence is the contract, and an uncontracted
  # projection rots into vacuity). The firing's actual declarations — fired skeletons, in this
  # module's own shape — are checked against the declared sets; an emission outside `emits`, a
  # member-binding key outside `binds`, an exclusion outside `suppresses` refuses at the firing
  # that breached, naming the site, the field and the delta. This is what makes the declaration
  # TRUE rather than aspirational. The check is inseparable from the firing: this function IS the
  # escape's firing path.
  fireEscape =
    e: ctx:
    let
      declarations = e.fn ctx;
      breaches = concatMap (
        d:
        # The shape arm (P-2, exec gate): a declaration outside the skeleton shape — no `ctor`,
        # or a ctor no row knows (what a raw unwrapped v1 lambda returns) — is a contract breach
        # at the author's door, not an internal crash blaming this module.
        if !(isAttrs d && d ? ctor && isString d.ctor && rows ? ${d.ctor}) then
          [
            {
              field = "shape";
              delta =
                if isAttrs d && d ? ctor then
                  "a declaration whose ctor is not a known constructor"
                else
                  "a declaration without a ctor";
            }
          ]
        else
          map (k: {
            field = "emits";
            delta = k;
          }) (filter (k: !elem k e.emits) (rows.${d.ctor}.emitted d))
          ++ map (k: {
            field = "binds";
            delta = k;
          }) (if d.ctor == "member" then filter (k: !elem k e.binds) (attrNames d.payload) else [ ])
          ++ map (n: {
            field = "suppresses";
            delta = n;
          }) (if d.ctor == "suppress" && !elem d.target e.suppresses then [ d.target ] else [ ])
      ) declarations;
      renderBreach =
        br: if br.field == "shape" then "shape: ${br.delta}" else "${br.field} is missing '${br.delta}'";
    in
    if breaches != [ ] then
      refuse "policy-body/codomain-breach"
        {
          site = e.name;
          inherit breaches;
        }
        "the escape '${e.name}' breached its declared codomain at this firing: ${
          prelude.concatMapStringsSep "; " renderBreach breaches
        } — the declaration at the site must state the whole codomain, and the check at every firing is what keeps it true rather than aspirational"
    else
      declarations;
in
{
  inherit
    ctorNames
    emit
    forEach
    body
    escape
    admit
    deriveCodomain
    fireEscape
    ;
}
