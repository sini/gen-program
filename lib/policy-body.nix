# THE POLICY-BODY ALGEBRA, ON TERMS: registration-time normal forms whose codomain is READ, never
# fired for, and the interpreter that resolves an admitted body at a context.
#
# Spec of record: den-ag-design specs/2026-08-26-gen-policy-body-algebra-spec.md (carrier
# den-hoag-0o6mh; governing ruling den-hoag-nzu9 arm (c) — terms as the normal form, closures as a
# declared escape carrying the codomain contract), made terms-only by
# specs/2026-10-02-gen-program-terms-only-spec.md (den-hoag-lwbb1 unit 3, U3a) over the approved
# design specs/2026-10-01-gen-first-order-rules-design.md Section 4.
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
# ── EVERY FREE SLOT IS A TERM ──
# `when`, the payload values, `over`, and the edge/realize targets are terms of gen-algebra's one
# algebra (`T`, applied to the one minting authority). The walk runs `checkClause` at construction
# and again at registration under the one declared coordinate set `declared` the body carries, so
# a body reads a coordinate only where a positive atom of its condition covers it (Apt–Blair–Walker),
# and the interpreter resolves it under that same value — one `D` for checking and resolving, by
# construction. A closure is applied nowhere on the term path: a door clause's body is `ref r`, and
# `r` resolves through the door the framework supplies. Until that door exists (gen-rules, unit 4)
# the declared escape below stays the closure's path, so every refusal still names it.
#
# ── THE MANIFESTNESS INVARIANT, AS CONSTRUCTED ──
# The four ★ slots — constructor, kind, the payload attrset's SPINE, the suppress target — are
# registration-time data, and the firing context is UNREACHABLE from them by construction: the
# context enters a body only through term slots, and the walk's signature takes no context. The
# operational predicate is REGISTRATION-FIXED-AND-CONTEXT-UNREACHABLE (the spec's Q3, ruled adopt).
#
# ── REFUSALS ARE TAGGED VALUES, NEVER THROWS ──
# Every refusal is `{ refused = true; code; blamed = "author"; witness; message; }` — the
# crossing's refusal discipline, with the blamed party the policy AUTHOR. A refusal the term algebra
# returns is carried under the code `policy-body/<core code>` with the core's witness, so
# `unsafe-read`, `undeclared-name` and `term-function` keep their names. The owned margin —
# convertible by no walk, and always LOUD — is divergence PLUS the non-throw/assert evaluation
# errors `tryEval` cannot contain (spec §2.4, P-1 re-scope).
#
# ── THE NAMES ARE THE RULED MECHANISM COLUMN'S ──
# The five constructors take substrate names from den-hoag-12xc's owner-approved two-column
# mapping: `member`, `deliver`, `edge`, `suppress`, `realize`. den's v1 verbs stay at the framework
# surface as den's vocabulary-map entries; no identifier here utters them.
{
  prelude,
  T,
  hashIdentity,
}:
let
  inherit (builtins)
    all
    attrNames
    attrValues
    concatLists
    concatMap
    elem
    filter
    genList
    head
    isAttrs
    isFunction
    isList
    isString
    length
    mapAttrs
    seq
    sort
    tryEval
    ;
  inherit (T)
    term
    isTerm
    children
    readCtxHeads
    checkClause
    resolveTerm
    ;

  # Derived sets are canonical: sorted and deduplicated, so equality of codomains is byte
  # equality and order/multiplicity invariance (ADR-0022 alignment, oracle O5) is structural.
  sortUnique = xs: sort (a: b: a < b) (prelude.unique xs);

  # ── THE CLOSED CONSTRUCTOR ENUM ──
  # Closed; extended by owner ruling only (ADR-0012 r3).
  ctorNames = [
    "member"
    "deliver"
    "edge"
    "suppress"
    "realize"
  ];

  # ── THE CONSTRUCTOR ROW TABLE ──
  # Consumed by the walk's field-presence check, by BOTH folds and by the interpreter. `binds` is
  # the set of MEMBER-BINDING payload keys — true of `member` alone. `realize` emits "instantiate"
  # (v1's effect-type string, the spec's O3 table's word); `suppress` feeds `suppresses`.
  rows = {
    member = {
      fields = [
        "kind"
        "payload"
      ];
      emitted = s: [ s.kind ];
      bindsFrom = s: attrNames s.payload;
    };
    deliver = {
      fields = [ "payload" ];
      emitted = _: [ "delivery" ];
      bindsFrom = _: [ ];
    };
    edge = {
      fields = [ "target" ];
      emitted = _: [ "edge" ];
      bindsFrom = _: [ ];
    };
    suppress = {
      fields = [ "target" ];
      emitted = _: [ ];
      bindsFrom = _: [ ];
    };
    realize = {
      fields = [ "target" ];
      emitted = _: [ "instantiate" ];
      bindsFrom = _: [ ];
    };
  };

  # Every refusal names the remedy: a term, or — for a closure — the declared escape, which stays
  # the closure's path until the gen-rules door exists (spec §2.10, U3a). The signpost is how the
  # compat channel is discovered rather than fought.
  escapePointer = "write the slot as a term of gen-algebra's `term` algebra, or, for a closure, the declared escape (`escape`, with its required total emits/binds/suppresses contract) is the sanctioned alternative";

  refuse = code: witness: message: {
    refused = true;
    blamed = "author";
    inherit code witness message;
  };
  isRefusal = v: isAttrs v && (v.refused or false) == true;
  isCoreRefusal = v: isAttrs v && attrNames v == [ "left" ];
  fromCore =
    r:
    refuse "policy-body/${r.left.code}" r.left.witness (
      r.left.witness.message or "the term algebra refused this clause (${r.left.code}); ${escapePointer}"
    );

  # ── THE INSTANCE ──
  # Every core former but `readFrom`, which reads a crossing target root a rule has none of
  # (unifying spec OQ3). No slots: a rule body holds no module payload.
  vocabulary = filter (f: f != "ReadFrom") T.knownFormers;
  instanceOf = declared: { inherit vocabulary declared; };
  # Under an iteration the item joins the scope: it is a coordinate the iteration supplies.
  withItem = declared: if declared == null then null else declared ++ [ "item" ];

  # A door-registration identifier is `refId`'s encoding, a one-key JSON record `declared` or
  # `nested`. Tested by `match`, never `fromJSON`: a non-JSON identifier must not abort.
  isDoorId = id: isString id && builtins.match "[{]\"(declared|nested)\":.*" id != null;
  subterms = t: if isTerm t then [ t ] ++ concatMap subterms (children t) else [ ];
  doorRefsIn = t: filter (x: x.__bodyTerm == "Ref" && isDoorId x.id) (subterms t);
  refPosition =
    where: refs:
    refuse "policy-body/ref-position"
      {
        inherit where;
        ids = map (r: r.id) refs;
      }
      "a door-registration `ref` is admitted only as the whole body of a door clause; at ${where} it would hand the door's output, and the closures of its scope, into data (unifying spec §2.8, UC1)";

  # `over`'s cover is its SAFETY reads — the heads of the reads that can fail on absence (`readCtx`,
  # `default`), unifying §2.6. A `has`/`eq` inside `over` is a test, two-valued under `D`, not a read
  # to cover: deriving the cover from every context reader would turn
  # `ifThenElse (has b) (lit 1) (lit 2)` into a guard and drop an iteration the core resolves.
  overCondition =
    over:
    term.all (
      map term.has (
        prelude.unique (
          map (x: x.head) (
            filter (
              x:
              elem x.__bodyTerm [
                "ReadCtx"
                "Default"
              ]
            ) (subterms over)
          )
        )
      )
    );

  # ── IDENTITY (ADR-0034) ──
  # A rule mints over its two terms' digests through the one authority, in the tagged sum
  # gen-algebra's `identityOf` reads; a term with no identity makes the rule unmintable by name.
  digest = t: if isAttrs t then (t.__mint or { }).minted or null else null;
  ruleMint =
    c:
    let
      d = {
        condition = digest c.condition;
        body = digest c.body;
      };
    in
    if d.condition == null || d.body == null then
      { unmintable = "a term of this rule carries no identity"; }
    else
      {
        minted = hashIdentity "rule" [ "condition" "body" ] (l: d.${l});
      };
  # The iteration mints over `over` and the emitted rules' digests.
  iterationMint =
    c:
    let
      d = {
        over = digest c.over;
        emit = map digest c.emit;
      };
    in
    if d.over == null || elem null d.emit then
      { unmintable = "`over` or an emitted rule of this iteration carries no identity"; }
    else
      {
        minted = hashIdentity "rule-iteration" [ "over" "emit" ] (l: d.${l});
      };

  # ── THE STRUCTURAL WALK ──
  # Runs at construction (each former calls it) and again at registration (`admit`), so a record
  # hand-rolled around the formers fails the same walk. The walk's signature takes no context.
  bodyTermOf =
    s:
    if elem "payload" rows.${s.ctor}.fields then
      term.attrs s.payload
    else if s.ctor == "suppress" then
      term.lit s.target
    else
      s.target;

  walkSkeleton =
    itemScoped: declared: s:
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
            "__mint"
          ]
          ++ row.fields;
          fields = attrNames s;
          extra = filter (f: !elem f allowed) fields;
          missing = filter (f: !elem f fields) row.fields;
          spine = tryEval (seq s.payload true);
          target = tryEval (seq s.target s.target);
          fnSlot = filter (k: (s ? ${k}) && isFunction s.${k}) [
            "when"
            "target"
          ];
          cond = s.when or term.always;
          clause = {
            condition =
              if itemScoped then
                term.all [
                  (term.has "item")
                  cond
                ]
              else
                cond;
            body = bodyTermOf s;
          };
          checked = checkClause (instanceOf (if itemScoped then withItem declared else declared)) clause;
          refs = doorRefsIn clause.body;
        in
        # F1: field presence is total per the ctor row — out-of-row refused, in-row required.
        if extra != [ ] then
          refuse "policy-body/skeleton-malformed" extra
            "the `${ctor}` row admits exactly the fields ${toString allowed} and this skeleton also carries ${toString extra} — an out-of-row field is refused, never ignored; ${escapePointer}"
        else if missing != [ ] then
          refuse "policy-body/skeleton-malformed" missing
            "the `${ctor}` row requires the fields ${toString row.fields} and this skeleton is missing ${toString missing} — absence is a decision, and here it is a malformation; ${escapePointer}"
        else if ctor == "member" && !(tryEval (seq s.kind (isString s.kind))).value or false then
          refuse "policy-body/skeleton-malformed" "kind"
            "the `kind` slot must force to a string at construction; ${escapePointer}"
        # V4: dynamic exclude target. The ruled dial D3: suppress targets are ★ LITERAL — a term or
        # a closure here is the computed exclusion target V4 names.
        else if ctor == "suppress" && !(target.success && isString target.value) then
          refuse "policy-body/exclude-target-unfixed" s.target
            "the `suppress` target must force to a literal policy reference at construction (V4, the ruled D3 dial) — a computed or context-dependent exclusion target cannot be admitted, and ${escapePointer}"
        # V3: computed payload keys. The spine either forces to a finite definite name set at
        # construction — a merge over registration-fixed data is ADMITTED (the Q3 reading) — or it
        # does not force, and refuses.
        else if elem "payload" row.fields && !spine.success then
          refuse "policy-body/payload-keys-unfixed" "payload"
            "the payload spine does not force to a finite definite name set at construction (V3) — the KEYS are ★ registration data even though the values are terms; ${escapePointer}"
        # V2: the `{...}@ctx` pass-through. A bare function at the payload slot re-emits the whole
        # context; an attrset whose values are terms keeps the keys fixed.
        else if elem "payload" row.fields && !isAttrs s.payload then
          refuse "policy-body/payload-not-keyed" s.payload
            "the payload slot must be an attrset of terms — a bare function here is the context pass-through shape (V2), whose keys nothing can read without firing; ${escapePointer}"
        else if fnSlot != [ ] then
          refuse "policy-body/term-function" fnSlot
            "`${head fnSlot}` holds a function; a rule body is first-order — `when` is a condition term (has/eq/all/any/always/not) and a target is a term; ${escapePointer}"
        else if isCoreRefusal checked then
          fromCore checked
        else if refs != [ ] then
          refPosition "the body of a `${ctor}` skeleton" refs
        else
          s // { __mint = ruleMint clause; };

  # The door clause: a first-order condition and the body `ref r`, with the codomain contract the
  # framework declared when it registered the closure. `binds`/`suppresses` are a finite name list,
  # or `null`, the written over-approximation: every name of the declared kinds (design Section 4).
  isNameSet = v: v == null || (isList v && all isString v);
  walkDoor =
    declared: c:
    let
      required = [
        "body"
        "emits"
        "binds"
        "suppresses"
      ];
      allowed = required ++ [
        "when"
        "__mint"
      ];
      extra = filter (f: !elem f allowed) (attrNames c);
      missing = filter (f: !(c ? ${f})) required;
      clause = {
        condition = c.when or term.always;
        inherit (c) body;
      };
      checked = checkClause (instanceOf declared) clause;
    in
    if extra != [ ] then
      refuse "policy-body/skeleton-malformed" extra
        "a door clause carries exactly ${toString allowed}, and this one also carries ${toString extra} — an out-of-row field is refused, never ignored"
    else if missing != [ ] then
      refuse "policy-body/skeleton-malformed" missing
        "a door clause declares its codomain at registration — ${toString required} are REQUIRED (`[ ]` is written, and `null` is the written over-approximation)"
    else if (c ? when) && isFunction c.when then
      refuse "policy-body/term-function" [ "when" ]
        "a door clause's condition is first-order: `has` over its required formals, or `always`; ${escapePointer}"
    else if !(isTerm c.body && c.body.__bodyTerm == "Ref" && isDoorId c.body.id) then
      refuse "policy-body/door-clause-body" (
        if isTerm c.body then c.body.__bodyTerm else builtins.typeOf c.body
      ) "a door clause's body is the reference term `ref r`, `r` a door-registration identifier (`refId`)"
    else if
      !(isList c.emits && all isString c.emits) || !isNameSet c.binds || !isNameSet c.suppresses
    then
      refuse "policy-body/skeleton-malformed" required
        "`emits` is a list of kinds; `binds` and `suppresses` are a list of names or `null` (every name of the declared kinds)"
    else if isCoreRefusal checked then
      fromCore checked
    else
      c // { __mint = ruleMint clause; };

  # A clause is a skeleton (discriminated by `ctor`), an iteration `{ over, emit }` (by `over`), or
  # a door clause (by `body`). ForEach carries EXACTLY `over` and `emit`: a per-item guard is the
  # skeleton-level `when`, which the scope convention (the item joins the scope) already serves.
  walkClause =
    declared: c:
    if isFunction c then
      refuse "policy-body/constructor-not-manifest" c
        "a bare lambda is not a clause — a normal-form body is a list of clauses whose constructor the walk can read without firing (V1); ${escapePointer}"
    else if !isAttrs c then
      refuse "policy-body/skeleton-malformed" c
        "a clause is an emission skeleton, `{ over, emit }`, or a door clause; ${escapePointer}"
    else if isRefusal c then
      c
    else if c ? over then
      let
        extra = filter (
          f:
          !elem f [
            "over"
            "emit"
            "__mint"
          ]
        ) (attrNames c);
        emitList = tryEval (seq c.emit (isList c.emit));
        checked = checkClause (instanceOf declared) {
          condition = overCondition c.over;
          body = c.over;
        };
        refs = doorRefsIn c.over;
      in
      if extra != [ ] then
        refuse "policy-body/skeleton-malformed" extra
          "`forEach` carries exactly `over` and `emit`, and this one also carries ${toString extra} — a per-item guard is the skeleton-level `when` (the item joins the scope); an out-of-row field is refused, never ignored"
      else if !(c ? emit) || !emitList.success || !emitList.value then
        refuse "policy-body/skeleton-malformed" c
          "`forEach` needs `emit`, a list of emission skeletons, each of which fires once per item of `over`"
      else if isFunction c.over then
        refuse "policy-body/term-function" [ "over" ] "`over` is a list-valued term; ${escapePointer}"
      else if isCoreRefusal checked then
        fromCore checked
      else if refs != [ ] then
        refPosition "`over`" refs
      else
        let
          walked = map (walkSkeleton true declared) c.emit;
          bad = filter isRefusal walked;
          it = c // {
            emit = walked;
          };
        in
        if bad != [ ] then head bad else it // { __mint = iterationMint it; }
    else if c ? ctor then
      walkSkeleton false declared c
    else if c ? body then
      walkDoor declared c
    else
      refuse "policy-body/skeleton-malformed" (attrNames c)
        "a clause is discriminated by `ctor` (an emission skeleton), `over` (an iteration) or `body` (a door clause), and this attrset carries none of them; ${escapePointer}";

  # ── THE FORMERS ──
  # Each runs the walk at call time under the open world, so a violation refuses at the author's
  # construction site; `body` re-walks every clause under its declared set.
  emit = walkSkeleton false null;
  forEach = walkClause null;

  isDeclaredSet = d: d == null || (isList d && all isString d);

  # RECORD class (den-hoag-7gp66 P1, R5): `checkRequired` makes a missing field NAMED and CATCHABLE,
  # and `builtins.seq checked (…)` forces it at application. `declared` is REQUIRED: `null` is
  # written for the open world, because absence is a decision (spec §4 OQ-D).
  body =
    args:
    let
      checked = prelude.checkRequired "gen-program.body" [ "name" "clauses" "declared" ] args;
      inherit (checked) name clauses declared;
      lst = tryEval (seq clauses (isList clauses));
    in
    builtins.seq checked (
      if !isDeclaredSet declared then
        refuse "policy-body/skeleton-malformed" "declared"
          "`declared` is the framework's declared coordinate set: a list of names, or `null` for the open world"
      else if !lst.success || !lst.value then
        refuse "policy-body/skeleton-malformed" name
          "a body is `{ name; clauses = [ ... ]; declared; }` and `clauses` must force to a list at construction"
      else
        let
          walked = map (walkClause declared) clauses;
          bad = filter isRefusal walked;
        in
        if bad != [ ] then
          head bad
        else
          {
            refused = false;
            opaque = false;
            inherit name declared;
            clauses = walked;
          }
    );

  # ── THE DECLARED ESCAPE — THE CLOSURE'S PATH UNTIL THE gen-rules DOOR EXISTS ──
  # Kept in U3a (spec §2.10): retirements come last, once the door exists, so there is no window in
  # which a closure has no path. NO DEFAULTS on the five fields: `[ ]` is written, not defaulted —
  # absence is a decision the author makes visibly. The prices, all by construction: five required
  # total fields; the per-firing contract below; `opaque = true` queryable; and no silent entry.
  # The `...` opens the formal for `prelude.checkOptions`, so an UNKNOWN field is named and caught
  # (den-hoag-7gp66 P1, arm (C)); `builtins.functionArgs escape` reads the identical five formals.
  escape =
    {
      name,
      fn,
      emits,
      binds,
      suppresses,
      ...
    }@args:
    builtins.seq
      (prelude.checkOptions "gen-program.escape" (builtins.attrNames (builtins.functionArgs escape)) args)
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
            "declared"
            "refused"
            "opaque"
          ]
        ) (attrNames v);
      in
      # The out-of-row principle at record level: a declared-codomain field beside normal-form
      # clauses is the migration half-step whose stale declaration the derivation would silently
      # contradict — refused, never dropped.
      if extra != [ ] then
        refuse "policy-body/skeleton-malformed" extra
          "a normal-form body carries exactly `name`, `clauses` and `declared`, and this record also carries ${toString extra} — the codomain is DERIVED from the clauses here, so a declared field beside them is refused rather than silently dropped"
      else if !(v ? declared) then
        refuse "policy-body/skeleton-malformed" [ "declared" ]
          "a body states its declared coordinate set — absence is a decision, so `null` (the open world) is written"
      else
        body {
          name = v.name or "(unnamed)";
          inherit (v) clauses declared;
        }
    else
      refuse "policy-body/skeleton-malformed" (attrNames v)
        "a policy body is `{ name; clauses; declared; }` in the normal form or an `opaque = true` escape; ${escapePointer}";

  # ── THE DERIVATIONS ──
  # Three syntactic folds over the clause list, with NO evaluation over any context — the
  # signature has no context parameter. ForEach contributes its skeletons exactly as Emit does:
  # the folds are invariant under multiplicity — `over` is never read (ADR-0022). A door clause,
  # like an escape, contributes its DECLARED contract; a `null` (the over-approximation) is never
  # collapsed into a finite set, so a body's `binds`/`suppresses` is `null` if any clause declares it.
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
        skeletons = concatMap (
          c:
          if c ? over then
            c.emit
          else if c ? ctor then
            [ c ]
          else
            [ ]
        ) b.clauses;
        doors = filter (c: !(c ? over) && !(c ? ctor)) b.clauses;
        nameSet =
          field: fromSkeletons:
          let
            sets = map (d: d.${field}) doors;
          in
          if elem null sets then null else sortUnique (fromSkeletons ++ concatLists sets);
      in
      {
        emits = sortUnique (
          concatMap (s: rows.${s.ctor}.emitted s) skeletons ++ concatMap (d: d.emits) doors
        );
        binds = nameSet "binds" (concatMap (s: rows.${s.ctor}.bindsFrom s) skeletons);
        suppresses = nameSet "suppresses" (
          concatMap (s: if s.ctor == "suppress" then [ s.target ] else [ ]) skeletons
        );
      };

  # ── THE ESCAPE'S PER-FIRING CONTRACT ──
  # Contracted at EVERY FIRING (ADR-0008: the licence is the contract). The firing's actual
  # declarations are checked against the declared sets; a breach refuses at the firing, naming the
  # site, the field and the delta. This function IS the escape's firing path.
  fireEscape =
    e: ctx:
    let
      declarations = e.fn ctx;
      breaches = concatMap (
        d:
        # The shape arm (P-2, exec gate): a declaration outside the skeleton shape is a contract
        # breach at the author's door, not an internal crash blaming this module.
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

  # ── THE INTERPRETER ──
  # Resolves an admitted body at a context under the body's own `declared` (one D for checking and
  # resolving, by construction) and resolves a door clause's `ref r` through the framework's door,
  # which receives `{ id; context; sources; captured; }` and answers `{ output; scope; }` (unifying
  # spec §2.8). The result is the list of fired declarations, data only, or a refusal. No closure is
  # held or applied: `captured` is handed back to the door unopened (G5). Validating the door's
  # output against its declared codomain is the door's (design Section 4), so it is not re-checked.
  groundInstances =
    args:
    let
      a = prelude.checkRequired "gen-program.groundInstances" [ "body" "context" ] args;
      b = a.body;
      door = args.door or null;

      envOf = context: declared: sources: scope: {
        inherit context declared sources;
        ref =
          if door == null then
            null
          else
            id:
            if isDoorId id then
              door {
                inherit id context sources;
                captured = scope.${id} or null;
              }
            else
              {
                left = {
                  code = "ref-unresolved";
                  witness = { inherit id; };
                };
              };
      };
      res =
        env: t:
        let
          r = resolveTerm env t;
        in
        if r ? left then fromCore r else r.right;
      collect =
        rs:
        let
          bad = filter isRefusal rs;
        in
        if bad != [ ] then head bad else concatLists rs;

      # A read's identity in a firing preimage: its source identity, never its value (0cmbt §3 a′).
      # Under a declared set an ABSENT coordinate is a two-valued fact (Clark completion), so it
      # enters as the fixed absence tag; a present read with no source has no identity.
      readIds =
        env: reads:
        let
          idOf =
            n:
            if env.sources ? ${n} then
              env.sources.${n}
            else if env.declared != null && !(env.context ? ${n}) then
              { absent = true; }
            else
              null;
          ids = map idOf reads;
        in
        if elem null ids then
          null
        else
          builtins.listToAttrs (
            genList (i: {
              name = builtins.elemAt reads i;
              value = builtins.elemAt ids i;
            }) (length reads)
          );

      # R9: a fired declaration's identity is the rule identity plus its firing atoms, the derived
      # reads of the condition and the body, each by source.
      firingMint =
        env: rule: c:
        let
          ids = readIds env (prelude.unique (readCtxHeads c.condition ++ readCtxHeads c.body));
        in
        if rule == null || ids == null then
          { unmintable = "a read of this firing has no source identity, or the rule has none"; }
        else
          {
            minted = hashIdentity "rule-firing" [ "rule" "sources" ] (
              l:
              {
                inherit rule;
                sources = ids;
              }
              .${l}
            );
          };

      # An iteration item's source is the iteration's own: its rule identity, the sources of
      # `over`'s reads, and the item's position (spec §4 OQ-H). No supplier provides `item`.
      itemSource =
        env: c: i:
        let
          ids = readIds env (readCtxHeads c.over);
          it = digest c;
        in
        if it == null || ids == null then
          null
        else
          hashIdentity "rule-iteration-item" [ "iteration" "sources" "index" ] (
            l:
            {
              iteration = it;
              sources = ids;
              index = i;
            }
            .${l}
          );

      fireSkeleton =
        env: s:
        let
          cond = res env (s.when or term.always);
          fired =
            if elem "payload" rows.${s.ctor}.fields then
              let
                vals = mapAttrs (_: res env) s.payload;
                bad = filter isRefusal (attrValues vals);
              in
              if bad != [ ] then
                head bad
              else
                {
                  inherit (s) ctor;
                  payload = vals;
                }
                // (if s ? kind then { inherit (s) kind; } else { })
            else if s.ctor == "suppress" then
              { inherit (s) ctor target; }
            else
              let
                t = res env s.target;
              in
              if isRefusal t then
                t
              else
                {
                  inherit (s) ctor;
                  target = t;
                };
        in
        if isRefusal cond then
          cond
        else if !cond then
          [ ]
        else if isRefusal fired then
          fired
        else
          [
            (
              fired
              // {
                __mint = firingMint env (digest s) {
                  condition = s.when or term.always;
                  body = bodyTermOf s;
                };
              }
            )
          ];

      fireDoor =
        env: scope: c:
        let
          cond = res env (c.when or term.always);
          r = res env c.body;
        in
        if isRefusal cond then
          cond
        else if !cond then
          [ ]
        else if isRefusal r then
          r
        else
          let
            scope' = scope // (r.scope or { });
            env' = envOf env.context env.declared env.sources scope';
          in
          collect (map (fireOutput env' scope') r.output);

      # The door's output is data: fired declarations, and nested door clauses. A nested door clause
      # passes the same walk as a written one, under the body's one `D`, before it fires under the
      # environment extended with the scope the door returned (design Section 3 (f), G5).
      fireOutput =
        env: scope: o:
        if isAttrs o && o ? body && !(o ? ctor) then
          let
            w = walkDoor env.declared o;
          in
          if isRefusal w then w else fireDoor env scope w
        else
          [ o ];

      fireClause =
        env: scope: c:
        if c ? over then
          let
            ok = res env (overCondition c.over);
            items = res env c.over;
          in
          if isRefusal ok then
            ok
          else if !ok then
            [ ]
          else if isRefusal items then
            items
          else if !isList items then
            refuse "policy-body/over-not-list" (builtins.typeOf items) "`over` resolved to a non-list"
          else
            collect (
              concatLists (
                genList (
                  i:
                  let
                    src = itemSource env c i;
                    env' = envOf (env.context // { item = builtins.elemAt items i; }) (withItem env.declared) (
                      env.sources // (if src == null then { } else { item = src; })
                    ) scope;
                  in
                  map (fireSkeleton env') c.emit
                ) (length items)
              )
            )
        else if c ? ctor then
          fireSkeleton env c
        else
          fireDoor env scope c;
    in
    builtins.seq a (
      if isRefusal b then
        b
      else if !(isAttrs b && b ? clauses && (b.refused or true) == false) then
        refuse "policy-body/skeleton-malformed" "body" "`groundInstances` takes an admitted body"
      # One `D` by construction: the declared set is read from the admitted body, never defaulted —
      # a missing field would silently pick the open world (spec §4 OQ-D).
      else if !(b ? declared) then
        refuse "policy-body/skeleton-malformed" [ "declared" ]
          "`groundInstances` resolves under the body's own declared set, and this body carries none — admit it through `body`/`admit`, which require `declared` (`null` is the written open world)"
      else
        collect (map (fireClause (envOf a.context b.declared (args.sources or { }) { }) { }) b.clauses)
    );
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
    groundInstances
    ;
}
