# Type system bugs

One entry per bug in the type system itself. Each gives the rule as implemented, before
and after, minimized to pseudocode, so this file can be diffed against the formalism:
was the formalism wrong too, or did the implementation deviate?

Notation. `D` maps a type variable to its capability bound. `rcs(D,T)` is the set of
capabilities `T` can have: `{rc}` for `rc C[..]` and for `rc X`, all of `D(X)` for a bare
`X`. `T[rc]` replaces the outermost capability of `T`.

## 1. The minimal type of a call is not unique

Frontend#27, 2026-08-24. Crash, not unsoundness. `PromotionMatrixTest`.

A call has a set of applicable promotions, each giving a result type; the type of the
call is the least of them.

    minimal(D, Ts) = { T in Ts | no T' in Ts with T' != T and T' <: T }

    was:  best(D, Ts) = the unique element of minimal(D, Ts), error if not unique
    now:  best(D, Ts) = the first element of minimal(D, Ts)
          -- promotions are generated in a fixed order, "as declared" first

Witness. `D(X) = {imm,mut}` and `Ts = {X, imm X}`, reached with an `imm` or `iso`
receiver, which is what keeps both "as declared" and "strengthen result" applicable.
`X <: imm X` fails because `mut` is not `<: imm`, and `imm X <: X` fails because `imm` is
not `<: mut`, so `minimal` has two elements. Both are sound, so `<:` cannot break the
tie. Taking the glb of the bound instead would make it unique but is unsound: it would
call an existing `imm` object `iso`.

## 2. Subtyping ignores the capability of a generic argument

Frontend#38 with StandardLibrary#49, 2026-09-08. Unsound. `GenericCapabilityAliasTest`.

    T1 <: T2  iff  T1 = T2  or  readImmVar(D,T1,T2)
                   or sameShape(D,T1,T2)  or  viaSuper(D,T1,T2)

    sameShape(D, T1, T2) =
      eqModVar(D, T1[mut], T2[mut])            -- outermost capability neutralised
      and forall r1 in rcs(D,T1), r2 in rcs(D,T2). r1 <: r2

    eqModVar(D, A, B) = match (A, B) with
      A = B                           -> true
      (X, rc X) or (rc X, X)          -> D(X) = {rc}
      (rc1 C[A1..An], rc2 C'[B1..Bn]) -> C = C'
                                         and forall i. eqModVar(D, Ai, Bi)
                                         was: rc1 and rc2 discarded here
                                         now: and rc1 = rc2
      otherwise                       -> false

`eqModVar` is entered at depth 0 with both capabilities already replaced by `mut`, so the
added conjunct constrains only depth 1 and below: the arguments become invariant.

Witness. `mut Box[mut C] <: mut Box[imm C]` held, and so did its converse, so a `mut`
alias stayed observable through an `imm` one.

Side condition dropped with it: a `BaseId` body must be `x` or `x.as{..}`, and the check
additionally demanded that the `.as` call resolve at an `imm` receiver. `BaseContainer` is
sealed and declares one `.as`, so the capability it resolves at says nothing about whether
the body is the identity.
