# Immutable alias observes mutation

Use this directory as a Fearless project root, with the real standard library.
`Hello` is the entry point. This is an executable companion to
`GenericCapabilityAliasTest.rejectsImmutableAliasToCapturedMutableCell`.

`Boxes` returns a mutable box whose `.get` returns its captured `cell`.
`User.freeze` changes only the generic argument, from `mut Var[Nat]` to
`imm Var[Nat]`, retaining the mutable outer box capability. `frozen` is
explicitly declared `imm Var[Nat]`; `User.observe` also explicitly requires
that immutable type. The original mutable alias remains live.

The current compiler accepts the program. Running it prints:

```text
0
1
```

Both observations use the same immutable reference. Between them,
`cell.set(1)` mutates the same object through its original mutable alias.
There is no fresh variable allocation in `.get` and no reassignment of
`frozen`. This demonstrates the soundness problem; rejecting the invalid
conversion is the intended regression outcome.

Verified with `Coordinator.main(projectRoot)` using the maintained
integration build and real standard-library cache. The runtime probe
asserted the complete output was exactly `0\n1\n` and exited 0.
