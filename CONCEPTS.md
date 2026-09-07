# Concepts

## walker duality

The ES5 generator lowerer's suspension predicates (`contains_yield`,
`contains_await`, `count_yields`, `contains_yield_array`,
`statements_contain_await`) are views of one predicate that must agree
per shape: containment true with count zero inline-clones a live
suspension (miscompile), and a non-zero count on an eval-accepted shape
inflates resume-label arithmetic. Zero in `count_yields` means "provably
clean"; anything not provably clean routes to `eval`, which either splits
or refuses.

*Avoid:* "three-view predicate", "count/contains symmetry" — say walker
duality.
