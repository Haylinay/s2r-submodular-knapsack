import S2R.StreamingComplexity

/-! Complete S2R development. `S2R.Instance.s2r_verified_streaming` returns
an owned feasible selection with the exact original value, n^3 queries,
141*n^3 charged auxiliary operations and 66*n^2 peak RAM words. Rows are
fused into one cursor scan, empty jobs are omitted, and a seed winner is
copied at most once before its cache is released. No global history table
is retained. See the full polynomial bounds and model limitations in
FORMALIZATION_STATUS. -/
