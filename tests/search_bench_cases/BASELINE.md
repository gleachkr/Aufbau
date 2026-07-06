# Search bench baseline

Generated on 2026-06-09 after the Stage 0 capability fixtures. Updated
during Stage 7 for the forward-instantiation capability reclassification,
and on 2026-06-10 during Stage 8 for multi-layer forward saturation and
realistic forward-instantiation probes. Regenerated on 2026-06-11 after
family-fact derivation landed and euclid's redundant `bot_elim` forward
annotation was removed.

Regenerated again on 2026-06-11 after Stage 4 open backward generation
landed. The former Stage 4 probes are now supported, and the table adds
negative controls for inconsistent repeated existentials, missing `@vars`
witnesses, recover-owned no-fallback behavior, and `exact?`/`apply?`
non-participation. Timings are reference points, not exact thresholds;
compare within normal machine noise and use the counters to explain large
changes.

Extended on 2026-06-11 with the five `fwd/bwd compose` scenarios
(`forward_backward_compose.mm0`, `nd_forward_backward.mm0`): the Stage 4+7
composition probes (a forward family fact discharging an open backward
subgoal, Hilbert and ND style) and the forward-direct boundary guard. These
landed together with the recover-surface match-back fix in
`generate.zig:acceptedConclusion` (an implicit-conclusion child whose top
rule concludes through a `@view` used to return the raw conclusion, which
structurally conflicted with the reduced open target). Other scenarios'
timings were re-checked within noise; the heavy `auto?` reference points are
unchanged.

Regenerated on 2026-06-12 after Stage 5 ACUI finite-domain witness
enumeration landed. The former Stage 5 probes are now supported:
`zermelo nd_exists_intro_mem` (member witness from the recover target's own
context) and `zermelo nd_union_intro_imp` (context split + hypothesis-only
witness from the split member, on the now `@auto backward` `union_intro`).
Four `stage5` toy scenarios cover repeated metas, no-valid-member, ambiguous
members, and the ACUI unit. Counter dumps add `acui witness attempts`.

## Compact table

Command:

```text
zig build bench-search -Doptimize=ReleaseFast \
  --cache-dir .cache/zig-local/ --global-cache-dir .cache/zig-global/ \
  -- --compact
```

```text
search benchmark scenarios: 80
scenario                                            total      setup     search
simple exact zero-hypothesis axiom                  0.755ms      0.625ms      0.086ms
simple apply with unresolved hypotheses             0.117ms      0.063ms      0.033ms
multi-hyp exact with many refs                      0.225ms      0.170ms      0.033ms
homogeneous nd-style ref pool                       0.190ms      0.142ms      0.034ms
transparent definition-heavy exact                  0.086ms      0.057ms      0.013ms
view lookup with different raw head                 0.199ms      0.155ms      0.030ms
zermelo cb_bijection_surj_body exact?               5.444ms      3.218ms      2.011ms
peano ax_mp implication exact?                      0.552ms      0.451ms      0.026ms
peano successor congruence exact?                   0.803ms      0.606ms      0.116ms
peano multiplication transitive exact?              1.836ms      1.404ms      0.324ms
peano distributivity transitive exact?              1.818ms      1.420ms      0.289ms
euclid successor no fixed point exact?              4.021ms      1.270ms      2.670ms
euclid final existential exact?                     6.006ms      4.723ms      1.135ms
euclid prime factor or-elim exact?                 18.973ms     16.598ms      2.190ms
euclid final generalization exact?                  6.616ms      4.793ms      1.662ms
church beta conversion exact?                       7.571ms      1.311ms      6.187ms
church and definition refl exact?                   3.218ms      2.464ms      0.655ms
church not definition trans exact?                  4.715ms      3.495ms      1.056ms
zermelo function intro exact?                       5.598ms      2.992ms      2.407ms
zermelo image preimage exact?                      18.990ms      8.931ms      9.833ms
zermelo cb surjection exact?                        4.795ms      2.842ms      1.718ms
zermelo hilbert cantor body exact?                  4.757ms      3.631ms      0.915ms
auto depth-2 chain auto?                            0.120ms      0.069ms      0.030ms
auto depth-3 chain auto?                            0.114ms      0.053ms      0.036ms
auto two-hyp binder pinning auto?                   0.108ms      0.067ms      0.027ms
auto def-conclusion binder pinning auto?            0.108ms      0.066ms      0.026ms
zermelo nd_imp_id auto?                             2.435ms      1.765ms      0.604ms
zermelo nd_explosion auto?                          3.031ms      1.833ms      1.125ms
zermelo nd_and_comm auto?                           5.554ms      1.772ms      3.717ms
zermelo nd_eq_symm auto?                            6.918ms      1.825ms      5.026ms
zermelo nd_and_comm split auto?                     4.482ms      1.854ms      2.557ms
zermelo nd_ext_imp split auto?                     10.907ms      1.838ms      9.001ms
zermelo nd_sep_intro_imp split auto?                7.010ms      1.833ms      5.104ms
zermelo nd_or_comm auto? (split, validation gap)      6.995ms      1.885ms      5.021ms
zermelo nd_exists_intro_mem auto? (Stage 5 ACUI witness)      0.820ms      0.299ms      0.487ms
stage5 repeated meta from member auto?              0.842ms      0.303ms      0.519ms
stage5 no valid member auto? (no result)            1.115ms      0.269ms      0.827ms
stage5 ambiguous members auto? (deterministic order)      1.908ms      0.333ms      1.556ms
stage5 unit context auto? (no result)               0.609ms      0.317ms      0.273ms
zermelo nd_union_intro_imp auto? (Stage 5 split + witness)     10.857ms      1.887ms      8.887ms
zermelo nd_exists_elim_split auto?                 13.011ms      1.955ms     10.968ms
zermelo nd_exists_elim_const auto?                  3.173ms      2.003ms      1.086ms
auto church beta conversion auto?                  29.463ms      1.404ms     27.974ms
auto church and definition refl auto?               8.325ms      2.427ms      5.792ms
auto church not definition trans auto?             14.383ms      3.512ms     10.687ms
auto euclid final generalization auto?            288.855ms      4.778ms    283.905ms
auto zermelo image preimage auto?                 259.642ms      8.630ms    250.709ms
auto zermelo cb surjection auto?                  411.943ms      2.953ms    408.664ms
auto martin_lof add_comm id_trans auto?           143.617ms      2.262ms    140.943ms
auto martin_lof add_comm capstone auto? (no result)      7.752ms      2.493ms      4.989ms
auto martin_lof add_comm id_trans deep auto?       40.116ms      2.275ms     37.492ms
auto martin_lof id_sym_ty J_elim auto? (no result)      5.589ms      1.781ms      3.729ms
auto zermelo nested all_intro auto?                70.654ms      5.576ms     64.839ms
auto zermelo_hilbert imp_id auto? (no result)       1.130ms      0.953ms      0.118ms
auto nd_eq_subst_mem double imp_intro auto?         3.413ms      2.054ms      1.289ms
hyp-only witness auto? (Stage 4 open backward)      0.169ms      0.118ms      0.035ms
generated child pins parent auto? (Stage 4 open backward)      0.202ms      0.123ms      0.064ms
repeated unknown auto? (Stage 4 open backward)      0.181ms      0.125ms      0.041ms
inconsistent repeated unknown auto? (no result, Stage 4)      0.322ms      0.130ms      0.177ms
bound @vars choice auto? (Stage 4 open backward)      0.196ms      0.139ms      0.042ms
missing @vars witness auto? (no result, Stage 4)      0.211ms      0.151ms      0.045ms
euclid ex_intro open witness auto? (Stage 4 open backward)      2.450ms      1.354ms      1.033ms
unannotated rule auto? (no result, Stage 4 gate)      0.202ms      0.143ms      0.042ms
bare-meta target auto? (no result, Stage 4 guard)      0.217ms      0.162ms      0.041ms
recover-owned fallback auto? (no result, Stage 4)      0.223ms      0.151ms      0.058ms
auto backward exact? ignored (no result, Stage 4)      0.123ms      0.106ms      0.004ms
auto backward apply? stays one-step (Stage 4)       0.134ms      0.108ms      0.013ms
all_elim forward instantiation auto? (Stage 7 forward)      0.727ms      0.268ms      0.440ms
all_elim single-step instantiation auto? (supported boundary)      0.569ms      0.265ms      0.283ms
all_elim two-layer derived direct auto? (Stage 8 forward)      0.704ms      0.246ms      0.438ms
all_elim three-layer chain auto? (Stage 8 forward)      0.990ms      0.267ms      0.699ms
euclid le_total two-layer instantiation auto? (Stage 8)      3.504ms      1.566ms      1.854ms
euclid prime-factor instance auto? (Stage 8 forward)      5.165ms      1.831ms      3.197ms
euclid dvd_fact and_elim chain auto? (Stage 8 forward)      5.830ms      1.707ms      4.001ms
fwd/bwd compose hilbert minor-in-pool auto? (Stage 4+7)      0.623ms      0.242ms      0.360ms
fwd/bwd compose hilbert open-minor auto? (Stage 4+7)      0.581ms      0.233ms      0.328ms
fwd/bwd compose hilbert forward-direct auto? (Stage 7)      0.521ms      0.222ms      0.278ms
fwd/bwd compose nd minor-in-pool auto? (Stage 4+7)      1.158ms      0.312ms      0.824ms
fwd/bwd compose nd open-minor auto? (Stage 4+7)      0.985ms      0.331ms      0.634ms
forward saturation loop stress auto? (bounded, no result)      0.288ms      0.077ms      0.195ms
```

## Full counter dumps for auto? scenarios

Command:

```text
zig build bench-search -Doptimize=ReleaseFast \
  --cache-dir .cache/zig-local/ --global-cache-dir .cache/zig-global/ \
  -- --filter='auto?'
```

```text
search benchmark scenarios: 80

auto depth-2 chain auto?
  suggestions: 1
  total wall: 0.753 ms
  cold setup: 0.588 ms
  warm search: 0.114 ms
  rule index build: 0.010 ms
  ref index build: 0.000 ms
  shape emission: 0.002 ms
  rule lookup: 0.003 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.008 ms
  candidate rules before conclusion validation: 6
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    qr hyp=0 phase=initial depth=0 refs=0 fallback=none
    qr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    qr hyp=0 phase=initial depth=0 refs=0 fallback=none
    qr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    pq hyp=0 phase=initial depth=0 refs=0 fallback=none
    pq hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    p: attempts=1 accepted=1 rejected=0
    pq: attempts=1 accepted=1 rejected=0
    qr: attempts=1 accepted=1 rejected=0

auto depth-3 chain auto?
  suggestions: 1
  total wall: 0.109 ms
  cold setup: 0.050 ms
  warm search: 0.037 ms
  rule index build: 0.001 ms
  ref index build: 0.000 ms
  shape emission: 0.003 ms
  rule lookup: 0.003 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.007 ms
  candidate rules before conclusion validation: 10
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 4
  full tryCandidate calls: 4
  accepted candidates: 4
  generated chain attempts: 6
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    rs hyp=0 phase=initial depth=0 refs=0 fallback=none
    rs hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    rs hyp=0 phase=initial depth=0 refs=0 fallback=none
    rs hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    qr hyp=0 phase=initial depth=0 refs=0 fallback=none
    qr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    rs hyp=0 phase=initial depth=0 refs=0 fallback=none
    rs hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    qr hyp=0 phase=initial depth=0 refs=0 fallback=none
    qr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    pq hyp=0 phase=initial depth=0 refs=0 fallback=none
    pq hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    p: attempts=1 accepted=1 rejected=0
    pq: attempts=1 accepted=1 rejected=0
    qr: attempts=1 accepted=1 rejected=0
    rs: attempts=1 accepted=1 rejected=0

auto two-hyp binder pinning auto?
  suggestions: 1
  total wall: 0.123 ms
  cold setup: 0.065 ms
  warm search: 0.045 ms
  rule index build: 0.002 ms
  ref index build: 0.001 ms
  shape emission: 0.002 ms
  rule lookup: 0.001 ms
  ref lookup: 0.001 ms
  tc clone: 0.000 ms
  tc apply: 0.019 ms
  candidate rules before conclusion validation: 3
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 1
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 1
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 1
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    r hyp=0 phase=initial depth=0 refs=1 fallback=none
    r hyp=1 phase=initial depth=0 refs=0 fallback=none
    r hyp=0 phase=initial depth=0 refs=1 fallback=none
    r hyp=1 phase=initial depth=0 refs=0 fallback=none
    r hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    r hyp=1 phase=dynamic depth=1 refs=0 fallback=none
  full validation attempts by rule:
    nk: attempts=1 accepted=1 rejected=0
    r: attempts=1 accepted=1 rejected=0

auto def-conclusion binder pinning auto?
  suggestions: 1
  total wall: 0.118 ms
  cold setup: 0.071 ms
  warm search: 0.033 ms
  rule index build: 0.002 ms
  ref index build: 0.000 ms
  shape emission: 0.002 ms
  rule lookup: 0.001 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.012 ms
  candidate rules before conclusion validation: 3
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 1
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    r hyp=0 phase=initial depth=0 refs=0 fallback=none
    r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    pk: attempts=1 accepted=1 rejected=0
    r: attempts=1 accepted=1 rejected=0

zermelo nd_imp_id auto?
  suggestions: 1
  total wall: 2.770 ms
  cold setup: 1.983 ms
  warm search: 0.723 ms
  rule index build: 0.378 ms
  ref index build: 0.000 ms
  shape emission: 0.074 ms
  rule lookup: 0.006 ms
  ref lookup: 0.007 ms
  tc clone: 0.002 ms
  tc apply: 0.064 ms
  candidate rules before conclusion validation: 55
  conclusion member prunes: 3
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=1 accepted=1 rejected=0
    imp_intro: attempts=1 accepted=1 rejected=0

zermelo nd_explosion auto?
  suggestions: 1
  total wall: 3.027 ms
  cold setup: 1.835 ms
  warm search: 1.129 ms
  rule index build: 0.376 ms
  ref index build: 0.000 ms
  shape emission: 0.153 ms
  rule lookup: 0.014 ms
  ref lookup: 0.015 ms
  tc clone: 0.002 ms
  tc apply: 0.151 ms
  candidate rules before conclusion validation: 112
  conclusion member prunes: 10
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 5
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=1 accepted=1 rejected=0
    bot_elim: attempts=1 accepted=1 rejected=0
    imp_intro: attempts=1 accepted=1 rejected=0

zermelo nd_and_comm auto?
  suggestions: 0
  total wall: 5.566 ms
  cold setup: 1.824 ms
  warm search: 3.682 ms
  rule index build: 0.330 ms
  ref index build: 0.007 ms
  shape emission: 1.544 ms
  rule lookup: 0.083 ms
  ref lookup: 0.133 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 889
  conclusion member prunes: 78
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 52
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none

zermelo nd_eq_symm auto?
  suggestions: 0
  total wall: 8.385 ms
  cold setup: 3.346 ms
  warm search: 4.981 ms
  rule index build: 0.345 ms
  ref index build: 0.000 ms
  shape emission: 2.240 ms
  rule lookup: 0.119 ms
  ref lookup: 0.169 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 1149
  conclusion member prunes: 108
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 66
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ext hyp=0 phase=initial depth=0 refs=0 fallback=none
    ext hyp=1 phase=initial depth=0 refs=0 fallback=none
    ext hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    ext hyp=0 phase=initial depth=0 refs=0 fallback=none
    ext hyp=1 phase=initial depth=0 refs=0 fallback=none
    ext hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none

zermelo nd_and_comm split auto?
  suggestions: 1
  total wall: 4.306 ms
  cold setup: 1.791 ms
  warm search: 2.452 ms
  rule index build: 0.363 ms
  ref index build: 0.004 ms
  shape emission: 0.690 ms
  rule lookup: 0.037 ms
  ref lookup: 0.327 ms
  tc clone: 0.001 ms
  tc apply: 0.315 ms
  candidate rules before conclusion validation: 342
  conclusion member prunes: 26
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 43
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 17
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 43
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    and_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    and_elim_r: attempts=1 accepted=1 rejected=0
    and_elim_l: attempts=1 accepted=1 rejected=0
    and_intro: attempts=1 accepted=1 rejected=0

zermelo nd_ext_imp split auto?
  suggestions: 1
  total wall: 11.147 ms
  cold setup: 1.862 ms
  warm search: 9.223 ms
  rule index build: 0.366 ms
  ref index build: 0.000 ms
  shape emission: 2.750 ms
  rule lookup: 0.137 ms
  ref lookup: 0.126 ms
  tc clone: 0.006 ms
  tc apply: 2.555 ms
  candidate rules before conclusion validation: 824
  conclusion member prunes: 68
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 12
  full tryCandidate calls: 12
  accepted candidates: 12
  generated chain attempts: 47
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    opair_eq_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ext hyp=0 phase=initial depth=0 refs=0 fallback=none
    ext hyp=1 phase=initial depth=0 refs=0 fallback=none
    ext hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=6 accepted=6 rejected=0
    ext: attempts=4 accepted=4 rejected=0
    imp_intro: attempts=2 accepted=2 rejected=0

zermelo nd_sep_intro_imp split auto?
  suggestions: 1
  total wall: 7.123 ms
  cold setup: 1.897 ms
  warm search: 5.161 ms
  rule index build: 0.378 ms
  ref index build: 0.000 ms
  shape emission: 0.603 ms
  rule lookup: 0.037 ms
  ref lookup: 0.036 ms
  tc clone: 0.002 ms
  tc apply: 2.347 ms
  candidate rules before conclusion validation: 240
  conclusion member prunes: 19
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 5
  full tryCandidate calls: 5
  accepted candidates: 5
  generated chain attempts: 13
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=2 accepted=2 rejected=0
    sep_intro: attempts=1 accepted=1 rejected=0
    imp_intro: attempts=2 accepted=2 rejected=0

zermelo nd_or_comm auto? (split, validation gap)
  suggestions: 1
  total wall: 6.801 ms
  cold setup: 1.826 ms
  warm search: 4.901 ms
  rule index build: 0.342 ms
  ref index build: 0.005 ms
  shape emission: 1.461 ms
  rule lookup: 0.067 ms
  ref lookup: 0.776 ms
  tc clone: 0.001 ms
  tc apply: 0.828 ms
  candidate rules before conclusion validation: 672
  conclusion member prunes: 50
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 3
  per-hyp filtered ref list total: 369
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 41
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 331
  hyp definite mismatches: 0
  hyp unknown matches: 38
  recover member injections: 0
  split context guard rejects: 6
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    or_elim hyp=0 phase=dynamic depth=2 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    or_elim hyp=0 phase=dynamic depth=2 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    or_elim hyp=0 phase=dynamic depth=2 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    or_intro_r: attempts=1 accepted=1 rejected=0
    or_intro_l: attempts=1 accepted=1 rejected=0
    or_elim: attempts=1 accepted=1 rejected=0

zermelo nd_exists_intro_mem auto? (Stage 5 ACUI witness)
  suggestions: 1
  total wall: 0.820 ms
  cold setup: 0.281 ms
  warm search: 0.519 ms
  rule index build: 0.039 ms
  ref index build: 0.000 ms
  shape emission: 0.031 ms
  rule lookup: 0.015 ms
  ref lookup: 0.001 ms
  tc clone: 0.001 ms
  tc apply: 0.241 ms
  candidate rules before conclusion validation: 19
  conclusion member prunes: 5
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 4
  full tryCandidate calls: 4
  accepted candidates: 3
  generated chain attempts: 4
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 1
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 1
  meta rollbacks: 2
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=2 accepted=1 rejected=1
    ex_intro: attempts=1 accepted=1 rejected=0
    imp_intro: attempts=1 accepted=1 rejected=0

stage5 repeated meta from member auto?
  suggestions: 1
  total wall: 0.851 ms
  cold setup: 0.298 ms
  warm search: 0.533 ms
  rule index build: 0.043 ms
  ref index build: 0.000 ms
  shape emission: 0.030 ms
  rule lookup: 0.012 ms
  ref lookup: 0.001 ms
  tc clone: 0.001 ms
  tc apply: 0.258 ms
  candidate rules before conclusion validation: 22
  conclusion member prunes: 8
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 4
  full tryCandidate calls: 4
  accepted candidates: 3
  generated chain attempts: 4
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 1
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 1
  meta rollbacks: 2
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=2 accepted=1 rejected=1
    ex_intro: attempts=1 accepted=1 rejected=0
    imp_intro: attempts=1 accepted=1 rejected=0

stage5 no valid member auto? (no result)
  suggestions: 0
  total wall: 1.132 ms
  cold setup: 0.290 ms
  warm search: 0.823 ms
  rule index build: 0.042 ms
  ref index build: 0.000 ms
  shape emission: 0.177 ms
  rule lookup: 0.059 ms
  ref lookup: 0.009 ms
  tc clone: 0.003 ms
  tc apply: 0.262 ms
  candidate rules before conclusion validation: 121
  conclusion member prunes: 51
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 10
  full tryCandidate calls: 10
  accepted candidates: 0
  generated chain attempts: 22
  recursive apply calls: 0
  rejected candidates after validation: 10
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/10/0/0
  meta assignments: 10
  meta rollbacks: 20
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=10 accepted=0 rejected=10

stage5 ambiguous members auto? (deterministic order)
  suggestions: 2
  total wall: 2.767 ms
  cold setup: 0.989 ms
  warm search: 1.725 ms
  rule index build: 0.052 ms
  ref index build: 0.000 ms
  shape emission: 0.032 ms
  rule lookup: 0.012 ms
  ref lookup: 0.000 ms
  tc clone: 0.006 ms
  tc apply: 1.165 ms
  candidate rules before conclusion validation: 15
  conclusion member prunes: 4
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 6
  full tryCandidate calls: 6
  accepted candidates: 5
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 2
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 2
  meta rollbacks: 3
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=1 accepted=1 rejected=0
    tag_member: attempts=3 accepted=2 rejected=1
    ex_intro: attempts=2 accepted=2 rejected=0

stage5 unit context auto? (no result)
  suggestions: 0
  total wall: 0.589 ms
  cold setup: 0.270 ms
  warm search: 0.300 ms
  rule index build: 0.065 ms
  ref index build: 0.000 ms
  shape emission: 0.067 ms
  rule lookup: 0.030 ms
  ref lookup: 0.006 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 63
  conclusion member prunes: 25
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 12
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/12/0/0
  meta assignments: 0
  meta rollbacks: 12
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none

zermelo nd_union_intro_imp auto? (Stage 5 split + witness)
  suggestions: 1
  total wall: 10.515 ms
  cold setup: 1.831 ms
  warm search: 8.616 ms
  rule index build: 0.369 ms
  ref index build: 0.000 ms
  shape emission: 1.066 ms
  rule lookup: 0.075 ms
  ref lookup: 0.081 ms
  tc clone: 0.031 ms
  tc apply: 5.024 ms
  candidate rules before conclusion validation: 525
  conclusion member prunes: 25
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 40
  full tryCandidate calls: 40
  accepted candidates: 11
  generated chain attempts: 25
  recursive apply calls: 0
  rejected candidates after validation: 29
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 2
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/26/0/0
  meta assignments: 2
  meta rollbacks: 17
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    power_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    power_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nd_forall_specialize hyp=0 phase=initial depth=0 refs=0 fallback=none
    nd_forall_specialize hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    power_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    power_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nd_forall_specialize hyp=0 phase=initial depth=0 refs=0 fallback=none
    nd_forall_specialize hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    union_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    sep_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    pairset_intro_left: attempts=10 accepted=0 rejected=10
    pairset_intro_right: attempts=10 accepted=0 rejected=10
    nd_pairset_left: attempts=7 accepted=0 rejected=7
    ax: attempts=9 accepted=7 rejected=2
    union_intro: attempts=4 accepted=4 rejected=0

zermelo nd_exists_elim_split auto?
  suggestions: 1
  total wall: 12.790 ms
  cold setup: 1.851 ms
  warm search: 10.863 ms
  rule index build: 0.385 ms
  ref index build: 0.007 ms
  shape emission: 3.644 ms
  rule lookup: 0.182 ms
  ref lookup: 1.453 ms
  tc clone: 0.004 ms
  tc apply: 1.749 ms
  candidate rules before conclusion validation: 1362
  conclusion member prunes: 108
  final conclusion prunes: 9
  conclusion probes: 0
  ref pool size: 3
  per-hyp filtered ref list total: 306
  ref tuple count after filtering: 6
  full tryCandidate calls: 6
  accepted candidates: 5
  generated chain attempts: 89
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 304
  hyp definite mismatches: 0
  hyp unknown matches: 2
  recover member injections: 0
  split context guard rejects: 40
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
  full validation attempts by rule:
    ex_elim: attempts=3 accepted=2 rejected=1
    imp_elim: attempts=2 accepted=2 rejected=0
    imp_intro: attempts=1 accepted=1 rejected=0

zermelo nd_exists_elim_const auto?
  suggestions: 1
  total wall: 3.013 ms
  cold setup: 1.893 ms
  warm search: 1.048 ms
  rule index build: 0.359 ms
  ref index build: 0.021 ms
  shape emission: 0.125 ms
  rule lookup: 0.008 ms
  ref lookup: 0.044 ms
  tc clone: 0.001 ms
  tc apply: 0.337 ms
  candidate rules before conclusion validation: 58
  conclusion member prunes: 6
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 5
  per-hyp filtered ref list total: 1
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 1
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=5 fallback=broad_shape
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=5 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=5 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=5 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=5 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=5 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=5 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=5 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    imp_intro: attempts=2 accepted=2 rejected=0

auto church beta conversion auto?
  suggestions: 2
  total wall: 30.322 ms
  cold setup: 1.313 ms
  warm search: 28.933 ms
  rule index build: 0.092 ms
  ref index build: 0.082 ms
  shape emission: 0.659 ms
  rule lookup: 0.043 ms
  ref lookup: 0.283 ms
  tc clone: 0.025 ms
  tc apply: 26.592 ms
  candidate rules before conclusion validation: 157
  conclusion member prunes: 20
  final conclusion prunes: 11
  conclusion probes: 0
  ref pool size: 18
  per-hyp filtered ref list total: 82
  ref tuple count after filtering: 49
  full tryCandidate calls: 49
  accepted candidates: 7
  generated chain attempts: 11
  recursive apply calls: 0
  rejected candidates after validation: 42
  hyp syntactic matches: 44
  hyp definite mismatches: 0
  hyp unknown matches: 38
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    inst hyp=0 phase=initial depth=0 refs=1 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=1 fallback=none
    inst hyp=2 phase=dynamic depth=0 refs=1 fallback=none
    inst hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    inst hyp=1 phase=dynamic depth=2 refs=11 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=2 fallback=none
    trans hyp=1 phase=initial depth=0 refs=3 fallback=none
    trans hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    trans hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    trans hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    eqmp hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=1 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=11 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=11 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=11 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    bineq2 hyp=1 phase=dynamic depth=2 refs=1 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=11 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    bineq2 hyp=1 phase=dynamic depth=2 refs=4 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=11 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=18 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=7 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=1 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=1 fallback=none
    inst hyp=1 phase=initial depth=0 refs=11 fallback=none
    inst hyp=2 phase=initial depth=0 refs=1 fallback=none
    inst hyp=2 phase=dynamic depth=0 refs=1 fallback=none
    inst hyp=0 phase=dynamic depth=1 refs=1 fallback=none
  full validation attempts by rule:
    weaken: attempts=4 accepted=1 rejected=3
    inst: attempts=33 accepted=3 rejected=30
    trans: attempts=4 accepted=0 rejected=4
    aeq2: attempts=1 accepted=0 rejected=1
    bineq2: attempts=1 accepted=0 rejected=1
    reflt: attempts=2 accepted=2 rejected=0
    eqmp: attempts=1 accepted=0 rejected=1
    thmR: attempts=1 accepted=0 rejected=1
    appT: attempts=1 accepted=1 rejected=0
    sym: attempts=1 accepted=0 rejected=1

auto church and definition refl auto?
  suggestions: 2
  total wall: 8.170 ms
  cold setup: 2.346 ms
  warm search: 5.721 ms
  rule index build: 0.133 ms
  ref index build: 0.259 ms
  shape emission: 1.202 ms
  rule lookup: 0.023 ms
  ref lookup: 0.201 ms
  tc clone: 0.006 ms
  tc apply: 1.990 ms
  candidate rules before conclusion validation: 76
  conclusion member prunes: 7
  final conclusion prunes: 14
  conclusion probes: 0
  ref pool size: 14
  per-hyp filtered ref list total: 39
  ref tuple count after filtering: 8
  full tryCandidate calls: 8
  accepted candidates: 8
  generated chain attempts: 4
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 11
  hyp definite mismatches: 0
  hyp unknown matches: 28
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=14 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    leqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=0 fallback=none
    cbv hyp=0 phase=initial depth=0 refs=3 fallback=none
    cbv hyp=1 phase=initial depth=0 refs=1 fallback=none
    cbv hyp=2 phase=initial depth=0 refs=0 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=14 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    thmR hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqTR1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    appT hyp=0 phase=initial depth=0 refs=0 fallback=none
    appT hyp=1 phase=initial depth=0 refs=1 fallback=none
    appTR2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    appTR2 hyp=1 phase=initial depth=0 refs=5 fallback=none
    appTR21 hyp=0 phase=initial depth=0 refs=0 fallback=none
    appTR21 hyp=1 phase=initial depth=0 refs=2 fallback=none
    appTR22 hyp=0 phase=initial depth=0 refs=0 fallback=none
    appTR22 hyp=1 phase=initial depth=0 refs=2 fallback=none
    eqTR2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqcT hyp=0 phase=initial depth=0 refs=1 fallback=none
    eqcT hyp=1 phase=initial depth=0 refs=1 fallback=none
    eqcT hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    eqcT hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    inst hyp=1 phase=dynamic depth=1 refs=14 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    inst hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=14 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    leqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=0 fallback=none
    cbv hyp=0 phase=initial depth=0 refs=1 fallback=none
    cbv hyp=1 phase=initial depth=0 refs=3 fallback=none
    cbv hyp=2 phase=initial depth=0 refs=0 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    leqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    leqt hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cbv hyp=0 phase=initial depth=0 refs=3 fallback=none
    cbv hyp=1 phase=initial depth=0 refs=1 fallback=none
    cbv hyp=2 phase=initial depth=0 refs=0 fallback=none
    cbv hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    cbv hyp=0 phase=dynamic depth=1 refs=3 fallback=none
    cbv hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eqTR1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    appTR2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    appTR2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    appTR21 hyp=0 phase=initial depth=0 refs=1 fallback=none
    appTR21 hyp=1 phase=initial depth=0 refs=0 fallback=none
    appTR22 hyp=0 phase=initial depth=0 refs=1 fallback=none
    appTR22 hyp=1 phase=initial depth=0 refs=0 fallback=none
    lamT hyp=0 phase=initial depth=0 refs=1 fallback=none
    lamT hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eqTR2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    lamTR hyp=0 phase=initial depth=0 refs=1 fallback=none
    lamTR hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    cbv hyp=0 phase=dynamic depth=1 refs=3 fallback=none
    cbv hyp=2 phase=dynamic depth=2 refs=0 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    EQT_ELIM hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=14 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=0 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=7 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=7 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=14 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=0 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    EQT_INTRO hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    reflt: attempts=3 accepted=3 rejected=0
    eqcT: attempts=1 accepted=1 rejected=0
    sym: attempts=1 accepted=1 rejected=0
    weaken: attempts=1 accepted=1 rejected=0
    lamT: attempts=1 accepted=1 rejected=0
    lamTR: attempts=1 accepted=1 rejected=0

auto church not definition trans auto?
  suggestions: 4
  total wall: 14.204 ms
  cold setup: 3.430 ms
  warm search: 10.606 ms
  rule index build: 0.816 ms
  ref index build: 0.020 ms
  shape emission: 2.890 ms
  rule lookup: 0.125 ms
  ref lookup: 0.675 ms
  tc clone: 0.017 ms
  tc apply: 4.116 ms
  candidate rules before conclusion validation: 615
  conclusion member prunes: 59
  final conclusion prunes: 32
  conclusion probes: 0
  ref pool size: 6
  per-hyp filtered ref list total: 114
  ref tuple count after filtering: 44
  full tryCandidate calls: 44
  accepted candidates: 28
  generated chain attempts: 27
  recursive apply calls: 0
  rejected candidates after validation: 16
  hyp syntactic matches: 87
  hyp definite mismatches: 0
  hyp unknown matches: 27
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=2 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=4 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=1 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim1 hyp=2 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=0 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=1 phase=initial depth=0 refs=4 fallback=none
    DISCH hyp=0 phase=initial depth=0 refs=1 fallback=none
    DISCH hyp=1 phase=initial depth=0 refs=1 fallback=none
    DISCH hyp=2 phase=initial depth=0 refs=1 fallback=none
    DISCH hyp=2 phase=dynamic depth=0 refs=1 fallback=none
    DISCH hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    DISCH hyp=1 phase=dynamic depth=2 refs=1 fallback=none
    specp hyp=0 phase=initial depth=0 refs=1 fallback=none
    specp hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=0 phase=initial depth=0 refs=2 fallback=none
    SPEC hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=2 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=3 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=0 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=1 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=0 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=1 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=3 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=1 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    eqmp hyp=1 phase=dynamic depth=0 refs=4 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=2 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=4 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=1 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim1 hyp=2 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=0 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=1 phase=initial depth=0 refs=4 fallback=none
    specp hyp=0 phase=initial depth=0 refs=0 fallback=none
    specp hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=0 phase=initial depth=0 refs=2 fallback=none
    SPEC hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=2 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=3 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=0 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=1 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=0 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=1 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=3 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=1 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=0 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    aeqt hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeqt hyp=1 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq1 hyp=1 phase=initial depth=0 refs=1 fallback=none
    aeq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    aeq2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq hyp=2 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=1 phase=initial depth=0 refs=0 fallback=none
    bineq1 hyp=2 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    bineq2 hyp=1 phase=initial depth=0 refs=1 fallback=none
    bineq2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=2 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=4 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=1 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim1 hyp=2 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=0 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=1 phase=initial depth=0 refs=4 fallback=none
    specp hyp=0 phase=initial depth=0 refs=0 fallback=none
    specp hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=0 phase=initial depth=0 refs=2 fallback=none
    SPEC hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=2 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=3 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=0 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=1 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=0 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=1 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=3 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=1 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=0 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=2 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=2 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=4 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=1 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim1 hyp=2 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=0 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=1 phase=initial depth=0 refs=4 fallback=none
    specp hyp=0 phase=initial depth=0 refs=0 fallback=none
    specp hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=0 phase=initial depth=0 refs=2 fallback=none
    SPEC hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=2 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=3 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=0 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=1 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=0 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=1 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=3 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONTR hyp=1 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=0 phase=initial depth=0 refs=0 fallback=none
    IMP_ANTISYM hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=6 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmp hyp=1 phase=initial depth=0 refs=4 fallback=none
    ded hyp=0 phase=initial depth=0 refs=0 fallback=none
    ded hyp=1 phase=initial depth=0 refs=0 fallback=none
    reflt hyp=0 phase=initial depth=0 refs=2 fallback=none
    reflt hyp=0 phase=dynamic depth=0 refs=2 fallback=none
    inst hyp=0 phase=initial depth=0 refs=0 fallback=none
    inst hyp=1 phase=initial depth=0 refs=2 fallback=none
    inst hyp=2 phase=initial depth=0 refs=0 fallback=none
    sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=0 phase=initial depth=0 refs=0 fallback=none
    eqmpr hyp=1 phase=initial depth=0 refs=4 fallback=none
    EQT_ELIM hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim1 hyp=1 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim1 hyp=2 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=0 phase=initial depth=0 refs=2 fallback=none
    encoded_and_elim2 hyp=1 phase=initial depth=0 refs=0 fallback=none
    encoded_and_elim2 hyp=2 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT1 hyp=0 phase=initial depth=0 refs=0 fallback=none
    CONJUNCT2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=0 phase=initial depth=0 refs=0 fallback=none
    MP hyp=1 phase=initial depth=0 refs=4 fallback=none
    specp hyp=0 phase=initial depth=0 refs=0 fallback=none
    specp hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=0 phase=initial depth=0 refs=2 fallback=none
    SPEC hyp=1 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=2 phase=initial depth=0 refs=0 fallback=none
    SPEC hyp=3 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=0 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=1 phase=initial depth=0 refs=0 fallback=none
    CHOOSE hyp=2 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=0 phase=initial depth=0 refs=0 fallback=none
    DISJ_CASES hyp=1 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    DISCH: attempts=9 accepted=9 rejected=0
    impcT: attempts=5 accepted=5 rejected=0
    proj1_eval: attempts=2 accepted=0 rejected=2
    proj2_eval: attempts=2 accepted=0 rejected=2
    weaken: attempts=7 accepted=7 rejected=0
    thmR: attempts=6 accepted=0 rejected=6
    eqTR2: attempts=8 accepted=4 rejected=4
    eqTR1: attempts=4 accepted=2 rejected=2
    eqmp: attempts=1 accepted=1 rejected=0

auto euclid final generalization auto?
  suggestions: 1
  total wall: 286.509 ms
  cold setup: 4.602 ms
  warm search: 281.730 ms
  rule index build: 0.439 ms
  ref index build: 0.587 ms
  shape emission: 134.388 ms
  rule lookup: 3.063 ms
  ref lookup: 36.968 ms
  tc clone: 0.140 ms
  tc apply: 43.460 ms
  candidate rules before conclusion validation: 10540
  conclusion member prunes: 661
  final conclusion prunes: 47
  conclusion probes: 0
  ref pool size: 22
  per-hyp filtered ref list total: 7370
  ref tuple count after filtering: 100
  full tryCandidate calls: 100
  accepted candidates: 15
  generated chain attempts: 646
  recursive apply calls: 0
  rejected candidates after validation: 85
  hyp syntactic matches: 4637
  hyp definite mismatches: 702
  hyp unknown matches: 2031
  recover member injections: 4914
  split context guard rejects: 745
  acui witness attempts: 0
  recover guard rejects (match/extract): 638/20
  metas created (wild/exist/univ/bound): 0/2/3/0
  meta assignments: 0
  meta rollbacks: 2
  derived refs: 12
  forward rule attempts: 199
  forward match tuples: 15
  forward layers run: 3
  forward saturation exhausted: true
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    all_intro_sub hyp=0 phase=initial depth=0 refs=7 fallback=none
    all_intro_sub hyp=0 phase=dynamic depth=0 refs=7 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=7 fallback=none
    peano5 hyp=0 phase=initial depth=0 refs=7 fallback=none
    peano5 hyp=1 phase=initial depth=0 refs=0 fallback=none
    peano5_strong hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=7 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_intro_sub hyp=0 phase=initial depth=0 refs=7 fallback=none
    all_intro_sub hyp=0 phase=dynamic depth=0 refs=7 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=7 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=7 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=7 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    peano5 hyp=0 phase=initial depth=0 refs=7 fallback=none
    peano5 hyp=1 phase=initial depth=0 refs=0 fallback=none
    peano5 hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_intro_sub hyp=0 phase=initial depth=0 refs=7 fallback=none
    all_intro_sub hyp=0 phase=dynamic depth=0 refs=7 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=7 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    peano5 hyp=0 phase=initial depth=0 refs=7 fallback=none
    peano5 hyp=1 phase=initial depth=0 refs=0 fallback=none
    peano5 hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    peano5_strong hyp=0 phase=initial depth=0 refs=0 fallback=none
    peano5_strong hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    peano5_strong hyp=0 phase=initial depth=0 refs=0 fallback=none
    peano5_strong hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=7 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    all_intro_sub: attempts=40 accepted=13 rejected=27
    bot_elim: attempts=17 accepted=0 rejected=17
    all_elim: attempts=2 accepted=0 rejected=2
    ex_elim_sub: attempts=14 accepted=2 rejected=12
    or_elim: attempts=27 accepted=0 rejected=27

auto zermelo image preimage auto?
  suggestions: 1
  total wall: 258.308 ms
  cold setup: 8.800 ms
  warm search: 249.220 ms
  rule index build: 1.073 ms
  ref index build: 0.422 ms
  shape emission: 96.979 ms
  rule lookup: 2.641 ms
  ref lookup: 8.549 ms
  tc clone: 0.086 ms
  tc apply: 108.093 ms
  candidate rules before conclusion validation: 5481
  conclusion member prunes: 384
  final conclusion prunes: 61
  conclusion probes: 0
  ref pool size: 11
  per-hyp filtered ref list total: 1853
  ref tuple count after filtering: 27
  full tryCandidate calls: 27
  accepted candidates: 13
  generated chain attempts: 367
  recursive apply calls: 0
  rejected candidates after validation: 14
  hyp syntactic matches: 1607
  hyp definite mismatches: 114
  hyp unknown matches: 132
  recover member injections: 0
  split context guard rejects: 1176
  acui witness attempts: 0
  recover guard rejects (match/extract): 80/173
  metas created (wild/exist/univ/bound): 0/0/4/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 10
  forward rule attempts: 49
  forward match tuples: 12
  forward layers run: 3
  forward saturation exhausted: true
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=11 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=11 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=11 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=2 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim hyp=0 phase=dynamic depth=1 refs=2 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=4 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    has_preimage_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    has_preimage_intro hyp=1 phase=initial depth=0 refs=1 fallback=none
    has_preimage_intro hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    has_preimage_intro hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    image_has_preimage hyp=0 phase=initial depth=0 refs=0 fallback=none
    surj_has_preimage hyp=0 phase=initial depth=0 refs=0 fallback=none
    surj_has_preimage hyp=1 phase=initial depth=0 refs=6 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=11 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=11 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=11 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=11 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=2 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=4 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=1 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=1 phase=initial depth=0 refs=6 fallback=none
    cantor_out_case hyp=2 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=3 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    image_has_preimage hyp=0 phase=initial depth=0 refs=0 fallback=none
    image_has_preimage hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=11 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=dynamic depth=1 refs=1 fallback=none
    or_elim hyp=0 phase=dynamic depth=2 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=2 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim hyp=0 phase=dynamic depth=1 refs=2 fallback=none
    has_preimage_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    has_preimage_intro hyp=1 phase=initial depth=0 refs=1 fallback=none
    has_preimage_intro hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    has_preimage_intro hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    surj_has_preimage hyp=0 phase=initial depth=0 refs=0 fallback=none
    surj_has_preimage hyp=1 phase=initial depth=0 refs=6 fallback=none
    surj_has_preimage hyp=1 phase=dynamic depth=0 refs=6 fallback=none
    surj_has_preimage hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    surj_has_preimage hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=11 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=11 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=11 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=11 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=11 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
  full validation attempts by rule:
    ex_elim: attempts=26 accepted=13 rejected=13
    all_elim: attempts=1 accepted=0 rejected=1

auto zermelo cb surjection auto?
  suggestions: 1
  total wall: 410.759 ms
  cold setup: 2.883 ms
  warm search: 407.546 ms
  rule index build: 1.250 ms
  ref index build: 0.692 ms
  shape emission: 264.595 ms
  rule lookup: 3.401 ms
  ref lookup: 38.766 ms
  tc clone: 0.010 ms
  tc apply: 10.493 ms
  candidate rules before conclusion validation: 12962
  conclusion member prunes: 433
  final conclusion prunes: 3771
  conclusion probes: 0
  ref pool size: 3
  per-hyp filtered ref list total: 1616
  ref tuple count after filtering: 16
  full tryCandidate calls: 16
  accepted candidates: 13
  generated chain attempts: 394
  recursive apply calls: 0
  rejected candidates after validation: 3
  hyp syntactic matches: 1616
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 1113
  acui witness attempts: 0
  recover guard rejects (match/extract): 580/1070
  metas created (wild/exist/univ/bound): 0/0/10/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 26
  forward rule attempts: 72
  forward match tuples: 26
  forward layers run: 3
  forward saturation exhausted: true
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=2 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    cb_bijection_surj_body hyp=0 phase=initial depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=1 phase=initial depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=2 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=1 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=1 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=2 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=3 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=2 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    cb_bijection_surj_body hyp=0 phase=initial depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=1 phase=initial depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    cb_bijection_surj_body hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
  full validation attempts by rule:
    cb_bijection_surj_body: attempts=13 accepted=13 rejected=0
    nd_imp_id: attempts=3 accepted=0 rejected=3

auto martin_lof add_comm id_trans auto?
  suggestions: 4
  total wall: 143.654 ms
  cold setup: 2.386 ms
  warm search: 140.845 ms
  rule index build: 1.020 ms
  ref index build: 0.571 ms
  shape emission: 1.812 ms
  rule lookup: 0.072 ms
  ref lookup: 1.438 ms
  tc clone: 0.015 ms
  tc apply: 131.992 ms
  candidate rules before conclusion validation: 65
  conclusion member prunes: 7
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 21
  per-hyp filtered ref list total: 69
  ref tuple count after filtering: 29
  full tryCandidate calls: 29
  accepted candidates: 8
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 21
  hyp syntactic matches: 20
  hyp definite mismatches: 30
  hyp unknown matches: 19
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=21 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=8 fallback=none
    app_elim hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    id_trans_ty hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=21 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=8 fallback=none
    app_elim hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    id_trans_ty hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=21 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=1 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    eq_tm_to_Id hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_tm_to_Id hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=21 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=1 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=8 fallback=none
    app_elim hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    app_elim hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=1 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    id_trans_ty hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    id_trans_ty hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=21 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=1 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=1 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=3 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=3 fallback=none
    eq_tm_to_Id hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_tm_to_Id hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    app_elim: attempts=9 accepted=0 rejected=9
    id_trans_ty: attempts=6 accepted=6 rejected=0
    weaken: attempts=3 accepted=0 rejected=3
    weaken2: attempts=3 accepted=0 rejected=3
    weaken3: attempts=3 accepted=0 rejected=3
    exchange: attempts=3 accepted=0 rejected=3
    eq_tm_to_Id: attempts=2 accepted=2 rejected=0

auto martin_lof add_comm capstone auto? (no result)
  suggestions: 0
  total wall: 7.935 ms
  cold setup: 2.485 ms
  warm search: 5.124 ms
  rule index build: 1.015 ms
  ref index build: 0.646 ms
  shape emission: 2.452 ms
  rule lookup: 0.231 ms
  ref lookup: 0.265 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 156
  conclusion member prunes: 65
  final conclusion prunes: 12
  conclusion probes: 0
  ref pool size: 22
  per-hyp filtered ref list total: 121
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 108
  hyp unknown matches: 13
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    nat_ind_elim hyp=2 phase=dynamic depth=1 refs=4 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=22 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=4 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=12 fallback=none
    nat_ind_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=4 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=4 fallback=none

auto martin_lof add_comm id_trans deep auto?
  suggestions: 1
  total wall: 39.666 ms
  cold setup: 2.223 ms
  warm search: 37.077 ms
  rule index build: 1.016 ms
  ref index build: 0.339 ms
  shape emission: 4.835 ms
  rule lookup: 0.175 ms
  ref lookup: 1.383 ms
  tc clone: 0.024 ms
  tc apply: 22.194 ms
  candidate rules before conclusion validation: 233
  conclusion member prunes: 17
  final conclusion prunes: 2
  conclusion probes: 0
  ref pool size: 16
  per-hyp filtered ref list total: 67
  ref tuple count after filtering: 54
  full tryCandidate calls: 54
  accepted candidates: 20
  generated chain attempts: 15
  recursive apply calls: 0
  rejected candidates after validation: 34
  hyp syntactic matches: 30
  hyp definite mismatches: 0
  hyp unknown matches: 37
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    id_sym_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    ap_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    ap_ty hyp=1 phase=initial depth=0 refs=1 fallback=none
    ap_suc_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    app_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    app_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    app_elim hyp=1 phase=dynamic depth=0 refs=3 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    app_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=initial depth=0 refs=0 fallback=none
    id_trans_ty hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=2 phase=dynamic depth=0 refs=1 fallback=none
    id_sym_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    id_sym_ty hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    nat_ind_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    nat_ind_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    nat_ind_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    nat_ind_elim hyp=3 phase=initial depth=0 refs=2 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    add_suc_right hyp=0 phase=initial depth=0 refs=1 fallback=none
    add_suc_right hyp=1 phase=initial depth=0 refs=1 fallback=none
    add_suc_right hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    add_suc_right hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    ap_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    ap_ty hyp=1 phase=initial depth=0 refs=1 fallback=none
    ap_ty hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ap_suc_ty hyp=0 phase=initial depth=0 refs=0 fallback=none
    ap_suc_ty hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    id_trans_ty hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=16 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    add_suc_right: attempts=1 accepted=1 rejected=0
    id_sym_ty: attempts=1 accepted=1 rejected=0
    ap_suc_ty: attempts=2 accepted=2 rejected=0
    weaken: attempts=10 accepted=3 rejected=7
    weaken2: attempts=10 accepted=2 rejected=8
    weaken3: attempts=10 accepted=0 rejected=10
    var: attempts=2 accepted=1 rejected=1
    exchange: attempts=8 accepted=0 rejected=8
    id_trans_ty: attempts=2 accepted=2 rejected=0
    eq_tm_to_Id: attempts=2 accepted=2 rejected=0
    eq_tm_sym: attempts=2 accepted=2 rejected=0
    add_suc_left: attempts=4 accepted=4 rejected=0

auto martin_lof id_sym_ty J_elim auto? (no result)
  suggestions: 0
  total wall: 5.817 ms
  cold setup: 1.778 ms
  warm search: 3.966 ms
  rule index build: 0.293 ms
  ref index build: 0.039 ms
  shape emission: 1.883 ms
  rule lookup: 0.158 ms
  ref lookup: 0.421 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 432
  conclusion member prunes: 95
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 7
  per-hyp filtered ref list total: 10
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 30
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 10
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ty_conv hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ty_conv hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=1 fallback=none
    ty_conv hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    ty_conv hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_ty_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_ty_trans hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken2 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=initial depth=0 refs=0 fallback=none
    weaken3 hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    exchange hyp=0 phase=initial depth=0 refs=0 fallback=none
    exchange hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=1 phase=initial depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_left_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=initial depth=0 refs=0 fallback=none
    Id_right_regular hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    J_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    J_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    J_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    jiff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    jiff_mp hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    jiff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_left hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_tm_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ty_conv hyp=0 phase=initial depth=0 refs=0 fallback=none

auto zermelo nested all_intro auto?
  suggestions: 1
  total wall: 69.983 ms
  cold setup: 5.407 ms
  warm search: 64.349 ms
  rule index build: 0.905 ms
  ref index build: 0.303 ms
  shape emission: 3.223 ms
  rule lookup: 0.084 ms
  ref lookup: 0.350 ms
  tc clone: 0.023 ms
  tc apply: 58.553 ms
  candidate rules before conclusion validation: 134
  conclusion member prunes: 9
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 7
  per-hyp filtered ref list total: 116
  ref tuple count after filtering: 18
  full tryCandidate calls: 18
  accepted candidates: 3
  generated chain attempts: 6
  recursive apply calls: 0
  rejected candidates after validation: 15
  hyp syntactic matches: 97
  hyp definite mismatches: 0
  hyp unknown matches: 19
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=dynamic depth=1 refs=3 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    function_functional hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=dynamic depth=1 refs=3 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=1 phase=initial depth=0 refs=2 fallback=none
    cantor_in_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=1 phase=initial depth=0 refs=2 fallback=none
    cantor_out_case hyp=2 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=3 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=dynamic depth=1 refs=3 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    function_functional hyp=0 phase=initial depth=0 refs=0 fallback=none
    function_functional hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=7 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=7 fallback=none
    not_elim hyp=1 phase=dynamic depth=0 refs=7 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    cantor_in_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_in_case hyp=1 phase=initial depth=0 refs=2 fallback=none
    cantor_in_case hyp=1 phase=dynamic depth=0 refs=2 fallback=none
    cantor_in_case hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    cantor_in_case hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    cantor_out_case hyp=0 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=1 phase=initial depth=0 refs=2 fallback=none
    cantor_out_case hyp=2 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=3 phase=initial depth=0 refs=0 fallback=none
    cantor_out_case hyp=1 phase=dynamic depth=0 refs=2 fallback=none
    cantor_out_case hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    cantor_out_case hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    all_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=7 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    eq_replace: attempts=15 accepted=0 rejected=15
    all_intro: attempts=3 accepted=3 rejected=0

auto zermelo_hilbert imp_id auto? (no result)
  suggestions: 0
  total wall: 1.124 ms
  cold setup: 0.958 ms
  warm search: 0.111 ms
  rule index build: 0.031 ms
  ref index build: 0.000 ms
  shape emission: 0.033 ms
  rule lookup: 0.008 ms
  ref lookup: 0.004 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 26
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none

auto nd_eq_subst_mem double imp_intro auto?
  suggestions: 1
  total wall: 3.435 ms
  cold setup: 2.057 ms
  warm search: 1.311 ms
  rule index build: 0.336 ms
  ref index build: 0.010 ms
  shape emission: 0.136 ms
  rule lookup: 0.009 ms
  ref lookup: 0.044 ms
  tc clone: 0.011 ms
  tc apply: 0.588 ms
  candidate rules before conclusion validation: 58
  conclusion member prunes: 6
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 3
  per-hyp filtered ref list total: 5
  ref tuple count after filtering: 5
  full tryCandidate calls: 5
  accepted candidates: 2
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 3
  hyp syntactic matches: 5
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=3 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=3 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=3 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    eq_replace hyp=1 phase=dynamic depth=1 refs=3 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=3 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    empty_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=initial depth=0 refs=0 fallback=none
    sep_elim_right hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    imp_intro: attempts=2 accepted=2 rejected=0
    eq_replace: attempts=3 accepted=0 rejected=3

hyp-only witness auto? (Stage 4 open backward)
  suggestions: 1
  total wall: 0.173 ms
  cold setup: 0.121 ms
  warm search: 0.036 ms
  rule index build: 0.002 ms
  ref index build: 0.000 ms
  shape emission: 0.001 ms
  rule lookup: 0.001 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.008 ms
  candidate rules before conclusion validation: 3
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 1
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 1
  meta rollbacks: 1
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    hyp_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    hyp_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    pred_K: attempts=1 accepted=1 rejected=0
    hyp_only_use: attempts=1 accepted=1 rejected=0

generated child pins parent auto? (Stage 4 open backward)
  suggestions: 1
  total wall: 0.196 ms
  cold setup: 0.129 ms
  warm search: 0.052 ms
  rule index build: 0.003 ms
  ref index build: 0.000 ms
  shape emission: 0.003 ms
  rule lookup: 0.002 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.008 ms
  candidate rules before conclusion validation: 6
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/3/0/0
  meta assignments: 2
  meta rollbacks: 3
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    generated_child_parent hyp=0 phase=initial depth=0 refs=0 fallback=none
    generated_child_parent hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    generated_child_parent hyp=0 phase=initial depth=0 refs=0 fallback=none
    generated_child_parent hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    child_from_mark hyp=0 phase=initial depth=0 refs=0 fallback=none
    child_from_mark hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    mark_K: attempts=1 accepted=1 rejected=0
    child_from_mark: attempts=1 accepted=1 rejected=0
    generated_child_parent: attempts=1 accepted=1 rejected=0

repeated unknown auto? (Stage 4 open backward)
  suggestions: 1
  total wall: 0.185 ms
  cold setup: 0.130 ms
  warm search: 0.039 ms
  rule index build: 0.004 ms
  ref index build: 0.000 ms
  shape emission: 0.002 ms
  rule lookup: 0.002 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.005 ms
  candidate rules before conclusion validation: 4
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 1
  meta rollbacks: 1
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    repeated_unknown_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    repeated_unknown_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    repeated_unknown_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    repeated_unknown_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
  full validation attempts by rule:
    left_K: attempts=1 accepted=1 rejected=0
    right_K: attempts=1 accepted=1 rejected=0
    repeated_unknown_use: attempts=1 accepted=1 rejected=0

inconsistent repeated unknown auto? (no result, Stage 4)
  suggestions: 0
  total wall: 0.329 ms
  cold setup: 0.132 ms
  warm search: 0.183 ms
  rule index build: 0.006 ms
  ref index build: 0.000 ms
  shape emission: 0.023 ms
  rule lookup: 0.025 ms
  ref lookup: 0.003 ms
  tc clone: 0.004 ms
  tc apply: 0.008 ms
  candidate rules before conclusion validation: 25
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 12
  full tryCandidate calls: 12
  accepted candidates: 12
  generated chain attempts: 24
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/12/0/0
  meta assignments: 12
  meta rollbacks: 24
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=initial depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    inconsistent_repeated_use hyp=1 phase=dynamic depth=1 refs=0 fallback=none
  full validation attempts by rule:
    bad_left_K: attempts=12 accepted=12 rejected=0

bound @vars choice auto? (Stage 4 open backward)
  suggestions: 2
  total wall: 0.183 ms
  cold setup: 0.127 ms
  warm search: 0.042 ms
  rule index build: 0.005 ms
  ref index build: 0.000 ms
  shape emission: 0.001 ms
  rule lookup: 0.002 ms
  ref lookup: 0.000 ms
  tc clone: 0.000 ms
  tc apply: 0.010 ms
  candidate rules before conclusion validation: 4
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 4
  full tryCandidate calls: 4
  accepted candidates: 4
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    bound_choice_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_choice_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    pred_any: attempts=2 accepted=2 rejected=0
    bound_choice_use: attempts=2 accepted=2 rejected=0

missing @vars witness auto? (no result, Stage 4)
  suggestions: 0
  total wall: 0.198 ms
  cold setup: 0.142 ms
  warm search: 0.041 ms
  rule index build: 0.009 ms
  ref index build: 0.000 ms
  shape emission: 0.008 ms
  rule lookup: 0.004 ms
  ref lookup: 0.001 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 13
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    bound_missing_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none

euclid ex_intro open witness auto? (Stage 4 open backward)
  suggestions: 1
  total wall: 2.517 ms
  cold setup: 1.371 ms
  warm search: 1.074 ms
  rule index build: 0.414 ms
  ref index build: 0.001 ms
  shape emission: 0.143 ms
  rule lookup: 0.011 ms
  ref lookup: 0.012 ms
  tc clone: 0.005 ms
  tc apply: 0.248 ms
  candidate rules before conclusion validation: 90
  conclusion member prunes: 5
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 8
  full tryCandidate calls: 8
  accepted candidates: 6
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 2
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 1
  meta rollbacks: 2
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 1
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    add_cancel_left_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    add_cancel_left_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_sym_nd hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_sym_nd hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_antisym_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_antisym_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_antisym_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dvd_zero_imp_eq_zero_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_zero_imp_eq_zero_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=0 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    eq_intro_nd: attempts=1 accepted=1 rejected=0
    add_0_ax: attempts=1 accepted=1 rejected=0
    mul_0_ax: attempts=1 accepted=0 rejected=1
    add_zero_left_ax: attempts=1 accepted=1 rejected=0
    mul_zero_left_ax: attempts=1 accepted=0 rejected=1
    mul_one_left_ax: attempts=1 accepted=1 rejected=0
    mul_one_right_ax: attempts=1 accepted=1 rejected=0
    ex_intro: attempts=1 accepted=1 rejected=0

unannotated rule auto? (no result, Stage 4 gate)
  suggestions: 0
  total wall: 0.214 ms
  cold setup: 0.147 ms
  warm search: 0.043 ms
  rule index build: 0.010 ms
  ref index build: 0.000 ms
  shape emission: 0.008 ms
  rule lookup: 0.004 ms
  ref lookup: 0.001 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 13
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=initial depth=0 refs=0 fallback=none
    plain_only_use hyp=0 phase=dynamic depth=0 refs=0 fallback=none

bare-meta target auto? (no result, Stage 4 guard)
  suggestions: 0
  total wall: 0.205 ms
  cold setup: 0.142 ms
  warm search: 0.045 ms
  rule index build: 0.008 ms
  ref index build: 0.000 ms
  shape emission: 0.007 ms
  rule lookup: 0.004 ms
  ref lookup: 0.001 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 13
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/12/0/0
  meta assignments: 0
  meta rollbacks: 12
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    bare_meta_use hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape

recover-owned fallback auto? (no result, Stage 4)
  suggestions: 0
  total wall: 0.203 ms
  cold setup: 0.148 ms
  warm search: 0.042 ms
  rule index build: 0.008 ms
  ref index build: 0.000 ms
  shape emission: 0.005 ms
  rule lookup: 0.004 ms
  ref lookup: 0.001 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 13
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 0
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 0
  forward rule attempts: 0
  forward match tuples: 0
  forward layers run: 0
  forward saturation exhausted: false
  hyp lookup diagnostics:
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=initial depth=0 refs=0 fallback=broad_shape
    recover_cannot_fire hyp=0 phase=dynamic depth=0 refs=0 fallback=broad_shape

all_elim forward instantiation auto? (Stage 7 forward)
  suggestions: 2
  total wall: 0.697 ms
  cold setup: 0.245 ms
  warm search: 0.432 ms
  rule index build: 0.029 ms
  ref index build: 0.017 ms
  shape emission: 0.013 ms
  rule lookup: 0.003 ms
  ref lookup: 0.014 ms
  tc clone: 0.000 ms
  tc apply: 0.285 ms
  candidate rules before conclusion validation: 4
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 2
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 2
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/2
  metas created (wild/exist/univ/bound): 0/0/2/0
  meta assignments: 3
  meta rollbacks: 2
  derived refs: 2
  forward rule attempts: 3
  forward match tuples: 2
  forward layers run: 3
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=2 rejected=0

all_elim single-step instantiation auto? (supported boundary)
  suggestions: 2
  total wall: 0.525 ms
  cold setup: 0.236 ms
  warm search: 0.270 ms
  rule index build: 0.035 ms
  ref index build: 0.007 ms
  shape emission: 0.030 ms
  rule lookup: 0.006 ms
  ref lookup: 0.016 ms
  tc clone: 0.000 ms
  tc apply: 0.104 ms
  candidate rules before conclusion validation: 23
  conclusion member prunes: 4
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 4
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 2
  hyp definite mismatches: 2
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 2/0
  metas created (wild/exist/univ/bound): 0/0/1/0
  meta assignments: 1
  meta rollbacks: 1
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    eq_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=0 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=1 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    pair_congr hyp=0 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=1 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    pair_congr hyp=0 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=1 phase=initial depth=0 refs=0 fallback=none
    pair_congr hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_trans hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_sym hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=3 accepted=3 rejected=0

all_elim two-layer derived direct auto? (Stage 8 forward)
  suggestions: 2
  total wall: 0.676 ms
  cold setup: 0.239 ms
  warm search: 0.419 ms
  rule index build: 0.027 ms
  ref index build: 0.023 ms
  shape emission: 0.013 ms
  rule lookup: 0.003 ms
  ref lookup: 0.007 ms
  tc clone: 0.000 ms
  tc apply: 0.280 ms
  candidate rules before conclusion validation: 4
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 2
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 2
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/2
  metas created (wild/exist/univ/bound): 0/0/2/0
  meta assignments: 3
  meta rollbacks: 2
  derived refs: 2
  forward rule attempts: 3
  forward match tuples: 2
  forward layers run: 3
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=2 rejected=0

all_elim three-layer chain auto? (Stage 8 forward)
  suggestions: 2
  total wall: 1.000 ms
  cold setup: 0.265 ms
  warm search: 0.715 ms
  rule index build: 0.034 ms
  ref index build: 0.025 ms
  shape emission: 0.016 ms
  rule lookup: 0.004 ms
  ref lookup: 0.008 ms
  tc clone: 0.000 ms
  tc apply: 0.529 ms
  candidate rules before conclusion validation: 6
  conclusion member prunes: 2
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 2
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 2
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 2
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 1/2
  metas created (wild/exist/univ/bound): 0/0/3/0
  meta assignments: 5
  meta rollbacks: 2
  derived refs: 3
  forward rule attempts: 3
  forward match tuples: 3
  forward layers run: 3
  forward saturation exhausted: true
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=2 rejected=0

euclid le_total two-layer instantiation auto? (Stage 8)
  suggestions: 1
  total wall: 3.392 ms
  cold setup: 1.491 ms
  warm search: 1.826 ms
  rule index build: 0.330 ms
  ref index build: 0.026 ms
  shape emission: 0.585 ms
  rule lookup: 0.030 ms
  ref lookup: 0.133 ms
  tc clone: 0.001 ms
  tc apply: 0.316 ms
  candidate rules before conclusion validation: 133
  conclusion member prunes: 12
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 13
  ref tuple count after filtering: 2
  full tryCandidate calls: 2
  accepted candidates: 1
  generated chain attempts: 6
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 3
  hyp definite mismatches: 10
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 20/0
  metas created (wild/exist/univ/bound): 0/0/2/0
  meta assignments: 3
  meta rollbacks: 2
  derived refs: 2
  forward rule attempts: 10
  forward match tuples: 2
  forward layers run: 3
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_intro_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=1 rejected=1

euclid prime-factor instance auto? (Stage 8 forward)
  suggestions: 2
  total wall: 5.160 ms
  cold setup: 1.750 ms
  warm search: 3.266 ms
  rule index build: 0.399 ms
  ref index build: 0.063 ms
  shape emission: 1.513 ms
  rule lookup: 0.048 ms
  ref lookup: 0.132 ms
  tc clone: 0.002 ms
  tc apply: 0.560 ms
  candidate rules before conclusion validation: 127
  conclusion member prunes: 8
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 10
  ref tuple count after filtering: 3
  full tryCandidate calls: 3
  accepted candidates: 3
  generated chain attempts: 6
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 5
  hyp definite mismatches: 5
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 5/0
  metas created (wild/exist/univ/bound): 0/0/1/0
  meta assignments: 1
  meta rollbacks: 1
  derived refs: 1
  forward rule attempts: 7
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_intro hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_intro hyp=1 phase=initial depth=0 refs=0 fallback=none
    bi_intro hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dne hyp=0 phase=initial depth=0 refs=0 fallback=none
    dne hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    all_elim: attempts=3 accepted=3 rejected=0

euclid dvd_fact and_elim chain auto? (Stage 8 forward)
  suggestions: 3
  total wall: 5.662 ms
  cold setup: 1.684 ms
  warm search: 3.866 ms
  rule index build: 0.348 ms
  ref index build: 0.047 ms
  shape emission: 0.480 ms
  rule lookup: 0.015 ms
  ref lookup: 0.286 ms
  tc clone: 0.009 ms
  tc apply: 2.130 ms
  candidate rules before conclusion validation: 106
  conclusion member prunes: 6
  final conclusion prunes: 5
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 8
  ref tuple count after filtering: 10
  full tryCandidate calls: 10
  accepted candidates: 5
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 5
  hyp syntactic matches: 5
  hyp definite mismatches: 3
  hyp unknown matches: 0
  recover member injections: 8
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 7/0
  metas created (wild/exist/univ/bound): 0/1/0/0
  meta assignments: 0
  meta rollbacks: 1
  derived refs: 2
  forward rule attempts: 10
  forward match tuples: 2
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    le_iff_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    lt_from_suc_le hyp=0 phase=initial depth=0 refs=0 fallback=none
    suc_le_from_lt hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    pos_of_one_lt_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    not_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    not_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    not_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=1 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=1 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=1 fallback=none
    or_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    ex_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    add_cancel_left_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    add_cancel_left_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    mul_cancel_left_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    eq_sym_nd hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_sym_nd hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_antisym_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_antisym_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_antisym_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    and_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    bot_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_intro hyp=0 phase=initial depth=0 refs=1 fallback=none
    ex_intro hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    eq_replace hyp=0 phase=initial depth=0 refs=0 fallback=none
    eq_replace hyp=1 phase=initial depth=0 refs=1 fallback=none
    eq_replace hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_iff_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_from_suc_le hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_from_suc_le hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    suc_le_from_lt hyp=0 phase=initial depth=0 refs=0 fallback=none
    suc_le_from_lt hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    pos_of_one_lt_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    pos_of_one_lt_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_from_add hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_from_suc_le hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_from_suc_le hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    suc_le_from_lt hyp=0 phase=initial depth=0 refs=0 fallback=none
    suc_le_from_lt hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_implies_le_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    pos_of_one_lt_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    pos_of_one_lt_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    or_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=2 phase=initial depth=0 refs=0 fallback=none
    or_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    bi_elim_l hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_l hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_l hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_l hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=initial depth=0 refs=0 fallback=none
    bi_elim_r hyp=1 phase=initial depth=0 refs=1 fallback=none
    bi_elim_r hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    bi_elim_r hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim_sub hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim_sub hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    ex_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    ex_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    le_trans_ax hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    le_trans_ax hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    le_trans_ax hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    dvd_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=initial depth=0 refs=0 fallback=none
    dvd_elim hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=1 phase=initial depth=0 refs=0 fallback=none
    lt_of_le_ne_ax hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    dvd_pos_imp_le_ax hyp=0 phase=initial depth=0 refs=0 fallback=none
  full validation attempts by rule:
    ax: attempts=1 accepted=0 rejected=1
    lt_from_suc_le: attempts=2 accepted=0 rejected=2
    lt_implies_le_ax: attempts=2 accepted=2 rejected=0
    pos_of_one_lt_ax: attempts=2 accepted=2 rejected=0
    le_iff_add: attempts=1 accepted=1 rejected=0
    suc_le_from_lt: attempts=1 accepted=0 rejected=1
    le_trans_ax: attempts=1 accepted=0 rejected=1

fwd/bwd compose hilbert minor-in-pool auto? (Stage 4+7)
  suggestions: 2
  total wall: 0.618 ms
  cold setup: 0.217 ms
  warm search: 0.379 ms
  rule index build: 0.042 ms
  ref index build: 0.005 ms
  shape emission: 0.015 ms
  rule lookup: 0.003 ms
  ref lookup: 0.014 ms
  tc clone: 0.003 ms
  tc apply: 0.224 ms
  candidate rules before conclusion validation: 13
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 2
  per-hyp filtered ref list total: 5
  ref tuple count after filtering: 5
  full tryCandidate calls: 5
  accepted candidates: 4
  generated chain attempts: 2
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 2
  hyp definite mismatches: 3
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 3/0
  metas created (wild/exist/univ/bound): 0/1/1/0
  meta assignments: 2
  meta rollbacks: 2
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=1 phase=dynamic depth=1 refs=1 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=1 rejected=1
    mp: attempts=2 accepted=2 rejected=0
    P_K: attempts=1 accepted=1 rejected=0

fwd/bwd compose hilbert open-minor auto? (Stage 4+7)
  suggestions: 2
  total wall: 0.565 ms
  cold setup: 0.214 ms
  warm search: 0.333 ms
  rule index build: 0.028 ms
  ref index build: 0.005 ms
  shape emission: 0.024 ms
  rule lookup: 0.004 ms
  ref lookup: 0.017 ms
  tc clone: 0.001 ms
  tc apply: 0.162 ms
  candidate rules before conclusion validation: 19
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 6
  ref tuple count after filtering: 6
  full tryCandidate calls: 6
  accepted candidates: 5
  generated chain attempts: 3
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 2
  hyp definite mismatches: 4
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 4/0
  metas created (wild/exist/univ/bound): 0/1/1/0
  meta assignments: 2
  meta rollbacks: 2
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    fwd_bwd_minor_in_pool hyp=0 phase=initial depth=0 refs=1 fallback=none
    fwd_bwd_minor_in_pool hyp=1 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    mp hyp=1 phase=dynamic depth=1 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    fwd_bwd_minor_in_pool hyp=0 phase=initial depth=0 refs=1 fallback=none
    fwd_bwd_minor_in_pool hyp=1 phase=initial depth=0 refs=0 fallback=none
    fwd_bwd_minor_in_pool hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    fwd_bwd_minor_in_pool hyp=0 phase=dynamic depth=1 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=2 accepted=1 rejected=1
    P_K: attempts=2 accepted=2 rejected=0
    mp: attempts=1 accepted=1 rejected=0
    fwd_bwd_minor_in_pool: attempts=1 accepted=1 rejected=0

fwd/bwd compose hilbert forward-direct auto? (Stage 7)
  suggestions: 2
  total wall: 0.511 ms
  cold setup: 0.221 ms
  warm search: 0.271 ms
  rule index build: 0.024 ms
  ref index build: 0.008 ms
  shape emission: 0.014 ms
  rule lookup: 0.003 ms
  ref lookup: 0.011 ms
  tc clone: 0.002 ms
  tc apply: 0.163 ms
  candidate rules before conclusion validation: 9
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 3
  ref tuple count after filtering: 4
  full tryCandidate calls: 4
  accepted candidates: 3
  generated chain attempts: 1
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 3
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/1/1/0
  meta assignments: 1
  meta rollbacks: 2
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    iff_mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    iff_mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    iff_mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mp hyp=0 phase=initial depth=0 refs=0 fallback=none
    mp hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mp hyp=0 phase=dynamic depth=0 refs=0 fallback=none
  full validation attempts by rule:
    all_elim: attempts=4 accepted=3 rejected=1

fwd/bwd compose nd minor-in-pool auto? (Stage 4+7)
  suggestions: 2
  total wall: 1.188 ms
  cold setup: 0.311 ms
  warm search: 0.857 ms
  rule index build: 0.043 ms
  ref index build: 0.018 ms
  shape emission: 0.071 ms
  rule lookup: 0.008 ms
  ref lookup: 0.033 ms
  tc clone: 0.002 ms
  tc apply: 0.476 ms
  candidate rules before conclusion validation: 25
  conclusion member prunes: 6
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 2
  per-hyp filtered ref list total: 8
  ref tuple count after filtering: 8
  full tryCandidate calls: 8
  accepted candidates: 7
  generated chain attempts: 4
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 5
  hyp definite mismatches: 3
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 3/0
  metas created (wild/exist/univ/bound): 0/1/1/0
  meta assignments: 3
  meta rollbacks: 3
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=2 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=2 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=2 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    all_elim: attempts=5 accepted=4 rejected=1
    imp_elim: attempts=2 accepted=2 rejected=0
    P_K_nd: attempts=1 accepted=1 rejected=0

fwd/bwd compose nd open-minor auto? (Stage 4+7)
  suggestions: 2
  total wall: 0.964 ms
  cold setup: 0.314 ms
  warm search: 0.631 ms
  rule index build: 0.048 ms
  ref index build: 0.009 ms
  shape emission: 0.056 ms
  rule lookup: 0.007 ms
  ref lookup: 0.034 ms
  tc clone: 0.001 ms
  tc apply: 0.306 ms
  candidate rules before conclusion validation: 29
  conclusion member prunes: 6
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 1
  per-hyp filtered ref list total: 8
  ref tuple count after filtering: 7
  full tryCandidate calls: 7
  accepted candidates: 6
  generated chain attempts: 4
  recursive apply calls: 0
  rejected candidates after validation: 1
  hyp syntactic matches: 4
  hyp definite mismatches: 4
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 4/0
  metas created (wild/exist/univ/bound): 0/1/1/0
  meta assignments: 2
  meta rollbacks: 2
  derived refs: 1
  forward rule attempts: 2
  forward match tuples: 1
  forward layers run: 2
  forward saturation exhausted: false
  hyp lookup diagnostics:
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=0 phase=initial depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=1 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=0 phase=initial depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=1 phase=initial depth=0 refs=0 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=0 phase=dynamic depth=1 refs=1 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=1 phase=dynamic depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=0 phase=initial depth=0 refs=1 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=1 phase=initial depth=0 refs=0 fallback=none
    nd_fwd_bwd_minor_in_pool hyp=1 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=dynamic depth=1 refs=0 fallback=none
    mpbi hyp=0 phase=initial depth=0 refs=0 fallback=none
    mpbi hyp=1 phase=initial depth=0 refs=1 fallback=broad_shape
    mpbi hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    imp_elim hyp=0 phase=initial depth=0 refs=0 fallback=none
    imp_elim hyp=1 phase=initial depth=0 refs=1 fallback=none
    imp_elim hyp=0 phase=dynamic depth=0 refs=0 fallback=none
    all_elim hyp=0 phase=initial depth=0 refs=1 fallback=none
    all_elim hyp=0 phase=dynamic depth=0 refs=1 fallback=none
  full validation attempts by rule:
    P_K_nd: attempts=2 accepted=2 rejected=0
    nd_fwd_bwd_minor_in_pool: attempts=1 accepted=1 rejected=0
    all_elim: attempts=3 accepted=2 rejected=1
    imp_elim: attempts=1 accepted=1 rejected=0

forward saturation loop stress auto? (bounded, no result)
  suggestions: 0
  total wall: 0.269 ms
  cold setup: 0.068 ms
  warm search: 0.186 ms
  rule index build: 0.002 ms
  ref index build: 0.067 ms
  shape emission: 0.006 ms
  rule lookup: 0.002 ms
  ref lookup: 0.004 ms
  tc clone: 0.000 ms
  tc apply: 0.000 ms
  candidate rules before conclusion validation: 0
  conclusion member prunes: 0
  final conclusion prunes: 0
  conclusion probes: 0
  ref pool size: 4
  per-hyp filtered ref list total: 0
  ref tuple count after filtering: 0
  full tryCandidate calls: 0
  accepted candidates: 0
  generated chain attempts: 0
  recursive apply calls: 0
  rejected candidates after validation: 0
  hyp syntactic matches: 0
  hyp definite mismatches: 0
  hyp unknown matches: 0
  recover member injections: 0
  split context guard rejects: 0
  acui witness attempts: 0
  recover guard rejects (match/extract): 0/0
  metas created (wild/exist/univ/bound): 0/0/0/0
  meta assignments: 0
  meta rollbacks: 0
  derived refs: 64
  forward rule attempts: 71
  forward match tuples: 65
  forward layers run: 2
  forward saturation exhausted: true
```
