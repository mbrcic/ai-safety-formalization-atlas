# External Formalizations

External builds use immutable source archives and an immutable prover image.
They are intentionally separate from normal Lean CI because the image is large.
Run both reproduced sessions with:

```console
scripts/reproduce_isabelle.sh all
```

## Isabelle/HOL: Rice's theorem

- Upstream: [AFP — Recursion Theory I](https://www.isa-afp.org/entries/Recursion-Theory-I.html)
- Author: Michael Nedzelsky
- License: BSD-3-Clause (AFP BSD License)
- Release: `2026-02-06`, compatible with Isabelle2025-2
- Archive SHA-256: `b5314c859ce3b2876ef01151f394c1a5e6b234b0fc6563698dbb0250c73cd3f8`
- Session: `Recursion-Theory-I`
- Theory: `RecEnSet.thy`
- Declarations: `Rice_1`, `Rice_2`, `Rice_3`
- Coverage relationship: `Rice_2` is `EQUIVALENT` to the survey's ordinary
  Rice-theorem row. It states that every nonempty, nonuniversal index set is
  not computable.
- Additional value: `Rice_1` supplies an explicit one-reduction, and `Rice_3`
  supplies a semantic c.e.-set interface. They are reproduced provenance and
  possible future interfaces, not two additional survey-result coverage claims.
- Migration decision: do not port `Rice_2`, because Mathlib already supplies
  the canonical Lean result. Defer `Rice_1` and `Rice_3` until a downstream
  reduction or c.e.-set proof requires their additional structure.
- Local reproduction: passed on 2026-07-18 in 8 seconds of session time.

Command:

```console
scripts/reproduce_isabelle.sh rice
```

## Isabelle/HOL: Arrow's impossibility theorem

- Upstream: [AFP — Arrow and Gibbard-Satterthwaite](https://www.isa-afp.org/entries/ArrowImpossibilityGS.html)
- Author: Tobias Nipkow
- License: BSD-3-Clause (AFP BSD License)
- Release: `2026-02-06`, compatible with Isabelle2025-2
- Archive SHA-256: `8174c738b42203100170ff25f3c9fc2c6d16d8556fbaff205c0eaa98a3813da7`
- Session: `ArrowImpossibilityGS`
- Theories and declarations:
  - `Thys/Arrow_Order.thy`: `Arrow`
  - `Thys/Arrow_Utility.thy`: `dictator`
- Relationship: `EQUIVALENT`. The entry contains two formalizations of
  Arrow's theorem, based respectively on strict orders and utility functions.
- Local reproduction: passed on 2026-07-18 in 2 seconds of session time.
- Migration decision: retain both Isabelle theories as provenance and interface
  specifications. Neither proof was ported. CC Liang's Lean 4 order proof is the
  canonical source, and the atlas derives its utility-facing theorem through a
  finite-preorder representation bridge.

Command:

```console
scripts/reproduce_isabelle.sh arrow
```

## Reproduction environment

- Official image: `makarius/isabelle:Isabelle2025-2`
- Image digest: `sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc`
- Isabelle version reported by the image: `Isabelle2025-2`
- Host architecture used: `x86_64`

The scripts verify archive hashes before extraction. Successful builds establish
the cited Isabelle statements; they do not establish a direct AI-safety bridge.
