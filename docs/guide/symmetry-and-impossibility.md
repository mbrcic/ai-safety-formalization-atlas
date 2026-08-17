# Symmetry and impossibility

*A reading path, not a result. Everything named here is proved elsewhere and
graded in its own row; nothing new is claimed on this page.*

Most of the impossibility results in this atlas are the same argument.

> **If a structure cannot tell two things apart, it cannot do a job that requires
> telling them apart.**

The variations are in what "cannot tell apart" means — a permutation of the
search domain, a relabelling of voters, an automorphism of a communication
network, a diagonal that maps a set onto its own function space — and in what
the job is. Read separately they look like five unrelated formalizations. They
are five instances, and the shared machinery now lives in
`AISafetyAtlas.Combinatorics.PermInvariance`.

## The shape

Each result fixes a group acting on the objects, shows the acting group is *too
large* for the object to carry information, and concludes that the job fails.

| Result | What acts | What the symmetry forces | Where |
|---|---|---|---|
| Requisite variety | disturbance values on a regulator's table | a regulator with fewer states than the disturbance cannot admit fewer than two outcomes | `Control.RequisiteVariety.two_le_card_admittedOutcomes` |
| No Free Lunch | `Equiv.Perm X` on objectives `X → Y` | performance is algorithm-independent **exactly** on permutation-closed priors | `Learning.Sharp.nfl_adaptive_iff_permInvariant` |
| Structure is never symmetric | `Equiv.Perm X` on relations over `X` | an invariant relation is constant off the diagonal, so no non-trivial neighbourhood survives | `Combinatorics.PermInvariance.exists_perm_rel_not_iff` |
| Leader election | automorphisms of a network | a symmetric protocol from a symmetric start never elects a unique leader | `Compositional.Symmetry.symmetric_no_unique_leader` |
| Gibbard–Satterthwaite, Arrow | relabelling voters and alternatives | no rule is simultaneously resolute, non-dictatorial and strategyproof | `SocialChoice.gibbard_satterthwaite`, `SocialChoice.arrow` |

## The two directions, and why the pairing matters

Requisite variety and No Free Lunch point opposite ways, and reading them
together is the point.

**Requisite variety says symmetry is expensive.** A regulator must have at least
as much variety as the disturbance or the outcome cannot be pinned down. Not
distinguishing costs you.

**No Free Lunch says symmetry is what makes the theorem bite.** Performance is
algorithm-independent *precisely* on the priors that cannot tell objectives
apart. And Igel–Toussaint's Theorem 3 says almost no prior is of that kind
(`card_closedUnderPermutation_nonempty`), while Theorem 4 says no space carrying
structure is either.

So the honest reading of NFL is not "search is hopeless". It is: **the hypothesis
under which search is hopeless is one that essentially nothing satisfies.** The
same symmetry that makes the theorem true is what keeps it from applying. That
is a conclusion the atlas can state only because both directions are mechanized
and the counts are proved rather than asserted.

**Careful here.** Theorem 4 does *not* establish that a structured search space
has no permutation-closed prior — see the non-claim in `Learning.Sharp`. The
step from "the neighbourhood relation is not invariant" to "this family of
objectives is not closed under permutation" is print's own Examples 2 and 3, and
neither is formalized. The uniform prior is permutation-invariant whatever
structure the space carries.

## The one that is a different symmetry

`Logic.lawvere_fixed_point` is the diagonal argument in its general form: a
surjection `α → (α → β)` forces every `g : β → β` to have a fixed point. Gödel,
Tarski, Cantor, Rice and the halting problem are all instances of it in the
literature.

**In this tree they are not routed through it.** `Computability.rice`,
`Logic.chaitin_incompleteness` and the self-reference results in `Knowledge` and
`SelfAwareness` are each proved directly, and no proof anywhere in the library
depends on `lawvere_fixed_point` — `scripts/report_consumers.py --queue` lists it
as `Examples/ only`, its sole reference being the `#check` in
`AISafetyAtlas.Examples.Registry`. That is a real gap in the atlas's structure
rather than a subtlety, and it is recorded here rather than papered over: the
general theorem is present, the instances are present, and the arrows between
them are not.

## Where the shared machinery lives

`AISafetyAtlas.Combinatorics.PermInvariance` holds the permutation half:
`permOrbit`, `ClosedUnderPermutation`, `spectrum` and the fact that the multiset
of values is the complete invariant of an orbit, the bijection between
relabelling-invariant families and families of multisets, the counts, and the
results about invariant relations and graphs.

Two places do this kind of reasoning without using it, deliberately:
`Compositional.Hyperproperties.Product.toBatch_perm` is the `Finset` image of
`spectrum` and cannot be strengthened to the `iff` because it forgets
multiplicity; and `Upstream` relabels voters and alternatives by hand, but is
vendored and left untouched.
