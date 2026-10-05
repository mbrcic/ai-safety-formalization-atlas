# Bridge review — `Sovereignty.DelegationChain.power_over_a_matter_does_not_compose`

**Row `LAND-SOV-AUTH-001` · module `AISafetyAtlas/Sovereignty/DelegationChain.lean` · `HUMAN_REVIEW`**

Siblings: [`obedience_does_not_give_authority`](review-obedience-does-not-give-authority.md),
[`attestation_is_not_the_claim`](review-attestation-is-not-the-claim.md),
[`properties_are_independent`](review-properties-are-independent.md).

## Decision

| | |
|---|---|
| Verdict | ☑ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | Mario Brcic (mbrcic) |
| Date | 2026-10-05 |
| Note | Accepted on the allowed claim as sharpened 2026-10-03; re-signed 2026-10-05 after the closure audit found that nothing encodes power over a party and that, under the natural encoding, composition holds. The claim is now about two matters. |

## The statement

```lean
public theorem power_over_a_matter_does_not_compose
    (G : GameForm.{u, max v y, w} N (X × Y)) (C D : Set N) (x₀ : X) (y₀ : Y)
    (hfst : Forces G C (Prod.fst ⁻¹' {x₀}))
    (hsnd : Forces G D (Prod.snd ⁻¹' {y₀}))
    (hfree : ∀ sC : ∀ i : C, G.strategy i, ∃ s : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) ∧ (G.outcome s).2 ≠ y₀) :
    Forces G C (Prod.fst ⁻¹' {x₀}) ∧ Forces G D (Prod.snd ⁻¹' {y₀}) ∧
      ¬ Forces G C (Prod.snd ⁻¹' {y₀})
```

## What to check

1. **All three conjuncts are stated together because each alone misleads.** The
   first two are what an assurance chain documents; the third is what it is taken
   to establish.
2. **`hfree` is a hypothesis, not derived**, and that is deliberate: whether a
   real chain leaves a coordinate free is precisely the contestable question.
   Check the hypothesis is the *definition* of the coordinate being free of `C`
   and does not smuggle in more.
3. **Power-over is relative to a matter.** Dropping the matter is what makes the
   composition look valid. Confirm the two `Forces` claims really are about
   different coordinates.

## Allowed claim

> Power over one matter and another party's power over a second matter need not
> combine into power over the second: where every commitment of the first party
> leaves the second matter free, it does not force it. This is about two matters,
> not about power over a party: nothing here models one party's power over
> another, and under the natural reading of that ("whatever B can force, A can
> force") composition does hold.

## Forbidden

- **Not** a claim that any real assurance chain leaves a coordinate free.
- **Not** "delegation does not work." A chain where the upstream party does
  control the downstream matter — by a contract with a remedy that binds, by
  holding the key, by being able to withdraw the input — is not an instance. That
  is the useful form: the property an accountability framework must establish is
  control of the **matter**, not of the party.
- **Not** a refutation of "A has power over B and B over the outcome, so A over
  the outcome." Read as A forcing whatever B forces, that inference holds; the
  theorem concerns two different matters.
- **Not** about blame, responsibility or liability, none of which is modelled.
- **Not** about contracts, incentives or enforcement.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "AI value chains cannot be made accountable." | conditional on a free coordinate, which is not asserted of any chain |
| "The vendor is contractually bound, so the deployer controls the outcome." | requires control of the specific matter — the inference this refuses wherever that matter is free of the deployer (`hfree`) |
| "So accountability should sit with the last party in the chain." | no normative claim; the theorem locates a gap, it does not allocate duty |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`, and
`Examples/Sovereignty/Authority.lean`'s `split` inhabits `hfree` at a concrete
game — `split_opponent_forces_fst`, `split_principal_forces_snd`,
`split_opponent_not_forces_snd`.
