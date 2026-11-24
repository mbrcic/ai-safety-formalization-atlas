# v6 impact pass: outcome (closed 2026-11-22, completed 2026-11-23)

The completion pass of 2026-11-23 (section at the end) adjudicated the 34 rows below and replaced the
22 hand-derived transfers with Lean.

The pass was closed early. Grounded adjudication finished for 78 rows
(`adjudication/A00`-`A09`, `B00`-`B03`, `B06`, `B08`; Fable). The remaining 34 rows were never
adjudicated: the Fable runs were stopped, an Opus re-run was started and also stopped. Under the
Part 95 rule (a grade changes only when an adjudicator names a v6 rule), they **carry their
current grade** and are flagged `v6-unadjudicated`.

## Adjudicated (78 rows)

| Move | Rows |
|---|---|
| Wider -> Same (30) | 014 024 031 037 045 047 061 072 086 099 103 112 115 129 138 142 156 163 173 195 214 233 243 249 261 269 292 296 299 314 |
| Same -> Wider (3) | 228 230 241 |
| Drop below print (5) | 070 Mixed, 254 Refuted, 259 Beyond, 277 Mixed, 284 Narrower |
| Unchanged (40) | the rest |

- 22 of the 30 Wider -> Same moves rest on a **hand-derived** transfer (none is a Lean declaration):
  061 099 142 024 031 045 072 086 103 112 138 163 173 233 243 249 261 269 296 299 047 292. The other
  eight (014 037 115 129 156 195 214 314) rest on reading rulings or direct certification.
- Drops do not take effect until the author answers their reading questions (rulings of 2026-11-22).
- Argued flags: 076, 148, 193.
- Control row 241 moved (E22 pattern), so the selection leaks; it touches only Same/Wider.

## Not adjudicated (34 rows, current grade carried)

- Track T, Wider/Same only at stake: 136 149 164 169 179 011 042 306.
- Track T routed to F (could drop): 001 106 131 215 283 297.
- 035: open concern that Pauly Thm 3.2's own construction may fail at finite S.
- Track F, F08-F11 (blind: Fable + Opus): 010 015 051 065 090 095 123 155 181 207 227 229 240
  255 281 282 293 305 307. Both blind graders put 015 065 090 207 240 281 below print, and
  255 is split (Mixed/Narrower). These seven are the open headline risk.

## Questions for the author

1. Reading questions: **ruled 2026-11-22** (ADJUDICATION-LOG.md, last section). No row
   stays below print: 070 Wider (lemma proved), 254 Wider, 277 Wider (argued), 284 Same (composite
   carrier proved), 259 Beyond (outside the count).
2. Do hand-derived transfers count? **Ruled 2026-11-22: yes, flagged** (scope-grading.md G11).
   Under a Lean-only rule the 22 transfer rows would revert to Wider; coverage is unchanged either way.
   (All 22 are in Lean since 2026-11-23; 7 later rows rest on a hand-checked transfer.)
3. Does §7.1's transfer test apply to definitions (112 138 163 173 243)? **Ruled 2026-11-22: yes**
   (scope-grading.md G12).
4. Does §7.1 admit a family of sub-instances (288)? **Ruled 2026-11-22: no, one map only**
   (scope-grading.md G13). Does the round-2 mechanism-table reading extend to 148 and 090?
   **Ruled 2026-11-22: yes.**
5. R13 and R18 are still open.

## Still owed (as of 2026-11-22; see the completion pass)

- ~~Codex cross-checks of 254 and 277~~: done 2026-11-23, both agree (254 Wider, 277 Wider, argued).
- 232: Same under the "N is any set" ruling (2026-11-22).

## Completion pass (2026-11-23, Codex)

Deviation from Part 95 recorded here: Codex, not Fable, adjudicated.

1. **Blind grades restored.** Codex graded F08-F11 and T00-T07 blind (the batches where an Opus
   stand-in had replaced it). Raw output is not published, as for the other blind grades.
2. **Grounded adjudication** of the 34 rows above, plus 073 108 121 299 312 (flagged by the new
   track-T grades) and the cross-checks of 254 and 277: `adjudication/C01`-`C07`.
   - Wider -> Same (7), transfer checked by hand (G11): 051 155 227 001 106 215 283.
   - Held: 010 015 065 090 293 305 307 035 297 136 149 169 179 011 042 306 073 108 121 312, and
     282 Same. 254 Wider and 277 Wider (argued) agree with the author's rulings.
   - Reading questions (8), **ruled 2026-11-23 as recommended**: 095 Wider (normalization is a
     convention), 123 Wider (the rate function is kinematic, time in [0, inf)), 181 and 164 Wider
     (the entropy, complexity and identification sentences explain u = -rho(h)), 255 Wider
     (domination needs capacity, not exercise), 229 Same ("not fully rational" is start-value
     suboptimality, as print's "strictly less" requires), 281 Same (print supplies the composition:
     "since the execution of T(I) cannot harm humans"), 240 footnote 6 = exactly one (still Mixed).
   - Below print, owed, costed in the audit: 240 Mixed (under 300 lines), 131 Mixed (Codex closure
     failed: needs a verified universality layer, over 300 lines), 207 Mixed (over 300 lines).
   - 299: Narrower under the ruled reading (open field and time domain); closed by a Lean
     generalization of the dynamics over a time field and coefficient algebra
     (`closures.jsonl`), so it keeps Same.
3. **Lean transfers** (`docs/provenance/transfers/`, CI-checked; `transfers-lean.jsonl`): all 22
   hand-derived transfers above now compile in Lean, and five rows graded Wider whose transfer the
   restored blind grades found (034 036 041 044; 002's was later withdrawn) are Same on a Lean transfer.
   No transfer proof uses its row's main cited theorem (061 and 142 use cited auxiliary lemmas). The
   other 34 such candidates were not attempted in this step; they stay Wider.

Result: 93 Same / 216 Wider / 4 Mixed / 1 None, 2 closed, 42 Beyond; 5 cells owed (005, 135, 131,
207, 240), each costed. Hand-derived transfers remaining: the 7 new ones above.

## Frozen for v0.10.0 (2026-11-23, author: "freeze")

No further grading or adjudication passes for v0.10.0. Lean transfers for the restored track-T
candidates were then written by Claude Opus agents (batches D1-D5; each
report read, and a transfer rejected when its map copies the truth value of the Lean condition,
SPEC E2). The fixed list carried to v0.10.1, nothing to be added to it:

- Transfer candidates not attempted: 212 242 257 266 272 291 303 315 (232 was already Same).
- Failed in D1-D5: 113 (not attempted, estimated 250-350 lines), 188 (no structural map), 189 (reading: the setting
  binds U in Ch_D), 194 (budget: needs a sensor-purification layer).
- 107: rejected (its map encodes the Lean condition; E2). Stays Wider unless a structural map is found.
- 002 and 084: transfers withdrawn after an independent review (002's map copies the Lean optimum into
  the print instance; 084's attainment map is built from the Lean objective's rank order; E2). Wider.
- 299: Same by the author's ruling; the controllability and observability properties are still stated
  at real time and complex coefficients (the equations were generalized). Generalize them.
- 075, 175, 197: compiled under the reading that print's "discrete state space" sets no cardinality
  bound; await the author's reading, Wider until then (files kept, CI-checked).
- Closures 131 and 207 (Mixed, owed, costed in the audit).

Accepted Lean transfers from D1-D5 (Wider -> Same): 069 081 089 093 104 110 111 126 127 139 143
157 168 182 183 185. Flags noted in `transfers-lean.jsonl`: 127 (the
Lean statement is near-trivial), 143 (a library lemma does most of the work), 183 (the intermediate line
translates an entropy scalar), 185 (re-derives a cited auxiliary from an uncited lemma).

Final for v0.10.0: 108 Same / 201 Wider / 4 Mixed / 1 None, 2 closed, 42 Beyond; 5 cells owed (005, 135,
131, 207, 240), each costed. Same rows on a Lean transfer: 42; on a transfer checked by hand: 7.
