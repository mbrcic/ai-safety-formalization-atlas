# Repository AI instruction files: design reference

> **Last verified:** 2026-09-06
> **Scope:** repository instruction files for coding/AI agents: naming, structure, scoping, loading, size, writing style, portability, and token efficiency.
> **Purpose:** reference material for humans or agents that create, audit, or refactor repository instructions. This file is not intended to be loaded on every coding task.

## Evidence model

This reference separates two kinds of statements:

- **Documented fact:** current behavior or guidance stated by a provider, official project, or implementation source. The source ID is shown in the relevant table or paragraph.
- **Synthesis:** a cross-platform recommendation derived from several documented behaviors. A synthesis is not a vendor requirement or empirically universal optimum.

Provider behavior changes. Where a vendor's documentation conflicts with another vendor's behavior, the active tool's documentation wins.

## Core synthesis

- For a multi-agent repository, a root `AGENTS.md` is the best current **portable shared-core candidate**, because it is an open Markdown convention and is directly supported by Codex, GitHub Copilot surfaces, Cursor, Devin Desktop/Cascade, Cline, and Junie; Claude Code can import it, and Gemini CLI can be configured to use it as a context filename. `[AGENTS] [OAI-CODEX] [GH-SUPPORT] [CURSOR] [DEVIN-AGENTS] [CLINE] [JUNIE] [CLAUDE] [GEMINI-CONTEXT]`
- `AGENTS.md` is **not a universal execution standard**. Discovery, nested-file semantics, precedence, and supported surfaces differ by tool. Never infer those behaviors from the filename alone.
- Keep the always-loaded core short and broadly relevant. Move path-, language-, component-, or task-specific material into scoped/on-demand mechanisms where the supported agent provides them. `[CLAUDE] [CURSOR] [DEVIN-RULES] [CLINE]`
- Store each substantive rule in one canonical place. Imports/adapters can preserve one source of truth, but imported text still consumes context. `[CLAUDE] [GEMINI-IMPORT]`
- Prefer concrete, verifiable instructions: exact commands, paths, conditions, formats, and acceptance checks. `[CLAUDE] [MICROSOFT] [CLINE]`
- Use headings and short bullets. Numbered lists should mean real sequence, not visual decoration. `[CLAUDE] [MICROSOFT]`
- Reference canonical examples, configuration, or documentation instead of copying large style guides or code examples into persistent context. `[CURSOR] [CLINE]`
- Do not encode mechanically enforceable policy only in prose. Use formatters, linters, tests, CI, hooks, permissions, or agent configuration for hard controls; instructions should point to those mechanisms. `[CLAUDE] [CURSOR]`
- Avoid conflicting instruction sources even when a product documents precedence. Conflict-free scoping is more portable across agents. `[CLAUDE] [GH-CLI]`
- Optimize for **relevant context**, not the smallest possible file. Removing necessary repository knowledge can be worse than carrying a modest amount of additional context.
- There is no universal optimal line, byte, character, or token count. Numeric limits below are either provider-specific facts or explicitly labeled house recommendations.
- Current OpenAI model guidance explicitly recommends auditing instruction files and skills accessible to the model because newer models can be sensitive to guidance in files such as `AGENTS.md`. `[OAI-MODEL]`

## Cross-platform compatibility facts

| Tool | Repository instruction sources | Discovery / scoping | Imports / combination / precedence | Size or context guidance | Source |
|---|---|---|---|---|---|
| **OpenAI Codex** | `AGENTS.override.md`, `AGENTS.md`, configured fallback filenames; user-level files in `$CODEX_HOME` | Project files are discovered from project/Git root to the current working directory. At most one candidate file is selected per directory; `AGENTS.override.md` is preferred over `AGENTS.md`, then configured fallbacks. | Project files are ordered root → working directory, so more-specific text appears later. | Current implementation applies `project_doc_max_bytes` as a **cumulative project-instruction byte budget**; default is **32 KiB**. | `[OAI-CODEX] [OAI-CODE]` |
| **Claude Code** | `./CLAUDE.md`, `./.claude/CLAUDE.md`, `CLAUDE.local.md`, `.claude/rules/**/*.md` | Ancestor/current-directory `CLAUDE.md` files load at launch; descendant files load when Claude reads files there. `.claude/rules/` can use `paths` frontmatter. | Claude Code does **not** directly read `AGENTS.md`; a `CLAUDE.md` can import it with `@AGENTS.md`. Imports expand into context and support up to **4 hops**. | Anthropic says to **target under 200 lines per `CLAUDE.md`**; longer files consume more context and can reduce adherence. | `[CLAUDE]` |
| **Gemini CLI** | `GEMINI.md` by default; `context.fileName` can specify another name or list, including `AGENTS.md` | Loads global context, project/current-directory + ancestor context up to the Git root, and subdirectory context files; discovered content is concatenated. | `@file` imports are expanded. Import depth is configurable; current default is **5 levels**. `/memory show` exposes the concatenated context. | No numeric file-size recommendation is stated in the referenced context-file docs. Imports and multiple files still expand the effective context. | `[GEMINI-CONTEXT] [GEMINI-IMPORT]` |
| **GitHub Copilot** | `.github/copilot-instructions.md`, `.github/instructions/**/*.instructions.md`, and—depending on Copilot surface—`AGENTS.md`, `CLAUDE.md`, `GEMINI.md` | Support varies by surface. Path-specific `*.instructions.md` use `applyTo`; Copilot also supports agent instructions on selected surfaces. | GitHub's general Copilot precedence is personal → path-specific repo → repo-wide → agent instructions → organization. **Copilot CLI is different:** it combines applicable files and defines no general precedence among the combined instruction files. CLI supports `@` references in `.github/copilot-instructions.md`, `AGENTS.md`, and `CLAUDE.md`, but not in `GEMINI.md` or `*.instructions.md`. | GitHub recommends short, self-contained instructions; no universal repository-instruction byte/line limit is stated in the referenced docs. | `[GH-SUPPORT] [GH-CUSTOM] [GH-CLI]` |
| **Cursor** | `.cursor/rules/**/*.mdc`, root/subdirectory `AGENTS.md`, root `CLAUDE.md`; legacy `.cursorrules` is being deprecated | Native `.mdc` rules can be always-on, model-selected, glob-scoped, or manual. Nested `AGENTS.md` files combine with parents and more-specific instructions take precedence. | Cursor CLI reads root `AGENTS.md` and `CLAUDE.md` alongside `.cursor/rules`. Team Rules take precedence over Project Rules, then User Rules. | Cursor recommends **under 500 lines per rule**, splitting large concepts into focused rules. | `[CURSOR] [CURSOR-CLI]` |
| **Devin Desktop / Cascade** | Root/nested `AGENTS.md`; `.devin/rules/*.md` preferred; legacy `.windsurf/rules/*.md` fallback | Root `AGENTS.md` is always-on. Nested `AGENTS.md` becomes an automatically generated directory glob. Native rules support always-on, glob, model-decision, and manual activation. | `.devin/` is the preferred rule location; `.windsurf/` remains backward-compatible fallback. | Workspace rule: **12,000 characters per file**. Global rule: **6,000 characters**. These are character limits, not KiB limits. | `[DEVIN-AGENTS] [DEVIN-RULES]` |
| **Cline** | `.clinerules/` (`.md` and `.txt`), `AGENTS.md`, `~/.agents/AGENTS.md`, legacy-compatible `.cursorrules`, `.windsurfrules` | `.clinerules` supports `paths` YAML frontmatter; rules without frontmatter are always active. | Workspace and global rules are combined; workspace rules take precedence over global rules when they conflict. | No numeric limit is stated in the referenced guide; Cline explicitly warns that rules consume context and should remain concise. | `[CLINE]` |
| **JetBrains Junie** | `.junie/AGENTS.md`, root `AGENTS.md`, `.junie/playbook.md`, `.junie/rules/*.md`, legacy `.junie/guidelines.md`; global `~/.junie/AGENTS.md` | `.junie/AGENTS.md`, when present, is preferred and used **exclusively**. Otherwise Junie combines root `AGENTS.md` + playbook + `.junie/rules/*.md`. | Project guidelines take precedence over global guidelines. Identical global/project content can be deduplicated. | JetBrains' support guidance suggests keeping `.junie/AGENTS.md` around **20–40 lines** to reduce quota use; this is product-specific practical advice, not a hard limit. | `[JUNIE] [JUNIE-KB]` |
| **AGENTS.md convention** | `AGENTS.md` | Plain Markdown; no required fields/schema. The convention describes nested files with closer files taking precedence. | Treat this as a portability convention, not proof of a particular tool's implementation. Vendor documentation controls actual discovery and precedence. | No standard size limit. | `[AGENTS]` |

### Important portability consequence

**Nested `AGENTS.md` is not semantically portable enough to be the default cross-tool scoping mechanism.**

- Codex resolves project instructions according to the chain from project root to its **working directory**. `[OAI-CODEX] [OAI-CODE]`
- Cursor applies nested `AGENTS.md` according to files under that directory. `[CURSOR]`
- Devin Desktop/Cascade turns nested `AGENTS.md` into a directory glob. `[DEVIN-AGENTS]`
- Gemini CLI scans and concatenates context files from its hierarchy, including subdirectory context files below the working directory. `[GEMINI-CONTEXT]`
- Copilot behavior depends on the specific Copilot surface. `[GH-SUPPORT]`

For a repository that must behave consistently across several agents, keep universal rules at the root and use vendor-native scoped rules only where needed and tested.

## Recommended architecture

The following is synthesis, not a universal vendor requirement.

| Need | Recommended implementation | Reason |
|---|---|---|
| Shared repository-wide core | `/AGENTS.md` | Maximizes current cross-tool reuse while remaining plain, reviewable Markdown. |
| Claude compatibility | Small `/CLAUDE.md` containing `@AGENTS.md` **only when needed** | Claude does not read `AGENTS.md` directly. Keep Claude-specific additions below the import. |
| Gemini compatibility | Prefer configuring Gemini's context filename to include `AGENTS.md`; otherwise use a minimal `GEMINI.md` import | Avoid maintaining a second copy of shared rules. |
| Copilot-specific global rules | `/.github/copilot-instructions.md` | Use only for behavior genuinely specific to Copilot or a Copilot surface. |
| Copilot path-specific rules | `/.github/instructions/<topic>.instructions.md` | Native `applyTo` scoping is clearer than making global text conditional in prose. |
| Cursor-specific scoped rules | `/.cursor/rules/<topic>.mdc` | Native glob/relevance/manual activation. |
| Devin/Cascade-specific rules | `/.devin/rules/<topic>.md` | Current preferred native rule location. |
| Cline-specific conditional rules | `/.clinerules/<topic>.md` | Native `paths` scoping. |
| Junie-specific additions | Root `AGENTS.md` + `/.junie/rules/*.md` where needed | If `.junie/AGENTS.md` exists, Junie uses it exclusively and the root shared core is no longer combined automatically. |
| Detailed human/reference material | `/docs/...` | Keep long explanation out of persistent model context; point to it when relevant. |

### Adapter hazards

Adapters are useful for deduplication but can create duplicate effective context:

- Cursor reads both root `AGENTS.md` and root `CLAUDE.md`. If `CLAUDE.md` imports `AGENTS.md` for Claude Code, Cursor may receive overlapping shared guidance. Test the effective instruction set before assuming the adapter is harmless. `[CURSOR] [CURSOR-CLI]`
- Copilot CLI can discover `AGENTS.md`, `CLAUDE.md`, `GEMINI.md`, Copilot files, and path-specific instructions in the same session. It removes some identical duplicate copies but does not define a general precedence order among all combined files. `[GH-CLI]`
- Gemini `context.fileName` can be a list. Listing both `AGENTS.md` and `GEMINI.md` while also importing one from the other can duplicate context. `[GEMINI-CONTEXT] [GEMINI-IMPORT]`
- Junie's `.junie/AGENTS.md` is not a thin additive adapter: when present, it is used exclusively instead of the normal root-`AGENTS.md` combination. `[JUNIE]`

Therefore: **one canonical rule, minimal adapters, and explicit testing of the effective loaded context**.

## Naming

- Use vendor-required filenames and extensions exactly.
- For the portable shared file, use the canonical uppercase spelling `AGENTS.md`, even where a specific tool also accepts lowercase.
- Name scoped files by **concern or scope**: `testing.md`, `lean.md`, `api-design.md`, `docs.instructions.md`, `react-patterns.mdc`.
- Avoid vague names such as `misc.md`, `important.md`, `rules2.md`.
- Do not use numeric prefixes to imply precedence unless the product explicitly defines that behavior. Cline documents numeric prefixes as optional organization only. `[CLINE]`
- Keep personal or machine-local preferences in user/local instruction locations rather than shared repository files.
- Keep temporary task state out of persistent instruction files.

## Recommended content structure

`AGENTS.md` has no required schema. `[AGENTS]` The following order is a compact cross-platform synthesis; omit sections that have no repository-specific content.

| Section | Include |
|---|---|
| `# <Repository> instructions` | One descriptive title. |
| `## Scope` | Where the instructions apply and any important exclusions. |
| `## Sources of truth` | Canonical specs, configs, architecture docs, generated sources, examples, or ownership locations the agent should consult rather than duplicate. |
| `## Repository map` | Only non-obvious directories/files needed to work correctly. Omit if the layout is obvious. |
| `## Commands` | Exact install, build, test, lint, format, generation, or validation commands that are repository-specific or easy to get wrong. |
| `## Conventions and constraints` | Architecture boundaries, compatibility requirements, naming, generated-file rules, repository-specific implementation conventions. |
| `## Validation` | Which checks are required for which changes; name commands rather than saying only "test your work." |
| `## Boundaries` | Real prohibitions or approval boundaries: secrets, generated/protected files, destructive/external actions, dependency or compatibility restrictions. |
| `## Scoped context` | Routes to narrower instructions, skills, runbooks, or documentation when a task requires them. |
| Optional `## Contribution / handoff` | Commit/PR/reporting requirements only if the repository actually expects agents to perform or report them. |

Do not preserve empty headings merely because a template contains them.

## What belongs where

| Information | Best home |
|---|---|
| Broad, stable repository conventions used on most tasks | Root shared instruction file |
| Language/component/path-specific conventions | Native scoped rule or carefully tested nested instruction |
| Repeatable multi-step procedure | Skill, workflow, prompt file, runbook, or task-specific context |
| Detailed architecture rationale | Architecture docs / ADRs |
| Large API/reference material | Documentation loaded on demand |
| Canonical implementation example | Existing source/example file; reference its path |
| Formatting rules | Formatter/linter configuration |
| Type/schema requirements | Compiler, type checker, schema validation |
| Test gates | Test runner / CI |
| Permissions / forbidden operations | Agent permissions, hooks, sandbox, repository settings |
| Temporary issue/task requirements | Issue, PR, or current user prompt |
| Personal preferences | User/local instruction scope |
| Secrets/credentials | Never an instruction file; use secret management |

A useful rule of thumb: persistent instructions should contain information the agent **needs repeatedly and cannot safely infer**, plus pointers to authoritative sources.

## Writing guidelines

| Principle | Recommended form | Evidence |
|---|---|---|
| Specificity | `Run npm test after changing src/api/**` rather than `test your changes`. | `[CLAUDE] [CLINE]` |
| Observable behavior | Describe inputs, actions, outputs, and checks that a reviewer can verify. | `[CLAUDE] [MICROSOFT]` |
| Atomicity | Keep independent requirements in separate bullets. | `[MICROSOFT]` |
| Explicit scope | Prefer `When editing migrations, ...` over an unqualified rule that has exceptions. | `[CLAUDE] [CLINE]` |
| Exact references | Put commands, paths, filenames, symbols, and literal values in backticks. | `[CLAUDE] [CURSOR]` |
| Structure | Use short `##` sections and bullets; add `###` only for a real subgroup. | `[CLAUDE] [MICROSOFT]` |
| Sequence | Use numbered steps only when order matters. | `[MICROSOFT]` |
| Positive action | Prefer what to do; use `Do not`/`Never` for genuine prohibitions. | `[MICROSOFT]` |
| Rationale | Add a short "why" only when it changes edge-case interpretation or prevents a recurring mistake. | `[CLINE]` |
| Examples | Prefer a canonical file reference; inline an example only when it resolves a real format/ambiguity that prose does not. | `[CURSOR] [CLINE]` |
| Duplication | State a substantive rule once; reference or import its canonical source elsewhere. | `[CLAUDE] [GH-CLI]` |
| Currency | Delete obsolete rules instead of layering contradictory exceptions over them. | `[CLAUDE] [CLINE]` |

### Avoid

- vague filler: `write clean code`, `be careful`, `follow best practices`;
- persona inflation: `act as a world-class engineer`;
- broad `always` / `never` language when the real rule has conditions or exceptions;
- repeated paraphrases of the same rule;
- long project history or rationale that belongs in documentation;
- commands and facts that are both obvious and reliably derivable from current configuration;
- entire style guides or large copied examples;
- temporary issue state;
- secrets or credentials;
- instructions whose success is defined only by unverifiable internal reasoning rather than observable work.

## Size and token efficiency

### Documented product-specific facts

| Product | Documented guidance / limit | Unit / interpretation | Source |
|---|---|---|---|
| Codex | **32 KiB default** `project_doc_max_bytes` | Current implementation treats this as a cumulative project-instruction **byte** budget. This is a loading cap/default, not an ideal file size. | `[OAI-CODEX] [OAI-CODE]` |
| Claude Code | **Target under 200 lines per `CLAUDE.md`** | Provider recommendation. Imported files still consume context. | `[CLAUDE]` |
| Cursor | **Keep rules under 500 lines** | Provider recommendation per rule; Cursor also recommends splitting large rules. | `[CURSOR]` |
| Devin Desktop / Cascade | **12,000 characters** per workspace rule; **6,000 characters** global | Hard/product limits measured in characters, not bytes. | `[DEVIN-RULES]` |
| Junie | **Around 20–40 lines** in `.junie/AGENTS.md` | JetBrains support recommendation for quota efficiency; not a hard limit. | `[JUNIE-KB]` |
| Gemini CLI | No numeric target in referenced context docs | Multiple files/imports are expanded into effective context. | `[GEMINI-CONTEXT] [GEMINI-IMPORT]` |
| Cline | No numeric target in referenced rule guide | Provider says rules consume context and should be concise. | `[CLINE]` |
| AGENTS.md convention | No numeric standard | Plain Markdown; tool-specific limits still apply. | `[AGENTS]` |

**Characters, bytes, KiB, lines, and tokens are different units.** In particular, a 12,000-character product limit is not the same as 12 KiB for non-ASCII text. `1 KiB = 1024 bytes`.

Token count is model/tokenizer dependent. Google gives roughly four characters per token as a general approximation in its Gemini prompt guide, but that is not precise enough for repository enforcement. `[GEMINI-PROMPT]` Prefer deterministic UTF-8 byte counts plus line counts for repository budgets; measure actual tokens only when targeting a known tokenizer/model.

### Conservative house budget

The following is a **synthesis for token-efficient multi-agent repositories**, not an empirical optimum or vendor requirement.

| Instruction unit | Preferred target | Strong signal to split or re-scope |
|---|---:|---:|
| Root always-loaded shared core | **≤100 nonblank lines and ≤8 KiB UTF-8** | ~150 lines or ~12 KiB |
| Thin vendor adapter | **≤20 nonblank lines and ≤2 KiB** | It contains substantive shared policy instead of only adaptation/vendor-specific rules |
| Scoped/topic rule | **≤80 nonblank lines and ≤6 KiB** | It contains multiple independent concerns or is approaching always-loaded-file size |

Use both the line and byte target; whichever is reached first should trigger review. Do not game the budget by packing many requirements into very long lines.

Why these numbers: they are deliberately below Claude's `<200`-line recommendation, leave substantial headroom below Codex's 32 KiB cumulative default, remain below Devin/Cascade's 12,000-character workspace-rule limit for ordinary ASCII-heavy text, and reflect the repeated provider recommendation to keep persistent context concise and scoped. `[CLAUDE] [OAI-CODEX] [DEVIN-RULES] [CURSOR] [CLINE]`

The exact target should be changed only when representative agent behavior or a supported platform's limits justify it.

## Imports versus references

Imports solve maintenance duplication; they do **not** automatically save tokens.

- Claude `@path` imports are expanded into context; maximum recursive import depth is currently 4. `[CLAUDE]`
- Gemini `@file` imports are expanded; default maximum import depth is currently 5. `[GEMINI-IMPORT]`
- Therefore a 3-line adapter that imports a 10 KiB file can still contribute roughly that imported content to effective context.
- Prefer a **path/reference** rather than an import when the agent needs a document only for specific tasks.
- Import content that is intended to function as instructions. Do not eagerly import large READMEs, ADR collections, generated documentation, or style guides merely because they are authoritative references.
- Keep import chains shallow and acyclic.
- Check the tool's active-context/debug view where available: Claude `/context`, Gemini `/memory show`, Copilot CLI `/instructions`. `[CLAUDE] [GEMINI-CONTEXT] [GH-CLI]`

### Human-only comments

Claude Code strips block-level HTML comments from injected `CLAUDE.md` context, allowing maintainer notes without consuming Claude context. This is **Claude-specific**; do not rely on HTML comments being ignored by other agents. `[CLAUDE]`

## Precedence and conflict

There is no cross-agent universal precedence model.

- A narrower rule should normally **specialize** a broader rule rather than contradict it.
- If an exception is real, state it explicitly at the narrow scope and avoid duplicate contradictory copies.
- GitHub Copilot's general precedence and Copilot CLI's merge behavior are different. `[GH-CUSTOM] [GH-CLI]`
- Codex ordering is root → working directory, while other tools can scope by edited/current files. `[OAI-CODEX] [CURSOR] [DEVIN-AGENTS]`
- Repository prose cannot redefine higher-level system, organization, user, sandbox, or tool permissions supplied by the active platform.

For multi-agent portability, **conflict avoidance is safer than relying on precedence**.

## Instructions versus other mechanisms

| Need | Prefer |
|---|---|
| Stable rule relevant to nearly every task | Always-loaded instruction |
| Stable rule for one path/language/component | Scoped rule |
| Complex task-specific procedure | Skill/workflow/prompt/runbook |
| Large factual/reference corpus | Documentation / retrieval / on-demand context |
| Repeated code shape | Canonical example/template file |
| Formatting/style that can be checked | Formatter/linter |
| Build/test acceptance | Script/test runner/CI |
| Hard action restriction | Permission system, hook, sandbox, repository setting |
| One-off task constraint | Current prompt/issue/PR |

This separation is supported directly by Claude's distinction between `CLAUDE.md`, path-scoped rules, skills, and hooks; Cursor's distinction between rules and skills; and Devin/Cascade's distinction between rules, `AGENTS.md`, workflows, and skills. `[CLAUDE] [CURSOR-LEARN] [DEVIN-RULES]`

## Source synthesis

Across the current sources, the strongest recurring conclusions are:

1. Persistent instructions work best when they are **specific, concise, structured, current, and non-conflicting**. `[CLAUDE] [CURSOR] [CLINE] [MICROSOFT]`
2. **Persistent context has a cost**. Large always-on files consume context/quota and can reduce instruction adherence or focus. `[CLAUDE] [CLINE] [JUNIE-KB]`
3. **Scoping is preferable to global accumulation** when a rule matters only for certain paths or tasks. `[CLAUDE] [CURSOR] [DEVIN-AGENTS] [CLINE]`
4. **Exact commands, paths, examples, and constraints** outperform generic quality language. `[CLAUDE] [CURSOR] [CLINE] [MICROSOFT]`
5. **Imports are organizational tools, not context compression.** `[CLAUDE] [GEMINI-IMPORT]`
6. **Instruction discovery is part of the product contract.** A file that is well written but not loaded—or is loaded twice—is incorrectly integrated.
7. **Machine enforcement should replace prose where possible.** `[CLAUDE] [CURSOR]`
8. For multi-agent repositories, the most robust architecture is currently **small shared root core + vendor-native scoped detail + on-demand procedures + mechanical enforcement**.


## Additional repository-rule ecosystems

These tools are relevant to instruction-file design even though they do not all use `AGENTS.md` as their primary project mechanism.

| Tool | Repository mechanism | Design-relevant behavior | Source |
|---|---|---|---|
| **Amazon Q Developer** | `/.amazonq/rules/*.md` | Project rules are Markdown files automatically used as project context in supported IDE/chat and GitHub/GitLab integrations. Multiple rule files are supported. Amazon Q can also generate a `memory-bank/` under `.amazonq/rules`, reinforcing the distinction between persistent rule/context material and source code. | `[AMAZON-Q]` |
| **Continue** | `/.continue/rules/*.md` | Rules enter Agent, Chat, and Edit system-message context. Markdown is recommended; optional `globs` frontmatter scopes rules when matching files are in context. Rules are joined in toolbar order. | `[CONTINUE]` |
| **Zed Agent** | Project instruction files; `AGENTS.md` is the primary recommended convention | Instructions are always-on context; Skills are for reusable on-demand task procedures. Zed recognizes several compatibility filenames and uses the **first matching project instruction file** from its documented list, so creating multiple adapters can change which file is actually loaded. | `[ZED]` |
| **Aider** | Any conventions/reference Markdown loaded with `/read` / `--read`, optionally configured in `.aider.conf.yml` | Aider does not require a standard repository instruction filename. Its docs recommend a small conventions file loaded read-only; unrelated context can distract the model and increase token cost. | `[AIDER]` |

These systems support the broader synthesis but also show why `AGENTS.md` should be described as the **best shared-core candidate**, not a universal native format.

## Coverage boundary

This reference prioritizes tools with current official documentation that materially changes repository instruction-file architecture, scoping, loading, precedence, or size decisions. It is not intended to enumerate every editor, agent wrapper, or compatibility alias.

A tool belongs in the compatibility tables when its official documentation establishes at least one design-relevant fact that is not already captured by the generic `AGENTS.md` convention. Unsupported or undocumented assumptions should not be added merely to make the ecosystem list longer.

## Primary and official sources

All sources below were checked on 2026-09-06.

| ID | Source | Used for |
|---|---|---|
| `[OAI-CODEX]` | OpenAI, *Unrolling the Codex agent loop*: https://openai.com/index/unrolling-the-codex-agent-loop/ | Codex instruction aggregation, root→cwd ordering, 32 KiB default. |
| `[OAI-CODE]` | OpenAI Codex source, `codex-rs/core/src/agents_md.rs`: https://github.com/openai/codex/blob/main/codex-rs/core/src/agents_md.rs | Current implementation: candidate order, one file/directory, cumulative byte budget, truncation. |
| `[OAI-MODEL]` | OpenAI, *Model guidance*: https://developers.openai.com/api/docs/guides/latest-model | Current recommendation to audit accessible instruction files/skills. |
| `[CLAUDE]` | Anthropic, *How Claude remembers your project*: https://code.claude.com/docs/en/memory | `CLAUDE.md`, `AGENTS.md` import, loading order, path rules, 200-line target, import behavior, enforcement distinction. |
| `[GEMINI-CONTEXT]` | Google, *Provide Context with GEMINI.md Files*: https://google-gemini.github.io/gemini-cli/docs/cli/gemini-md.html | Hierarchical context discovery, concatenation, imports, configurable filenames, `/memory`. |
| `[GEMINI-IMPORT]` | Google, *Memory Import Processor*: https://google-gemini.github.io/gemini-cli/docs/core/memport.html | Import expansion, recursion, default max depth, circular-import handling. |
| `[GEMINI-PROMPT]` | Google, *Prompt design strategies*: https://ai.google.dev/gemini-api/docs/prompting-strategies | Clear/specific instructions, prompt structure, rough token-character approximation. |
| `[GH-SUPPORT]` | GitHub, *Support for different types of custom instructions*: https://docs.github.com/en/copilot/reference/custom-instructions-support | Surface-by-surface Copilot instruction-file support. |
| `[GH-CUSTOM]` | GitHub, *About customizing GitHub Copilot responses*: https://docs.github.com/en/copilot/concepts/prompting/response-customization | Repository instruction types and general Copilot precedence. |
| `[GH-CLI]` | GitHub, *Adding custom instructions for GitHub Copilot CLI*: https://docs.github.com/en/copilot/how-tos/copilot-cli/customize-copilot/add-custom-instructions | CLI discovery, combination/no general precedence, `@` references, `/instructions`. |
| `[CURSOR]` | Cursor, *Rules*: https://prod.cursor.com/docs/rules | `.mdc`, rule activation, nested `AGENTS.md`, `CLAUDE.md`, 500-line recommendation, precedence, references. |
| `[CURSOR-CLI]` | Cursor, *Using Agent in CLI*: https://prod.cursor.com/docs/cli/using | CLI loads root `AGENTS.md` and `CLAUDE.md` alongside native rules. |
| `[CURSOR-LEARN]` | Cursor, *Customizing agents*: https://prod.cursor.com/learn/customizing-agents | Rules as static context; skills for specialized/on-demand knowledge. |
| `[DEVIN-AGENTS]` | Devin, *AGENTS.md*: https://docs.devin.ai/desktop/cascade/agents-md | Root/nested `AGENTS.md` discovery and automatic scoping. |
| `[DEVIN-RULES]` | Devin, *Memories & Rules*: https://docs.devin.ai/desktop/cascade/memories | `.devin/rules`, legacy Windsurf fallback, rule activation, character limits, workflows/skills distinction. |
| `[CLINE]` | Cline, *Rules*: https://docs.cline.bot/customization/cline-rules | Rule sources, `.md`/`.txt`, precedence, conditional paths, concise/scannable guidance. |
| `[JUNIE]` | JetBrains, *Guidelines and memory*: https://junie.jetbrains.com/docs/guidelines-and-memory.html | Junie `AGENTS.md` discovery, `.junie/AGENTS.md` exclusivity, global/project precedence. |
| `[JUNIE-KB]` | JetBrains Support, *How to control Junie's quota usage to avoid high token consumption?*: https://youtrack.jetbrains.com/articles/SUPPORT-A-1981/How-to-control-Junies-quota-usage-to-avoid-high-token-consumption | Product-specific practical recommendation to keep guidelines around 20–40 lines. |
| `[MICROSOFT]` | Microsoft, *Write effective instructions for declarative agents*: https://learn.microsoft.com/en-us/microsoft-365/copilot/extensibility/declarative-agent-instructions | Atomic actions, precise verbs, Markdown structure, bullets vs ordered steps. This is general instruction-writing evidence, not repository-file discovery evidence. |
| `[AGENTS]` | AGENTS.md open-format project: https://agents.md/ | Plain-Markdown convention, no required fields, ecosystem support. The project is currently stewarded by the Agentic AI Foundation under the Linux Foundation. |

| `[AMAZON-Q]` | AWS, *Creating project rules for use with Amazon Q Developer chat*: https://docs.aws.amazon.com/amazonq/latest/qdeveloper-ug/context-project-rules.html | `.amazonq/rules/*.md`, automatic project context, multiple project rules. |
| `[CONTINUE]` | Continue, *How to Create and Manage Rules in Continue*: https://docs.continue.dev/customize/deep-dives/rules | `.continue/rules`, Markdown/YAML rule format, `globs` scoping, rule combination. |
| `[ZED]` | Zed, *Instructions*: https://zed.dev/docs/ai/instructions | `AGENTS.md` recommendation, compatibility filenames, first-match project loading, instructions-versus-skills distinction. |
| `[AIDER]` | Aider, *Specifying coding conventions*: https://aider.chat/docs/usage/conventions.html | Read-only conventions files, always-load configuration, small convention-file pattern. |

## Audit note on source conflicts

A current OpenAI documentation issue reports inconsistent wording across Codex documentation about whether `project_doc_max_bytes` is per-file or cumulative. The current Codex implementation decrements one shared remaining byte budget while loading project instruction entries, so this reference records the **implementation-backed cumulative interpretation**. `[OAI-CODE]`

When provider prose and current implementation materially disagree, record the disagreement rather than silently choosing whichever wording is more convenient.
