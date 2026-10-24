# Publishing

Where this skill is listed, how it got there, and what's left. Checked against each venue's own docs
on 2026-10-24.

## Automatic once the repo is public

| Venue | Mechanism |
|---|---|
| Claude Code marketplace | `.claude-plugin/marketplace.json` at the root: `/plugin marketplace add alok/vericoding-skill` |
| `gh skill` | `gh skill publish --tag vX.Y.Z` validates against the Agent Skills spec, adds the `agent-skills` topic, cuts a release |
| skills.sh (`npx skills`) | Indexed on the first `npx skills add alok/vericoding-skill`; ranked by installs |
| SkillsMP, claude-plugins.dev | Crawl public GitHub for `SKILL.md` |
| claudemarketplaces.com | Crawls marketplace files; pulls install counts from skills.sh |
| Gemini CLI extension gallery | `gemini-extension.json` at the root plus the `gemini-cli-extension` topic; crawled daily |

## Submitted

| Venue | How | Notes |
|---|---|---|
| Copilot CLI default marketplace (github/awesome-copilot) | Issue in their external-plugin form format, pinned to a release tag and SHA | Bots run quality gates; a maintainer comments `/approve` |

## Needs the owner

| Venue | Steps | Why it can't be automated |
|---|---|---|
| Anthropic plugin directory (claude.ai, Cowork, Claude Code `@claude-community`) | claude.ai/directory/manage → Submit new → Plugin bundle → `alok/vericoding-skill`, path `/` → Validate → data-handling and compliance answers → Submit → Publish after review | Needs the owner's claude.ai account and attestations. Answers: the plugin makes no network calls, collects no data, and runs local verifiers only. |
| ClawHub (OpenClaw) | `npm i -g clawhub && clawhub login && clawhub skill publish ./skills/vericoding --slug vericoding --name "Vericoding" --categories development --topics "lean4,formal-verification,vericoding"` | Needs a GitHub device-flow login, and everything published there is relicensed MIT-0 |
| OpenAI plugin directory | Zip upload in the plugin portal | Needs a verified OpenAI org; display name and short description at most 30 characters each |
| Cursor Marketplace | Form at cursor.com/marketplace/publish | Manual review, form needs the owner |
| Smithery | `PUT api.smithery.ai/skills/{namespace}/{slug}` with the git URL | Needs a Smithery API key |

## Later (venues with an age or usage bar)

| List | Bar | Earliest |
|---|---|---|
| VoltAgent/awesome-agent-skills | "real community usage" | after some installs |
| hesreallyhim/awesome-claude-code | 14 days old with continued commits, or 100 stars; web form only | 2026-11-07 |
| heilcheng/awesome-agent-skills | 20 stars, 14 days old | 2026-11-07 |
| JGalego/awesome-vericoding | public, documented, installable; one resource per PR; unreviewed AI-written PRs are closed | now, by the owner |

## Releasing a new version

1. Bump `version` in `.claude-plugin/plugin.json`, `.claude-plugin/marketplace.json`,
   `gemini-extension.json` and `skills/vericoding/SKILL.md` (`metadata.version`).
2. `python3 -m unittest discover -s tests` and `claude plugin validate --strict --profile directory .`
3. `gh skill publish --tag vX.Y.Z`
4. The Anthropic directory and awesome-copilot pick up the tracked branch or need a re-review comment.
