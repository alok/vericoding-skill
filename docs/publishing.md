# Publishing

Where this skill is listed, how it got there, and what's left. Checked against each venue's own docs
on 2026-10-24.

## Live

| Venue | Status (2026-10-24) |
|---|---|
| GitHub | https://github.com/alok/vericoding-skill, releases v0.1.0 and v0.1.1 via `gh skill publish` |
| Claude Code marketplace | `/plugin marketplace add alok/vericoding-skill`, then `/plugin install vericoding@vericoding-skill`; install tested in an isolated config |
| skills.sh (`npx skills`) | Listed at https://skills.sh/alok/vericoding-skill/vericoding after the first install |
| `gh skill` | `gh skill install alok/vericoding-skill`; found by `gh skill search vericoding` |

## Crawled, no action needed

| Venue | Mechanism |
|---|---|
| SkillsMP, claude-plugins.dev | Crawl public GitHub for `SKILL.md` |
| claudemarketplaces.com | Crawls marketplace files; pulls install counts from skills.sh |
| Gemini CLI extension gallery | `gemini-extension.json` at the root plus the `gemini-cli-extension` topic; crawled daily |

## Submitted, awaiting review

| Venue | Where | Status |
|---|---|---|
| Copilot CLI default marketplace (github/awesome-copilot) | https://github.com/github/awesome-copilot/issues/5397 | All automated gates pass on v0.1.1 (`ready-for-review`); waiting for a maintainer `/approve`. The first run failed for lack of a root `plugin.json`, which v0.1.1 added. |

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

1. Bump `version` in `plugin.json` (Agent Plugins 1.0, read by Copilot, Codex and Cursor),
   `.claude-plugin/plugin.json`, `.claude-plugin/marketplace.json`, `scripts/vc_check.py` (`VERSION`),
   `gemini-extension.json` and `skills/vericoding/SKILL.md` (`metadata.version`).
2. `python3 -m unittest discover -s tests` and `claude plugin validate --strict --profile directory .`
3. `gh skill publish --tag vX.Y.Z`
4. The Anthropic directory and awesome-copilot pick up the tracked branch or need a re-review comment.
