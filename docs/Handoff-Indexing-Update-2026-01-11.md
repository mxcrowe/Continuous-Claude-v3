# Handoff Indexing Summary (2026-01-11) - Orion (Codex 5.2)

## Goal
Make handoff indexing more consistent by standardizing summaries and improving fallback behavior when headings vary.

## What Changed
- Added explicit Context section headings guidance for markdown handoffs in `.claude/skills/create_handoff/SKILL.v6.md`.
- Made `summary` a required field in YAML handoffs in `.claude/skills/create_handoff/SKILL.md`.
- Updated `opc/scripts/core/artifact_index.py` to:
  - Prefer `summary` in YAML frontmatter when present.
  - Fall back to other sections or the first paragraph if summary headings are missing.
  - Index handoff files with `.yaml` and `.yml` extensions (in addition to `.md`).

## Why
Handoff queries were returning empty or inconsistent summaries when files lacked the expected headings. Requiring a summary field and adding robust fallback logic ensures a reliable snippet for search and statusline use.

## Validation Performed
- Created a minimal handoff without a Summary heading.
- Indexed the file and confirmed it could be found via `artifact_query.py` using a keyword in the content.

## Follow-ups
- Encourage all handoffs to include `summary:` in YAML frontmatter.
- If desired, mirror the `summary:` addition into other handoff templates and auto-handoff generators.
