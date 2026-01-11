# Local Setup Notes (CCV3 + Hexis)

## Summary
This environment is configured to run CCV3 with local embeddings, Postgres memory, and SQLite handoff indexing. Hooks are enabled via CC_ALLOWLIST.

## Key Configuration
- Postgres stack: `G:\Dev\Continuous-Claude-v3\docker\docker-compose.yml`
- Port: 55432 (set POSTGRES_PORT=55432 when starting stack)
- DB: continuous_claude
- opc env: `G:\Dev\Continuous-Claude-v3\opc\.env`
  - DATABASE_URL, OPC_POSTGRES_URL, AGENTICA_POSTGRES_URL all set to 55432/continuous_claude

## Embeddings
- Local embeddings require: `sentence-transformers` + `torch`
- Fixed schema: `archival_memory.embedding` uses `vector(1024)`
- Store/recall test:
  - `uv run python scripts/core/store_learning.py ...`
  - `uv run python scripts/core/recall_learnings.py --query "MVP test"`

## Hooks / Allowlist
- CC_ALLOWLIST set in VS Code settings:
  - `G:\Dev\Continuous-Claude-v3;G:\Dev\llm-council`
- Hooks rebuilt with `bash .claude/hooks/build.sh`

## Handoffs (SQLite Context Graph)
- Handoffs index into SQLite: `.claude/cache/artifact-index/context.db`
- Files must be under `thoughts/shared/handoffs/...` to auto-index
- Search works only if headings include:
  - `## Summary` (or Session Summary / Top 5 Correctness Risks via parser patch)
- Index manually:
  - `uv run python opc/scripts/core/artifact_index.py --file <handoff>`
- Query:
  - `uv run python opc/scripts/core/artifact_query.py "keyword" --type handoffs`

## Local Patches Applied
- `docker/init-schema.sql`: embedding dim 1024
- `opc/scripts/core/recall_learnings.py`: fix sys.path for scripts.* imports
- `opc/scripts/core/artifact_index.py`: map Session Summary / Top 5 Correctness Risks to summary

## Known Gotchas
- `recall_learnings.py` needs `scripts.*` import fix (patched)
- FTS queries require matching words from summary fields
- Running index/query from different cwd points to different SQLite DBs
