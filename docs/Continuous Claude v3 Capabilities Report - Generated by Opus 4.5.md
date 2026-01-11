# CCV3 (Continuous Claude v3) Capabilities Report
Generated: 2026-01-10

## Summary

CCV3 is a comprehensive Claude Code enhancement framework featuring 100+ skills, 30+ specialized agents, multi-step workflows, an extensive hook system, and a persistent memory system.

---

## 1. Skills (Slash Commands)

### Core Workflows
- /fix - Bug investigation and resolution (sleuth -> premortem -> kraken -> arbiter -> commit)
- /build - Feature implementation (architect -> kraken -> arbiter)
- /explore - Codebase exploration (scout)
- /debug - Deep investigation (sleuth -> debug-agent -> profiler)
- /tdd - Test-driven development (arbiter -> kraken -> arbiter)
- /review - Code review (critic, judge)
- /refactor - Code transformation (phoenix -> kraken -> judge)

### Session Management
- /create_handoff - Create handoff for new session
- /resume_handoff - Resume from handoff
- /continuity_ledger - Save state for compaction
- /onboard - Onboard to brownfield project

### Development Tools
- /commit - Git commits with approval
- /describe_pr - Generate PR descriptions
- /premortem - Risk analysis before implementation
- /recall - Search past learnings
- /remember - Store new learning
- /test - Test execution
- /release - Version bumps and changelog

### Research
- /perplexity-search - AI web research
- /nia-docs - Library documentation
- /github-search - GitHub code/repos/issues
- /firecrawl-scrape - Web scraping
- /morph-search - Fast text search (20x grep)
- /ast-grep-find - Structural code search
- /recall-reasoning - Past reasoning search

### Code Analysis
- /tldr-code - Token-efficient context (CFG, DFG, call graph)
- /qlty-check - Linting, auto-fix (70+ linters)
- /braintrust-analyze - Session analysis

### Math
- /math - Unified math entry (SymPy, Z3, Pint)
- /prove - Formal verification (Lean 4)
- /pint-compute - Unit conversions

### Meta Skills
- /help - Interactive discovery
- /workflow-router - Goal-based routing
- /skill-developer - Create skills
- /hook-developer - Hook reference
- /debug-hooks - Debug hooks
- /mot - System health check

---

## 2. Agents

### Exploration and Research
- scout (Sonnet) - Codebase exploration
- oracle (Sonnet) - External research
- pathfinder (Sonnet) - External repo analysis

### Planning and Architecture
- architect (Sonnet) - Feature planning
- plan-agent (Sonnet) - Implementation plans
- phoenix (Sonnet) - Refactoring planning

### Implementation
- kraken (Opus) - TDD implementation, resumable
- spark (Haiku) - Quick fixes

### Review and Validation
- arbiter (Sonnet) - Test execution
- critic (Sonnet) - Code review
- judge (Sonnet) - Refactoring review
- aegis (Sonnet) - Security analysis

### Investigation
- sleuth (Sonnet) - Bug investigation
- debug-agent (Sonnet) - Log analysis
- profiler (Sonnet) - Performance

### Documentation
- scribe (Sonnet) - Documentation
- chronicler (Sonnet) - Learning extraction
- herald (Sonnet) - Release notes

---

## 3. Workflows

### /fix (Bug Resolution)
Scopes: bug, hook, deps, pr-comments
Chain: sleuth -> [HUMAN] -> premortem -> kraken -> [HUMAN] -> commit

### /build (Feature Implementation)
Modes: greenfield, brownfield, tdd
Chain: plan-agent -> premortem deep -> kraken -> arbiter -> commit

---

## 4. Hooks

### Session Lifecycle
- session-register (SessionStart) - DB registration
- session-start-continuity (resume) - Restore state
- session-end-cleanup (SessionEnd) - Cleanup
- session-outcome (SessionEnd) - Outcome prompt

### User Prompts
- skill-activation-prompt - Suggest skills
- memory-awareness - Inject learnings
- impact-refactor - Refactoring warnings

### Tool Interception
- tldr-read-enforcer (Read) - Suggest tldr
- smart-search-router (Grep) - Route to ast-grep
- file-claims (Edit) - Track ownership
- signature-helper (Edit) - Inject signatures

### Post-Edit
- typescript-preflight - Type-check
- compiler-in-the-loop - Compiler validation
- import-validator - Validate imports
- post-edit-diagnostics - Run diagnostics

---

## 5. Memory System

### Recall
cd opc and run: uv run python scripts/core/recall_learnings.py --query topic

### Store
cd opc and run: uv run python scripts/core/store_learning.py --session-id x --type WORKING_SOLUTION --content ...

Types: WORKING_SOLUTION, FAILED_APPROACH, ARCHITECTURAL_DECISION, CODEBASE_PATTERN, ERROR_FIX, USER_PREFERENCE, OPEN_THREAD

---

## 6. CLI Tools

### TLDR
- tldr tree src/ - File tree
- tldr structure src/ - Code structure
- tldr cfg file.py func - Control flow
- tldr dfg file.py func - Data flow
- tldr impact func src/ - Reverse call graph
- tldr dead src/ - Dead code
- tldr diagnostics . - Type check + lint

---

## 7. Key Files

- .claude/settings.json - Hook configuration
- .claude/skills/*/SKILL.md - Skill definitions
- .claude/skills/skill-rules.json - Activation triggers
- .claude/agents/*.md - Agent definitions
- .claude/rules/*.md - Always-on instructions
- .claude/hooks/src/*.ts - Hook source
- opc/scripts/core/ - Memory scripts
- thoughts/shared/plans/ - Plans
- thoughts/shared/handoffs/ - Handoffs

---

## 8. Best Practices

1. Use workflows, not individual agents
2. Run premortem before implementation
3. Create handoffs before ending sessions
4. Store learnings for memory
5. Delegate to agents (keep main context clean)
6. Use scout over Explore (more accurate)
7. Use tldr before reading files (95% savings)
8. Check memory before researching
