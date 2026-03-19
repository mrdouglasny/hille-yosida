# Pick Next TODO Task

Scan the TODO/ directory and help the user choose which task to work on next.

## Step 1: Scan and Parse

Read all TODO/*.md files (excluding README.md, _template.md). For each file, extract:
- **Priority**: HIGH, MEDIUM, or LOW
- **Status**: Look for ✅ COMPLETED, 🔄 IN PROGRESS, ⚠️ NOT STARTED
- **Lead Model**: Claude or Gemini (prefer Claude-led tasks)
- **Category**: L0 Formal, L1 Symbolic, L2 Reference, L3 Production, Infrastructure
- **Goal**: First sentence of the Goal section

## Step 2: Filter and Rank

1. Exclude tasks marked ✅ COMPLETED
2. **Check lock status** (if locks MCP available):
   - For each task, identify which subproject(s) it affects
   - If a subproject is locked by another agent, mark task as 🔒 LOCKED
   - Locked tasks should still be shown but deprioritized
3. Sort by:
   - HIGH priority first
   - Unlocked tasks before locked tasks
   - Claude-led tasks preferred
   - NOT STARTED before IN PROGRESS (unless resuming makes sense)

## Step 3: Present Options

Show top 5-6 candidates in this format:

```
=== Available Tasks ===

1. [HIGH] 03_lean_proofs.md
   Goal: Complete formal proofs for core theorems
   Status: 🔄 IN PROGRESS | Lead: Claude | Project: lean

2. [MEDIUM] 04_analysis.md
   Goal: Run convergence analysis
   Status: ⚠️ NOT STARTED | Lead: Claude | Project: analysis

3. [HIGH] 🔒 07_verification.md
   Goal: Verify numerical results
   Status: ⚠️ NOT STARTED | Lead: Claude | Project: verify (locked by gemini)

Which task should I work on? (1-N, or 'skip', or 'show <n>' for details)
```

## Step 4: Handle User Response

- **Number (1-5)**: Read full task file, acquire lock if needed, begin work
- **'skip'**: End without action
- **'show N'**: Display full contents of task N, then re-ask
- **'other'**: Ask user which specific file to work on

## Step 5: Execute Task

Once user picks a task:

1. Read the full task file
2. Check if project lock is needed
   - If so, use `lock_acquire` with your task description
3. Create a todo list from the Acceptance Criteria
4. Work through each criterion systematically
5. Update the task file's Log section with progress
6. When all criteria met:
   - Mark status as ✅ COMPLETED
   - Move file to DONE/ directory
   - Release any locks held
   - Update history if configured

## Notes

- Follow project PROTOCOL.md conventions for any code changes
- Validate work against acceptance criteria before marking complete
- If blocked, update task status to 🔄 IN PROGRESS with notes and ask user for guidance
