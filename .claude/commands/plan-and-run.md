# Plan and Run Autonomous Agent

Plan a multi-step task and execute it autonomously.

## Usage

```
/plan-and-run <task_description>
```

## Instructions

### Phase 1: Planning

1. **Understand the task** - Parse the user's request
2. **Explore the codebase** - Use Glob, Grep, Read to understand context
3. **Identify dependencies** - What needs to happen first?
4. **Create todo list** - Use TodoWrite to create actionable items
5. **Present plan** - Show the user the planned steps

### Phase 2: Confirmation

Ask the user to confirm the plan before execution:

```
Plan created with <N> steps:
1. <step 1>
2. <step 2>
...

Proceed? [Y/n]
```

### Phase 3: Execution

For each todo item:

1. Mark as `in_progress`
2. Execute the step
3. Verify success
4. Mark as `completed`
5. Update user on progress

### Phase 4: Summary

Report final status:

```
=== EXECUTION COMPLETE ===

Completed: <N>/<M> tasks
- <task 1>: done
- <task 2>: done
...

Changes made:
- <file1>: <description>
- <file2>: <description>

Remaining issues:
- <any blockers or follow-ups>
```

## Best Practices

- **Atomic steps**: Each todo should be independently verifiable
- **Checkpoints**: Pause for user input on critical decisions
- **Rollback plan**: Know how to undo changes if needed
- **Progress visibility**: Keep todos updated in real-time

## Error Handling

If a step fails:

1. Mark todo as `in_progress` (not completed)
2. Create new todo for the fix
3. Ask user whether to:
   - Retry with a different approach
   - Skip and continue
   - Abort the remaining plan

## Example

```
User: /plan-and-run Add unit tests for the Covariance module