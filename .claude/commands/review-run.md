# Review Autonomous Run

Review the results of an autonomous agent run and summarize what was accomplished.

## Usage

```
/review-run
```

## Instructions

### Step 1: Gather Context

Check the current state:

1. **Git status**: What files were changed?
   ```bash
   git status
   git diff --stat
   ```

2. **Recent commits**: What was committed?
   ```bash
   git log --oneline -10
   ```

3. **Todo list**: Check current todos for completed items

### Step 2: Analyze Changes

For each changed file:

1. **Read the diff**: Understand what changed
2. **Categorize**: Bug fix, feature, refactor, docs, etc.
3. **Assess quality**: Are there issues?

### Step 3: Generate Summary

Create a summary report:

```markdown
# Run Summary

**Date:** <date>
**Duration:** <if known>

## Changes Made

### Files Modified
| File | Type | Description |
|------|------|-------------|
| <file> | <type> | <what changed> |

### Commits Created
- `<hash>`: <message>

## Quality Assessment

### Completed Successfully
- <item 1>
- <item 2>

### Issues Found
- <issue 1>
- <issue 2>

### Needs Review
- <item requiring human review>

## Recommendations

1. <recommendation>
2. <recommendation>

## Next Steps

- [ ] <follow-up task>
- [ ] <follow-up task>
```

### Step 4: Check for Problems

Look for common issues:

1. **Incomplete changes**: Files mentioned but not modified
2. **Test failures**: Run tests if applicable
3. **Build errors**: Check if project still builds
4. **Leftover debug code**: `console.log`, `dbg!`, etc.
5. **Sorries added**: In Lean projects, check for new `sorry`

### Step 5: Report

Present the summary to the user with actionable next steps.

## Notes

- Be honest about what worked and what didn't
- Highlight anything that needs human verification
- Suggest improvements for future runs
