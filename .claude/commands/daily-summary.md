# Daily Work Summary

Generate a concise executive summary of work since the last summary.

## Step 1: Gather Data

```bash
# Find most recent summary file
LAST_SUMMARY=$(ls -t history/summaries/*.md 2>/dev/null | head -1)

# Get timestamp from last summary (look for "Generated:" line)
if [[ -n "$LAST_SUMMARY" ]]; then
    LAST_DATE=$(grep "Generated:" "$LAST_SUMMARY" | sed 's/.*Generated: //' | cut -d' ' -f1)
    echo "Last summary: $LAST_SUMMARY ($LAST_DATE)"
    SINCE="$LAST_DATE"
else
    echo "No previous summary found, using today"
    SINCE="today 00:00"
fi

# Git commits since last summary
git log --since="$SINCE" --pretty=format:"%h - %s"

# Check TODO files for completed items (moved to DONE/)
ls DONE/*.md 2>/dev/null | head -5
```

**Key:** The summary covers work since the **last summary timestamp**, not just "today". This handles:
- Late night work sessions
- Multi-day gaps between summaries
- Work spanning midnight

## Step 2: Write Summary

Create `history/summaries/YYYY-MM-DD.md` with this structure:

```markdown
# Daily Summary: YYYY-MM-DD

## Accomplishments

- **Major achievement 1** (context or result)
- **Major achievement 2**:
  - Sub-item with detail if needed
  - Another sub-item
- **Major achievement 3** (reference to TODO or doc if applicable)

## Status Changes

- project: ⚠️ → ✅ (reason)
- project: Created (N new subprojects/files)

## Next Steps

1. Priority task (TODO reference)
2. Another priority task
3. Third task
4. Fourth task (aim for 4-6 items)

---
*Generated: YYYY-MM-DD HH:MM*
```

## Guidelines

**Content priorities:**
1. **Completed TODOs** - mention by name when moved to DONE/
2. **New projects/subprojects** - list with one-line description of purpose
3. **Framework/architecture work** - docs, plans, coordination systems
4. **Infrastructure** - scripts, tools, automation
5. **Numerical results** - only if significant milestones

**For new subprojects, describe their purpose:**
```
- **Created new project structure**:
  - projectA/ - Description of project A purpose
  - projectB/ - Description of project B purpose
```

**For next steps, be comprehensive:**
- Include 4-6 items spanning different areas
- Reference TODO files when applicable
- Include ongoing work

**DON'T include:**
- Lock status changes (infrastructure detail)
- Every file modified
- Consistency check output
- Trivial edits

## If Summary Exists

Ask user: "Summary exists. (1) Append, (2) Replace, or (3) Skip?"
