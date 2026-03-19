# Summarize arXiv Paper

Fetch and summarize an arXiv paper, creating a standardized summary file.

## Usage

```
/arxiv-summarize <arxiv_id_or_url>
```

Examples:
- `/arxiv-summarize 2301.12345`
- `/arxiv-summarize https://arxiv.org/abs/2301.12345`

## Instructions

### Step 1: Parse the arXiv ID

Extract the arXiv ID from the input (e.g., `2301.12345` from URL or direct input).

### Step 2: Fetch the Paper

Use WebFetch to get the abstract page:

```
WebFetch(url: "https://arxiv.org/abs/<arxiv_id>", prompt: "Extract the title, authors, abstract, and subjects")
```

### Step 3: Get the PDF (Optional)

If more detail is needed, fetch the PDF:
- PDF URL: `https://arxiv.org/pdf/<arxiv_id>.pdf`

### Step 4: Create Summary File

Create `refs/<arxiv_id>.md` with this structure:

```markdown
# <Paper Title>

**arXiv:** [<arxiv_id>](https://arxiv.org/abs/<arxiv_id>)
**Authors:** <author list>
**Submitted:** <date>
**Subjects:** <subject areas>

## Abstract

<original abstract>

## Summary

<2-3 paragraph summary of the paper's main contributions>

## Key Results

1. **<Result 1>**: <description>
2. **<Result 2>**: <description>
...

## Relevance to This Project

<How this paper relates to the current codebase, if applicable>

## Key Definitions/Theorems

| Name | Statement | Reference |
|------|-----------|-----------|
| <name> | <informal statement> | Theorem X.Y |

## Notes

- <Additional notes>
- <Questions for follow-up>
```

### Step 5: Report

Output:
```
Created: refs/<arxiv_id>.md

Paper: <title>
Authors: <authors>
Key topics: <subjects>

Summary highlights:
- <point 1>
- <point 2>
```

## Directory Structure

Papers are saved to `refs/` directory:
```
refs/
├── 2301.12345.md
├── 2302.67890.md
└── ...
```

Create the `refs/` directory if it doesn't exist.

## Notes

- Focus on mathematical content relevant to formalization
- Highlight definitions that could be formalized
- Note any existing Lean/Coq/Isabelle formalizations mentioned
- Cross-reference with other papers in refs/ if relevant
