#!/bin/bash
# Read the JSON payload from Claude Code via stdin
PAYLOAD=$(cat -)
NAME=$(echo "$PAYLOAD" | jq -r '.name')
CWD=$(echo "$PAYLOAD" | jq -r '.cwd')

# Define where the jj workspace should be created
WORKSPACE_BASE="$CWD/.claude/workspaces/"
mkdir -p "$WORKSPACE_BASE"
WORKSPACE_DIR="$WORKSPACE_BASE/$NAME"

# Create the jj workspace (redirect output to keep stdout clean)
jj workspace add "$WORKSPACE_DIR" > /dev/null 2>&1

echo "$WORKSPACE_DIR"