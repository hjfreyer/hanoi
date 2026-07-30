#!/bin/bash
# Read the JSON payload from Claude Code via stdin
PAYLOAD=$(cat -)
NAME=$(echo "$PAYLOAD" | jq -r '.name')
CWD=$(echo "$PAYLOAD" | jq -r '.cwd')

# Define where the jj workspace should be created
WORKSPACE_DIR="$CWD/.claude/workspaces/$NAME"

# Create the jj workspace (redirect output to keep stdout clean)
jj workspace add "$WORKSPACE_DIR" > /dev/null 2>&1

# Claude Code expects the absolute path to the new workspace on stdout
ABS_PATH=$(cd "$WORKSPACE_DIR" && pwd)
echo "$ABS_PATH"