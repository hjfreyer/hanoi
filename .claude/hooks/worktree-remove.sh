#!/bin/bash

# Read the JSON payload
PAYLOAD=$(cat -)
PATH_TO_REMOVE=$(echo "$PAYLOAD" | jq -r '.worktree_path')

# Tell jj to forget the workspace
cd "$PATH_TO_REMOVE" && jj workspace forget > /dev/null 2>&1

# Delete the workspace directory from the filesystem
rm -rf "$PATH_TO_REMOVE"