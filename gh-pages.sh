#!/usr/bin/env bash

# Exit immediately if any command fails
set -e

# Prevent infinite loops when the script itself runs 'git push'
if [[ -n "$GH_PAGES_DEPLOYING" ]]; then
    exit 0
fi

# Clean up any broken or lingering worktrees from previous failed runs
git worktree prune

# Build the project (replace with your actual build command if needed)
cd paper && latexmk -pdf -f main.tex && cd -

# Check out the gh-pages branch files into a temporary directory
# This avoids switching branches in your working directory
TARGET_DIR=$(mktemp -d)
git worktree add "$TARGET_DIR" gh-pages

# Delete all existing files in the gh-pages worktree (except .git)
# This ensures stale build assets are removed
find "$TARGET_DIR" -mindepth 1 -maxdepth 1 ! -name '.git' -exec rm -rf {} +

# Copy the contents of dist/ to the root of the gh-pages worktree
cp -r paper/main.pdf "$TARGET_DIR"

# Navigate to the worktree to commit and push changes
cd "$TARGET_DIR"
git add -A
git commit --allow-empty -m "Deploy to GitHub Pages: $(date)"
git push origin gh-pages

# Clean up the temporary worktree
cd -
git worktree remove "$TARGET_DIR"

echo "✅ Deployment successful!"

exit 0

