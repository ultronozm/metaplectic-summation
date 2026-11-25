#!/bin/bash
# Stage the exercise sheets for the site build.
#
# The sheets live in exercises/, but the tex-site machinery builds only
# top-level files.  Copy them to the top level of the build checkout and
# add them to its index, so that they are built, their aux files serve
# the \externaldocument references between them, and the deploy snapshot
# carries their sources for the TeX links.  Run this only in a throwaway
# checkout (CI, or the clone made by preview-site.sh), never in the
# working tree.

set -euo pipefail
top=$(git rev-parse --show-toplevel)
case "$top" in
  */_site.new) ;;
  *) [ "${GITHUB_ACTIONS:-}" = true ] || { echo "refusing to stage in $top" >&2; exit 1; } ;;
esac
cd "$top"
for f in exercises/*.tex; do
  cp -p "$f" .
  git add -- "$(basename "$f")"
done
