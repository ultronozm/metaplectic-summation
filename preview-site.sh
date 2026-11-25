#!/bin/bash
# Build a local preview of the deploy snapshot into _site/.
#
# Mirrors .github/workflows/build.yml (dispatch with rebuild_all, no
# carried-forward artifacts) followed by make-index.yml: every note is
# compiled and converted in CI order, failures are retried once, notes that import a
# later note with \externaldocument get the second xr pass, the link
# check runs, and index.html and listing.json are made.  The result holds
# what the deploy branch would: the tracked sources plus *.pdf, *.html,
# *.aux and listing.json.
#
# Before the build, the paper's links to Lean are checked
# (scripts/lean-links.py --check).  After it, the table of statements
# checked in Lean is regenerated in index.org (scripts/lean-table.py),
# in the working tree too, so that it can be committed.  The build fails
# on unresolved references in the LaTeX logs and on "??" in the HTML.
#
# The build starts from a clone of HEAD, overlaid with uncommitted
# changes to tracked files, so edits can be previewed before committing.
# The new site is swapped in only at the end, so a running server keeps
# serving the old one meanwhile.
#
# Serve with:  python3 -m http.server -d _site 8000
# Check with:  node scripts/check-site/check.mjs http://127.0.0.1:8000/

set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

python3 scripts/lean-links.py --check
site="$root/_site.new"

case "$site" in
  */_site.new) ;;
  *) echo "refusing to use $site" >&2; exit 1 ;;
esac
rm -rf -- "$site"
git clone --quiet --no-hardlinks "$root" "$site"

# Overlay uncommitted changes to tracked files.  Untracked files are
# left out, as in CI, so drafts in progress are not built.
git diff --name-only --diff-filter=d HEAD -z |
  xargs -0 -I{} sh -c 'mkdir -p "$(dirname "$2/$1")" && cp -p "$1" "$2/$1"' sh {} "$site"
git diff --name-only --diff-filter=D HEAD -z |
  xargs -0 -I{} rm -f "$site/{}"
(cd "$site" && git add -A)

cd "$site"
export LC_ALL=C

# Determine files to build (rebuild_all).
EXCLUDE=$(jq -r '.exclude[]' config.json)
filter_excludes() {
  while read -r f; do
    [ -z "$f" ] && continue
    base=$(basename "$f")
    stem=${base%.*}
    if ! printf '%s\n' "$EXCLUDE" | grep -qxF "$base" &&
       ! printf '%s\n' "$EXCLUDE" | grep -qxF "$stem"; then
      echo "$f"
    fi
  done
}
git ls-files '*.tex' | awk '!/\//' | filter_excludes | sort -u > .files-to-build.txt || true
git ls-files '*.org' | awk '!/\//' | grep -vx 'index.org' | filter_excludes | sort -u > .org-files-to-build.txt || true

# Compile and convert (see build.yml for the reasoning behind each step).
strip_tocindent() {
  for a in *.aux; do
    [ -e "$a" ] || continue
    perl -i -ne 'print unless /\\newlabel\{tocindent/' "$a"
  done
  return 0
}
build() {
  ./compile.sh "$1" </dev/null >"${1%.tex}.build.log" 2>&1 &&
    ./convert.sh "$1" </dev/null >>"${1%.tex}.build.log" 2>&1
}
FAILED=""
while read -r f; do
  [ -z "$f" ] && continue
  strip_tocindent
  if build "$f"; then echo "OK: $f"; else FAILED="$FAILED $f"; echo "FAILED: $f (will retry)"; fi
done < .files-to-build.txt
RETRY="$FAILED"
FAILED=""
for f in $RETRY; do
  strip_tocindent
  if build "$f"; then echo "OK on retry: $f"; else FAILED="$FAILED $f"; echo "FAILED: $f"; fi
done
ORDER=""
while read -r f; do
  [ -z "$f" ] && continue
  case " $RETRY " in *" $f "*) ;; *) ORDER="$ORDER $f" ;; esac
done < .files-to-build.txt
for f in $RETRY; do
  case " $FAILED " in *" $f "*) ;; *) ORDER="$ORDER $f" ;; esac
done
SECOND=""
rest=" $ORDER "
for f in $ORDER; do
  rest=" ${rest#*" $f "}"
  for dep in $(sed -n 's/^[[:space:]]*\\externaldocument\(\[[^]]*\]\)\{0,1\}{\([^}]*\)}.*/\2/p' "$f"); do
    case "$rest" in
      *" $dep.tex "*) SECOND="$SECOND $f"; break ;;
    esac
  done
done
for f in $SECOND; do
  strip_tocindent
  if build "$f"; then echo "OK on xr pass: $f"; else FAILED="$FAILED $f"; echo "FAILED on xr pass: $f"; fi
done

# Convert Org.
while read -r f; do
  [ -z "$f" ] && continue
  if emacs --batch -l ./tex2html.el --eval "(tex2html-convert-org-file \"$f\")" </dev/null >/dev/null 2>&1; then
    echo "OK: $f"
  else
    FAILED="$FAILED $f"; echo "FAILED: $f"
  fi
done < .org-files-to-build.txt

# Check TeX links (warning-only); the report stays outside the site.
emacs --batch -l ./tex2html.el --eval '(tex2html-check-links "link-check-report.md")' >/dev/null 2>&1 || true
mv link-check-report.md "$root/link-check-report.md"

# Regenerate the Lean table of the landing page from the fresh aux file,
# and carry it back to the working tree.
paper=schwartz-space-n-fold-cover-sl2
if [ -e "$paper.aux" ] && python3 scripts/lean-table.py "$paper.aux"; then
  if ! cmp -s index.org "$root/index.org"; then
    cp index.org "$root/index.org"
    echo "index.org: Lean table updated in the working tree; commit it."
  fi
else
  FAILED="$FAILED (lean-table)"
fi

# make-index.yml
emacs --batch -l ./tex2html.el --eval "(tex2html-make-index)" >/dev/null 2>&1 || FAILED="$FAILED index.org"

# Keep the LaTeX logs outside the site, and fail on unresolved references.
logs="$root/_site-logs"
rm -rf -- "$logs"; mkdir -p "$logs"
while read -r f; do
  [ -z "$f" ] && continue
  for ext in log build.log; do
    [ -e "${f%.tex}.$ext" ] && cp -p "${f%.tex}.$ext" "$logs/"
  done
done < .files-to-build.txt
if grep -E -H "(Reference|Citation) .* undefined|There were undefined|Label\(s\) may have changed|Rerun to get cross-references" \
     "$logs"/*.log | grep -v '\.build\.log:' >"$logs/undefined.txt"; then
  echo "Unresolved references (logs in $logs):" >&2
  cat "$logs/undefined.txt" >&2
  FAILED="$FAILED (unresolved-references)"
fi
# A reference tex2html could not resolve shows as ?? in the HTML.
if grep -l '??' *.html >"$logs/html-unresolved.txt"; then
  echo "?? in HTML:" >&2
  cat "$logs/html-unresolved.txt" >&2
  FAILED="$FAILED (html-unresolved)"
fi

# Keep only what the deploy branch would contain.
git ls-files --others -z | while IFS= read -r -d '' f; do
  case "$f" in
    */*) ;;
    *.pdf|*.html|*.aux|listing.json) continue ;;
  esac
  rm -f -- "$f"
done
rm -rf -- .git

echo
echo "Link check: $(sed -n 3p "$root/link-check-report.md")"
grep '^- ' "$root/link-check-report.md" || true
if [ -n "$FAILED" ]; then
  echo "Failed:$FAILED" >&2
  exit 1
fi
n_html=$(ls *.html | wc -l | tr -d ' '); n_pdf=$(ls *.pdf | wc -l | tr -d ' ')
cd "$root"
# Swap the new build in at the end, so a running server keeps serving the old one meanwhile.
rm -rf -- "$root/_site.old"
[ -d "$root/_site" ] && mv -- "$root/_site" "$root/_site.old"
mv -- "$site" "$root/_site"
rm -rf -- "$root/_site.old"
echo "Built $n_html HTML pages and $n_pdf PDFs in $root/_site"
