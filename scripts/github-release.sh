#!/usr/bin/env bash
# Create GitHub releases for version tags from RELEASE_NOTES.md.
#
#   scripts/github-release.sh [--dry-run] [--update] [TAG...]
#
# With no tags, every v* tag that has no release yet is processed, so the
# script doubles as a backfill. A release is titled "Aufbau X.Y.Z" and its
# body is the "# Aufbau X.Y.Z" section of RELEASE_NOTES.md as committed at
# the tag. GitHub renders a newline in a release body as a line break, so
# hard-wrapped paragraphs and list items are joined into single lines.
# The highest version tag is marked the latest release; any other tag is
# created without touching the latest marker.
#
# An existing release is left alone unless --update is given, which
# replaces its body with the notes from the file; --update needs explicit
# tags so a backfill cannot overwrite hand-edited releases by accident.
# Tags must already be on the remote. Needs `gh` authenticated with write
# access to the repo.
set -euo pipefail

dry_run=false
update=false
while (( $# )); do
  case "$1" in
    --dry-run) dry_run=true ;;
    --update) update=true ;;
    --*) echo "unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
  shift
done

if (( $# )); then
  tags=("$@")
elif [[ "${update}" == true ]]; then
  echo "--update needs the tags to update" >&2
  exit 2
else
  mapfile -t tags < <(git tag --list 'v[0-9]*' --sort=version:refname)
fi
latest="$(git tag --list 'v[0-9]*' --sort=version:refname | tail -n 1)"

# Print the "# Aufbau VERSION" section of RELEASE_NOTES.md at TAG: from its
# heading up to the next heading or "---" separator, without trailing blank
# lines, with each paragraph or list item joined into one line. Fenced
# code blocks are copied verbatim.
notes_for() {
  git show "$1:RELEASE_NOTES.md" | awk -v heading="# Aufbau $2" '
    function flush() { if (cur != "") { lines[++n] = cur; last = n }; cur = "" }
    /^```/ { fence = !fence; if (!fence || on) { flush(); if (on) lines[++n] = $0; last = n }; next }
    fence { if (on) { lines[++n] = $0; last = n }; next }
    /^# / { flush(); on = ($0 == heading) }
    /^---$/ { flush(); on = 0 }
    !on { next }
    /^$/ { flush(); lines[++n] = "" ; next }
    /^#/ { flush(); lines[++n] = $0; last = n; next }
    /^([-*]|[0-9]+\.) / { flush(); cur = $0; next }
    { sub(/^[ \t]+/, ""); cur = (cur == "") ? $0 : cur " " $0 }
    END { flush(); for (i = 1; i <= last; i++) print lines[i] }
  '
}

for tag in "${tags[@]}"; do
  if [[ ! "${tag}" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
    echo "${tag}: not a stable version tag, skipping" >&2
    continue
  fi
  version="${tag#v}"

  exists=false
  if gh release view "${tag}" >/dev/null 2>&1; then
    exists=true
  fi
  if [[ "${exists}" == true && "${update}" != true ]]; then
    echo "${tag}: release exists, skipping"
    continue
  fi

  notes="$(notes_for "${tag}" "${version}")"
  if [[ -z "${notes}" ]]; then
    echo "${tag}: RELEASE_NOTES.md has no '# Aufbau ${version}' section" >&2
    exit 1
  fi

  if [[ "${exists}" == true ]]; then
    verb=edit
    args=(--notes-file -)
  else
    verb=create
    args=(--verify-tag --title "Aufbau ${version}" --notes-file -)
    if [[ "${tag}" == "${latest}" ]]; then
      args+=(--latest)
    else
      args+=(--latest=false)
    fi
  fi

  if [[ "${dry_run}" == true ]]; then
    echo "${tag}: would ${verb} release (${args[*]})"
    continue
  fi
  printf '%s\n' "${notes}" | gh release "${verb}" "${tag}" "${args[@]}"
done
