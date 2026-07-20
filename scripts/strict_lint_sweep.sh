#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

log="$(mktemp)"
trap 'rm -f "$log"' EXIT

status=0
while IFS= read -r file; do
  : >"$log"
  if ! lake env lean \
      -Dlinter.flexible=true \
      -Dlinter.style.longLine=true \
      -Dlinter.style.multiGoal=true \
      -Dlinter.style.openClassical=true \
      "$file" >"$log" 2>&1; then
    echo "ERROR: strict elaboration failed: $file"
    cat "$log"
    status=1
  elif [[ -s "$log" ]]; then
    echo "ERROR: strict linter output: $file"
    cat "$log"
    status=1
  fi
done < <(find KolmogorovMathlib -type f -name '*.lean' -print | LC_ALL=C sort; printf '%s\n' KolmogorovMathlib.lean)

exit "$status"
