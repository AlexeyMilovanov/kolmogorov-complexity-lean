#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

list_files=false
shard_count=1
shard_index=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --list-files)
      list_files=true
      shift
      ;;
    --shard-count)
      if [[ $# -lt 2 ]]; then
        echo "ERROR: --shard-count requires a value"
        exit 1
      fi
      shard_count="$2"
      shift 2
      ;;
    --shard-index)
      if [[ $# -lt 2 ]]; then
        echo "ERROR: --shard-index requires a value"
        exit 1
      fi
      shard_index="$2"
      shift 2
      ;;
    *)
      echo "ERROR: Unknown argument: $1"
      exit 1
      ;;
  esac
done

if [[ ! "$shard_count" =~ ^[1-9][0-9]{0,9}$ ]] ||
    (( 10#$shard_count > 2147483647 )); then
  echo "ERROR: --shard-count must be an integer between 1 and 2147483647"
  exit 1
fi
if [[ ! "$shard_index" =~ ^(0|[1-9][0-9]{0,9})$ ]] ||
    (( 10#$shard_index >= 10#$shard_count )); then
  echo "ERROR: --shard-index must be an integer in [0, shard-count)"
  exit 1
fi
shard_count=$((10#$shard_count))
shard_index=$((10#$shard_index))

logdir="$(mktemp -d)"
trap 'rm -rf "$logdir"' EXIT

unsorted_inventory="$logdir/inventory.unsorted"
inventory="$logdir/inventory"
if ! find KolmogorovMathlib -type f -name '*.lean' -print0 \
    >"$unsorted_inventory"; then
  echo "ERROR: failed to enumerate project Lean sources"
  exit 1
fi
printf '%s\0' KolmogorovMathlib.lean >>"$unsorted_inventory"
if ! LC_ALL=C sort -z "$unsorted_inventory" >"$inventory"; then
  echo "ERROR: failed to sort the project Lean source inventory"
  exit 1
fi

mapfile -d '' -t all_files <"$inventory"
files=()
for i in "${!all_files[@]}"; do
  if (( i % shard_count == shard_index )); then
    files+=("${all_files[i]}")
  fi
done

if [[ "$list_files" == true ]]; then
  for f in "${files[@]}"; do
    echo "$f"
  done
  exit 0
fi

export logdir
worker() {
  local index="$1"
  local file="$2"
  local log="$logdir/$index.log"
  local status_file="$logdir/$index.status"

  if ! lake env lean \
      -Dlinter.flexible=true \
      -Dlinter.style.longLine=true \
      -Dlinter.style.multiGoal=true \
      -Dlinter.style.openClassical=true \
      "$file" >"$log" 2>&1; then
    printf '1\n' >"$status_file"
  elif [[ -s "$log" ]]; then
    printf '2\n' >"$status_file"
  else
    printf '0\n' >"$status_file"
  fi
}
export -f worker

dispatch_status=0
for index in "${!files[@]}"; do
  printf '%s\0%s\0' "$index" "${files[index]}"
done | xargs -0 -r -n 2 -P 2 bash -c 'worker "$1" "$2"' _ ||
  dispatch_status=$?

status=0
for index in "${!files[@]}"; do
  file="${files[index]}"
  log="$logdir/$index.log"
  status_file="$logdir/$index.status"

  if [[ ! -f "$status_file" ]]; then
    echo "ERROR: missing worker status for $file"
    status=1
  else
    file_status="$(cat "$status_file")"
    if [[ "$file_status" == "1" ]]; then
      echo "ERROR: strict elaboration failed: $file"
      cat "$log"
      status=1
    elif [[ "$file_status" == "2" ]]; then
      echo "ERROR: strict linter output: $file"
      cat "$log"
      status=1
    elif [[ "$file_status" != "0" ]]; then
      echo "ERROR: unknown worker status for $file"
      status=1
    fi
  fi
done
if [[ "$dispatch_status" != 0 ]]; then
  echo "ERROR: strict worker dispatch failed with status $dispatch_status"
  status=1
fi

exit "$status"
