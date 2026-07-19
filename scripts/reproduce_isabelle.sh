#!/usr/bin/env bash
set -euo pipefail

readonly ISABELLE_IMAGE="makarius/isabelle@sha256:9bd33b183c399327c5d554fc8cde27c29b5d2b20cdc6fe7a604caa3f951018fc"

reproduce() {
  local archive_url="$1"
  local archive_sha256="$2"
  local directory="$3"
  local session="$4"

  docker run --rm \
    --entrypoint /bin/bash \
    --env AFP_ARCHIVE_URL="$archive_url" \
    --env AFP_ARCHIVE_SHA256="$archive_sha256" \
    --env AFP_DIRECTORY="$directory" \
    --env AFP_SESSION="$session" \
    "$ISABELLE_IMAGE" \
    -lc '
      set -euo pipefail
      mkdir -p /tmp/afp
      curl -sSfL "$AFP_ARCHIVE_URL" -o /tmp/afp-entry.tar.gz
      echo "$AFP_ARCHIVE_SHA256  /tmp/afp-entry.tar.gz" | sha256sum --check --strict
      tar -xzf /tmp/afp-entry.tar.gz -C /tmp/afp
      Isabelle/bin/isabelle build -v -D "/tmp/afp/$AFP_DIRECTORY" "$AFP_SESSION"
    '
}

reproduce_rice() {
  reproduce \
    "https://isa-afp.org/release/afp-Recursion-Theory-I-2026-02-06.tar.gz" \
    "b5314c859ce3b2876ef01151f394c1a5e6b234b0fc6563698dbb0250c73cd3f8" \
    "Recursion-Theory-I" \
    "Recursion-Theory-I"
}

reproduce_arrow() {
  reproduce \
    "https://isa-afp.org/release/afp-ArrowImpossibilityGS-2026-02-06.tar.gz" \
    "8174c738b42203100170ff25f3c9fc2c6d16d8556fbaff205c0eaa98a3813da7" \
    "ArrowImpossibilityGS" \
    "ArrowImpossibilityGS"
}

reproduce_nfl() {
  reproduce \
    "https://isa-afp.org/release/afp-No_Free_Lunch_ML-2026-02-06.tar.gz" \
    "93ce8953bac6b09a29f6d2aafa64d4dbedf49e11f13cdad4cddc42f95f173588" \
    "No_Free_Lunch_ML" \
    "No_Free_Lunch_ML"
}

case "${1:-all}" in
  rice)
    reproduce_rice
    ;;
  arrow)
    reproduce_arrow
    ;;
  nfl)
    reproduce_nfl
    ;;
  all)
    reproduce_rice
    reproduce_arrow
    reproduce_nfl
    ;;
  *)
    echo "usage: $0 [rice|arrow|nfl|all]" >&2
    exit 2
    ;;
esac
