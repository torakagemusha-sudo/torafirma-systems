#!/usr/bin/env bash
# Local gizmo: verify Arithmetic Clock certificate pack is present.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DIR="$ROOT/arithmetic-clock/verification/certificates"
REQUIRED=(
  AXIOM_CERTIFICATE.json
  BUILD_CERTIFICATE.json
  CONTROL_CERTIFICATE.json
  DECLARATION_CERTIFICATE.json
  PRIVACY_CERTIFICATE.json
  REPRODUCIBILITY_CERTIFICATE.json
  SOURCE_CERTIFICATE.json
)
echo "Checking $DIR"
missing=0
for f in "${REQUIRED[@]}"; do
  if [[ -f "$DIR/$f" ]]; then
    printf "  OK  %s (%s bytes)\n" "$f" "$(wc -c < "$DIR/$f")"
  else
    printf "  MISS %s\n" "$f"
    missing=1
  fi
done
[[ $missing -eq 0 ]] || exit 1
echo "All certificates present."
