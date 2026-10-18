#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_manuscript_correspondence.py
(cd source && shasum -a 256 -c SHA256SUMS)
cd formalization
lake build
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT HUP INT TERM
lake env lean SRWTightness/Audit.lean > "$audit_log"
cat "$audit_log"
python3 ../verify_certificate.py "$audit_log"
