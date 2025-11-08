#!/bin/bash
#$ -q long
#$ -pe smp 4
#$ -N tlc-test8-dfid

set -euo pipefail

JAR=/users/sradha/tla2tools.jar
SPEC=test1_security_puf_based_securityview_step5_revocation_fixed2_FIXED.tla
CFG=test8.cfg

# DFID with minimal options (no heap/seed/tmp flags)
java -jar "$JAR" \
  -workers 1 \
  -dfid 12 \
  -deadlock \
  -config "$CFG" "$SPEC"

