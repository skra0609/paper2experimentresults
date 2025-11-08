#!/bin/bash
#$ -q long
#$ -pe smp 4
#$ -N output

java -jar /users/sradha/tla2tools.jar -workers $NSLOTS -deadlock \
  -config test5.cfg \
   test1_security_puf_based_securityview_step5_revocation_fixed2_FIXED.tla
