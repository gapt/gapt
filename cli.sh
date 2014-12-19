#!/bin/sh
JARFILE="$(dirname $0)/target/scala-2.11/gapt-assembly-1.9.jar"

if ! test -f "$JARFILE"; then
  echo Jar not found at "$JARFILE"
  echo Run sbt assembly!
  exit 1
fi

java -Xss10m -Xmx2g -jar "$JARFILE" "$@"
