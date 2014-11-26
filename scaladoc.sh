#!/bin/sh
GAPT_PATH="`dirname \"$0\"`"              # relative
GAPT_PATH="`( cd \"$GAPT_PATH\" && pwd )`"  # absolutized and normalized
if [ -z "$GAPT_PATH" ] ; then
  # error; for some reason, the path is not accessible
  # to the script (e.g. permissions re-evaled after suid)
  exit 1  # fail
fi
cd "$GAPT_PATH"
if [ -d scaladoc ]; then
	rm -rf scaladoc
fi
mkdir scaladoc
rm -rf ~/.m2/repository/at/logic
JAVA_OPTS="-Xmx3g" scaladoc -d scaladoc -classpath $(find ~/.m2/repository/ -iname *.jar|xargs| tr ' ' ':') $(find source -regextype posix-extended -regex '.*\.(scala|java)$'|grep -v Test | grep -v treeviz)
