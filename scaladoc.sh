#!/bin/sh

rm -rf scaladoc
mkdir scaladoc
rm -rf ~/.m2/repository/at/logic
JAVA_OPTS="-Xmx3g" scaladoc -d scaladoc -classpath $(find ~/.m2/repository/ -iname *.jar|xargs| tr ' ' ':') $(find source -regextype posix-extended -regex '.*\.(scala|java)$'|grep -v Test|grep -v gui/treeviz)
