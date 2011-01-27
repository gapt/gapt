#!/bin/sh

OLDDIR=`pwd`

# make temp dir dependent on system time
TDIR=$HOME/gapt-`date +%y-%m-%d-%S-%N`

echo Cleaning up temporary directory $TDIR
rm -rf $TDIR

echo Cleaning up maven repository
rm -rf $USER/.m2/at/logic

echo Getting sources
svn checkout https://gapt.googlecode.com/svn/trunk/source $TDIR

echo Compiling
cd $TDIR
mvn install


cd $OLDDIR

