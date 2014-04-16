#!/usr/bin/env bash

# searches the actual $PATH, local directory and its development subpath for 
# the prooftool jar package and runs the scala interpreter
# (preference is given to the development version)

export VERSION="1.7"
export JARNAME="prooftool-$VERSION-jar-with-dependencies.jar"
export RELEASE="prooftool-$VERSION.jar"
export SCP=""
export RCP=""
#export POSSIBLE_PATHS="$(echo $PATH | sed "s/:/\" \"/"g | sed "s/^/\"/" |sed "s/$/\"/")"
export JAVA_OPTS="-Xss20m -Xmx2g"
export OLDIFS="$IFS"
export IFS=":"
#echo $POSSIBLE_PATHS

if test _$1_ = _-h_ -o _$1_ = _--help_ ; then
  echo "GAPT Command Line Interface"
  echo "  searches the path and current directory for a release or development version of the "
  echo "  GAPT jar and executes it."
  echo ""
  echo "usage: gui.sh [-d]"
  echo ""
  echo "   -d : prefer development version over release version"
  exit 1
fi


# look for java

export JAVA="java"
if [ -f "$JAVA_HOME/bin/java" ] ; then
  JAVA="$JAVA_HOME/bin/java"
fi

export WHICH_JAVA=`which "$JAVA" 2> /dev/null`

if [ _${WHICH_JAVA}_ = __  ] ; then
 echo "java executable not found, please check your path and set JAVA_HOME correctly"
 exit 1
fi


# look for development version
for I in ${PATH} .; do
    if [ -f "$I/${JARNAME}" ];
    then
	export SCP=$I
	break
    fi
done

for I in ${PATH} .; do
    if [ -f "$I/gui/prooftool/target/${JARNAME}" ];
    then
	export SCP="$I/gui/prooftool/target"
	break
    fi
done

#look for release
for I in $PATH .; do
    if [ -f "$I/${RELEASE}" ];
    then
        export RCP="$I"
        break
    fi
done

export IFS=$OLDIFS

if test _$1_ = _-d_ ; then echo "forcing development version!" ; fi

if test "_${RCP}_" = __ -o _$1_ = _-d_ ; then 
if test "_${SCP}_" = __ ; then 
    echo "Could not find ${JARNAME} nor ${RELEASE} in path or current directory!"
else
    echo found ${JARNAME} in ${SCP}!
#    export JAVA_OPTS="-Xss2m -Xmx2g"
    "$JAVA" -jar ${SCP}/${JARNAME} $1
fi
else
    echo "found release version ${RELEASE} in ${RCP}"
    "$JAVA" -jar "${RCP}"/${RELEASE} $1
fi

# workaround because jline somehow mixes up the terminal
#reset



