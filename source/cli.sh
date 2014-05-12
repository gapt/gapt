#!/usr/bin/env bash

# searches the actual $PATH, local directory and its development subpath for
# the CLI jar package and runs the scala interpreter
# (preference is given to the development version)

export VERSION="1.8"
export JARNAME="cli-$VERSION-jar-with-dependencies.jar"
export RELEASE="gapt-cli-$VERSION.jar"
export SCP=""
export RCP=""
#export POSSIBLE_PATHS="$(echo $PATH | sed "s/:/\" \"/"g | sed "s/^/\"/" |sed "s/$/\"/")"
export JAVA_MEM="2g"
export JAVA_STACK="10m"
#export JAVA_OPTS="-Xss1m -Xmx$JAVA_MEM"
export OLDIFS="$IFS"
export IFS=":"
#echo $POSSIBLE_PATHS
export CALL_RESET="yes"
export FORCE_DEVEL="no"


while getopts "hdm:n" FLAG; do
  case $FLAG in
    d)
      echo "forcing development version!"
      export FORCE_DEVEL="yes"
      ;;
    n)
      export CALL_RESET="no"
      ;;
    m)
      export JAVA_MEM="$OPTARG"
      ;;
    h)
      echo "GAPT Command Line Interface"
      echo "  searches the path and current directory for a release or development version of the "
      echo "  GAPT jar and executes it."
      echo ""
      echo "usage: cli.sh [-d|-n|-m MEM]"
      echo ""
      echo "   -d : prefer development version over release version"
      echo "   -n : do not call 'reset' after exiting (helps with debugging but the terminal will not print characters typed)"
      echo "   -m : give MEM amount of memory to the java virtual machine (default: 2g)"
      exit 1
      ;;
  esac
done

shift $(( OPTIND - 1 ));

export JAVA_OPTS="-Xss$JAVA_STACK -Xmx$JAVA_MEM"
#echo $JAVA_OPTS

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
    if [ -f "$I/cli/target/${JARNAME}" ];
    then
	export SCP="$I/cli/target"
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

#if test _$1_ = _-d_ ; then echo "forcing development version!" ; fi


if test "_${RCP}_" = __ -o $FORCE_DEVEL = "yes" ; then
if test "_${SCP}_" = __ ; then
    echo "Could not find ${JARNAME} nor ${RELEASE} in path or current directory!"
else
    echo found ${JARNAME} in ${SCP}!
#    export JAVA_OPTS="-Xss2m -Xmx2g"
    "$JAVA" -jar ${SCP}/${JARNAME}
fi
else
    echo "found release version ${RELEASE} in ${RCP}"
    "$JAVA" -jar "${RCP}"/${RELEASE}
fi

# workaround because jline somehow mixes up the terminal
if test $CALL_RESET = yes; then
    reset
fi



