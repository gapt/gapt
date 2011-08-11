#!env bash
# searches the actual $PATH, local directory and its development subpath for 
# the CLI jar package and runs the scala interpreter
# (preference is given to the development version)

export JARNAME="cli-1.0-SNAPSHOT-jar-with-dependencies.jar"
export JAVAVIEWER="javaviewer-1.0-SNAPSHOT.jar"
export M2=$HOME/.m2/repository/
export JGRAPH=$M2/jgraph/jgraph/5.13.0.0/jgraph-5.13.0.0.jar:$M2/org/jgrapht/jgrapht-jdk1.5/0.7.3/jgrapht-jdk1.5-0.7.3.jar
export SCP=""
export POSSIBLE_PATHS=`echo $PATH | sed s/:/\\ /g`

for I in ${POSSIBLE_PATHS} .; do
    if test -f $I/${JARNAME};
    then
	export SCP=$I
	break
    fi
done

for I in ${POSSIBLE_PATHS} .; do
    if test -f $I/cli/target/${JARNAME};
    then
	export SCP="$I/cli/target"
	break
    fi
done

for I in ${POSSIBLE_PATHS} .; do
    if test -f $I/${JARNAME};
    then
	export GUIP=$I
	break
    fi
done

for I in ${POSSIBLE_PATHS} .; do
    if test -f $I/gui/javaviewer/target/${JAVAVIEWER};
    then
	export GUIP="$I/gui/javaviewer/target"
	break
    fi
done

if test _${SCP}_ = __ ; then 
    echo "Could not find ${JARNAME}!"
else if test _${GUIP}_ = __ ; then
    echo "Could not find ${JARNAME}!"
else
    echo found ${JARNAME} in ${SCP}!
    echo found ${JAVAVIEWER} in ${GUIP}!
    export JAVA_OPTS="-Xss2m -Xmx2g"
    scala -classpath ${SCP}/${JARNAME}:${GUIP}/${JAVAVIEWER}:$JGRAPH -i gui-cli-script.scala
fi
fi
