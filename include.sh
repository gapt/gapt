gapt_version="1.9"

heap_size="2g"
stack_size="20m"

for _binary in "$JAVA_HOME/bin/java" "$(which java)"; do
    if [[ -x "$_binary" ]]; then
        java="$_binary"
        break
    fi
done
if [[ -z "$java" ]]; then
    echo "Java executable not found, please check your path and maybe set JAVA_HOME correctly." >&2
    exit 1
fi

for _jar in "$basedir/gapt-$gapt_version.jar" "$basedir/target/scala-2.11/gapt-assembly-$gapt_version.jar"; do
    if [[ -f "$_jar" ]]; then
        gapt_jar="$_jar"
        break
    fi
done
if [[ -z "$gapt_jar" ]]; then
    echo "Could not find gapt jar.  Run sbt assembly." >&2
    exit 1
fi

run_gapt() {
    "$java" -Xmx"$heap_size" -Xss"$stack_size" -cp "$gapt_jar:." "$@"
}
