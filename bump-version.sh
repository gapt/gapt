set -e

RELEASE_VERSION_PATTERN='[0-9]\+\.[0-9]\+\(\.[0-9]\+\)\?'
SNAPSHOT_VERSION_PATTERN="${RELEASE_VERSION_PATTERN}-SNAPSHOT"
ANY_VERSION_PATTERN="${RELEASE_VERSION_PATTERN}\|${SNAPSHOT_VERSION_PATTERN}"

function usage {
    echo "\
Usage: $0 [(release|snapshot)] <version>
Bumps version numbers to the given version."
}

if [[ $# -ne 2 ]]; then
    >&2 echo "$0: Invalid number of arguments"
    usage
    exit 1
fi

MODE=$1
NEW_VERSION=$2

case "$MODE" in
    release)
        # The =~ operator requires an unquoted regular expression.
        VERSION_PATTERN='^[0-9]+.[0-9]+(.[0-9]+)?$'
        if ! [[ ${NEW_VERSION} =~ ${VERSION_PATTERN} ]]; then
            >&2 echo "Invalid relase version $NEW_VERSION"
            exit 1
        fi
        ;;
    snapshot)
        ;;
    *)
        >&2 echo "Invalid command: $1"
        usage
        exit 1
        ;;
esac

case "$MODE" in
    release)
        sed -i "45,47s/$RELEASE_VERSION_PATTERN/$NEW_VERSION/" README.md
        sed -i "56s/$RELEASE_VERSION_PATTERN/$NEW_VERSION/" README.md
        sed -i "7s/$ANY_VERSION_PATTERN/$NEW_VERSION/" build.sbt
        sed -i "163s/$ANY_VERSION_PATTERN/$NEW_VERSION/" doc/user_manual.tex
        sed -i "232s/$RELEASE_VERSION_PATTERN/$NEW_VERSION/" doc/user_manual.tex
        sed -i "1s/$ANY_VERSION_PATTERN/$NEW_VERSION/" include.sh
        ;;
    snapshot)
        NEW_SNAPSHOT_VERSION="${NEW_VERSION}-SNAPSHOT"
        sed -i "7s/$SNAPSHOT_VERSION_PATTERN/$NEW_SNAPSHOT_VERSION/" build.sbt
        sed -i "163s/$SNAPSHOT_VERSION_PATTERN/$NEW_SNAPSHOT_VERSION/" doc/user_manual.tex
        sed -i "232s/$SNAPSHOT_VERSION_PATTERN/$NEW_SNAPSHOT_VERSION/" doc/user_manual.tex
        sed -i "1s/$SNAPSHOT_VERSION_PATTERN/$NEW_SNAPSHOT_VERSION/" include.sh
        sed -i "3i ## Version ${NEW_VERSION} (unreleased)\n" RELEASE-NOTES.md
        ;;
esac
