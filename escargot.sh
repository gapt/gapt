#!/usr/bin/env bash
basedir="$(dirname "$0")"
. "$basedir/include.sh"

run_gapt at.logic.gapt.provers.escargot.Escargot "$@"
