#!/bin/bash
basedir="$(dirname "$0")"
. "$basedir/include.sh"

run_gapt at.logic.provers.atp.Main "$@"
