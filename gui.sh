#!/bin/bash
basedir="$(dirname "$0")"
. "$basedir/include.sh"

run_gapt at.logic.gui.prooftool.gui.Main "$@"
