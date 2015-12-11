#!/usr/bin/env bash
basedir="$(dirname "$0")"
. "$basedir/include.sh"

while getopts "hm:" FLAG; do
  case $FLAG in
    m) heap_size="$OPTARG" ;;
    *)
      echo "GAPT Command Line Interface"
      echo ""
      echo "usage: gapt.sh [-h] [-m MEM]"
      echo ""
      echo "   -m : give MEM amount of memory to the java virtual machine (default: 2g)"
      exit 1
      ;;
  esac
done

run_gapt at.logic.gapt.cli.CLIMain "$@"
