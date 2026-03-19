#!/usr/bin/env bash
set -ex
git_repo_clean() {
  git diff --quiet &&
  git diff --cached --quiet &&
  test -z "$(git ls-files --others --exclude-standard)"
}

if [[ "$(git rev-parse --show-toplevel 2>/dev/null)" != "$(pwd -P)" ]]; then
  echo "Run this script from the repository root" >&2
  exit 1
fi

if ! git_repo_clean; then
  echo "Repository is not clean" >&2
  exit 1
fi

user=${1:-}
if [[ -z "$user" ]]; then
  echo "Usage: $0 <user>" >&2
  echo "Need to provide user that is used to deploy to website"
  exit 1
fi

sbt checkFormat evalUserManual test
if ! git_repo_clean; then
  echo "after sbt checkFormat evalUserManual test releaseDist there were changes in the repo" >&2
  exit 1
fi

sbt releaseDist
version=$(sbt --error 'print core/version')
echo "All checks succeeded"
echo "Manually test the version at ./target/gapt-$version.tar.gz. If it is good to deploy answer the next prompt with y"
read -r -p "Proceed with deployment of ./target/gapt-$version.tar.gz to GAPT website with user $user? [y/N] " confirm
if [[ "$confirm" != "y" && "$confirm" != "yes" ]]; then
  echo "Deployment aborted"
  exit 1
fi

scp ./target/gapt-$version.tar.gz $user@rick.logic.at:~
echo "Copied $gapt-$version.tar.gz to $user@rick.logic.at:~"
ssh $user@rick.logic.at << END_SSH
sftp -b - $user@finn.logic.at << END_FTP
cd /shared/groupshares/gapt/downloads
put gapt-$version.tar.gz
END_FTP
END_SSH
echo "Copied gapt-$version.tar.gz to gapt website"
