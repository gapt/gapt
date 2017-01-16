* fresh checkout
* bump all versions (9.7 and 9.8-SNAPSHOT) to 9.8
* git commit -am 'Release 9.8.' && git tag -a v9.8
* nix-shell --pure -p sbt --command 'sbt test'
* sbt evalUserManual test
* sbt releaseDist
* check whether gapt.sh works in tarball
* sbt publish
* bump version to 9.9-SNAPSHOT
* git commit -am 'Bump version to 9.9-SNAPSHOT' && git push && git push --tags
* upload to website!
* update website
* announce to mailing list
