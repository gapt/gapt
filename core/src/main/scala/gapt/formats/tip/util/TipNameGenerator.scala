package gapt.formats.tip.util

import gapt.utils.NameGenerator

class TipNameGenerator(initiallyUsed: Iterable[String])
    extends NameGenerator(
      initiallyUsed ++ List(
        "case",
        "match",
        "ite",
        "and",
        "or",
        "forall",
        "exists",
        "=>",
        "=",
        "declare-sort",
        "declare-const",
        "declare-fun",
        "declare-datatypes",
        "define-fun",
        "define-fun-rec",
        "define-funs-rec",
        "prove",
        "par",
        "assert",
        "not",
        "true",
        "false"
      )
    ) {}
