package gapt.formats.tptp

object TstpSourceSyntax {
  extension (source: Source)
    def parentLabels: Seq[String] = source match {
      case Source.Name(name)                                => Seq(name)
      case Source.Inference(_, _, parents)                  => parents.flatMap(_.source.parentLabels)
      case Source.Internal(_, _, parents)                   => parents.flatMap(_.source.parentLabels)
      case Source.File(_, _)                                => Seq.empty // for now we treat file sources as axioms that don't have parents
      case Source.Theory(_, _)                              => Seq.empty
      case Source.Creator(_, _, parents)                    => parents.flatMap(_.source.parentLabels)
      case Source.Unknown                                   => Seq.empty
      case Source.List(sources)                             => sources.flatMap(_.parentLabels)
      case Source.General(GeneralColon(TptpTerm(label), _)) => Seq(label)
      case Source.General(TptpTerm(dagSource))              => Seq(dagSource)
      case Source.General(term)                             => throw IllegalArgumentException(s"parent must be a simple term. got: $term")
    }
}
