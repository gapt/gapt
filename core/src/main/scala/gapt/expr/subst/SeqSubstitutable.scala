package gapt.expr.subst

trait SeqSubstitutable {
  implicit def SubstitutableSeq[S <: Substitution, T, U]( implicit ev: Substitutable[S, T, U] ): Substitutable[S, Seq[T], Seq[U]] =
    ( sub, seq ) => seq.map( ev.applySubstitution( sub, _ ) )
}
