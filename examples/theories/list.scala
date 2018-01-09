package at.logic.gapt.examples.theories
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._

object list extends Theory( logic ) {

  indTy( ty"list ?a", hoc"nil{?a}: list ?a", hoc"cons{?a}: ?a>list ?a>list ?a" )
  fun( hoc"head{?a}: list ?a > ?a", "head (cons x xs) = x", "head nil = arbitrary" )
  fun( hoc"tail{?a}: list ?a > list ?a", "tail (cons x xs) = xs", "tail nil = nil" )
  val consornil = lemma( hof"xs = cons (head xs) (tail xs) | xs = nil{?a}" ) { include( "head", "tail" ); anaInd }
  val consnenil = lemma( hof"cons x xs != nil{?a}" ) { include( "is_nil" ); escrgt }

  fun(
    hoc"app{?a}: list ?a > list ?a > list ?a",
    "app (cons x xs) ys = cons x (app xs ys)",
    "app nil ys = ys" )
  val appnilr = lemma( hof"app xs nil = (xs : list ?a)" ) { include( "app" ); anaInd }
  val appassoc = lemma( hof"app x (app y z) = app{?a} (app x y) z" ) { include( "app" ); anaInd }
  val appeqnil = lemma( hof"app x y = nil{?a} -> x=nil & y=nil" ) { include( "app", "consornil", "consnenil" ); escrgt }

  fun(
    hoc"map{?a ?b}: (?a>?b) > (list?a > list?b)",
    "map f (cons x xs) = cons (f x) (map f xs)",
    "map f nil = nil" )

}
