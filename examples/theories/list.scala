package at.logic.gapt.examples.theories
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._

object list extends Theory( logic ) {

  indTy( ty"list ?a", hoc"nil{?a}: list ?a", hoc"cons{?a}: ?a>list ?a>list ?a" )
  fun( hoc"head{?a}: list ?a > ?a", "head (cons x xs) = x", "head nil = arbitrary" )
  fun( hoc"tail{?a}: list ?a > list ?a", "tail (cons x xs) = xs", "tail nil = nil" )
  attr( "simp" )( "headcons", "tail" )
  val consornil = lemma( hof"xs = cons (head xs) (tail xs) | xs = nil{?a}" ) { induction( hov"xs:list?a" ) onAll simp.h }
  val consnenil = lemma( hof"cons x xs != nil{?a}", "simp" ) { include( "is_nil" ); escrgt }

  fun(
    hoc"app{?a}: list ?a > list ?a > list ?a",
    "app (cons x xs) ys = cons x (app xs ys)",
    "app nil ys = ys" )
  attr( "simp" )( "app" )
  val appnilr = lemma( hof"app xs nil = (xs : list ?a)", "simp" ) { include( "app" ); anaInd }
  val appassoc = lemma( hof"app x (app y z) = app{?a} (app x y) z", "simp" ) { include( "app" ); anaInd }
  val appeqnil = lemma( hof"app x y = nil{?a} <-> x=nil & y=nil", "simp" ) { include( "app", "consornil", "consnenil" ); escrgt }

  fun(
    hoc"map{?a ?b}: (?a>?b) > (list?a > list?b)",
    "map f (cons x xs) = cons (f x) (map f xs)",
    "map f nil = nil" )
  attr( "simp" )( "map" )
  val mapapp = lemma( hof"map{?a?b} f (app x y) = app (map f x) (map f y)", "simp" ) { induction( hov"x:list?a" ) onAll simp.h }

  fun(
    hoc"filter{?a}: (?a>o) > list?a>list?a",
    "filter p nil = nil",
    "filter p (cons x xs) = app (ite (p x) (cons x nil) nil) (filter p xs)" )
  val filterapp = lemma( hof"filter{?a} p (app x y) = app (filter p x) (filter p y)", "simp" ) {
    induction( hov"x:list?a" ) onAll simp.h( "filter" )
  }

  fun(
    hoc"rev{?a}: list?a > list?a",
    "rev nil = nil",
    "rev (cons x xs) = app (rev xs) (cons x nil)" )
  attr( "simp" )( "rev" )
  val revapp = lemma( hof"rev{?a} (app x y) = app (rev y) (rev x)" ) {
    generalize( hov"y:list?a" ); induction( hov"x:list?a" ) onAll simp.h
  }
  val revmap = lemma( hof"rev (map{?a?b} f x) = map f (rev x)" ) {
    induction( hov"x:list?a" ) onAll simp.h
  }
  val revfilter = lemma( hof"rev{?a} (filter p x) = filter p (rev x)" ) {
    induction( hov"x:list?a" ); simp.h( "filter" )
    cut( "", hof"p (x_0:?a)" ) onAll simp.h( "filter" )
  }
  val filterrev = lemma( hof"filter p (rev x) = rev{?a} (filter p x)" ) { simp.w( "revfilter" ) }

  fun( hoc"lall{?a}: (?a>o) > list?a>o", "lall p nil = true", "lall p (cons x xs) = (p x & lall p xs)" )
  attr( "simp" )( "lall" )
  val lallapp = lemma( hof"lall{?a} p (app x y) <-> lall p x & lall p y", "simp" ) { induction( hov"x:list?a" ) onAll simp.h; prop }
  val lallrev = lemma( hof"lall{?a} p (rev x) <-> lall p x", "simp" ) { induction( hov"x:list?a" ) onAll simp.h; prop }
}

object listlength extends Theory( list, nat ) {
  fun( hoc"len{?a}: list?a > nat", "len nil = 0", "len (cons x xs) = s (len xs)" )
  attr( "simp" )( "len" )
  val lenapp = lemma( hof"len{?a} (app x y) = len x + len y", "simp" ) { induction( hov"x:list?a" ) onAll simp.h }
  val lenmap = lemma( hof"len (map{?a?b} f x) = len x", "simp" ) { induction( hov"x:list?a" ) onAll simp.h }
  val lenrev = lemma( hof"len (rev{?a} x) = len x", "simp" ) { induction( hov"x:list?a" ) onAll simp.h }

  dfn( hof"cnt{?a} (x:?a) ys = len (filter ('=' x) ys)" )
  val cntconseq = lemma( hof"cnt{?a} x (cons x ys) = s (cnt x ys)", "simp" ) { simp.w( "cnt", "filter" ) }
  val cntconsne = lemma( hof"x != y -> cnt{?a} x (cons y ys) = cnt x ys", "simp" ) { decompose; simp.h( "cnt", "filter" ) }
  val cntapp = lemma( hof"cnt{?a} x (app y z) = cnt x y + cnt x z", "simp" ) { simp.w( "cnt" ) }
  val cntrev = lemma( hof"cnt{?a} x (rev y) = cnt x y", "simp" ) { simp.w( "cnt", "filterrev" ) }

  dfn( hof"perm{?a} xs ys = (!(z:?a) cnt z xs = cnt z ys)" )
  val permrfl = lemma( hof"perm{?a} x x", "simp" ) { simp.w( "perm" ) }
  val permsym = lemma( hof"perm{?a} x y -> perm y x" ) { simp.w( "perm" ); decompose; simp.h }
  val permtrans = lemma( hof"perm{?a} x y & perm y z -> perm x z" ) { simp.w( "perm" ); decompose; simp.h }
  val permrev = lemma( hof"perm{?a} x (rev x)", "simp" ) { simp.w( "perm" ) }
}

object listfold extends Theory( list, props ) {
  fun(
    hoc"foldr{?a?b} : (?a>?b>?b) > ?b > list?a>?b",
    "foldr f z nil = z",
    "foldr f z (cons x xs) = f x (foldr f z xs)" )
  attr( "simp" )( "foldr" )
  val foldrapp = lemma( hof"unit f z & assoc f -> foldr{?a?a} f z (app x y) = f (foldr f z x) (foldr f z y) ", "simp" ) {
    simp.w( "unit", "assoc" ); decompose; induction( hov"x:list?a" ) onAll simp.h
  }
}

object natlists extends Theory( listfold, nat ) {
  dfn( hof"sum l = foldr '+' 0 l" )
  val sumnil = lemma( hof"sum nil = 0", "simp" ) { simp.w( "sum" ) }
  val sumcons = lemma( hof"sum (cons x xs) = x + sum xs", "simp" ) { simp.w( "sum" ) }
  val sumapp = lemma( hof"sum (app x y) = sum x + sum y", "simp" ) { simp.w( "sum" ) }

  dfn( hof"prod l = foldr '*' 1 l" )
  val prodnil = lemma( hof"prod nil = 1", "simp" ) { simp.w( "prod" ) }
  val prodcons = lemma( hof"prod (cons x xs) = x * prod xs", "simp" ) { simp.w( "prod" ) }
  val prodapp = lemma( hof"prod (app x y) = prod x * prod y", "simp" ) { simp.w( "prod" ) }
}
