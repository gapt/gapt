package at.logic.gapt.examples.theories
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.ProofLink

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
  val cntnil = lemma( hof"cnt{?a} x nil = 0", "simp" ) { simp.w( "cnt", "filter" ) }
  val cntconseq = lemma( hof"cnt{?a} x (cons x ys) = s (cnt x ys)", "simp" ) { simp.w( "cnt", "filter" ) }
  val cntconsne = lemma( hof"x != y -> cnt{?a} x (cons y ys) = cnt x ys", "simp" ) { decompose; simp.h( "cnt", "filter" ) }
  val cntapp = lemma( hof"cnt{?a} x (app y z) = cnt x y + cnt x z", "simp" ) { simp.w( "cnt" ) }
  val cntrev = lemma( hof"cnt{?a} x (rev y) = cnt x y", "simp" ) { simp.w( "cnt", "filterrev" ) }

  dfn( hof"perm{?a} xs ys = (!(z:?a) cnt z xs = cnt z ys)" )
  val permrfl = lemma( hof"perm{?a} x x", "simp" ) { simp.w( "perm" ) }
  val permsym = lemma( hof"perm{?a} x y -> perm y x" ) { simp.w( "perm" ); decompose; simp.h }
  val permtrans = lemma( hof"perm{?a} x y & perm y z -> perm x z" ) { simp.w( "perm" ); decompose; simp.h }
  val permrev = lemma( hof"perm{?a} x (rev x)", "simp" ) { simp.w( "perm" ) }

  fun(
    hoc"del{?a}: ?a > list?a > list ?a",
    "del x nil = nil",
    "del x (cons y ys) = ite (x = y) ys (cons y (del x ys))" )
  attr( "simp" )( "delnil" )
  val delconseq = lemma( hof"del{?a} x (cons x xs) = xs", "simp" ) { simp.w( "del" ) }
  val delconsne = lemma( hof"x!=y -> del{?a} x (cons y xs) = cons y (del x xs)", "simp" ) { decompose; simp.h.w( "del" ) }
  val cntdeleq = lemma( hof"cnt{?a} x (del x ys) = p (cnt x ys)", "simp" ) {
    induction( hov"ys:list?a" ) onAll simp.h( "del" )
    cut( "", hof"x = (x_0 : ?a)" ) onAll simp.h
  }
  val cntdelne = lemma( hof"x!=y -> cnt{?a} x (del y ys) = cnt x ys", "simp" ) {
    impR; induction( hov"ys:list?a" ) onAll simp.h( "del" )
    cut( "xx0", hof"x = (x_0 : ?a)" ) onAll cut( "yx0", hof"y = (x_0 : ?a)" ) onAll simp.h
    simp.h.on( "IHys_0" ); simp.h
    simp.h.on( "IHys_0" ); quasiprop
  }
  val permdel = lemma( hof"perm{?a} x y -> perm (del z x) (del z y)" ) {
    simp.w( "perm" ); decompose; cut( "z0z", hof"z_0 = (z:?a)" ) onAll simp.h
  }
  val permnill = lemma( hof"perm{?a} nil y <-> y=nil", "simp" ) {
    simp.w( "perm" ); induction( hov"y:list?a" ) onAll simp
    exR( le"x:?a" ).forget; simp
  }
  val permnilr = lemma( hof"perm{?a} x nil <-> x=nil", "simp" ) { include( "permsym", "permnill" ); escrgt }

  dfn( hof"elem{?a} xs (x:?a) = (cnt x xs != 0)" )
  val elemnil = lemma( hof"-elem{?a} nil x", "simp" ) { simp.w( "elem" ) }
  val elemcons = lemma( hof"elem{?a} (cons y ys) x <-> (x=y | elem ys x)", "simp" ) {
    cut( "", hof"x=(y:?a)" ) onAll simp.h.w( "elem" )
  }
}

object listfold extends Theory( listlength, props ) {
  fun(
    hoc"foldr{?a?b} : (?a>?b>?b) > ?b > list?a>?b",
    "foldr f z nil = z",
    "foldr f z (cons x xs) = f x (foldr f z xs)" )
  attr( "simp" )( "foldr" )
  val foldrapp = lemma( hof"unit f z & assoc f -> foldr{?a?a} f z (app x y) = f (foldr f z x) (foldr f z y) ", "simp" ) {
    simp.w( "unit", "assoc" ); decompose; induction( hov"x:list?a" ) onAll simp.h
  }
  val foldrdel = lemma( hof"assoc{?a} f & comm f -> elem ys x -> f x (foldr f z (del x ys)) = foldr f z ys" ) {
    impR; induction( hov"ys:list?a" ) onAll simp onAll decompose onAll simp.h
    destruct( "g_1_0" ); simp.h
    cut( "xx0", hof"x=(x_0:?a)" ) onAll simp.h
    include( "assoc", "comm" ); escrgt
  }
  val foldrperm = lemma( hof"assoc{?a} f & comm f -> perm x y -> foldr f z x = foldr f z y" ) {
    impR; generalize( hov"y:list?a" ); induction( hov"x:list?a" ) onAll simp.h onAll decompose onAll simp.h
    cut( "pd", hof"perm(x_1, del(x_0:?a, y))" ); by { include( "permdel", "delconseq" ); escrgt }
    cut( "pyc", hof"!z cnt{?a}(z,y) = cnt(z,cons(x_0,x_1))" ); by { forget( "g_1_1" ); simp.w( "perm" ).on( "g_1_0" ); simp.h }
    cut( "eyx_0", hof"elem y (x_0:?a)" ); by { forget( "g_1_1" ); simp.w( "elem" ).h }
    allL( "IHx_0", le"del{?a} x_0 y" ).forget; simp.h
    simp.h( "foldrdel" )
  }
}

object natlists extends Theory( listfold, nat ) {
  dfn( hof"sum l = foldr '+' 0 l" )
  val sumnil = lemma( hof"sum nil = 0", "simp" ) { simp.w( "sum" ) }
  val sumcons = lemma( hof"sum (cons x xs) = x + sum xs", "simp" ) { simp.w( "sum" ) }
  val sumapp = lemma( hof"sum (app x y) = sum x + sum y", "simp" ) { simp.w( "sum" ) }
  val sumperm = lemma( hof"perm x y -> sum x = sum y" ) { decompose; simp.h.w( "sum", "foldrperm" ) }

  dfn( hof"prod l = foldr '*' 1 l" )
  val prodnil = lemma( hof"prod nil = 1", "simp" ) { simp.w( "prod" ) }
  val prodcons = lemma( hof"prod (cons x xs) = x * prod xs", "simp" ) { simp.w( "prod" ) }
  val prodapp = lemma( hof"prod (app x y) = prod x * prod y", "simp" ) { simp.w( "prod" ) }
  val prodperm = lemma( hof"perm x y -> prod x = prod y" ) { decompose; simp.h.w( "prod", "foldrperm" ) }
}
