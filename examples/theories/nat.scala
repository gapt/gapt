package gapt.examples.theories

import gapt.expr._
import gapt.formats.babel.Precedence
import gapt.proofs.gaptic._

object nat extends Theory( logic, props ) {
  indTy( ty"nat", hoc"0: nat", hoc"s: nat>nat" )

  infix( "+", Precedence.plusMinus ); infix( "-", Precedence.plusMinus )
  infix( "*", Precedence.timesDiv )
  infix( "<=", Precedence.infixRel ); infix( "<", Precedence.infixRel )

  fun( hoc"p: nat>nat", "p(s(x)) = x", "p(0) = 0" )
  fun( hoc"'+': nat>nat>nat", "x+0 = x", "x+s(y)=s(x+y)" )
  fun( hoc"'-': nat>nat>nat", "x-0=x", "x-s(y)=p(x)-y" )
  fun( hoc"'*': nat>nat>nat", "x*0 = 0", "x*s(y)=x*y+x" )
  dfn( hof"1 = s(0)" )
  fun( hoc"pow: nat>nat>nat", "pow x 0 = 1", "pow x (s y) = pow x y * x" )
  dfn( hof"(x <= y) = (?z y = x+z)" )
  dfn( hof"(x < y) = (s x <= y)" )

  attr( "simp" )( "p", "add", "mul", "sub", "pow", "1" )

  val sne0 = lemma( hof"s(x) != 0", "simp" ) { include( "is_0" ); escrgt }
  val `0nes` = lemma( hof"0 != s(x)", "simp" ) { include( "sne0" ); escrgt }
  val sor0 = lemma( hof"x = 0 | x = s(p(x))" ) { include( "ps" ); anaInd }
  val sinj = lemma( hof"s(x) = s(y) <-> x = y", "simp" ) { include( "ps" ); escrgt }
  val sp = lemma( hof"x!=0 -> s(p(x)) = x", "simp" ) { induction( hov"x:nat" ) onAll simp }

  val add0l = lemma( hof"0+x = x", "simp" ) { include( "add" ); anaInd }
  val addsl = lemma( hof"s(x)+y = s(x+y)", "simp" ) { include( "add" ); anaInd }
  val addcomm = lemma( hof"x+y=y+x" ) { include( "add", "add0l", "addsl" ); anaInd }
  val addcommiff = lemma( hof"x+y=y+x <-> true", "simp" ) { include( "addcomm" ); escrgt }
  val addassoc = lemma( hof"x+(y+z) = (x+y)+z" ) { include( "add" ); anaInd }
  val addac1inst = lemma( hof"assoc(+) & comm(+) & unit(+,0)", "simp" ) { simp.w( "assoc", "comm", "unit", "addassoc" ) }
  val addinj = lemma( hof"x+y=x+z <-> y=z", "simp" ) { induction( hov"x:nat" ).onAll( simp.h ) }
  val addinjr = lemma( hof"y+x=z+x <-> y=z", "simp" ) { include( "addinj", "addcomm" ); escrgt }
  val addinjr2 = lemma( hof"x=y+x <-> y=0", "simp" ) { include( "addinjr", "add0l" ); escrgt }
  val add0eq = lemma( hof"x+y=0 <-> x=0 & y=0", "simp" ) { include( "add", "sne0", "sor0" ); escrgt }

  val mul0l = lemma( hof"0*x = 0", "simp" ) { include( "mul", "add0l" ); anaInd }
  val mulsl = lemma( hof"s(x)*y = x*y+y", "simp" ) { include( "mul", "add0", "adds", "addcomm", "addassoc" ); anaInd }
  val mulcomm = lemma( hof"x*y=y*x" ) { include( "mul", "mul0l", "mulsl" ); anaInd }
  val muladd = lemma( hof"x*(y+z) = x*y + x*z" ) { include( "mul", "add", "addassoc", "addcomm" ); anaInd }
  val addmul = lemma( hof"(x+y)*z = x*z + y*z" ) { include( "mulcomm", "muladd" ); escrgt }
  val mulassoc = lemma( hof"x*(y*z)=(x*y)*z" ) { include( "mul", "muladd" ); anaInd }
  val mulcommiff = lemma( hof"x*y=y*x <-> true", "simp" ) { include( "mulcomm" ); escrgt }
  val mulac1inst = lemma( hof"assoc(*) & comm(*) & unit(*,s 0)", "simp" ) { simp.w( "assoc", "comm", "unit", "mulassoc" ) }
  val mul1 = lemma( hof"x*1 = x" ) { include( "1", "mul", "add0l" ); escrgt }
  val mul0eq = lemma( hof"x*y=0 <-> x=0 | y=0", "simp" ) { include( "sor0", "sne0", "mul", "mul0l", "add" ); escrgt }
  val mul1eq = lemma( hof"x*y=s(0) <-> x=s(0) & y=s(0)", "simp" ) {
    induction( hov"y:nat" ) onAll simp
    induction( hov"x:nat" ) onAll simp
    prop
  }
  val muleq1 = lemma( hof"s(0)=x*y <-> x=s(0) & y=s(0)", "simp" ) { include( "mul1eq" ); escrgt }
  val mulinj = lemma( hof"x!=0 -> x*y=x*z <-> y=z", "simp" ) { include( "sor0", "sne0", "mul", "mul0eq", "addinjr" ); anaIndG }
  val mulinjr = lemma( hof"x!=0 & y*x=z*x -> y=z" ) { include( "mulcomm", "mulinj" ); escrgt }
  val mulid = lemma( hof"x=x*y <-> y=1|x=0" ) { induction( hov"y:nat" ) onAll simp; prop }

  val powadd = lemma( hof"pow(x, y+z) = pow(x,y) * pow(x,z)" ) { include( "pow", "add", "mulassoc", "mul1" ); anaInd }
  val powmull = lemma( hof"pow(x, y*z) = pow(pow(x, y), z)" ) { include( "pow", "powadd", "mul", "mul1" ); anaInd }
  val powmulr = lemma( hof"pow(x*y, z) = pow(x,z) * pow(y,z)" ) { include( "pow", "mul1", "mulcomm", "mulassoc" ); anaInd }
  val pow1 = lemma( hof"pow(s(0), x) = s(0)", "simp" ) { induction( hov"x:nat" ) onAll simp.h }
  val poweq1 = lemma( hof"pow(x,y)=s(0) <-> x=s(0) | y=0", "simp" ) {
    induction( hov"y:nat" ) onAll simp; forget( "IHy_0" )
    cut( "", hof"x=s(0)" ) onAll simp.h
  }

  val subadd = lemma( hof"(x+y)-y=x", "simp" ) { include( "add", "sub", "p" ); anaInd }
  val sub0l = lemma( hof"0-x=0", "simp" ) { induction( hov"x:nat" ) onAll simp.h }
  val subself = lemma( hof"x-x=0", "simp" ) { induction( hov"x:nat" ) onAll simp.h }
  val subpl = lemma( hof"p(x)-y=p(x-y)", "simp" ) { generalize( hov"x:nat" ); induction( hov"y:nat" ) onAll simp.h }
  val subps = lemma( hof"p(s(x)-y)=x-y", "simp" ) { include( "subpl", "p" ); escrgt }
  val subaddr = lemma( hof"x-(y+z)=x-y-z", "simp" ) { induction( hov"z:nat" ) onAll simp.h }
  val subaddl = lemma( hof"(x+y)-z=(x-z)+(y-(z-x))" ) {
    generalize( hov"z:nat" ); induction( hov"x:nat" ) onAll simp.h; decompose
    induction( hov"z:nat" ) onAll simp.h
  }
  val addsubsub = lemma( hof"a+b-c-b = a-c", "simp" ) { induction( hov"b:nat" ) onAll simp.h.wo( "subpl" ) }
  val mulsub = lemma( hof"x*(y-z) = x*y - x*z", "simp" ) {
    generalize( hov"y:nat" ); induction( hov"z:nat" ) onAll allR; simp
    induction( hov"y:nat" ); simp; forget( "IHy_0" ); simp.h
  }
}

object natorder extends Theory( nat ) {
  val lerefl = lemma( hof"x<=x", "simp" ) { include( "le", "add" ); escrgt }
  val le0l = lemma( hof"0<=x", "simp" ) { include( "le", "add0l" ); escrgt }
  val lesl = lemma( hof"s(x)<=y <-> x<=y&x!=y" ) { simp.w( "le" ); include( "addsl", "add", "addinj", "sne0", "sor0" ); escrgt }
  val less = lemma( hof"s(x)<=s(y) <-> x<=y", "simp" ) { include( "le", "addsl", "sinj" ); escrgt }
  val le0r = lemma( hof"x<=0 <-> x=0", "simp" ) { include( "le", "add0eq", "le0l" ); escrgt }
  val les0 = lemma( hof"~(s(x)<=0)", "simp" ) { include( "le0r", "sne0" ); escrgt }
  val lesuc = lemma( hof"x<=s(x)", "simp" ) { include( "le", "add" ); escrgt }
  val letrans = lemma( hof"x<=y & y<=z -> x<=z" ) { include( "le", "addassoc" ); anaInd }
  val leantisymm = lemma( hof"x<=y & y<=x -> x=y" ) { simp.w( "le" ); include( "add", "addassoc", "addinj", "add0eq" ); escrgt }
  val lesr = lemma( hof"x<=s(y) <-> (x<=y|x=s(y))" ) { simp.w( "le" ); include( "sor0", "sinj", "add", "p" ); escrgt }
  val letotal = lemma( hof"x<=y | y<=x" ) {
    induction( hov"x:nat" ); simp.w( "lesl", "lesr" ); destruct( "IHx_0" ) onAll simp.h( "lesl", "lesr" )
    revert( "IHx_0" ); induction( hov"y:nat" ); simp.h; forget( "IHy_0" )
    decompose; revert( "g_0", "g_1_1_1" ); simp.h
  }
  val notle = lemma( hof"~(x<=y) <-> (y<=x&x!=y)" ) { include( "letotal", "leantisymm" ); escrgt }
  val lepl = lemma( hof"p(x)<=y <-> x=s(y)|x<=y" ) {
    induction( hov"x:nat" ) onAll simp.w( "lesl" )
    cut( "", hof"x_0=(y:nat)" ) onAll simp.h
  }
  val lepr = lemma( hof"y!=0 -> x<=p(y) <-> s(x)<=y", "simp" ) { induction( hov"y:nat" ) onAll simp }

  val addsub = lemma( hof"y<=x -> (x-y)+y = x", "simp" ) { include( "addcomm", "subadd", "le" ); escrgt }

  val addbnd = lemma( hof"x<=x+y & y<=x+y", "simp" ) { include( "le", "addcomm" ); escrgt }
  val addmon = lemma( hof"x1<=x2 & y1<=y2 -> x1+y1 <= x2+y2" ) { simp.w( "le" ); include( "addcomm", "addassoc" ); escrgt }
  val mulbnd = lemma( hof"y!=0 -> x<=x*y & x<=y*x", "simp" ) { induction( hov"y:nat" ) onAll simp }
  val mulmon = lemma( hof"x1<=x2 & y1<=y2 -> x1*y1 <= x2*y2" ) { simp.w( "le" ); include( "addmul", "muladd", "addcomm", "addassoc" ); escrgt }

  val lesub = lemma( hof"x-y<=x", "simp" ) { induction( hov"y:nat" ) onAll simp.h( "lepl" ) }
  val leadd = lemma( hof"x<=x+y", "simp" ) { induction( hov"y:nat" ) onAll simp.h }
  val leaddr = lemma( hof"x<=y+x", "simp" ) { include( "leadd", "addcomm" ); escrgt }
  val lemul = lemma( hof"y!=0 -> x<=x*y", "simp" ) { induction( hov"y:nat" ) onAll simp }

  val submon = lemma( hof"x1<=x2 & y2<=y1 -> x1-y1 <= x2-y2" ) {
    impR; simp.w( "le" ).on( "g_0" ); decompose
    simp.h( "subaddl" ); include( "lesub", "leadd", "letrans" ); escrgt
  }

  val addlecancelr = lemma( hof"x+y<=x+z <-> y<=z", "simp" ) {
    destruct( "g" )
    simp.w( "le" ); include( "addassoc", "addinj" ); escrgt
    decompose; simp.h( "addmon", "lerefl" )
  }
  val addlecancell = lemma( hof"y+x<=z+x <-> y<=z", "simp" ) { include( "addlecancelr", "addcomm" ); escrgt }
  val subeq0 = lemma( hof"x<=y -> x-y=0", "simp" ) {
    induction( hov"y:nat" ) onAll simp.w( "lesl", "lesr" ) onAll decompose; destruct( "g_0" ) onAll simp.h
    forget( "g_0", "IHy_0" ); induction( hov"y_0:nat" ) onAll simp.h
  }

  val ltirrefl = lemma( hof"~(x<x)", "simp" ) { include( "lt", "add", "addlecancelr", "les0" ); escrgt }
  val lttrans = lemma( hof"x<y & y<z -> x<z" ) { include( "lesuc", "lt", "letrans" ); escrgt }
  val lt0r = lemma( hof"~(x<0)", "simp" ) { include( "lt", "les0" ); escrgt }
  val lt0s = lemma( hof"0<s(x)", "simp" ) { include( "lt", "less", "le0l" ); escrgt }
  val ltsl = lemma( hof"s(x)<y <-> x<y&y!=s(x)" ) { include( "lt", "lesl" ); escrgt }
  val ltsr = lemma( hof"x<s(y) <-> x=y|x<y" ) { include( "lt", "lesr", "lesl", "lerefl" ); escrgt }
  val ltss = lemma( hof"s(x)<s(y) <-> x<y", "simp" ) { simp.w( "lt" ) }
  val ltsuc = lemma( hof"x<s(x)", "simp" ) { include( "lt", "lerefl" ); escrgt }
  val lt0l = lemma( hof"0<x <-> x!=0", "simp" ) { include( "ltirrefl", "sor0", "lt0s" ); escrgt }

  val ltmull = lemma( hof"x!=0 & s(0)<y -> x<x*y" ) {
    induction( hov"y:nat" ) onAll simp
    induction( hov"y_0:nat" ) onAll simp
    induction( hov"x:nat" ) onAll simp
    simp.w( "lt" )
  }
  val ltmulr = lemma( hof"x!=0 & s(0)<y -> x<y*x" ) { include( "mulcomm", "ltmull" ); escrgt }

  val addsmonr = lemma( hof"x+y1<x+y2 <-> y1<y2", "simp" ) { simp.w( "lt", "lesl" ) }
  val addsmonl = lemma( hof"y1+x<y2+x <-> y1<y2", "simp" ) { simp.w( "lt", "lesl" ) }
}

object natdivision extends Theory( natorder ) {
  val divmodgtot = lemma( hof"b!=0 -> ?d?r (r<b & d*b+r=a)" ) {
    impR; induction( hov"a: nat" )
    include( "lt0s", "sor0", "add", "mul", "mul0l", "p" ); escrgt
    include( "lt0l", "ltsl", "add", "mulsl", "sor0", "ltsuc" ); escrgt
  }
  val divmodg0 = lemma( hof"r<b & d*b+r=0 -> d=0 & r=0" ) { include( "lt0r", "add0eq", "mul0eq" ); escrgt }
  val divmodgss = lemma( hof"s(r)<b & d*b+s(r)=s(a) -> r<b & d*b+r=a" ) { include( "ltsuc", "lttrans", "add", "sinj" ); escrgt }
  val divmodgs0 = lemma( hof"0<b & d*b+0=s(a) -> p(b)<b & p(d)*b+p(b)=a & d!=0" ) {
    include( "ltsuc", "mulsl", "add", "lt0r", "sor0", "mul0eq", "sinj" ); escrgt
  }
  val divmodgpfn = lemma( hof"r1<b & d1*b+r1=a & r2<b & d2*b+r2=a -> d1=d2 & r1=r2" ) {
    include( "ltirrefl", "divmodg0", "divmodgss", "divmodgs0", "sor0", "p" )
    generalize( hov"r1:nat", hov"r2:nat", hov"d1:nat", hov"d2:nat" ); induction( hov"a:nat" ); escrgt
    repeat( allR ); induction( hov"r1: nat" ).onAll( induction( hov"r2: nat" ) ).onAll( escrgt )
  }
  infix( "/", Precedence.timesDiv )
  infix( "%", Precedence.timesDiv, const = "mod" )
  indfn( "/", hof"!a!b?d (b!=0 -> ?r (r<b & d*b+r=a))" ) { include( "divmodgtot" ); escrgt }
  indfn( "mod", hof"!a!b?r (b!=0 -> r<b & (a/b)*b+r=a)" ) { include( "div" ); escrgt }
  val divmod = lemma( hof"b!=0 | 0<b -> a%b<b & (a/b)*b+a%b=a", "simp" ) { include( "mod", "lt0r" ); escrgt }
  val divmoduniq = lemma( hof"r<b & d*b+r=a -> a/b=d & a%b=r" ) { include( "divmod", "lt0r", "divmodgpfn" ); escrgt }
  val divmodiff = lemma( hof"r<b & d*b+r=a <-> b!=0 & d=a/b & r=a%b" ) { include( "divmod", "divmoduniq", "lt0r" ); escrgt }
  val divmodlt = lemma( hof"a<b -> a/b=0 & a%b = a", "simp" ) { include( "divmodiff", "mul0l", "add0l" ); escrgt }
  val divmod0 = lemma( hof"b!=0 -> 0/b=0 & 0%b = 0", "simp" ) { include( "divmodlt", "sor0", "lt0s" ); escrgt }
  val divmodge = lemma( hof"b!=0&b<=a -> a/b=s((a-b)/b) & a%b = (a-b)%b", "simp" ) {
    impR
    include( "divmoduniq" ); chain( "divmoduniq" ) onAll forget( "divmoduniq" ); simp.h
    cut( "", hof"(a-b)/b*b + (a-b)%b + b = a" ); by { forget( "g_1" ); simp.h }
    simp.h; include( "addassoc", "addcomm" ); escrgt
  }
  val divmodmul = lemma( hof"b!=0 -> (b*a)/b=a & (b*a)%b=0", "simp" ) {
    decompose; include( "divmoduniq" ); chain( "divmoduniq" ) onAll forget( "divmoduniq" )
    simp.h.on( "g_1" ); include( "mulcomm", "add" ); escrgt
  }
}

object natdivisible extends Theory( natdivision ) {
  dfn( hof"dvd x y = (?z y = x*z)" )
  val dvdmod = lemma( hof"x!=0 -> dvd x y <-> y%x=0" ) {
    simp.w( "dvd" ); decompose; andR onAll impR; decompose; simp.h
    exR( le"y/x" ).forget; simp.h; include( "divmod", "mulcomm", "add" ); escrgt
  }
  val dvd0 = lemma( hof"dvd x 0", "simp" ) { include( "dvd", "mul" ); escrgt }
  val dvd0l = lemma( hof"dvd 0 x <-> x=0", "simp" ) { include( "dvd", "mul0l" ); escrgt }
  val dvd1 = lemma( hof"dvd 1 x", "simp" ) { include( "dvd", "mul1", "mulcomm" ); escrgt }
  val dvds0 = lemma( hof"dvd (s 0) x", "simp" ) { include( "dvd1", "1" ); escrgt }
  val dvd1r = lemma( hof"dvd x (s 0) <-> x=1", "simp" ) { simp.w( "dvd" ); escrgt }
  val dvdrefl = lemma( hof"dvd x x", "simp" ) { include( "dvd", "mul1" ); escrgt }
  val dvdtrans = lemma( hof"dvd x y -> dvd y z -> dvd x z" ) { include( "dvd", "mulassoc" ); escrgt }
  val dvdantisym = lemma( hof"dvd x y & dvd y x -> x=y" ) {
    cut( "x0", hof"x!=0" ); by { simp.h.on( "g" ); quasiprop }
    cut( "y0", hof"y!=0" ); by { simp.h.on( "g" ) }
    simp.w( "dvd" ); include( "mulassoc", "mul", "mulinj", "mul1", "mul1eq" ); escrgt
  }
  val dvdmul = lemma( hof"dvd x (x*y)", "simp" ) { simp.w( "dvd" ); exR( le"y:nat" ).forget; simp }
  val dvdmulr = lemma( hof"dvd x (y*x)", "simp" ) { include( "dvdmul", "mulcomm" ); escrgt }
  val dvdcancel = lemma( hof"x!=0 -> dvd (x*y) (x*z) <-> dvd y z", "simp" ) {
    simp.w( "dvd" ); include( "mulassoc", "mulinj" ); escrgt
  }
  val dvdcancel2 = lemma( hof"x!=0 -> dvd (y*x) (x*z) <-> dvd y z", "simp" ) { include( "mulcomm", "dvdcancel" ); escrgt }
  val dvdle = lemma( hof"y!=0 & dvd x y -> x<=y" ) { simp.w( "dvd" ); decompose; simp.h.on( "g_0_0" ); decompose; simp.h }

  dfn( hof"prime x = (1<x & !y (dvd(y,x) -> y=1|y=x))" )
  val notprime0 = lemma( hof"~prime 0", "simp" ) { simp.w( "prime" ) }
  val notprime1 = lemma( hof"~prime (s 0)", "simp" ) { simp.w( "prime" ) }
  val prime2 = lemma( hof"prime (s (s 0))", "simp" ) {
    simp.w( "prime" ); allR; cut( "c", hof"y!=0" ) onAll simp.h( "dvdmod" ); revert( "c" )
    induction( hov"y:nat" ) onAll simp
    induction( hov"y_0:nat" ) onAll simp
    induction( hov"y_1:nat" ) onAll simp.w( "ltsl" )
  }
  val primene0 = lemma( hof"prime n -> n!=0" ) { include( "notprime0" ); escrgt }
  val primene1 = lemma( hof"prime n -> n!=s 0" ) { include( "notprime1" ); escrgt }

  dfn( hof"composite x = (?y?z (x=y*z & 1<y&1<z))" )
  val primecomp = lemma( hof"prime x <-> 1<x & ~composite x" ) {
    simp.w( "prime", "composite" ); cut( "1x", hof"~(s 0<x)" ) onAll simp.w( "1x" )
    simp.w( "ltsl" ); simp.w( "ltsl" ).on( "1x" ); andR onAll impR
    by { // ->
      decompose; allL( le"y:nat" ); allL( le"z:nat" )
      forget( "g_0" ); revert( "g_0_0", "g_0_1" ); simp.h( "mulid" )
    }
    by { // <-
      simp.w( "dvd" ); decompose
      allL( le"y:nat", le"z:nat" ).forget; simp.h.on( "g_0" )
      destruct( "g_0" ); simp.h
      destruct( "g_0" ); simp.h
      simp.h.on( "g_1_1_1" )
    }
  }

  val muldiv = lemma( hof"y!=0 & x%y=0 -> y*(x/y)=x", "simp" ) { include( "mod", "mulcomm", "add" ); escrgt }

  val dvdprime__ = lemma( hof"prime y -> y*z=x*(y*w) <-> z=x*w" ) {
    include( "mulcomm", "mulinjr", "mulassoc", "mulcomm", "notprime0" ); escrgt
  }
  val dvdprime_ = lemma( hof"prime x -> !x!w!z (prime x & w < y & dvd x (w*z) -> dvd x w | dvd x z) -> dvd x (y*z) -> dvd x y | dvd x z" ) {
    decompose
    cut( "zy", hof"~(z<y)" ); by { include( "mulcomm" ); escrgt }
    cut( "s0y", hof"s(0)<y" ); by { simp.w( "ltsl" ).on( "s0y" ); destruct( "s0y" ); simp.h.on( "g_1_1_1_0" ); simp.h.on( "g_1_1_0" ) }

    cut( "py", hof"prime y" ); by {
      simp.h.w( "primecomp", "composite" ).on( "py" ); decompose
      cut( "y0y", hof"y_0<y" ); by { simp.w( "ltsl" ).on( "py_0_1" ); simp.h.w( "ltmull" ).on( "y0y" ) }
      cut( "z0y", hof"z_0<y" ); by { simp.w( "ltsl" ).on( "py_1" ); simp.h.w( "ltmulr" ).on( "z0y" ) }
      cut( "dvdy0y", hof"dvd y_0 y" ); by { simp.h.on( "dvdy0y" ) }
      cut( "dvdz0y", hof"dvd z_0 y" ); by { simp.h.on( "dvdz0y" ) }
      allL( "g_1_0", le"x:nat", le"y_0:nat", le"z_0*z" )
      allL( "g_1_0", le"x:nat", le"z_0:nat", le"z:nat" ).forget
      include( "dvdtrans", "mulassoc" ); escrgt
    }

    cut( "y0", hof"y!=0 & y!=s(0)" ); by { simp.w( "ltsl" ).on( "s0y" ) }

    cut( "a", hof"?a y*z=x*a" ); by( simp.w( "dvd" ).on( "g_1_1_0" ) ); exL( "a" )

    cut( "ya", hof"~dvd y a" ); by {
      negR( "ya" ); simp.w( "dvd" ).on( "ya" ); exL
      simp.w( "dvd" ).on( "g_1_1_1_1" ); exR( le"z_0:nat" ).forget
      simp.h.on( "a" ).w( "dvdprime__" )
    }

    cut( "yx", hof"~dvd y x" ); by { negR( "yx" ); simp.w( "prime" ).on( "g_0" ); escrgt }

    cut( "m0", hof"x%y != 0" ); by { simp.w( "dvd" ).on( "yx" ); allL( "yx", le"x/y" ).forget; simp.h.on( "yx" ) }

    cut( "a1", hof"y*z = ((x/y)*y + x%y)*a" ); by { include( "mod" ); escrgt }
    cut( "a2", hof"y*z - ((x/y)*y)*a = (x%y)*a" ); by { include( "addmul", "addcomm", "subadd" ); escrgt }
    cut( "a3", hof"y*(z - (x/y)*a) = (x%y)*a" ); by { include( "mulsub", "mulcomm", "mulassoc" ); escrgt }

    cut( "dam", hof"dvd y (x%y * a)" ); by { simp.w( "dvd" ).on( "dam" ); exR( "dam", le"z - (x/y)*a" ).forget; quasiprop }

    // dvd x (y*z)
    allL( "g_1_0", le"y:nat", le"x%y", le"a:nat" ).forget; simp.h.on( "g_1_0" )

    cut( "mxyy", hof"x%y < y" ); by { include( "mod" ); escrgt }
    cut( "ymxy", hof"y <= x%y" ); by { simp.h.w( "dvdle" ).on( "ymxy" ) }

    simp.w( "lt", "lesl" ).on( "mxyy" ); include( "leantisymm" ); escrgt
  }
  val dvdprime = lemma( hof"prime x -> dvd x (y*z) <-> dvd x y | dvd x z", "simp" ) {
    cut( "b", hof"!y!x!w!z (prime x & w < y & dvd x (w*z) -> dvd x w | dvd x z)" ); by {
      forget( "g" )
      allR; induction( hov"y:nat" ); simp; repeat( allR ); simp.w( "ltsr" )
      cut( "wy0", hof"w = (y_0:nat)" ) onAll simp.w( "wy0" ); by { escrgt }
      include( "dvdprime_" ); allL( "dvdprime_", le"x:nat", le"y_0:nat", le"z:nat" ).forget; escrgt
    }

    allL( le"s(y)", le"x:nat", le"y:nat", le"z:nat" ).forget; simp.on( "b" )
    include( "dvdmul", "dvdmulr", "dvdtrans" ); escrgt
  }
}
