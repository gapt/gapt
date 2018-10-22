package gapt.expr

package object arithmetic {

  object int {

    object TInt extends TBase( "$int", Nil )

    object sum {
      def apply( s: Expr, t: Expr ) = {
        require( s.ty == TInt, s"Int sum needs int argument, not ${s.ty}" )
        require( t.ty == TInt, s"Int sum needs int argument, not ${t.ty}" )
      }
    }

  }

  object real {

    object TReal extends TBase( "$real", Nil )

  }

  object rational {

    object TRational extends TBase( "$rat", Nil )

  }

}