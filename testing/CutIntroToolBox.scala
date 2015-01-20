/**********
 * some test scripts for experimenting with cut-introduction
 *
 * scala> :load testing/CutIntroToolBox.scala
 **********/

import at.logic.algorithms.cutIntroduction._

// TODO: is it possible to define strictSubsetOf on the level of a scala Set locally for this file only?

def strictSubGrammar( g1 : Grammar, g2 : Grammar ) = {
  g1.u.toSet.subsetOf( g2.u.toSet ) && g1.s.toSet.subsetOf( g2.s.toSet ) &&
  ( g1.u.toSet != g2.u.toSet || g1.s.toSet != g2.s.toSet )
}

def strictRightSubGrammar( g1 : Grammar, g2 : Grammar ) = {
  g1.u.toSet == g2.u.toSet &&
  g1.s.toSet.subsetOf( g2.s.toSet ) && g1.s.toSet != g2.s.toSet
}

def strictLeftSubGrammar( g1 : Grammar, g2 : Grammar ) = {
  g1.u.toSet.subsetOf( g2.u.toSet ) && g1.u.toSet != g2.u.toSet &&
  g1.s.toSet == g2.s.toSet
}

def strictLeftRightSubGrammar( g1 : Grammar, g2 : Grammar ) = {
  g1.u.toSet.subsetOf( g2.u.toSet ) && g1.u.toSet != g2.u.toSet &&
  g1.s.toSet.subsetOf( g2.s.toSet ) && g1.s.toSet != g2.s.toSet
}

// expects list of grammars, sorted by size (so that all strict super grammars of G are behind G)
def removeStrictSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => strictSubGrammar( Gs.head, curG ))
    Gs.head :: removeStrictSuperGrammars( newTail )
  }
}

// expects list of grammars, sorted by size (so that all strict right-super grammars of G are behind G)
def removeStrictRightSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => strictRightSubGrammar( Gs.head, curG ))
    Gs.head :: removeStrictRightSuperGrammars( newTail )
  }
}

// expects list of grammars, sorted by size (so that all strict left-super grammars of G are behind G)
def removeStrictLeftSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => strictLeftSubGrammar( Gs.head, curG ))
    Gs.head :: removeStrictLeftSuperGrammars( newTail )
  }
}

// expects list of grammars, sorted by size (so that all strict left&right-super grammars of G are behind G)
def removeStrictLeftRightSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => strictLeftRightSubGrammar( Gs.head, curG ))
    Gs.head :: removeStrictLeftRightSuperGrammars( newTail )
  }
}

def testSuperGrammars( P : LKProof ) {
  val Gs = computeGrammars( extractTerms( P ))
  println ( "number of grammars: " + Gs.length )

  val Gs_woRight = removeStrictRightSuperGrammars( Gs )
  println ( "after removal if U1 = U2 and S1 c S2: " + Gs_woRight.length )

  val Gs_woLeft = removeStrictLeftSuperGrammars( Gs )
  println ( "after removal if U1 c U2 and S1 = S2: " + Gs_woLeft.length )

  val Gs_woLeftRight = removeStrictLeftRightSuperGrammars( Gs )
  println ( "after removal if U1 c U2 and S1 c S2: " + Gs_woLeftRight.length )

  val Gs_woAll = removeStrictSuperGrammars( Gs )
  println ( "after removal if U1 c U2 or S1 c S2: " + Gs_woAll.length )
}
