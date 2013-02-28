/**********
 * some test scripts for experimenting with cut-introduction
 *
 * scala> :load ../testing/CutIntroToolBox.scala
 **********/

import at.logic.algorithms.cutIntroduction._

// expects list of grammars, sorted by size (so that all strict super grammars of G are behind G)
def removeSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => curG.strictSuperGrammarOf( Gs.head ))
    Gs.head :: removeSuperGrammars( newTail )
  }
}

// expects list of grammars, sorted by size (so that all strict super grammars of G are behind G)
def removeLeftSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => curG.strictLeftSuperGrammarOf( Gs.head ))
    Gs.head :: removeSuperGrammars( newTail )
  }
}

// expects list of grammars, sorted by size (so that all strict super grammars of G are behind G)
def removeRightSuperGrammars( Gs : List[Grammar] ) : List[Grammar] = {
  if ( Gs == Nil ) Nil
  else {
    val newTail = Gs.tail.filterNot( curG => curG.strictRightSuperGrammarOf( Gs.head ))
    Gs.head :: removeSuperGrammars( newTail )
  }
}

def testSuperGrammars( P : LKProof ) {
  val Gs = computeGrammars( extractTerms( P ))
  println ( "number of grammars: " + Gs.length )
  val Gs_woLeft = removeLeftSuperGrammars( Gs )
  println ( "after removing left-super grammars: " + Gs_woLeft.length )
  val Gs_woRight = removeRightSuperGrammars( Gs )
  println ( "after removing right-super grammars: " + Gs_woRight.length )
  val Gs_woBoth = removeSuperGrammars( Gs )
  println ( "after removing all super grammars: " + Gs_woBoth.length )
}
