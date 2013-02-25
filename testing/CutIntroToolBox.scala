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

def testSuperGrammars( P : LKProof ) {
  val Gs = computeGrammars( extractTerms( P ))
  val newGs = removeSuperGrammars( Gs )
  println ( "size before: " + Gs.length + ", size after removing super-grammars: " + newGs.length )
}

