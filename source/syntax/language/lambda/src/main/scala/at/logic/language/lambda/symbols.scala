/*
 * Symbols.scala
 */

package at.logic.language.lambda.symbols

abstract class SymbolA {
  override def equals(v: Any) = v match {
    case v: SymbolA => v.toString == this.toString
    case _ => false
  }
}

// This is used for renaming variables during substitution.
// DO NOT confuse this with DeBruijn indices, there are no such indices in
// this program.
class VariantSymbol(val s: String, val i: Int) extends SymbolA {
  override def toString() = s + i
}
object VariantSymbol {
  def apply(s: String) : VariantSymbol = new VariantSymbol(s, 0)
  def apply(s: String, i: Int) : VariantSymbol = new VariantSymbol(s, i)
  def unapply(sym: SymbolA) = sym match {
    case vs : VariantSymbol => Some((vs.s, vs.i))
    case _ => None
  }
}

class StringSymbol(val s: String) extends SymbolA {
  override def toString() = s
}
object StringSymbol {
  def apply(s: String) = new StringSymbol(s)
  def unapply(s: SymbolA) = s match {
    case ss : StringSymbol => Some(ss.s)
    case _ => None
  }
}

// Renames the variables in 'toRename' such that the new names do not clash
// with variables in 'blackList'.
object getRenaming {
  def apply(toRename: SymbolA, blackList: List[SymbolA]) : SymbolA = apply(List(toRename), blackList).head
  def apply(toRename: List[SymbolA], blackList: List[SymbolA]) : List[SymbolA] = toRename match {
    case s :: tl => 
      if ( blackList.exists(e => e == s) ) {
        val newSym = s match {
          case StringSymbol(n) => VariantSymbol(n, 0)
          case VariantSymbol(n, i) => VariantSymbol(n, i+1)
        }
        // Put back in the list to check if the renaming does not clash again.
        getRenaming(newSym::tl, blackList)
      }
      else s :: ( getRenaming(tl, blackList) )
    case Nil => List()
  }
}


