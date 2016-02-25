package at.logic.gapt.utils

import scala.collection.mutable

object NameGenerator {
  val nameRegex = """(.*)_(\d+)""".r
}
import NameGenerator._

class NameGenerator( initiallyUsed: Iterable[String] ) {
  private val used = initiallyUsed.to[mutable.Set]

  def fresh( name: String ): String =
    if ( used( name ) ) {
      name match {
        case nameRegex( prefix, idx ) => freshWithIndex( prefix )
        case _                        => freshWithIndex( name )
      }
    } else {
      used += name
      name
    }

  def freshWithIndex( name: String ): String =
    fresh( name, firstFreeIndex( name ) )

  private val firstFreeIndex = mutable.Map[String, Int]().withDefaultValue( 0 )
  private def fresh( prefix: String, idx: Int ): String = {
    val newName = s"${prefix}_$idx"
    if ( used( newName ) ) {
      fresh( prefix, idx + 1 )
    } else {
      firstFreeIndex( prefix ) = idx + 1
      used += newName
      newName
    }
  }

  def freshStream( name: String ) = Stream.continually( freshWithIndex( name ) )
}
