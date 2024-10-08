package gapt.utils

import scala.collection.mutable

object NameGenerator {

  /**
   * Shared by name generators to avoid overhead of recompiling the
   * regular expression on instance creation.
   */
  private val nameVariantRegex = """(.*)_(\d+)""".r

}

class NameGenerator(initiallyUsed: Iterable[String]) {

  private val usedNames = initiallyUsed.iterator.to(mutable.Set)

  /**
   * Generates fresh names.
   *
   * @param name The name for which a fresh variant is to be generated.
   * @return Returns `name` if `name` does not occur in the initially used
   * names and `name` has not yet been generated by this name generator.
   * Otherwise, a name of the form`name`_<n> is returned, such that `name`_<n>
   * has not been generated by a previous call to this method.
   */
  def fresh(name: String): String = {

    import NameGenerator.nameVariantRegex

    if (usedNames contains name) {
      name match {
        case nameVariantRegex(prefix, _) => freshWithIndex(prefix)
        case _                           => freshWithIndex(name)
      }
    } else {
      usedNames += name
      name
    }
  }

  /**
   * Generates a fresh variant of a name.
   *
   * @param name The name for which a fresh variant is to be generated.
   * @return Returns a name of the form `name`_<n>, such that this name has
   * not been generated by any previous call to this name generator.
   */
  def freshWithIndex(name: String): String =
    fresh(name, firstFreeIndex(name))

  /**
   * Generates a fresh variant of a name.
   * @param baseName The pattern based on which names are generated. For every
   * distinct non-negative integers i and j, `baseName(i)` and `baseName(j)`
   * must be distinct names.
   * @return A name of the form `baseName(n)` that has not been generated by any
   * previous call to this name generator and such that `n` is the least
   * non-negative integer with this property. Furthermore the subsequent names
   * generated by this name generator will not include `baseName(n)`.
   */
  def freshWithIndex(baseName: Int => String): String = {
    var index = 0
    while (usedNames.contains(baseName(index))) {
      index += 1
    }
    val newName = baseName(index)
    usedNames += newName
    newName
  }

  private val firstFreeIndex = mutable.Map[String, Int]().withDefaultValue(0)

  private def fresh(prefix: String, idx: Int): String = {
    val newName = s"${prefix}_$idx"
    if (usedNames(newName)) {
      fresh(prefix, idx + 1)
    } else {
      firstFreeIndex(prefix) = idx + 1
      usedNames += newName
      newName
    }
  }

  /**
   * Generates a stream of fresh variants.
   *
   * @param name The name for which a stream of fresh variants is to be
   * generated.
   * @return A stream of fresh variants of the form `name`_<n>.
   */
  def freshStream(name: String): LazyList[String] = {
    LazyList.continually(freshWithIndex(name))
  }

  /**
   * Creates a new name generator from this name generator.
   *
   * @return The new name generator does not generate any names that have so
   * far been generated by this name generator, moreover it does not generate
   * names that are contained in the initially used names of this name
   * generator.
   */
  def fork: NameGenerator = new NameGenerator(usedNames)
}
