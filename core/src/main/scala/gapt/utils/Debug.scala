package gapt.utils

extension [T](x: T) {

  /**
  * Pretty-prints out the value and returns it.
  * This is useful for debug printing inside a nested structure
  *
  * @return the value this method is called on
  */
  def dbg = pprint.log(x)
}
