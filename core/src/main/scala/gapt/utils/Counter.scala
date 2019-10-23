package gapt.utils

class Counter {
  private var state = 0
  def nextId(): Int = {
    state = state + 1
    state
  }
}
