package gapt.proofs.lk

class LKRuleCreationException( name: String, message: String )
  extends Exception( s"Cannot create $name: " + message )
