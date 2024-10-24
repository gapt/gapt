package gapt.expr.schema

import gapt.expr.Const
import gapt.expr.ty.TBase

object Tw extends TBase("ω", List())

object zero extends Const("0", Tw, Nil)
object succ extends Const("s", Tw ->: Tw, Nil)
object pred extends Const("p", Tw ->: Tw, Nil)