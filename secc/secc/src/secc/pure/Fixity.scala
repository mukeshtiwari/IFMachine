package secc.pure

sealed trait Assoc
case object Left extends Assoc
case object Right extends Assoc
case object Non extends Assoc

sealed trait Fixity { def prec: Int }
case object Nilfix extends Fixity { def prec = 0 }
case object Formfix extends Fixity { def prec = 0 }
case class Prefix(prec: Int) extends Fixity
case class Postfix(prec: Int) extends Fixity
case class Infix(assoc: Assoc, prec: Int) extends Fixity


