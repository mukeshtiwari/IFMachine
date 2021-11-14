package secc.c

sealed trait Type extends beaver.Symbol
sealed trait CompoundType extends Type
sealed trait BaseType extends Type { def self: beaver.Symbol = this }
sealed trait TypeName extends Type { def name: String }
sealed trait LogicType extends Type

object Type {
  case class param(name: String) extends LogicType {
    override def toString = "$" + name
  }

  case class list(elem: Type) extends LogicType {
    override def toString = "list<" + elem + ">"
  }

  case class array(dom: Type, ran: Type) extends LogicType {
    override def toString = "array<" + dom + ", " + ran + ">"
  }
}

case object Void extends BaseType {
  override def toString = "void"
}

case object SignedInt extends BaseType {
  override def toString = "int"
}

case object SignedChar extends BaseType {
  override def toString = "char"
}

case class TypedefName(name: String) extends TypeName {
  override def toString = name
}

case class StructName(name: String) extends TypeName {
  override def toString = "struct " + name
}

case class UnionName(name: String) extends TypeName {
  override def toString = "enum " + name
}

case class EnumName(name: String) extends TypeName {
  override def toString = "enum " + name
}

case class PtrType(typ: Type) extends Type {
  override def toString = typ + " *"
}

case class AnonStruct(fields: List[Field]) extends CompoundType {
  def this(fields: Array[Field]) = this(fields.toList)
  override def toString = fields.mkString("struct { ", ";", "}")
}

case class AnonUnion(fields: List[Field]) extends CompoundType {
  def this(fields: Array[Field]) = this(fields.toList)
  override def toString = fields.mkString("union { ", ";", "}")
}

case class AnonEnum(consts: List[String]) extends CompoundType {
  def this(consts: Array[String]) = this(consts.toList)
  override def toString = consts.mkString("enum { ", ",", "}")
}