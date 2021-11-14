package secc.pure

sealed trait Sort extends Sort.term {
  def free: Set[Param]
  def instance: Sort
  def contains(that: Param): Boolean
  def rename(re: TRen): Sort
  def subst(ty: Typing): Sort
}

trait Parametric[A] {
  this: A =>
  def params: Set[Param]
  def rename(re: TRen): A
  def subst(ty: Typing): A

  def generic: A = {
    val re = Sort.fresh(params)
    if (!re.isEmpty) {
      rename(re)
    } else {
      this
    }
  }
}

case class Param(name: String, index: Option[Int] = None) extends Sort with Sort.x {
  def fresh(index: Int) = {
    Param(name, Some(index))
  }
  def contains(that: Param) = (this == that)

  var _instance: Option[Sort] = None

  def instance_=(that: Sort) {
    assert(_instance.isEmpty, "parameter already instantiated: " + this + ", new instance: " + that)
    _instance = Some(that)
  }

  def instance = _instance match {
    case Some(that) =>
      val res = that.instance
      _instance = Some(res)
      res
    case None =>
      this
  }

  override def toString = "$" + (name __ index)
}

object Param {
  val alpha = Param("a")
  val beta = Param("b")

  val list = Sort.list(alpha)
  val array = Sort.array(alpha, beta)
}

case class Constr(fun: Fun, test: Fun, sels: List[Fun]) {
  def free = fun.params ++ test.params ++ sels.flatMap(_.params)
  def rename(re: TRen) = ???
  def subst(ty: Typing) = ???
  override def toString = {
    val args = sels map { fun => fun + ": " + fun.ret }
    fun.format(args, 0, Non) + " with " + test
  }
}

object Sort extends Alpha[Sort, Param] {
  val bool = base("bool")
  val int = base("int")
  val sec = base("sec")
  val unit = base("unit")

  case class base(name: String) extends Sort {
    def free = Set()
    def contains(that: Param) = false
    def instance = this
    def rename(re: TRen) = this
    def subst(ty: Typing) = this
    override def toString = name
  }

  case class pointer(elem: Sort) extends Sort {
    def free = elem.free
    def contains(that: Param) = elem contains that
    def instance = pointer(elem.instance)
    def rename(re: TRen) = pointer(elem rename re)
    def subst(ty: Typing) = pointer(elem subst ty)
    override def toString = "Pointer<" + elem + ">"
  }

  case class array(dom: Sort, ran: Sort) extends Sort {
    def free = dom.free ++ ran.free
    def contains(that: Param) = (dom contains that) || (ran contains that)
    def instance = array(dom.instance, ran.instance)
    def rename(re: TRen) = array(dom rename re, ran rename re)
    def subst(ty: Typing) = array(dom subst ty, ran subst ty)
    override def toString = "Array<" + dom + ", " + ran + ">"
  }

  case class list(elem: Sort) extends Sort {
    def free = elem.free
    def contains(that: Param) = elem contains that
    def instance = list(elem.instance)
    def rename(re: TRen) = list(elem rename re)
    def subst(ty: Typing) = list(elem subst ty)
    override def toString = "List<" + elem + ">"
  }

  case class tuple(elems: List[Sort]) extends Sort {
    def free = Set(elems flatMap (_.free): _*)
    def contains(that: Param) = elems exists (_ contains that)
    def instance = tuple(elems map (_.instance))
    def rename(re: TRen) = tuple(elems map (_ rename re))
    def subst(ty: Typing) = tuple(elems map (_ subst ty))
    override def toString = "Tuple<" + elems.mkString(", ") + ">"
  }

  case class datatype(self: Param, constrs: List[Constr]) extends Sort with Sort.bind {
    def bound = Set(self)
    def free = Set(constrs flatMap (_.free): _*) - self
    def contains(that: Param) = ???
    def instance = ???
    def rename(a: TRen, re: TRen) = datatype(self rename a, constrs map (_ rename re))
    def subst(a: TRen, ty: Typing) = datatype(self rename a, constrs map (_ subst ty))
    override def toString = "Datatype<" + self + ". " + constrs.mkString(" | ") + ">"
  }

  def unify(pats: List[Sort], args: List[Sort]): Unit = {
    unify(pats, args, Set.empty[Param])
  }

  def unify(pats: List[Sort], args: List[Sort], nongen: Set[Param]): Unit = (pats, args) match {
    case (Nil, Nil) =>
    case (pat :: pats, arg :: args) =>
      unify(pat, arg, nongen)
      unify(pats, args, nongen)
    case _ =>
      assert(false, "ill-typed: " + pats + " mismatches " + args)
  }

  def unify(pat: Sort, arg: Sort): Unit = {
    unify(pat, arg, Set.empty[Param])
  }

  def unify(pat: Sort, arg: Sort, nongen: Set[Param]): Unit = {
    // println("unify")
    // println("  " + pat + " = " + arg)
    // println("  " + pat.instance + " = " + arg.instance)
    _unify(pat, arg, nongen)
    // println("result")
    // println("  " + pat + " = " + arg)
    // println("  " + pat.instance + " = " + arg.instance)
  }

  def _unify(pat: Sort, arg: Sort, nongen: Set[Param]): Unit = (pat.instance, arg.instance) match {
    case (pat, arg) if pat == arg =>
    case (p: Param, arg) =>
      assert(!(nongen contains p), "ill-typed: non-generic " + pat + " cannot be instantiated with " + arg)
      assert(!(arg contains p), "ill-typed: recursive unification " + pat + " occurs in " + arg)
      // println(p + ".instance = " + arg)
      p.instance = arg
    case (arg, p: Param) =>
      unify(p, arg, nongen)
    case (pointer(pat), pointer(arg)) =>
      unify(pat, arg, nongen)
    case (array(patdom, patran), array(argdom, argran)) =>
      unify(patdom, argdom, nongen)
      unify(patran, argran, nongen)
    case (list(pat), list(arg)) =>
      unify(pat, arg, nongen)
    case (tuple(pats), tuple(args)) =>
      unify(pats, args, nongen)
    case (pat, arg) =>
      assert(false, "ill-typed: " + pat + " mismatches " + arg)
  }
}