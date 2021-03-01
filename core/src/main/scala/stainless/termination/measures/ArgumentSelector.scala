package stainless
package termination
package measures

trait ArgumentSelector {  
  val symbols: termination.trees.Symbols
  import termination.trees._
  import symbols._

  // An ADT sort corresponds to a container type if (and only if) it has
  // a single non-recursive constructor
  object ContainerType {
    def unapply(c: ADTType): Option[Seq[ValDef]] = c.getSort.constructors match {
      case Seq(tcons) =>
        if (tcons.fields.exists(vd => isSubtypeOf(vd.tpe, c))) None
        else Some(tcons.fields)
      case _ => None
    }
  }

  def flatTypes(tpe: Type): Set[Expr => Expr] = {
    def rec(tpe: Type): Set[Expr => Expr] = tpe match {
      case ContainerType(fields) =>
        fields.flatMap {
          vd => rec(vd.tpe).map(recons => (e: Expr) => recons(adtSelector(e, vd.id)))
        }.toSet
      case TupleType(tpes) =>
        tpes.indices.flatMap {
          index => rec(tpes(index)).map(recons => (e: Expr) => recons(tupleSelect(e, index + 1, true)))
        }.toSet
      case _ => Set((e: Expr) => e)
    }

    rec(tpe)
  }

  def flatTypesPowerset(tpe: Type): Set[Expr => Expr] = {
    def powerSetToFunSet(l: TraversableOnce[Expr => Expr]): Set[Expr => Expr] = {
      l.toSet.subsets.filter(_.nonEmpty).map{
        (reconss: Set[Expr => Expr]) => (e : Expr) =>
          tupleWrap(reconss.toSeq map { f => f(e) })
      }.toSet
    }

    powerSetToFunSet(flatTypes(tpe))
  } 
}