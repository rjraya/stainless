package stainless
package termination
package measures

trait MeasureAnnotator {

  import termination.trees._

  def annotate(funDef: FunDef, measure: Expr): FunDef = {
    funDef.copy(fullBody = 
      exprOps.withMeasure(
        funDef.fullBody, 
        Some(measure.setPos(funDef))
      )
    )
  }

  // if given a measure of the form (induced,rest) where
  // induced is potentially a tuple, flatten will compute
  // the measure (induced.flatten,rest)
  //
  // in principle we consider only one nesting depth
  def flatten(induced: Expr, rest: Seq[Expr], syms: Symbols): Expr = {
    val unwrapped: Seq[Expr] = induced.getType(syms) match {
      case TupleType(_) => unwrapTuple(induced, true)(syms)
      case _            => Seq(induced)
    }
    tupleWrap(unwrapped ++ rest)
  }


}

