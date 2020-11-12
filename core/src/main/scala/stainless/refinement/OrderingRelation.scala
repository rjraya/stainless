/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package refinement

trait OrderingRelation extends SolverProvider { self: StructuralSize => 
  val checker: ProcessingPipeline
  import checker.program.trees._

  val description: String

  /** Strictly decreasing: args1 < args2 */
  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** Weakly decreasing: args1 <= args2 */
  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr
}

trait SumOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols._

  val description = "comparing sum of argument sizes"

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    LessThan(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    LessEquals(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }
}

trait LexicographicOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols._

  val description = "comparing argument lists lexicographically"

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = true, sizeOfOneExpr = e => self.fullSize(e))
  }

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = false, sizeOfOneExpr = e => self.fullSize(e))
  }
}

trait BVOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols._

  val description = "comparing bitvector arguments lexicographically"

  def bvSize(e: Expr): Expr = FunctionInvocation(bvAbs(e.getType.asInstanceOf[BVType]).id, Seq(), Seq(e))

  /* Note: We swap the arguments to the [[lexicographicallySmaller]] call since
   * [[bvSize]] maps into negative values! (avoids -Integer.MIN_VALUE overflow) */
  def groupedBySize(as: Seq[Expr]): Map[Int, Seq[Expr]] =
    as.collect { case IsTyped(e, BVType(_, i)) => i -> e }.groupBy(_._1).mapValues(_.map(_._2))

  private def compare(args1: Seq[Expr], args2: Seq[Expr], strict: Boolean): Expr = {
    val bv1 = groupedBySize(args1)
    val bv2 = groupedBySize(args2)

    val commonKeys = bv1.keys.toSet intersect bv2.keys.toSet

    orJoin(commonKeys.map { k =>
      // Here we swap bv1 and bv2!
      val kindDecreasing = lexicographicallySmaller(bv2(k), bv1(k), strict = strict, sizeOfOneExpr = bvSize)

      val kindsNotIncreasing =
        andJoin(
          commonKeys
            .filter { _ != k }
            .map { pk =>
              lexicographicallySmaller(bv2(pk), bv1(pk), strict = false, sizeOfOneExpr = bvSize)
            }
            .toSeq
        )

      and(kindDecreasing, kindsNotIncreasing)
    }.toSeq)
  }

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = compare(args1, args2, true)

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = compare(args1, args2, false)
}
