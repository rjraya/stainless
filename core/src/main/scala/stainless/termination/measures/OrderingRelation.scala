package stainless
package termination

trait OrderingRelation {
  val trees: termination.trees.type
  val sizes: SizeFunctions
  import trees._

  val description: String

  /** Strictly decreasing: args1 < args2 */
  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** Weakly decreasing: args1 <= args2 */
  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** Associated measure to the ordering */
  def measure(args: Seq[Expr]): Expr
}

trait SumOrdering extends OrderingRelation { self =>
  val trees: termination.trees.type
  val sizes: SizeFunctions
  import trees._

  val description = "comparing sum of argument sizes"

  private def size(args: Seq[Expr]): Expr = sizes.fullSize(tupleWrap(args))

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessThan(size(args1), size(args2))
  

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessEquals(size(args1), size(args2))
  
  def measure(args: Seq[Expr]): Expr = size(args)
}

trait LexicographicOrdering extends OrderingRelation { self =>
  import trees._

  val description = "comparing argument lists lexicographically"

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = true, sizeOfOneExpr = e => sizes.fullSize(e))
  }

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = false, sizeOfOneExpr = e => sizes.fullSize(e))
  }

  // this should be extended to handle several types of lexicographic measures
  def measure(args: Seq[Expr]): Expr =
    tupleWrap(args.map { arg => sizes.fullSize(arg) })

  def lexicographicallySmaller(s1: Seq[Expr], s2: Seq[Expr], strict: Boolean, sizeOfOneExpr: Expr => Expr): Expr = {
    // Note: The Equal and LessThan ASTs work for both BigInt and Bitvector

    val sameSizeExprs = for ((arg1, arg2) <- s1 zip s2) yield Equals(sizeOfOneExpr(arg1), sizeOfOneExpr(arg2))

    val lessBecauseLessAtFirstDifferentPos =
      orJoin(for (firstDifferent <- 0 until scala.math.min(s1.length, s2.length)) yield and(
          andJoin(sameSizeExprs.take(firstDifferent)),
          LessThan(sizeOfOneExpr(s1(firstDifferent)), sizeOfOneExpr(s2(firstDifferent)))
      ))

    if (s1.length > s2.length || (s1.length == s2.length && !strict)) {
      or(andJoin(sameSizeExprs), lessBecauseLessAtFirstDifferentPos)
    } else {
      lessBecauseLessAtFirstDifferentPos
    }
  }
}


