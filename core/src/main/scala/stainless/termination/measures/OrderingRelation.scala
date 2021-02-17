package stainless
package termination

trait OrderingRelation {
  val trees: termination.trees.type
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
  val symbols: trees.Symbols
  val sizes: SizeFunctions
  import trees._

  val description = "comparing sum of argument sizes"

  private def size(args: Seq[Expr]) = sizes.fullSize(tupleWrap(args))

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessThan(size(args1), size(args2))
  

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessEquals(size(args1), size(args2))
  
  def measure(args: Seq[Expr]): Expr = size(args)
}