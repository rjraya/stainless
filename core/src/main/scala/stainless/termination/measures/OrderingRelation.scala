package stainless
package termination

trait OrderingRelation {
  val trees: Trees
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
  val trees: Trees
  val symbols: trees.Symbols
  import trees._

  object sizes extends SizeFunctions {
    val trees: self.trees.type = self.trees
    val symbols: self.symbols.type = self.symbols
  }

  val description = "comparing sum of argument sizes"

  private def size(args: Seq[Expr]) = sizes.fullSize(tupleWrap(args))

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessThan(size(args1), size(args2))
  

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = 
    LessEquals(size(args1), size(args2))
  
  def measure(args: Seq[Expr]): Expr = size(args)
}