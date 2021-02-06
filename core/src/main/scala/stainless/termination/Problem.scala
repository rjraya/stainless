package stainless
package termination

trait Problem {

  val program: Program { val trees: Trees }
  import program._
  import program.trees.{FunDef}


  def funSet: Set[FunDef]
  def funDefs: Seq[FunDef]
  def contains(fd: FunDef): Boolean = funSet(fd)

  override def toString: String = funDefs.map(_.id).mkString("Problem(", ",", ")")
}