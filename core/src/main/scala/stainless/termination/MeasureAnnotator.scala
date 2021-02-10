package stainless
package termination

trait MeasureAnnotator {

  val s: Trees
  val t: s.type

  def annotate(funDef: s.FunDef, measure: s.Expr) {
    ???
  }
}