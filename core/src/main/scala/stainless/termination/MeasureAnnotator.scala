package stainless
package termination

trait MeasureAnnotator {

  val s: Trees
  val t: Trees

  def annotate(funDef: s.FunDef, measure: s.Expr) {
    funDef.copy(fullBody = 
      s.exprOps.withMeasure(
        funDef.fullBody, 
        Some(measure.setPos(funDef))
      )
    )
  }

}