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

}

