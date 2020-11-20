/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package refinement

import scala.language.existentials

trait Processor {
  
  val strengthener: ProcessingPipeline

  type Problem = Set[strengthener.program.trees.FunDef]
  def run(problem: Problem): Unit
}

trait OrderingProcessor extends Processor {

  val ordering: OrderingRelation {
    val strengthener: OrderingProcessor.this.strengthener.type
  }

}