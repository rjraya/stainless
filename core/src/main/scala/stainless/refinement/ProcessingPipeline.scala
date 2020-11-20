/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package refinement

import scala.collection.mutable.{Map => MutableMap}


trait ProcessingPipeline extends Strengthener { self =>
  import context._
  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  protected val processors: List[Processor { val strengthener: self.type }]

  def strengthen(fds: Set[FunDef]): Unit = {
    processors.map{
      p => p.run(fds)
    }
  }
}
