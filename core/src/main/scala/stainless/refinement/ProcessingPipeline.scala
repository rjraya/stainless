/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package refinement

trait ProcessingPipeline extends Strengthener { self =>
  import context._
  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  protected val processors: List[Processor { val checker: self.type }]

  def strengthen(fds: Set[FunDef]): Set[FunDef] = 
    self.strengthenApplications(fds)

}
