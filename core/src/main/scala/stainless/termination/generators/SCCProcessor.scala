package stainless
package termination
package generators

trait SCCProcessor extends TerminationPipeline { self => 
  import termination.trees._

  override def extract(fids: Seq[Problem], symbols: Symbols): (Seq[Problem], Symbols) = {
    val fds = fids.flatMap{p => p.map{id => symbols.getFunction(id)}}
    val funDefs = symbols.transitiveCallees(fds.toSet) ++ fds
    val pairs = symbols.allCalls.flatMap {
      case (id1, id2) =>
        val (fd1, fd2) = (symbols.getFunction(id1), symbols.getFunction(id2))
        if (funDefs(fd1) && funDefs(fd2)) Some(fd1 -> fd2) else None
    }

    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val allComponents: Seq[Set[FunDef]] = inox.utils.SCC.scc(callGraph)
    val sortedComponents = 
      allComponents.sorted(symbols.CallGraphOrderings.componentOrdering.compare)
    val componentIds = sortedComponents.map{ _.map{ _.id } }


    (componentIds, symbols)  
  }

}

object SCCProcessor { self =>
  def apply(implicit ctx: inox.Context): TerminationPipeline = 
    new { override val context = ctx } with SCCProcessor
}
