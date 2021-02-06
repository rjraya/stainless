package stainless
package termination

trait SCCProcessor extends extraction.ExtractionPipeline {
  val s: ast.Trees
  val t: ast.Trees

  def extract(symbols: s.Symbols): Seq[Problem] = {
    val funDefs = problems.flatMap{ problem =>  
      transitiveCallees(problem.funDefs) + problem.funDefs
    } 
    val pairs = allCalls.flatMap {
      case (id1, id2) =>
        val (fd1, fd2) = (symbols.getFunction(id1), symbols.getFunction(id2))
        if (funDefs(fd1) && funDefs(fd2)) Some(fd1 -> fd2) else None
    }

    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val allComponents = inox.utils.SCC.scc(callGraph)
  }

}