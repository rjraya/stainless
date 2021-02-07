package stainless
package termination

trait SCCProcessor extends TerminationPipeline {
  val s: ast.Trees
  val t: ast.Trees

  def extract(fds: Seq[s.FunDef], symbols: s.Symbols): (Seq[t.FunDef], t.Symbols) = {
    val funDefs = symbols.transitiveCallees(fds.toSet) ++ fds
    val pairs = symbols.allCalls.flatMap {
      case (id1, id2) =>
        val (fd1, fd2) = (symbols.getFunction(id1), symbols.getFunction(id2))
        if (funDefs(fd1) && funDefs(fd2)) Some(fd1 -> fd2) else None
    }

    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val allComponents = inox.utils.SCC.scc(callGraph)

    val f: t.Symbols = super.transform(symbols)

    ()
  }

}