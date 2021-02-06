package stainless
package termination

trait SCCProcessor {

  val program: Program { val trees: Trees }

  import program._
  import program.trees._
  import program.symbols._

  def run(problems: Seq[Problem]): Seq[Problem] = {
    val funDefs = problems.flatMap{ problem =>  
      problem.funDefs.flatMap{ funDef => 
        transitiveCallees(funDef) + funDef 
      }
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