package stainless
package termination

import scala.annotation.tailrec

trait RecursionProcessor extends IterativePipeline 
                            with measures.MeasureAnnotator { self => 
  import termination.trees._

  private def isSubtreeOf(expr: Expr, v: Variable): Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case v2: Variable if v == v2 => !fst
      case ADTSelector(cc, _)      => rec(cc, false)
      case Annotated(e, _)         => rec(e, fst)
      case _                       => false
    }
    rec(expr, true)
  }

  private def isSubtreePredicate(arg: ValDef, path: Path, args: Seq[Expr], index: Int) = {
    args(index) match {
      // handle case class deconstruction in match expression!
      case v: Variable =>
        path.bindings.exists {
          case (vd, ccs) if vd.toVariable == v => isSubtreeOf(ccs, arg.toVariable)
          case _                               => false
        }
      case expr =>
        isSubtreeOf(expr, arg.toVariable)
    }
  }

  override def extract(fids: Problem, symbols: Symbols): (Problem, Symbols) = {
    if (fids.size > 1) (fids, symbols) 
    else {
      object analysis extends RelationBuilder { 
        val symbolz = symbols
        val program: inox.Program{
          val trees: termination.trees.type; 
          val symbols: symbolz.type
        } = inox.Program(termination.trees)(symbolz)
        val context = ???
      }

      val funDef = symbols.getFunction(fids.head)
      val recInvocations = analysis.getRelations(funDef).filter { 
        case analysis.Relation(fd, _, fi, _) => fd == fi.tfd(symbols).fd
      }

      if (recInvocations.isEmpty) { (fids, symbols) } 
      else {
        val decreasedArgument = funDef.params.zipWithIndex.find {
          case (arg, index) =>
            recInvocations.forall {
              case analysis.Relation(_, path, FunctionInvocation(_, _, args), _) =>
                isSubtreePredicate(arg, path, args, index)
            }
        }

        decreasedArgument match {
          case Some(p) =>
            val symbolz = symbols
            object ordering extends SumOrdering {  
              val trees: termination.trees.type = termination.trees
              val symbols: symbolz.type = symbolz
            }
            val annotated: FunDef = 
              annotate(funDef,ordering.measure(Seq(p._1.toVariable)))
                        
            (Set(), updater.transform(annotated, symbols))
          case None =>
            (fids, symbols)
        }
      }
    }  
  }

  object updater extends UpdateTransformer {
    val s: termination.trees.type = termination.trees
    val t: termination.trees.type = termination.trees
  }
}
 