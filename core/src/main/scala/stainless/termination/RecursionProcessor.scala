package stainless
package termination

import scala.annotation.tailrec

trait RecursionProcessor extends TerminationPipeline 
                            with MeasureAnnotator { self => 

  val s: Trees
  val t: Trees

  private def isSubtreeOf(expr: s.Expr, v: s.Variable): Boolean = {
    @tailrec
    def rec(e: s.Expr, fst: Boolean): Boolean = e match {
      case v2: s.Variable if v == v2 => !fst
      case s.ADTSelector(cc, _)      => rec(cc, false)
      case s.Annotated(e, _)         => rec(e, fst)
      case _                       => false
    }
    rec(expr, true)
  }

  private def isSubtreePredicate(arg: s.ValDef, path: s.Path, args: Seq[s.Expr], index: Int) = {
    args(index) match {
      // handle case class deconstruction in match expression!
      case v: s.Variable =>
        path.bindings.exists {
          case (vd, ccs) if vd.toVariable == v => isSubtreeOf(ccs, arg.toVariable)
          case _                               => false
        }
      case expr =>
        isSubtreeOf(expr, arg.toVariable)
    }
  }

  override def extract(fids: Problem, 
                       symbols: s.Symbols): (Problem, t.Symbols) = {
    if (fids.size > 1) { (fids, identity.transform(symbols)) } 
    else {
      object analysis extends RelationBuilder { 
        val symbolz = symbols
        val program: inox.Program{
          val trees: RecursionProcessor.this.s.type; 
          val symbols: symbolz.type
        } = inox.Program(s)(symbolz)
        val context = ???
      }

      val funDef = symbols.getFunction(fids.head)
      val recInvocations = analysis.getRelations(funDef).filter { 
        case analysis.Relation(fd, _, fi, _) => fd == fi.tfd(symbols).fd
      }

      if (recInvocations.isEmpty) {
        (fids, identity.transform(symbols))  
      } else {
        val decreasedArgument = funDef.params.zipWithIndex.find {
          case (arg, index) =>
            recInvocations.forall {
              case analysis.Relation(_, path, s.FunctionInvocation(_, _, args), _) =>
                isSubtreePredicate(arg, path, args, index)
            }
        }

        decreasedArgument match {
          case Some(p) =>
            val symbolz = symbols
            object ordering extends SumOrdering {  
              val trees: s.type = s
              val symbols: symbolz.type = symbolz
            }
            val annotated: s.FunDef = 
              annotate(funDef,ordering.measure(Seq(p._1.toVariable)))
                        
            (Set(), updater.transform(annotated, symbols))
          case None =>
            (fids, identity.transform(symbols))
        }
      }
    }  
  }

  object identity extends IdentityTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  object updater extends UpdateTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }
}
