package stainless
package termination

import scala.annotation.tailrec

trait RecursionProcessor extends TerminationPipeline {
  val s: Trees
  val t: s.type

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

  override def extract(fids: Problem, symbols: s.Symbols): (Problem, t.Symbols) = {
    if (fids.size > 1) {
      val transformer = new s.IdentitySymbolTransformer{}
      (fids, transformer.transform(symbols))  
    } else {
      val funDef = fids.head
      val recInvocations = getRelations(funDef).filter { 
        case Relation(fd, _, fi, _) => fd == fi.tfd.fd
      }

      if (recInvocations.isEmpty) {
        // annotate measure 0
        ???
      } else {
        val decreases = funDef.params.zipWithIndex.find {
          case (arg, index) =>
            recInvocations.forall {
              case Relation(_, path, s.FunctionInvocation(_, _, args), _) =>
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
        }

        decreases match {
          case Some(p) =>
            val measure = ordering.measure(Seq(p._1.toVariable))
            // anotate funDef with measure
            ???
          case None =>
            // cannot continue analysing
            ???
        }
      }
    }  
  }
}
