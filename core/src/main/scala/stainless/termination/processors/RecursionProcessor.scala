package stainless
package termination

import scala.annotation.tailrec

trait RecursionProcessor extends IterativePipeline
                            with MeasurePipeline
                            with AnalysisPipeline
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

  override def extract(fids: Problem, syms: Symbols): (Problem, Symbols) = { 
    println("running recursion processor with " + fids)
    /* println(syms.functions.values.map(_.asString(
      new PrinterOptions(printUniqueIds = true)
    ))) */
    if (fids.size > 1) (fids, syms) 
    else {
      val funDef = syms.getFunction(fids.head)
      val recInvocations = analysis.getRelations(funDef).filter { 
        case analysis.Relation(fd, _, fi, _) => 
        
          fd == fi.tfd(syms).fd
      }
      println("recursive invocations of " + funDef.id)
      println(recInvocations)
      if (recInvocations.isEmpty) { println("solved in recursion processor") ; (Set(), syms) } 
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
	          println("annotating " + funDef.id + " in recursion processor")
            val integerOrdering = measures._1
            val measure = integerOrdering.measure(Seq(p._1.toVariable))
            val annotated: FunDef = annotate(funDef,measure)
            (Set(), updater.transform(annotated, syms))
          case None =>
              (fids, syms)
        }
      }
    }  
  }  
}

object RecursionProcessor { self =>
  def apply(implicit ctx: inox.Context, 
            m: Measures,
            a: Analysis): IterativePipeline = 
    new { 
      override val context = ctx 
      override val measures = m
      override val analysis = a
    } with RecursionProcessor
}