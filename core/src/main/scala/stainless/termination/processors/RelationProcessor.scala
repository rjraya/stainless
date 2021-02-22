/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination
package processors

import scala.language.existentials

import inox.utils._ 

import scala.concurrent.duration._

trait RelationProcessor extends MeasurePipeline 
                        with AnalysisPipeline
                        with measures.MeasureAnnotator {
  import termination.trees._

  override def extract(fids: Problem, syms: Symbols): (Problem, Symbols) = { 
    println("running relation processor")
    val funDefs = fids.map( id => syms.getFunction(id) ) 
    val formulas = funDefs.map { funDef =>
      funDef -> analysis.getRelations(funDef).collect {
        case analysis.Relation(_, path, fi @ FunctionInvocation(_, _, args), _) if funDefs(fi.tfd(syms).fd) =>
          val args0 = funDef.params.map(_.toVariable)
          def constraint(expr: Expr) = path implies expr
          val lessThan = measures._1.lessThan(args, args0)
          val lessEquals = measures._1.lessEquals(args, args0)
          (fi.tfd(syms).fd, (constraint(lessThan), constraint(lessEquals)))
      }
    }

    sealed abstract class Result
    case object Success extends Result
    case class Dep(deps: Set[FunDef]) extends Result
    case object Failure extends Result

    val sizes = measures._2.getFunctions(syms)
    val newSyms: Symbols = sizes.foldLeft(syms)( 
      (symb, sze) => updater.transform(sze, symb) 
    )
    val program: inox.Program{
        val trees: termination.trees.type; 
        val symbols: trees.Symbols
      } = inox.Program(termination.trees)(newSyms)
    val api = extraction.extractionSemantics
                        .getSemantics(program)
                        .getSolver(context)
                        .withTimeout(2.5.seconds)
                        .toAPI 

    val decreasing = formulas.map {
      case (fd, formulas) =>
        val solved = formulas.map {
          case (fid, (gt, ge)) =>
            if (api.solveVALID(gt).contains(true)) Success
            else if (api.solveVALID(ge).contains(true)) Dep(Set(fid))
            else Failure
        }

        val result =
          if (solved.contains(Failure)) Failure
          else {
            val deps = solved.collect { case Dep(fds) => fds }.flatten
            if (deps.isEmpty) Success
            else Dep(deps)
          }
        fd -> result
    }

    val (terminating, nonTerminating) = {
      val ok = decreasing.collect { case (fd, Success) => fd -> IntegerLiteral(0) }
      val nok = decreasing.collect { case (fd, Dep(fds)) => fd -> fds }.toList

      var iteration = 0
      val (allOk, allNok) = fixpoint[(Set[(FunDef, IntegerLiteral)], List[(FunDef, Set[FunDef])])] {
        case (fds, deps) =>
          iteration += 1
          val (okDeps, nokDeps) = deps.partition { case (fd, deps) => deps.subsetOf(fds.map { _._1 }) }
          val newFds = fds ++ okDeps.map { p =>
            (p._1, IntegerLiteral(iteration))
          }
          (newFds, nokDeps)
      } ((ok.toSet, nok))

      (allOk, allNok.map(_._1).toSet ++ decreasing.collect { case (fd, Failure) => fd })
    }

    assert(terminating.map(_._1) ++ nonTerminating == funDefs)

    if (nonTerminating.isEmpty) {
      val newSyms = terminating.foldLeft(syms){ (updatedSyms, tf) =>
        val measure = exprOps.measureOf(tf._1.fullBody) match {
          case Some(measure) => measure
          case None =>
            val induced = measures._1.measure(tf._1.params.map { _.toVariable })
            flatten(induced, Seq(tf._2), syms)
        }
        val annotated: FunDef = annotate(tf._1,measure)
        updater.transform(annotated, updatedSyms)
      }
      (Set(), newSyms)
    } else {
      (fids, syms)
    }
  }

}

object RelationProcessor { self =>
  def apply(implicit ctx: inox.Context, 
            m: Measures,
            a: Analysis): MeasurePipeline = 
    new {  
      override val context = ctx 
      override val measures = m
      override val analysis = a
    } with RelationProcessor
}