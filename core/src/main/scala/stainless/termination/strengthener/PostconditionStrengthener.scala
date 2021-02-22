/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}
import scala.language.existentials

import scala.concurrent.duration._

trait PostconditionStrengthener extends MeasurePipeline { self =>
  import termination.trees._

  private val strengthenedPost: MutableMap[Identifier, Option[Lambda]] = MutableMap.empty

  private object postStrengthener extends IdentitySymbolTransformer {
    override def transform(syms: Symbols): Symbols =
      syms.withFunctions(syms.functions.toSeq.map {
        case (id, fd) =>
          strengthenedPost.get(id) match {
            case Some(post @ Some(_)) => fd.copy(fullBody = s.exprOps.withPostcondition(fd.fullBody, post))
            case _                    => fd
          }
      })
  }

  private def strengthen(fd: FunDef, syms: Symbols, cmp: (Seq[Expr], Seq[Expr]) => Expr): Boolean = {
    import syms._
    println("strengthening " + fd.id)
    val postcondition = {
      val res = ValDef.fresh("res", fd.returnType)
      val post = fd.postcondition match {
        case Some(post) => application(post, Seq(res.toVariable))
        case _          => BooleanLiteral(true)
      }
      val sizePost = cmp(Seq(res.toVariable), fd.params.map(_.toVariable))
      Lambda(Seq(res), and(post, sizePost))
    }

    val formula = implies(fd.precOrTrue, application(postcondition, Seq(fd.body.get)))

    val strengthener = new IdentitySymbolTransformer {
      override def transform(syms: Symbols): Symbols = super.transform(syms).withFunctions {
        Seq(fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, Some(postcondition))))
      }
    }

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
    // @nv: variablesOf(formula) should be non-empty as we may proceed to invalid strenghtening otherwise
    if (exprOps.variablesOf(formula).nonEmpty &&
        api.solveVALID(formula).contains(true)) {
      strengthenedPost(fd.id) = Some(postcondition)
      true
    } else {
      false
    }
  }
  
  override def extract(fids: Problem, symbols: Symbols): (Problem, Symbols) = {
    println("running post-condition strengthener")
    val funDefs = fids.map( id => symbols.getFunction(id) )
    val callees: Set[FunDef] = funDefs.flatMap(fd => symbols.transitiveCallees(fd))
    val sortedCallees: Seq[FunDef] = callees.toSeq.sorted(symbols.CallGraphOrderings.functionOrdering.compare)

    val ordering = measures._1
    
    // We don't add postconditions to the entire SCC 
    for (fd <- sortedCallees if !strengthenedPost.isDefinedAt(fd.id)) {
      strengthenedPost(fd.id) = None
      // test if size is smaller or equal to input
      val weakConstraintHolds = strengthen(fd, symbols, ordering.lessEquals)

      val strongConstraintHolds = 
        if (weakConstraintHolds) strengthen(fd, symbols, ordering.lessThan) else false
    }
    println("end postcondition strengthener")
    val res = (fids, postStrengthener.transform(symbols))
    symbols.functions.map{ case (name,fun) => println(fun) }
    res
  }
}

object PostconditionStrengthener { self =>
  def apply(implicit ctx: inox.Context, 
            m: Measures): MeasurePipeline = 
    new { 
      override val context = ctx 
      override val measures = m
    } with PostconditionStrengthener
}