/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}
import scala.language.existentials

trait PostconditionStrengthener extends TerminationPipeline { self =>

  val s: Trees // stainless.trees.type
  val t: Trees // stainless.trees.type

  val ctx: inox.Context

  private val strengthenedPost: MutableMap[Identifier, Option[s.Lambda]] = MutableMap.empty

  private object postStrengthener extends s.IdentitySymbolTransformer {
    override def transform(syms: s.Symbols): t.Symbols =
      syms.withFunctions(syms.functions.toSeq.map {
        case (id, fd) =>
          strengthenedPost.get(id) match {
            case Some(post @ Some(_)) => fd.copy(fullBody = s.exprOps.withPostcondition(fd.fullBody, post))
            case _                    => fd
          }
      })
  }

  private def strengthen(fd: s.FunDef, symbols: s.Symbols, cmp: (Seq[s.Expr], Seq[s.Expr]) => s.Expr): Boolean = {
    import s._
    import symbols._
    
    val postcondition = {
      val res = s.ValDef.fresh("res", fd.returnType)
      val post = fd.postcondition match {
        case Some(post) => application(post, Seq(res.toVariable))
        case _          => s.BooleanLiteral(true)
      }
      val sizePost = cmp(Seq(res.toVariable), fd.params.map(_.toVariable))
      s.Lambda(Seq(res), and(post, sizePost))
    }

    val formula = implies(fd.precOrTrue, application(postcondition, Seq(fd.body.get)))

    val strengthener = new IdentitySymbolTransformer {
      override def transform(syms: Symbols): Symbols = super.transform(syms).withFunctions {
        Seq(fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, Some(postcondition))))
      }
    }

    val newSymbols = strengthener.transform(symbols)
    val newProgram = inox.Program(s)(newSymbols)
    val api: inox.solvers.SimpleSolverAPI = ???
      // inox.solvers.SimpleSolverAPI(solvers.SolverFactory.apply(newProgram, ctx))

    // @nv: variablesOf(formula) should be non-empty as we may proceed to invalid strenghtening otherwise
    if (exprOps.variablesOf(formula).nonEmpty &&
        api.solveVALID(???/* formula */).contains(true)) {
      strengthenedPost(fd.id) = Some(postcondition)
      true
    } else {
      false
    }
  }
  
  override def extract(fids: Problem, symbols: s.Symbols): (Problem, t.Symbols) = {
    val funDefs = fids.map( id => symbols.getFunction(id) )
    val callees: Set[s.FunDef] = funDefs.flatMap(fd => symbols.transitiveCallees(fd))
    val sortedCallees: Seq[s.FunDef] = callees.toSeq.sorted(symbols.CallGraphOrderings.functionOrdering.compare)

    val symbolz = symbols
    object ordering extends SumOrdering {  
      val trees: s.type = s
      val symbols: symbolz.type = symbolz
    }
    
    // We don't add postconditions to the entire SCC 
    for (fd <- sortedCallees if !strengthenedPost.isDefinedAt(fd.id)) {
      strengthenedPost(fd.id) = None
      // test if size is smaller or equal to input
      val weakConstraintHolds = strengthen(fd, symbols, ordering.lessEquals)

      val strongConstraintHolds = 
        if (weakConstraintHolds) strengthen(fd, symbols, ordering.lessThan) else false
    }


    // call to strengthen
    // (fids, symbols)
    ???
  }
}
