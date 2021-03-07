/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

trait RelationBuilder extends CICFA { self =>

  import program.trees._
  import program.symbols._

  case class Relation(fd: FunDef, path: Path, call: FunctionInvocation, inLambda: Boolean) {
    override def toString: String =
      "Relation(" + fd.id + "," + path.toClause + ", " +
        call.tfd.id + call.args.mkString("(", ",", ")") + "," + inLambda + ")"

    def compose(that: Relation): Relation = {
      val tfd = call.tfd
      val instPath = that.path.instantiate(tfd.tpSubst)
      assert(that.fd == tfd.fd, "Cannot compose relations with incompatible functions")

      val freshParams = tfd.params.map(_.freshen)
      val paramPath = Path.empty withBindings (freshParams zip call.args)
      val subst: Map[ValDef, Expr] = (tfd.params zip freshParams.map(_.toVariable)).toMap

      val freshSubst = (instPath.bound map { vd =>
        vd -> vd.freshen
      }).toMap
      val newSubst = subst ++ freshSubst.mapValues(_.toVariable)
      val newPath = instPath.map(freshSubst, exprOps.replaceFromSymbols(newSubst, _))

      val newCall =
        exprOps.replaceFromSymbols(newSubst, tfd.instantiate(that.call)).asInstanceOf[FunctionInvocation]

      Relation(fd, path merge paramPath merge newPath, newCall, inLambda || that.inLambda)
    }
  }

  def getRelations(funDef: FunDef): Set[Relation] = {
    val analysis = analyze(funDef.id)

    // TODO: transform into a traverser which yields the relations list.
    object collector extends transformers.TransformerWithPC with transformers.DefinitionTransformer {
      val s: program.trees.type = program.trees
      val t: program.trees.type = program.trees
      val symbols: program.symbols.type = program.symbols

      type Env = Path
      val initEnv = Path.empty
      val pp = Path

      var inLambda: Boolean = false
      val relations: ListBuffer[Relation] = new ListBuffer

      override def transform(e: Expr, path: Path): Expr = e match {
        case fi @ FunctionInvocation(_, _, args) =>
          relations += Relation(funDef, path, fi, inLambda)

          fi.copy(args = (getFunction(fi.id).params.map(_.id) zip args).map {
            case (id, l @ Lambda(largs, body)) /* if analysis.isApplied(l) */ =>
              println("in an applied lambda with arg " + l)
              val old = inLambda
              inLambda = true
              val constr = largs match {
                  case vd@ValDef(lname, RefinementType(avd, refT), f) :: t => 
                    val newVar = Variable(lname, RefinementType(avd, refT), f)
                    exprOps.replace(Map((avd.toVariable,newVar)), refT)
                  case _ => 
                    BooleanLiteral(true)
                }

              println("constr is " + constr)
              val res = Lambda(largs, transform(body, path withBounds largs withCond constr))
              inLambda = old
              res
            case (_, arg) => 
              transform(arg, path)
          })

        case l: Lambda =>
          if (analysis.isApplied(l)) {
            val old = inLambda
            inLambda = true
            val res = super.transform(e, path)
            inLambda = old
            res
          } else {
            l
          }

        case _ =>
          super.transform(e, path)
      }
    }

    collector.transform(funDef)
    println("relations of "+ funDef.id)
    collector.relations.map(r => println(r))
    collector.relations.toSet
  }
}
 