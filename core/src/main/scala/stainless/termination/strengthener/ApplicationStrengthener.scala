package stainless
package termination
package strengthener

import scala.language.existentials

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait ApplicationStrengthener extends IterativePipeline
                              with MeasurePipeline
                              with AnalysisPipeline { self =>  
  import termination.trees._
  
  sealed abstract class SizeConstraint
  case object StrongDecreasing extends SizeConstraint
  case object WeakDecreasing extends SizeConstraint
  case object NoConstraint extends SizeConstraint

  private val strengthenedApp: MutableSet[FunDef] = MutableSet.empty

  protected def strengthened(fd: FunDef): Boolean = strengthenedApp(fd)

  private val appConstraint: MutableMap[(Identifier, Identifier), SizeConstraint] = MutableMap.empty

  def applicationConstraint(fid: Identifier, id: Identifier, largs: Seq[ValDef], args: Seq[Expr], ordering: OrderingRelation): Option[Expr] =
    appConstraint.get(fid -> id) match {
      case Some(StrongDecreasing) => Some(ordering.lessThan(largs.map(_.toVariable), args))
      case Some(WeakDecreasing)   => Some(ordering.lessEquals(largs.map(_.toVariable), args))
      case _                      => None
    }

  private val toUpdate: MutableMap[Identifier, (Type, Int)] = MutableMap.empty


  // constraint v -> 
  private def bodyDecrease(fd: FunDef, 
                           fdArgs: Seq[Variable],
                           symbols: Symbols,
                           ordering: OrderingRelation,
                           api: inox.solvers.SimpleSolverAPI { val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} }
                          ): Map[Variable, SizeConstraint] = {
    val applications = symbols.collectWithPC(fd.fullBody) {
      case (Application(v: Variable, args), path) => (path, v, args)
    }.distinct
    val fdArgs = fd.params.map(_.toVariable)
    val allFormulas = 
      for ((path, v, appArgs) <- applications) yield {
        val soft = path implies ordering.lessEquals(appArgs, fdArgs)
        val hard = path implies ordering.lessThan(appArgs, fdArgs)
        v -> ((soft, hard))
      }

    val formulaMap = allFormulas.groupBy(_._1).mapValues(_.map(_._2).unzip).toMap

    val constraints = 
      for ((v, (weakFormulas, strongFormulas)) <- formulaMap) yield v -> {
        if (api.solveVALID(termination.trees.andJoin(weakFormulas.toSeq)).contains(true)) {
          if (api.solveVALID(andJoin(strongFormulas.toSeq)).contains(true)) {
            StrongDecreasing
          } else WeakDecreasing
        } else NoConstraint
      }
    constraints
  }

  // constraint fi -> v for v higher-order parameter of f
  private def higherOrderDecrease(
                          fd: FunDef, 
                          fdArgs: Seq[Variable],
                          constraints: Map[Variable, SizeConstraint], 
                          ordering: OrderingRelation,
                          api: inox.solvers.SimpleSolverAPI { val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} },
                          symbols: Symbols): Unit = {
    val fdHOArgs = fdArgs.filter(_.tpe.isInstanceOf[FunctionType]).toSet
    val invocations = symbols.collectWithPC(fd.fullBody) {
      case (fi @ FunctionInvocation(_, _, args), path)
          if (fdHOArgs intersect args.collect { case v: Variable => v }.toSet).nonEmpty =>
        (path, args, (args zip fi.tfd(symbols).fd.params).collect {
          case (v: Variable, vd) if fdHOArgs(v) => v -> ((fi.id, vd.id))
        })
    }
    val var2invocations: Seq[(Variable, ((Identifier, Identifier), Path, Seq[Expr]))] =
      for ((path, args, mapping) <- invocations; (v, p) <- mapping) yield v -> (p, path, args)
    val invocationMap: Map[Variable, Seq[((Identifier, Identifier), Path, Seq[Expr])]] =
      var2invocations.groupBy(_._1).mapValues(_.map(_._2))

    val outers = invocationMap.mapValues(_.filter(_._1._1 != fd))
    for (v <- fdHOArgs) {
      appConstraint(fd.id -> v.id) = constraint(v, outers.getOrElse(v, Seq.empty), constraints, fdArgs, ordering, symbols, api)
    }

    val selfs = invocationMap.mapValues(_.filter(_._1._1 == fd))
    for (v <- fdHOArgs) {
      appConstraint(fd.id -> v.id) = constraint(v, selfs.getOrElse(v, Seq.empty), constraints, fdArgs, ordering, symbols, api)
    }
  }

  // constraint f -> fi and combination of constraints
  def constraint(
          v: Variable,
          passings: Seq[((Identifier, Identifier), Path, Seq[Expr])],
          constraints: Map[Variable,SizeConstraint],
          fdArgs: Seq[Variable], 
          ordering: OrderingRelation,
          symbols: Symbols, 
          api: inox.solvers.SimpleSolverAPI { val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} }
      ): SizeConstraint = {
    import symbols._
    if (constraints.get(v) == Some(NoConstraint)) NoConstraint
    else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
    else {
      passings.foldLeft[SizeConstraint](constraints.getOrElse(v, StrongDecreasing)) {
        case (constraint, (key, path, args)) =>
          lazy val strongFormula = path implies ordering.lessThan(args, fdArgs)
          lazy val weakFormula = path implies ordering.lessEquals(args, fdArgs)

          (constraint, appConstraint.get(key)) match {
            case (_, Some(NoConstraint)) => scala.sys.error("Whaaaat!?!? This shouldn't happen...")
            case (_, None)               => NoConstraint
            case (NoConstraint, _)       => NoConstraint
            case (StrongDecreasing | WeakDecreasing, Some(StrongDecreasing)) =>
              if (api.solveVALID(weakFormula).contains(true)) StrongDecreasing
              else NoConstraint
            case (StrongDecreasing, Some(WeakDecreasing)) =>
              if (api.solveVALID(strongFormula).contains(true)) StrongDecreasing
              else if (api.solveVALID(weakFormula).contains(true)) WeakDecreasing
              else NoConstraint
            case (WeakDecreasing, Some(WeakDecreasing)) =>
              if (api.solveVALID(weakFormula).contains(true)) WeakDecreasing
              else NoConstraint
          }
      }
    }
  }

  def annotateStrength(fd: FunDef, syms: Symbols, ordering: OrderingRelation): FunDef = {
    object transformer extends {
      val s: termination.trees.type = termination.trees;
      val t: termination.trees.type = termination.trees;
      val symbols: termination.trees.Symbols = syms
    } with transformers.TransformerWithPC
      with    transformers.DefinitionTransformer {
      type Env = Path
      val initEnv = Path.empty
      val pp = Path

      override def transform(e: Expr, path: Path): Expr = e match {
        case fi @ FunctionInvocation(_, _, args) =>
          println("annotating function invocation " + fi.id + " called from " + fd.id)
	        println(appConstraint)
          val analyzed = analysis.analyze(fd.id) 
          /* creating new arguments */
          val newArgs = (symbols.getFunction(fi.id).params.map(_.id).zipWithIndex zip args).map {
            case ((id,index), l @ Lambda(largs, body)) if analyzed.isApplied(l) =>
              val cnstr = self.applicationConstraint(fi.id, id, largs, args, ordering)
              cnstr match {
                case Some(constr) => 
                  /* create a new lambda */
                  println("creating a new lambda!!!!!")
                  val newLArgs = largs.map{ larg => 
                    val refineArg = ValDef.fresh("z", larg.tpe)
                    val cnstr1 = exprOps.replace(Map(larg.toVariable -> refineArg.toVariable),constr)
                    val tpe1 = RefinementType(refineArg, cnstr1)
		                toUpdate += fi.id -> (tpe1, index)
                    larg.copy(tpe = tpe1)
                  }
                  val recBody = transform(body, path withBounds largs)

                  val largsDefs = largs.map(_.toVariable)
                  val newLArgsDefs = newLArgs.map(_.toVariable)
                  val subst = largsDefs.zip(newLArgsDefs).toMap
                  val newBody = exprOps.replaceFromSymbols(subst, recBody)                  
                  Lambda(newLArgs, newBody)
                case None => l
              }
            case (_, arg) => transform(arg, path)
          }

          fi.copy(args = newArgs)
        case _ => super.transform(e, path)
      }
    }

    transformer.transform(fd)
  }

  def annotateSymbols(syms: Symbols, ordering: OrderingRelation): Symbols = {
    val funsToUpdate = toUpdate.keys.map{ syms.getFunction(_) }
    //println("functions to update")
    //println(toUpdate)

    val res = funsToUpdate.foldLeft(syms){ (symbols, f) =>
      val (newType, index) = toUpdate(f.id)
      val newFun = f.params(index).getType(syms) match {
        case ts@FunctionType(domTypes,retType) =>
          val param = f.params(index) 
          val largs = domTypes.map{ t => ValDef.fresh("z", t) }
          val cnstr = self.applicationConstraint(f.id, param.id, largs, f.params.map(_.toVariable), ordering)
          cnstr match {
            case Some(constraint) => 
              val newDomTypes = largs.map{ larg => RefinementType(larg, constraint) }
              val newParam = param.copy(tpe = FunctionType(newDomTypes,retType))
              val newParams = f.params.updated(index,newParam)
              f.body(syms) match {
                case Some(body) => 
                  val newBody = exprOps.replace(
                    Map(param.toVariable -> newParam.toVariable),body)
                  f.copy(params = newParams, fullBody = newBody)
                case None =>
                  f.copy(params = newParams)
              }
            case None => throw inox.FatalError("should be a constraint") 
          }
          
        case _ =>             
          throw inox.FatalError("should be a lambda") 
      }

      updater.transform(newFun,symbols)
    }
    //println("annotated symbols")
    //println(res)
    /* println(res.asString(
      new PrinterOptions(printUniqueIds = true, printTypes = true, symbols = Some(res)))
    ) */
    res
  }


  override def extract(fids: Problem, symbols: Symbols): (Problem, Symbols) = {
    import symbols._
    println("running application strengthener")
    println(symbols.functions.values.map(_.id.asString(
      new PrinterOptions(printUniqueIds = true)
    )))
    val funDefs: Set[FunDef] = fids.map( id => symbols.getFunction(id) )
    val transitiveFunDefs = funDefs ++ funDefs.flatMap(f => symbols.transitiveCallees(f))
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted(symbols.CallGraphOrderings.functionOrdering)

    val sizes = measures._2.getFunctions(symbols)
    val newSyms: Symbols = sizes.foldLeft(symbols)((symb, sze) => updater.transform(sze, symb))
    val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} 
      = inox.Program(termination.trees)(newSyms)
    val api = extraction.extractionSemantics.getSemantics(program).getSolver(context).toAPI 
    val ordering = measures._1

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd)) {
      val fdArgs: Seq[Variable] = fd.params.map(_.toVariable)    
      val constraints = bodyDecrease(fd, fdArgs,symbols,ordering,api)
      higherOrderDecrease(fd,fdArgs,constraints,ordering,api,symbols)
      strengthenedApp += fd 
    }

    val annotatedFuns = strengthenedApp.map{ fd => annotateStrength(fd, symbols, ordering) }.toSeq
    val newSizes = measures._2.getFunctions(symbols).toSeq
    val updatedSymbols = updater.updateFuns(annotatedFuns++newSizes,symbols)
    val annotatedSymbols = annotateSymbols(updatedSymbols,ordering)
    println("annotatedSymbols")
    println(annotatedSymbols)
    (fids, annotatedSymbols)
  }
}

object ApplicationStrengthener { self =>
  def apply(implicit ctx: inox.Context, 
            m: Measures, 
            a: Analysis): IterativePipeline = 
    new { 
      override val context = ctx 
      override val measures = m
      override val analysis = a
    } with ApplicationStrengthener
}