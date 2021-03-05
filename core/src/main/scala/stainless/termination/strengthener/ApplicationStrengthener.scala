package stainless
package termination
package strengthener

import scala.language.existentials

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap, ListBuffer}

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

  // constraint v -> 
  private def bodyDecrease(fd: FunDef, 
                           fdArgs: Seq[Variable],
                           symbols: Symbols,
                           ordering: OrderingRelation,
                           api: inox.solvers.SimpleSolverAPI { val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} }
                          ): Map[Variable, SizeConstraint] = {
    val applications = symbols.collectWithPC(fd.fullBody) {
      case (Application(v: Variable, args), path) => 
        println("detected application of " + v + " to " + args + " under path " + path)
        (path, v, args)
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
    println(formulaMap)
    println(constraints)
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

  def instantiateFun(fi: FunctionInvocation, symbols: Symbols, ordering: OrderingRelation): FunDef   =  {
    println("instantiate fun")
    val called = symbols.getFunction(fi.id)
    val tFd = fi.tfd(symbols)
    val name = FreshIdentifier(called.id + fi.tps.mkString(""))
    val newBody = exprOps.postMap {
        case FunctionInvocation(fi.id, _, args) => 
          Some(FunctionInvocation(name, Seq(), args))
        case _ => 
          None
      } (tFd.fullBody)
    val fd = new FunDef(name,Seq(),tFd.params,tFd.returnType,newBody,tFd.flags ++ Seq(Synthetic))
    val freshFd = exprOps.freshenSignature(fd)
    val freshBody = exprOps.freshenLocals(freshFd.fullBody)
    val res = freshFd.copy(fullBody = freshBody)
    //println(res)
    res
  }

  def refineFun(fi: FunctionInvocation, instFd: FunDef, symbols: Symbols, ordering: OrderingRelation): FunDef = {
    println("refine fun")
    val called = symbols.getFunction(fi.id)
    val calledIds = called.params.map(_.id)
    val params = instFd.params
    val newParams: Seq[ValDef] = 
      (calledIds zip params.map(p => (p, p.getType(symbols)))).map {
        case (id, (param,ts@FunctionType(domTypes,retType))) =>
          val largs = domTypes.map{ t => ValDef.fresh("z", t) }
          self.applicationConstraint(fi.id, id, largs, params.map(_.toVariable), ordering) match {
            case Some(constr) => 
              val newDomTypes = largs.map{ larg => RefinementType(larg, constr) }
              param.copy(tpe = FunctionType(newDomTypes,retType))
            case None => param
          }
        case (_, (param, typ)) => param
      }

    val newFd = instFd.body(symbols) match {
      case Some(body) => 
        val newBody = exprOps.replaceFromSymbols(
          (params.map(_.toVariable) zip newParams.map(_.toVariable)).toMap, 
          body)
        instFd.copy(params = newParams, fullBody = newBody)      
      case None => 
        instFd.copy(params = newParams)      
    }

    instances += newFd
    //println(newFd)
    newFd
  }

  private val instances: ListBuffer[FunDef] = new ListBuffer[FunDef]

  def refineArgs(fi: FunctionInvocation, fd: FunDef, symbols: Symbols, ordering: OrderingRelation): Seq[Expr] = {
    val called = symbols.getFunction(fi.id)
    val calledIds = called.params.map(_.id)
    val newArgs = (calledIds zip fi.args).map {
      case (id, l @ Lambda(largs, body)) =>
        self.applicationConstraint(fi.id, id, largs, fi.args, ordering) match {
          case Some(constr) => 
            val newLArgs = largs.map{ larg => 
              val refineArg = ValDef.fresh("z", larg.tpe)
              val tpe1 = RefinementType(
                refineArg,
                exprOps.replace(Map(larg.toVariable -> refineArg.toVariable),constr)
              )
              larg.copy(tpe = tpe1)
            }
            val subst = (largs.map(_.toVariable) zip newLArgs.map(_.toVariable)).toMap
            val newBody = exprOps.replaceFromSymbols(subst,body)   
            Lambda(newLArgs, newBody)
          case None => l
        }
      case (_, arg) => arg
    } 
    println(newArgs)
    newArgs
  }

  def annotateStrength(fd: FunDef, syms: Symbols, ordering: OrderingRelation): FunDef = {
    object transformer extends {
      val s: termination.trees.type = termination.trees;
      val t: termination.trees.type = termination.trees;
      val symbols: termination.trees.Symbols = syms
    } with transformers.TransformerWithPC
      with transformers.DefinitionTransformer {
      type Env = Path
      val initEnv = Path.empty
      val pp = Path

      override def transform(e: Expr, path: Path): Expr = e match {
        case fi @ FunctionInvocation(fid,_, args) =>

          val called = symbols.getFunction(fi.id)
          val calledIds = called.params.map(_.id)
          val recTrans = args.map(arg => transform(arg,path))
          val newFi = FunctionInvocation(fid,fi.tps, recTrans)
          val newArgs = refineArgs(newFi,fd,symbols, ordering)

          val strengthen = 
            calledIds.exists{ id => 
              appConstraint.get(fid -> id) == Some(StrongDecreasing) ||
              appConstraint.get(fid -> id) == Some(WeakDecreasing) }
          println(appConstraint)
          println("strengthen " + strengthen)  
          println("calledIds " + calledIds)
          println("fid " + fid)       
          val explicitTParams = 
            fi.tps.filter{ p => !p.isInstanceOf[TypeParameter] }.nonEmpty
          println("explicitTParams " + explicitTParams)
          val isSynthetic = called.flags contains Synthetic
          println(isSynthetic)
          val newFid = if(strengthen && explicitTParams && !isSynthetic){
            println("strengthen")
            val instFd = instantiateFun(fi, syms, ordering)
            println("instantiated fun")
            println(instFd) 
            val newSymbols = updater.updateFuns(Seq(instFd),symbols)
            val refFd = refineFun(fi, instFd, newSymbols, ordering).id
            println("refined function")
            println(refFd)
            refFd
          } else fi.id

          val newTArgs = if(strengthen && explicitTParams && !isSynthetic) Seq() else fi.tps
          
          fi.copy(id = newFid, tps = newTArgs, args = newArgs)
        case _ => super.transform(e, path)
      }
    }

    println("strengthening " + fd.id)
    transformer.transform(fd)
  }

  override def extract(fids: Problem, symbols: Symbols): (Problem, Symbols) = {
    import symbols._
    println("running application strengthener")/* 
    println(symbols.functions.values.map(_.id.asString(
      new PrinterOptions(printUniqueIds = true)
    ))) */
    val funDefs: Set[FunDef] = fids.map( id => symbols.getFunction(id) )
    val transitiveFunDefs = funDefs ++ funDefs.flatMap(f => symbols.transitiveCallees(f))
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted(symbols.CallGraphOrderings.functionOrdering)

    val ordering = measures._1
    val sizes = measures._2.getFunctions(symbols)

    val newSyms: Symbols = updater.updateFuns(sizes, symbols)
    val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} 
      = inox.Program(termination.trees)(newSyms)
    val api = extraction.extractionSemantics.getSemantics(program).getSolver(context).toAPI 
    

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd)) {
      val fdArgs: Seq[Variable] = fd.params.map(_.toVariable)    
      val constraints = bodyDecrease(fd, fdArgs,symbols,ordering,api)
      higherOrderDecrease(fd,fdArgs,constraints,ordering,api,symbols)
      strengthenedApp += fd 
    }

    val annotatedFuns = strengthenedApp.map(annotateStrength(_,symbols,ordering)).toSeq
    val newSizes = measures._2.getFunctions(symbols).toSeq
    val newInstances = instances
    val updatedSymbols = updater.updateFuns(annotatedFuns++newSizes++newInstances,symbols)
    /* println("updatedSymbols")
    println(updatedSymbols.functions.values.map(_.asString(
      new PrinterOptions(printUniqueIds = true)))) */ 
    (fids, updatedSymbols)
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