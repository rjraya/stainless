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
    val api = getAPI(symbols)

    val formulaMap = allFormulas.groupBy(_._1).mapValues(_.map(_._2).unzip).toMap

    val constraints = 
      for ((v, (weakFormulas, strongFormulas)) <- formulaMap) yield v -> {
        if (api.solveVALID(andJoin(weakFormulas.toSeq)).contains(true)) {
          if (api.solveVALID(andJoin(strongFormulas.toSeq)).contains(true)) {
            StrongDecreasing
          } else WeakDecreasing
        } else NoConstraint
      }
    /* println(formulaMap)
    println(constraints) */
    constraints
  }

  // constraint fi -> v for v higher-order parameter of f
  private def higherOrderDecrease(
                          fd: FunDef, 
                          fdArgs: Seq[Variable],
                          constraints: Map[Variable, SizeConstraint], 
                          ordering: OrderingRelation,
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
      appConstraint(fd.id -> v.id) = constraint(v, outers.getOrElse(v, Seq.empty), constraints, fdArgs, ordering, symbols)
    }

    val selfs = invocationMap.mapValues(_.filter(_._1._1 == fd))
    for (v <- fdHOArgs) {
      appConstraint(fd.id -> v.id) = constraint(v, selfs.getOrElse(v, Seq.empty), constraints, fdArgs, ordering, symbols)
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
      ): SizeConstraint = {
    import symbols._
    val api = getAPI(symbols)

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

  def refineFun(fd: FunDef, symbols: Symbols) = {
    val ordering = measures._1
    val newParams = fd.params.map{ param =>
      param.getType(symbols) match {
        case t@FunctionType(domTypes,retType) =>
          val largs = domTypes.map{ t => ValDef.fresh("z", t) }
          self.applicationConstraint(fd.id, param.id, largs, fd.params.map(_.toVariable), ordering) match {
            case Some(constr) => 
              val newDomTypes = largs.map{ larg => RefinementType(larg, constr) }
              param.copy(tpe = FunctionType(newDomTypes,retType))
            case None => param
          }          
        case _ => param
      }
    }
    val subst: Map[Variable,Expr] = 
      fd.params.map(_.toVariable).zip(newParams.map(_.toVariable)).toMap
    val newBody = exprOps.replaceFromSymbols(subst,fd.fullBody)
   
    fd.copy(params = newParams, fullBody = newBody)
  }

  /*
    because of polymorphic sizes, we need to copy the refinement induced 
    in the called function to the invocation
  */
  def refineInv(fi: FunctionInvocation, symbols: Symbols): FunctionInvocation = {
    val ordering = measures._1
    val called = symbols.getFunction(fi.id)

    val subst: Map[Variable,Expr] = 
      called.params.map(_.toVariable).zip(fi.args).toMap
    val tySubst: Map[TypeParameter, Type] = 
      called.tparams.map(_.tp).zip(fi.tps).toMap

    val newArgs = (called.params zip fi.args).map {
      case (ValDef(id,tp@FunctionType(doms,ret),flags), l @ Lambda(largs, body)) =>
        val newLArgs = (doms zip largs).map{ case (dom,larg) => 
          val instance = typeOps.instantiateType(dom, tySubst)
          val argTp = typeOps.replaceFromSymbols(subst,instance)
          larg.copy(tpe = argTp)
        }  
        val largsSubst: Map[Variable, Expr] =
          largs.map(_.toVariable).zip(newLArgs.map(_.toVariable)).toMap 
        val newBody = exprOps.replaceFromSymbols(largsSubst, body)
        Lambda(newLArgs, newBody)
      case (_, arg) => arg
    } 
    
    fi.copy(args = newArgs)
  }


  private val refinedIds: ListBuffer[Identifier] = new ListBuffer[Identifier]

  def annotateStrength(fd: FunDef, syms: Symbols, ordering: OrderingRelation): Seq[FunDef] = {
    val refinedFuns = new ListBuffer[FunDef]
    
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
          val strengthen = 
            called.params.map(_.id).exists{ id => 
              appConstraint.get(fid -> id) == Some(StrongDecreasing) ||
              appConstraint.get(fid -> id) == Some(WeakDecreasing) }
          val newArgs = args.map(arg => transform(arg,path))   

          if(strengthen){
            if(!(refinedIds contains called)){
              // refine the function
              refinedIds += called.id
              refinedFuns += refineFun(called, syms)
            } 
            // refine the call
            refineInv(fi, syms)
          } else {
            fi.copy(args = newArgs)
          }
        case _ => super.transform(e, path)
      }
    }

    println("strengthening " + fd.id)
    Seq(transformer.transform(fd)) ++ refinedFuns.toSeq
  }

  def getAPI(symbols: Symbols) = {
    val sizes = measures._2.getFunctions(symbols)
    val newSyms: Symbols = updater.updateFuns(sizes, symbols)
    val program: inox.Program{ val trees: termination.trees.type; val symbols: trees.Symbols} 
      = inox.Program(termination.trees)(newSyms)
    extraction.extractionSemantics.getSemantics(program).getSolver(context).toAPI 
  }

  override def extract(fids: Problem, symbols: Symbols): (Problem, Symbols) = {
    import symbols._
    println("running application strengthener on " + fids)
    /* println(symbols.functions.values.map(_.asString(
      new PrinterOptions(printUniqueIds = true)
    ))) */
    val funDefs: Set[FunDef] = fids.map( id => symbols.getFunction(id) )
    val transitiveFunDefs = funDefs ++ funDefs.flatMap(f => symbols.transitiveCallees(f))
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted(symbols.CallGraphOrderings.functionOrdering)

    val ordering = measures._1
    val sizes = measures._2.getFunctions(symbols)
    val newSyms: Symbols = updater.updateFuns(sizes, symbols)

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd)) {
      val fdArgs: Seq[Variable] = fd.params.map(_.toVariable)    
      val constraints = bodyDecrease(fd, fdArgs,newSyms,ordering)
      higherOrderDecrease(fd,fdArgs,constraints,ordering,newSyms)
      strengthenedApp += fd 
    }

    val annotatedSyms = 
      strengthenedApp.foldLeft(newSyms){
        case (syms,fdS) =>          
          updater.updateFuns(annotateStrength(fdS,syms,ordering), syms)
      }
      strengthenedApp.map(annotateStrength(_,newSyms,ordering)).toSeq
    val newSizes = measures._2.getFunctions(newSyms).toSeq
    val updatedSymbols = updater.updateFuns(newSizes,annotatedSyms)
    /* println("updatedSymbols")
    println(updatedSymbols.functions.values.map(_.asString(
      new PrinterOptions(printUniqueIds = true))))  */
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