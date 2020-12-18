package stainless
package termination

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait AppStrengthener extends TerminationTransformer with inox.transformers.SymbolTransformer { self =>
  val s: Trees
  val t: Trees
  import s._
    import CallGraphOrderings._

  
  def transform(syms: s.Symbols): t.Symbols = ???

  sealed abstract class SizeConstraint
  case object StrongDecreasing extends SizeConstraint
  case object WeakDecreasing extends SizeConstraint
  case object NoConstraint extends SizeConstraint

  private val strengthenedApp: MutableSet[FunDef] = MutableSet.empty

  protected def strengthened(fd: FunDef): Boolean = strengthenedApp(fd)

  private val appConstraint: MutableMap[(Identifier, Identifier), SizeConstraint] = MutableMap.empty

  def applicationConstraint(fid: Identifier, id: Identifier, largs: Seq[ValDef], args: Seq[Expr]): Expr =
    appConstraint.get(fid -> id) match {
      case Some(StrongDecreasing) => self.lessThan(largs.map(_.toVariable), args)
      case Some(WeakDecreasing)   => self.lessEquals(largs.map(_.toVariable), args)
      case _                      => BooleanLiteral(true)
    }

  def strengthenApplications(funDefs: Set[FunDef])(implicit dbg: inox.DebugSection): Unit = {
    reporter.debug("- Strengthening applications")

    val api = getAPI

    val transitiveFunDefs = funDefs ++ funDefs.flatMap(transitiveCallees)
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd)) {

      val applications = collectWithPC(fd.fullBody) {
        case (Application(v: Variable, args), path) => (path, v, args)
      }.distinct

      val fdArgs = fd.params.map(_.toVariable)

      val allFormulas = for ((path, v, appArgs) <- applications) yield {
        val soft = path implies self.lessEquals(appArgs, fdArgs)
        val hard = path implies self.lessThan(appArgs, fdArgs)
        v -> ((soft, hard))
      }

      val formulaMap = allFormulas.view.groupBy(_._1).mapValues(_.map(_._2).unzip).toMap

      val constraints = for ((v, (weakFormulas, strongFormulas)) <- formulaMap) yield v -> {
        if (api.solveVALID(andJoin(weakFormulas.toSeq)).contains(true)) {
          if (api.solveVALID(andJoin(strongFormulas.toSeq)).contains(true)) {
            StrongDecreasing
          } else {
            WeakDecreasing
          }
        } else {
          NoConstraint
        }
      }

      val fdHOArgs = fdArgs.filter(_.tpe.isInstanceOf[FunctionType]).toSet

      val invocations = collectWithPC(fd.fullBody) {
        case (fi @ FunctionInvocation(_, _, args), path)
            if (fdHOArgs intersect args.collect { case v: Variable => v }.toSet).nonEmpty =>
          (path, args, (args zip fi.tfd.fd.params).collect {
            case (v: Variable, vd) if fdHOArgs(v) => v -> ((fi.id, vd.id))
          })
      }

      val var2invocations: Seq[(Variable, ((Identifier, Identifier), Path, Seq[Expr]))] =
        for ((path, args, mapping) <- invocations; (v, p) <- mapping) yield v -> (p, path, args)
      val invocationMap: Map[Variable, Seq[((Identifier, Identifier), Path, Seq[Expr])]] =
        var2invocations.groupBy(_._1).mapValues(_.map(_._2))

      def constraint(
          v: Variable,
          passings: Seq[((Identifier, Identifier), Path, Seq[Expr])]
      ): SizeConstraint = {
        if (constraints.get(v) == Some(NoConstraint)) NoConstraint
        else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
        else
          passings.foldLeft[SizeConstraint](constraints.getOrElse(v, StrongDecreasing)) {
            case (constraint, (key, path, args)) =>
              lazy val strongFormula = path implies self.lessThan(args, fdArgs)
              lazy val weakFormula = path implies self.lessEquals(args, fdArgs)

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

      val outers = invocationMap.mapValues(_.filter(_._1._1 != fd))
      for (v <- fdHOArgs) {
        appConstraint(fd.id -> v.id) = constraint(v, outers.getOrElse(v, Seq.empty))
      }

      val selfs = invocationMap.mapValues(_.filter(_._1._1 == fd))
      for (v <- fdHOArgs) {
        appConstraint(fd.id -> v.id) = constraint(v, selfs.getOrElse(v, Seq.empty))
      }

      strengthenedApp += fd
    }
  }

}