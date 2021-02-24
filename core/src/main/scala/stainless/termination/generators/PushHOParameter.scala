package stainless
package termination
package generators

trait PushHOParameter extends TerminationPipeline { self => 
  import termination.trees._

  override def extract(fids: Seq[Problem], syms: Symbols): (Seq[Problem], Symbols) = {
    object scanBody extends {
      val s: termination.trees.type = termination.trees;
      val t: termination.trees.type = termination.trees;
      val symbols: termination.trees.Symbols = syms
    } with transformers.Transformer {
      type Env = Unit

      override def transform(e: Expr, env: Env): Expr = e match {
        case fi @ FunctionInvocation(id, _, args) =>
          val (hoArgs,foArgs) = 
            args.partition(_.getType(symbols).isInstanceOf[FunctionType])
          val newArgs = foArgs ++ hoArgs
          fi.copy(args = newArgs)
        case _ => super.transform(e, env)
      }
    } 

    val newFuns: Seq[FunDef] = syms.functions.values.map{ fd => 
      val (hoParams,foParams) = fd.params.partition(_.tpe.isInstanceOf[FunctionType])
      val newParams = foParams ++ hoParams
      val newBody = scanBody.transform(fd.fullBody, ()) 
      fd.copy(params = newParams, fullBody = newBody)
    }.toSeq

    (fids, updater.updateFuns(newFuns, syms))
  }

}

object PushHOParameter { self =>
  def apply(implicit ctx: inox.Context): TerminationPipeline = 
    new { override val context = ctx } with PushHOParameter
}
