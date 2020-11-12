package stainless
package refinement

import scala.collection.mutable.{Map => MutableMap, HashSet => MutableSet, ListBuffer => MutableList}

trait RefinementInference
  extends extraction.IdentitySorts with extraction.SimpleFunctions { self =>

  val s: Trees
  val t: Trees
  import s._

  val sizes: SizeFunctions { val trees: s.type } = new {
    val trees: s.type = self.s
  } with SizeFunctions

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]((fd, context) =>
    
  
    ???
  )

  override protected def getContext(symbols: s.Symbols) = TransformerContext(symbols, ???)

  protected case class TransformerContext(symbols: Symbols, someCache: Any) {
    val program = inox.Program(s)(symbols)
    val pipeline = Strengthener(program, self.context)(sizes)

    def inferStrengthening(original: Set[FunDef]): FunDef = {
      pipeline.strengthen(original)
      ???
    }

    ???
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    ???
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    
    val strengthenApps = ???

    ???
  }
}

object RefinementInference { self =>
  def apply(tr: Trees)(implicit ctx: inox.Context): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
  } with RefinementInference
}
