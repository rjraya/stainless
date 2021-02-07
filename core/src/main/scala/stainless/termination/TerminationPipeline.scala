package stainless
package termination

trait TerminationPipeline { self =>
  val s: ast.Trees
  val t: ast.Trees

  def extract(funDefs: Seq[s.FunDef], symbols: s.Symbols): (Seq[t.FunDef], t.Symbols)

  def andThen(that: TerminationPipeline { val s: self.t.type }): TerminationPipeline {
    val s: self.s.type
    val t: that.t.type
  } = new TerminationPipeline {
    override val s: self.s.type = self.s
    override val t: that.t.type = that.t

    override def extract(funDefs: Seq[self.s.FunDef], symbols: self.s.Symbols): (Seq[that.t.FunDef], that.t.Symbols) = {
      val (tFunDefs, tSymbols) = self.extract(funDefs, symbols)
      that.extract(tFunDefs, tSymbols)
    }
  }
}

