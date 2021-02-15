package stainless
package termination

/*
 An identity transformation on symbols,
 convenient for many phases of the termination 
 pipeline.
*/
trait IdentityTransformer extends inox.transformers.SymbolTransformer { self => 
  val s: Trees
  val t: Trees

  private object transformer extends transformers.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  override def transform(symbols: s.Symbols): t.Symbols = {
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq.map(transformer.transform))
      .withFunctions(symbols.functions.values.toSeq.map(transformer.transform))
  }
}

trait UpdateTransformer { self => 
  val s: Trees
  val t: Trees

  private object transformer extends transformers.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  def transform(funDef: s.FunDef, symbols: s.Symbols): t.Symbols = {
    val updated = symbols.functions.updated(funDef.id, funDef)
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq.map(transformer.transform))
      .withFunctions(updated.values.toSeq.map(transformer.transform))
  }
}