package stainless
package termination

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

  def transform(fds: Seq[s.FunDef], symbols: s.Symbols): t.Symbols = {
    val updated = symbols.functions ++ fds.map(fd => fd.id -> fd)
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq.map(transformer.transform))
      .withFunctions(updated.values.toSeq.map(transformer.transform))
  }

  def updateFuns(fds: Seq[s.FunDef], symbols: s.Symbols): t.Symbols = {
    val newIds = fds.map{ _.id }
    val remaining = symbols.functions.filter{ p => !newIds.contains(p._1) }
    val newFuns = fds.map{ fd => (fd.id, fd) }
    val newMap = remaining ++ newFuns
    t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq.map(transformer.transform))
      .withFunctions(newMap.values.toSeq.map(transformer.transform))
    
  }
}

object updater extends UpdateTransformer {
  val s: termination.trees.type = termination.trees
  val t: termination.trees.type = termination.trees
}