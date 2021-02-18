/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait MeasureInference extends extraction.ExtractionPipeline { self =>
  val s: termination.trees.type
  val t: termination.trees.type

  def generatorsPipeline: TerminationPipeline = 
    generators.extractor
  def processorsPipeline(m: Measures, a: Analysis): IterativePipeline = 
    processors.extractor(m,a)

  def measures(syms: termination.trees.Symbols): Measures = {
    object szes extends {
      val trees: termination.trees.type = termination.trees
      val symbols: termination.trees.Symbols = syms
    } with SizeFunctions 
    
    object integerOrdering extends {
      val trees: termination.trees.type = termination.trees
      val symbols: termination.trees.Symbols = syms
      val sizes: szes.type = szes
    } with SumOrdering
    
    (integerOrdering, szes)
  }

  def analysis(syms: termination.trees.Symbols): Analysis = {
    new RelationBuilder with ChainBuilder { 
      val program: inox.Program{
        val trees: termination.trees.type; 
        val symbols: syms.type
      } = inox.Program(termination.trees)(syms)
      val context = self.context
    }
  }

  def extract(symbols: s.Symbols): t.Symbols = {
    val funIds = symbols.functions.values.map(_.id).toSet
    val (problems, genSyms) = generatorsPipeline.extract(Seq(funIds), symbols)
    val (m,a) = (measures(symbols), analysis(symbols))
    val (remaining, modSyms) = 
      processorsPipeline(m,a).extract(problems,genSyms)
    val sizeFuncs = m._2.getFunctions(modSyms)
    val newSymbols = sizeFuncs.foldLeft(modSyms)( (acc, l) => updater.transform(l,acc) )
    newSymbols
  }

  def invalidate(id: Identifier): Unit = ()
}

object MeasureInference { self =>
  def apply(tr: termination.trees.type)(implicit ctx: inox.Context): extraction.ExtractionPipeline {
    val s: termination.trees.type
    val t: termination.trees.type
  } = new {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
  } with MeasureInference
}
