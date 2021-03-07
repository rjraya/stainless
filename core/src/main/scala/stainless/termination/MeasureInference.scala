/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait MeasureInference extends extraction.ExtractionPipeline { self =>
  val s: termination.trees.type
  val t: termination.trees.type

  def generatorsPipeline: TerminationPipeline = 
    generators.extractor
  def processorsPipeline(m: Measures, a: Analysis, syms: s.Symbols): IterativePipeline = 
    processors.extractor(m,a,syms)
  def strengtheningPipeline(m: Measures, a: Analysis) =
    strengthener.extractor(m,a) 

  def getMeasures(syms: termination.trees.Symbols): (Seq[OrderingRelation], SizeFunctions) = {
    object szes extends {
      val trees: termination.trees.type = termination.trees
      val symbols: termination.trees.Symbols = syms
    } with SizeFunctions 
    
    object integerOrdering extends {
      val trees: termination.trees.type = termination.trees
      val symbols: termination.trees.Symbols = syms
      val sizes: szes.type = szes
    } with SumOrdering

    object lexicographicOrdering extends {
      val trees: termination.trees.type = termination.trees
      val symbols: termination.trees.Symbols = syms
      val sizes: szes.type = szes
    } with LexicographicOrdering

    (Seq(integerOrdering, lexicographicOrdering), szes)
  }

  def analyzer(syms: termination.trees.Symbols): Analysis = {
    new CICFA with RelationBuilder with ChainBuilder { 
      val program: inox.Program{
        val trees: termination.trees.type; 
        val symbols: syms.type
      } = inox.Program(termination.trees)(syms)
      val context = self.context
    }
  }

  def schedulerWithMeasure(
    problem: Problem, 
    measure: Measures, 
    syms: s.Symbols
  ): Option[s.Symbols] = {
      val (_, nSymbols) = 
        strengtheningPipeline(measure, analyzer(syms)).extract(problem,syms)  
      //val nSymbols = syms

      val (remaining, modSyms) = 
        processorsPipeline(measure,analyzer(nSymbols),nSymbols).extract(problem,nSymbols)
      if(remaining.isEmpty){ 
        val sfuns = measure._2.getFunctions(modSyms)
        Some(updater.transform(sfuns, modSyms))
      } else {
        None
      }
    }

  def problemScheduler(
    problem: Problem, 
    measures: Seq[Measures], 
    syms: termination.trees.Symbols
  ): Option[termination.trees.Symbols] =       
    measures.iterator
            .map(schedulerWithMeasure(problem, _,syms))
            .collectFirst{ case Some(nSyms) => nSyms } 
  
  def scheduler(
    measures: Seq[Measures], 
    symbols: termination.trees.Symbols,
    problems: Seq[Problem]
  ): termination.trees.Symbols = {
    problems.foldLeft(symbols){ (osyms, p) => 
      problemScheduler(p, measures, osyms) match {
        case Some(nSyms) => nSyms
        case None => throw inox.FatalError("Could not solve termination problem") 
      }
    }
  }

  def extract(symbols: s.Symbols): t.Symbols = {
    val funIds = symbols.functions.values.map(_.id).toSet
    val (problems, genSyms) = generatorsPipeline.extract(Seq(funIds), symbols)
    /* println("generated symbols")
    println(genSyms.functions.values.map(
      _.asString    
    ))
    println("generated problems")
    println(problems) */
    val measures: Seq[Measures] = {
      val (orders, szes) = getMeasures(genSyms)
      orders.map(e => (e,szes))
    }
    val res = scheduler(measures, genSyms, problems.reverse)
    println("result")
    res.functions.values.map(_.asString).map(println)
    res
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
