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

  def processingScheduler(
    measures: Seq[Measures], 
    symbols: termination.trees.Symbols,
    problems: Seq[Problem]
  ): (Seq[Problem], termination.trees.Symbols, Seq[s.FunDef])= measures match {
    case measure :: _ => 
      val analysis = analyzer(symbols) 
      val (remaining, modSyms) = 
        processorsPipeline(measure,analysis).extract(problems,symbols)
      if(remaining.isEmpty){ 
        val sizeFunctions = measure._2.getFunctions(modSyms)
        (Seq(), modSyms, sizeFunctions)
      } else processingScheduler(measures.tail, modSyms, remaining)
    case Nil => (problems, symbols, Seq())
  }

  def strengtheningScheduler(
    measures: Seq[Measures], 
    symbols: termination.trees.Symbols,
    problems: Seq[Problem]
  ): termination.trees.Symbols = {
    def strengthenWithMeasure(problem: Problem, measure: Measures): Option[s.Symbols] = {
      println("initial symbols")
      println(symbols.functions.values)
      val preAnalysis = analyzer(symbols)
      val strength = strengtheningPipeline(measure, preAnalysis)
      //println("original symbols")
      //println(symbols)
      val (_, nSymbols) = strength.extract(problem,symbols) 
      val analysis = analyzer(nSymbols) 
      println("after strengthening")
      println(nSymbols)
      val processors = processorsPipeline(measure,analysis)
      val (remaining, modSyms) = processors.extract(problem,nSymbols)
      if(remaining.isEmpty){ 
        val sfuns = measure._2.getFunctions(modSyms)
        Some(updater.transform(sfuns, modSyms))
      } else {
        None
      }
    }
    def strengthenProblem(problem: Problem, measures: Seq[Measures]): Option[s.Symbols] = measures match {
      case m :: ms => strengthenWithMeasure(problem, m) match {
        case Some(syms) => Some(syms)
        case None => strengthenProblem(problem, ms)
      }
      case Nil => None
    }

    problems match {
      case p :: ps => 
        strengthenProblem(p, measures) match {
          case Some(nSyms) => 
            strengtheningScheduler(measures,nSyms,ps)
          case None => 
            throw inox.FatalError("Could not solve termination problem") 
        }   
      case Nil => symbols
    }
  }

  def extract(symbols: s.Symbols): t.Symbols = {
    val funIds = symbols.functions.values.map(_.id).toSet
    val (problems, genSyms) = generatorsPipeline.extract(Seq(funIds), symbols)
    val measures: Seq[Measures] = {
      val (orders, szes) = getMeasures(genSyms)
      orders.map(e => (e,szes))
    }
    strengtheningScheduler(measures, genSyms, problems)
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
