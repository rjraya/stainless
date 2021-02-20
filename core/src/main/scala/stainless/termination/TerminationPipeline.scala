package stainless
package termination

import transformers._

trait TerminationPipeline { self =>
  import termination.trees._

  implicit val context: inox.Context
  type Problem = Set[Identifier]

  def extract(fps: Seq[Problem], symbols: Symbols): (Seq[Problem], Symbols)

  def andThen(that: TerminationPipeline)(implicit ctx: inox.Context): TerminationPipeline = 
    new TerminationPipeline {
      override val context = ctx

      override def extract(fids: Seq[self.Problem], symbols: Symbols): (Seq[that.Problem], Symbols) = {
        val (tFunIds, tSymbols) = self.extract(fids, symbols)
        that.extract(tFunIds, tSymbols)
      }
    }
}

trait IterativePipeline extends TerminationPipeline { self =>
  import termination.trees._

  def extract(fps: Problem, symbols: Symbols): (Problem, Symbols)

  override def extract(fps: Seq[Problem], symbols: Symbols): (Seq[Problem], Symbols) = {
    fps match {
      case p :: ps => 
        val (nProblem, nSymbols) = extract(p,symbols)
        if (nProblem.isEmpty) extract(ps,nSymbols)
        else {
          println(nProblem)
          println(nSymbols)
          throw inox.FatalError("Could not solve termination problem") 
        }
      case _ => (fps, symbols)
    }
  }
  
  def andThen(that: IterativePipeline)(implicit ctx: inox.Context): IterativePipeline = 
    new IterativePipeline {
      override val context = ctx

      override def extract(fids: self.Problem, symbols: Symbols): (that.Problem, Symbols) = {
        val (tFunIds, tSymbols) = self.extract(fids, symbols)
        that.extract(tFunIds, tSymbols)
      }
    }

}

trait MeasurePipeline extends IterativePipeline {
  val measures: Measures
}

trait AnalysisPipeline extends IterativePipeline {
  val analysis: Analysis
}