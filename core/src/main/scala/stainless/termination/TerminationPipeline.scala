package stainless
package termination

import transformers._

trait TerminationPipeline { self =>
  val s: Trees
  val t: Trees

  type Problem = Set[Identifier]
  type Analyzer = RelationBuilder

  def extract(fids: Seq[Problem], 
              symbols: s.Symbols, 
              analysis: Analyzer): (Seq[Problem], t.Symbols)

  def andThen(that: TerminationPipeline { val s: self.t.type }): TerminationPipeline {
    val s: self.s.type
    val t: that.t.type
  } = new TerminationPipeline {
    override val s: self.s.type = self.s
    override val t: that.t.type = that.t

    override def extract(fids: Seq[self.Problem], symbols: self.s.Symbols): (Seq[that.Problem], that.t.Symbols) = {
      val (tFunIds, tSymbols) = self.extract(fids, symbols)
      that.extract(tFunIds, tSymbols)
    }
  }
}

object TerminationPipeline {
  def apply(transformer: TerminationTransformer { val s: Trees; val t: Trees }): TerminationPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = new TerminationPipeline { self =>
    override val s: transformer.s.type = transformer.s
    override val t: transformer.t.type = transformer.t

    override def extract(fids: Seq[Problem], symbols: s.Symbols): (Seq[Problem], t.Symbols) = {
      transformer.transform(fids, symbols)
    }
  }
}