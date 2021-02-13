package stainless
package termination

import transformers._

trait TerminationPipeline { self =>
  val s: Trees
  val t: Trees

  type Problem = Set[Identifier]

  def extract(fids: Problem, 
              symbols: s.Symbols): (Problem, t.Symbols)

  def extract(fps: Seq[Problem], 
              symbols: s.Symbols): (Seq[Problem], t.Symbols) = {
    fps.map{ p => extract(p, symbols) }
    ???
  }

  def andThen(that: TerminationPipeline { val s: self.t.type }): TerminationPipeline {
    val s: self.s.type
    val t: that.t.type
  } = new TerminationPipeline {
    override val s: self.s.type = self.s
    override val t: that.t.type = that.t

    override def extract(fids: self.Problem, symbols: self.s.Symbols): (that.Problem, that.t.Symbols) = {
      val (tFunIds, tSymbols) = self.extract(fids, symbols)
      that.extract(tFunIds, tSymbols)
    }
  }
}
