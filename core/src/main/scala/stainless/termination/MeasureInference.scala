/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait MeasureInference extends extraction.ExtractionPipeline { self =>
  val s: Trees
  val t: Trees

  //def pipeline = recursionProcessor

  def extract(symbols: s.Symbols): t.Symbols = {
    val program = inox.Program(s)(symbols)

    ???
  }
  def invalidate(id: Identifier): Unit = ???
}

object MeasureInference { self =>
  def apply(tr: Trees)(implicit ctx: inox.Context): extraction.ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
  } with MeasureInference
}
