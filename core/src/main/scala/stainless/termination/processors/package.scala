package stainless
package termination

package object processors {
  def extractor(m: Measures, a: Analysis)(implicit ctx: inox.Context) = {
    RecursionProcessor(ctx, m, a)
  }
}