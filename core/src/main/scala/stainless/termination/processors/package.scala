package stainless
package termination

package object processors {
  def extractor(m: Measures)(implicit ctx: inox.Context) = {
    RecursionProcessor(ctx, m)
  }
}