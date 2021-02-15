package stainless
package termination

package object generators {
  def extractor(implicit ctx: inox.Context) = {
    SCCProcessor(ctx)
  }
}