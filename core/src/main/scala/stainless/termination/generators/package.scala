package stainless
package termination

package object generators {
  def extractor(implicit ctx: inox.Context) = {
    PushHOParameter(ctx) andThen
    SCCProcessor(ctx)
  }
}