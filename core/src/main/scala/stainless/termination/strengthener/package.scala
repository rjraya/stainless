package stainless
package termination

package object strengthener {
  def extractor(m: Measures)(implicit ctx: inox.Context) = {
    PostconditionStrengthener(ctx,m)
  }
}