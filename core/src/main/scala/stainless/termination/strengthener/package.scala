package stainless
package termination

package object strengthener {
  def extractor(m: Measures, a: Analysis)(implicit ctx: inox.Context) = {
    PostconditionStrengthener(ctx,m) andThen
    ApplicationStrengthener(ctx,m,a)
  }
}