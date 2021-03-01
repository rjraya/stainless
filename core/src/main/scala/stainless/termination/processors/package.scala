package stainless
package termination

package object processors {
  def extractor(m: Measures, a: Analysis, symbols: termination.trees.Symbols)(implicit ctx: inox.Context) = {
    RecursionProcessor(ctx, m, a) andThen
    RelationProcessor(ctx, m, a) /*andThen 
    ChainProcessor(ctx,m,a,symbols)*/ 
  }
}