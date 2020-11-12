package stainless
package refinement

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait Strengthener { self =>

  val program: Program { val trees: Trees }
  val context: inox.Context

  import program.trees._
  import program.symbols._

  def strengthen(fds: Set[FunDef]): Set[FunDef]

}

object Strengthener {
  def apply(p: Program { val trees: Trees }, ctx: inox.Context)(sze: SizeFunctions { val trees: p.trees.type })
      : Strengthener { val program: p.type } =
    new {
      val program: p.type = p
      val context = ctx
    } with ProcessingPipeline { self =>
      import p.trees._

      object encoder extends {
        val s: p.trees.type = p.trees
        val t: stainless.trees.type = stainless.trees
      } with inox.transformers.TreeTransformer {
        override def transform(e: s.Expr): t.Expr = e match {
          case s.Decreases(measure, body) => transform(body)
          case _                          => super.transform(e)
        }
      }

      object cfa extends CICFA {
        val program: self.program.type = self.program
        val context = self.context
      }

      object integerOrdering extends {
        val strengthener: self.type = self
        val sizes: sze.type = sze
        val cfa: self.cfa.type = self.cfa
        val encoder: self.encoder.type = self.encoder
      } with SumOrdering with StructuralSize 

      object lexicographicOrdering extends {
        val strengthener: self.type = self
        val sizes: sze.type = sze
        val cfa: self.cfa.type = self.cfa
        val encoder: self.encoder.type = self.encoder
      } with LexicographicOrdering with StructuralSize

      object bvOrdering extends {
        val strengthener: self.type = self
        val sizes: sze.type = sze
        val cfa: self.cfa.type = self.cfa
        val encoder: self.encoder.type = self.encoder
      } with BVOrdering with StructuralSize 

      object appSum extends {
        val strengthener: self.type = self
        val ordering: integerOrdering.type = integerOrdering
      } with AppStrengthener with SumOrdering with StructuralSize 
      // different to termination
      // TODO: rewrite to usual form by eliminating Ordering from
      //       appstrengthener and just leaving a "strengthener" member

      object appLex extends {
        val strengthener: self.type = self
        val ordering: lexicographicOrdering.type = lexicographicOrdering
      } with AppStrengthener with LexicographicOrdering with StructuralSize

      object appBv extends {
        val strengthener: self.type = self
        val ordering: lexicographicOrdering.type = lexicographicOrdering
      } with AppStrengthener with BVOrdering with StructuralSize

      val processors = {
        List(
          appSum,
          appLex,
          appBv
        )
      }
    }
}
