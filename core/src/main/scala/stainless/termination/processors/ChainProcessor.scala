/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination
package processors

import scala.language.existentials
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

import scala.concurrent.duration._

trait ChainProcessor extends IterativePipeline
                        with MeasurePipeline 
                        with AnalysisPipeline
                        with measures.MeasureAnnotator
                        with measures.ArgumentSelector {
  import termination.trees._

  private def lessThan(e1s: Seq[(Path, Expr)], e2: Expr, syms: Symbols): Seq[(Expr, Expr, Expr => Expr)] = {
    flatTypesPowerset(e2.getType(syms)).toSeq.map(recons => (andJoin(e1s.map {
      case (path, e1) => path implies measures._1.lessThan(Seq(recons(e1)), Seq(recons(e2)))
    }), recons(e2), recons))
  }

  def getAPI(syms: Symbols) = {
    val sizes = measures._2.getFunctions(syms)
    val newSyms: Symbols = sizes.foldLeft(syms)( 
      (symb, sze) => updater.transform(sze, symb) 
    )
    val program: inox.Program{
        val trees: termination.trees.type; 
        val symbols: trees.Symbols
      } = inox.Program(termination.trees)(newSyms)
    extraction.extractionSemantics
                        .getSemantics(program)
                        .getSolver(context)
                        .withTimeout(2.5.seconds)
                        .toAPI
  }

  def findDecrease(bases: Seq[FunDef], 
                   chainsMap: Map[FunDef,(Set[FunDef], Set[ChainProcessor.this.analysis.Chain])],
                   syms: Symbols): (Seq[analysis.Chain], Option[FunDef], Option[Expr => Expr]) = {  
    val depth: Int = 1 // Number of unfoldings 
    val api = getAPI(syms)

    def solveIter(i: Int,allChains: Set[analysis.Chain],
                  cs: Set[analysis.Chain],base: FunDef): (Set[analysis.Chain], Option[Expr => Expr]) = {
      if(i < 0) (cs,None)
      else {
        val e1s = cs.toSeq.map { chain =>
          val (path, args) = chain.loop
          (path, tupleWrap(args))
        }
        val e2 = tupleWrap(base.params.map(_.toVariable))
        val formulas = lessThan(e1s, e2, syms)
        val decreases: Option[(Expr, Expr, Expr => Expr)] = formulas.find { case (query, _, _) =>
          api.solveVALID(query).contains(true)
        }
        if (decreases.isDefined) (cs,Some(decreases.get._3))
        else {
          val newChains = cs.flatMap(c1 => allChains.flatMap(c2 => c1 compose c2))
          solveIter(i-1,allChains,newChains, base)
        }
      }
    }

    def solveBase(bases: Seq[FunDef]): (Seq[analysis.Chain], Option[FunDef], Option[Expr => Expr]) = bases match {
      case base :: bs => 
        val chains = chainsMap(base)._2
        val allChains = chainsMap(base)._2
        val (cs,reconstr) = solveIter(depth, allChains,chains, base)
        if(reconstr.isDefined) (cs.toSeq, Some(base), reconstr) 
        else solveBase(bs)
      case Nil => (Seq(), None, None)  
    }

    solveBase(bases)
  }

  override def extract(fids: Problem, syms: Symbols): (Problem, Symbols) = { 
    println("running chain processor")
    val funDefs = fids.map{ fid => syms.getFunction(fid) }
    funDefs.map{ f => println(f) }
    val chainsMap = funDefs.map { funDef => 
      funDef -> analysis.getChains(funDef) 
    }.toMap
    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) {
      case (set, (fd, (fds, chains))) => set ++ fds
    }

    if (loopPoints.size > 1) { return (fids,syms) }

    val bases = 
      {if (loopPoints.nonEmpty) loopPoints 
      else chainsMap.collect { 
        case (fd, (fds, chains)) if chains.nonEmpty => fd 
      }}.toSeq
    
    findDecrease(bases,chainsMap,syms) match {
      case (cs, Some(base), Some(reconstr)) => 
        val newFunDefs = annotateChain(cs,base,reconstr)
        println("new functions")
        println(newFunDefs.map{ f => f.asString(new PrinterOptions(printUniqueIds = true)) })
        (Set(), updater.updateFuns(newFunDefs,syms))
      case (Seq(), _, _) => (fids, syms)       
    }
  }

  private val annotationMap: MutableMap[FunDef,Seq[(Expr,Expr)]] = MutableMap.empty

  def domIndex(c: analysis.Chain, f: FunDef, i: Int): Int = c.relations match {
    case analysis.Relation(fd,_,fi,_) :: _ if (fd.id == f.id) => i
    case analysis.Relation(fd,_,fi,_) :: _ if (fi.id == f.id) => i+1
    case r :: rs => domIndex(c,f,i+1)
    case _ => -1
  }

  def annotateChain(cs: Seq[analysis.Chain],base: FunDef,recons: Expr => Expr): Seq[FunDef] = {
    println("annotate chains")
    println(cs)
    println("with base")
    println(base.id) 
    println("annotation map")
    println(annotationMap)
    val ordering = measures._1
    def measure(expr: Seq[Expr]) =
      ordering.measure(Seq(recons(tupleWrap(expr))))
    def tupleMeasure(i: Int, expr: Expr, j: Int, k: Int) =
      tupleWrap(Seq(IntegerLiteral(i), expr, IntegerLiteral(j), IntegerLiteral(k)))
    // annotate base
    val args = measure(base.params.map(_.toVariable))
    val M = cs.map{ c => c.size }.max
    val baseMeasure = tupleMeasure(0,args,0,M-1)
    annotationMap += (base -> Seq((BooleanLiteral(true),baseMeasure)))

    println("base measure")
    println(baseMeasure)
    // we assume the chains cs start at base
    for (c <- cs; member <- c.fds if member.id != base.id) {
      val n = c.size
      val i = domIndex(c,member,0)
      val (domRpath,_) = analysis.Chain(c.relations.take(i)).loop
      val (imgRpath,args1) = analysis.Chain(c.relations.drop(i)).loop
      val margs1 = bindingsToLets(imgRpath.bindings, measure(args1))
      val cond1 = and(domRpath.toClause, imgRpath.toClause)
      val measure1 = tupleMeasure(0,margs1,(1-i)%n,M-1)
      val cond2 = domRpath.toClause
      val measure2 = tupleMeasure((1-i)%n,margs1,0,M-1)
      val cond3 = imgRpath.toClause
      val measure3 = tupleMeasure(0,IntegerLiteral(0),0,M-i)
      val newE = Seq((cond1,measure1),(cond2,measure2),(cond3,measure3))
      println("new bindings for " + member.id)
      println(newE)
      annotationMap += (member -> newE)
      println("annotation map")
      println(annotationMap)
    }

    val default = tupleMeasure(0,IntegerLiteral(0),0,0)
    println("annotationMap")
    println(annotationMap)
    for((fd,bindings) <- annotationMap.toSeq) yield {
      val measure = bindings.foldLeft(default){ case (acc,(path,expr)) =>
        IfExpr(path,expr,acc)
      }
      annotate(fd,measure)
    }
  }
}

object ChainProcessor { self =>
  def apply(implicit ctx: inox.Context, 
            m: Measures,
            a: Analysis,
            s: termination.trees.Symbols): IterativePipeline = 
    new {  
      override val context = ctx 
      override val measures = m
      override val analysis = a
      override val symbols = s
    } with ChainProcessor
}