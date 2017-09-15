import FunsAndTypes._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.io.Source

object HW2 {
  var system = new ArrayBuffer[(SimpleType, SimpleType)]
  var freevs = Map.empty[Variable, Var]
  val gvarmap = mutable.Map.empty[Variable, SimpleType]

  def makeSystem(expr: LambdaExpression): SimpleType = {
    expr match {
      case Abstraction(v, e) =>
          val nvar = newVar
          gvarmap(v) = nvar
          Impl(nvar, makeSystem(e))

      case Application(l, r) =>
        val tl = makeSystem(l)
        val tr = makeSystem(r)
        val nv = newVar
        system += (tl -> Impl(tr, nv))
        nv

      case v@Variable(_, _) if gvarmap.contains(v) => gvarmap(v)
      case v@Variable(_, _) if freevs.contains(v) => freevs(v)
    }
  }

  def main(args: Array[String]): Unit = {
    try {
      val (expr, rmap) = makeVarsUnique(LambdaPackratParser.parse(Source.fromFile("./task2.in").mkString).get)
      freevs = getFreeVars(Set.empty, expr).map(v => v -> newVar).toMap
      var t = makeSystem(expr)
      val sbst = solveSystem(system)
      println(sbst(t))
      for (v <- freevs) {
        println(rmap(v._1) ++ " : " ++ sbst(freevs(v._1)).toString)
      }
    } catch {
      case e : RuntimeException => println(e.getMessage)
    }
  }
}
